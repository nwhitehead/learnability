#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path

import angr
import archinfo
import pyvex
from angr import options as angr_options

ROOT = Path(__file__).resolve().parents[2]
FIXTURE_DIR = ROOT / "tools" / "vex_ref" / "fixtures"
DEFAULT_LEAN_FIXTURE = ROOT / "Instances" / "Examples" / "VexLeaRdiPlus5Fixture.lean"
DEFAULT_LEAN_NAMESPACE = "Instances.Examples.VexLeaRdiPlus5Fixture"


def parse_intlike(value: int | str) -> int:
    if isinstance(value, int):
        return value
    if isinstance(value, str):
        return int(value, 0)
    raise TypeError(f"unsupported integer literal: {value!r}")


def parse_reg_assignment(text: str) -> tuple[str, int]:
    name, value = text.split("=", 1)
    return name, int(value, 0)


def parse_mem_assignment(text: str) -> tuple[int, int]:
    addr, value = text.split("=", 1)
    return int(addr, 0), int(value, 0)


def arch_from_name(name: str):
    lowered = name.lower()
    if lowered == "amd64":
        return archinfo.ArchAMD64()
    raise ValueError(f"unsupported arch: {name}")


def reg_name(arch, offset: int) -> str:
    return arch.translate_register_name(offset)


def expr_to_data(arch, expr):
    if isinstance(expr, pyvex.expr.Get):
        return {"tag": "get", "reg": reg_name(arch, expr.offset)}
    if isinstance(expr, pyvex.expr.RdTmp):
        return {"tag": "tmp", "tmp": expr.tmp}
    if isinstance(expr, pyvex.expr.Const):
        return {"tag": "const", "value": int(expr.con.value)}
    if isinstance(expr, pyvex.expr.Load):
        if expr.end != "Iend_LE":
            raise ValueError(f"unsupported load endness: {expr.end}")
        if expr.ty != "Ity_I64":
            raise ValueError(f"unsupported load type: {expr.ty}")
        return {"tag": "load64", "addr": expr_to_data(arch, expr.addr)}
    if isinstance(expr, pyvex.expr.Binop):
        if expr.op != "Iop_Add64":
            raise ValueError(f"unsupported binop: {expr.op}")
        if len(expr.args) != 2:
            raise ValueError(f"unexpected arg count for {expr.op}: {len(expr.args)}")
        return {
            "tag": "add64",
            "lhs": expr_to_data(arch, expr.args[0]),
            "rhs": expr_to_data(arch, expr.args[1]),
        }
    raise ValueError(f"unsupported expr: {type(expr).__name__}")


def cond_binop_to_data(arch, expr):
    if isinstance(expr, pyvex.expr.Binop):
        if expr.op != "Iop_CmpEQ64":
            raise ValueError(f"unsupported cond binop: {expr.op}")
        if len(expr.args) != 2:
            raise ValueError(f"unexpected arg count for {expr.op}: {len(expr.args)}")
        return {
            "tag": "eq64",
            "lhs": expr_to_data(arch, expr.args[0]),
            "rhs": expr_to_data(arch, expr.args[1]),
        }
    raise ValueError(f"unsupported condition binop: {type(expr).__name__}")


def cond_to_data(arch, expr, tmp_conds):
    if isinstance(expr, pyvex.expr.RdTmp):
        if expr.tmp not in tmp_conds:
            raise ValueError(f"unsupported exit tmp guard: t{expr.tmp}")
        return tmp_conds[expr.tmp]
    if isinstance(expr, pyvex.expr.Binop):
        return cond_binop_to_data(arch, expr)
    raise ValueError(f"unsupported condition expr: {type(expr).__name__}")


def stmt_to_data(arch, stmt, tmp_conds):
    if isinstance(stmt, pyvex.stmt.IMark):
        return None
    if isinstance(stmt, pyvex.stmt.WrTmp):
        if isinstance(stmt.data, pyvex.expr.Binop) and stmt.data.op == "Iop_CmpEQ64":
            tmp_conds[stmt.tmp] = cond_binop_to_data(arch, stmt.data)
            return None
        return {"tag": "wrtmp", "tmp": stmt.tmp, "expr": expr_to_data(arch, stmt.data)}
    if isinstance(stmt, pyvex.stmt.Put):
        return {"tag": "put", "reg": reg_name(arch, stmt.offset), "expr": expr_to_data(arch, stmt.data)}
    if isinstance(stmt, pyvex.stmt.Store):
        if stmt.end != "Iend_LE":
            raise ValueError(f"unsupported store endness: {stmt.end}")
        return {
            "tag": "store64",
            "addr": expr_to_data(arch, stmt.addr),
            "value": expr_to_data(arch, stmt.data),
        }
    if isinstance(stmt, pyvex.stmt.Exit):
        return {
            "tag": "exit",
            "cond": cond_to_data(arch, stmt.guard, tmp_conds),
            "target": int(stmt.dst.value),
        }
    raise ValueError(f"unsupported stmt: {type(stmt).__name__}")


def lean_expr(expr: dict) -> str:
    tag = expr["tag"]
    if tag == "get":
        return f".get .{expr['reg']}"
    if tag == "tmp":
        return f".tmp {expr['tmp']}"
    if tag == "const":
        return f".const 0x{expr['value']:x}"
    if tag == "load64":
        return f".load64 ({lean_expr(expr['addr'])})"
    if tag == "add64":
        return f".add64 ({lean_expr(expr['lhs'])}) ({lean_expr(expr['rhs'])})"
    raise ValueError(f"unsupported lean expr tag: {tag}")


def lean_stmt(stmt: dict) -> str:
    tag = stmt["tag"]
    if tag == "wrtmp":
        return f".wrTmp {stmt['tmp']} ({lean_expr(stmt['expr'])})"
    if tag == "put":
        return f".put .{stmt['reg']} ({lean_expr(stmt['expr'])})"
    if tag == "store64":
        return f".store64 ({lean_expr(stmt['addr'])}) ({lean_expr(stmt['value'])})"
    if tag == "exit":
        return f".exit ({lean_cond(stmt['cond'])}) 0x{stmt['target']:x}"
    raise ValueError(f"unsupported lean stmt tag: {tag}")


def lean_cond(cond: dict) -> str:
    tag = cond["tag"]
    if tag == "eq64":
        return f".eq64 ({lean_expr(cond['lhs'])}) ({lean_expr(cond['rhs'])})"
    raise ValueError(f"unsupported lean cond tag: {tag}")


def normalize_mem64le(mem64le: dict[int, int]) -> list[dict[str, int]]:
    return [
        {"addr": addr, "value": value}
        for addr, value in sorted(mem64le.items())
    ]


def lean_mem64le(mem64le: list[dict[str, int]]) -> str:
    expr = "ByteMem.empty"
    for cell in mem64le:
        expr = f"(ByteMem.write64le {expr} 0x{cell['addr']:x} 0x{cell['value']:x})"
    return expr


def build_fixture(
    name: str,
    arch_name: str,
    base: int,
    code: bytes,
    inputs: dict[str, int],
    input_mem64le: dict[int, int] | None = None,
    watch_mem64le: list[int] | None = None,
) -> dict:
    arch = arch_from_name(arch_name)
    irsb = pyvex.IRSB(code, base, arch)
    statements = []
    tmp_conds = {}
    for stmt in irsb.statements:
        data = stmt_to_data(arch, stmt, tmp_conds)
        if data is not None:
            statements.append(data)
    if not isinstance(irsb.next, pyvex.expr.Const):
        raise ValueError("only constant fallthrough next expressions are supported")

    project = angr.load_shellcode(code, arch=arch_name, start_offset=base)
    state = project.factory.blank_state(
        addr=base,
        add_options={
            angr_options.ZERO_FILL_UNCONSTRAINED_MEMORY,
            angr_options.ZERO_FILL_UNCONSTRAINED_REGISTERS,
        },
    )
    state.memory.store(base, code)
    for reg, value in inputs.items():
        setattr(state.regs, reg, value)
    input_mem64le = input_mem64le or {}
    for addr, value in input_mem64le.items():
        state.memory.store(addr, value.to_bytes(8, byteorder="little"))
    succ = project.factory.successors(state)
    if len(succ.successors) != 1:
        raise ValueError(f"expected one successor, got {len(succ.successors)}")
    out = succ.successors[0]

    watch_mem64le = watch_mem64le or sorted(input_mem64le.keys())
    expected = {
        "rax": out.solver.eval(out.regs.rax),
        "rcx": out.solver.eval(out.regs.rcx),
        "rdi": out.solver.eval(out.regs.rdi),
        "rip": out.solver.eval(out.regs.rip),
        "mem64le": [
            {
                "addr": addr,
                "value": int.from_bytes(out.solver.eval(out.memory.load(addr, 8), cast_to=bytes), "little"),
            }
            for addr in watch_mem64le
        ],
    }
    concrete_input = {
        "rax": inputs.get("rax", 0),
        "rcx": inputs.get("rcx", 0),
        "rdi": inputs.get("rdi", 0),
        "rip": base,
        "mem64le": normalize_mem64le(input_mem64le),
    }

    return {
        "name": name,
        "arch": arch_name,
        "base": base,
        "bytes": [b for b in code],
        "vex_pretty": str(irsb),
        "block": {
            "stmts": statements,
            "next": int(irsb.next.con.value),
        },
        "input": concrete_input,
        "expected": expected,
    }


def write_json(fixture: dict) -> Path:
    FIXTURE_DIR.mkdir(parents=True, exist_ok=True)
    out = FIXTURE_DIR / f"{fixture['name']}.json"
    out.write_text(json.dumps(fixture, indent=2) + "\n")
    return out


def default_lean_namespace(name: str) -> str:
    parts = name.split("_")
    if parts and parts[0].lower() == "amd64":
        parts = parts[1:]
    camel = "".join(part.capitalize() for part in parts)
    return f"Instances.Examples.Vex{camel}Fixture"


def lean_namespace_to_path(namespace: str) -> Path:
    return ROOT.joinpath(*namespace.split(".")).with_suffix(".lean")


def resolve_lean_target(
    name: str,
    lean_output: str | None,
    lean_namespace: str | None,
    *,
    derive_from_name: bool,
) -> tuple[Path, str]:
    if derive_from_name:
        namespace = lean_namespace or default_lean_namespace(name)
        path = Path(lean_output) if lean_output else lean_namespace_to_path(namespace)
    else:
        namespace = lean_namespace or DEFAULT_LEAN_NAMESPACE
        path = Path(lean_output) if lean_output else DEFAULT_LEAN_FIXTURE
    if not path.is_absolute():
        path = ROOT / path
    return path, namespace


def write_lean(fixture: dict, lean_path: Path, lean_namespace: str) -> Path:
    stmts = ",\n      ".join(lean_stmt(stmt) for stmt in fixture["block"]["stmts"])
    byte_list = ", ".join(f"0x{b:02x}" for b in fixture["bytes"])
    input_mem = lean_mem64le(fixture["input"].get("mem64le", []))
    expected_mem = lean_mem64le(fixture["expected"].get("mem64le", []))
    lean = f"""import Instances.ISAs.VexISA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace {lean_namespace}

open VexISA

def bytes : List UInt8 := [{byte_list}]

def block : Block :=
  {{ stmts := [
      {stmts}
    ],
    next := 0x{fixture['block']['next']:x} }}

def input : ConcreteState :=
  {{ rax := 0x{fixture['input']['rax']:x},
    rcx := 0x{fixture['input']['rcx']:x},
    rdi := 0x{fixture['input']['rdi']:x},
    rip := 0x{fixture['input']['rip']:x},
    mem := {input_mem} }}

def expected : ConcreteState :=
  {{ rax := 0x{fixture['expected']['rax']:x},
    rcx := 0x{fixture['expected']['rcx']:x},
    rdi := 0x{fixture['expected']['rdi']:x},
    rip := 0x{fixture['expected']['rip']:x},
    mem := {expected_mem} }}

end {lean_namespace}
"""
    lean_path.parent.mkdir(parents=True, exist_ok=True)
    lean_path.write_text(lean)
    return lean_path


def emit_fixture(
    name: str,
    arch_name: str,
    base: int,
    code: bytes,
    inputs: dict[str, int],
    input_mem64le: dict[int, int],
    watch_mem64le: list[int],
    *,
    lean_output: str | None,
    lean_namespace: str | None,
    derive_from_name: bool,
) -> tuple[Path, Path]:
    fixture = build_fixture(name, arch_name, base, code, inputs, input_mem64le, watch_mem64le)
    lean_path, resolved_namespace = resolve_lean_target(
        name,
        lean_output,
        lean_namespace,
        derive_from_name=derive_from_name,
    )
    json_path = write_json(fixture)
    final_lean_path = write_lean(fixture, lean_path, resolved_namespace)
    return json_path, final_lean_path


def load_manifest_specs(manifest_path: Path) -> list[dict]:
    data = json.loads(manifest_path.read_text())
    if isinstance(data, list):
        return data
    if isinstance(data, dict) and isinstance(data.get("fixtures"), list):
        return data["fixtures"]
    raise ValueError("manifest must be a list or an object with a 'fixtures' list")


def main() -> None:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--manifest")
    mode.add_argument("--name")
    parser.add_argument("--arch")
    parser.add_argument("--base", type=lambda s: int(s, 0))
    parser.add_argument("--bytes")
    parser.add_argument("--input-reg", action="append", default=[])
    parser.add_argument("--input-mem64le", action="append", default=[])
    parser.add_argument("--watch-mem64le", action="append", default=[])
    parser.add_argument("--lean-output")
    parser.add_argument("--lean-namespace")
    args = parser.parse_args()

    if args.manifest:
        for spec in load_manifest_specs(Path(args.manifest)):
            inputs = {reg: parse_intlike(value) for reg, value in spec.get("input_regs", {}).items()}
            input_mem64le = {
                parse_intlike(addr): parse_intlike(value)
                for addr, value in spec.get("input_mem64le", {}).items()
            }
            watch_mem64le = [parse_intlike(addr) for addr in spec.get("watch_mem64le", [])]
            json_path, lean_path = emit_fixture(
                spec["name"],
                spec["arch"],
                parse_intlike(spec["base"]),
                bytes.fromhex(spec["bytes"]),
                inputs,
                input_mem64le,
                watch_mem64le,
                lean_output=spec.get("lean_output"),
                lean_namespace=spec.get("lean_namespace") or spec.get("lean_module"),
                derive_from_name=True,
            )
            print(json_path)
            print(lean_path)
        return

    missing = [
        flag
        for flag, value in (("--arch", args.arch), ("--base", args.base), ("--bytes", args.bytes))
        if value is None
    ]
    if missing:
        parser.error(f"{', '.join(missing)} required unless --manifest is used")

    code = bytes.fromhex(args.bytes)
    inputs = dict(parse_reg_assignment(item) for item in args.input_reg)
    input_mem64le = dict(parse_mem_assignment(item) for item in args.input_mem64le)
    watch_mem64le = [int(item, 0) for item in args.watch_mem64le]
    json_path, lean_path = emit_fixture(
        args.name,
        args.arch,
        args.base,
        code,
        inputs,
        input_mem64le,
        watch_mem64le,
        lean_output=args.lean_output,
        lean_namespace=args.lean_namespace,
        derive_from_name=False,
    )
    print(json_path)
    print(lean_path)


if __name__ == "__main__":
    main()
