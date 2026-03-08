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
    if tag == "add64":
        return f".add64 ({lean_expr(expr['lhs'])}) ({lean_expr(expr['rhs'])})"
    raise ValueError(f"unsupported lean expr tag: {tag}")


def lean_stmt(stmt: dict) -> str:
    tag = stmt["tag"]
    if tag == "wrtmp":
        return f".wrTmp {stmt['tmp']} ({lean_expr(stmt['expr'])})"
    if tag == "put":
        return f".put .{stmt['reg']} ({lean_expr(stmt['expr'])})"
    if tag == "exit":
        return f".exit ({lean_cond(stmt['cond'])}) 0x{stmt['target']:x}"
    raise ValueError(f"unsupported lean stmt tag: {tag}")


def lean_cond(cond: dict) -> str:
    tag = cond["tag"]
    if tag == "eq64":
        return f".eq64 ({lean_expr(cond['lhs'])}) ({lean_expr(cond['rhs'])})"
    raise ValueError(f"unsupported lean cond tag: {tag}")


def build_fixture(name: str, arch_name: str, base: int, code: bytes, inputs: dict[str, int]) -> dict:
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
    succ = project.factory.successors(state)
    if len(succ.successors) != 1:
        raise ValueError(f"expected one successor, got {len(succ.successors)}")
    out = succ.successors[0]

    expected = {
        "rax": out.solver.eval(out.regs.rax),
        "rcx": out.solver.eval(out.regs.rcx),
        "rdi": out.solver.eval(out.regs.rdi),
        "rip": out.solver.eval(out.regs.rip),
    }
    concrete_input = {
        "rax": 0,
        "rcx": inputs.get("rcx", 0),
        "rdi": inputs.get("rdi", 0),
        "rip": base,
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
    mem := ByteMem.empty }}

def expected : ConcreteState :=
  {{ rax := 0x{fixture['expected']['rax']:x},
    rcx := 0x{fixture['expected']['rcx']:x},
    rdi := 0x{fixture['expected']['rdi']:x},
    rip := 0x{fixture['expected']['rip']:x},
    mem := ByteMem.empty }}

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
    *,
    lean_output: str | None,
    lean_namespace: str | None,
    derive_from_name: bool,
) -> tuple[Path, Path]:
    fixture = build_fixture(name, arch_name, base, code, inputs)
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
    parser.add_argument("--lean-output")
    parser.add_argument("--lean-namespace")
    args = parser.parse_args()

    if args.manifest:
        for spec in load_manifest_specs(Path(args.manifest)):
            inputs = {reg: parse_intlike(value) for reg, value in spec.get("input_regs", {}).items()}
            json_path, lean_path = emit_fixture(
                spec["name"],
                spec["arch"],
                parse_intlike(spec["base"]),
                bytes.fromhex(spec["bytes"]),
                inputs,
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
    json_path, lean_path = emit_fixture(
        args.name,
        args.arch,
        args.base,
        code,
        inputs,
        lean_output=args.lean_output,
        lean_namespace=args.lean_namespace,
        derive_from_name=False,
    )
    print(json_path)
    print(lean_path)


if __name__ == "__main__":
    main()
