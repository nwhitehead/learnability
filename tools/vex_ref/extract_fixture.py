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
LEAN_FIXTURE = ROOT / "Instances" / "Examples" / "VexLeaRdiPlus5Fixture.lean"


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


def stmt_to_data(arch, stmt):
    if isinstance(stmt, pyvex.stmt.IMark):
        return None
    if isinstance(stmt, pyvex.stmt.WrTmp):
        return {"tag": "wrtmp", "tmp": stmt.tmp, "expr": expr_to_data(arch, stmt.data)}
    if isinstance(stmt, pyvex.stmt.Put):
        return {"tag": "put", "reg": reg_name(arch, stmt.offset), "expr": expr_to_data(arch, stmt.data)}
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
    raise ValueError(f"unsupported lean stmt tag: {tag}")


def build_fixture(name: str, arch_name: str, base: int, code: bytes, inputs: dict[str, int]) -> dict:
    arch = arch_from_name(arch_name)
    irsb = pyvex.IRSB(code, base, arch)
    statements = []
    for stmt in irsb.statements:
        data = stmt_to_data(arch, stmt)
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
    succ = project.factory.successors(state, num_inst=1)
    if len(succ.successors) != 1:
        raise ValueError(f"expected one successor, got {len(succ.successors)}")
    out = succ.successors[0]

    expected = {
        "rax": out.solver.eval(out.regs.rax),
        "rdi": out.solver.eval(out.regs.rdi),
        "rip": out.solver.eval(out.regs.rip),
    }
    concrete_input = {
        "rax": 0,
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


def write_lean(fixture: dict) -> Path:
    stmts = ",\n      ".join(lean_stmt(stmt) for stmt in fixture["block"]["stmts"])
    byte_list = ", ".join(f"0x{b:02x}" for b in fixture["bytes"])
    lean = f"""import Instances.ISAs.VexISA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Instances.Examples.VexLeaRdiPlus5Fixture

open VexISA

def bytes : List UInt8 := [{byte_list}]

def block : Block :=
  {{ stmts := [
      {stmts}
    ],
    next := 0x{fixture['block']['next']:x} }}

def input : ConcreteState :=
  {{ rax := 0x{fixture['input']['rax']:x},
    rdi := 0x{fixture['input']['rdi']:x},
    rip := 0x{fixture['input']['rip']:x} }}

def expected : ConcreteState :=
  {{ rax := 0x{fixture['expected']['rax']:x},
    rdi := 0x{fixture['expected']['rdi']:x},
    rip := 0x{fixture['expected']['rip']:x} }}

end Instances.Examples.VexLeaRdiPlus5Fixture
"""
    LEAN_FIXTURE.parent.mkdir(parents=True, exist_ok=True)
    LEAN_FIXTURE.write_text(lean)
    return LEAN_FIXTURE


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--name", required=True)
    parser.add_argument("--arch", required=True)
    parser.add_argument("--base", required=True, type=lambda s: int(s, 0))
    parser.add_argument("--bytes", required=True)
    parser.add_argument("--input-reg", action="append", default=[])
    args = parser.parse_args()

    code = bytes.fromhex(args.bytes)
    inputs = dict(parse_reg_assignment(item) for item in args.input_reg)
    fixture = build_fixture(args.name, args.arch, args.base, code, inputs)
    json_path = write_json(fixture)
    lean_path = write_lean(fixture)
    print(json_path)
    print(lean_path)


if __name__ == "__main__":
    main()
