# VEX Opcode / IR Coverage Report

This report inventories the current Lean VEX slice against the generated fixture corpus and the
pinned `angr`/`pyvex` extractor support.

## Current Lean Surface

```text
Category   Supported constructors / ops
---------  -----------------------------------------------------------------
Reg        rax, rcx, rdi, rip
Expr       const, get, tmp, add64, load64
Cond       eq64
Stmt       wrTmp, put, store64, exit
```

## Extractor-Supported pyvex Shapes

```text
Kind                 Supported now
-------------------  ---------------------------------------------
pyvex expr classes   Binop, Const, Get, Load, RdTmp
pyvex stmt classes   Exit, IMark, Put, Store, WrTmp
expr binops          Iop_Add64
condition binops     Iop_CmpEQ64
lowered expr tags    const, get, load64, tmp
lowered stmt tags    put, wrtmp
```

## Corpus Inventory

```text
Fixture count  20
```

### Statement tag counts

```text
Stmt tag   Count
---------  -----
wrtmp         48
put           19
exit          10
store64        1
```

### Expression / condition tag counts

```text
Expr / cond tag  Count
---------------  -----
tmp                 50
get                 33
const               20
add64               14
cond:eq64           10
load64               1
```

### Fixture inventory

```text
amd64_jrcxz_skip_lea_fallthrough.json
amd64_jrcxz_skip_lea_rax_rdi_plus_rcx_fallthrough.json
amd64_jrcxz_skip_lea_rax_rdi_plus_rcx_taken.json
amd64_jrcxz_skip_lea_rcx_rdi_plus_5_fallthrough.json
amd64_jrcxz_skip_lea_rcx_rdi_plus_5_taken.json
amd64_jrcxz_skip_lea_rdi_rdi_plus_8_fallthrough.json
amd64_jrcxz_skip_lea_rdi_rdi_plus_8_taken.json
amd64_jrcxz_skip_lea_taken.json
amd64_jrcxz_skip_mov_rax_rdi_fallthrough.json
amd64_jrcxz_skip_mov_rax_rdi_taken.json
amd64_lea_rax_rcx_plus_5.json
amd64_lea_rax_rdi.json
amd64_lea_rax_rdi_plus_rcx.json
amd64_lea_rax_rdi_plus_rcx_plus_8.json
amd64_lea_rcx_rdi_plus_5.json
amd64_lea_rdi_plus_5.json
amd64_mov_mem_rdi_rax.json
amd64_mov_rax_mem_rdi.json
amd64_mov_rcx_rdi.json
amd64_mov_rdi_rcx.json
```

## Effective Coverage Summary

```text
Layer              Covered now                          Notes
-----------------  -----------------------------------  -----------------------------------------------
Registers          rax, rcx, rdi, rip                  tiny architectural slice
Data movement      GET, PUT, tmp flow                  straight-line register transfer
Arithmetic         Iop_Add64                           current lea-style corpus only
Memory reads       LDle:I64                            proved in Lean, cross-checked against angr
Memory writes      STle with 64-bit data               proved in Lean, cross-checked against angr
Branch conditions  Iop_CmpEQ64 via Exit                current jrcxz-style slice
CFG shape          fallthrough + single guarded exit   not multi-block, not general CFG
```

## Supported Raw VEX IR Patterns

```text
VEX concept            Supported form now
--------------------   ------------------------------------------------------
WrTmp                  yes
Put                    yes
Exit                   yes, one current condition family
Load                   yes, LDle:I64
Store                  yes, STle(I64 payload)
Binop arithmetic       Add64
Binop comparison       CmpEQ64
Temps                  yes, via WrTmp / RdTmp
IMark                  parsed/observed, not semantically interesting itself
```

## Not Yet Covered

```text
Arithmetic / bitwise   Iop_Sub64, Iop_And64, Iop_Or64, Iop_Xor64,
                       Iop_Shl64, Iop_Shr64, Iop_Sar64
Comparisons            CmpLT*, CmpLE*, CmpNE*, signed/unsigned families
Memory widths          anything other than 64-bit little-endian load/store
Casts / width changes  sign extension, zero extension, truncation
Flags / helpers        ccall helpers, flag computation machinery
Effects                Dirty helpers, CAS, atomics
Control flow           indirect jumps, calls, returns, multi-block CFG
Expressions            ITE and richer expression surface
Registers              everything beyond rax/rcx/rdi/rip
Architectures          everything beyond AMD64
```

## Turing-Completeness Status

No. This slice is not Turing complete.

```text
Reason
---------------------------------------------------------
No multi-block semantics
No general loop / back-edge model in the VEX frontend
No indirect control flow
Tiny expression and statement fragment
Tiny architectural register slice
```

## Immediate Next Coverage Targets

```text
1. More memory fixtures within the existing 64-bit LE model
2. More arithmetic/binop support: Sub64, bitwise ops, shifts
3. More comparisons / branch conditions beyond equality
4. Wider register coverage before flags / cc machinery
```
