# VEX Width Milestone 1

This milestone adds the first real width-sensitive semantics to the Lean VEX model without crossing into flags or broader partial-register aliasing.

## What Is Implemented

The core VEX expression/symbolic-summary layers now support the minimal width operators needed for real lifted AMD64 32-bit writes:

- `.low32`
- `.uext32`

Semantically, both are modeled as masking to the low 32 bits of a `UInt64` value.

This is sufficient for the common VEX pattern:

- `64to32`
- `32Uto64`

which expresses a 32-bit write that zero-extends back into the full 64-bit architectural register.

## What Real Lifted Patterns Are Now Covered

The model is checked against pinned `angr` / `pyvex` fixtures for:

- `mov eax, edi`
- `mov ecx, edi`
- `lea eax, [rdi+5]`
- `lea ecx, [rdi+5]`

These are important because they exercise:

- 32-bit truncation from a 64-bit source
- zero-extension into a 64-bit destination register
- non-`rax` destinations
- width-sensitive writes after arithmetic address computation without flags

## What This Does Not Yet Cover

This is not full width semantics.

Still deferred:

- flags / cc machinery (`cc_op`, `cc_dep1`, `cc_dep2`)
- width-sensitive arithmetic that brings in flags, such as `add eax, edi`
- partial-register aliasing beyond the zero-extending 32-bit case
- narrower widths such as 8-bit and 16-bit writes
- sign-extending writes
- architecture-specific overlapping register families beyond the current AMD64 instance

## Why This Milestone Matters

The bridge architecture now covers a real, nontrivial width-sensitive slice of lifted VEX on top of the generic finite-register core.

That means the project has moved beyond:

- purely full-width register transfer

and into:

- real sub-register-width behavior that appears immediately in lifted AMD64 code

without yet committing to the much larger flags/aliasing design space.

## Recommended Next Boundary

The next semantic boundary after this milestone is:

1. flags / condition-code support for width-sensitive arithmetic

That is the point where patterns like `add eax, edi` become available.
