# Learnability Framework — Review Standards

Review gates for all commits. Agents MUST check these before approving.

## Existing Gates

1. **0 sorries** — no `sorry` in any `.lean` file
2. **Totality** — functions should be total (no partial pattern matches)

## Computability Gates (NEW)

3. **No `noncomputable` without sophie's approval** — decidable algorithms
   must compute. Any `noncomputable` requires sophie's explicit sign-off.
   Review agents flag any `noncomputable` as blocking; sophie approves or rejects.

4. **No existence-only proofs for runnable things** — `exists x, P x` is wrong
   when the point is to produce `x`. If a definition should be executable,
   it must construct its result, not just prove one exists.

5. **No `Classical.choice` in computational paths** — use `Decidable` instances
   only. Classical reasoning is fine in pure proof terms (theorems), not in
   definitions that should run. Specifically:
   - `open Classical` is banned in `def`/`abbrev` blocks
   - `Nonempty.choose`, `Classical.choice`, `Classical.arbitrary` are banned
     in definitions
   - `Decidable` instances must be provided or derived, not conjured via
     `Classical.dec`

6. **Computational mapping** — every definition must answer one of:
   - "What computational content does this map to?" (e.g., `finsetQuery` maps
     to selecting an unexplored branch from a finite set)
   - "What meta-property of an implementation does this capture?" (e.g.,
     `Bisimilar` captures observational equivalence)
   - If neither applies, the definition needs justification.

## Justified Noncomputable

Some `noncomputable` markers are genuinely justified:
- `Quotient.lift` is noncomputable in Lean 4's kernel (architectural limitation)
- Definitions quantifying over infinite/undecidable domains in pure proof context
- Fintype instances constructed via injections (kernel limitation)

These STILL require sophie's sign-off. The justification goes in
`plans/noncomputable-audit.md`, not just a code comment.

## Review Agent Checklist

For each commit, verify:
- [ ] `grep -c 'sorry' *.lean` returns 0
- [ ] `grep 'noncomputable' *.lean` — each occurrence is either previously
      approved (in noncomputable-audit.md) or flagged as blocking
- [ ] `grep 'Classical.choice\|Classical.arbitrary\|Nonempty.choose' *.lean` —
      none in `def`/`abbrev` context
- [ ] `grep 'open Classical' *.lean` — not in scope of any `def`/`abbrev`
- [ ] New definitions have clear computational or meta-property mapping
