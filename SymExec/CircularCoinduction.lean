import SymExec.EffectiveObservability
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Circular Coinduction for Unbounded Loops

Extends the branch framework to handle unbounded loops. A loop body can now
be a full `CompTree` (with internal branching), not just a single `Branch`.

## Key Idea

A `LoopSummary` has:
- `body : CompTree Sub PC` — one iteration (may branch internally)
- `continues`/`exits : PC` — loop control conditions
- `bodyEffect : State → State` — deterministic concrete effect
- `bodyEffect_spec` — proof that bodyEffect agrees with treeBehavior

## Convergence

The **guard-free** branch set (`loopBranchSet`) accumulates symbolic branches
by composing the body's denotation with previously discovered branches.
It is monotone and, when it stabilizes, equals `denot(boundedIter body n)`
for all n ≥ K (`loopBranchSet_eq_boundedIter_denot`, `symbolic_loop_convergence`).

The **guarded** loop tree (`guardedLoopTree`) adds continue/exit guards and
its concrete semantics matches `boundedWhileBehavior`
(`guardedLoopTree_eq_boundedWhileBehavior`). The bridge from guard-free
stabilization to completeness of the full unbounded `whileBehavior` is
`stabilization_complete`: if `loopBranchSet` stabilizes at K, every
`whileBehavior` execution completes within K iterations.

**Worst case:** (1 + B)^K branches (exponential in unrolling depth K).
**With absorptivity:** B * K branches (linear). Absorptivity holds when
  branches in the same PC-equivalence class compose identically — true for
  parsers and other programs with finite symbolic state. The claim that this
  follows from `pcSetoid` congruence is not yet formalized (see finding #5).

## Connection to Stalagmite

Stubs in stalagmite ARE loop summaries. Co-refinement IS circular coinduction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! ## Loop Summary -/

section LoopSummary

variable {Sub PC State : Type*}

/-- A loop summary: characterizes a while loop by its body (a CompTree with
    possible internal branching), continue/exit conditions, and a deterministic
    effect function.

    The determinism field reflects that compiled programs are deterministic:
    given a concrete state, the body produces exactly one successor state
    (even if multiple symbolic paths exist internally). The `bodyEffect_spec`
    biconditional formalizes this: `treeBehavior` relates `s` to `s'` iff
    `s' = bodyEffect s`. -/
structure LoopSummary (Sub PC State : Type*) (isa : SymbolicISA Sub PC State) where
  /-- The computation tree for one loop iteration (may have internal choice). -/
  body : CompTree Sub PC
  /-- Condition for loop to repeat (checked after body executes). -/
  continues : PC
  /-- Condition for loop to exit (checked after body executes). -/
  exits : PC
  /-- Deterministic effect of one iteration on concrete states. -/
  bodyEffect : State → State
  /-- The effect function IS the tree's behavior: `treeBehavior isa body s s'`
      holds iff `s' = bodyEffect s`. Encodes determinism — exactly one
      successor per state. -/
  bodyEffect_spec : ∀ s s', CompTree.treeBehavior isa body s s' ↔ s' = bodyEffect s
  /-- Guard partition: continues and exits are complementary conditions.
      `continues ↔ pc_not exits` captures both disjointness (continues → ¬exits)
      and exhaustivity (¬exits → continues). In a standard while loop, the
      continue condition IS the negation of the exit condition. -/
  guard_partition : ∀ s, isa.satisfies s continues ↔ isa.satisfies s (isa.pc_not exits)

variable (isa : SymbolicISA Sub PC State)

/-- Iterate the body effect n times. Computable, deterministic. -/
def iterateBody (summary : LoopSummary Sub PC State isa) (n : ℕ) (s : State) : State :=
  summary.bodyEffect^[n] s

/-- Zero iterations = identity. -/
theorem iterateBody_zero (summary : LoopSummary Sub PC State isa) (s : State) :
    iterateBody isa summary 0 s = s := rfl

/-- Iteration unfolds: n+1 steps = one step then n steps. -/
theorem iterateBody_succ (summary : LoopSummary Sub PC State isa) (n : ℕ) (s : State) :
    iterateBody isa summary (n + 1) s =
    iterateBody isa summary n (summary.bodyEffect s) := by
  simp [iterateBody, Function.iterate_succ, Function.comp]

end LoopSummary


/-! ## While Loop Behavior -/

section WhileLoop

variable {Sub PC State : Type*} (isa : SymbolicISA Sub PC State)

/-- The behavior of a while loop:
    `while continues { body }` relates s to s' when there exists
    some number of iterations n such that body executes n times,
    `continues` holds before each iteration (at the pre-body state),
    and `exits` holds after the final iteration.

    For n = 0: just check exits at the initial state (zero iterations).
    For n ≥ 1: continues holds at iterations 0..n-1, exits at iteration n. -/
def whileBehavior (summary : LoopSummary Sub PC State isa) : State → State → Prop :=
  fun s s' => ∃ n,
    (iterateBody isa summary n s = s') ∧
    (∀ k, k < n → isa.satisfies (summary.bodyEffect^[k] s) summary.continues) ∧
    isa.satisfies (summary.bodyEffect^[n] s) summary.exits

/-- A loop summary is **sound** when the body captures the one-step behavior
    and the continue/exit conditions are exhaustive. -/
def LoopSummary.Sound (summary : LoopSummary Sub PC State isa)
    (oneStepBehavior : State → State → Prop) : Prop :=
  (∀ s, oneStepBehavior s (summary.bodyEffect s)) ∧
  (∀ s, isa.satisfies s summary.continues ∨ isa.satisfies s summary.exits)

end WhileLoop


/-! ## Loop Branch Set

The symbolic branches accumulated after n unrollings of the loop body. -/

section LoopBranchSet

variable {Sub PC State : Type*} [DecidableEq Sub] [DecidableEq PC]
  (isa : SymbolicISA Sub PC State)

/-- Symbolic branches after n unrollings.
    - 0 unrollings: {skip}
    - n+1: previous ∪ compose(body_branches, previous) -/
def loopBranchSet (summary : LoopSummary Sub PC State isa) :
    ℕ → Finset (Branch Sub PC)
  | 0 => {Branch.skip isa}
  | n + 1 => loopBranchSet summary n ∪
      composeBranchFinsets isa (CompTree.denot isa summary.body) (loopBranchSet summary n)

/-- The loop branch set is monotone. -/
theorem loopBranchSet_mono (summary : LoopSummary Sub PC State isa) :
    ∀ n, loopBranchSet isa summary n ⊆ loopBranchSet isa summary (n + 1) := by
  intro n
  show loopBranchSet isa summary n ⊆
    loopBranchSet isa summary n ∪
      composeBranchFinsets isa (CompTree.denot isa summary.body) (loopBranchSet isa summary n)
  exact Finset.subset_union_left

/-- Monotonicity extended to any gap. -/
theorem loopBranchSet_mono' (summary : LoopSummary Sub PC State isa) :
    ∀ n m, n ≤ m → loopBranchSet isa summary n ⊆ loopBranchSet isa summary m := by
  intro n m h
  induction h with
  | refl => exact Finset.Subset.refl _
  | step h ih => exact Finset.Subset.trans ih (loopBranchSet_mono isa summary _)

/-- After stabilization, no further unrollings add branches. -/
theorem loopBranchSet_stable (summary : LoopSummary Sub PC State isa) (K : ℕ)
    (h_stab : loopBranchSet isa summary K = loopBranchSet isa summary (K + 1)) :
    ∀ n, n ≥ K → loopBranchSet isa summary n = loopBranchSet isa summary K := by
  intro n hn
  induction n with
  | zero =>
      have hK : K = 0 := by omega
      rw [hK]
  | succ m ih =>
    by_cases hm : m ≥ K
    · -- m ≥ K, so by IH: S(m) = S(K)
      have hm_eq := ih hm
      -- S(m+1) = S(m) ∪ compose(body, S(m)) = S(K) ∪ compose(body, S(K)) = S(K+1) = S(K)
      show loopBranchSet isa summary m ∪
          composeBranchFinsets isa (CompTree.denot isa summary.body)
            (loopBranchSet isa summary m) =
        loopBranchSet isa summary K
      rw [hm_eq]
      -- Goal: S(K) ∪ compose(body, S(K)) = S(K)
      -- h_stab : S(K) = S(K+1) = S(K) ∪ compose(body, S(K))
      exact h_stab.symm
    · -- m < K, so m + 1 ≤ K, and since m + 1 ≥ K (from hn), m + 1 = K
      have : m + 1 = K := by omega
      rw [this]

/-- **Convergence theorem.**

    If the guard-free branch set stabilizes at step K, it equals the branch
    set at K for all subsequent steps. By `loopBranchSet_eq_boundedIter_denot`,
    this is equivalently the stabilization of `denot(boundedIter body n)`.

    Note: this is a statement about the guard-free `loopBranchSet`, not the
    guarded `guardedLoopTree`. The bridge from stabilization here to
    completeness for full `whileBehavior` is `stabilization_complete`.

    The cardinality of the stabilized set depends on the program:
    - Worst case: (1 + B)^K (exponential, no branch collapsing)
    - With absorptivity: ≤ 1 + B * K (linear, see `absorptive_card_bound`) -/
theorem symbolic_loop_convergence
    (summary : LoopSummary Sub PC State isa) (K : ℕ)
    (h_stab : loopBranchSet isa summary K = loopBranchSet isa summary (K + 1)) :
    ∀ n, n ≥ K → loopBranchSet isa summary n = loopBranchSet isa summary K :=
  loopBranchSet_stable isa summary K h_stab


/-! ### Absorptive Composition Bound

When composition is "absorptive" — each unrolling adds at most B new
branches regardless of how large the existing set is — the total branch
count is linear: at most 1 + B * K.

This holds for programs where branches in the same PC-equivalence class
compose identically (the congruence property from Quotient.lean). In
particular, it holds for parsers and other finite-state programs. -/

/-- Absorptivity: composing body branches with the existing set adds at most
    B new branches per step. -/
def Absorptive (summary : LoopSummary Sub PC State isa) : Prop :=
  ∀ n, (composeBranchFinsets isa (CompTree.denot isa summary.body)
          (loopBranchSet isa summary n) \
        loopBranchSet isa summary n).card ≤
    (CompTree.denot isa summary.body).card

/-- Under absorptivity, each step increases the branch set by at most B. -/
theorem absorptive_step_bound (summary : LoopSummary Sub PC State isa)
    (h_abs : Absorptive isa summary) (n : ℕ) :
    (loopBranchSet isa summary (n + 1)).card ≤
    (loopBranchSet isa summary n).card + (CompTree.denot isa summary.body).card := by
  -- S(n+1) = S(n) ∪ compose(body, S(n))
  -- |A ∪ B| = |A| + |B \ A| (disjoint decomposition)
  show (loopBranchSet isa summary n ∪
      composeBranchFinsets isa (CompTree.denot isa summary.body)
        (loopBranchSet isa summary n)).card ≤
    (loopBranchSet isa summary n).card + (CompTree.denot isa summary.body).card
  let A := loopBranchSet isa summary n
  let B := composeBranchFinsets isa (CompTree.denot isa summary.body)
              (loopBranchSet isa summary n)
  -- |A ∪ B| ≤ |A| + |B| (standard), but we need the tighter |A| + |B \ A|.
  -- Key: |A ∪ B| + |A ∩ B| = |A| + |B|, so |A ∪ B| = |A| + |B| - |A ∩ B|
  -- Also |B \ A| = |B| - |A ∩ B|, so |A ∪ B| = |A| + |B \ A|.
  -- We have |B \ A| ≤ denot.card by absorptivity.
  have h_card_eq : (A ∪ B).card + (A ∩ B).card = A.card + B.card :=
    Finset.card_union_add_card_inter A B
  have h_sdiff_card : (B \ A).card + (A ∩ B).card = B.card := by
    rw [Finset.inter_comm]; exact Finset.card_sdiff_add_card_inter B A
  -- So (A ∪ B).card = A.card + B.card - (A ∩ B).card = A.card + (B \ A).card
  have h_union : (A ∪ B).card = A.card + (B \ A).card := by omega
  rw [h_union]
  have h_sdiff_le := h_abs n
  -- (B \ A) is definitionally equal to the sdiff in h_abs
  change A.card + (B \ A).card ≤ A.card + (CompTree.denot isa summary.body).card
  exact Nat.add_le_add_left h_sdiff_le A.card

/-- **Linear bound under absorptivity: total branches ≤ 1 + B * K.** -/
theorem absorptive_card_bound (summary : LoopSummary Sub PC State isa)
    (h_abs : Absorptive isa summary) (n : ℕ) :
    (loopBranchSet isa summary n).card ≤
      1 + (CompTree.denot isa summary.body).card * n := by
  induction n with
  | zero => simp [loopBranchSet, Finset.card_singleton]
  | succ k ih =>
    have h_step := absorptive_step_bound isa summary h_abs k
    have h_mul : (CompTree.denot isa summary.body).card * (k + 1) =
        (CompTree.denot isa summary.body).card * k +
        (CompTree.denot isa summary.body).card :=
      Nat.mul_succ _ k
    omega

end LoopBranchSet


/-! ## Bridge: loopBranchSet = denot (boundedIter body n)

The guard-free `loopBranchSet` equals the symbolic denotation of
`CompTree.boundedIter body n`. This connects the convergence machinery
to the existing soundness/completeness theorems for CompTree.

For the guarded while loop, we then compose with guard assertions. -/

section LoopBranchSetBridge

variable {Sub PC State : Type*} [DecidableEq Sub] [DecidableEq PC]
  (isa : SymbolicISA Sub PC State)

/-- Skip is always in the loop branch set. -/
theorem skip_mem_loopBranchSet (summary : LoopSummary Sub PC State isa) (n : ℕ) :
    Branch.skip isa ∈ loopBranchSet isa summary n := by
  induction n with
  | zero => simp [loopBranchSet]
  | succ k ih => exact loopBranchSet_mono isa summary k ih

/-- composeBranchFinsets is monotone in the second argument. -/
theorem composeBranchFinsets_mono_right {State' : Type*}
    (isa' : SymbolicISA Sub PC State')
    (B₁ : Finset (Branch Sub PC)) {B₂ B₃ : Finset (Branch Sub PC)}
    (h : B₂ ⊆ B₃) :
    composeBranchFinsets isa' B₁ B₂ ⊆ composeBranchFinsets isa' B₁ B₃ := by
  intro x hx
  simp only [composeBranchFinsets, Finset.mem_biUnion, Finset.mem_image] at hx ⊢
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hx
  exact ⟨b₁, hb₁, b₂, h hb₂, rfl⟩

/-- The loop branch set is contained in {skip} ∪ compose(body, loopBranchSet n).
    This captures the "self-similar" structure: every accumulated branch is
    either skip or arises from composing body branches with previous results. -/
theorem loopBranchSet_sub_skip_union_compose
    (summary : LoopSummary Sub PC State isa) (n : ℕ) :
    loopBranchSet isa summary n ⊆
      {Branch.skip isa} ∪
        composeBranchFinsets isa (CompTree.denot isa summary.body)
          (loopBranchSet isa summary n) := by
  induction n with
  | zero =>
    -- loopBranchSet 0 = {skip}, and {skip} ⊆ {skip} ∪ anything
    intro x hx
    exact Finset.mem_union.mpr (Or.inl hx)
  | succ k ih =>
    -- loopBranchSet (k+1) = loopBranchSet k ∪ compose(body, loopBranchSet k)
    -- By IH: loopBranchSet k ⊆ {skip} ∪ compose(body, loopBranchSet k)
    -- And compose(body, loopBranchSet k) ⊆ compose(body, loopBranchSet (k+1)) by monotonicity
    intro x hx
    show x ∈ {Branch.skip isa} ∪
        composeBranchFinsets isa (CompTree.denot isa summary.body)
          (loopBranchSet isa summary (k + 1))
    have hx' : x ∈ loopBranchSet isa summary k ∪
        composeBranchFinsets isa (CompTree.denot isa summary.body)
          (loopBranchSet isa summary k) := hx
    rcases Finset.mem_union.mp hx' with h_old | h_new
    · -- x ∈ loopBranchSet k: by IH, x ∈ {skip} ∪ compose(body, loopBranchSet k)
      have := ih h_old
      rcases Finset.mem_union.mp this with h_skip | h_comp
      · exact Finset.mem_union.mpr (Or.inl h_skip)
      · exact Finset.mem_union.mpr (Or.inr
          (composeBranchFinsets_mono_right isa _ (loopBranchSet_mono isa summary k) h_comp))
    · -- x ∈ compose(body, loopBranchSet k): monotonicity lifts to loopBranchSet (k+1)
      exact Finset.mem_union.mpr (Or.inr
        (composeBranchFinsets_mono_right isa _ (loopBranchSet_mono isa summary k) h_new))

/-- **Bridge theorem:** `loopBranchSet` equals the symbolic denotation of
    `CompTree.boundedIter body n`.

    This connects the convergence/stabilization/absorptivity results to the
    existing soundness and completeness theorems for CompTree denotation. -/
theorem loopBranchSet_eq_boundedIter_denot
    (summary : LoopSummary Sub PC State isa) (n : ℕ) :
    loopBranchSet isa summary n =
      CompTree.denot isa (.boundedIter summary.body n) := by
  induction n with
  | zero =>
    simp only [loopBranchSet, CompTree.denot]
  | succ k ih =>
    -- loopBranchSet (k+1) = loopBranchSet k ∪ compose(body, loopBranchSet k)
    -- denot (boundedIter body (k+1)) = choiceBranchFinsets {skip} (compose(body, denot(boundedIter body k)))
    -- By IH: loopBranchSet k = denot (boundedIter body k)
    simp only [loopBranchSet, CompTree.denot, choiceBranchFinsets]
    rw [← ih]
    -- Goal: S ∪ compose(body, S) = {skip} ∪ compose(body, S)
    -- where S = loopBranchSet k
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with h_old | h_new
      · have := loopBranchSet_sub_skip_union_compose isa summary k h_old
        rcases Finset.mem_union.mp this with h_s | h_c
        · exact Finset.mem_union.mpr (Or.inl h_s)
        · exact Finset.mem_union.mpr (Or.inr h_c)
      · exact Finset.mem_union.mpr (Or.inr h_new)
    · intro hx
      rcases Finset.mem_union.mp hx with h_skip | h_comp
      · exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_singleton.mp h_skip ▸ skip_mem_loopBranchSet isa summary k))
      · exact Finset.mem_union.mpr (Or.inr h_comp)

end LoopBranchSetBridge


/-! ## Guarded Loop Tree

A `while continues { body }` with exit condition `exits`, bounded to n
iterations. Continues is checked BETWEEN iterations (after body, before
the next body), matching `whileBehavior` semantics:
- 0 iterations: `assert exits`
- n+1: `choice (assert exits) (seq body (afterBody n))`
  where `afterBody` handles the between-iterations continue/exit decision. -/

section GuardedLoopTree

variable {Sub PC State : Type*} [DecidableEq Sub] [DecidableEq PC]
  (isa : SymbolicISA Sub PC State)

/-- Post-body decision: after body has executed, either exit or (check continues,
    execute body again, recurse). This is the "between iterations" logic.

    - 0: must exit (assert exits)
    - n+1: exit OR (continues holds, body executes, recurse) -/
def afterBody (summary : LoopSummary Sub PC State isa) :
    ℕ → CompTree Sub PC
  | 0 => .assert summary.exits
  | n + 1 => .guardedChoice summary.exits
      .skip
      (.seq (.assert summary.continues) (.seq summary.body (afterBody summary n)))

/-- The guarded while loop as a CompTree, bounded to at most n iterations.
    Matches `whileBehavior` semantics: continues is checked BETWEEN iterations
    (after body, before the next body), not before the first or after the last.

    - 0 iterations: assert exits at initial state
    - n+1: exit OR (execute body, then afterBody decides continue/exit) -/
def guardedLoopTree (summary : LoopSummary Sub PC State isa) :
    ℕ → CompTree Sub PC
  | 0 => .assert summary.exits
  | n + 1 => .guardedChoice summary.exits
      .skip
      (.seq summary.body (afterBody isa summary n))

/-- Symbolic denotation of the guarded loop tree. -/
def guardedLoopDenot (summary : LoopSummary Sub PC State isa) (n : ℕ) :
    Finset (Branch Sub PC) :=
  CompTree.denot isa (guardedLoopTree isa summary n)

/-- The guarded loop tree inherits soundness and completeness from CompTree.
    Since `guardedLoopTree` is itself a CompTree, `denot_sound_complete` applies
    directly. The bridge `loopBranchSet_eq_boundedIter_denot` connects the
    convergence results to the unguarded body, and the guards are just CompTree
    operations (assert, seq, choice) that the existing framework handles.

    This means: to get a sound+complete branch model for a while loop bounded
    to n iterations, use `guardedLoopDenot summary n` — the existing CompTree
    soundness/completeness applies, and the convergence of the underlying
    `loopBranchSet` bounds the growth. -/
theorem guardedLoopDenot_sound_complete
    (summary : LoopSummary Sub PC State isa) (n : ℕ) :
    BranchModel.Sound isa
      (↑(guardedLoopDenot isa summary n) : Set (Branch Sub PC))
      (CompTree.treeBehavior isa (guardedLoopTree isa summary n)) ∧
    BranchModel.Complete isa
      (↑(guardedLoopDenot isa summary n) : Set (Branch Sub PC))
      (CompTree.treeBehavior isa (guardedLoopTree isa summary n)) := by
  exact CompTree.denot_sound_complete isa (guardedLoopTree isa summary n)

/-- Bounded while behavior: `whileBehavior` restricted to at most `bound` iterations.
    This is the semantic target for `guardedLoopTree`. -/
def boundedWhileBehavior (summary : LoopSummary Sub PC State isa) (bound : ℕ) :
    State → State → Prop :=
  fun s s' => ∃ n, n ≤ bound ∧
    (iterateBody isa summary n s = s') ∧
    (∀ k, k < n → isa.satisfies (summary.bodyEffect^[k] s) summary.continues) ∧
    isa.satisfies (summary.bodyEffect^[n] s) summary.exits

/-- `f^[n+1] x = f^[n] (f x)` — definitional from `Function.iterate`. -/
private theorem iterate_succ_apply' {α : Type*} (f : α → α) (n : ℕ) (x : α) :
    f^[n + 1] x = f^[n] (f x) := rfl

/-- `f^[n+1] x = f (f^[n] x)` (pointwise form of iterate_succ'). -/
private theorem iterate_succ_apply {α : Type*} (f : α → α) (n : ℕ) (x : α) :
    f^[n + 1] x = f (f^[n] x) := by
  rw [Function.iterate_succ', Function.comp_apply]

/-- Iterating f commutes: `f^[n] (f x) = f (f^[n] x)`. -/
private theorem iterate_comm {α : Type*} (f : α → α) (n : ℕ) (x : α) :
    f^[n] (f x) = f (f^[n] x) := by
  rw [← iterate_succ_apply' f n x, iterate_succ_apply f n x]

omit [DecidableEq Sub] [DecidableEq PC] in
/-- The concrete behavior of `afterBody n` matches the "between iterations" semantics:
    starting from state s (which is already post-body), either exit or (continues holds,
    do body, recurse with up to n more post-body decisions). -/
private theorem afterBody_behavior
    (summary : LoopSummary Sub PC State isa) (n : ℕ) (s s' : State) :
    CompTree.treeBehavior isa (afterBody isa summary n) s s' ↔
      ∃ m, m ≤ n ∧
        (summary.bodyEffect^[m] s = s') ∧
        (∀ k, k < m → isa.satisfies (summary.bodyEffect^[k] s) summary.continues) ∧
        isa.satisfies (summary.bodyEffect^[m] s) summary.exits := by
  induction n generalizing s with
  | zero =>
    simp only [afterBody, CompTree.treeBehavior, assertBehavior]
    constructor
    · rintro ⟨hsat, heq⟩
      exact ⟨0, le_refl 0, heq.symm, fun k hk => by omega, heq ▸ hsat⟩
    · rintro ⟨m, hm, heq, -, hext⟩
      have hm0 : m = 0 := by omega
      subst hm0; simp at heq; exact ⟨heq ▸ hext, heq.symm⟩
  | succ n ih =>
    simp only [afterBody, CompTree.treeBehavior, choiceBehavior, assertBehavior,
               seqBehavior, skipBehavior]
    constructor
    · rintro (⟨t₁, ⟨hsat, ht₁⟩, heq⟩ | ⟨_, ⟨_, hrfl⟩, t₁, ⟨hcont, ht₁⟩, t₂, hbody, hafter⟩)
      · -- exit branch: seqBehavior (assertBehavior exits) skipBehavior
        subst ht₁; exact ⟨0, Nat.zero_le _, heq.symm, fun k hk => by omega, heq ▸ hsat⟩
      · -- continue branch: seqBehavior (assertBehavior (pc_not exits)) (seqBehavior (assertBehavior continues) ...)
        subst hrfl; subst ht₁
        have hdet := (summary.bodyEffect_spec _ t₂).mp hbody; subst hdet
        rw [ih] at hafter
        obtain ⟨m', hm', heq', hconts', hext'⟩ := hafter
        refine ⟨m' + 1, by omega, ?_, ?_, ?_⟩
        · rw [iterate_succ_apply']; exact heq'
        · intro k hk
          cases k with
          | zero => exact hcont
          | succ k' =>
            rw [iterate_succ_apply']
            exact hconts' k' (by omega)
        · rw [iterate_succ_apply']; exact hext'
    · rintro ⟨m, hm, heq, hconts, hext⟩
      cases m with
      | zero =>
        -- exit: produce seqBehavior (assertBehavior exits) skipBehavior
        -- heq : s = s', need ⟨t, ⟨satisfies s exits, s = t⟩, s' = t⟩
        left; simp at heq; exact ⟨s, ⟨heq ▸ hext, rfl⟩, heq.symm⟩
      | succ m' =>
        -- continue: produce seqBehavior (assertBehavior (pc_not exits)) (seqBehavior (assertBehavior continues) ...)
        right
        have hcont0 := hconts 0 (by omega)
        refine ⟨s, ⟨(summary.guard_partition s).mp hcont0, rfl⟩, _, ⟨hcont0, rfl⟩,
                summary.bodyEffect _, (summary.bodyEffect_spec s _).mpr rfl, ?_⟩
        rw [ih]
        refine ⟨m', by omega, ?_, ?_, ?_⟩
        · rw [iterate_succ_apply'] at heq; exact heq
        · intro k hk
          have := hconts (k + 1) (by omega)
          rw [iterate_succ_apply'] at this; exact this
        · rw [iterate_succ_apply'] at hext; exact hext

omit [DecidableEq Sub] [DecidableEq PC] in
/-- **Semantic equivalence:** `treeBehavior (guardedLoopTree summary bound)` is exactly
    `boundedWhileBehavior summary bound`.

    This closes finding #1: the guarded loop tree has sound+complete branches
    (from `guardedLoopDenot_sound_complete`) AND matches the concrete loop semantics. -/
theorem guardedLoopTree_eq_boundedWhileBehavior
    (summary : LoopSummary Sub PC State isa) (bound : ℕ) (s s' : State) :
    CompTree.treeBehavior isa (guardedLoopTree isa summary bound) s s' ↔
    boundedWhileBehavior isa summary bound s s' := by
  induction bound generalizing s with
  | zero =>
    simp only [guardedLoopTree, CompTree.treeBehavior, assertBehavior,
               boundedWhileBehavior, iterateBody]
    constructor
    · rintro ⟨hsat, heq⟩
      exact ⟨0, le_refl 0, heq.symm, fun k hk => by omega, heq ▸ hsat⟩
    · rintro ⟨m, hm, heq, -, hext⟩
      have hm0 : m = 0 := by omega
      subst hm0; simp at heq; exact ⟨heq ▸ hext, heq.symm⟩
  | succ n ih =>
    simp only [guardedLoopTree, CompTree.treeBehavior, choiceBehavior,
               assertBehavior, seqBehavior, skipBehavior, boundedWhileBehavior, iterateBody]
    constructor
    · rintro (⟨t₁, ⟨hsat, ht₁⟩, heq⟩ | ⟨_, ⟨_, hrfl⟩, t, hbody, hafter⟩)
      · -- exit branch: exits at s, s' = s
        subst ht₁; exact ⟨0, Nat.zero_le _, heq.symm, fun k hk => by omega, heq ▸ hsat⟩
      · -- continue branch: pc_not exits at s, then body, then afterBody
        subst hrfl
        rename_i h_not_exits
        have hdet := (summary.bodyEffect_spec _ t).mp hbody; subst hdet
        rw [afterBody_behavior] at hafter
        obtain ⟨m', hm', heq', hconts', hext'⟩ := hafter
        refine ⟨m' + 1, by omega, ?_, ?_, ?_⟩
        · rw [iterate_succ_apply']; exact heq'
        · intro k hk
          cases k with
          | zero =>
            -- k = 0: need continues at s. We have pc_not exits at s (from guardedChoice).
            -- guard_partition.mpr gives continues from pc_not exits.
            exact (summary.guard_partition _).mpr h_not_exits
          | succ k' =>
            -- k = k'+1: need continues at bodyEffect^[k'+1] s = bodyEffect^[k'] (bodyEffect s)
            rw [iterate_succ_apply']
            exact hconts' k' (by omega)
        · rw [iterate_succ_apply']; exact hext'
    · rintro ⟨m, hm, heq, hconts, hext⟩
      cases m with
      | zero =>
        left; simp at heq; exact ⟨_, ⟨heq ▸ hext, rfl⟩, heq.symm⟩
      | succ m' =>
        -- m'+1 iterations: continues at s (k=0), so pc_not exits at s
        right
        have hcont_s := hconts 0 (by omega)
        simp at hcont_s
        refine ⟨_, ⟨(summary.guard_partition _).mp hcont_s, rfl⟩,
                summary.bodyEffect _, (summary.bodyEffect_spec _ _).mpr rfl, ?_⟩
        rw [afterBody_behavior]
        refine ⟨m', by omega, ?_, ?_, ?_⟩
        · rw [iterate_succ_apply'] at heq; exact heq
        · intro k hk
          have := hconts (k + 1) (by omega)
          rw [iterate_succ_apply'] at this; exact this
        · rw [iterate_succ_apply'] at hext; exact hext

end GuardedLoopTree


/-! ## Finite State Convergence (Corollary)

When the concrete state space is finite, pigeonhole guarantees that the
concrete `bodyEffect` orbit eventually cycles (`finite_effect_convergence`).
This is weaker than symbolic branch-set stabilization: it proves orbit
periodicity of concrete iterates, not that `loopBranchSet` stabilizes.
The connection from concrete orbit periodicity to symbolic stabilization
is not yet formalized (finding #4).

In practice, the stabilization bound comes from domain knowledge
(e.g., parser states), not state exhaustion. -/

section FiniteConvergence

variable {Sub PC State : Type*} [DecidableEq Sub] [DecidableEq PC]
  (isa : SymbolicISA Sub PC State)

/-- Iterating a periodic function: if `f^[p] x = x` with `p > 0`,
    then `f^[n] x = f^[n % p] x`. -/
private theorem iterate_mod_of_periodic {α : Type*} {f : α → α} {x : α} {p : ℕ}
    (_hp : 0 < p) (h : f^[p] x = x) (n : ℕ) :
    f^[n] x = f^[n % p] x := by
  have key : ∀ m, f^[p * m] x = x := by
    intro m; induction m with
    | zero => simp
    | succ m ih => rw [Nat.mul_succ, Function.iterate_add, Function.comp_apply, h, ih]
  conv_lhs => rw [show n = n % p + p * (n / p) from (Nat.mod_add_div n p).symm]
  rw [Function.iterate_add, Function.comp_apply, key]

/-- If the state space is finite, the body effect's orbit must cycle.
    This gives a concrete (though potentially large) stabilization bound. -/
theorem finite_effect_convergence
    [Fintype State] [DecidableEq State]
    (f : State → State) :
    ∃ maxIter,
      ∀ n, n ≥ maxIter →
        ∀ s : State, f^[n] s ∈
          Finset.image (fun k => f^[k] s) (Finset.range maxIter) := by
  use Fintype.card State + 1
  intro n hn s
  have h_card : Fintype.card State < Fintype.card (Fin (Fintype.card State + 1)) := by
    simp [Fintype.card_fin]
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, hij, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun (k : Fin (Fintype.card State + 1)) => f^[k.val] s) h_card
  have i_ne_j : i ≠ j := by intro h; exact hij (Fin.ext h)
  obtain ⟨a, b, hab, h_eq, hb⟩ : ∃ a b, a < b ∧ f^[a] s = f^[b] s ∧ b < Fintype.card State + 1 := by
    rcases Nat.lt_or_gt_of_ne i_ne_j with h | h
    · exact ⟨i, j, h, heq, hj⟩
    · exact ⟨j, i, h, heq.symm, hi⟩
  have p_pos : 0 < b - a := Nat.sub_pos_of_lt hab
  have h_periodic : f^[b - a] (f^[a] s) = f^[a] s := by
    have : f^[b] s = f^[b - a] (f^[a] s) := by
      conv_lhs => rw [show b = (b - a) + a from by omega]
      rw [Function.iterate_add, Function.comp_apply]
    rw [← this, ← h_eq]
  have h_reduce : ∀ m, m ≥ a → f^[m] s = f^[a + (m - a) % (b - a)] s := by
    intro m hm
    have h1 : f^[m] s = f^[m - a] (f^[a] s) := by
      conv_lhs => rw [show m = (m - a) + a from by omega]
      rw [Function.iterate_add, Function.comp_apply]
    have h2 : f^[m - a] (f^[a] s) = f^[(m - a) % (b - a)] (f^[a] s) :=
      iterate_mod_of_periodic p_pos h_periodic _
    have h3 : f^[(m - a) % (b - a)] (f^[a] s) = f^[a + (m - a) % (b - a)] s := by
      conv_rhs => rw [show a + (m - a) % (b - a) = (m - a) % (b - a) + a from by omega]
      rw [Function.iterate_add, Function.comp_apply]
    rw [h1, h2, h3]
  have h_bound : ∀ m, m ≥ a → a + (m - a) % (b - a) < Fintype.card State + 1 := by
    intro m _
    have : (m - a) % (b - a) < b - a := Nat.mod_lt _ p_pos
    omega
  have hn' : n ≥ a := by omega
  rw [h_reduce n hn']
  apply Finset.mem_image.mpr
  exact ⟨a + (n - a) % (b - a), Finset.mem_range.mpr (h_bound n hn'), rfl⟩

end FiniteConvergence


/-! ## Stabilization Completeness

When the guard-free branch set `loopBranchSet` stabilizes at step K, every
concrete while loop execution completes within K iterations. This connects
symbolic convergence to concrete termination: if no new symbolic branches
appear after K unrollings, the concrete orbit must cycle within K steps.

The proof:
1. `boundedIter body (K+1)` reaches `bodyEffect^[K+1] s` (induction)
2. Completeness gives a branch `b` witnessing this in `denot(boundedIter body (K+1))`
3. Bridge + stabilization: `b` is already in `denot(boundedIter body K)`
4. Soundness: `b` witnesses a transition in `treeBehavior(boundedIter body K)`
5. Determinism: the reached state is `bodyEffect^[m] s` for some `m ≤ K`
6. Periodicity: all future iterates equal some iterate in `0..K`
7. Therefore any while loop exit within `K` steps. -/

section StabilizationCompleteness

variable {Sub PC State : Type*} [DecidableEq Sub] [DecidableEq PC]
  (isa : SymbolicISA Sub PC State)


omit [DecidableEq Sub] [DecidableEq PC] in
/-- The bounded loop iteration reaches the n-th iterate of bodyEffect. -/
private theorem boundedIter_reaches_iterate
    (summary : LoopSummary Sub PC State isa) (n : ℕ) (s : State) :
    CompTree.treeBehavior isa (.boundedIter summary.body n) s (summary.bodyEffect^[n] s) := by
  induction n generalizing s with
  | zero =>
    simp only [CompTree.treeBehavior, skipBehavior, Function.iterate_zero, id]
  | succ n ih =>
    simp only [CompTree.treeBehavior, choiceBehavior, seqBehavior]
    right
    exact ⟨summary.bodyEffect s, (summary.bodyEffect_spec s _).mpr rfl,
           ih (summary.bodyEffect s)⟩

omit [DecidableEq Sub] [DecidableEq PC] in
/-- Every output of `boundedIter body n` is `bodyEffect^[m] s` for some `m ≤ n`. -/
private theorem boundedIter_deterministic
    (summary : LoopSummary Sub PC State isa) (n : ℕ) (s s' : State)
    (h : CompTree.treeBehavior isa (.boundedIter summary.body n) s s') :
    ∃ m, m ≤ n ∧ s' = summary.bodyEffect^[m] s := by
  induction n generalizing s with
  | zero =>
    simp only [CompTree.treeBehavior, skipBehavior] at h
    exact ⟨0, le_refl 0, h⟩
  | succ n ih =>
    simp only [CompTree.treeBehavior, choiceBehavior, seqBehavior, skipBehavior] at h
    rcases h with heq | ⟨t, hbody, hrest⟩
    · exact ⟨0, Nat.zero_le _, heq⟩
    · have hdet := (summary.bodyEffect_spec s t).mp hbody; subst hdet
      obtain ⟨m', hm', heq'⟩ := ih (summary.bodyEffect s) hrest
      exact ⟨m' + 1, by omega, heq'⟩

/-- **Orbit repetition lemma.** If `loopBranchSet` stabilizes at K, then for every
    initial state s, `bodyEffect^[K+1] s = bodyEffect^[m] s` for some `m ≤ K`.

    Proof: completeness gives a branch for the (K+1)-step execution; the bridge +
    stabilization places it in the K-step set; soundness + determinism extract the
    earlier iterate. -/
private theorem orbit_repetition
    (summary : LoopSummary Sub PC State isa) (K : ℕ)
    (h_stab : loopBranchSet isa summary K = loopBranchSet isa summary (K + 1))
    (s : State) :
    ∃ m, m ≤ K ∧ summary.bodyEffect^[K + 1] s = summary.bodyEffect^[m] s := by
  -- Step 1: boundedIter(K+1) reaches bodyEffect^[K+1] s
  have h_reach := boundedIter_reaches_iterate isa summary (K + 1) s
  -- Step 2: completeness gives a witnessing branch
  obtain ⟨b, hb_mem, hb_sat, hb_eval⟩ :=
    CompTree.denot_complete isa (.boundedIter summary.body (K + 1)) s _ h_reach
  -- Step 3: bridge + stabilization: b is in denot(boundedIter body K)
  rw [Finset.mem_coe, ← loopBranchSet_eq_boundedIter_denot isa summary (K + 1),
      ← h_stab, loopBranchSet_eq_boundedIter_denot isa summary K] at hb_mem
  -- Step 4: soundness gives treeBehavior(boundedIter body K) s (eval_sub b.sub s)
  have h_beh := CompTree.denot_sound isa (.boundedIter summary.body K) b
    (Finset.mem_coe.mpr hb_mem) s hb_sat
  -- Step 5: eval_sub b.sub s = bodyEffect^[K+1] s
  rw [hb_eval] at h_beh
  -- Step 6: determinism extracts the earlier iterate
  obtain ⟨m, hm, heq⟩ := boundedIter_deterministic isa summary K s _ h_beh
  exact ⟨m, hm, heq⟩

/-- **Stabilization completeness.** If `loopBranchSet` stabilizes at step K,
    then every concrete while loop execution (`whileBehavior`) completes within
    K iterations (`boundedWhileBehavior`).

    "If symbolic branches converge, the loop terminates within K iterations
    for all reachable behaviors."

    The argument: orbit repetition (from soundness + completeness + bridge)
    gives periodicity of the concrete bodyEffect orbit. Any exit state after
    K steps already appeared at some step ≤ K, and continues conditions at
    earlier steps are inherited from the original execution. -/
theorem stabilization_complete
    (summary : LoopSummary Sub PC State isa) (K : ℕ)
    (h_stab : loopBranchSet isa summary K = loopBranchSet isa summary (K + 1))
    (s s' : State)
    (h : whileBehavior isa summary s s') :
    boundedWhileBehavior isa summary K s s' := by
  obtain ⟨n, h_iter, h_conts, h_exits⟩ := h
  simp only [iterateBody] at h_iter
  -- h_iter : bodyEffect^[n] s = s'
  by_cases hn : n ≤ K
  · exact ⟨n, hn, h_iter, h_conts, h_exits⟩
  · push_neg at hn  -- hn : K < n
    -- Orbit repetition: bodyEffect^[K+1] s = bodyEffect^[m] s for some m ≤ K
    obtain ⟨m, hm, h_rep⟩ := orbit_repetition isa summary K h_stab s
    -- Periodicity setup
    have p_pos : 0 < K + 1 - m := by omega
    have h_periodic : summary.bodyEffect^[K + 1 - m] (summary.bodyEffect^[m] s) =
        summary.bodyEffect^[m] s := by
      have : summary.bodyEffect^[K + 1] s =
          summary.bodyEffect^[K + 1 - m] (summary.bodyEffect^[m] s) := by
        conv_lhs => rw [show K + 1 = (K + 1 - m) + m from by omega]
        rw [Function.iterate_add, Function.comp_apply]
      rw [← this, h_rep]
    -- All iterates ≥ m reduce to iterates in m..K
    have h_reduce : ∀ j, j ≥ m →
        summary.bodyEffect^[j] s =
        summary.bodyEffect^[m + (j - m) % (K + 1 - m)] s := by
      intro j hj
      have h1 : summary.bodyEffect^[j] s =
          summary.bodyEffect^[j - m] (summary.bodyEffect^[m] s) := by
        conv_lhs => rw [show j = (j - m) + m from by omega]
        rw [Function.iterate_add, Function.comp_apply]
      have h2 := iterate_mod_of_periodic p_pos h_periodic (j - m)
      have h3 : summary.bodyEffect^[(j - m) % (K + 1 - m)] (summary.bodyEffect^[m] s) =
          summary.bodyEffect^[m + (j - m) % (K + 1 - m)] s := by
        conv_rhs =>
          rw [show m + (j - m) % (K + 1 - m) = (j - m) % (K + 1 - m) + m from by omega]
        rw [Function.iterate_add, Function.comp_apply]
      rw [h1, h2, h3]
    -- The reduced index m' is ≤ K
    have h_bound : m + (n - m) % (K + 1 - m) ≤ K := by
      have : (n - m) % (K + 1 - m) < K + 1 - m := Nat.mod_lt _ p_pos
      omega
    set m' := m + (n - m) % (K + 1 - m) with hm'_def
    -- bodyEffect^[m'] s = bodyEffect^[n] s = s'
    have h_eq : summary.bodyEffect^[m'] s = summary.bodyEffect^[n] s :=
      (h_reduce n (by omega)).symm
    refine ⟨m', h_bound, ?_, ?_, ?_⟩
    · -- iterateBody m' s = s'
      simp only [iterateBody]
      exact h_eq.trans h_iter
    · -- continues at intermediate states
      intro k hk
      exact h_conts k (by omega)
    · -- exits at bodyEffect^[m'] s = bodyEffect^[n] s
      rw [h_eq]
      exact h_exits

end StabilizationCompleteness
