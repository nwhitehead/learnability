import EffectiveObservability
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Circular Coinduction for Unbounded Loops

Extends the branch framework to handle unbounded loops via the Lucanu-Rusu-Arusoaie
technique (JSC 2017). Instead of unrolling a loop N times (exponential branch count),
we characterize the loop by a **loop summary**: execute the body once symbolically,
producing a branch, plus continue/exit conditions.

## Key Idea

A `LoopSummary` is a tuple `(body, continues, exits)` where:
- `body : Branch Sub PC` — one iteration's substitution + guard
- `continues : PC` — loop repeats when this holds (of the post-body state)
- `exits : PC` — loop terminates when this holds (of the post-body state)

The loop summary characterizes ALL iterations: the n-th iteration's branch
is `body^n` (n-fold composition via `Branch.compose`), and the loop exits
when the post-state satisfies `exits` and no longer satisfies `continues`.

## Connection to Stalagmite

Stubs in stalagmite ARE loop summaries:
- A stub is a pre-computed summary of a function's behavior
- Co-refinement (re-run with tighter stubs until no new grammar rules) IS
  circular coinduction reaching fixpoint
- The guardedness condition (nontrivial body) corresponds to stubs requiring
  at least one real step before re-invoking

## ICTAC Context

ICTAC's `PWhile b p` is handled via bounded unrolling (`CompTree.boundedIter`).
This phase lifts that to unbounded loops by showing that loop summaries
produce sound (and potentially complete) branch models for the full while
loop behavior, without requiring an a priori iteration bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! ## Loop Summary -/

section LoopSummary

variable {Sub PC State : Type*}

/-- A loop summary: characterizes a while loop by its body effect and
    continue/exit conditions.

    `body` is the branch for one iteration (substitution + guard).
    `continues` holds of the post-body state when the loop repeats.
    `exits` holds of the post-body state when the loop terminates. -/
structure LoopSummary (Sub PC : Type*) where
  /-- The branch for one loop iteration. -/
  body : Branch Sub PC
  /-- Condition for loop to repeat (checked after body executes). -/
  continues : PC
  /-- Condition for loop to exit (checked after body executes). -/
  exits : PC

/-! ## Iterated Branch Composition -/

variable (isa : SymbolicISA Sub PC State)

/-- Compose a branch with itself n times.
    `iterateBranch isa b 0 = Branch.skip isa` (identity).
    `iterateBranch isa b (n+1) = Branch.compose isa b (iterateBranch isa b n)`. -/
def iterateBranch (b : Branch Sub PC) : ℕ → Branch Sub PC
  | 0 => Branch.skip isa
  | n + 1 => b.compose isa (iterateBranch b n)

/-- Zero iterations = skip. -/
theorem iterateBranch_zero (b : Branch Sub PC) :
    iterateBranch isa b 0 = Branch.skip isa := rfl

/-- One iteration = the branch itself (up to semantic equivalence).
    The sub is equal; the PC is semantically equivalent. -/
theorem iterateBranch_one_sub (b : Branch Sub PC) :
    (iterateBranch isa b 1).sub = isa.compose_sub b.sub isa.id_sub := rfl

/-- The effect of iterated composition is iterated application.
    `eval (b^n) s = eval_b (eval_b (... (eval_b s)))` (n times). -/
theorem iterateBranch_effect (b : Branch Sub PC) (s : State) (n : ℕ) :
    (iterateBranch isa b n).effect isa s =
    (b.effect isa)^[n] s := by
  induction n generalizing s with
  | zero => simp [iterateBranch, Branch.skip_effect, Function.iterate_zero]
  | succ n ih =>
    simp only [iterateBranch, Function.iterate_succ, Function.comp]
    rw [Branch.compose_effect]
    exact ih (b.effect isa s)

end LoopSummary


/-! ## While Loop Behavior -/

section WhileLoop

variable {Sub PC State : Type*} (isa : SymbolicISA Sub PC State)

/-- The behavior of a while loop:
    `while continues { body }` relates s to s' when there exists
    some number of iterations n such that:
    - body executes n times starting from s
    - after each of the first n iterations, `continues` holds
    - after the n-th iteration, `exits` holds
    - s' is the state after n iterations

    This is the transitive closure of body under the continue condition,
    with exit on the exit condition. -/
def whileBehavior (summary : LoopSummary Sub PC) : State → State → Prop :=
  fun s s' => ∃ n,
    -- The state after n iterations is s'
    (isa.eval_sub (iterateBranch isa summary.body n).sub s = s') ∧
    -- Body's PC is satisfied at each step
    (∀ k, k < n → isa.satisfies ((summary.body.effect isa)^[k] s) summary.body.pc) ∧
    -- Continue holds after each of the first n-1 body executions
    (∀ k, k < n → isa.satisfies ((summary.body.effect isa)^[k + 1] s) summary.continues) ∧
    -- Exit holds after the final iteration (or immediately for n=0)
    isa.satisfies ((summary.body.effect isa)^[n] s) summary.exits

/-! ## Loop Summary Soundness

If the body branch is sound for a one-step behavior, then iterating it
is sound for the iterated behavior. -/

/-- A loop summary is **sound** for a while loop when:
    1. The body branch is sound for one iteration of the loop body
    2. The exit condition is complete (every exiting state satisfies `exits`)
    3. The continue/exit conditions are exhaustive -/
def LoopSummary.Sound (summary : LoopSummary Sub PC)
    (oneStepBehavior : State → State → Prop) : Prop :=
  -- Body branch captures one iteration when body PC holds
  (∀ s, isa.satisfies s summary.body.pc →
    oneStepBehavior s (isa.eval_sub summary.body.sub s)) ∧
  -- Continue and exit partition the post-body states
  (∀ s, isa.satisfies s summary.continues ∨ isa.satisfies s summary.exits)

/-- The iterated branch effect chains one-step effects.
    If each intermediate state satisfies the body PC, then one step
    is sound at each intermediate state along the chain. -/
theorem iterated_oneStep_chain
    (summary : LoopSummary Sub PC)
    (oneStep : State → State → Prop)
    (h_sound : ∀ s, isa.satisfies s summary.body.pc →
      oneStep s (isa.eval_sub summary.body.sub s))
    (n : ℕ) (s : State)
    (h_pcs : ∀ k, k < n → isa.satisfies ((summary.body.effect isa)^[k] s) summary.body.pc) :
    ∀ k, k < n →
      oneStep ((summary.body.effect isa)^[k] s)
              ((summary.body.effect isa)^[k + 1] s) := by
  intro k hk
  simp only [Function.iterate_succ', Function.comp]
  exact h_sound _ (h_pcs k hk)

end WhileLoop


/-! ## Practical Loop Summary Theorem

The key practical result: a loop summary produces a finite set of branches
that soundly approximates the while loop for any given iteration bound.
This connects loop summaries to the existing convergence machinery. -/

section PracticalLoop

variable {Sub PC State : Type*} [DecidableEq Sub] [DecidableEq PC]
  (isa : SymbolicISA Sub PC State)

/-- Generate the branch set for a loop summary with a given iteration bound.
    Produces one branch per possible exit point (0 to maxIter iterations). -/
def loopBranches (summary : LoopSummary Sub PC) (maxIter : ℕ) :
    Finset (Branch Sub PC) :=
  Finset.image
    (fun n => (iterateBranch isa summary.body n).compose isa ⟨isa.id_sub, summary.exits⟩)
    (Finset.range (maxIter + 1))

/-- The branch set for a loop is a superset of any smaller bound. -/
theorem loopBranches_mono (summary : LoopSummary Sub PC) (n m : ℕ) (h : n ≤ m) :
    loopBranches isa summary n ⊆ loopBranches isa summary m := by
  intro b hb
  simp only [loopBranches, Finset.mem_image, Finset.mem_range] at hb ⊢
  obtain ⟨k, hk, rfl⟩ := hb
  exact ⟨k, by omega, rfl⟩

/-- The cardinality of loop branches is bounded by the iteration bound + 1. -/
theorem loopBranches_card (summary : LoopSummary Sub PC) (maxIter : ℕ) :
    (loopBranches isa summary maxIter).card ≤ maxIter + 1 := by
  unfold loopBranches
  exact le_trans Finset.card_image_le (by simp [Finset.card_range])

omit [DecidableEq Sub] [DecidableEq PC] in
/-- Helper: boundedIter accepts n ≤ maxIter steps of assert-then-assign.
    By induction on maxIter. The 0-iteration case uses skipBehavior.
    The (m+1)-iteration case: n=0 takes the skip choice, n=k+1 takes one
    body step then applies the IH on the shifted state. -/
private theorem boundedIter_takes_n_steps
    (body : Branch Sub PC) (maxIter n : ℕ) (hn : n ≤ maxIter)
    (s : State)
    (h_pcs : ∀ k, k < n → isa.satisfies ((body.effect isa)^[k] s) body.pc) :
    CompTree.treeBehavior isa
      (.boundedIter (.seq (.assert body.pc) (.assign body.sub)) maxIter)
      s ((body.effect isa)^[n] s) := by
  induction maxIter generalizing n s with
  | zero =>
    obtain rfl : n = 0 := Nat.eq_zero_of_le_zero hn
    simp [CompTree.treeBehavior, skipBehavior]
  | succ m ih =>
    simp only [CompTree.treeBehavior]
    cases n with
    | zero =>
      left
      simp [skipBehavior]
    | succ k =>
      right
      simp only [seqBehavior]
      refine ⟨body.effect isa s, ?_, ?_⟩
      · -- One body step: assert body.pc then assign body.sub
        simp only [assertBehavior, assignBehavior]
        exact ⟨s, ⟨h_pcs 0 (Nat.zero_lt_succ k), rfl⟩,
               by simp [Branch.effect]⟩
      · -- Remaining k steps via IH on shifted state
        have iter_shift : (body.effect isa)^[k + 1] s =
            (body.effect isa)^[k] (body.effect isa s) := by
          simp [Function.iterate_succ, Function.comp]
        rw [iter_shift]
        apply ih k (by omega) (body.effect isa s)
        intro j hj
        have := h_pcs (j + 1) (by omega)
        simp only [Function.iterate_succ, Function.comp] at this
        exact this

omit [DecidableEq Sub] [DecidableEq PC] in
/-- A loop summary with bounded iterations embeds into CompTree.
    The encoding: `seq (boundedIter (seq (assert body.pc) (assign body.sub)) maxIter) (assert exits)`.
    This witnesses that bounded loops can be represented in the existing framework. -/
theorem loopSummary_bounded_embedding (summary : LoopSummary Sub PC) (maxIter : ℕ) :
    ∃ tree : CompTree Sub PC,
      ∀ s s' n, n ≤ maxIter →
        (isa.eval_sub (iterateBranch isa summary.body n).sub s = s') →
        isa.satisfies s' summary.exits →
        (∀ k, k < n → isa.satisfies ((summary.body.effect isa)^[k] s) summary.body.pc) →
        CompTree.treeBehavior isa tree s s' := by
  refine ⟨.seq (.boundedIter (.seq (.assert summary.body.pc) (.assign summary.body.sub)) maxIter)
              (.assert summary.exits), ?_⟩
  intro s s' n hn h_eval h_exits h_pcs
  -- The tree behavior is: seq (boundedIter ...) (assert exits)
  -- = ∃ mid, treeBehavior (boundedIter ...) s mid ∧ assertBehavior isa exits mid s'
  simp only [CompTree.treeBehavior, seqBehavior, assertBehavior]
  -- mid = s' = (body.effect isa)^[n] s
  have h_effect : s' = (summary.body.effect isa)^[n] s := by
    rw [← h_eval]
    exact iterateBranch_effect isa summary.body s n
  refine ⟨s', ?_, h_exits, rfl⟩
  rw [h_effect]
  exact boundedIter_takes_n_steps isa summary.body maxIter n hn s h_pcs

end PracticalLoop


/-! ## Connection to Convergence

The fundamental observation: a while loop with a loop summary can be analyzed
by the existing convergence machinery. The oracle discovers branches for each
iteration depth, and convergence is guaranteed when:
- The loop has a known maximum iteration count (reduces to boundedIter), or
- The loop is stabilizing: there exists N such that for all n ≥ N, the
  n-th iteration branch is already in the model (the state space is finite
  and the loop eventually cycles)

For practical symex (stalagmite), stubs provide the loop summary, and
re-execution with tighter stubs corresponds to refining the iteration bound
until convergence — this IS circular coinduction. -/

section Convergence

variable {Sub PC State : Type*} [DecidableEq Sub] [DecidableEq PC]
  (isa : SymbolicISA Sub PC State)

/-- Iterating a periodic function: if `f^[p] x = x` with `p > 0`,
    then `f^[n] x = f^[n % p] x`. Proof: decompose `n = n%p + p*(n/p)`
    and show `f^[p*m] x = x` by induction on `m`. -/
private theorem iterate_mod_of_periodic {α : Type*} {f : α → α} {x : α} {p : ℕ}
    (_hp : 0 < p) (h : f^[p] x = x) (n : ℕ) :
    f^[n] x = f^[n % p] x := by
  have key : ∀ m, f^[p * m] x = x := by
    intro m; induction m with
    | zero => simp
    | succ m ih => rw [Nat.mul_succ, Function.iterate_add, Function.comp_apply, h, ih]
  conv_lhs => rw [show n = n % p + p * (n / p) from (Nat.mod_add_div n p).symm]
  rw [Function.iterate_add, Function.comp_apply, key]

omit [DecidableEq Sub] [DecidableEq PC] in
/-- If the state space is finite and the loop body is deterministic
    (the substitution is an endofunction), then the loop must eventually
    cycle and the branch model stabilizes. This gives us convergence
    without knowing the iteration bound a priori.

    Proof: by pigeonhole, the orbit of any state under a deterministic
    function on a finite type must cycle within `|State| + 1` steps.
    Once it cycles, `iterate_mod_of_periodic` shows all further iterates
    land in the first `|State| + 1` values. -/
theorem finite_loop_convergence
    [Fintype State] [DecidableEq State]
    (summary : LoopSummary Sub PC) :
    ∃ maxIter,
      ∀ n, n ≥ maxIter →
        ∀ s : State, (isa.eval_sub (iterateBranch isa summary.body n).sub s) ∈
          Finset.image (fun k => isa.eval_sub (iterateBranch isa summary.body k).sub s)
            (Finset.range maxIter) := by
  use Fintype.card State + 1
  intro n hn s
  -- Convert eval_sub to iterate via iterateBranch_effect
  let f := summary.body.effect isa
  have h_iter : ∀ k, isa.eval_sub (iterateBranch isa summary.body k).sub s = f^[k] s := by
    intro k
    change Branch.effect isa (iterateBranch isa summary.body k) s = _
    exact iterateBranch_effect isa summary.body s k
  simp only [h_iter]
  -- By pigeonhole: the map (k : Fin (|State|+1)) ↦ f^[k] s has more inputs than outputs
  have h_card : Fintype.card State < Fintype.card (Fin (Fintype.card State + 1)) := by
    simp [Fintype.card_fin]
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, hij, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun (k : Fin (Fintype.card State + 1)) => f^[k.val] s) h_card
  -- WLOG i < j (they're not equal since hij)
  have i_ne_j : i ≠ j := by intro h; exact hij (Fin.ext h)
  -- Get ordered pair: a < b with f^[a] s = f^[b] s
  obtain ⟨a, b, hab, h_eq, hb⟩ : ∃ a b, a < b ∧ f^[a] s = f^[b] s ∧ b < Fintype.card State + 1 := by
    rcases Nat.lt_or_gt_of_ne i_ne_j with h | h
    · exact ⟨i, j, h, heq, hj⟩
    · exact ⟨j, i, h, heq.symm, hi⟩
  -- f^[b-a](f^[a] s) = f^[a] s, so f^[a] s is periodic with period p = b - a
  have p_pos : 0 < b - a := Nat.sub_pos_of_lt hab
  have h_periodic : f^[b - a] (f^[a] s) = f^[a] s := by
    have : f^[b] s = f^[b - a] (f^[a] s) := by
      conv_lhs => rw [show b = (b - a) + a from by omega]
      rw [Function.iterate_add, Function.comp_apply]
    rw [← this, ← h_eq]
  -- For any n, f^[n] s = f^[a + (n-a) % p] s when n ≥ a
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
  -- a + (n-a) % (b-a) < b ≤ card State + 1 = maxIter
  have h_bound : ∀ m, m ≥ a → a + (m - a) % (b - a) < Fintype.card State + 1 := by
    intro m _
    have : (m - a) % (b - a) < b - a := Nat.mod_lt _ p_pos
    omega
  -- Apply to our n
  have hn' : n ≥ a := by omega
  rw [h_reduce n hn']
  apply Finset.mem_image.mpr
  exact ⟨a + (n - a) % (b - a), Finset.mem_range.mpr (h_bound n hn'), rfl⟩

end Convergence
