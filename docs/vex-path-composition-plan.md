# VEX Path Composition Plan

Goal: make the fixed-path extractibility theorem compositional.

## Batch #1 target

Prove that extraction commutes with path composition up to semantic model equivalence.

Concretely, for fixed lifted VEX block paths `blocks₁` and `blocks₂`, we want:

1. A concrete path append law.
2. A symbolic path append law.
3. A state-level equivalence theorem between:
   - `composeSummaryFinsets (lowerBlockPathSummaries blocks₁) (lowerBlockPathSummaries blocks₂)`
   - `lowerBlockPathSummaries (blocks₁ ++ blocks₂)`
4. An observation-level corollary via `VexModelEqState -> VexModelEq`.

## Expected theorem ladder

### Step 1: concrete append

```lean
theorem execBlockPath_append
  (blocks₁ blocks₂ : List (Block Reg)) (input : ConcreteState Reg) :
  execBlockPath (blocks₁ ++ blocks₂) input =
    Finset.biUnion (execBlockPath blocks₁ input) (fun mid => execBlockPath blocks₂ mid)
```

### Step 2: symbolic append

```lean
theorem lowerBlockPathSummaries_append
  (blocks₁ blocks₂ : List (Block Reg)) :
  lowerBlockPathSummaries (blocks₁ ++ blocks₂) =
    composeSummaryFinsets (lowerBlockPathSummaries blocks₁) (lowerBlockPathSummaries blocks₂)
```

### Step 3: executable/set-level composition

```lean
theorem summarySuccs_lowerBlockPathSummaries_append_eq
  (blocks₁ blocks₂ : List (Block Reg)) (input : ConcreteState Reg) :
  summarySuccs (composeSummaryFinsets
      (lowerBlockPathSummaries blocks₁)
      (lowerBlockPathSummaries blocks₂)) input =
    summarySuccs (lowerBlockPathSummaries (blocks₁ ++ blocks₂)) input
```
```

This should follow from:
- `summarySuccs_composeSummaryFinsets`
- `summarySuccs_lowerBlockPathSummaries_eq_execBlockPath`
- `execBlockPath_append`
- `lowerBlockPathSummaries_append`

### Step 4: semantic/model-level theorem

```lean
theorem lowerBlockPathSummaries_append_modelEqState
  (Relevant : ConcreteState Reg → Prop)
  (blocks₁ blocks₂ : List (Block Reg)) :
  VexModelEqState Relevant
    (composeSummaryFinsets
      (lowerBlockPathSummaries blocks₁)
      (lowerBlockPathSummaries blocks₂))
    (lowerBlockPathSummaries (blocks₁ ++ blocks₂))
```

### Step 5: extractibility corollary

```lean
theorem extractiblePathModel_compose
  (Relevant : ConcreteState Reg → Prop)
  (observe : ConcreteState Reg → Obs)
  (blocks₁ blocks₂ : List (Block Reg)) :
  VexModelEq Relevant observe
    (composeSummaryFinsets
      (lowerBlockPathSummaries blocks₁)
      (lowerBlockPathSummaries blocks₂))
    (lowerBlockPathSummaries (blocks₁ ++ blocks₂))
```

This should be an immediate transport from the state-level theorem.

## Commit shape

1. `docs`: record the batch #1 plan
2. `theory`: add concrete and symbolic path append lemmas
3. `theory`: add state-level and observation-level path composition theorems

Build stays green after each commit.
