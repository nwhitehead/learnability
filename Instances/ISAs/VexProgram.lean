import Mathlib.Data.Fintype.Basic
import Instances.ISAs.VexBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

/-- A lifted VEX program as a block map keyed by concrete instruction pointer. -/
structure Program (Reg : Type) where
  blocks : UInt64 → Option (Block Reg)

/-- Read the current instruction pointer from the concrete state. -/
def currentIp {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (ip_reg : Reg) (state : ConcreteState Reg) : UInt64 :=
  state.read ip_reg

/-- Fetch the block at the state's current instruction pointer. -/
def fetchBlock {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (program : Program Reg) (ip_reg : Reg) (state : ConcreteState Reg) : Option (Block Reg) :=
  program.blocks (currentIp ip_reg state)

/-- Concrete one-step semantics for a fetched VEX block. -/
def ProgramStep {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (program : Program Reg) (ip_reg : Reg)
    (input output : ConcreteState Reg) : Prop :=
  ∃ block,
    fetchBlock program ip_reg input = some block ∧
    SyntaxDenotes block input output

/-- One-step semantics through lowered summary families for a fetched VEX block. -/
def ProgramSummaryStep {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (program : Program Reg) (ip_reg : Reg)
    (input output : ConcreteState Reg) : Prop :=
  ∃ block,
    fetchBlock program ip_reg input = some block ∧
    LoweredDenotes block input output

/-- Fetched concrete block execution and fetched lowered-summary execution coincide. -/
theorem programStep_iff_summaryStep {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (program : Program Reg) (ip_reg : Reg) (input output : ConcreteState Reg) :
    ProgramStep program ip_reg input output ↔
      ProgramSummaryStep program ip_reg input output := by
  constructor
  · intro h
    rcases h with ⟨block, hFetch, hStep⟩
    exact ⟨block, hFetch, (syntax_iff_lowered block input output).mp hStep⟩
  · intro h
    rcases h with ⟨block, hFetch, hStep⟩
    exact ⟨block, hFetch, (syntax_iff_lowered block input output).mpr hStep⟩

end VexISA
