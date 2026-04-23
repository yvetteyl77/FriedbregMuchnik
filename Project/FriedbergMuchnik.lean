module

public import Mathlib.Computability.Halting
public import Mathlib.Data.List.GetD
public import Project.OracleCode
public import Project.Queries
public import Project.Substitute
public import Project.PartrecCode
public import Project.FMTruePath

namespace Computability

open RecursiveIn Denumerable StageState

-- TODO: Why are the following instances not in mathlib?

instance {α} [LE α] [DecidableLE α] : DecidableLE (Option α) := fun a b => by
  cases a <;> cases b <;> simp <;> infer_instance

instance {α} [LT α] [DecidableLT α] : DecidableLT (Option α) := fun a b => by
  cases a <;> cases b <;> simp <;> infer_instance

open Classical in
/--
The **Friedberg-Muchnik Theorem**: there exist two Turing-incomparable RE predicates.

Witnesses are `AsetLim` and `BsetLim` from the tree-method construction
in `Project.FMConstruction`. The four required facts are the RE-ness
lemmas in `FMConstruction` and the non-reducibility lemmas in
`FMTruePath`.
-/
theorem exists_incomparable_rePreds :
    ∃ p q : ℕ → Prop, REPred p ∧ REPred q ∧
      ¬(ofPred p ≤ᵀ ofPred q) ∧ ¬(ofPred q ≤ᵀ ofPred p) :=
  ⟨AsetLim, BsetLim, rePred_AsetLim, rePred_BsetLim,
   not_AsetLim_le_BsetLim, not_BsetLim_le_AsetLim⟩

end Computability
