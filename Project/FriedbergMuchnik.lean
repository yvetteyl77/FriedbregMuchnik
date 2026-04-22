module

public import Mathlib.Computability.Halting
public import Mathlib.Data.List.GetD
public import Project.OracleCode
public import Project.Queries
public import Project.Substitute
public import Project.PartrecCode

namespace Computability

open RecursiveIn Denumerable

-- TODO: Why are the following instances not in mathlib?

instance {α} [LE α] [DecidableLE α] : DecidableLE (Option α) := fun a b => by
  cases a <;> cases b <;> simp <;> infer_instance

instance {α} [LT α] [DecidableLT α] : DecidableLT (Option α) := fun a b => by
  cases a <;> cases b <;> simp <;> infer_instance

/--
Convert a predicate `α → Prop` into an indicator function `α → ℕ`.
-/
def ofPred {α} (p : α → Prop) [∀ a, Decidable (p a)] : α → ℕ :=
  fun a => (decide (p a)).toNat

open Classical in
/--
The **Friedberg-Muchnik Theorem**: there exist two Turing-incomparable RE predicates.
-/
theorem exists_incomparable_rePreds : ∃ p q : ℕ → Prop, REPred p ∧ REPred q ∧ ¬(ofPred p ≤ᵀ ofPred q) ∧ ¬(ofPred q ≤ᵀ ofPred p) := by
  sorry

end Computability
