module

public import Mathlib.Computability.Halting
public import Project.FMStage
public import Project.OracleCode

namespace Computability

open RecursiveIn Code

/--
Convert a decidable predicate `α → Prop` into an indicator function `α → ℕ`,
returning `1` on satisfying elements and `0` elsewhere.
-/
public def ofPred {α} (p : α → Prop) [∀ a, Decidable (p a)] : α → ℕ :=
  fun a => (decide (p a)).toNat

/--
Turn a finite approximation of a set into an oracle. The oracle returns
`1` on members of `F` and `0` elsewhere, so it agrees with `ofPred` on
members of `F`.
-/
public def finsetOracle (F : Finset ℕ) : ℕ →. ℕ :=
  fun n => Part.some (if n ∈ F then 1 else 0)

namespace StageState

/--
Process the strategy at node `σ` with computation budget `s`.

* If `σ` has already acted, do nothing.
* If `σ` has no follower, assign a fresh one.
* Otherwise, run `evaln` on the opponent-side oracle with budget `s`
  against the code indexed by `σ.level / 2`. If it converges to `0`,
  `σ` *acts*: enroll the follower on its own side, mark `σ` as acted,
  and injure all lower-priority strategies via `initializeBelow`.

The parity of `σ.level` selects which requirement is being handled:
* Even level `2e` → `R_{2e}`: diagonalize `A` against `φ_e^B`, so the
  oracle is `B` and a hit enrolls into `A`.
* Odd level `2e+1` → `R_{2e+1}`: symmetric.
-/
public noncomputable def stepStrategy (st : StageState) (σ : Node) (s : ℕ) :
    StageState :=
  if st.acted σ then st
  else match st.follower σ with
    | none => st.setFollower σ st.freshBound
    | some x =>
      let c : Code := Denumerable.ofNat Code (σ.level / 2)
      let oracle : ℕ →. ℕ :=
        if σ.level % 2 = 0 then finsetOracle st.B else finsetOracle st.A
      match Code.evaln oracle s c x with
      | some 0 =>
          let st₁ := st.markActed σ
          let st₂ :=
            if σ.level % 2 = 0 then st₁.enrollA x else st₁.enrollB x
          st₂.initializeBelow σ
      | _ => st

/--
One full stage of the construction: walk the tree from the root down to
the level-`s` node visited in the current state, giving every strategy
on the walk a chance to act with budget `s`.

The walk is computed incrementally: after each `stepStrategy` call, the
accumulator's `acted` flag may have changed, so the next `visitedNode`
call consults the updated state. This matches the informal description
"walk down the tree using current guesses, process each strategy you
visit".
-/
public noncomputable def stageStep (st : StageState) (s : ℕ) : StageState :=
  (List.range (s + 1)).foldl
    (fun acc k => acc.stepStrategy (acc.visitedNode k) s) st

/-- The stage function, starting from the empty state. -/
public noncomputable def stage : ℕ → StageState
  | 0     => empty
  | s + 1 => stageStep (stage s) s

@[simp] lemma stage_zero : stage 0 = empty := rfl

lemma stage_succ (s : ℕ) : stage (s + 1) = stageStep (stage s) s := rfl

/-! ### Monotonicity of the stage -/

/-- `stepStrategy` only grows `A` and `B`. -/
lemma le_stepStrategy (st : StageState) (σ : Node) (s : ℕ) :
    st ≤ st.stepStrategy σ s := by sorry

/-- `stageStep` only grows `A` and `B`. -/
lemma le_stageStep (st : StageState) (s : ℕ) :
    st ≤ st.stageStep s := by sorry

/-- `A` and `B` are monotone across stages. -/
lemma stage_mono : Monotone stage := by sorry

/-! ### The enumerated sets

These are the final RE predicates produced by the construction, obtained
as the union of all stage approximations.
-/

/-- The RE predicate `A` enumerated by the construction. -/
public def AsetLim : ℕ → Prop := fun x => ∃ s, x ∈ (stage s).A

/-- The RE predicate `B` enumerated by the construction. -/
public def BsetLim : ℕ → Prop := fun x => ∃ s, x ∈ (stage s).B

/-- Membership in `AsetLim` is witnessed by membership in some stage. -/
lemma AsetLim_iff (x : ℕ) : AsetLim x ↔ ∃ s, x ∈ (stage s).A := Iff.rfl

/-- Membership in `BsetLim` is witnessed by membership in some stage. -/
lemma BsetLim_iff (x : ℕ) : BsetLim x ↔ ∃ s, x ∈ (stage s).B := Iff.rfl

/-! ### Computability enumerability (RE-ness)

These reduce to the primitive-recursiveness of `stage` as a function
`ℕ → StageState`, which in turn relies on `primrec_evaln` from
`Project.OracleCode`. The state encoding (`Finset ℕ`, the two
node-indexed functions with finite support) needs to be shown primrec;
this is bookkeeping, not mathematical content.
-/

/-- `AsetLim` is RE. -/
public lemma rePred_AsetLim : REPred AsetLim := by sorry

/-- `BsetLim` is RE. -/
public lemma rePred_BsetLim : REPred BsetLim := by sorry

end StageState

end Computability
