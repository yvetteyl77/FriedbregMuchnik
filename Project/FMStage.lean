module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Max
public import Project.Tree

namespace Computability

open Node

/--
State of the Friedberg-Muchnik construction after a finite number of
stages. Tracks:

* `A`, `B`   : the two RE approximations built so far.
* `follower` : the current follower (candidate witness) assigned to each
               strategy node, or `none` if unassigned.
* `acted`    : which nodes have already enumerated their follower.
* `support`  : a finite set of nodes outside of which the state is trivial
               (no follower, not acted). This ensures `StageState` has a
               finite description at every stage.
-/
public structure StageState where
  A : Finset ℕ
  B : Finset ℕ
  follower : Node → Option ℕ
  acted : Node → Bool
  support : Finset Node
  support_spec : ∀ σ ∉ support, follower σ = none ∧ acted σ = false

namespace StageState

/-- The empty / initial state: nothing enumerated, no followers, nothing acted. -/
public def empty : StageState where
  A := ∅
  B := ∅
  follower := fun _ => none
  acted := fun _ => false
  support := ∅
  support_spec := by intro σ _; exact ⟨rfl, rfl⟩

@[simp] lemma empty_A : empty.A = ∅ := rfl
@[simp] lemma empty_B : empty.B = ∅ := rfl
@[simp] lemma empty_follower (σ : Node) : empty.follower σ = none := rfl
@[simp] lemma empty_acted (σ : Node) : empty.acted σ = false := rfl

/-! ### Enrollment operations

These are the primitive moves the construction will compose in `stageStep`.
Each returns a new state with the appropriate book-keeping update.
-/

/-- Add `x` to the set `A`. -/
public def enrollA (st : StageState) (x : ℕ) : StageState :=
  { st with A := insert x st.A }

/-- Add `x` to the set `B`. -/
public def enrollB (st : StageState) (x : ℕ) : StageState :=
  { st with B := insert x st.B }

/-- Assign a follower `x` to node `σ`. Overwrites any existing follower. -/
public def setFollower (st : StageState) (σ : Node) (x : ℕ) : StageState where
  A := st.A
  B := st.B
  follower := Function.update st.follower σ (some x)
  acted := st.acted
  support := insert σ st.support
  support_spec := by
    intro τ hτ
    have hτσ : τ ≠ σ := fun h => hτ (h ▸ Finset.mem_insert_self σ st.support)
    have hτsup : τ ∉ st.support :=
      fun h => hτ (Finset.mem_insert_of_mem h)
    refine ⟨?_, ?_⟩
    · simp [Function.update_of_ne hτσ, (st.support_spec τ hτsup).1]
    · exact (st.support_spec τ hτsup).2

/-- Clear the follower at `σ`. -/
public def clearFollower (st : StageState) (σ : Node) : StageState where
  A := st.A
  B := st.B
  follower := Function.update st.follower σ none
  acted := st.acted
  support := st.support
  support_spec := by
    intro τ hτ
    by_cases hτσ : τ = σ
    · subst hτσ
      refine ⟨?_, (st.support_spec τ hτ).2⟩
      simp [Function.update_self]
    · exact ⟨by simp [Function.update_of_ne hτσ, (st.support_spec τ hτ).1],
            (st.support_spec τ hτ).2⟩

/-- Mark `σ` as having acted. -/
public def markActed (st : StageState) (σ : Node) : StageState where
  A := st.A
  B := st.B
  follower := st.follower
  acted := Function.update st.acted σ true
  support := insert σ st.support
  support_spec := by
    intro τ hτ
    have hτσ : τ ≠ σ := fun h => hτ (h ▸ Finset.mem_insert_self σ st.support)
    have hτsup : τ ∉ st.support :=
      fun h => hτ (Finset.mem_insert_of_mem h)
    refine ⟨(st.support_spec τ hτsup).1, ?_⟩
    simp [Function.update_of_ne hτσ, (st.support_spec τ hτsup).2]

/--
Initialize every node of strictly lower priority than `σ`: drop their
followers and reset their `acted` flag. This is the "injury" step used
when `σ` acts and thereby invalidates the work of lower-priority
strategies.
-/
public def initializeBelow (st : StageState) (σ : Node) : StageState where
  A := st.A
  B := st.B
  follower := fun τ => if σ.priorityLT τ then none else st.follower τ
  acted := fun τ => if σ.priorityLT τ then false else st.acted τ
  support := st.support.filter (fun τ => ¬ σ.priorityLT τ)
  support_spec := by
    intro τ hτ
    by_cases hpτ : σ.priorityLT τ
    · exact ⟨by simp [hpτ], by simp [hpτ]⟩
    · have hτsup : τ ∉ st.support := fun h =>
        hτ (Finset.mem_filter.mpr ⟨h, hpτ⟩)
      exact ⟨by simp [hpτ, (st.support_spec τ hτsup).1],
             by simp [hpτ, (st.support_spec τ hτsup).2]⟩

/-! ### Monotonicity predicates -/

/-- `st₁` is a prefix of `st₂` in the enrollment sense: the RE sets have
only grown. -/
public abbrev LE (st₁ st₂ : StageState) : Prop :=
  st₁.A ⊆ st₂.A ∧ st₁.B ⊆ st₂.B

public instance : Preorder StageState where
  le := LE
  le_refl st := ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
  le_trans _ _ _ h1 h2 :=
    ⟨Finset.Subset.trans h1.1 h2.1, Finset.Subset.trans h1.2 h2.2⟩

lemma le_of_enrollA (st : StageState) (x : ℕ) : st ≤ st.enrollA x :=
  ⟨Finset.subset_insert _ _, Finset.Subset.refl _⟩

lemma le_of_enrollB (st : StageState) (x : ℕ) : st ≤ st.enrollB x :=
  ⟨Finset.Subset.refl _, Finset.subset_insert _ _⟩

lemma le_of_setFollower (st : StageState) (σ : Node) (x : ℕ) :
    st ≤ st.setFollower σ x :=
  ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩

lemma le_of_clearFollower (st : StageState) (σ : Node) :
    st ≤ st.clearFollower σ :=
  ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩

lemma le_of_markActed (st : StageState) (σ : Node) :
    st ≤ st.markActed σ :=
  ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩

lemma le_of_initializeBelow (st : StageState) (σ : Node) :
    st ≤ st.initializeBelow σ :=
  ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩

/-! ### Fresh-follower witness

At every stage we need a natural number larger than any follower seen so
far and any element of `A ∪ B`, to pick a fresh follower when needed.
This keeps followers disjoint from already-enumerated elements.
-/

/-- An upper bound on all "live" natural numbers in the state: strictly
greater than every enrolled element and every current follower. Uses
`Finset.sup` with `id` (which returns `0` on the empty finset), adding
the three bounds together to get a conservative but simple estimate. -/
public def freshBound (st : StageState) : ℕ :=
  st.A.sup id + st.B.sup id +
    st.support.sup (fun σ => (st.follower σ).getD 0) + 1

lemma freshBound_gt_A {st : StageState} {x : ℕ} (hx : x ∈ st.A) :
    x < st.freshBound := by
  have h : x ≤ st.A.sup id := Finset.le_sup (f := id) hx
  unfold freshBound; omega

lemma freshBound_gt_B {st : StageState} {x : ℕ} (hx : x ∈ st.B) :
    x < st.freshBound := by
  have h : x ≤ st.B.sup id := Finset.le_sup (f := id) hx
  unfold freshBound; omega

lemma freshBound_gt_follower {st : StageState} {σ : Node} {x : ℕ}
    (hx : st.follower σ = some x) : x < st.freshBound := by
  have hσsup : σ ∈ st.support := by
    by_contra h
    rw [(st.support_spec σ h).1] at hx
    cases hx
  have hle : x ≤ st.support.sup (fun σ => (st.follower σ).getD 0) := by
    have := Finset.le_sup (f := fun σ => (st.follower σ).getD 0) hσsup
    simp [hx] at this
    exact this
  unfold freshBound; omega

/-! ### The visited node at a given stage

The "visited node" at stage `s` is the length-`s` node obtained by walking
from the root and taking outcome `true` at any node already marked acted
(in the current state) and `false` otherwise. This is the node whose
strategy gets to act at stage `s`.
-/

/-- Walk of length `s` down the tree guided by `st.acted`. -/
public def visitedNode (st : StageState) : ℕ → Node
  | 0     => Node.root
  | s + 1 =>
    let σ := visitedNode st s
    σ.extend (st.acted σ)

@[simp] lemma visitedNode_zero (st : StageState) :
    st.visitedNode 0 = Node.root := rfl

@[simp] lemma level_visitedNode (st : StageState) (s : ℕ) :
    (st.visitedNode s).level = s := by
  induction s with
  | zero => rfl
  | succ s ih => simp [visitedNode, Node.extend, Node.level, ih]

/-- The visited node at stage `s` is a prefix of the visited node at any
later stage, *provided the state's `acted` flag is preserved* on the
relevant prefix. (This hypothesis will be discharged in
`FriedbergMuchnik.lean` using the finite-injury lemma.) -/
lemma visitedNode_isPrefix_of_acted_stable (st st' : StageState) (s t : ℕ)
    (hst : s ≤ t)
    (hstable : ∀ k < s, st.acted (st.visitedNode k) = st'.acted (st.visitedNode k)) :
    IsPrefix (st.visitedNode s) (st'.visitedNode t) := by sorry

end StageState

end Computability
