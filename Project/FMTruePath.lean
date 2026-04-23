module

public import Project.FMConstruction

namespace Computability

open Classical RecursiveIn

namespace StageState

/-! ### The "visited infinitely often" predicate

A node `σ` is visited infinitely often iff for every threshold `N`, some
stage `s ≥ N` visits a node extending `σ`. This is the standard
leftmost-path criterion.
-/

/-- `σ` is visited at stage `s` if the length-`s` node visited at stage
`s` has `σ` as a prefix. -/
public def IsVisitedAt (σ : Node) (s : ℕ) : Prop :=
  Node.IsPrefix σ ((stage s).visitedNode s)

/-- `σ` is visited infinitely often during the construction. -/
public def VisitedInf (σ : Node) : Prop :=
  ∀ N, ∃ s ≥ N, IsVisitedAt σ s

/-- `σ` is visited only finitely often. -/
public def VisitedFin (σ : Node) : Prop :=
  ∃ N, ∀ s ≥ N, ¬ IsVisitedAt σ s

/-- Trichotomy: every node is either visited infinitely often or not.
Uses classical `em` since `VisitedInf` is not decidable in general. -/
lemma visitedInf_or_visitedFin (σ : Node) : VisitedInf σ ∨ VisitedFin σ := by
  rcases Classical.em (VisitedInf σ) with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    unfold VisitedInf at h
    push_neg at h
    exact h

/-- The root is visited at every stage: `[]` is a prefix of every node. -/
lemma visitedInf_root : VisitedInf ([] : Node) := fun N =>
  ⟨N, le_refl N, List.nil_prefix⟩

/-! ### The true path

The true path is the leftmost infinite path all of whose finite prefixes
are visited infinitely often. Since `false < true`, we prefer the
`false` branch whenever it is itself visited infinitely often.

We define the prefix recursively; `truePath n` is then the outcome at
level `n`.
-/

/-- The length-`n` prefix of the true path. -/
public noncomputable def truePathPrefix : ℕ → Node
  | 0     => []
  | n + 1 =>
    let σ := truePathPrefix n
    if VisitedInf (σ.extend false) then σ.extend false else σ.extend true

/-- The `n`-th outcome of the true path. -/
public noncomputable def truePath (n : ℕ) : Bool :=
  if VisitedInf ((truePathPrefix n).extend false) then false else true

@[simp] lemma truePathPrefix_zero : truePathPrefix 0 = ([] : Node) := rfl

lemma truePathPrefix_succ (n : ℕ) :
    truePathPrefix (n + 1) = (truePathPrefix n).extend (truePath n) := by
  show (if _ then _ else _) = (truePathPrefix n).extend (if _ then _ else _)
  split_ifs <;> rfl

lemma length_truePathPrefix (n : ℕ) : (truePathPrefix n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [truePathPrefix_succ]
      simp [Node.extend, ih]

/-! ### Key properties of the true path

These are the two facts that drive the correctness of the construction.
-/

/-- Every prefix of the true path is visited infinitely often. -/
lemma truePathPrefix_visitedInf (n : ℕ) : VisitedInf (truePathPrefix n) := by sorry

/-- A node strictly to the left of the true path is visited only
finitely often. "Strictly to the left" means a node of the same length
`n` that is lex-less-than `truePathPrefix n`. -/
lemma left_of_truePath_visitedFin (σ : Node)
    (hlen : σ.length = σ.length)
    (hleft : σ.lex (truePathPrefix σ.length)) :
    VisitedFin σ := by sorry

/-! ### Finite injury on the true path

The true-path strategies are never injured from stage `S` onwards.
This is the finite-injury property and follows from the fact that only
strictly-higher-priority nodes can injure. Combined with the
left-of-truePath-finite-injury lemma, each true-path node has a
stable follower and stable `acted` flag.
-/

/-- After some finite stage, the `acted` flag at `truePathPrefix n`
never changes again. -/
lemma truePath_acted_eventually_stable (n : ℕ) :
    ∃ S, ∀ s ≥ S, (stage s).acted (truePathPrefix n) =
      (stage S).acted (truePathPrefix n) := by sorry

/-- After some finite stage, the follower at `truePathPrefix n` never
changes again, and is in fact assigned. -/
lemma truePath_follower_eventually_stable (n : ℕ) :
    ∃ S x, ∀ s ≥ S, (stage s).follower (truePathPrefix n) = some x := by sorry

/-! ### Satisfaction of requirements on the true path

For each `e`:
* requirement `R_{2e}` (at level `2e`): `φ_e^B ≠ ofPred A`
* requirement `R_{2e+1}` (at level `2e+1`): `φ_e^A ≠ ofPred B`

The argument splits on `truePath (2e)` (resp. `(2e+1)`):
* If the outcome is `true`, the strategy acted: it enrolled its
  follower `x` into the diagonalizing side after observing
  `φ_e^{B_s}(x) ↓ = 0`. Use-principle preservation (ensured because
  only finitely many injuries happen) means `φ_e^B(x) = 0`, but
  `x ∈ A`, so they disagree.
* If the outcome is `false`, the strategy never acted — either because
  `φ_e^{B_s}(x) ↑` (so the reduction doesn't even compute) or returns
  `≠ 0` (so `φ_e^B(x) ≠ 0 = ofPred A x` since `x ∉ A`).
-/

/-- The strategy at `truePathPrefix (2e)` satisfies requirement `R_{2e}`. -/
lemma truePath_even_satisfies (e : ℕ) :
    ¬ ∀ x, (Code.eval (Denumerable.ofNat Code e) (ofPred BsetLim) x : Part ℕ)
             = Part.some (ofPred AsetLim x) := by sorry

/-- The strategy at `truePathPrefix (2e+1)` satisfies requirement `R_{2e+1}`. -/
lemma truePath_odd_satisfies (e : ℕ) :
    ¬ ∀ x, (Code.eval (Denumerable.ofNat Code e) (ofPred AsetLim) x : Part ℕ)
             = Part.some (ofPred BsetLim x) := by sorry

/-! ### The two non-reducibility results

Any Turing reduction `ofPred A ≤ᵀ ofPred B` is computed by some code
`e`, which is handled at the true-path node at level `2e+1`. The
satisfaction lemma above then delivers a contradiction.
-/

open scoped Computability in
/-- `A` is not Turing-reducible to `B`. -/
public lemma not_AsetLim_le_BsetLim : ¬ (ofPred AsetLim ≤ᵀ ofPred BsetLim) := by sorry

open scoped Computability in
/-- `B` is not Turing-reducible to `A`. -/
public lemma not_BsetLim_le_AsetLim : ¬ (ofPred BsetLim ≤ᵀ ofPred AsetLim) := by sorry

end StageState

end Computability
