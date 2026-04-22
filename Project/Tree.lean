module

public import Mathlib.Data.List.Infix
public import Mathlib.Data.List.Lex
public import Mathlib.Data.Vector.Defs
public import Mathlib.Data.Fintype.BigOperators

namespace Computability

/--
A node of the binary priority tree `2^<ω`. An element of `Node` is a finite
sequence of outcomes; at each level the outcome `false` denotes "waited /
did not act" and `true` denotes "acted". The empty list is the root.

Convention: `false < true`, so leftmost-first corresponds to the standard
"higher priority" ordering on strategies.
-/
public abbrev Node := List Bool

namespace Node

/-- The level of a node is its depth in the tree (= its length). -/
public abbrev level (σ : Node) : ℕ := σ.length

/-- The root node. -/
public abbrev root : Node := []

/-- Extend a node by one outcome. -/
public abbrev extend (σ : Node) (b : Bool) : Node := σ ++ [b]

/-- Restrict a node to its first `n` outcomes. -/
public abbrev take (σ : Node) (n : ℕ) : Node := List.take n σ

/-- `σ` is a (not-necessarily-strict) ancestor of `τ`. Unfolds to `List.IsPrefix`. -/
public def IsPrefix (σ τ : Node) : Prop := σ <+: τ

/-- `σ` is a strict ancestor of `τ`. -/
public def IsStrictPrefix (σ τ : Node) : Prop := σ <+: τ ∧ σ ≠ τ

/--
Lexicographic (leftmost-first) order on `Node`, inherited from the
`LinearOrder (List Bool)` instance derived from `List.Lex (· < ·)`.
-/
public def lex (σ τ : Node) : Prop := σ < τ

/--
Priority order: `σ` has higher priority than `τ` iff either `σ` is a strict
prefix of `τ` or `σ` is strictly to the left of `τ` lexicographically.
-/
public def priorityLT (σ τ : Node) : Prop := IsStrictPrefix σ τ ∨ lex σ τ

end Node

/-! ### Basic lemmas about levels and extension -/

namespace Node

@[simp] lemma level_root : root.level = 0 := rfl

@[simp] lemma level_extend (σ : Node) (b : Bool) :
    (σ.extend b).level = σ.level + 1 := by
  simp [extend, level]

@[simp] lemma take_zero (σ : Node) : σ.take 0 = root := by
  simp [take, root]

@[simp] lemma take_length (σ : Node) : σ.take σ.level = σ := by
  simp [take, level]

lemma take_level (σ : Node) (n : ℕ) (hn : n ≤ σ.level) :
    (σ.take n).level = n := by
  simp only [take, level, List.length_take]
  exact min_eq_left hn

/-! ### Prefix lemmas — thin wrappers around `List.IsPrefix`. -/

@[refl] lemma IsPrefix.refl (σ : Node) : IsPrefix σ σ := List.prefix_rfl

@[trans] lemma IsPrefix.trans {σ τ ρ : Node}
    (h1 : IsPrefix σ τ) (h2 : IsPrefix τ ρ) : IsPrefix σ ρ :=
  List.IsPrefix.trans h1 h2

lemma IsPrefix.antisymm {σ τ : Node}
    (h1 : IsPrefix σ τ) (h2 : IsPrefix τ σ) : σ = τ :=
  h1.eq_of_length (le_antisymm h1.length_le h2.length_le)

lemma root_isPrefix (σ : Node) : IsPrefix root σ := List.nil_prefix

lemma take_isPrefix (σ : Node) (n : ℕ) : IsPrefix (σ.take n) σ :=
  List.take_prefix n σ

lemma isPrefix_extend_self (σ : Node) (b : Bool) :
    IsPrefix σ (σ.extend b) := List.prefix_append σ [b]

/--
Two prefixes of a common node are comparable.
-/
lemma IsPrefix.total_of_prefix {σ τ ρ : Node}
    (h1 : IsPrefix σ ρ) (h2 : IsPrefix τ ρ) :
    IsPrefix σ τ ∨ IsPrefix τ σ := by
  sorry

/-! ### Strict prefix lemmas -/

lemma IsStrictPrefix.level_lt {σ τ : Node} (h : IsStrictPrefix σ τ) :
    σ.level < τ.level :=
  lt_of_le_of_ne h.1.length_le (fun heq => h.2 (h.1.eq_of_length heq))

lemma IsStrictPrefix.irrefl (σ : Node) : ¬ IsStrictPrefix σ σ :=
  fun h => h.2 rfl

@[trans] lemma IsStrictPrefix.trans {σ τ ρ : Node}
    (h1 : IsStrictPrefix σ τ) (h2 : IsStrictPrefix τ ρ) :
    IsStrictPrefix σ ρ :=
  ⟨h1.1.trans h2.1, fun heq => by
    have hlt := h1.level_lt.trans h2.level_lt
    rw [heq] at hlt
    exact lt_irrefl _ hlt⟩

/-! ### Lex order lemmas — via the `LinearOrder (List Bool)` instance. -/

lemma lex_irrefl (σ : Node) : ¬ lex σ σ := lt_irrefl σ

@[trans] lemma lex_trans {σ τ ρ : Node}
    (h1 : lex σ τ) (h2 : lex τ ρ) : lex σ ρ := lt_trans h1 h2

/--
Trichotomy for `lex`: for any two nodes, at least one of equality, strict
prefix (either direction), or lex comparability holds. Note this is
weaker than the full priority trichotomy below — it handles both the
lex case and the prefix case via the `LinearOrder` instance's
`lt_trichotomy`, but doesn't split the prefix case.
-/
lemma lex_trichotomy (σ τ : Node) :
    σ = τ ∨ IsStrictPrefix σ τ ∨ IsStrictPrefix τ σ ∨ lex σ τ ∨ lex τ σ := by
  sorry

/-! ### Priority order lemmas -/

lemma priorityLT_irrefl (σ : Node) : ¬ priorityLT σ σ := by
  rintro (h | h)
  · exact IsStrictPrefix.irrefl σ h
  · exact lex_irrefl σ h

@[trans] lemma priorityLT_trans {σ τ ρ : Node}
    (h1 : priorityLT σ τ) (h2 : priorityLT τ ρ) : priorityLT σ ρ := by
  sorry

/--
Trichotomy for the priority order.
-/
lemma priorityLT_trichotomy (σ τ : Node) :
    σ = τ ∨ priorityLT σ τ ∨ priorityLT τ σ := by
  sorry

/-! ### Decidability -/

instance : DecidableEq Node := inferInstanceAs (DecidableEq (List Bool))

instance (σ τ : Node) : Decidable (IsPrefix σ τ) :=
  inferInstanceAs (Decidable (σ <+: τ))

instance (σ τ : Node) : Decidable (IsStrictPrefix σ τ) := by
  unfold IsStrictPrefix; infer_instance

instance (σ τ : Node) : Decidable (lex σ τ) :=
  inferInstanceAs (Decidable (σ < τ))

instance (σ τ : Node) : Decidable (priorityLT σ τ) := by
  unfold priorityLT; infer_instance

/-! ### Finiteness at each level -/

/--
There are exactly `2^n` nodes of level `n`. Identifying `{σ : Node // σ.level = n}`
with `List.Vector Bool n`, this is `Fintype.card_vector`.
-/
lemma card_nodes_of_level (n : ℕ) :
    Fintype.card (List.Vector Bool n) = 2 ^ n := by
  rw [card_vector]; rfl

end Node

end Computability
