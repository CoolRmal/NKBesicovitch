/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerPattern

/-!
# Finite admissible corner trees

Nodes have separate finite labels even when their numerical heights agree.
Each nonterminal node carries a corner pattern, and each of its children
has exactly the triple prescribed by the inner-code identity. Terminal
nodes need only three distinct heights, with no input projection estimate.
-/

@[expose] public section

namespace NKBesicovitch.Projection

/-- A finite labeled height tree whose nonterminal nodes carry admissible corner patterns. -/
structure CornerTree (m : ℕ) (β : ℝ) (J : ℕ) where
  Node : Type
  nodeFintype : Fintype Node
  level : Node → ℕ
  level_le : ∀ v, level v ≤ J
  a : Node → ℝ
  b : Node → ℝ
  c : Node → ℝ
  b_ne_a : ∀ v, b v ≠ a v
  c_ne_a : ∀ v, c v ≠ a v
  c_ne_b : ∀ v, c v ≠ b v
  root : Node
  root_level : level root = 0
  pattern : ∀ v, level v < J → CornerPattern m β
  pattern_a : ∀ v h, (pattern v h).a = a v
  pattern_b : ∀ v h, (pattern v h).b = b v
  pattern_c : ∀ v h, (pattern v h).c = c v
  child : ∀ v h, (pattern v h).children → Node
  child_level : ∀ v h u, level (child v h u) = level v + 1
  child_a : ∀ v h u, a (child v h u) = b v
  child_b : ∀ v h u, b (child v h u) = u.val.2
  child_c : ∀ v h u, c (child v h u) =
    dualTime (b v) (a v)
      (cornerInnerCoefficient (a v) (c v) (pattern v h).κ u.val.1) u.val.2

attribute [instance] CornerTree.nodeFintype

namespace CornerTree

variable {m J : ℕ} {β : ℝ}

/-- Every height used in the tree, including terminal triples and all input patterns. -/
noncomputable def times (T : CornerTree m β J) : Finset ℝ :=
  Finset.univ.biUnion fun v ↦ {T.a v, T.b v, T.c v} ∪
    if h : T.level v < J then (T.pattern v h).times else ∅

theorem a_mem_times (T : CornerTree m β J) (v : T.Node) : T.a v ∈ T.times := by
  classical
  exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, Finset.mem_union_left _ (by simp)⟩

theorem b_mem_times (T : CornerTree m β J) (v : T.Node) : T.b v ∈ T.times := by
  classical
  exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, Finset.mem_union_left _ (by simp)⟩

theorem c_mem_times (T : CornerTree m β J) (v : T.Node) : T.c v ∈ T.times := by
  classical
  exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, Finset.mem_union_left _ (by simp)⟩

theorem times_nonempty (T : CornerTree m β J) : T.times.Nonempty :=
  ⟨T.a T.root, T.a_mem_times T.root⟩

theorem pattern_times_subset (T : CornerTree m β J) (v : T.Node) (h : T.level v < J) :
    (T.pattern v h).times ⊆ T.times := by
  classical
  intro t ht
  exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _,
    Finset.mem_union_right _ (by simpa only [dite_eq_left h] using ht)⟩

end CornerTree

end NKBesicovitch.Projection
