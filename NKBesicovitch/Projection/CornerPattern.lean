/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Estimates
public import NKBesicovitch.Projection.CornerCode

/-!
# Admissible height data at one corner node

A pattern records the three parent heights, the outer and inner input
estimates, and every nondegeneracy condition needed for their code maps.
Children are labeled by an outer height and an inner height. Their first
height is the common parent height `b`.
-/

@[expose] public section

namespace NKBesicovitch.Projection

/-- Fixed geometric and analytic input data for one node of a corner tree. -/
structure CornerPattern (m : ℕ) (β : ℝ) where
  a : ℝ
  b : ℝ
  c : ℝ
  κ : ℝ
  a_ne_b : a ≠ b
  c_ne_a : c ≠ a
  c_ne_b : c ≠ b
  κ_ne_zero : κ ≠ 0
  outer : Finset ℝ
  outer_nonempty : outer.Nonempty
  inner : ℝ → Finset ℝ
  inner_nonempty : ∀ u ∈ outer, (inner u).Nonempty
  outer_ne_a : ∀ u ∈ outer, u ≠ a
  outer_ne_c : ∀ u ∈ outer, u ≠ c
  inner_ne_b : ∀ u ∈ outer, ∀ t ∈ inner u, t ≠ b
  inner_ne_a : ∀ u ∈ outer, ∀ t ∈ inner u, t ≠ a
  dual_ne_inner : ∀ u ∈ outer, ∀ t ∈ inner u,
    dualTime b a (cornerInnerCoefficient a c κ u) t ≠ t
  outer_estimate : HasProjectionEstimate m β outer
  inner_estimate : ∀ u ∈ outer, HasProjectionEstimate m β (inner u)

namespace CornerPattern

variable {m : ℕ} {β : ℝ}

/-- Child labels; the numerical child triple is `(b, t, dualTime b a sᵤ t)`. -/
noncomputable def children (P : CornerPattern m β) : Finset (ℝ × ℝ) :=
  P.outer.biUnion fun u ↦ (P.inner u).image fun t ↦ (u, t)

theorem mem_children {P : CornerPattern m β} {u t : ℝ} :
    (u, t) ∈ P.children ↔ u ∈ P.outer ∧ t ∈ P.inner u := by
  simp [children]

theorem children_nonempty (P : CornerPattern m β) : P.children.Nonempty := by
  obtain ⟨u, hu⟩ := P.outer_nonempty
  obtain ⟨t, ht⟩ := P.inner_nonempty u hu
  exact ⟨(u, t), mem_children.mpr ⟨hu, ht⟩⟩

theorem innerCoefficient_ne_zero (P : CornerPattern m β) {u : ℝ} (hu : u ∈ P.outer) :
    cornerInnerCoefficient P.a P.c P.κ u ≠ 0 :=
  cornerInnerCoefficient_ne_zero P.κ_ne_zero (P.outer_ne_a u hu) (P.outer_ne_c u hu)

theorem child_dual_ne_base (P : CornerPattern m β) {u t : ℝ} (h : (u, t) ∈ P.children) :
    dualTime P.b P.a (cornerInnerCoefficient P.a P.c P.κ u) t ≠ P.b := by
  obtain ⟨hu, ht⟩ := mem_children.mp h
  exact dualTime_ne_base P.a_ne_b.symm (P.innerCoefficient_ne_zero hu)
    (P.inner_ne_b u hu t ht) (P.inner_ne_a u hu t ht)

/-- All parent, outer, inner, and dual heights needed by this node. -/
noncomputable def times (P : CornerPattern m β) : Finset ℝ :=
  insert P.a (insert P.b (insert P.c (P.outer ∪ P.children.biUnion fun p ↦
    {p.2, dualTime P.b P.a (cornerInnerCoefficient P.a P.c P.κ p.1) p.2})))

theorem a_mem_times (P : CornerPattern m β) : P.a ∈ P.times := by simp [times]

theorem b_mem_times (P : CornerPattern m β) : P.b ∈ P.times := by simp [times]

theorem c_mem_times (P : CornerPattern m β) : P.c ∈ P.times := by simp [times]

theorem outer_subset_times (P : CornerPattern m β) : P.outer ⊆ P.times := by
  intro u hu
  simp [times, hu]

theorem inner_mem_times (P : CornerPattern m β) {u t : ℝ} (h : (u, t) ∈ P.children) :
    t ∈ P.times := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_insert_of_mem
  apply Finset.mem_insert_of_mem
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(u, t), h, by simp⟩)

theorem dual_mem_times (P : CornerPattern m β) {u t : ℝ} (h : (u, t) ∈ P.children) :
    dualTime P.b P.a (cornerInnerCoefficient P.a P.c P.κ u) t ∈ P.times := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_insert_of_mem
  apply Finset.mem_insert_of_mem
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(u, t), h, by simp⟩)

theorem times_subset (P : CornerPattern m β) {I : Set ℝ}
    (ha : P.a ∈ I) (hb : P.b ∈ I) (hc : P.c ∈ I)
    (houter : ∀ u ∈ P.outer, u ∈ I)
    (hinner : ∀ u ∈ P.outer, ∀ t ∈ P.inner u, t ∈ I)
    (hdual : ∀ u ∈ P.outer, ∀ t ∈ P.inner u,
      dualTime P.b P.a (cornerInnerCoefficient P.a P.c P.κ u) t ∈ I) :
    ∀ t ∈ P.times, t ∈ I := by
  intro t ht
  simp only [times, Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | ht | ⟨p, hp, rfl | rfl⟩
  · exact ha
  · exact hb
  · exact hc
  · exact houter _ ht
  · exact hinner _ (mem_children.mp hp).1 _ (mem_children.mp hp).2
  · exact hdual _ (mem_children.mp hp).1 _ (mem_children.mp hp).2

end CornerPattern

end NKBesicovitch.Projection
