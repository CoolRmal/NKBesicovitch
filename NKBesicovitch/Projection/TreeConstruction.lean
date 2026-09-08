/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CornerTree
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Sigma

/-!
# Constructing finite corner trees

A terminal triple is a depth-zero tree. Grafting one admissible pattern
onto a finite collection of matching child trees adds one level. Thus
availability of patterns at every distinct triple gives trees of every
finite depth, with no projection assumptions imposed on terminal nodes.
-/

@[expose] public section

namespace NKBesicovitch.Projection.CornerTree

variable {m J : ℕ} {β : ℝ}

/-- A terminal tree with its prescribed distinct heights. -/
def leaf {a b c : ℝ} (hba : b ≠ a) (hca : c ≠ a) (hcb : c ≠ b) : CornerTree m β 0 where
  Node := Unit
  nodeFintype := inferInstance
  level := fun _ ↦ 0
  level_le := fun _ ↦ le_rfl
  a := fun _ ↦ a
  b := fun _ ↦ b
  c := fun _ ↦ c
  b_ne_a := fun _ ↦ hba
  c_ne_a := fun _ ↦ hca
  c_ne_b := fun _ ↦ hcb
  root := ()
  root_level := rfl
  pattern := fun _ h ↦ (Nat.not_lt_zero _ h).elim
  pattern_a := fun _ h ↦ (Nat.not_lt_zero _ h).elim
  pattern_b := fun _ h ↦ (Nat.not_lt_zero _ h).elim
  pattern_c := fun _ h ↦ (Nat.not_lt_zero _ h).elim
  child := fun _ h ↦ (Nat.not_lt_zero _ h).elim
  child_level := fun _ h ↦ (Nat.not_lt_zero _ h).elim
  child_a := fun _ h ↦ (Nat.not_lt_zero _ h).elim
  child_b := fun _ h ↦ (Nat.not_lt_zero _ h).elim
  child_c := fun _ h ↦ (Nat.not_lt_zero _ h).elim

/-- Add a root pattern above child trees with the prescribed inner-code triples. -/
noncomputable def graft (P : CornerPattern m β) (B : P.children → CornerTree m β J)
    (ha : ∀ u, (B u).a (B u).root = P.b)
    (hb : ∀ u, (B u).b (B u).root = u.val.2)
    (hc : ∀ u, (B u).c (B u).root =
      dualTime P.b P.a (cornerInnerCoefficient P.a P.c P.κ u.val.1) u.val.2) :
    CornerTree m β (J + 1) where
  Node := Unit ⊕ Σ u : P.children, (B u).Node
  nodeFintype := inferInstance
  level := Sum.elim (fun _ ↦ 0) (fun v ↦ (B v.1).level v.2 + 1)
  level_le := by
    rintro (_ | ⟨u, v⟩)
    · exact Nat.zero_le _
    · exact Nat.succ_le_succ ((B u).level_le v)
  a := Sum.elim (fun _ ↦ P.a) (fun v ↦ (B v.1).a v.2)
  b := Sum.elim (fun _ ↦ P.b) (fun v ↦ (B v.1).b v.2)
  c := Sum.elim (fun _ ↦ P.c) (fun v ↦ (B v.1).c v.2)
  b_ne_a := by
    rintro (_ | ⟨u, v⟩)
    · exact P.a_ne_b.symm
    · exact (B u).b_ne_a v
  c_ne_a := by
    rintro (_ | ⟨u, v⟩)
    · exact P.c_ne_a
    · exact (B u).c_ne_a v
  c_ne_b := by
    rintro (_ | ⟨u, v⟩)
    · exact P.c_ne_b
    · exact (B u).c_ne_b v
  root := Sum.inl ()
  root_level := rfl
  pattern := by
    rintro (_ | ⟨u, v⟩) h
    · exact P
    · exact (B u).pattern v (Nat.lt_of_succ_lt_succ h)
  pattern_a := by
    rintro (_ | ⟨u, v⟩) h
    · rfl
    · exact (B u).pattern_a v _
  pattern_b := by
    rintro (_ | ⟨u, v⟩) h
    · rfl
    · exact (B u).pattern_b v _
  pattern_c := by
    rintro (_ | ⟨u, v⟩) h
    · rfl
    · exact (B u).pattern_c v _
  child := by
    rintro (_ | ⟨u, v⟩) h z
    · exact Sum.inr ⟨z, (B z).root⟩
    · exact Sum.inr ⟨u, (B u).child v (Nat.lt_of_succ_lt_succ h) z⟩
  child_level := by
    rintro (_ | ⟨u, v⟩) h z
    · exact congrArg (· + 1) (B z).root_level
    · exact congrArg (· + 1) ((B u).child_level v _ z)
  child_a := by
    rintro (_ | ⟨u, v⟩) h z
    · exact ha z
    · exact (B u).child_a v _ z
  child_b := by
    rintro (_ | ⟨u, v⟩) h z
    · exact hb z
    · exact (B u).child_b v _ z
  child_c := by
    rintro (_ | ⟨u, v⟩) h z
    · exact hc z
    · exact (B u).child_c v _ z

theorem graft_times_subset (P : CornerPattern m β) (B : P.children → CornerTree m β J)
    (ha : ∀ u, (B u).a (B u).root = P.b)
    (hb : ∀ u, (B u).b (B u).root = u.val.2)
    (hc : ∀ u, (B u).c (B u).root =
      dualTime P.b P.a (cornerInnerCoefficient P.a P.c P.κ u.val.1) u.val.2)
    {I : Set ℝ} (hP : ∀ t ∈ P.times, t ∈ I)
    (hB : ∀ u, ∀ t ∈ (B u).times, t ∈ I) :
    ∀ t ∈ (graft P B ha hb hc).times, t ∈ I := by
  apply times_subset
  · rintro (_ | ⟨u, v⟩)
    · exact hP _ P.a_mem_times
    · exact hB u _ ((B u).a_mem_times v)
  · rintro (_ | ⟨u, v⟩)
    · exact hP _ P.b_mem_times
    · exact hB u _ ((B u).b_mem_times v)
  · rintro (_ | ⟨u, v⟩)
    · exact hP _ P.c_mem_times
    · exact hB u _ ((B u).c_mem_times v)
  · rintro (_ | ⟨u, v⟩) h t ht
    · exact hP t ht
    · exact hB u t ((B u).pattern_times_subset v (Nat.lt_of_succ_lt_succ h) ht)

theorem exists_of_patterns
    (hP : ∀ a b c : ℝ, b ≠ a → c ≠ a → c ≠ b →
      ∃ P : CornerPattern m β, P.a = a ∧ P.b = b ∧ P.c = c)
    (J : ℕ) (a b c : ℝ) (hba : b ≠ a) (hca : c ≠ a) (hcb : c ≠ b) :
    ∃ T : CornerTree m β J, T.a T.root = a ∧ T.b T.root = b ∧ T.c T.root = c := by
  classical
  induction J generalizing a b c with
  | zero => exact ⟨leaf hba hca hcb, rfl, rfl, rfl⟩
  | succ J ih =>
    obtain ⟨P, ha, hb, hc⟩ := hP a b c hba hca hcb
    have hchild (u : P.children) : ∃ T : CornerTree m β J,
        T.a T.root = P.b ∧ T.b T.root = u.val.2 ∧ T.c T.root =
          dualTime P.b P.a (cornerInnerCoefficient P.a P.c P.κ u.val.1) u.val.2 := by
      obtain ⟨hu, ht⟩ := CornerPattern.mem_children.mp u.property
      exact ih _ _ _ (P.inner_ne_b _ hu _ ht) (P.child_dual_ne_base u.property)
        (P.dual_ne_inner _ hu _ ht)
    choose B hBa hBb hBc using hchild
    exact ⟨graft P B hBa hBb hBc, ha, hb, hc⟩

end NKBesicovitch.Projection.CornerTree
