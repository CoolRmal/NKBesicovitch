/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Incidence
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring

/-!
# Pair codes and dual slice parameters

The pair code is a linear combination of two projections at dual heights.
All nonzero denominators are explicit; the identities do not rely on the
arbitrary value of division at zero. These are equations (22)–(25) of the
supplied projection manuscript.
-/

@[expose] public section

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- The code of two lines sharing a point at height `a`. -/
def pairCode (a b c : ℝ) (p : PairCoordinates m) : Space m :=
  c • atHeight b (lineAt a p.1 p.2.1) + (b - a) • p.2.2

/-- The second slice height dual to `t` for this pair code. -/
noncomputable def dualTime (a b c t : ℝ) : ℝ := a + (b - a) * (t - a) / (c * (t - b))

theorem dualTime_sub_base (a b c t : ℝ) :
    dualTime a b c t - a = (b - a) * (t - a) / (c * (t - b)) := by
  simp [dualTime]

theorem dualTime_ne_base {a b c t : ℝ} (hab : a ≠ b) (hc : c ≠ 0) (hta : t ≠ a)
    (htb : t ≠ b) : dualTime a b c t ≠ a := by
  rw [← sub_ne_zero, dualTime_sub_base]
  exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hab.symm) (sub_ne_zero.mpr hta))
    (mul_ne_zero hc (sub_ne_zero.mpr htb))

theorem pairCode_dual_coefficient {a b c t : ℝ} (hab : a ≠ b) (hc : c ≠ 0)
    (hta : t ≠ a) (htb : t ≠ b) :
    (b - a) / (dualTime a b c t - a) = c * (t - b) / (t - a) := by
  rw [dualTime_sub_base]
  field_simp

/-- The code is determined by the two projections at dual heights. -/
theorem pairCode_eq_dual_projections {a b c t : ℝ} (hab : a ≠ b) (hc : c ≠ 0)
    (hta : t ≠ a) (htb : t ≠ b) (p : PairCoordinates m) :
    pairCode a b c p =
      (c * (b - a) / (t - a)) • atHeight t (lineAt a p.1 p.2.1) +
      ((b - a) / (dualTime a b c t - a)) •
        atHeight (dualTime a b c t) (lineAt a p.1 p.2.2) := by
  have hta' := sub_ne_zero.mpr hta
  have hdual := sub_ne_zero.mpr (dualTime_ne_base hab hc hta htb)
  have hsum : c * (b - a) / (t - a) + (b - a) / (dualTime a b c t - a) = c := by
    rw [pairCode_dual_coefficient hab hc hta htb]
    field_simp
    ring
  rw [pairCode, atHeight_lineAt, atHeight_lineAt, atHeight_lineAt]
  calc
    c • (p.1 + (b - a) • p.2.1) + (b - a) • p.2.2 =
        c • p.1 + (c * (b - a)) • p.2.1 + (b - a) • p.2.2 := by module
    _ = (c * (b - a) / (t - a) + (b - a) / (dualTime a b c t - a)) • p.1 +
        ((c * (b - a) / (t - a)) * (t - a)) • p.2.1 +
        (((b - a) / (dualTime a b c t - a)) * (dualTime a b c t - a)) • p.2.2 := by
      rw [hsum, div_mul_cancel₀ _ hta', div_mul_cancel₀ _ hdual]
    _ = _ := by module

/-- Recover a pair from its first line and code value. -/
noncomputable def pairFromCode (a b c : ℝ) (g : Line m) (z : Space m) : PairCoordinates m :=
  (atHeight a g, (g.2, (b - a)⁻¹ • (z - c • atHeight b g)))

theorem first_pairFromCode (a b c : ℝ) (g : Line m) (z : Space m) :
    lineAt a (pairFromCode a b c g z).1 (pairFromCode a b c g z).2.1 = g :=
  lineAt_atHeight a g

theorem pairCode_pairFromCode {a b : ℝ} (hab : a ≠ b) (c : ℝ) (g : Line m) (z : Space m) :
    pairCode a b c (pairFromCode a b c g z) = z := by
  change c • atHeight b (lineAt a (atHeight a g) g.2) +
    (b - a) • ((b - a)⁻¹ • (z - c • atHeight b g)) = z
  simp only [lineAt_atHeight, smul_smul,
    mul_inv_cancel₀ (sub_ne_zero.mpr hab.symm), one_smul]
  module

theorem pairFromCode_pairCode {a b : ℝ} (hab : a ≠ b) (c : ℝ) (p : PairCoordinates m) :
    pairFromCode a b c (lineAt a p.1 p.2.1) (pairCode a b c p) = p := by
  change (atHeight a (lineAt a p.1 p.2.1),
    (p.2.1, (b - a)⁻¹ • (c • atHeight b (lineAt a p.1 p.2.1) + (b - a) • p.2.2 -
      c • atHeight b (lineAt a p.1 p.2.1)))) = p
  simp [atHeight_lineAt, smul_smul,
    inv_mul_cancel₀ (sub_ne_zero.mpr hab.symm)]

/-- The first-line family on a specified code fiber, expressed without an existential projection. -/
def pairFiber (a b c : ℝ) (W : Set (PairCoordinates m)) (z : Space m) : Set (Line m) :=
  {g | pairFromCode a b c g z ∈ W}

theorem measurableSet_pairFiber (a b c : ℝ) {W : Set (PairCoordinates m)}
    (hW : MeasurableSet W) (z : Space m) : MeasurableSet (pairFiber a b c W z) := by
  have hm : Continuous (fun g : Line m ↦ pairFromCode a b c g z) := by
    unfold pairFromCode atHeight
    fun_prop
  exact hW.preimage hm.measurable

theorem mem_pairFiber_iff {a b : ℝ} (hab : a ≠ b) (c : ℝ) (W : Set (PairCoordinates m))
    (g : Line m) (z : Space m) :
    g ∈ pairFiber a b c W z ↔ ∃ p ∈ W, lineAt a p.1 p.2.1 = g ∧ pairCode a b c p = z := by
  constructor
  · intro hg
    exact ⟨pairFromCode a b c g z, hg, first_pairFromCode a b c g z,
      pairCode_pairFromCode hab c g z⟩
  · rintro ⟨p, hp, rfl, rfl⟩
    change pairFromCode a b c (lineAt a p.1 p.2.1) (pairCode a b c p) ∈ W
    rwa [pairFromCode_pairCode hab]

end NKBesicovitch.Projection
