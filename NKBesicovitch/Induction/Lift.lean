/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Induction.Estimates
public import NKBesicovitch.Induction.DiagonalStep
public import NKBesicovitch.Induction.XRayExponents

/-!
# Reducing the plate deficit by a prescribed subcritical ratio

The diagonal step divides the dimension deficit by `ρ`. The available
X-ray exponent scale can always accommodate the preceding input exponent,
so this operation can be repeated any finite number of times.
-/

public section

open MeasureTheory Set Metric NKBesicovitch.Grassmannian NKBesicovitch.XRay
open scoped ENNReal NNReal

namespace NKBesicovitch.Induction

private theorem plate_coefficient_power (C δ : ℝ≥0) {α a ρ p t : ℝ}
    (ha : 0 < a) (hρ : 0 < ρ) (hp : 0 < p) (ht : t = ρ * p / a) :
    (C * δ ^ (-α / a)) ^ t⁻¹ = C ^ t⁻¹ * δ ^ (-(α / ρ) / p) := by
  rw [NNReal.mul_rpow, ← NNReal.rpow_mul]
  congr 2
  rw [ht]
  field_simp

variable {n m k : ℕ} (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ)

include v b in
theorem HasPlateEstimate.lift_of_sphericalXRay (hkn : k + 1 ≤ n) (hkm : k ≤ m)
    {α a ρ p q : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hp : 0 < p)
    (hpq : p ≤ q) (hqr : q ≤ ρ * p) (har : a ≤ ρ * p)
    (hlow : HasPlateEstimate hkm α a)
    (hxray : ∀ R : ℝ≥0, ∃ B : ℝ≥0,
      ∀ f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞, Measurable f →
        Function.support f ⊆ closedBall 0 (R : ℝ) →
          sphericalXRayNorm f (ENNReal.ofReal q) (ENNReal.ofReal (ρ * p)) ≤
            B * eLpNorm f (ENNReal.ofReal p) volume) :
    HasPlateEstimate hkn (α / ρ) p := by
  let t := ρ * p / a
  have ht : 1 ≤ t := (le_div_iff₀ ha).2 (by simpa using har)
  have he : ENNReal.ofReal a * ENNReal.ofReal t = ENNReal.ofReal (ρ * p) := by
    rw [← ENNReal.ofReal_mul ha.le]
    congr 1
    dsimp [t]
    field_simp
  let S : ℝ≥0∞ := (((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere univ)⁻¹) ^
    (1 / (ENNReal.ofReal q).toReal)
  have hS : S ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity)
    (ENNReal.inv_ne_top.mpr (isOpen_univ.measure_ne_zero _ ⟨v, mem_univ v⟩))
  intro R
  obtain ⟨C, hc⟩ := hlow R
  obtain ⟨B, hb⟩ := hxray R
  refine ⟨(2 : ℝ≥0) ^ m * C ^ t⁻¹ * S.toNNReal * B, fun δ hδ f hf hs ↦ ?_⟩
  have hqa : ENNReal.ofReal q ≤ ENNReal.ofReal a * ENNReal.ofReal t := by
    rw [he]
    exact ENNReal.ofReal_le_ofReal hqr
  have h := eLpNorm_plateMaximal_diagonal_step v b hkn hkm (show 0 < (δ : ℝ) from hδ) ht
    (ENNReal.ofReal_pos.mpr ha).ne' ENNReal.ofReal_ne_top
    (ENNReal.ofReal_le_ofReal hpq) hqa (ENNReal.ofReal_pos.mpr (hp.trans_le hpq)).ne'
    ENNReal.ofReal_ne_top (C * δ ^ (-α / a)) B
    (hc δ hδ) (fun g hg hgs ↦ by simpa only [he] using hb g hg hgs) hf hs
  rw [plate_coefficient_power C δ ha hρ hp (rfl : t = ρ * p / a)] at h
  convert h using 1
  simp only [ENNReal.coe_mul, ENNReal.coe_toNNReal hS, S]
  ac_rfl

/-- A single lift always reduces the deficit by any fixed ratio below the critical value. -/
theorem HasPlateEstimate.exists_lift {m k : ℕ} (hm : 0 < m) (hkm : k ≤ m)
    {α a ρ : ℝ} (ha : 0 < a) (hρ : ρ ∈ Ioo 2 criticalExponent)
    (hlow : HasPlateEstimate hkm α a) :
    ∃ p : ℝ, 2 ≤ p ∧ HasPlateEstimate (Nat.succ_le_succ hkm) (α / ρ) p := by
  let : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) := ⟨by simp⟩
  let v : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
    ⟨EuclideanSpace.single 0 1, by simp⟩
  let b := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) m
    (v := (v : EuclideanSpace ℝ (Fin (m + 1))))
    (norm_pos_iff.mp (by rw [norm_eq_of_mem_sphere v]; norm_num))).repr.symm
  obtain ⟨p, q, hp, hpq, hqr, har, hx⟩ :=
    exists_sphericalXRayNorm_bound_ratio (E := EuclideanSpace ℝ (Fin (m + 1))) m hρ a
  exact ⟨p, hp, HasPlateEstimate.lift_of_sphericalXRay v b (Nat.succ_le_succ hkm) hkm
    ha (by linarith [hρ.1]) (by linarith) hpq hqr har hlow hx⟩

end NKBesicovitch.Induction
