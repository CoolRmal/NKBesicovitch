/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Induction.TerminalDisk
public import NKBesicovitch.Operators.DiskGlobalization

/-!
# The global Schwartz terminal estimate

Smooth localization removes the support restriction from the positive
Schwartz disk estimate obtained by summing the Fourier terminal step.
-/

public section

open MeasureTheory
open scoped SchwartzMap ENNReal NNReal

namespace NKBesicovitch.Induction

variable {m k : ℕ} [Nonempty (Fin m)]

/-- A subunit plate deficit gives a global disk estimate on positive Schwartz inputs. -/
theorem HasPlateEstimate.exists_eLpNorm_diskMaximal_schwartz_global_le
    {hkm : k ≤ m} {α p : ℝ} (h : HasPlateEstimate hkm α p) (hα : α < 1) (hp : 2 ≤ p) :
    ∃ C : ℝ≥0, ∀ f : 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℝ), (∀ x, 0 ≤ f x) →
      eLpNorm (diskMaximal (fun x ↦ ENNReal.ofReal (f x))) (ENNReal.ofReal p)
        (Grassmannian.probability (Nat.succ_le_succ hkm)) ≤
          C * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  let q : ℝ≥0 := .mk p hp0.le
  have hq : 0 < q := hp0
  have he : ENNReal.ofReal p = (q : ℝ≥0∞) := ENNReal.ofReal_eq_coe_nnreal hp0.le
  obtain ⟨C, hC⟩ := h.exists_eLpNorm_diskMaximal_schwartz_le hα hp 3
  rw [he] at hC ⊢
  refine ⟨(3 : ℝ≥0) ^ (((m + 1 : ℕ) : ℝ) / p) * C, fun f hf ↦ ?_⟩
  exact eLpNorm_diskMaximal_schwartz_le_of_local (Nat.succ_le_succ hkm) hq C hC f hf

end NKBesicovitch.Induction
