/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.TreeFamilies
public import NKBesicovitch.Projection.TreeThreshold
public import NKBesicovitch.Projection.PatternBound

/-!
# The normalized bound from an admissible finite corner tree

Fix the tree before the line family. Balanced companions, the root and
terminal estimates, and finite stopping then supply all geometric inputs
to the corner bound. Constants are uniform across the finitely many nodes.
The theorem here treats line mass at least one and projection size above
the fixed threshold; the remaining bounded cases use the two-slice seed.
-/

public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection.CornerTree

variable {m J : ℕ} {β : ℝ}

theorem exists_large_normalized_bound [Nonempty (Fin m)] (T : CornerTree m β J)
    (hJ : 0 < J) (hβ : 1 < β) (hβ2 : β ≤ 2) :
    let q := β / (β - 1)
    ∃ C N₀ : ℝ, 0 < C ∧ 1 ≤ N₀ ∧
      ∀ G : Set (Line m), MeasurableSet G → IsBounded G →
      (parallelMultiplicity G).toReal ≤ 1 → 1 ≤ (volume G).toReal →
      ∀ N : ℝ, N₀ ≤ N → (∀ t ∈ T.times, volume (atHeight t '' G) ≤ ENNReal.ofReal N) →
      (volume G).toReal ≤ C *
        N ^ ((2 * q + 3 * q ^ 2 - 2 + (200 * q ^ 2 + 2 * q) / J) /
          (q + 2 * q ^ 2 - 2)) := by
  classical
  let r := (T.times.card : ℝ)
  have hr : 0 < r := Nat.cast_pos.mpr T.times_nonempty.card_pos
  have hc₀ : 0 < 1 / (4 * r) := by positivity
  have hc₁ : 0 < 1 / (2 * r) := by positivity
  let ι := {v : T.Node // T.level v < J}
  choose B _ hB using fun v : ι ↦
    (T.pattern v.val v.property).exists_stopping_node_constant hβ hβ2 hc₀ hc₁ hc₁
  obtain ⟨D, hD⟩ := (Set.finite_range B).bddAbove
  obtain ⟨N₀, hN₀, hthreshold⟩ := T.exists_stopping_threshold hJ hc₀
  refine ⟨max 1 D, N₀, zero_lt_one.trans_le (le_max_left _ _), hN₀,
    fun G hG hGb hM hL N hN hπ ↦ ?_⟩
  have hN₁ := hN₀.trans hN
  have hNpos := zero_lt_one.trans_le hN₁
  have hLpos := zero_lt_one.trans_le hL
  obtain ⟨S, hη, hVlower, hVupper⟩ := exists_companionSystem T.times T.times_nonempty hG hGb
    (ENNReal.toReal_pos_iff.mp hLpos).1 hNpos hπ
  have hVreal : 0 < (volume S.centers * S.η).toReal :=
    lt_of_lt_of_le (by positivity) hVlower
  obtain ⟨hVpos, hVfin⟩ := ENNReal.toReal_pos_iff.mp hVreal
  obtain ⟨hroot, hprune⟩ := hthreshold N hN
  obtain ⟨v, hv, U, hU, hUP, hparent, hQ, hchild⟩ := T.exists_stopping_families hJ S
    hVpos hVfin.ne rfl hc₀.le hL hN₁ hVlower hπ hroot
  have ha := T.pattern_times_subset v hv (T.pattern v hv).a_mem_times
  have hb := T.pattern_times_subset v hv (T.pattern v hv).b_mem_times
  have hpair : volume (companionPairs (T.pattern v hv).b S.centers
      (S.companion (T.pattern v hv).b)) = volume S.centers * S.η := by
    apply volume_companionPairs_of_constant_mass _ S.centers_measurable
      (S.companion_measurable _ hb) S.η
    rintro _ ⟨g, hg, rfl⟩
    exact S.slice_eq _ hb g hg
  have hηlower : (1 / (2 * r)) * (volume G).toReal * N ^ (-1 : ℝ) ≤ S.η.toReal := by
    rw [hη, Real.rpow_neg_one]
    change (1 / (2 * r)) * (volume G).toReal * N⁻¹ ≤ (volume G).toReal / (2 * r * N)
    exact le_of_eq (by field_simp)
  have h := hB (⟨v, hv⟩ : ι) G hGb hM S.centers
    (S.companion (T.pattern v hv).a) (S.companion (T.pattern v hv).b)
    S.centers_measurable (S.companion_measurable _ ha) (S.companion_measurable _ hb)
    S.centers_subset (S.companion_subset _ ha) (S.companion_subset _ hb)
    S.η S.η_pos S.η_ne_top (S.slice_eq _ ha) (S.slice_eq _ hb)
    _ hVpos hVfin.ne hpair (volume G).toReal N hLpos hN₁ hVlower hVupper hηlower
    (fun t ht ↦ hπ t (T.pattern_times_subset v hv ht))
    J (T.level v) hJ hv (hprune v hv) U hU hUP hparent hQ hchild
  exact h.trans (mul_le_mul_of_nonneg_right
    ((hD (Set.mem_range_self (⟨v, hv⟩ : ι))).trans (le_max_right _ _))
    (Real.rpow_nonneg hNpos.le _))

end NKBesicovitch.Projection.CornerTree
