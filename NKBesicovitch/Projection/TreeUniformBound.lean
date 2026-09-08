/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.CompanionBounds
public import NKBesicovitch.Projection.TreeFamilies
public import NKBesicovitch.Projection.PatternBound

/-!
# The tree bound with common prescribed constants

A common stopping-node constant and a bound on the total number of
heights give the large-size estimate with that same constant. The root
and pruning thresholds remain explicit inputs for quantitative control.
-/

@[expose] public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection.CornerTree

variable {m J : ℕ} {β : ℝ}

theorem large_normalized_bound_of_stoppingNodeBounds [Nonempty (Fin m)] (T : CornerTree m β J)
    (hJ : 0 < J) {H C : ℝ} (hH : (T.times.card : ℝ) ≤ H)
    (hbound : ∀ v h, (T.pattern v h).StoppingNodeBound (1 / (4 * H)) (1 / 2) (1 / (2 * H)) C)
    {G : Set (Line m)} (hG : MeasurableSet G) (hGb : IsBounded G)
    (hM : (parallelMultiplicity G).toReal ≤ 1) (hL : 1 ≤ (volume G).toReal)
    {N : ℝ} (hN : 1 ≤ N) (hπ : ∀ t ∈ T.times, volume (atHeight t '' G) ≤ ENNReal.ofReal N)
    (hroot : (pairJacobian m (T.a T.root) (T.b T.root) (T.c T.root)).toReal <
      (1 / (4 * H)) * N ^ (96 : ℝ))
    (hprune : ∀ v h, 4 * (1 + 2 * ((T.pattern v h).outer.card : ℝ)) *
      (T.pattern v h).children.card ≤ N ^ (1 / (J : ℝ) ^ 2)) :
    let q := β / (β - 1)
    (volume G).toReal ≤ C * N ^
      ((2 * q + 3 * q ^ 2 - 2 + (200 * q ^ 2 + 2 * q) / J) / (q + 2 * q ^ 2 - 2)) := by
  have hHpos := (Nat.cast_pos.mpr T.times_nonempty.card_pos).trans_le hH
  have hc₀ : 0 < 1 / (4 * H) := by positivity
  have hNpos := zero_lt_one.trans_le hN
  have hLpos := zero_lt_one.trans_le hL
  obtain ⟨S, hηlower, hVlower, hVupper⟩ := exists_companionSystem_of_card_le T.times
    T.times_nonempty hH hG hGb (ENNReal.toReal_pos_iff.mp hLpos).1 hNpos hπ
  have hVreal : 0 < (volume S.centers * S.η).toReal :=
    lt_of_lt_of_le (by positivity) hVlower
  obtain ⟨hVpos, hVfin⟩ := ENNReal.toReal_pos_iff.mp hVreal
  obtain ⟨v, hv, U, hU, hUP, hparent, hQ, hchild⟩ := T.exists_stopping_families hJ S
    hVpos hVfin.ne rfl hc₀.le hL hN hVlower hπ hroot
  have ha := T.pattern_times_subset v hv (T.pattern v hv).a_mem_times
  have hb := T.pattern_times_subset v hv (T.pattern v hv).b_mem_times
  have hpair : volume (companionPairs (T.pattern v hv).b S.centers
      (S.companion (T.pattern v hv).b)) = volume S.centers * S.η := by
    apply volume_companionPairs_of_constant_mass _ S.centers_measurable
      (S.companion_measurable _ hb) S.η
    rintro _ ⟨g, hg, rfl⟩
    exact S.slice_eq _ hb g hg
  exact hbound v hv G hGb hM S.centers
    (S.companion (T.pattern v hv).a) (S.companion (T.pattern v hv).b)
    S.centers_measurable (S.companion_measurable _ ha) (S.companion_measurable _ hb)
    S.centers_subset (S.companion_subset _ ha) (S.companion_subset _ hb)
    S.η S.η_pos S.η_ne_top (S.slice_eq _ ha) (S.slice_eq _ hb)
    _ hVpos hVfin.ne hpair (volume G).toReal N hLpos hN hVlower hVupper hηlower
    (fun t ht ↦ hπ t (T.pattern_times_subset v hv ht))
    J (T.level v) hJ hv (hprune v hv) U hU hUP hparent hQ hchild

end NKBesicovitch.Projection.CornerTree
