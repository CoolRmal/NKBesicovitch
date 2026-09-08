/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.RootCoordinates
public import NKBesicovitch.Projection.Selection.RootParameters
public import NKBesicovitch.Projection.Selection.TreeTimes
public import NKBesicovitch.Projection.Selection.TreeUniformBounds

/-!
# Finite-vector parameters and heights for selected trees

Reindexing preserves joint measurability, the exact parameter volume,
all selected heights, and a uniform polynomial coordinate bound.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection.SelectableProjectionScheme

variable {m D L : ℕ} {β : ℝ} (S : SelectableProjectionScheme m β D L)

/-- The root-and-tree selection represented as a finite real vector. -/
noncomputable def finiteTreeParameters (I : Set ℝ) (J : ℕ) :
    Set (Fin (3 + Fintype.card (TreeCoordinate D L J)) → ℝ) :=
  TreeCoordinate.rootEquiv D L J ⁻¹' S.rootParameters I J

/-- The labeled tree height after enumerating both coordinates and labels. -/
noncomputable def finiteTreeTime (J : ℕ)
    (σ : Fin (3 + Fintype.card (TreeCoordinate D L J)) → ℝ)
    (i : Fin (Fintype.card (TreeTimeLabel L J))) : ℝ :=
  S.treeTime J (TreeCoordinate.rootEquiv D L J σ).1 (TreeCoordinate.rootEquiv D L J σ).2
    ((Fintype.equivFin (TreeTimeLabel L J)).symm i)

theorem measurableSet_finiteTreeParameters_family (J : ℕ) {X : Type} [MeasurableSpace X]
    (I : X → Set ℝ) (hI : MeasurableSet {p : X × ℝ | p.2 ∈ I p.1}) :
    MeasurableSet {p : X × (Fin (3 + Fintype.card (TreeCoordinate D L J)) → ℝ) |
      p.2 ∈ S.finiteTreeParameters (I p.1) J} := by
  have h := (S.measurableSet_rootParameters_family J hI).preimage
    (f := fun p : X × (Fin (3 + Fintype.card (TreeCoordinate D L J)) → ℝ) ↦
      (p.1, TreeCoordinate.rootEquiv D L J p.2))
    (measurable_fst.prodMk ((TreeCoordinate.rootEquiv D L J).measurable.comp measurable_snd))
  simpa only [finiteTreeParameters, preimage, mem_ofPred_eq, ofPred_mem_eq] using h

theorem volume_finiteTreeParameters (I : Set ℝ) (J : ℕ) :
    volume (S.finiteTreeParameters I J) = volume (S.rootParameters I J) :=
  (TreeCoordinate.volume_preserving_rootEquiv D L J).measure_preimage_equiv _

theorem measurable_finiteTreeTime (J : ℕ) (i : Fin (Fintype.card (TreeTimeLabel L J))) :
    Measurable (fun σ ↦ S.finiteTreeTime J σ i) :=
  S.measurable_treeTime J (TreeCoordinate.rootEquiv D L J).measurable.fst
    (TreeCoordinate.rootEquiv D L J).measurable.snd _

theorem finiteTreeTime_mem {I : Set ℝ} (hI : MeasurableSet I) (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) (J : ℕ) {σ : Fin (3 + Fintype.card (TreeCoordinate D L J)) → ℝ}
    (hσ : σ ∈ S.finiteTreeParameters I J) (i : Fin (Fintype.card (TreeTimeLabel L J))) :
    S.finiteTreeTime J σ i ∈ I :=
  S.treeTime_mem hI hIunit hIpos J hσ.1 hσ.2 _

theorem image_finiteTreeTime (J : ℕ)
    (σ : Fin (3 + Fintype.card (TreeCoordinate D L J)) → ℝ) :
    Finset.univ.image (S.finiteTreeTime J σ) =
      S.treeTimes J (TreeCoordinate.rootEquiv D L J σ).1 (TreeCoordinate.rootEquiv D L J σ).2 := by
  classical
  change Finset.univ.image ((S.treeTime J (TreeCoordinate.rootEquiv D L J σ).1
    (TreeCoordinate.rootEquiv D L J σ).2) ∘ (Fintype.equivFin (TreeTimeLabel L J)).symm) = _
  rw [← Finset.image_image, Finset.image_univ_equiv]
  rfl

theorem exists_finiteTree_coordinate_constant :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ I : Set ℝ, MeasurableSet I → I ⊆ Icc 0 1 → 0 < volume I →
      ∀ J : ℕ, ∀ σ ∈ S.finiteTreeParameters I J, ∀ j,
        |σ j| ≤ C * (volume I).toReal⁻¹ ^ (8 * S.boundExponent) := by
  obtain ⟨C, hC, hbound⟩ := S.exists_tree_coordinate_constant
  refine ⟨C, hC, fun I hI hIunit hIpos J σ hσ j ↦ ?_⟩
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hx := ENNReal.toReal_pos hIpos.ne' hIfin
  have hx₁ : (volume I).toReal ≤ 1 := by
    simpa only [measureReal_def, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
      ENNReal.toReal_one] using measureReal_mono (μ := volume) hIunit (by simp)
  have hCpow : 1 ≤ C * (volume I).toReal⁻¹ ^ (8 * S.boundExponent) :=
    one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ ((one_le_inv₀ hx).mpr hx₁))
  have hbase := mem_separatedTriples.mp hσ.1
  have habs {t : ℝ} (ht : t ∈ I) : |t| ≤ C * (volume I).toReal⁻¹ ^ (8 * S.boundExponent) := by
    have htunit := hIunit ht
    have ht₁ : |t| ≤ 1 := by simpa only [abs_of_nonneg htunit.1] using htunit.2
    exact ht₁.trans hCpow
  have h := TreeCoordinate.rootEquiv_symm_bound D L J
    (habs hbase.1) (habs hbase.2.1) (habs hbase.2.2.1)
    (hbound I hI hIunit hIpos J _ hσ.1 _ hσ.2) j
  simpa only [MeasurableEquiv.symm_apply_apply] using h

end NKBesicovitch.Projection.Selection.SelectableProjectionScheme
