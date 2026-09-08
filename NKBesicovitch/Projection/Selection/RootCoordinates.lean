/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.TreeCoordinates
public import Mathlib.Tactic.FinCases

/-!
# Reindexing a root triple and tree as a finite real vector

There are three root coordinates and one coordinate for each position
in the labeled tree. The coordinate equivalence preserves product
Lebesgue measure and the coordinatewise absolute-value bounds.
-/

@[expose] public section

open MeasureTheory

namespace NKBesicovitch.Projection.Selection.TreeCoordinate

variable (D L J : ℕ)

/-- Enumerate the three root positions followed by the tree positions. -/
noncomputable def rootIndexEquiv :
    ((Fin 2 ⊕ Unit) ⊕ TreeCoordinate D L J) ≃ Fin (3 + Fintype.card (TreeCoordinate D L J)) :=
  (Fintype.equivFin _).trans (finCongr (by simp))

/-- Split a finite parameter vector into its root triple and tree coordinates. -/
noncomputable def rootEquiv : (Fin (3 + Fintype.card (TreeCoordinate D L J)) → ℝ) ≃ᵐ
    (((ℝ × ℝ) × ℝ) × (TreeCoordinate D L J → ℝ)) :=
  (MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) (rootIndexEquiv D L J).symm).trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ ↦ ℝ)).trans
      (((MeasurableEquiv.sumPiEquivProdPi (fun _ ↦ ℝ)).trans
        (MeasurableEquiv.finTwoArrow.prodCongr (MeasurableEquiv.funUnique Unit ℝ))).prodCongr
          (MeasurableEquiv.refl _)))

theorem volume_preserving_rootEquiv : MeasurePreserving (rootEquiv D L J) volume volume := by
  have hroot := ((volume_preserving_finTwoArrow ℝ).prod
    (volume_preserving_funUnique Unit ℝ)).comp
      (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin 2 ⊕ Unit ↦ ℝ))
  exact ((hroot.prod (MeasurePreserving.id (volume : Measure (TreeCoordinate D L J → ℝ)))).comp
    (volume_measurePreserving_sumPiEquivProdPi
      (fun _ : (Fin 2 ⊕ Unit) ⊕ TreeCoordinate D L J ↦ ℝ))).comp
        (volume_measurePreserving_piCongrLeft (fun _ ↦ ℝ) (rootIndexEquiv D L J).symm)

theorem rootEquiv_symm_bound {p : ((ℝ × ℝ) × ℝ) × (TreeCoordinate D L J → ℝ)} {C : ℝ}
    (ha : |p.1.1.1| ≤ C) (hb : |p.1.1.2| ≤ C) (hc : |p.1.2| ≤ C)
    (hσ : ∀ j, |p.2 j| ≤ C) (i : Fin (3 + Fintype.card (TreeCoordinate D L J))) :
    |(rootEquiv D L J).symm p i| ≤ C := by
  obtain ⟨j, rfl⟩ := (rootIndexEquiv D L J).surjective i
  change |Sum.elim
    (Sum.elim (fun i : Fin 2 ↦ ![p.1.1.1, p.1.1.2] i) (fun _ : Unit ↦ p.1.2)) p.2
      ((rootIndexEquiv D L J).symm ((rootIndexEquiv D L J) j))| ≤ C
  rw [Equiv.symm_apply_apply]
  rcases j with (j | u) | j
  · fin_cases j
    · exact ha
    · exact hb
  · cases u
    exact hc
  · exact hσ j

end NKBesicovitch.Projection.Selection.TreeCoordinate
