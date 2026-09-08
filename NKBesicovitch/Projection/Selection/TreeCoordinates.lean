/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Data.Fintype.Sum

/-!
# Finite coordinates for labeled corner trees

At each nonterminal node there is one scalar, one outer parameter, and
one inner parameter per outer label. Every pair of labels carries a child
tree. Splitting off the root preserves canonical product Lebesgue measure,
so recursive selection can be estimated by Tonelli and finite products.
-/

@[expose] public section

open MeasureTheory Set

namespace NKBesicovitch.Projection.Selection

/-- Currying a finite rectangular array preserves product measure. -/
theorem volume_preserving_curry (ι κ X : Type*) [Fintype ι] [Fintype κ]
    [MeasureSpace X] [SigmaFinite (volume : Measure X)] :
    MeasurePreserving (MeasurableEquiv.curry ι κ X) volume volume := by
  apply MeasurePreserving.symm (MeasurableEquiv.curry ι κ X).symm
  refine ⟨(MeasurableEquiv.curry ι κ X).symm.measurable, (Measure.pi_eq ?_).symm⟩
  intro s _
  rw [MeasurableEquiv.map_apply]
  have h : (MeasurableEquiv.curry ι κ X).symm ⁻¹' univ.pi s =
      univ.pi (fun i ↦ univ.pi (fun j ↦ s (i, j))) := by
    ext f
    simp [MeasurableEquiv.curry, Set.mem_pi, Prod.forall]
  rw [h, volume_pi_pi]
  simp_rw [volume_pi_pi]
  exact (Fintype.prod_prod_type (fun ij ↦ volume (s ij))).symm

/-- Coordinate positions of a complete labeled corner tree of the specified depth. -/
def TreeCoordinate (D L : ℕ) : ℕ → Type
  | 0 => Fin 0
  | J + 1 => (Unit ⊕ (Fin D ⊕ (Fin L × Fin D))) ⊕
      ((Fin L × Fin L) × TreeCoordinate D L J)

instance instFintypeTreeCoordinate (D L : ℕ) : (J : ℕ) → Fintype (TreeCoordinate D L J)
  | 0 => inferInstanceAs (Fintype (Fin 0))
  | J + 1 => by
      letI : Fintype (TreeCoordinate D L J) := instFintypeTreeCoordinate D L J
      exact inferInstanceAs (Fintype ((Unit ⊕ (Fin D ⊕ (Fin L × Fin D))) ⊕
        ((Fin L × Fin L) × TreeCoordinate D L J)))

namespace TreeCoordinate

variable (D L J : ℕ)

/-- Split the real coordinates at one node into its scalar and scheme parameters. -/
def nodeEquiv :
    ((Unit ⊕ (Fin D ⊕ (Fin L × Fin D))) → ℝ) ≃ᵐ
      ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ)) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ ↦ ℝ)).trans
    ((MeasurableEquiv.funUnique Unit ℝ).prodCongr
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ ↦ ℝ)).trans
        ((MeasurableEquiv.refl _).prodCongr (MeasurableEquiv.curry (Fin L) (Fin D) ℝ))))

theorem volume_preserving_nodeEquiv : MeasurePreserving (nodeEquiv D L) volume volume := by
  have hi := ((MeasurePreserving.id (volume : Measure (Fin D → ℝ))).prod
    (volume_preserving_curry (Fin L) (Fin D) ℝ)).comp
      (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin D ⊕ (Fin L × Fin D) ↦ ℝ))
  exact ((volume_preserving_funUnique Unit ℝ).prod hi).comp
    (volume_measurePreserving_sumPiEquivProdPi
      (fun _ : Unit ⊕ (Fin D ⊕ (Fin L × Fin D)) ↦ ℝ))

/-- Separate a tree parameter into its root-node parameter and all labeled child parameters. -/
def splitEquiv : (TreeCoordinate D L (J + 1) → ℝ) ≃ᵐ
    (ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))) ×
      (Fin L × Fin L → TreeCoordinate D L J → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ ↦ ℝ)).trans
    ((nodeEquiv D L).prodCongr
      (MeasurableEquiv.curry (Fin L × Fin L) (TreeCoordinate D L J) ℝ))

theorem volume_preserving_splitEquiv :
    MeasurePreserving (splitEquiv D L J) volume volume := by
  exact ((volume_preserving_nodeEquiv D L).prod
    (volume_preserving_curry (Fin L × Fin L) (TreeCoordinate D L J) ℝ)).comp
      (volume_measurePreserving_sumPiEquivProdPi (fun _ : TreeCoordinate D L (J + 1) ↦ ℝ))

end TreeCoordinate

end NKBesicovitch.Projection.Selection
