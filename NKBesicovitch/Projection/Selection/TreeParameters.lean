/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.TreeCoordinates
public import NKBesicovitch.Projection.Selection.NodePatternLabels

/-!
# Jointly measurable whole-tree selection

A selected tree has a selected root node and a selected subtree at every
pair of labels, based at that pair's child triple. Keeping all label
occurrences makes the recursive parameter family jointly Borel, even
when distinct labels happen to give the same numerical height.
-/

@[expose] public section

open MeasureTheory Set

namespace NKBesicovitch.Projection.Selection.SelectableProjectionScheme

variable {m D L : ℕ} {β : ℝ} (S : SelectableProjectionScheme m β D L)

/-- The recursively selected coordinates of a tree with a prescribed root triple. -/
noncomputable def treeParameters (I : Set ℝ) :
    (J : ℕ) → ((ℝ × ℝ) × ℝ) → Set (TreeCoordinate D L J → ℝ)
  | 0, _ => univ
  | J + 1, q => {σ |
      (TreeCoordinate.splitEquiv D L J σ).1 ∈
        S.cornerNodeParameters I q.1.1 q.1.2 q.2 ((volume I).toReal / 100) ∧
      ∀ ij, (TreeCoordinate.splitEquiv D L J σ).2 ij ∈
        treeParameters I J
          (S.nodeChildTriple q.1.1 q.1.2 q.2 (TreeCoordinate.splitEquiv D L J σ).1 ij)}

theorem measurableSet_treeParameters_family (J : ℕ) {X : Type} [MeasurableSpace X]
    {I : Set (X × ℝ)} (hI : MeasurableSet I) {q : X → (ℝ × ℝ) × ℝ} (hq : Measurable q) :
    MeasurableSet {p : X × (TreeCoordinate D L J → ℝ) |
      p.2 ∈ S.treeParameters {t | (p.1, t) ∈ I} J (q p.1)} := by
  induction J generalizing X with
  | zero => exact MeasurableSet.univ
  | succ J ih =>
    have hs : Measurable (fun p : X × (TreeCoordinate D L (J + 1) → ℝ) ↦
        TreeCoordinate.splitEquiv D L J p.2) :=
      (TreeCoordinate.splitEquiv D L J).measurable.comp measurable_snd
    have hr := (S.measurableSet_cornerNodeParameters_family hI hq.fst.fst hq.fst.snd hq.snd
      ((measurable_measure_prodMk_left (ν := volume) hI).ennreal_toReal.div_const 100)).preimage
      (f := fun p : X × (TreeCoordinate D L (J + 1) → ℝ) ↦
        (p.1, (TreeCoordinate.splitEquiv D L J p.2).1)) (measurable_fst.prodMk hs.fst)
    have hI' : MeasurableSet
        {p : (X × (ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ)))) × ℝ |
          (p.1.1, p.2) ∈ I} := hI.preimage (measurable_fst.fst.prodMk measurable_snd)
    have hi (ij : Fin L × Fin L) := (ih hI'
      (S.measurable_nodeChildTriple (hq.comp measurable_fst).fst.fst
        (hq.comp measurable_fst).fst.snd (hq.comp measurable_fst).snd measurable_snd ij)).preimage
      (f := fun p : X × (TreeCoordinate D L (J + 1) → ℝ) ↦
        ((p.1, (TreeCoordinate.splitEquiv D L J p.2).1),
          (TreeCoordinate.splitEquiv D L J p.2).2 ij))
      ((measurable_fst.prodMk hs.fst).prodMk ((measurable_pi_apply ij).comp hs.snd))
    simpa only [treeParameters, preimage, mem_ofPred_eq, ← ofPred_forall,
      Function.comp_apply, ofPred_and, mem_inter_iff] using
      hr.inter (MeasurableSet.iInter hi)

theorem measurableSet_treeParameters {I : Set ℝ} (hI : MeasurableSet I)
    (J : ℕ) (q : (ℝ × ℝ) × ℝ) : MeasurableSet (S.treeParameters I J q) := by
  have h := S.measurableSet_treeParameters_family J
    (X := Unit) (I := {p : Unit × ℝ | p.2 ∈ I}) (hI.preimage measurable_snd)
    (q := fun _ ↦ q) measurable_const
  exact h.preimage (f := fun σ ↦ ((), σ)) (by fun_prop)

/-- One recursive selection step, expressed in root and child product coordinates. -/
noncomputable def treeStepParameters (I : Set ℝ) (J : ℕ) (q : (ℝ × ℝ) × ℝ) :
    Set ((ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))) ×
      (Fin L × Fin L → TreeCoordinate D L J → ℝ)) :=
  {p | p.1 ∈ S.cornerNodeParameters I q.1.1 q.1.2 q.2 ((volume I).toReal / 100) ∧
    ∀ ij, p.2 ij ∈ S.treeParameters I J (S.nodeChildTriple q.1.1 q.1.2 q.2 p.1 ij)}

theorem treeParameters_succ (I : Set ℝ) (J : ℕ) (q : (ℝ × ℝ) × ℝ) :
    S.treeParameters I (J + 1) q =
      TreeCoordinate.splitEquiv D L J ⁻¹' S.treeStepParameters I J q := rfl

theorem measurableSet_treeStepParameters {I : Set ℝ} (hI : MeasurableSet I)
    (J : ℕ) (q : (ℝ × ℝ) × ℝ) : MeasurableSet (S.treeStepParameters I J q) := by
  have h := (S.measurableSet_treeParameters hI (J + 1) q).preimage
    (TreeCoordinate.splitEquiv D L J).symm.measurable
  simpa only [treeParameters_succ, preimage_preimage, MeasurableEquiv.apply_symm_apply,
    preimage_id'] using h

end NKBesicovitch.Projection.Selection.SelectableProjectionScheme
