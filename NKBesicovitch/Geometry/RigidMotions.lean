/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Grassmannian.Action
public import NKBesicovitch.Operators.Defs

/-!
# Rigid motions of disks and plates

Translations and orthogonal operators preserve Lebesgue volume and carry the
disk and plate in a fixed direction to the corresponding rotated direction.
-/

@[expose] public section

open MeasureTheory Set

namespace NKBesicovitch

variable {n k : ℕ}

/-- Apply an orthogonal operator and then translate the center to `a`. -/
noncomputable def rigidMotion (u : Rotations n) (a : Space n) : Space n ≃ᵢ Space n :=
  (Unitary.linearIsometryEquiv u).toIsometryEquiv.trans (IsometryEquiv.vaddConst a)

theorem rigidMotion_apply (u : Rotations n) (a x : Space n) :
    rigidMotion u a x = Unitary.linearIsometryEquiv u x + a := rfl

theorem measurePreserving_rigidMotion (u : Rotations n) (a : Space n) :
    MeasurePreserving (rigidMotion u a) volume volume :=
  (Unitary.linearIsometryEquiv u).measurePreserving.add_right volume a

theorem preimage_unitDisk_rigidMotion (u : Rotations n) (a : Space n)
    (V : Grassmannian n k) :
    rigidMotion u a ⁻¹' unitDisk (Grassmannian.rotate u V).submodule a =
      unitDisk V.submodule 0 := by
  ext x
  simp only [Set.mem_preimage, unitDisk, Set.mem_ofPred_eq, rigidMotion_apply,
    add_sub_cancel_right, sub_zero, LinearIsometryEquiv.norm_map]
  apply and_congr_left
  intro _
  change Unitary.linearIsometryEquiv u x ∈
    Unitary.linearIsometryEquiv u '' (V.submodule : Set (Space n)) ↔
      x ∈ (V.submodule : Set (Space n))
  simp only [Set.mem_image, (Unitary.linearIsometryEquiv u).injective.eq_iff, exists_eq_right]

theorem image_unitDisk_rigidMotion (u : Rotations n) (a : Space n)
    (V : Grassmannian n k) :
    rigidMotion u a '' unitDisk V.submodule 0 =
      unitDisk (Grassmannian.rotate u V).submodule a := by
  rw [← preimage_unitDisk_rigidMotion u a V]
  exact (rigidMotion u a).surjective.image_preimage _

theorem preimage_plate_rigidMotion (u : Rotations n) (a : Space n)
    (V : Grassmannian n k) (δ : ℝ) :
    rigidMotion u a ⁻¹' plate δ (Grassmannian.rotate u V).submodule a =
      plate δ V.submodule 0 := by
  rw [plate, ← image_unitDisk_rigidMotion u a V]
  ext x
  simp only [Set.mem_preimage, plate, Metric.mem_thickening_iff_infEDist_lt,
    Metric.infEDist_image (rigidMotion u a).isometry]

theorem volume_plate_rotate (u : Rotations n) (a : Space n)
    (V : Grassmannian n k) (δ : ℝ) :
    volume (plate δ (Grassmannian.rotate u V).submodule a) =
      volume (plate δ V.submodule 0) := by
  rw [← preimage_plate_rigidMotion u a V δ]
  exact ((measurePreserving_rigidMotion u a).measure_preimage
    Metric.isOpen_thickening.measurableSet.nullMeasurableSet).symm

end NKBesicovitch
