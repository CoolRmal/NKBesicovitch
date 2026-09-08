/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Grassmannian.Transitivity

/-!
# Topological properties of direction space

The projection embedding makes the Grassmannian Hausdorff and second countable.
Transitivity realizes every nonempty Grassmannian as a compact orbit.
-/

public section

namespace NKBesicovitch.Grassmannian

variable {n k : ℕ}

theorem isEmbedding_projection : Topology.IsEmbedding (projection (n := n) (k := k)) :=
  projection_injective.isEmbedding_induced

instance : T2Space (Grassmannian n k) := isEmbedding_projection.t2Space

instance : SecondCountableTopology (Grassmannian n k) :=
  isEmbedding_projection.secondCountableTopology

theorem continuous_orbit (V : Grassmannian n k) : Continuous (fun u : Rotations n ↦ rotate u V) :=
  continuous_rotate.comp (continuous_id.prodMk continuous_const)

theorem orbit_surjective (V : Grassmannian n k) :
    Function.Surjective (fun u : Rotations n ↦ rotate u V) := exists_rotate_eq V

instance : CompactSpace (Grassmannian n k) := by
  by_cases h : Nonempty (Grassmannian n k)
  · obtain ⟨V⟩ := h
    exact (orbit_surjective V).compactSpace (continuous_orbit V)
  · have : IsEmpty (Grassmannian n k) := not_nonempty_iff.mp h
    infer_instance

end NKBesicovitch.Grassmannian
