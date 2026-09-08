/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.TreeParameters
public import NKBesicovitch.Projection.Selection.NodePolynomial

/-!
# Polynomial volume of whole-tree parameters

Splitting the coordinates gives an exact recursive integral for selection
volume. The one-node lower bound and preservation of separated child
triples then give a positive polynomial lower bound at every finite depth.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection

/-- The number of nonterminal nodes in the complete tree of label pairs. -/
def treeNodeCount (L : ℕ) : ℕ → ℕ
  | 0 => 0
  | J + 1 => 1 + L * L * treeNodeCount L J

namespace SelectableProjectionScheme

variable {m D L : ℕ} {β : ℝ} (S : SelectableProjectionScheme m β D L)

theorem volume_treeParameters_succ {I : Set ℝ} (hI : MeasurableSet I)
    (J : ℕ) (q : (ℝ × ℝ) × ℝ) :
    volume (S.treeParameters I (J + 1) q) =
      ∫⁻ p in S.cornerNodeParameters I q.1.1 q.1.2 q.2 ((volume I).toReal / 100),
        ∏ ij : Fin L × Fin L,
          volume (S.treeParameters I J (S.nodeChildTriple q.1.1 q.1.2 q.2 p ij)) := by
  rw [S.treeParameters_succ,
    (TreeCoordinate.volume_preserving_splitEquiv D L J).measure_preimage_equiv,
    Measure.volume_eq_prod, Measure.prod_apply (S.measurableSet_treeStepParameters hI J q),
    ← lintegral_indicator (S.measurableSet_cornerNodeParameters hI _ _ _ _)]
  apply lintegral_congr
  intro p
  by_cases hp : p ∈ S.cornerNodeParameters I q.1.1 q.1.2 q.2 ((volume I).toReal / 100)
  · rw [indicator_of_mem hp]
    have he : Prod.mk p ⁻¹' S.treeStepParameters I J q =
        univ.pi (fun ij ↦ S.treeParameters I J (S.nodeChildTriple q.1.1 q.1.2 q.2 p ij)) := by
      ext ρ
      simp only [treeStepParameters, mem_preimage, mem_ofPred_eq, hp, true_and,
        mem_pi, mem_univ, forall_true_left]
    rw [he, volume_pi_pi]
  · rw [indicator_of_notMem hp]
    have he : Prod.mk p ⁻¹' S.treeStepParameters I J q = ∅ := by
      ext ρ
      simp only [treeStepParameters, mem_preimage, mem_ofPred_eq, hp, false_and,
        mem_empty_iff_false]
    rw [he, measure_empty]

theorem volume_treeParameters_step_lower {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) (J : ℕ) {B : ℝ≥0∞}
    (hB : ∀ q ∈ separatedTriples I ((volume I).toReal / 100),
      B ≤ volume (S.treeParameters I J q)) {q : (ℝ × ℝ) × ℝ}
    (hq : q ∈ separatedTriples I ((volume I).toReal / 100)) :
    B ^ (L * L) * volume (S.cornerNodeParameters I q.1.1 q.1.2 q.2 ((volume I).toReal / 100)) ≤
      volume (S.treeParameters I (J + 1) q) := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  rw [S.volume_treeParameters_succ hI, ← setLIntegral_const]
  apply setLIntegral_mono' (S.measurableSet_cornerNodeParameters hI _ _ _ _)
  intro p hp
  calc
    _ = ∏ _ : Fin L × Fin L, B := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ ↦ zero_le) (fun ij _ ↦
      hB _ (S.cornerNodeParameters_child_triple hI hIunit hIpos (by positivity)
        (mem_separatedTriples.mp hq).2.1 hp ij.1 ij.2))

private theorem tree_volume_power_aux (C C₀ x : ℝ) (A N K : ℕ) :
    (C * x ^ (A * N)) ^ K * (C₀ * x ^ A) =
      (C ^ K * C₀) * x ^ (A * (1 + K * N)) := by
  simp only [Nat.mul_add, Nat.mul_one, pow_add, mul_pow, pow_mul]
  ring

/-- Uniform polynomial parameter volume at every finite depth. -/
theorem exists_tree_volume_constant (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Set ℝ, MeasurableSet I → I ⊆ Icc 0 1 → 0 < volume I →
      ∀ q ∈ separatedTriples I ((volume I).toReal / 100),
        ENNReal.ofReal (C * (volume I).toReal ^
          ((4 + (8 + 6 * L) * S.volumeExponent) * treeNodeCount L J)) ≤
            volume (S.treeParameters I J q) := by
  obtain ⟨C₀, hC₀, hnode⟩ := S.exists_node_volume_constant
  induction J with
  | zero =>
    refine ⟨1, by norm_num, fun I _ _ _ q _ ↦ ?_⟩
    change ENNReal.ofReal (1 * (volume I).toReal ^ 0) ≤
      Measure.pi (fun _ : Fin 0 ↦ (volume : Measure ℝ)) univ
    simp
  | succ J ih =>
    obtain ⟨C, hC, htree⟩ := ih
    refine ⟨C ^ (L * L) * C₀, by positivity, fun I hI hIunit hIpos q hq ↦ ?_⟩
    have h := S.volume_treeParameters_step_lower hI hIunit hIpos J
      (htree I hI hIunit hIpos) hq
    have hbound := le_trans (mul_le_mul le_rfl (hnode I hI hIunit hIpos q hq) zero_le zero_le) h
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
      tree_volume_power_aux] at hbound
    exact hbound

end SelectableProjectionScheme

end NKBesicovitch.Projection.Selection
