/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.Selection.TreeParameters
public import Mathlib.Tactic.FinCases

/-!
# Measurable labeled heights of a selected tree

The labels record the root triple, every outer height, and all child-tree
heights recursively. Inner heights and their duals occur in the child
root triples. The height maps are jointly measurable, and selected
parameters put every labeled height in the original time set.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection

/-- Labels of all heights used by a complete corner tree. -/
def TreeTimeLabel (L : ℕ) : ℕ → Type
  | 0 => Fin 3
  | J + 1 => (Fin 3 ⊕ Fin L) ⊕ ((Fin L × Fin L) × TreeTimeLabel L J)

instance instFintypeTreeTimeLabel (L : ℕ) : (J : ℕ) → Fintype (TreeTimeLabel L J)
  | 0 => inferInstanceAs (Fintype (Fin 3))
  | J + 1 => by
      letI : Fintype (TreeTimeLabel L J) := instFintypeTreeTimeLabel L J
      exact inferInstanceAs (Fintype ((Fin 3 ⊕ Fin L) ⊕ ((Fin L × Fin L) × TreeTimeLabel L J)))

/-- The three root labels at any depth. -/
def TreeTimeLabel.base (L : ℕ) : (J : ℕ) → Fin 3 → TreeTimeLabel L J
  | 0 => fun i ↦ i
  | _ + 1 => fun i ↦ Sum.inl (Sum.inl i)

namespace SelectableProjectionScheme

variable {m D L : ℕ} {β : ℝ} (S : SelectableProjectionScheme m β D L)

/-- The numerical height associated with a tree label. -/
noncomputable def treeTime : (J : ℕ) → ((ℝ × ℝ) × ℝ) →
    (TreeCoordinate D L J → ℝ) → TreeTimeLabel L J → ℝ
  | 0, q, _, i => ![q.1.1, q.1.2, q.2] i
  | _ + 1, q, _, Sum.inl (Sum.inl i) => ![q.1.1, q.1.2, q.2] i
  | J + 1, _, σ, Sum.inl (Sum.inr i) => S.time (TreeCoordinate.splitEquiv D L J σ).1.2.1 i
  | J + 1, q, σ, Sum.inr (ij, i) =>
      treeTime J (S.nodeChildTriple q.1.1 q.1.2 q.2 (TreeCoordinate.splitEquiv D L J σ).1 ij)
        ((TreeCoordinate.splitEquiv D L J σ).2 ij) i

theorem treeTime_base (J : ℕ) (q : (ℝ × ℝ) × ℝ) (σ : TreeCoordinate D L J → ℝ) (i : Fin 3) :
    S.treeTime J q σ (TreeTimeLabel.base L J i) = ![q.1.1, q.1.2, q.2] i := by
  cases J <;> rfl

theorem measurable_treeTime (J : ℕ) {X : Type*} [MeasurableSpace X]
    {q : X → (ℝ × ℝ) × ℝ} {σ : X → TreeCoordinate D L J → ℝ}
    (hq : Measurable q) (hσ : Measurable σ) (i : TreeTimeLabel L J) :
    Measurable (fun x ↦ S.treeTime J (q x) (σ x) i) := by
  induction J generalizing q with
  | zero =>
    fin_cases i
    · exact hq.fst.fst
    · exact hq.fst.snd
    · exact hq.snd
  | succ J ih =>
    have hs := (TreeCoordinate.splitEquiv D L J).measurable.comp hσ
    rcases i with (i | i) | ⟨ij, i⟩
    · fin_cases i
      · exact hq.fst.fst
      · exact hq.fst.snd
      · exact hq.snd
    · exact (S.measurable_time i).comp hs.fst.snd.fst
    · exact ih (S.measurable_nodeChildTriple hq.fst.fst hq.fst.snd hq.snd hs.fst ij)
        ((measurable_pi_apply ij).comp hs.snd) i

theorem treeTime_mem {I : Set ℝ} (hI : MeasurableSet I) (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) (J : ℕ) {q : (ℝ × ℝ) × ℝ}
    (hq : q ∈ separatedTriples I ((volume I).toReal / 100))
    {σ : TreeCoordinate D L J → ℝ} (hσ : σ ∈ S.treeParameters I J q)
    (i : TreeTimeLabel L J) : S.treeTime J q σ i ∈ I := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  induction J generalizing q with
  | zero =>
    have hbase := mem_separatedTriples.mp hq
    fin_cases i
    · exact hbase.1
    · exact hbase.2.1
    · exact hbase.2.2.1
  | succ J ih =>
    have hbase := mem_separatedTriples.mp hq
    rcases i with (i | i) | ⟨ij, i⟩
    · fin_cases i
      · exact hbase.1
      · exact hbase.2.1
      · exact hbase.2.2.1
    · exact (cornerOuterTimes_spec
        (S.cornerNodeParameters_outer_time_mem hI hIunit hIpos (by positivity) hσ.1 i)).1
    · exact ih (S.cornerNodeParameters_child_triple hI hIunit hIpos (by positivity)
        hbase.2.1 hσ.1 ij.1 ij.2) (hσ.2 ij) i

/-- The finite set of all labeled heights of a tree parameter. -/
noncomputable def treeTimes (J : ℕ) (q : (ℝ × ℝ) × ℝ) (σ : TreeCoordinate D L J → ℝ) : Finset ℝ :=
  Finset.univ.image (S.treeTime J q σ)

theorem mem_treeTimes {J : ℕ} {q : (ℝ × ℝ) × ℝ} {σ : TreeCoordinate D L J → ℝ} {t : ℝ} :
    t ∈ S.treeTimes J q σ ↔ ∃ i, S.treeTime J q σ i = t := by
  classical
  simp only [treeTimes, Finset.mem_image, Finset.mem_univ, true_and]

theorem base_mem_treeTimes (J : ℕ) (q : (ℝ × ℝ) × ℝ) (σ : TreeCoordinate D L J → ℝ)
    (i : Fin 3) : ![q.1.1, q.1.2, q.2] i ∈ S.treeTimes J q σ :=
  S.mem_treeTimes.mpr ⟨TreeTimeLabel.base L J i, S.treeTime_base J q σ i⟩

theorem child_treeTimes_subset (J : ℕ) (q : (ℝ × ℝ) × ℝ)
    (σ : TreeCoordinate D L (J + 1) → ℝ) (ij : Fin L × Fin L) :
    S.treeTimes J (S.nodeChildTriple q.1.1 q.1.2 q.2 (TreeCoordinate.splitEquiv D L J σ).1 ij)
      ((TreeCoordinate.splitEquiv D L J σ).2 ij) ⊆ S.treeTimes (J + 1) q σ := by
  intro t ht
  obtain ⟨i, hi⟩ := S.mem_treeTimes.mp ht
  exact S.mem_treeTimes.mpr ⟨Sum.inr (ij, i), hi⟩

theorem treeTimes_subset {I : Set ℝ} (hI : MeasurableSet I) (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) (J : ℕ) {q : (ℝ × ℝ) × ℝ}
    (hq : q ∈ separatedTriples I ((volume I).toReal / 100))
    {σ : TreeCoordinate D L J → ℝ} (hσ : σ ∈ S.treeParameters I J q) :
    ∀ t ∈ S.treeTimes J q σ, t ∈ I := by
  intro t ht
  obtain ⟨i, rfl⟩ := S.mem_treeTimes.mp ht
  exact S.treeTime_mem hI hIunit hIpos J hq hσ i

end SelectableProjectionScheme

end NKBesicovitch.Projection.Selection
