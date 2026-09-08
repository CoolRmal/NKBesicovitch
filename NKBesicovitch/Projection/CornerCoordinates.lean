/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Projection.PairCode

/-!
# Intrinsic corner coordinates

A corner is encoded by its middle line and the slopes of its first and last
lines. The first line meets the middle line at height `a`, and the last meets
it at height `b`. Lebesgue measure in these four vector coordinates is the
intrinsic corner measure used in the supplied manuscript.
-/

@[expose] public section

open MeasureTheory Set

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- Middle-line intercept and slope, followed by the first and last slopes. -/
abbrev CornerCoordinates (m : ℕ) := Line m × (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))

/-- First line of a corner, recovered from its first junction. -/
def cornerFirst (a : ℝ) (p : CornerCoordinates m) : Line m :=
  lineAt a (atHeight a p.1) p.2.1

/-- Last line of a corner, recovered from its second junction. -/
def cornerLast (b : ℝ) (p : CornerCoordinates m) : Line m :=
  lineAt b (atHeight b p.1) p.2.2

theorem atHeight_cornerFirst (a : ℝ) (p : CornerCoordinates m) :
    atHeight a (cornerFirst a p) = atHeight a p.1 := by
  simp [cornerFirst, atHeight_lineAt]

theorem atHeight_cornerLast (b : ℝ) (p : CornerCoordinates m) :
    atHeight b (cornerLast b p) = atHeight b p.1 := by
  simp [cornerLast, atHeight_lineAt]

/-- Parent pair, ordered as middle line then first line. -/
def cornerParent (a : ℝ) (p : CornerCoordinates m) : PairCoordinates m :=
  (atHeight a p.1, (p.1.2, p.2.1))

/-- Inner pair, ordered as middle line then last line. -/
def cornerInner (b : ℝ) (p : CornerCoordinates m) : PairCoordinates m :=
  (atHeight b p.1, (p.1.2, p.2.2))

theorem first_cornerParent (a : ℝ) (p : CornerCoordinates m) :
    lineAt a (cornerParent a p).1 (cornerParent a p).2.1 = p.1 := lineAt_atHeight a p.1

theorem second_cornerParent (a : ℝ) (p : CornerCoordinates m) :
    lineAt a (cornerParent a p).1 (cornerParent a p).2.2 = cornerFirst a p := rfl

theorem first_cornerInner (b : ℝ) (p : CornerCoordinates m) :
    lineAt b (cornerInner b p).1 (cornerInner b p).2.1 = p.1 := lineAt_atHeight b p.1

theorem second_cornerInner (b : ℝ) (p : CornerCoordinates m) :
    lineAt b (cornerInner b p).1 (cornerInner b p).2.2 = cornerLast b p := rfl

/-- Intrinsic corners formed by three lines in one family. -/
def cornerFamily (a b : ℝ) (G : Set (Line m)) : Set (CornerCoordinates m) :=
  {p | cornerFirst a p ∈ G ∧ p.1 ∈ G ∧ cornerLast b p ∈ G}

theorem measurableSet_cornerFamily (a b : ℝ) {G : Set (Line m)} (hG : MeasurableSet G) :
    MeasurableSet (cornerFamily a b G) := by
  have h₁ : Continuous (cornerFirst (m := m) a) := by
    unfold cornerFirst lineAt atHeight
    fun_prop
  have h₃ : Continuous (cornerLast (m := m) b) := by
    unfold cornerLast lineAt atHeight
    fun_prop
  exact (hG.preimage h₁.measurable).inter
    ((hG.preimage measurable_fst).inter (hG.preimage h₃.measurable))

theorem cornerParent_mem_pairFamily {a b : ℝ} {G : Set (Line m)}
    {p : CornerCoordinates m} (hp : p ∈ cornerFamily a b G) : cornerParent a p ∈ pairFamily a G :=
  ⟨by simpa only [first_cornerParent] using hp.2.1, hp.1⟩

theorem cornerInner_mem_pairFamily {a b : ℝ} {G : Set (Line m)}
    {p : CornerCoordinates m} (hp : p ∈ cornerFamily a b G) : cornerInner b p ∈ pairFamily b G :=
  ⟨by simpa only [first_cornerInner] using hp.2.1, hp.2.2⟩

end NKBesicovitch.Projection
