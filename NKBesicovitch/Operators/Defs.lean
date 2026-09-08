/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import NKBesicovitch.Grassmannian.Basic
public import NKBesicovitch.Geometry.Disks
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Nonnegative disk and plate maximal operators

Integrals and suprema take values in the extended nonnegative reals. A plate is
the open delta-neighborhood of a closed unit disk. Analytic bounds will require
positive delta and establish that every normalizing volume is positive and finite.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch

variable {n k : ℕ}

/-- The open delta-neighborhood of a radius-one disk. -/
def plate (δ : ℝ) (V : Submodule ℝ (Space n)) (a : Space n) : Set (Space n) :=
  Metric.thickening δ (unitDisk V a)

/-- The average of a nonnegative function over a unit disk in its intrinsic volume. -/
noncomputable def diskAverage (f : Space n → ℝ≥0∞) (V : Grassmannian n k) (a : Space n) :
    ℝ≥0∞ :=
  (∫⁻ v in Metric.closedBall (0 : V.submodule) 1, f (a + v)) /
    volume (Metric.closedBall (0 : V.submodule) 1)

/-- The supremum of the normalized unit-disk integrals in a fixed direction. -/
noncomputable def diskMaximal (f : Space n → ℝ≥0∞) (V : Grassmannian n k) : ℝ≥0∞ :=
  ⨆ a : Space n, diskAverage f V a

/-- The supremum of averages over thickened unit disks in a fixed direction. -/
noncomputable def plateMaximal (δ : ℝ) (f : Space n → ℝ≥0∞) (V : Grassmannian n k) :
    ℝ≥0∞ :=
  ⨆ a : Space n, (∫⁻ x in plate δ V.submodule a, f x) / volume (plate δ V.submodule a)

/-- The nonnegative local X-ray transform in slope-intercept coordinates. -/
noncomputable def localXRay (f : Space n × ℝ → ℝ≥0∞) (ξ x : Space n) : ℝ≥0∞ :=
  ∫⁻ t in Icc (0 : ℝ) 1, f (x + t • ξ, t)

end NKBesicovitch
