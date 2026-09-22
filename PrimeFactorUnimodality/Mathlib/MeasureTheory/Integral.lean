/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.CircleAverageAntipodal
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.FinsetAbel
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageAlgebra
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageComplex
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageRegularity
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageSupport
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.Trapezoid
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IoiTranslation

/-! # Reusable integral identities and remainder estimates

Export the finite Abel identity, translation on a half-line, and complex
trapezoid remainder while keeping each leaf independently importable.
-/
