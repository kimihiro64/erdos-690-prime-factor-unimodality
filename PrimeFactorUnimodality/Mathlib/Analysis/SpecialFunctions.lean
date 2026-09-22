/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.LogShiftLimit
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.LogTrapezoid
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaConjugation
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrability.LogCauchy
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Log.AffineRatio
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Log.Deriv
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.ComplexDecay
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Trigonometric.Autocorrelation
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Trigonometric.ZeroCount

/-! # Reusable special-function candidates

Export the logarithmic, gamma, and explicit integral results through a
small facade, leaving consumers free to import individual leaves.
-/
