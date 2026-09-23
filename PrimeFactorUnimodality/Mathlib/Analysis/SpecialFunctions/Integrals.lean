/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.CorrelationBound
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.CosineCorrelation
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ExpMoments
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ExpTrig
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogDampedParameter
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogDampedWindow
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.LogReciprocalSquarePair
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ReciprocalSquarePair
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ReciprocalSquarePairDeriv
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ReciprocalSquarePairWeighted

/-! # Finite correlation integrals and exponential moments

This facade exports explicit trigonometric correlation evaluations and
the general finite-interval square-integral bound. It also exports cubic
majorants for weighted exponential integrals in terms of four moments.
The reciprocal-pair modules add explicit improper tail integral bounds
and an exact logarithmic integral evaluation. The exponential modules also
give exact linear-weight and trigonometric endpoint formulas, with zero
exponents handled explicitly. The damped-tail modules give exact logarithmic
power integrals and closed majorants with a freely chosen power exponent.
Finite exponent-one windows instead use an elementary upper primitive.
Exponential cutoff parameters discharge the power-majorant choices exactly.
-/
