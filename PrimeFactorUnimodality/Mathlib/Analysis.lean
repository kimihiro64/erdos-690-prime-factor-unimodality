/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Analytic.Order.Conjugation
import PrimeFactorUnimodality.Mathlib.Analysis.Calculus.TaylorBound
import PrimeFactorUnimodality.Mathlib.Analysis.Complex
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.HorizontalIntegral
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.RationalPoint
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier
import PrimeFactorUnimodality.Mathlib.Analysis.PSeries.TailBound
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions

/-! # Reusable analytic candidates

Export calculus, complex analysis, Fourier estimates and special functions
through a bounded facade. Individual consumers can still import narrow leaves.
-/
