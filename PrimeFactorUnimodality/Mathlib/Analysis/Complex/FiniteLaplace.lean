/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Correlation
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.DirichletIntegral
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Monotonicity
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.PairedSeries
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.PairedStrip
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.RightResolventIntegral
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Scaling
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.WeightedBounds

/-! # Finite Laplace transformation, summability, and absolute contour pairings

This facade exports the finite-interval transform, its endpoint remainder
estimates and inversion, entire paired sums, and the Dirichlet and two-sided resolvent pairings.
It also exports exact scaling and the Volterra energy proof of positivity
for finite real correlation transforms on the closed right half-plane.
Real-source conjugation and bounded analytic strip comparison are included.
Nonnegative real sources also have an antitone real-axis transform.
Weighted-norm estimates retain the exact integral for sharp error bounds.
All imported candidates depend only on Mathlib and other candidates.
-/
