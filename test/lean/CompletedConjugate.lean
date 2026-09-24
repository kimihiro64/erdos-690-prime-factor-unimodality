import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.CompletedConjugate

/-! Regression coverage for completed-zeta conjugation, including height zero. -/

open scoped ComplexConjugate

example {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) :=
  completedRiemannZeta_conj_of_re_pos hs

example (t : ℝ) :
    conj (completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I)) =
      completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) :=
  conj_completedRiemannZeta_critical t

example : conj (completedRiemannZeta (1 / 2)) = completedRiemannZeta (1 / 2) := by
  simpa using conj_completedRiemannZeta_critical 0
