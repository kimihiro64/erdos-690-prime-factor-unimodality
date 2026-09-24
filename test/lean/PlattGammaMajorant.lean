import PrimeFactorUnimodality.Helpers.Analytic.PlattGammaMajorant

/-! The Gamma-window bound covers both height signs and the first admissible shift. -/

open PrimeFactorUnimodality

example (m k : Nat) (hm : 1 ≤ m) (t₀ h v : Real) (ht₀ : 0 ≤ t₀) :
    plattGammaWindow m k t₀ h v ≤
      Real.sqrt (2 * Real.pi) / 2 ^ m * (t₀ + |v| + 2 * (m : Real) - 1) ^ m *
        (2 * (m : Real) + 3 / 2 + |v|) ^ k * Real.exp (-v ^ 2 / (2 * h ^ 2)) :=
  plattGammaWindow_le_polynomial m k hm ht₀ h v

example (v : Real) :
    plattGammaWindow 1 0 1000 1 v ≤
      Real.sqrt (2 * Real.pi) / 2 ^ 1 * (1000 + |v| + 2 * (1 : Real) - 1) ^ 1 *
        (2 * (1 : Real) + 3 / 2 + |v|) ^ 0 * Real.exp (-v ^ 2 / (2 * (1 : Real) ^ 2)) := by
  simpa only [Nat.cast_one] using
    plattGammaWindow_le_polynomial 1 0 (by omega) (t₀ := 1000) (by norm_num) 1 v
