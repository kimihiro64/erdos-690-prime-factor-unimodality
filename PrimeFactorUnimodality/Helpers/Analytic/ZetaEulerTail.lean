import PrimeFactorUnimodality.Helpers.Analytic.ZetaFiniteApproximation
import PrimeFactorUnimodality.Mathlib.NumberTheory.BernoulliPeriodic

/-! # Complete higher-order Euler tails for arbitrary zeta evaluation points

Adapted from `RobinBV.Sieve.nontrivial_zero_euler_first` and
`nontrivial_zero_euler_expansion`, Jonas Whidden, Apache-2.0 WIPResearch
commit `bdc46941c4f2e13fb84e0a338b905bb10e711357`.
The zero premise is removed: the starting identity is the pinned PNT
continuation formula at every positive real part away from the pole.
The extracted Bernoulli recursion retains all boundary corrections.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory Polynomial Set

/-- The rising factorial appearing in successive Euler corrections. -/
def zetaRisingFactor (s : ℂ) (k : ℕ) : ℂ :=
  ∏ r ∈ Finset.range k, (s + (r : ℂ))

/-- One further integration by parts introduces the next rising factor. -/
theorem zetaRisingFactor_succ (s : ℂ) (k : ℕ) :
    zetaRisingFactor s (k + 1) = zetaRisingFactor s k * (s + (k : ℂ)) :=
  Finset.prod_range_succ _ _

/-- The entire periodic Bernoulli integral at the specified order. -/
def zetaEulerTail (N : ℕ) (s : ℂ) (k : ℕ) : ℂ :=
  ∫ x in Ioi (N : ℝ), (bernoulliPeriodic k x : ℂ) * (x : ℂ) ^ (-s - (k : ℂ))

/-- The first Euler discrepancy is exactly the normalized first Bernoulli tail. -/
theorem riemannZeta_sub_eulerApprox_eq_tail {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s - zetaEulerApprox N s = -s * zetaEulerTail N s 1 := by
  rw [riemannZeta_sub_eulerApprox hN hs hs1]
  have hB (x : ℝ) : bernoulliPeriodic 1 x = x - (⌊x⌋ : ℝ) - 1 / 2 := by
    simp only [bernoulliPeriodic, bernoulliNormalizedReal, bernoulliNormalized,
      Nat.factorial_one, Nat.cast_one, div_one, map_one, one_mul,
      Polynomial.bernoulli_one, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Int.fract]
    norm_num
  have hI : (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)) =
      -zetaEulerTail N s 1 := by
    rw [zetaEulerTail, ← integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      dsimp only
      rw [hB x, div_eq_mul_inv, ← cpow_neg]
      push_cast
      rw [show -(s + 1) = -s - 1 by ring]
      ring)
  rw [hI]
  ring

/-- The next-order identity is valid without assuming that the evaluation point is a zero. -/
theorem zetaEulerTail_recursion {N k : ℕ} (hN : 0 < N) (hk : 1 ≤ k)
    {s : ℂ} (hs : 0 < s.re) :
    zetaEulerTail N s k =
      -(bernoulliNormalizedReal (k + 1) 0 : ℂ) * (N : ℂ) ^ (-s - (k : ℂ)) +
        (s + (k : ℂ)) * zetaEulerTail N s (k + 1) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hz : (-s - (k : ℂ)).re < -1 := by
    simp only [sub_re, neg_re, natCast_re]
    linarith
  have h := bernoulliPeriodic_cpow_tail_recursion hk hN hz
  have he : -s - (k : ℂ) - 1 = -s - ((k + 1 : ℕ) : ℂ) := by push_cast; ring
  calc
    _ = -(bernoulliNormalizedReal (k + 1) 0 : ℂ) * (N : ℂ) ^ (-s - (k : ℂ)) -
        (-s - (k : ℂ)) * zetaEulerTail N s (k + 1) := by
      simpa only [zetaEulerTail, he, Complex.ofReal_natCast] using h
    _ = _ := by ring

/-- A finite rational coefficient bound controls the full higher-order tail. -/
theorem norm_zetaEulerTail_le {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re)
    (m : ℕ) :
    ‖zetaEulerTail N s (m + 1)‖ ≤ (bernoulliCoeffBound (m + 1) : ℝ) *
      (N : ℝ) ^ (-s.re - (m : ℝ)) / (s.re + (m : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hz : (-s - ((m + 1 : ℕ) : ℂ)).re < -1 := by
    simp only [sub_re, neg_re, natCast_re, Nat.cast_add, Nat.cast_one, add_re, one_re]
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have h := norm_bernoulliPeriodic_cpow_tail_le (m + 1) hN0 hz
  have he : (-s - ((m + 1 : ℕ) : ℂ)).re + 1 = -(s.re + (m : ℝ)) := by
    simp only [sub_re, neg_re, natCast_re, Nat.cast_add, Nat.cast_one, add_re, one_re]
    ring
  rw [he, neg_div_neg_eq] at h
  simpa only [zetaEulerTail, neg_add_rev, sub_eq_add_neg, mul_div_assoc, add_comm] using h

end

end PrimeFactorUnimodality
