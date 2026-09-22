import PrimeFactorUnimodality.Helpers.Analytic.DusartPrimeCountingAssembly
import PrimeFactorUnimodality.Helpers.Analytic.DusartThetaClosedPart02
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.PrimeCountingLogBounds
import PrimeFactorUnimodality.Helpers.FiniteCertificates.PrimePrefixCounts

set_option autoImplicit false

/-! # Regression checks for the independent Dusart analytic modules

These tests exercise the strict numerical margin, power-sum decomposition,
and reusable prime-count and logarithm enclosures without generated tables.
-/

namespace PrimeFactorUnimodality.Tests

example {x b q : Real} {k : Nat}
    (hb : 1 ≤ b) (hbx : b ≤ x) (hk : 3 ≤ k) (hq : 0 ≤ q)
    (h : 1 ≤ q ^ (3 * k) * b ^ (k - 3)) :
    x ^ (1 / (k : Real)) ≤ q * x ^ (1 / (3 : Real)) :=
  dusart_rpow_ratio_bound hb hbx hk hq h

example {y : Real} (hy : (4e18 : Real) ≤ y)
    (herror : |Chebyshev.theta y - y| ≤
      (648 : Real) / 1000 * y / Real.log y ^ 4) :
    (9999 : Real) / 10000 * y < Chebyshev.theta y :=
  theta_lower_9999_of_logFourth_error_at_large_strict hy herror

example {x : Real} (hx : 9 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x - Chebyshev.theta (Real.sqrt x) =
      ∑ k ∈ Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊,
        Chebyshev.theta (x ^ (1 / (k : Real))) :=
  dusart_lemma_3_3_prime_power_decomposition hx

example : Nat.primeCounting 7 = 4 := by
  have hlist : computablePrimesBelow 12 = [2, 3, 5, 7, 11] := by decide +kernel
  rw [primeCounting_eq_filter_length_of_prime_prefix (N := 11) (by norm_num) hlist]
  decide

example : ((4 : Real) * (693147 / 1000000) +
    (2 : Real) * (1098612 / 1000000) +
    (4 : Real) * (1609437 / 1000000)) / 2 ≤ Real.log 600 :=
  log_nat_lower_of_smooth_power (s := 2) (by norm_num) (by norm_num)

example : Real.log 600 ≤ ((6 : Real) * (693148 / 1000000) +
    (2 : Real) * (1098613 / 1000000) +
    (4 : Real) * (1609438 / 1000000)) / 2 :=
  log_nat_upper_of_smooth_power (s := 2) (by norm_num) (by norm_num) (by norm_num)

end PrimeFactorUnimodality.Tests
