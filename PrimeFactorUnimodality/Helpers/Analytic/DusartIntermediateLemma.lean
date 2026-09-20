import PrimeFactorUnimodality.Helpers.Analytic.DusartIntermediatePower
import PrimeFactorUnimodality.Helpers.Analytic.DusartIntermediateIndex

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PrimeFactorUnimodality

noncomputable section

/- Dusart's Lemma 3.3 on the interval between the direct computation and the
   analytic tail.  The prime-power decomposition and the coefficient table
   are assembled here without introducing a new analytic provider. -/
theorem dusart_lemma_3_3_intermediate
    {x : Real} (hlo : (10 : Real) ^ 7 ≤ x)
    (hhi : x ≤ (10 : Real) ^ 33)
    (theta_upper : ∀ y : Real, 0 < y →
      Chebyshev.theta y < (1000081 : Real) / 1000000 * y) :
    Chebyshev.psi x - Chebyshev.theta x -
        Chebyshev.theta (Real.sqrt x) <
      (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  have hxpos : 0 < x := by
    have : (0 : Real) < 10 ^ 7 := by norm_num
    exact this.trans_le hlo
  have hxone : 1 ≤ x := by
    have : (1 : Real) ≤ 10 ^ 7 := by norm_num
    exact this.trans hlo
  have hidx := dusart_intermediate_log_index_bounds hlo hhi
  let N : Nat := ⌊Real.log x / Real.log 2⌋₊
  have hN3 : 3 ≤ N := by omega
  have hsum := dusart_intermediate_power_sum_bound_relaxed hxone
    hidx.1 hidx.2 (dusart_floor_two_pow_le hxone)
  have htheta_sum :
      (∑ k ∈ Finset.Icc 3 N,
        Chebyshev.theta (x ^ (1 / (k : Real)))) <
      (1000081 : Real) / 1000000 *
        (∑ k ∈ Finset.Icc 3 N, x ^ (1 / (k : Real))) := by
    apply Finset.sum_lt_sum_of_nonempty
    · simp [hN3]
    · intro k hk
      apply theta_upper
      positivity
  have hdecomp := dusart_lemma_3_3_prime_power_decomposition
    (x := x) (by norm_num at hlo ⊢; linarith)
  have hcoef :
      (1000081 : Real) / 1000000 * ((1777 : Real) / 1000) <
        (1777745 : Real) / 1000000 := by norm_num
  dsimp [N] at hdecomp hsum htheta_sum
  calc
    Chebyshev.psi x - Chebyshev.theta x -
        Chebyshev.theta (Real.sqrt x) =
      ∑ k ∈ Finset.Icc 3 N,
        Chebyshev.theta (x ^ (1 / (k : Real))) := hdecomp
    _ < (1000081 : Real) / 1000000 *
        (∑ k ∈ Finset.Icc 3 N, x ^ (1 / (k : Real))) := htheta_sum
    _ ≤ (1000081 : Real) / 1000000 *
        ((1777 : Real) / 1000 * x ^ (1 / (3 : Real))) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = ((1000081 : Real) / 1000000 * ((1777 : Real) / 1000)) *
        x ^ (1 / (3 : Real)) := by ring
    _ < (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) :=
      mul_lt_mul_of_pos_right hcoef (by positivity)

end

end PrimeFactorUnimodularity
