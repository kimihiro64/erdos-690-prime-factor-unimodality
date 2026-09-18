import Mathlib.Data.Nat.Log
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitPrimeCounting
import PrimeFactorUnimodality.Proof.LargeRange.TailPrimorialBounds

set_option autoImplicit false

/-! # Prime-prefix bounds for the uniform tail -/

namespace PrimeFactorUnimodality

noncomputable section

/-- A convenient integral upper comparison for the `(r+1)`-st prime. -/
def tailPrimeUpper (r : Nat) : Nat := r * (Nat.log 2 r)

private theorem tail_log_index_lt_log_two_mul {r : Nat} (hr : 1 ≤ r) :
    Real.log r < ((Nat.log 2 r + 1 : Nat) : Real) * Real.log 2 := by
  have r_lt : r < 2 ^ (Nat.log 2 r + 1) :=
    (Nat.log_lt_iff_lt_pow (by omega) (by omega)).mp (by omega)
  have cast_lt : (r : Real) < (2 : Real) ^ (Nat.log 2 r + 1) := by
    exact_mod_cast r_lt
  have logged := Real.log_lt_log (by exact_mod_cast (show 0 < r by omega)) cast_lt
  rw [Real.log_pow] at logged
  simpa only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using logged

theorem tail_log_upper_lt {r : Nat} (hr : 38000 ≤ r) :
    Real.log (tailPrimeUpper r) <
      ((Nat.log 2 r : Nat) : Real) := by
  let L := Nat.log 2 r
  have fifteenLog : 15 ≤ Nat.log 2 r := by
    apply Nat.le_log_of_pow_le (by omega)
    norm_num
    omega
  have Lpos : 0 < L := by dsimp only [L]; omega
  have rpos : 0 < r := by omega
  have logR := tail_log_index_lt_log_two_mul (show 1 ≤ r by omega)
  have logFive : Real.log 5 < (17 : Real) / 10 := by
    have squareLt : (5 : Real) ^ 2 < 3 ^ 3 := by norm_num
    have logged := Real.log_lt_log (by positivity) squareLt
    rw [Real.log_pow, Real.log_pow] at logged
    norm_num at logged ⊢
    nlinarith [Real.log_three_lt_d9]
  have logL : Real.log L < (L : Real) / 4 := by
    have ratioPos : (0 : Real) < L / 5 := by positivity
    have decomposition : Real.log L = Real.log 5 + Real.log (L / 5) := by
      rw [← Real.log_mul (by norm_num : (5 : Real) ≠ 0) ratioPos.ne']
      congr 2
      field_simp
    have ratioLog := Real.log_le_sub_one_of_pos ratioPos
    rw [decomposition]
    have Llarge : (14 : Real) ≤ L := by exact_mod_cast (show 14 ≤ L by dsimp only [L]; omega)
    nlinarith
  have logTwo : Real.log 2 < (7 : Real) / 10 := Real.log_two_lt_d9.trans (by norm_num)
  have logProduct :
      Real.log (tailPrimeUpper r) = Real.log r + Real.log L := by
    have h :
        Real.log ((r : Real) * (Nat.log 2 r)) =
          Real.log r + Real.log (Nat.log 2 r) := by
      rw [Real.log_mul (by exact_mod_cast rpos.ne') (by positivity)]
    simpa only [tailPrimeUpper, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
      Nat.cast_one, L] using h
  rw [logProduct]
  have Lone : (1 : Real) ≤ L := by exact_mod_cast Lpos
  have LlargeReal : (15 : Real) ≤ L := by exact_mod_cast fifteenLog
  dsimp only [L] at logR ⊢
  push_cast at logR
  nlinarith

theorem tail_dusart_lower_at_upper {r : Nat} (hr : 38000 ≤ r) :
    (r + 1 : Real) ≤ dusartPiLower (tailPrimeUpper r) := by
  let L := Nat.log 2 r
  have LnatPos : 0 < L := by
    dsimp only [L]
    have : 15 ≤ Nat.log 2 r := by
      apply Nat.le_log_of_pow_le (by omega) <;> norm_num <;> omega
    omega
  have Lpos : (0 : Real) < L := by exact_mod_cast LnatPos
  have rpos : (0 : Real) < r := by positivity
  have upperPos : (0 : Real) < tailPrimeUpper r := by
    simp only [tailPrimeUpper, L]
    positivity
  have logUpperPos : 0 < Real.log (tailPrimeUpper r) := by
    apply Real.log_pos
    have upperGt : 1 < tailPrimeUpper r := by
      simp only [tailPrimeUpper]
      have : 1 ≤ Nat.log 2 r := by exact LnatPos
      nlinarith
    exact_mod_cast upperGt
  have logUpper := tail_log_upper_lt hr
  have logUpperL : Real.log (tailPrimeUpper r) < (L : Real) := by
    simpa only [L] using logUpper
  have quotient : (r : Real) < (tailPrimeUpper r : Real) /
      Real.log (tailPrimeUpper r) := by
    rw [lt_div_iff₀ logUpperPos]
    have upperCast : (tailPrimeUpper r : Real) = r * L := by
      simp only [tailPrimeUpper, L]
      push_cast
      ring
    calc
      (r : Real) * Real.log (tailPrimeUpper r) < r * L :=
        mul_lt_mul_of_pos_left logUpperL rpos
      _ = (tailPrimeUpper r : Real) := by rw [upperCast]
  have reciprocalPos : (0 : Real) < 1 / Real.log (tailPrimeUpper r) := by
    positivity
  have factor : (1 : Real) < 1 + 1 / Real.log (tailPrimeUpper r) := by
    linarith
  have quotientPos : 0 < (tailPrimeUpper r : Real) /
      Real.log (tailPrimeUpper r) := by positivity
  unfold dusartPiLower
  have productGain := mul_lt_mul_of_pos_left factor quotientPos
  have margin : (1 : Real) ≤
      (tailPrimeUpper r : Real) / Real.log (tailPrimeUpper r) *
        (1 / Real.log (tailPrimeUpper r)) := by
    have LLeR : L ≤ r := by
      dsimp only [L]
      have := Nat.log_lt_self 2 (show r ≠ 0 by omega)
      omega
    have LLeRReal : (L : Real) ≤ r := by exact_mod_cast LLeR
    have logUpperL : Real.log (tailPrimeUpper r) < (L : Real) := by
      simpa only [L] using tail_log_upper_lt hr
    have logSq : (Real.log (tailPrimeUpper r)) ^ 2 <
        (tailPrimeUpper r : Real) := by
      have logUpperNonneg : 0 ≤ Real.log (tailPrimeUpper r) := logUpperPos.le
      have LNonneg : (0 : Real) ≤ L := by positivity
      have sqLt : (Real.log (tailPrimeUpper r)) ^ 2 < (L : Real) ^ 2 :=
        (sq_lt_sq₀ logUpperNonneg LNonneg).2 logUpperL
      have upperCast : (tailPrimeUpper r : Real) = r * L := by
        simp only [tailPrimeUpper, L]
        push_cast
        ring
      have sqBound : (L : Real) ^ 2 ≤ (tailPrimeUpper r : Real) := by
        rw [upperCast]
        nlinarith [mul_pos rpos Lpos]
      exact sqLt.trans_le sqBound
    have logSqPos : 0 < (Real.log (tailPrimeUpper r)) ^ 2 := sq_pos_of_pos logUpperPos
    have quotientForm :
        (tailPrimeUpper r : Real) / Real.log (tailPrimeUpper r) *
            (1 / Real.log (tailPrimeUpper r)) =
          (tailPrimeUpper r : Real) / (Real.log (tailPrimeUpper r)) ^ 2 := by
      field_simp
    rw [quotientForm, one_le_div₀ logSqPos]
    simpa only [one_mul] using logSq.le
  have expansion :
      (tailPrimeUpper r : Real) / Real.log (tailPrimeUpper r) *
          (1 + 1 / Real.log (tailPrimeUpper r)) =
        (tailPrimeUpper r : Real) / Real.log (tailPrimeUpper r) +
          (tailPrimeUpper r : Real) / Real.log (tailPrimeUpper r) *
            (1 / Real.log (tailPrimeUpper r)) := by ring
  rw [expansion]
  linarith

theorem tail_primeAt_le_upper
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    {r : Nat} (hr : 38000 ≤ r) :
    primeAt r ≤ tailPrimeUpper r := by
  apply primeAt_le_of_dusart_lower primeCountingBounds
  · simp only [tailPrimeUpper]
    have : 1 ≤ Nat.log 2 r := by
      apply Nat.log_pos (by omega)
      omega
    nlinarith
  · simpa only [Nat.cast_add, Nat.cast_one] using tail_dusart_lower_at_upper hr

private theorem hundred_mul_sq_le_two_pow_pred {L : Nat} (hL : 15 ≤ L) :
    100 * L ^ 2 ≤ 2 ^ L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have squareStep : 100 * (n + 1) ^ 2 ≤ 2 * (100 * n ^ 2) := by
        nlinarith
      calc
        100 * (n + 1) ^ 2 ≤ 2 * (100 * n ^ 2) := squareStep
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by rw [pow_succ]; norm_num [mul_comm]

private theorem tail_hundred_logIndex_sq_le {r : Nat} (hr : 38000 ≤ r) :
    100 * (Nat.log 2 r) ^ 2 ≤ r := by
  let L := Nat.log 2 r
  have rne : r ≠ 0 := by omega
  have fifteenLog : 15 ≤ Nat.log 2 r := by
    apply Nat.le_log_of_pow_le (by omega)
    norm_num
    omega
  have Llarge : 15 ≤ L := by dsimp only [L]; omega
  have exponential := hundred_mul_sq_le_two_pow_pred Llarge
  have powerLe : 2 ^ L ≤ r := by
    simpa only [L] using Nat.pow_log_le_self 2 rne
  exact exponential.trans powerLe

private theorem tail_log_sq_small {r : Nat} (hr : 38000 ≤ r) :
    10000 * (Real.log r) ^ 2 < 57 * r := by
  let L := Nat.log 2 r
  have logR := tail_log_index_lt_log_two_mul (show 1 ≤ r by omega)
  have logTwo : Real.log 2 < (7 : Real) / 10 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have Lpos : (0 : Real) < L := by
    exact_mod_cast (show 0 < L by
      dsimp only [L]
      exact Nat.log_pos (by omega) (by omega))
  have logRPos : 0 < Real.log r := Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have Llarge : (15 : Real) ≤ L := by
    exact_mod_cast (show 15 ≤ L by
      dsimp only [L]
      apply Nat.le_log_of_pow_le (by omega) <;> norm_num <;> omega)
  have logRBound : Real.log r < (3 / 4 : Real) * L := by
    have scaled := mul_lt_mul_of_pos_left logTwo Lpos
    push_cast at logR
    nlinarith
  have discrete := tail_hundred_logIndex_sq_le hr
  have discreteReal : (100 : Real) * (L : Real) ^ 2 ≤ r := by
    exact_mod_cast discrete
  nlinarith [sq_nonneg (Real.log r - (3 / 4 : Real) * L)]

/-- At the selected tail scale the primorial logarithm already dominates
`log r`.  This small public consequence is useful when comparing reciprocal
prime error terms with a common denominator. -/
theorem tail_log_r_lt_log_primorial
    (thetaBounds : HasDusartThetaBounds) {r q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q) :
    Real.log r < Real.log (primorial q) := by
  have logRPos : 0 < Real.log r :=
    Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have primorialLower := tail_log_primorial_lower_sharp
    thetaBounds hr scaleLtQ
  have logSq := tail_log_sq_small hr
  have coefficient : (57 / 10000 : Real) <
      (106 / 125 : Real) * (491 / 500 : Real) := by norm_num
  have scaled : (57 / 10000 : Real) * r <
      (106 / 125 : Real) * (491 / 500 : Real) * r := by
    exact mul_lt_mul_of_pos_right coefficient (by positivity)
  have squareBelow : (Real.log r) ^ 2 <
      (106 / 125 : Real) * ((491 / 500 : Real) * r) := by
    nlinarith
  have lowerAbove : Real.log r <
      (106 / 125 : Real) * ((491 / 500 : Real) * r / Real.log r) := by
    have divided : Real.log r <
        ((106 / 125 : Real) * ((491 / 500 : Real) * r)) /
          Real.log r := (lt_div_iff₀ logRPos).2 (by
      nlinarith [squareBelow])
    convert divided using 1 <;> ring
  exact lowerAbove.trans primorialLower

/-- The elementary indexed-prime comparison lies below the selected
primorial.  This closes both prefix side conditions of the CRT valley. -/
theorem tail_primeUpper_le_primorial
    (thetaBounds : HasDusartThetaBounds) {r q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q) :
    tailPrimeUpper r ≤ primorial q := by
  let L := Nat.log 2 r
  have logRPos : 0 < Real.log r := Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have scaleLog := tail_log_primorial_lower thetaBounds hr scaleLtQ
  have logSq := tail_log_sq_small hr
  have logComparison : 2 * Real.log r <
      (21 / 25 : Real) * ((491 / 500 : Real) * r / Real.log r) := by
    have core : 2 * Real.log r <
        ((21 / 25 : Real) * ((491 / 500 : Real) * r)) / Real.log r := by
      rw [lt_div_iff₀ logRPos]
      nlinarith
    convert core using 1 <;> ring
  have logRSq : Real.log ((r : Real) ^ 2) < Real.log (primorial q) := by
    rw [Real.log_pow]
    exact logComparison.trans scaleLog
  have rSqLt : r ^ 2 < primorial q := by
    by_contra h
    have reverse : primorial q ≤ r ^ 2 := Nat.le_of_not_gt h
    have logReverse : Real.log (primorial q) ≤ Real.log ((r : Real) ^ 2) := by
      apply Real.log_le_log
      · exact_mod_cast primorial_pos q
      · exact_mod_cast reverse
    exact (not_lt_of_ge logReverse) logRSq
  have LLeR : L ≤ r := by
    dsimp only [L]
    have := Nat.log_lt_self 2 (show r ≠ 0 by omega)
    omega
  have upperLeSq : tailPrimeUpper r ≤ r ^ 2 := by
    calc
      tailPrimeUpper r = r * L := by simp only [tailPrimeUpper, L]
      _ ≤ r * r := Nat.mul_le_mul_left r LLeR
      _ = r ^ 2 := by ring
  exact upperLeSq.trans rSqLt.le

theorem tail_primeAt_le_primorial
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (thetaBounds : HasDusartThetaBounds) {r q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q) :
    primeAt r ≤ primorial q :=
  (tail_primeAt_le_upper primeCountingBounds hr).trans
    (tail_primeUpper_le_primorial thetaBounds hr scaleLtQ)

theorem tail_prefix_le_primorial
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (thetaBounds : HasDusartThetaBounds) {r q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q) :
    primeAt (r - 1) - 1 ≤ primorial q := by
  exact (Nat.sub_le _ _).trans ((primeAt_strictMono.monotone (Nat.sub_le r 1)).trans
    (tail_primeAt_le_primorial primeCountingBounds thetaBounds hr scaleLtQ))

theorem tail_descentDefined
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (thetaBounds : HasDusartThetaBounds) {r q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q) :
    r ≤ Nat.primeCounting' (2 * primorial q + 1) - 1 := by
  have nextLe := tail_primeAt_le_primorial primeCountingBounds thetaBounds hr scaleLtQ
  have endpointLe : primeAt r + 1 ≤ 2 * primorial q + 1 := by
    have primorialPos : 0 < primorial q := primorial_pos q
    omega
  have countMono := Nat.count_monotone Nat.Prime endpointLe
  have countAt := Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime r
  change Nat.primeCounting' (primeAt r + 1) ≤
    Nat.primeCounting' (2 * primorial q + 1) at countMono
  rw [Nat.primeCounting', primeAt, countAt] at countMono
  have countGe : r + 1 ≤ Nat.primeCounting' (2 * primorial q + 1) := by
    exact countMono
  have shifted := Nat.sub_le_sub_right countGe 1
  simpa only [Nat.add_sub_cancel] using shifted

end

end PrimeFactorUnimodality
