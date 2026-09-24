import PrimeFactorUnimodality.Proof.LargeRange.TailWeightBounds

set_option autoImplicit false

/-! # Uniform descent margins for the finite Abel shell

All numerical comparisons are exact rational inequalities between powers of
small integers. The final tangent-line argument applies to every index above
the cutoff; no enumeration of indices or record-gap witnesses is used.
-/

namespace PrimeFactorUnimodality

noncomputable section

theorem log_nat_gt_2109_div_200 {r : Nat} (hr : 38000 ≤ r) :
    (2109 / 200 : Real) < Real.log r := by
  have hpow : (2 : Real) ^ 15 * 3 ^ 26 * 5 ^ 2 < 38000 ^ 4 := by norm_num
  have h := Real.log_lt_log (by positivity) hpow
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_pow, Real.log_pow, Real.log_pow] at h
  norm_num at h
  have hb : (2109 / 200 : Real) < Real.log 38000 := by
    nlinarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]
  exact hb.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast hr))

private theorem log_2109_div_200_lt :
    Real.log (2109 / 200 : Real) < (23557 / 10000 : Real) := by
  have hpow : (2109 / 200 : Real) ^ 9 < 2 ^ 14 * 3 ^ 9 * 5 := by norm_num
  have h := Real.log_lt_log (by positivity) hpow
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h
  norm_num at h
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9]

private theorem log_ten_gt_23_div_10 : (23 / 10 : Real) < Real.log 10 := by
  rw [show (10 : Real) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  nlinarith [Real.log_two_gt_d9, Real.log_five_gt_d9]

theorem tail_ten_mul_le_prefix (bounds : HasDusartPrimeCountingBounds)
    {r : Nat} (hr : 38000 ≤ r) : 10 * r ≤ primeAt (r - 1) - 1 := by
  have rp : (0 : Real) < r := by exact_mod_cast (show 0 < r by omega)
  have logR := log_nat_gt_2109_div_200 hr
  have hlog : (12 : Real) < Real.log (10 * (r : Real)) := by
    rw [Real.log_mul (by norm_num) rp.ne']
    linarith [log_ten_gt_23_div_10]
  have lp : 0 < Real.log (10 * (r : Real)) := by linarith
  have coefficient : (10 : Real) / Real.log (10 * (r : Real)) *
      (1 + (6381 / 5000 : Real) / Real.log (10 * (r : Real))) < 1 := by
    have heq : (10 : Real) / Real.log (10 * (r : Real)) *
        (1 + (6381 / 5000 : Real) / Real.log (10 * (r : Real))) =
        10 * (Real.log (10 * (r : Real)) + 6381 / 5000) /
          (Real.log (10 * (r : Real))) ^ 2 := by
      field_simp
    rw [heq, div_lt_one (sq_pos_of_pos lp)]
    nlinarith [sq_nonneg (Real.log (10 * (r : Real)) - 12)]
  have upper : dusartPiUpper (10 * r) < (r : Real) := by
    unfold dusartPiUpper
    convert mul_lt_mul_of_pos_left coefficient rp using 1 <;> ring
  have countLt : Nat.primeCounting (10 * r) < r := by
    have h : (Nat.primeCounting (10 * r) : Real) < (r : Real) :=
      (bounds.2 (10 * r) (by omega)).trans_lt
        (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using upper)
    exact_mod_cast h
  by_contra h
  have ple : primeAt (r - 1) ≤ 10 * r := by omega
  have hm := Nat.monotone_primeCounting ple
  have hc : Nat.primeCounting (primeAt (r - 1)) = r := by
    simpa only [primeAt, Nat.primeCounting, Nat.primeCounting',
      Nat.sub_add_cancel (show 1 ≤ r by omega)] using
      Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime (r - 1)
  omega

theorem tail_descent_shell_numeric (thetaBounds : HasTailThetaBounds)
    (bounds : HasDusartPrimeCountingBounds) {r q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q) :
    (2519 / 4910 : Real) * Real.log r <
      Real.log (Real.log ((primorial q : Nat) : Real)) -
        Real.log (Real.log ((primeAt (r - 1) - 1 : Nat) : Real)) -
        (6381 / 5000 : Real) / (Real.log ((primeAt (r - 1) - 1 : Nat) : Real)) ^ 2 -
        1 / ((primeAt (r - 1) - 1 : Nat) : Real) := by
  let v : Real := Real.log r
  let v₀ : Real := 2109 / 200
  let X : Nat := primeAt (r - 1) - 1
  have vl : v₀ < v := log_nat_gt_2109_div_200 hr
  have vp : 0 < v := by dsimp only [v₀] at vl; linarith
  have v₀p : 0 < v₀ := by norm_num [v₀]
  have xlower : 10 * r ≤ X := tail_ten_mul_le_prefix bounds hr
  have xl : (380000 : Real) ≤ X := by exact_mod_cast (show 380000 ≤ X by omega)
  have lx : v₀ + 23 / 10 < Real.log X := by
    have h := Real.log_le_log (show (0 : Real) < 10 * (r : Real) by positivity)
      (show 10 * (r : Real) ≤ X by exact_mod_cast xlower)
    rw [Real.log_mul (by norm_num) (by positivity)] at h
    dsimp only [v] at vl
    exact (add_lt_add vl log_ten_gt_23_div_10).trans_le (by simpa only [add_comm] using h)
  have invSquare : (6381 / 5000 : Real) / (Real.log X) ^ 2 ≤
      (6381 / 5000 : Real) / (v₀ + 23 / 10) ^ 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact pow_le_pow_left₀ (by positivity) lx.le 2
  have invX : (1 : Real) / X ≤ 1 / 380000 :=
    one_div_le_one_div_of_le (by norm_num) xl
  have logDecomposition : Real.log v = Real.log v₀ + Real.log (v / v₀) := by
    rw [← Real.log_mul v₀p.ne' (show v / v₀ ≠ 0 by positivity)]
    congr 1
    field_simp
  have logUpper : Real.log v < 23557 / 10000 + (v / v₀ - 1) := by
    rw [logDecomposition]
    have h := Real.log_le_sub_one_of_pos (show 0 < v / v₀ by positivity)
    have h₀ := log_2109_div_200_lt
    dsimp only [v₀] at h ⊢
    linarith
  have shell := tail_descent_loglog_shell_lower_sharp thetaBounds bounds hr scaleLtQ
  dsimp only [v₀] at invSquare vl logUpper
  norm_num at invSquare
  dsimp only [v, X] at logUpper invSquare invX vl ⊢
  nlinarith

theorem tail_descent_numeric_of_primeCounting
    (thetaBounds : HasTailThetaBounds) (bounds : HasDusartPrimeCountingBounds)
    {r qPrev q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q)
    (scalePrev : (491 / 500 : Real) * r / Real.log r <
      (2519 / 2500 : Real) * qPrev) :
    (r : Real) < ((2 * qPrev + 1 : Nat) : Real) *
      (Real.log (Real.log ((primorial q : Nat) : Real)) -
        Real.log (Real.log ((primeAt (r - 1) - 1 : Nat) : Real)) -
        (6381 / 5000 : Real) / (Real.log ((primeAt (r - 1) - 1 : Nat) : Real)) ^ 2 -
        1 / ((primeAt (r - 1) - 1 : Nat) : Real)) := by
  have bracket := tail_descent_shell_numeric thetaBounds bounds hr scaleLtQ
  have lp : 0 < Real.log r := Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have cross : (491 / 500 : Real) * r <
      (2519 / 2500 : Real) * qPrev * Real.log r :=
    (div_lt_iff₀ lp).mp (by convert scalePrev using 1)
  have qp : (0 : Real) < qPrev := by
    have rp : (0 : Real) < r := by exact_mod_cast (show 0 < r by omega)
    by_contra h
    have qn : (qPrev : Real) ≤ 0 := le_of_not_gt h
    nlinarith [mul_nonpos_of_nonpos_of_nonneg qn lp.le]
  have raised := mul_lt_mul_of_pos_left bracket (show (0 : Real) < 2 * qPrev by positivity)
  push_cast
  nlinarith

end

end PrimeFactorUnimodality
