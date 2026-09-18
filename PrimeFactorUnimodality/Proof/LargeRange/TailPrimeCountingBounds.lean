import Mathlib.Analysis.Complex.ExponentialBounds
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitPrimeCounting
import PrimeFactorUnimodality.Proof.LargeRange.TailPrimorialBounds

set_option autoImplicit false

/-! # Prime-counting shell numerics for the optimized tail -/

namespace PrimeFactorUnimodality

noncomputable section

private theorem log_nine_sub_log_four_lt :
    Real.log 9 - Real.log 4 < (41 : Real) / 50 := by
  rw [show (9 : Real) = 3 ^ 2 by norm_num,
    show (4 : Real) = 2 ^ 2 by norm_num, Real.log_pow, Real.log_pow]
  nlinarith [Real.log_three_lt_d9, Real.log_two_gt_d9]

private theorem tail_shell_coefficient {M : Real} (hM : 2900 < M) :
    5 / M + 3 / (5 * M ^ 2) <
      9 / M * (1 + 1 / M) -
        4 / (M - 41 / 50) *
          (1 + (6381 / 5000 : Real) / (M - 41 / 50)) := by
  have MPos : 0 < M := by linarith
  let S : Real := M - (41 : Real) / 50
  have SPos : 0 < S := by
    dsimp only [S]
    linarith
  have identity :
      (9 / M * (1 + 1 / M) -
          4 / S * (1 + (6381 / 5000 : Real) / S)) -
          (5 / M + 3 / (5 * M ^ 2)) =
        ((42 / 5 : Real) * S ^ 2 -
          4 * (41 / 50 : Real) * M * S -
          4 * (6381 / 5000 : Real) * M ^ 2) /
            (M ^ 2 * S ^ 2) := by
    field_simp [MPos.ne', SPos.ne']
    ring
  have numeratorPos : (0 : Real) <
      (42 / 5 : Real) * S ^ 2 -
        4 * (41 / 50 : Real) * M * S -
        4 * (6381 / 5000 : Real) * M ^ 2 := by
    dsimp only [S]
    nlinarith [sq_nonneg (M - 2900)]
  have differencePos : (0 : Real) <
      (9 / M * (1 + 1 / M) -
          4 / S * (1 + (6381 / 5000 : Real) / S)) -
        (5 / M + 3 / (5 * M ^ 2)) := by
    rw [identity]
    exact div_pos numeratorPos (by positivity)
  dsimp only [S] at differencePos
  linarith

private theorem log_four_primorial_gt_shifted_log_nine
    (q : Nat) :
    Real.log (9 * primorial q) - (41 : Real) / 50 <
      Real.log (4 * primorial q) := by
  have PPos : (0 : Real) < primorial q := by
    exact_mod_cast primorial_pos q
  rw [Real.log_mul (by norm_num) PPos.ne',
    Real.log_mul (by norm_num) PPos.ne']
  linarith [log_nine_sub_log_four_lt]

private theorem tail_primorial_dominates_log_sq {q : Nat}
    (logLarge : 2900 < Real.log (9 * primorial q)) :
    (Real.log (9 * primorial q)) ^ 2 <
      (3 / 5 : Real) * primorial q := by
  let M := Real.log (9 * primorial q)
  have MPos : 0 ≤ M := by
    dsimp only [M]
    linarith
  have expEq : Real.exp M = (9 : Real) * primorial q := by
    dsimp only [M]
    rw [Real.exp_log (mul_pos (by norm_num) (by
      exact_mod_cast primorial_pos q))]
  have series := Real.pow_div_factorial_le_exp (x := M) MPos 4
  norm_num [Nat.factorial] at series
  rw [expEq] at series
  have M2Large : (360 : Real) < M ^ 2 := by
    dsimp only [M] at logLarge ⊢
    nlinarith
  have fourthEq : M ^ 4 = (M ^ 2) ^ 2 := by ring
  have fourthBound : M ^ 4 ≤ (216 : Real) * primorial q := by
    nlinarith [series]
  rw [fourthEq] at fourthBound
  have M2Pos : 0 < M ^ 2 := by positivity
  by_contra notLt
  have PBound : (3 : Real) * primorial q ≤ 5 * M ^ 2 := by
    dsimp only [M] at notLt ⊢
    nlinarith
  have squareBound : (M ^ 2) ^ 2 ≤ 360 * M ^ 2 := by
    nlinarith [fourthBound, PBound]
  nlinarith [mul_lt_mul_of_pos_right M2Large M2Pos]

/-- The wider shell `(4P,9P]` contains enough primes to force an average gap
strictly below `tailGapBound q`. -/
theorem tail_primeCounting_shell_numeric
    (thetaBounds : HasDusartThetaBounds) {r q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q)
    (qUpper : (q : Real) < (2519 / 2500 : Real) *
      ((491 / 500 : Real) * r / Real.log r)) :
    ((5 * primorial q : Nat) : Real) / tailGapBound q + 1 <
      dusartPiLower (9 * primorial q) -
        dusartPiUpper (4 * primorial q) := by
  let P : Nat := primorial q
  let M : Real := Real.log (9 * P)
  let L : Real := Real.log (4 * P)
  have PPos : (0 : Real) < P := by
    exact_mod_cast primorial_pos q
  have logPLower := tail_log_primorial_lower thetaBounds hr scaleLtQ
  have scaleLower := tailScale_gt_3500 hr
  have logLarge : (2900 : Real) < M := by
    have logP2900 : (2900 : Real) < Real.log P := by
      dsimp only [P]
      nlinarith
    have logPLeM : Real.log P ≤ M := by
      dsimp only [M, P]
      exact Real.log_le_log (by positivity) (by
        nlinarith [show (0 : Real) < primorial q by positivity])
    exact logP2900.trans_le logPLeM
  have MPos : 0 < M := by linarith
  have shiftedPos : 0 < M - (41 : Real) / 50 := by linarith
  have shiftedLtL : M - (41 : Real) / 50 < L := by
    dsimp only [M, L, P]
    exact log_four_primorial_gt_shifted_log_nine q
  have LPos : 0 < L := shiftedPos.trans shiftedLtL
  have upperCompare :
      dusartPiUpper (4 * P) <
        ((4 : Real) * P) / (M - 41 / 50) *
          (1 + (6381 / 5000 : Real) / (M - 41 / 50)) := by
    unfold dusartPiUpper
    change ((4 : Real) * P) / L *
        (1 + (6381 / 5000 : Real) / L) < _
    have first : ((4 : Real) * P) / L <
        ((4 : Real) * P) / (M - 41 / 50) := by
      exact div_lt_div_of_pos_left (by positivity) shiftedPos shiftedLtL
    have second : 1 + (6381 / 5000 : Real) / L <
        1 + (6381 / 5000 : Real) / (M - 41 / 50) := by
      have := div_lt_div_of_pos_left (show (0 : Real) < 6381 / 5000 by norm_num)
        shiftedPos shiftedLtL
      linarith
    exact mul_lt_mul first second.le (by positivity) (by positivity)
  have coefficient := tail_shell_coefficient logLarge
  have lowerExact : dusartPiLower (9 * P) =
      ((9 : Real) * P) / M * (1 + 1 / M) := by
    unfold dusartPiLower
    rfl
  have boundAboveLog : M < tailGapBound q := by
    dsimp only [M, P]
    exact tail_log_nine_primorial_lt_gapBound thetaBounds hr scaleLtQ qUpper
  have boundPos : (0 : Real) < tailGapBound q := by
    exact_mod_cast (show 0 < tailGapBound q by
      exact Nat.zero_lt_of_lt (tailGapBound_pos q))
  have widthCompare : ((5 * P : Nat) : Real) / tailGapBound q <
      ((5 * P : Nat) : Real) / M := by
    exact div_lt_div_of_pos_left (by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      positivity) MPos boundAboveLog
  have remainder := tail_primorial_dominates_log_sq (q := q) (by
    simpa only [M, P] using logLarge)
  rw [lowerExact]
  have coefficientScaled := mul_lt_mul_of_pos_left coefficient PPos
  have M2Pos : 0 < M ^ 2 := by positivity
  have bonus : (1 : Real) < (P : Real) * (3 / (5 * M ^ 2)) := by
    have fiveM2 : (5 : Real) * M ^ 2 < 3 * P := by
      dsimp only [M, P]
      nlinarith [remainder]
    rw [show (P : Real) * (3 / (5 * M ^ 2)) =
      (3 * P) / (5 * M ^ 2) by ring]
    rw [lt_div_iff₀ (by positivity : (0 : Real) < 5 * M ^ 2)]
    simpa only [one_mul] using fiveM2
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at coefficientScaled widthCompare ⊢
  have core :
      5 * (P : Real) / M + (P : Real) * (3 / (5 * M ^ 2)) <
        9 * (P : Real) / M * (1 + 1 / M) -
          4 * (P : Real) / (M - 41 / 50) *
            (1 + (6381 / 5000 : Real) / (M - 41 / 50)) := by
    calc
      5 * (P : Real) / M + (P : Real) * (3 / (5 * M ^ 2)) =
          (P : Real) * (5 / M + 3 / (5 * M ^ 2)) := by ring
      _ < (P : Real) *
          (9 / M * (1 + 1 / M) -
            4 / (M - 41 / 50) *
              (1 + (6381 / 5000 : Real) / (M - 41 / 50))) :=
        coefficientScaled
      _ = 9 * (P : Real) / M * (1 + 1 / M) -
          4 * (P : Real) / (M - 41 / 50) *
            (1 + (6381 / 5000 : Real) / (M - 41 / 50)) := by ring
  have start :
      5 * (P : Real) / tailGapBound q + 1 <
        5 * (P : Real) / M + (P : Real) * (3 / (5 * M ^ 2)) := by
    linarith
  exact start.trans (core.trans
    (sub_lt_sub_left upperCompare (9 * (P : Real) / M * (1 + 1 / M))))

end

end PrimeFactorUnimodality
