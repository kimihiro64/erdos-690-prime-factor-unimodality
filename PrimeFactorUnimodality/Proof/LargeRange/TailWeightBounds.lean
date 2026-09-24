import PrimeFactorUnimodality.Helpers.Analytic.ReciprocalPrimeBounds
import PrimeFactorUnimodality.Proof.LargeRange.TailPrefixBounds

set_option autoImplicit false

/-! # Reciprocal-prime weight numerics for the uniform tail -/

namespace PrimeFactorUnimodality

noncomputable section

private theorem tail_indexFactor_lt {r : Nat} (hr : 38000 ≤ r) :
    ((Nat.log 2 r : Nat) : Real) <
      (29 / 20 : Real) * Real.log r := by
  have rne : r ≠ 0 := by omega
  have powerLe : 2 ^ Nat.log 2 r ≤ r := Nat.pow_log_le_self 2 rne
  have castPower : (2 : Real) ^ Nat.log 2 r ≤ r := by exact_mod_cast powerLe
  have logged := Real.log_le_log (by positivity) castPower
  rw [Real.log_pow] at logged
  have logTwoLower : (69 / 100 : Real) < Real.log 2 := by
    exact (by norm_num : (69 / 100 : Real) < 0.6931471803).trans
      Real.log_two_gt_d9
  have logRLower := log_nat_gt_1054_div_100 hr
  push_cast
  nlinarith

private theorem log_fixed_index_product_lt :
    Real.log ((15283 : Real) / 1000) < (273 : Real) / 100 := by
  have powerLt : ((15283 : Real) / 1000) ^ 6 < 2 ^ 3 * 3 ^ 13 := by norm_num
  have logged := Real.log_lt_log (by positivity) powerLt
  rw [Real.log_pow, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Real.log_pow] at logged
  norm_num at logged ⊢
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9]

private theorem tail_log_indexFactor_lt {r : Nat} (hr : 38000 ≤ r) :
    Real.log ((Nat.log 2 r : Nat) : Real) <
      (13 / 50 : Real) * Real.log r := by
  let v := Real.log r
  let L : Real := ((Nat.log 2 r : Nat) : Real)
  have vLower : (527 / 50 : Real) < v := by
    have h := log_nat_gt_1054_div_100 hr
    norm_num at h ⊢
    exact h
  have Lpos : 0 < L := by
    dsimp only [L]
    exact_mod_cast (Nat.log_pos (by omega) (show 2 ≤ r by omega))
  have comparison : L < (29 / 20 : Real) * v := by
    simpa only [L, v] using tail_indexFactor_lt hr
  have productPos : 0 < (29 / 20 : Real) * v := by positivity
  have logComparison := Real.log_lt_log Lpos comparison
  have ratioPos : 0 < v / (527 / 50 : Real) := by positivity
  have decomposition :
      Real.log ((29 / 20 : Real) * v) =
        Real.log ((15283 : Real) / 1000) +
          Real.log (v / (527 / 50 : Real)) := by
    have algebra : (29 / 20 : Real) * v =
        (15283 / 1000 : Real) * (v / (527 / 50 : Real)) := by
      field_simp
      ring
    rw [algebra, Real.log_mul (by norm_num) ratioPos.ne']
  have ratioLog := Real.log_le_sub_one_of_pos ratioPos
  rw [decomposition] at logComparison
  have constantLog := log_fixed_index_product_lt
  dsimp only [L, v] at logComparison ⊢
  nlinarith

theorem tail_log_primeUpper_lt {r : Nat} (hr : 38000 ≤ r) :
    Real.log (tailPrimeUpper r) < (63 / 50 : Real) * Real.log r := by
  let L : Nat := Nat.log 2 r
  have rpos : 0 < r := by omega
  have Lpos : 0 < L := by
    dsimp only [L]
    exact Nat.log_pos (by omega) (by omega)
  have decomposition : Real.log (tailPrimeUpper r) =
      Real.log r + Real.log L := by
    simp only [tailPrimeUpper, L]
    push_cast
    rw [Real.log_mul (by exact_mod_cast rpos.ne') (by exact_mod_cast Lpos.ne')]
  rw [decomposition]
  have factorLog := tail_log_indexFactor_lt hr
  dsimp only [L] at factorLog ⊢
  linarith

private theorem log_primorial_ratio_constant :
    (-2076 / 5000 : Real) < Real.log ((208 : Real) / 315) := by
  have inversePower : ((315 : Real) / 208) ^ 26 < 2 ^ 3 * 3 ^ 5 * 5 ^ 2 := by norm_num
  have logged := Real.log_lt_log (by positivity) inversePower
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_pow, Real.log_pow] at logged
  have inverseLog : Real.log ((315 : Real) / 208) =
      -Real.log ((208 : Real) / 315) := by
    rw [show (315 : Real) / 208 = ((208 : Real) / 315)⁻¹ by norm_num,
      Real.log_inv]
  rw [inverseLog] at logged
  norm_num at logged
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9]

private theorem log_527_div_50_lt :
    Real.log ((527 : Real) / 50) < (23559 : Real) / 10000 := by
  have powerLt : ((527 : Real) / 50) ^ 8 < 2 ^ 5 * 3 ^ 14 := by norm_num
  have logged := Real.log_lt_log (by positivity) powerLt
  rw [Real.log_pow, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Real.log_pow] at logged
  norm_num at logged ⊢
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9]

private theorem tail_log_expression_lower {r : Nat} (hr : 38000 ≤ r) :
    (2519 / 4910 : Real) * Real.log r + 1 / 250 <
      Real.log r - 2 * Real.log (Real.log r) - 5 / 12 := by
  let v := Real.log r
  let v₀ : Real := 527 / 50
  have vLower : v₀ < v := by
    have h := log_nat_gt_1054_div_100 hr
    norm_num [v, v₀] at h ⊢
    exact h
  have v₀pos : 0 < v₀ := by norm_num [v₀]
  have vpos : 0 < v := v₀pos.trans vLower
  have ratioPos : 0 < v / v₀ := by positivity
  have logDecomposition : Real.log v = Real.log v₀ + Real.log (v / v₀) := by
    rw [← Real.log_mul v₀pos.ne' ratioPos.ne']
    congr 2
    field_simp
  have ratioLog := Real.log_le_sub_one_of_pos ratioPos
  have baseLog : Real.log v₀ < (23559 : Real) / 10000 := by
    simpa only [v₀] using log_527_div_50_lt
  have ratioLog' : Real.log (v / (527 / 50 : Real)) ≤
      v / (527 / 50 : Real) - 1 := by
    simpa only [v₀] using ratioLog
  have logVUpper : Real.log v < (23559 : Real) / 10000 +
      (v / (527 / 50 : Real) - 1) := by
    rw [logDecomposition]
    dsimp only [v₀] at baseLog ⊢
    linarith
  dsimp only [v₀] at vLower
  dsimp only [v] at logVUpper ⊢
  nlinarith

private theorem log_10372_gt_nine : (9 : Real) < Real.log 10372 := by
  have powerLt : (2 : Real) ^ 2 * 3 ^ 7 < 10372 := by norm_num
  have logged := Real.log_lt_log (by positivity) powerLt
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow] at logged
  rw [Real.log_pow] at logged
  norm_num at logged ⊢
  nlinarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

/-- The logarithmic part of the descent shell, before inserting either the
sharp Dusart reciprocal error or the coarser proved Mertens error.  Keeping
this estimate separate lets both analytic providers share the same prime and
primorial argument. -/
theorem tail_descent_loglog_shell_lower_sharp
    (thetaBounds : HasTailThetaBounds)
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    {r q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q) :
    Real.log r - 2 * Real.log (Real.log r) - 2076 / 5000 <
      Real.log (Real.log ((primorial q : Nat) : Real)) -
        Real.log (Real.log ((primeAt (r - 1) - 1 : Nat) : Real)) := by
  let P : Nat := primorial q
  let U : Nat := tailPrimeUpper r
  let X : Nat := primeAt (r - 1) - 1
  have prefixLeU : X ≤ U := by
    dsimp only [X, U]
    exact (Nat.sub_le _ _).trans
      ((primeAt_strictMono.monotone (Nat.sub_le r 1)).trans
        (tail_primeAt_le_upper primeCountingBounds hr))
  have logRPos : 0 < Real.log r :=
    Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have logP : (104 / 125 : Real) * r / Real.log r < Real.log P := by
    have h := tail_log_primorial_lower_sharp thetaBounds hr scaleLtQ
    have ratioPos : (0 : Real) < (r : Real) / Real.log r := by positivity
    have coefficient : (104 / 125 : Real) <
        (106 / 125 : Real) * (491 / 500 : Real) := by norm_num
    calc
      (104 / 125 : Real) * r / Real.log r <
          (106 / 125 : Real) * ((491 / 500 : Real) * r / Real.log r) := by
        convert mul_lt_mul_of_pos_right coefficient ratioPos using 1 <;> ring
      _ < Real.log (primorial q) := h
  have logU := tail_log_primeUpper_lt hr
  have logXLe : Real.log X ≤ Real.log U :=
    Real.log_le_log (by exact_mod_cast (show 0 < X by
      have threshold : 10372 ≤ X := by
        simpa only [X, show r + 1 - 2 = r - 1 by omega] using
          tail_prefixThreshold (k := r + 1) (by omega : 38000 ≤ r + 1)
      omega)) (by exact_mod_cast prefixLeU)
  have logPPos : 0 < Real.log P := by
    have : (0 : Real) < (104 / 125 : Real) * r / Real.log r := by positivity
    linarith
  have logUPos : 0 < Real.log U := by
    have : 1 < U := by
      dsimp only [U, tailPrimeUpper]
      have : 1 ≤ Nat.log 2 r := Nat.log_pos (by omega) (by omega)
      nlinarith
    exact Real.log_pos (by exact_mod_cast this)
  have logXPos : 0 < Real.log X := by
    apply Real.log_pos
    exact_mod_cast (show 1 < X by
      have threshold : 10372 ≤ X := by
        simpa only [X, show r + 1 - 2 = r - 1 by omega] using
          tail_prefixThreshold (k := r + 1) (by omega : 38000 ≤ r + 1)
      omega)
  have lowerLogLog :
      Real.log ((104 / 125 : Real) * r / Real.log r) <
        Real.log (Real.log P) := Real.log_lt_log (by positivity) logP
  have upperLogLog : Real.log (Real.log X) <
      Real.log ((63 / 50 : Real) * Real.log r) :=
    (Real.log_le_log logXPos logXLe).trans_lt
      (Real.log_lt_log logUPos logU)
  have logAlgebra :
      Real.log ((104 / 125 : Real) * r / Real.log r) -
          Real.log ((63 / 50 : Real) * Real.log r) =
        Real.log r - 2 * Real.log (Real.log r) +
          Real.log ((208 : Real) / 315) := by
    rw [Real.log_div (by positivity) logRPos.ne',
      Real.log_mul (by norm_num) (by positivity),
      Real.log_mul (by norm_num) logRPos.ne']
    have constantIdentity :
        Real.log (104 / 125 : Real) - Real.log (63 / 50 : Real) =
          Real.log ((208 : Real) / 315) := by
      calc
        Real.log (104 / 125 : Real) - Real.log (63 / 50 : Real) =
            Real.log ((104 / 125 : Real) / (63 / 50 : Real)) :=
          (Real.log_div (by norm_num) (by norm_num)).symm
        _ = Real.log ((208 : Real) / 315) := by norm_num
    linarith [constantIdentity]
  have constantLower := log_primorial_ratio_constant
  dsimp only [P, X] at lowerLogLog upperLogLog ⊢
  nlinarith

theorem tail_descent_loglog_shell_lower
    (thetaBounds : HasTailThetaBounds)
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    {r q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q) :
    Real.log r - 2 * Real.log (Real.log r) - 5 / 12 <
      Real.log (Real.log ((primorial q : Nat) : Real)) -
        Real.log (Real.log ((primeAt (r - 1) - 1 : Nat) : Real)) := by
  have h := tail_descent_loglog_shell_lower_sharp thetaBounds primeCountingBounds hr scaleLtQ
  linarith

theorem dusartReciprocalError_lt_one_div_500 {x : Nat}
    (hx : 10372 ≤ x) :
    dusartReciprocalError x < (1 : Real) / 500 := by
  have logLower : (9 : Real) < Real.log x :=
    log_10372_gt_nine.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast hx))
  have logPos : 0 < Real.log x := by linarith
  have squarePos : 0 < 10 * (Real.log x) ^ 2 := by positivity
  have cubePos : 0 < 15 * (Real.log x) ^ 3 := by positivity
  have first : 1 / (10 * (Real.log x) ^ 2) < (1 : Real) / 810 := by
    rw [div_lt_iff₀ squarePos]
    nlinarith [sq_nonneg (Real.log x - 9)]
  have second : 4 / (15 * (Real.log x) ^ 3) < (1 : Real) / 2700 := by
    rw [div_lt_iff₀ cubePos]
    have cubeLower : (729 : Real) < (Real.log x) ^ 3 := by nlinarith
    nlinarith
  unfold dusartReciprocalError
  nlinarith

/-- Uniform lower bound for the logarithmic shell appearing in the descent
weight. -/
theorem tail_descent_bracket_lower
    (thetaBounds : HasTailThetaBounds)
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    {r q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q) :
    (2519 / 4910 : Real) * Real.log r <
      Real.log (Real.log ((primorial q : Nat) : Real)) -
        Real.log (Real.log ((primeAt (r - 1) - 1 : Nat) : Real)) -
        dusartReciprocalError (((primorial q : Nat) : Real)) -
        dusartReciprocalError (((primeAt (r - 1) - 1 : Nat) : Real)) := by
  let P : Nat := primorial q
  let U : Nat := tailPrimeUpper r
  let X : Nat := primeAt (r - 1) - 1
  have prefixThreshold : 10372 ≤ X := by
    dsimp only [X]
    exact tail_prefixThreshold (k := r + 1) (by omega)
  have prefixLeU : X ≤ U := by
    dsimp only [X, U]
    exact (Nat.sub_le _ _).trans ((primeAt_strictMono.monotone (Nat.sub_le r 1)).trans
      (tail_primeAt_le_upper primeCountingBounds hr))
  have logRPos : 0 < Real.log r :=
    Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have logP : (104 / 125 : Real) * r / Real.log r < Real.log P := by
    have := tail_log_primorial_lower_sharp thetaBounds hr scaleLtQ
    dsimp only [P]
    have ratioPos : (0 : Real) < (r : Real) / Real.log r := by positivity
    have coefficient : (104 / 125 : Real) <
        (106 / 125 : Real) * (491 / 500 : Real) := by norm_num
    calc
      (104 / 125 : Real) * r / Real.log r <
          (106 / 125 : Real) * ((491 / 500 : Real) * r / Real.log r) := by
        convert mul_lt_mul_of_pos_right coefficient ratioPos using 1 <;> ring
      _ < Real.log (primorial q) := this
  have logU := tail_log_primeUpper_lt hr
  have logXLe : Real.log X ≤ Real.log U :=
    Real.log_le_log (by exact_mod_cast (show 0 < X by omega)) (by exact_mod_cast prefixLeU)
  have logPPos : 0 < Real.log P := by
    have : (0 : Real) < (104 / 125 : Real) * r / Real.log r := by positivity
    linarith
  have logUPos : 0 < Real.log U := by
    have : 1 < U := by
      dsimp only [U, tailPrimeUpper]
      have : 1 ≤ Nat.log 2 r := Nat.log_pos (by omega) (by omega)
      nlinarith
    exact Real.log_pos (by exact_mod_cast this)
  have logXPos : 0 < Real.log X :=
    Real.log_pos (by
      have : 1 < X := by omega
      exact_mod_cast this)
  have lowerLogLog :
      Real.log ((104 / 125 : Real) * r / Real.log r) <
        Real.log (Real.log P) := Real.log_lt_log (by positivity) logP
  have upperLogLog : Real.log (Real.log X) <
      Real.log ((63 / 50 : Real) * Real.log r) := by
    exact (Real.log_le_log logXPos logXLe).trans_lt
      (Real.log_lt_log logUPos logU)
  have logAlgebra :
      Real.log ((104 / 125 : Real) * r / Real.log r) -
          Real.log ((63 / 50 : Real) * Real.log r) =
        Real.log r - 2 * Real.log (Real.log r) +
          Real.log ((208 : Real) / 315) := by
    rw [Real.log_div (by positivity) logRPos.ne',
      Real.log_mul (by norm_num) (by positivity),
      Real.log_mul (by norm_num) logRPos.ne']
    have constantIdentity :
        Real.log (104 / 125 : Real) - Real.log (63 / 50 : Real) =
        Real.log ((208 : Real) / 315) := by
      calc
        Real.log (104 / 125 : Real) - Real.log (63 / 50 : Real) =
            Real.log ((104 / 125 : Real) / (63 / 50 : Real)) :=
          (Real.log_div (by norm_num) (by norm_num)).symm
        _ = Real.log ((208 : Real) / 315) := by
          have : ((104 / 125 : Real) / (63 / 50 : Real)) = 208 / 315 := by
            norm_num
          rw [this]
    linarith [constantIdentity]
  have mainExpression := tail_log_expression_lower hr
  have constantLower := log_primorial_ratio_constant
  have shellNoError : (2519 / 4910 : Real) * Real.log r + 1 / 250 <
      Real.log (Real.log P) - Real.log (Real.log X) := by
    nlinarith
  have pThreshold : 10372 ≤ P := by
    have qLarge := tail_selected_prime_ge_3501 hr scaleLtQ
    have base : primorial 13 ≤ P := by dsimp only [P]; exact primorial_mono (by omega)
    have value : primorial 13 = 30030 := by decide
    rw [value] at base
    omega
  have errorP := dusartReciprocalError_lt_one_div_500 pThreshold
  have errorX := dusartReciprocalError_lt_one_div_500 prefixThreshold
  dsimp only [P, X] at shellNoError errorP errorX ⊢
  nlinarith

theorem tail_descent_numeric
    (thetaBounds : HasTailThetaBounds)
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    {r qPrev q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q)
    (scalePrev : (491 / 500 : Real) * r / Real.log r <
      (2519 / 2500 : Real) * qPrev) :
    (r : Real) < ((2 * qPrev + 1 : Nat) : Real) *
      (Real.log (Real.log ((primorial q : Nat) : Real)) -
        Real.log (Real.log ((primeAt (r - 1) - 1 : Nat) : Real)) -
        dusartReciprocalError (((primorial q : Nat) : Real)) -
        dusartReciprocalError (((primeAt (r - 1) - 1 : Nat) : Real))) := by
  let B : Real :=
    Real.log (Real.log ((primorial q : Nat) : Real)) -
      Real.log (Real.log ((primeAt (r - 1) - 1 : Nat) : Real)) -
      dusartReciprocalError (((primorial q : Nat) : Real)) -
      dusartReciprocalError (((primeAt (r - 1) - 1 : Nat) : Real))
  have bracket : (2519 / 4910 : Real) * Real.log r < B := by
    simpa only [B] using
      tail_descent_bracket_lower thetaBounds primeCountingBounds hr scaleLtQ
  have logRPos : 0 < Real.log r :=
    Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have scaleCross : (491 / 500 : Real) * r <
      (2519 / 2500 : Real) * qPrev * Real.log r := by
    exact (div_lt_iff₀ logRPos).mp (by
      convert scalePrev using 1 <;> ring)
  have core : (r : Real) <
      (2 * qPrev : Nat) * ((2519 / 4910 : Real) * Real.log r) := by
    push_cast
    nlinarith
  have multiplierPos : (0 : Real) < 2 * qPrev := by
    have : (0 : Real) < qPrev := by
      have scalePos : (0 : Real) < (491 / 500 : Real) * r / Real.log r := by
        positivity
      nlinarith
    positivity
  have raised := mul_lt_mul_of_pos_left bracket multiplierPos
  dsimp only [B] at raised ⊢
  push_cast at raised ⊢
  have bracketPos : (0 : Real) <
      Real.log (Real.log ((primorial q : Nat) : Real)) -
        Real.log (Real.log ((primeAt (r - 1) - 1 : Nat) : Real)) -
        dusartReciprocalError (((primorial q : Nat) : Real)) -
        dusartReciprocalError (((primeAt (r - 1) - 1 : Nat) : Real)) := by
    have coefficientPos : (0 : Real) < 2519 / 4910 := by norm_num
    nlinarith
  nlinarith

end

end PrimeFactorUnimodality
