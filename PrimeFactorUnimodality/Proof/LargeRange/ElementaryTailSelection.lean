import PrimeFactorUnimodality.Helpers.Analytic.ElementaryPrimeIntervals

set_option autoImplicit false

/-!
# Elementary prime selection for the uniform tail

This replaces the unproved Dusart short-interval input in the prime-selection
step with the kernel-checked elementary Chebyshev bounds.  The scale is chosen
in natural arithmetic so no floor operation on reals is needed.
-/

namespace PrimeFactorUnimodality

/-- An elementary approximation to `r / log₂ r`. -/
def elementaryTailScale (r : Nat) : Nat := r / Nat.log 2 r

theorem elementaryTailScale_cast_le_div (r : Nat) :
    (elementaryTailScale r : Real) ≤ r / (Nat.log 2 r : Nat) := by
  exact Nat.cast_div_le

theorem real_div_sub_one_lt_elementaryTailScale {r : Nat} (hr : 2 ≤ r) :
    (r : Real) / (Nat.log 2 r : Nat) - 1 < elementaryTailScale r := by
  let L := Nat.log 2 r
  have LPosNat : 0 < L := by
    dsimp only [L]
    exact Nat.log_pos (by omega) hr
  have LPos : (0 : Real) < L := by exact_mod_cast LPosNat
  have remainderLt : r % L < L := Nat.mod_lt r LPosNat
  have remainderRatio : ((r % L : Nat) : Real) / L < 1 := by
    rw [div_lt_one LPos]
    exact_mod_cast remainderLt
  have decomposition : (r : Real) / L =
      (r / L : Nat) + ((r % L : Nat) : Real) / L := by
    have division := Nat.mod_add_div r L
    have divisionReal : ((r % L : Nat) : Real) + L * (r / L : Nat) = r := by
      exact_mod_cast division
    calc
      (r : Real) / L =
          (((r % L : Nat) : Real) + L * (r / L : Nat)) / L :=
        congrArg (fun x : Real => x / L) divisionReal.symm
      _ = (r / L : Nat) + ((r % L : Nat) : Real) / L := by
        field_simp
        ring
  dsimp only [elementaryTailScale, L] at decomposition ⊢
  rw [decomposition]
  linarith

private theorem log_lt_succ_logTwo_mul {r : Nat} (hr : 1 ≤ r) :
    Real.log r < ((Nat.log 2 r + 1 : Nat) : Real) * Real.log 2 := by
  have rLt : r < 2 ^ (Nat.log 2 r + 1) :=
    (Nat.log_lt_iff_lt_pow (by omega) (by omega)).mp (by omega)
  have castLt : (r : Real) < (2 : Real) ^ (Nat.log 2 r + 1) := by
    exact_mod_cast rLt
  have logged := Real.log_lt_log (by exact_mod_cast (show 0 < r by omega)) castLt
  rw [Real.log_pow] at logged
  simpa only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using logged

theorem elementaryTailScale_real_lower {r : Nat} (hr : 8600001 ≤ r) :
    (69 / 100 : Real) * r / Real.log r - 1 < elementaryTailScale r := by
  let L := Nat.log 2 r
  have LPosNat : 0 < L := by
    dsimp only [L]
    exact Nat.log_pos (by omega) (by omega)
  have LPos : (0 : Real) < L := by exact_mod_cast LPosNat
  have rPos : (0 : Real) < r := by positivity
  have logRPos : 0 < Real.log r := Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have powerLe : 2 ^ L ≤ r := by
    simpa only [L] using Nat.pow_log_le_self 2 (show r ≠ 0 by omega)
  have castPower : (2 : Real) ^ L ≤ r := by exact_mod_cast powerLe
  have logged := Real.log_le_log (by positivity) castPower
  rw [Real.log_pow] at logged
  have logTwoLower : (69 / 100 : Real) < Real.log 2 :=
    (by norm_num : (69 / 100 : Real) < 0.6931471803).trans Real.log_two_gt_d9
  have denominatorComparison : (69 / 100 : Real) * L < Real.log r := by
    nlinarith
  have ratioComparison :
      (69 / 100 : Real) * r / Real.log r < (r : Real) / L := by
    rw [div_lt_div_iff₀ logRPos LPos]
    nlinarith
  have floorLower := real_div_sub_one_lt_elementaryTailScale
    (r := r) (show 2 ≤ r by omega)
  change (r : Real) / L - 1 < elementaryTailScale r at floorLower
  exact (sub_lt_sub_right ratioComparison 1).trans floorLower

theorem elementaryTailScale_real_upper {r : Nat} (hr : 8600001 ≤ r) :
    (elementaryTailScale r : Real) <
      (84 / 115 : Real) * r / Real.log r := by
  let L := Nat.log 2 r
  have logLarge : 23 ≤ L := by
    dsimp only [L]
    apply Nat.le_log_of_pow_le (by omega)
    norm_num
    omega
  have LPos : (0 : Real) < L := by exact_mod_cast (show 0 < L by omega)
  have rPos : (0 : Real) < r := by positivity
  have logRPos : 0 < Real.log r := Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have logBound := log_lt_succ_logTwo_mul (show 1 ≤ r by omega)
  have logTwoUpper : Real.log 2 < (7 / 10 : Real) :=
    Real.log_two_lt_d9.trans (by norm_num)
  have logLargeReal : (23 : Real) ≤ L := by exact_mod_cast logLarge
  have successorBound : ((L + 1 : Nat) : Real) ≤ (24 / 23 : Real) * L := by
    push_cast
    nlinarith
  have logVsL : Real.log r < (84 / 115 : Real) * L := by
    change Real.log r < ((L + 1 : Nat) : Real) * Real.log 2 at logBound
    push_cast at logBound
    have scaledLog := mul_lt_mul_of_pos_left logTwoUpper
      (show (0 : Real) < L + 1 by positivity)
    nlinarith
  have ratioComparison : (r : Real) / L <
      (84 / 115 : Real) * r / Real.log r := by
    rw [div_lt_div_iff₀ LPos logRPos]
    nlinarith
  have scaleLe : (elementaryTailScale r : Real) ≤ (r : Real) / L := by
    simpa only [L] using elementaryTailScale_cast_le_div r
  exact scaleLe.trans_lt ratioComparison

private theorem real_div_lt_nat_div_add_one (m : Nat) {d : Nat} (hd : 0 < d) :
    (m : Real) / d < (m / d : Nat) + 1 := by
  have dPos : (0 : Real) < d := by exact_mod_cast hd
  have remainderLt : m % d < d := Nat.mod_lt m hd
  have remainderRatio : ((m % d : Nat) : Real) / d < 1 := by
    rw [div_lt_one dPos]
    exact_mod_cast remainderLt
  have division := Nat.mod_add_div m d
  have divisionReal : ((m % d : Nat) : Real) + d * (m / d : Nat) = m := by
    exact_mod_cast division
  have decomposition : (m : Real) / d =
      (m / d : Nat) + ((m % d : Nat) : Real) / d := by
    calc
      (m : Real) / d =
          (((m % d : Nat) : Real) + d * (m / d : Nat)) / d :=
        congrArg (fun x : Real => x / d) divisionReal.symm
      _ = (m / d : Nat) + ((m % d : Nat) : Real) / d := by
        field_simp
        ring
  rw [decomposition]
  linarith

private theorem threeHundredTwentyFiveThousand_mul_le_two_pow {L : Nat}
    (hL : 23 ≤ L) :
    325000 * L ≤ 2 ^ L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have step : 325000 * (n + 1) ≤ 2 * (325000 * n) := by
        nlinarith
      calc
        325000 * (n + 1) ≤ 2 * (325000 * n) := step
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by rw [pow_succ]; omega

/-- The elementary tail scale lies in the domain of the `13/10` prime
interval theorem throughout the intended post-record range. -/
theorem elementaryTailScale_ge_threeHundredTwentyFiveThousand {r : Nat}
    (hr : 8600001 ≤ r) :
    325000 ≤ elementaryTailScale r := by
  let L := Nat.log 2 r
  have logLarge : 23 ≤ L := by
    dsimp only [L]
    apply Nat.le_log_of_pow_le (by omega)
    norm_num
    omega
  have logPos : 0 < L := by omega
  apply (Nat.le_div_iff_mul_le logPos).2
  exact (threeHundredTwentyFiveThousand_mul_le_two_pow logLarge).trans
    (by
      simpa only [L] using Nat.pow_log_le_self 2 (show r ≠ 0 by omega))

/-- Consecutive primes at the elementary tail scale.  This is the direct
replacement for the selection consequence of `HasDusartShortIntervalPrime`;
all remaining tail work is now numerical optimization with these wider
ratios. -/
theorem exists_elementary_tail_consecutive_primes {r : Nat}
    (hr : 8600001 ≤ r) :
    ∃ qPrev q : Nat,
      ConsecutivePrimes qPrev q ∧
      10 * elementaryTailScale r / 13 < qPrev ∧
      elementaryTailScale r < q ∧
      q ≤ 13 * elementaryTailScale r / 10 :=
  exists_consecutive_primes_near_elementary (elementaryTailScale r)
    (elementaryTailScale_ge_threeHundredTwentyFiveThousand hr)

/-- The coarse elementary selector in the real units used by the analytic
tail inequalities. -/
theorem exists_elementary_tail_consecutive_primes_real {r : Nat}
    (hr : 8600001 ≤ r) :
    ∃ qPrev q : Nat,
      ConsecutivePrimes qPrev q ∧
      (69 / 130 : Real) * r / Real.log r - 10 / 13 < qPrev ∧
      elementaryTailScale r < q ∧
      (q : Real) < (546 / 575 : Real) * r / Real.log r := by
  obtain ⟨qPrev, q, consecutive, prevLower, scaleLtQ, qUpper⟩ :=
    exists_elementary_tail_consecutive_primes hr
  have floorApprox :
      ((10 * elementaryTailScale r : Nat) : Real) / 13 <
        (10 * elementaryTailScale r / 13 : Nat) + 1 :=
    real_div_lt_nat_div_add_one (10 * elementaryTailScale r) (by norm_num)
  have floorStep : 10 * elementaryTailScale r / 13 + 1 ≤ qPrev := by omega
  have prevReal : ((10 * elementaryTailScale r : Nat) : Real) / 13 < qPrev :=
    floorApprox.trans_le (by exact_mod_cast floorStep)
  have scaleLower := elementaryTailScale_real_lower hr
  have selectedUpper : (q : Real) ≤
      ((13 * elementaryTailScale r / 10 : Nat) : Real) := by exact_mod_cast qUpper
  have floorUpper : ((13 * elementaryTailScale r / 10 : Nat) : Real) ≤
      ((13 * elementaryTailScale r : Nat) : Real) / 10 := Nat.cast_div_le
  have scaleUpper := elementaryTailScale_real_upper hr
  refine ⟨qPrev, q, consecutive, ?_, scaleLtQ, ?_⟩
  · push_cast at prevReal
    ring_nf at scaleLower prevReal ⊢
    nlinarith
  · push_cast at floorUpper
    calc
      (q : Real) ≤ ((13 * elementaryTailScale r / 10 : Nat) : Real) := selectedUpper
      _ ≤ (13 * (elementaryTailScale r : Real)) / 10 := floorUpper
      _ < (546 / 575 : Real) * r / Real.log r := by
        ring_nf at scaleUpper ⊢
        nlinarith

private theorem oneMillionTwoHundredFiftyThousand_mul_le_two_pow {L : Nat}
    (hL : 25 ≤ L) :
    1250000 * L ≤ 2 ^ L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have step : 1250000 * (n + 1) ≤ 2 * (1250000 * n) := by
        nlinarith
      calc
        1250000 * (n + 1) ≤ 2 * (1250000 * n) := step
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by rw [pow_succ]; omega

theorem elementaryTailScale_ge_oneMillionTwoHundredFiftyThousand {r : Nat}
    (hr : 33554432 ≤ r) :
    1250000 ≤ elementaryTailScale r := by
  let L := Nat.log 2 r
  have logLarge : 25 ≤ L := by
    dsimp only [L]
    apply Nat.le_log_of_pow_le (by omega)
    norm_num
    exact hr
  have logPos : 0 < L := by omega
  apply (Nat.le_div_iff_mul_le logPos).2
  exact (oneMillionTwoHundredFiftyThousand_mul_le_two_pow logLarge).trans
    (by
      simpa only [L] using Nat.pow_log_le_self 2 (show r ≠ 0 by omega))

/-- Beyond `2^25`, the sharper elementary theta bounds improve both sides of
the selected consecutive pair. -/
theorem exists_elementary_tail_consecutive_primes_sharp {r : Nat}
    (hr : 33554432 ≤ r) :
    ∃ qPrev q : Nat,
      ConsecutivePrimes qPrev q ∧
      4 * elementaryTailScale r / 5 < qPrev ∧
      elementaryTailScale r < q ∧
      q ≤ 5 * elementaryTailScale r / 4 :=
  exists_consecutive_primes_near_elementary_sharp (elementaryTailScale r)
    (elementaryTailScale_ge_oneMillionTwoHundredFiftyThousand hr)

theorem exists_elementary_tail_consecutive_primes_sharp_real {r : Nat}
    (hr : 33554432 ≤ r) :
    ∃ qPrev q : Nat,
      ConsecutivePrimes qPrev q ∧
      (69 / 125 : Real) * r / Real.log r - 4 / 5 < qPrev ∧
      elementaryTailScale r < q ∧
      (q : Real) < (21 / 23 : Real) * r / Real.log r := by
  obtain ⟨qPrev, q, consecutive, prevLower, scaleLtQ, qUpper⟩ :=
    exists_elementary_tail_consecutive_primes_sharp hr
  have floorApprox :
      ((4 * elementaryTailScale r : Nat) : Real) / 5 <
        (4 * elementaryTailScale r / 5 : Nat) + 1 :=
    real_div_lt_nat_div_add_one (4 * elementaryTailScale r) (by norm_num)
  have floorStep : 4 * elementaryTailScale r / 5 + 1 ≤ qPrev := by omega
  have prevReal : ((4 * elementaryTailScale r : Nat) : Real) / 5 < qPrev :=
    floorApprox.trans_le (by exact_mod_cast floorStep)
  have scaleLower := elementaryTailScale_real_lower (r := r) (by omega)
  have selectedUpper : (q : Real) ≤
      ((5 * elementaryTailScale r / 4 : Nat) : Real) := by exact_mod_cast qUpper
  have floorUpper : ((5 * elementaryTailScale r / 4 : Nat) : Real) ≤
      ((5 * elementaryTailScale r : Nat) : Real) / 4 := Nat.cast_div_le
  have scaleUpper := elementaryTailScale_real_upper (r := r) (by omega)
  refine ⟨qPrev, q, consecutive, ?_, scaleLtQ, ?_⟩
  · push_cast at prevReal
    ring_nf at scaleLower prevReal ⊢
    nlinarith
  · push_cast at floorUpper
    calc
      (q : Real) ≤ ((5 * elementaryTailScale r / 4 : Nat) : Real) := selectedUpper
      _ ≤ (5 * (elementaryTailScale r : Real)) / 4 := floorUpper
      _ < (21 / 23 : Real) * r / Real.log r := by
        ring_nf at scaleUpper ⊢
        nlinarith

end PrimeFactorUnimodality
