import PrimeFactorUnimodality.Helpers.Analytic.DusartProofPart01

/-! # Dusart Lemma 3.3 finite rows, part 2

This module continues the compact finite interval assemblers used in the
direct proof of the published Lemma 3.3 bounds.
-/

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/- The finite boundary in Dusart's Lemma 3.3 is exactly 10^33. -/

def dusartLemma33FiniteRow_twohundredeightynine_threehundredfortytwo :
    DusartLemma33FiniteRow := by
  have htheta_seventeen := Chebyshev.theta_eq_sum_primesLE_log 17
  have hp17 : Nat.primesLE 17 = {2, 3, 5, 7, 11, 13, 17} := by decide
  rw [hp17] at htheta_seventeen
  norm_num [Nat.log, Nat.log.go] at htheta_seventeen
  have hlog10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [show (10 : Real) = 2 * 5 by norm_num, Real.log_mul]
    · norm_num
    all_goals positivity
  have hlog10_le11 : Real.log 10 ≤ Real.log 11 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hlog10_le13 : Real.log 10 ≤ Real.log 13 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hlog10_le17 : Real.log 10 ≤ Real.log 17 :=
    Real.log_le_log (by norm_num) (by norm_num)
  apply dusartLemma33FiniteRow_of_endpoint_bounds 289 342 17 23 12 (33 / 5)
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_342_lt_twenty_three
  · nlinarith [htheta_seventeen, hlog10, hlog10_le11, hlog10_le13,
      hlog10_le17, Real.log_two_gt_d9, Real.log_three_gt_d9,
      Real.log_five_gt_d9, LogTables.log_7_gt]
  · intro x hx hleft
    have hbase : ((33 / 5 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (33 / 5 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (33 / 5 : Real) = ((33 / 5 : Real) ^ (3 : Nat)) ^
          (1 / 3 : Real) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

theorem psi_sub_theta_nat_360_lt_twentyfour_point_two :
    Chebyshev.psi (360 : Real) - Chebyshev.theta 360 < (121 : Real) / 5 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 360
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 360
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 361,
      ↑(Nat.log p 360) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 361, Real.log ↑p < (121 : Real) / 5
  have hp : Nat.primesBelow 361 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
        127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
        191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
        257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
        331, 337, 347, 349, 353, 359} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt,
    ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
    ElementaryLogBounds.log_17_lt]

def dusartLemma33FiniteRow_threehundredfortythree_threehundredsixty :
    DusartLemma33FiniteRow := by
  have htheta_seventeen := Chebyshev.theta_eq_sum_primesLE_log 17
  have hp17 : Nat.primesLE 17 = {2, 3, 5, 7, 11, 13, 17} := by decide
  rw [hp17] at htheta_seventeen
  norm_num [Nat.log, Nat.log.go] at htheta_seventeen
  have hlog10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [show (10 : Real) = 2 * 5 by norm_num, Real.log_mul]
    · norm_num
    all_goals positivity
  have hlog10_le11 : Real.log 10 ≤ Real.log 11 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hlog10_le13 : Real.log 10 ≤ Real.log 13 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hlog10_le17 : Real.log 10 ≤ Real.log 17 :=
    Real.log_le_log (by norm_num) (by norm_num)
  apply dusartLemma33FiniteRow_of_endpoint_bounds 343 360 18
    ((121 : Real) / 5) (49 / 4) 7
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_360_lt_twentyfour_point_two
  · nlinarith [htheta_seventeen, hlog10, hlog10_le11, hlog10_le13,
      hlog10_le17, Real.log_two_gt_d9, Real.log_three_gt_d9,
      Real.log_five_gt_d9, LogTables.log_7_gt]
  · intro x hx hleft
    have hpow := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 343)
      hleft (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    norm_num at hpow ⊢
    exact hpow
  · norm_num

theorem dusartLemma33FiniteRowsCover_threesixty :
    DusartLemma33FiniteRowsCover
      ([dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
        dusartLemma33FiniteRow_three, dusartLemma33FiniteRow_four,
        dusartLemma33FiniteRow_five, dusartLemma33FiniteRow_six,
        dusartLemma33FiniteRow_seven, dusartLemma33FiniteRow_eight,
        dusartLemma33FiniteRow_nine, dusartLemma33FiniteRow_ten_twentyfour,
        dusartLemma33FiniteRow_twentyfive_thirtyfive,
        dusartLemma33FiniteRow_thirtysix_sixtythree,
        dusartLemma33FiniteRow_sixtyfour_onetwenty,
        dusartLemma33FiniteRow_onetwentyone_onehundredsixtyseven,
        dusartLemma33FiniteRow_onehundredsixtyeight,
        dusartLemma33FiniteRow_onenine_sixtythree,
        dusartLemma33FiniteRow_twohundredfiftysix_twohundredeightyeight] ++
        [dusartLemma33FiniteRow_twohundredeightynine_threehundredfortytwo,
         dusartLemma33FiniteRow_threehundredfortythree_threehundredsixty]) 360 := by
  apply dusartLemma33FiniteRowsCover_append_row
  · apply dusartLemma33FiniteRowsCover_append_row
      dusartLemma33FiniteRowsCover_twohundredeightyeight
    intro x hgt hx hX
    constructor
    · linarith
    · norm_num
      linarith
  · intro x hgt hx hX
    constructor
    · linarith
    · norm_num
      linarith

theorem psi_sub_theta_nat_511_lt_twentyseven_point_one :
    Chebyshev.psi (511 : Real) - Chebyshev.theta 511 < (271 : Real) / 10 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 511
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 511
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 512,
      ↑(Nat.log p 511) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 512, Real.log ↑p < (271 : Real) / 10
  have hp : Nat.primesBelow 512 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43,
        47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107,
        109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173,
        179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239,
        241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311,
        313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383,
        389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457,
        461, 463, 467, 479, 487, 491, 499, 503, 509} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt,
    ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
    ElementaryLogBounds.log_17_lt, ElementaryLogBounds.log_19_lt]

theorem psi_sub_theta_nat_528_lt_twenty_eight :
    Chebyshev.psi (528 : Real) - Chebyshev.theta 528 < 28 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 528
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 528
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 529,
      ↑(Nat.log p 528) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 529, Real.log ↑p < 28
  have hp : Nat.primesBelow 529 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
        127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
        191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
        257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
        331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397,
        401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
        467, 479, 487, 491, 499, 503, 509, 521, 523} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt,
    ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
    ElementaryLogBounds.log_17_lt, ElementaryLogBounds.log_19_lt]

def dusartLemma33FiniteRow_fivehundredtwelve_fivehundredeight :
    DusartLemma33FiniteRow := by
  have htheta_twentytwo := Chebyshev.theta_eq_sum_primesLE_log 22
  have hp22 : Nat.primesLE 22 = {2, 3, 5, 7, 11, 13, 17, 19} := by decide
  rw [hp22] at htheta_twentytwo
  norm_num [Nat.log, Nat.log.go] at htheta_twentytwo
  apply dusartLemma33FiniteRow_of_endpoint_bounds 512 528 22
    (28 : Real) 16 8
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_528_lt_twenty_eight
  · nlinarith [htheta_twentytwo, Real.log_two_gt_d9,
      Real.log_three_gt_d9, Real.log_five_gt_d9, LogTables.log_7_gt]
  · intro x hx hleft
    have hbase : ((8 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (8 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (8 : Real) = ((8 : Real) ^ (3 : Nat)) ^ (1 / 3 : Real) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

theorem psi_sub_theta_nat_624_lt_thirtyone :
    Chebyshev.psi (624 : Real) - Chebyshev.theta 624 < 31 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 624
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 624
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 625,
      ↑(Nat.log p 624) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 625, Real.log ↑p < 31
  have hp : Nat.primesBelow 625 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
        127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
        191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
        257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
        331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397,
        401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
        467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
        563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt,
    ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
    ElementaryLogBounds.log_17_lt, ElementaryLogBounds.log_19_lt,
    ElementaryLogBounds.log_23_lt]

def dusartLemma33FiniteRow_fivehundredseventysix_sixhundredtwentyfour :
    DusartLemma33FiniteRow := by
  have htheta_twentytwo := Chebyshev.theta_eq_sum_primesLE_log 22
  have hp22 : Nat.primesLE 22 = {2, 3, 5, 7, 11, 13, 17, 19} := by decide
  rw [hp22] at htheta_twentytwo
  norm_num [Nat.log, Nat.log.go] at htheta_twentytwo
  have hlog10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [show (10 : Real) = 2 * 5 by norm_num, Real.log_mul]
    · norm_num
    all_goals positivity
  have hlog10_le19 : Real.log 10 ≤ Real.log 19 :=
    Real.log_le_log (by norm_num) (by norm_num)
  apply dusartLemma33FiniteRow_of_endpoint_bounds 576 624 24
    (31 : Real) 18 8
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_624_lt_thirtyone
  · have hmono : Chebyshev.theta (22 : Real) ≤ Chebyshev.theta 24 := by
      apply Chebyshev.theta_mono
      norm_num
    nlinarith [htheta_twentytwo, hmono, hlog10,
      hlog10_le19, Real.log_two_gt_d9, Real.log_three_gt_d9,
      Real.log_five_gt_d9, LogTables.log_7_gt]
  · intro x hx hleft
    have hbase : ((8 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (8 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (8 : Real) = ((8 : Real) ^ (3 : Nat)) ^ (1 / 3 : Real) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

theorem psi_sub_theta_nat_675_lt_thirty_three :
    Chebyshev.psi (675 : Real) - Chebyshev.theta 675 < 33 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 675
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 675
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 676,
      ↑(Nat.log p 675) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 676, Real.log ↑p < 33
  have hp : Nat.primesBelow 676 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
        127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
        191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
        257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
        331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397,
        401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
        467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
        563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619,
        631, 641, 643, 647, 653, 659, 661, 673} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt,
    ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
    ElementaryLogBounds.log_17_lt, ElementaryLogBounds.log_19_lt,
    ElementaryLogBounds.log_23_lt]

def dusartLemma33FiniteRow_sixhundredtwentyfive_sixhundredseventyfive :
    DusartLemma33FiniteRow := by
  have htheta_twentyfour := Chebyshev.theta_eq_sum_primesLE_log 24
  have hp24 : Nat.primesLE 24 = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by decide
  rw [hp24] at htheta_twentyfour
  norm_num [Nat.log, Nat.log.go] at htheta_twentyfour
  have hlog10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [show (10 : Real) = 2 * 5 by norm_num, Real.log_mul]
    · norm_num
    all_goals positivity
  have hlog10_le23 : Real.log 10 ≤ Real.log 23 :=
    Real.log_le_log (by norm_num) (by norm_num)
  apply dusartLemma33FiniteRow_of_endpoint_bounds 625 675 24
    (33 : Real) 18 (17 / 2)
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_675_lt_thirty_three
  · nlinarith [htheta_twentyfour, hlog10, hlog10_le23,
      Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9,
      LogTables.log_7_gt]
  · intro x hx hleft
    have hbase : ((17 / 2 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (17 / 2 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (17 / 2 : Real) = ((17 / 2 : Real) ^ (3 : Nat)) ^
          (1 / 3 : Real) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

theorem psi_sub_theta_nat_728_lt_thirty_three :
    Chebyshev.psi (728 : Real) - Chebyshev.theta 728 < 33 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 728
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 728
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 729,
      ↑(Nat.log p 728) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 729, Real.log ↑p < 33
  have hp : Nat.primesBelow 729 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
        127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
        191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
        257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
        331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397,
        401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
        467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
        563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619,
        631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701,
        709, 719, 727} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt,
    ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
    ElementaryLogBounds.log_17_lt, ElementaryLogBounds.log_19_lt,
    ElementaryLogBounds.log_23_lt]

def dusartLemma33FiniteRow_sixhundredseventysix_sevenhundredtwentyeight :
    DusartLemma33FiniteRow := by
  have htheta_twentyfour := Chebyshev.theta_eq_sum_primesLE_log 24
  have hp24 : Nat.primesLE 24 = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by decide
  rw [hp24] at htheta_twentyfour
  norm_num [Nat.log, Nat.log.go] at htheta_twentyfour
  apply dusartLemma33FiniteRow_of_endpoint_bounds 676 728 26
    (33 : Real) 18 (87 / 10)
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_728_lt_thirty_three
  · have hmono : Chebyshev.theta (24 : Real) ≤ Chebyshev.theta 26 := by
      apply Chebyshev.theta_mono
      norm_num
    exact lt_of_lt_of_le (by
      nlinarith [htheta_twentyfour, Real.log_two_gt_d9,
        Real.log_three_gt_d9, Real.log_five_gt_d9, LogTables.log_7_gt]) hmono
  · intro x hx hleft
    have hbase : ((87 / 10 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (87 / 10 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (87 / 10 : Real) = ((87 / 10 : Real) ^ (3 : Nat)) ^
          (1 / 3 : Real) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

theorem psi_sub_theta_nat_840_lt_thirtyseven :
    Chebyshev.psi (840 : Real) - Chebyshev.theta 840 < 337 / 10 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 840
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 840
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 841,
      ↑(Nat.log p 840) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 841, Real.log ↑p < 337 / 10
  have hp : Nat.primesBelow 841 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
        127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
        191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
        257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
        331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397,
        401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
        467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
        563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619,
        631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701,
        709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
        797, 809, 811, 821, 823, 827, 829, 839} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt,
    ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
    ElementaryLogBounds.log_17_lt, ElementaryLogBounds.log_19_lt,
    ElementaryLogBounds.log_23_lt]

def dusartLemma33FiniteRow_sevenhundredtwentynine_eighthundredforty :
    DusartLemma33FiniteRow := by
  have htheta_twentyfour := Chebyshev.theta_eq_sum_primesLE_log 24
  have hp24 : Nat.primesLE 24 = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by decide
  rw [hp24] at htheta_twentyfour
  norm_num [Nat.log, Nat.log.go] at htheta_twentyfour
  apply dusartLemma33FiniteRow_of_endpoint_bounds 729 840 27
    (337 / 10 : Real) 18 9
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_840_lt_thirtyseven
  · have hmono : Chebyshev.theta (24 : Real) ≤ Chebyshev.theta 27 := by
      apply Chebyshev.theta_mono
      norm_num
    exact lt_of_lt_of_le (by
      nlinarith [htheta_twentyfour, Real.log_two_gt_d9,
        Real.log_three_gt_d9, Real.log_five_gt_d9, LogTables.log_7_gt]) hmono
  · intro x hx hleft
    have hbase : ((9 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (9 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (9 : Real) = ((9 : Real) ^ (3 : Nat)) ^ (1 / 3 : Real) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

theorem psi_sub_theta_nat_960_lt_thirtyseven_point_three :
    Chebyshev.psi (960 : Real) - Chebyshev.theta 960 < (373 : Real) / 10 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 960
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 960
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 961,
      ↑(Nat.log p 960) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 961, Real.log ↑p < (373 : Real) / 10
  have hp : Nat.primesBelow 961 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
        127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
        191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
        257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
        331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397,
        401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
        467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
        563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619,
        631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701,
        709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
        797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863,
        877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt,
    ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
    ElementaryLogBounds.log_17_lt, ElementaryLogBounds.log_19_lt,
    ElementaryLogBounds.log_23_lt, ElementaryLogBounds.log_29_lt]

def dusartLemma33FiniteRow_eighthundredfortyone_ninehundredsixty :
    DusartLemma33FiniteRow := by
  have htheta_twentynine := Chebyshev.theta_eq_sum_primesLE_log 29
  have hp29 : Nat.primesLE 29 = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29} := by decide
  rw [hp29] at htheta_twentynine
  norm_num [Nat.log, Nat.log.go] at htheta_twentynine
  apply dusartLemma33FiniteRow_of_endpoint_bounds 841 960 29
    ((373 : Real) / 10) 21 (47 / 5)
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_960_lt_thirtyseven_point_three
  · nlinarith [htheta_twentynine, Real.log_two_gt_d9,
      Real.log_three_gt_d9, Real.log_five_gt_d9, LogTables.log_7_gt,
      LogTables.log_11_gt, LogTables.log_13_gt, LogTables.log_17_gt,
      LogTables.log_19_gt, LogTables.log_23_gt, LogTables.log_29_gt]
  · intro x hx hleft
    have hbase : ((47 / 5 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (47 / 5 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (47 / 5 : Real) = ((47 / 5 : Real) ^ (3 : Nat)) ^
          (1 / 3 : Real) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

theorem log_31_lt_three_point_four_seven : Real.log 31 < (347 : Real) / 100 := by
  have h := Real.log_lt_log (by norm_num : (0 : Real) < 31)
    (by norm_num : (31 : Real) < 32)
  rw [show (32 : Real) = 2 ^ (5 : Nat) by norm_num, Real.log_pow] at h
  nlinarith [LogTables.log_2_lt]

theorem log_37_lt_three_point_seven : Real.log 37 < (37 : Real) / 10 := by
  have h := Real.log_lt_log (by norm_num : (0 : Real) < 37)
    (by norm_num : (37 : Real) < 40)
  rw [show (40 : Real) = 2 ^ (3 : Nat) * 5 by norm_num,
    Real.log_mul, Real.log_pow] at h
  · nlinarith [LogTables.log_2_lt, LogTables.log_5_lt]
  all_goals positivity

theorem log_41_lt_three_point_eight : Real.log 41 < (38 : Real) / 10 := by
  have h := Real.log_lt_log (by norm_num : (0 : Real) < 41)
    (by norm_num : (41 : Real) < 45)
  rw [show (45 : Real) = 3 ^ (2 : Nat) * 5 by norm_num,
    Real.log_mul, Real.log_pow] at h
  · nlinarith [LogTables.log_3_lt, LogTables.log_5_lt]
  all_goals positivity

theorem log_43_lt_three_point_nine : Real.log 43 < (39 : Real) / 10 := by
  have h := Real.log_lt_log (by norm_num : (0 : Real) < 43)
    (by norm_num : (43 : Real) < 45)
  rw [show (45 : Real) = 3 ^ (2 : Nat) * 5 by norm_num,
    Real.log_mul, Real.log_pow] at h
  · nlinarith [LogTables.log_3_lt, LogTables.log_5_lt]
  all_goals positivity

theorem psi_sub_theta_nat_2196_lt_fiftyseven :
    Chebyshev.psi (2196 : Real) - Chebyshev.theta 2196 < 57 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 2196
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 2196
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 2197,
      ↑(Nat.log p 2196) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 2197, Real.log ↑p < 57
  have hp : Nat.primesBelow 2197 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
        127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
        191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
        257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
        331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397,
        401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
        467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
        563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619,
        631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701,
        709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
        797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863,
        877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953,
        967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031,
        1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093,
        1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171,
        1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237,
        1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303,
        1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409,
        1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471,
        1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543,
        1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607,
        1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669,
        1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753,
        1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847,
        1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913,
        1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999,
        2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081,
        2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141,
        2143, 2153, 2161, 2179} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt,
    ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
    ElementaryLogBounds.log_17_lt, ElementaryLogBounds.log_19_lt,
    ElementaryLogBounds.log_23_lt, ElementaryLogBounds.log_29_lt,
    log_31_lt_three_point_four_seven, log_37_lt_three_point_seven,
    log_41_lt_three_point_eight, log_43_lt_three_point_nine]

def dusartLemma33FiniteRow_twothousandtwentyfive_twothousandonehundredninetysix :
    DusartLemma33FiniteRow := by
  have htheta_fortythree := Chebyshev.theta_eq_sum_primesLE_log 43
  have hp43 : Nat.primesLE 43 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43} := by decide
  rw [hp43] at htheta_fortythree
  norm_num [Nat.log, Nat.log.go] at htheta_fortythree
  apply dusartLemma33FiniteRow_of_endpoint_bounds 2025 2196 45
    (57 : Real) 36 (63 / 5)
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_2196_lt_fiftyseven
  · have hlog29_le31 : Real.log 29 ≤ Real.log 31 :=
      Real.log_le_log (by norm_num) (by norm_num)
    have hlog29_le37 : Real.log 29 ≤ Real.log 37 :=
      Real.log_le_log (by norm_num) (by norm_num)
    have hlog29_le41 : Real.log 29 ≤ Real.log 41 :=
      Real.log_le_log (by norm_num) (by norm_num)
    have hlog29_le43 : Real.log 29 ≤ Real.log 43 :=
      Real.log_le_log (by norm_num) (by norm_num)
    nlinarith [htheta_fortythree, Real.log_two_gt_d9,
      Real.log_three_gt_d9, Real.log_five_gt_d9, LogTables.log_7_gt,
      LogTables.log_11_gt, LogTables.log_13_gt, LogTables.log_17_gt,
      LogTables.log_19_gt, LogTables.log_23_gt, LogTables.log_29_gt,
      hlog29_le31, hlog29_le37, hlog29_le41, hlog29_le43]
  · intro x hx hleft
    have hbase : ((63 / 5 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (63 / 5 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (63 / 5 : Real) = ((63 / 5 : Real) ^ (3 : Nat)) ^
          (1 / 3 : Real) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

theorem psi_sub_theta_nat_2208_lt_fiftynine :
    Chebyshev.psi (2208 : Real) - Chebyshev.theta 2208 < 59 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 2208
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 2208
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 2209,
      ↑(Nat.log p 2208) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 2209, Real.log ↑p < 59
  have hp : Nat.primesBelow 2209 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
        127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
        191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
        257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
        331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397,
        401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
        467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
        563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619,
        631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701,
        709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
        797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863,
        877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953,
        967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031,
        1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093,
        1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171,
        1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237,
        1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303,
        1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409,
        1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471,
        1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543,
        1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607,
        1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669,
        1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753,
        1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847,
        1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913,
        1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999,
        2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081,
        2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141,
        2143, 2153, 2161, 2179, 2203, 2207} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt,
    ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
    ElementaryLogBounds.log_17_lt, ElementaryLogBounds.log_19_lt,
    ElementaryLogBounds.log_23_lt, ElementaryLogBounds.log_29_lt,
    log_31_lt_three_point_four_seven, log_37_lt_three_point_seven,
    log_41_lt_three_point_eight, log_43_lt_three_point_nine]

def dusartLemma33FiniteRow_twothousandonehundredninetyseven_twothousandtwohundredeight :
    DusartLemma33FiniteRow := by
  have htheta_fortythree := Chebyshev.theta_eq_sum_primesLE_log 43
  have hp43 : Nat.primesLE 43 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43} := by decide
  rw [hp43] at htheta_fortythree
  norm_num [Nat.log, Nat.log.go] at htheta_fortythree
  have hlog30_le31 : Real.log 30 ≤ Real.log 31 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hlog36_le37 : Real.log 36 ≤ Real.log 37 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hlog40_le41 : Real.log 40 ≤ Real.log 41 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hlog42_le43 : Real.log 42 ≤ Real.log 43 :=
    Real.log_le_log (by norm_num) (by norm_num)
  apply dusartLemma33FiniteRow_of_endpoint_bounds 2197 2208 46
    (59 : Real) 37 13
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_2208_lt_fiftynine
  · nlinarith [htheta_fortythree, hlog30_le31, hlog36_le37,
      hlog40_le41, hlog42_le43, LogTables.log_30_gt,
      Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9,
      LogTables.log_7_gt]
  · intro x hx hleft
    have hbase : ((13 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (13 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (13 : Real) = ((13 : Real) ^ (3 : Nat)) ^ (1 / 3 : Real) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

end

end PrimeFactorUnimodality
