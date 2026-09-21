import LeanCert.Tactic.IntervalAuto
import Mathlib.Analysis.Complex.ExponentialBounds
import PrimeFactorUnimodality.Helpers.Analytic.DusartFiniteRows
import PrimeFactorUnimodality.Helpers.Analytic.DusartIntermediateLemma
import PrimeFactorUnimodality.Helpers.Analytic.DusartLemma33MidrangeCover
import PrimeFactorUnimodality.Helpers.Analytic.ElementaryChebyshevConsequences
import PrimeFactorUnimodality.Helpers.Analytic.ElementaryLogBounds
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitThetaBounds
import PrimeFactorUnimodality.Helpers.Analytic.RelativePsiTheta
import PrimeFactorUnimodality.Helpers.Analytic.ZetaExplicitBounds


set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/- The finite boundary in Dusart's Lemma 3.3 is exactly 10^33. -/

/-! # DusartProof source part 01

This module is a sequential source split of the analytic development.
-/

theorem dusart_paper_lemma_3_3_finite_cutoff_eq :
    ((10 ^ 11 : Real) ^ 3) = 10 ^ 33 := by
  norm_num [pow_mul]

theorem psi_sub_theta_nat_24_lt_four :
    Chebyshev.psi (24 : Real) - Chebyshev.theta 24 < 4 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 24
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 24
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 25,
      ↑(Nat.log p 24) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 25, Real.log ↑p < 4
  have hp : Nat.primesBelow 25 = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9]

theorem psi_sub_theta_nat_3_eq_zero :
    Chebyshev.psi (3 : Real) - Chebyshev.theta 3 = 0 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 3
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 3
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesLE 3,
      ↑(Nat.log p 3) * Real.log ↑p) -
    ∑ p ∈ Nat.primesLE 3, Real.log ↑p = 0
  have hp : Nat.primesLE 3 = {2, 3} := by decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]

theorem psi_sub_theta_nat_8_lt_two :
    Chebyshev.psi (8 : Real) - Chebyshev.theta 8 < 2 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 8
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 8
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 9,
      ↑(Nat.log p 8) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 9, Real.log ↑p < 2
  have hp : Nat.primesBelow 9 = {2, 3, 5, 7} := by decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9]

theorem psi_sub_theta_nat_35_lt_eight :
    Chebyshev.psi (35 : Real) - Chebyshev.theta 35 < 8 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 35
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 35
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesLE 35,
      ↑(Nat.log p 35) * Real.log ↑p) -
    ∑ p ∈ Nat.primesLE 35, Real.log ↑p < 8
  have hp : Nat.primesLE 35 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  ring_nf
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt]

theorem psi_sub_theta_nat_63_lt_nine :
    Chebyshev.psi (63 : Real) - Chebyshev.theta 63 < 9 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 63
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 63
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesLE 63,
      ↑(Nat.log p 63) * Real.log ↑p) -
    ∑ p ∈ Nat.primesLE 63, Real.log ↑p < 9
  have hp : Nat.primesLE 63 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  ring_nf
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt]

def dusartLemma33FiniteRow_ten_twentyfour : DusartLemma33FiniteRow := by
  have htheta_three := Chebyshev.theta_eq_sum_primesLE_log 3
  have hp3 : Nat.primesLE 3 = {2, 3} := by decide
  rw [hp3] at htheta_three
  norm_num [Nat.log, Nat.log.go] at htheta_three
  apply dusartLemma33FiniteRow_of_endpoint_bounds 10 24 3 4 (1 / 2) 2
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_24_lt_four
  · nlinarith [htheta_three, Real.log_two_gt_d9,
      Real.log_pos (by norm_num : (1 : Real) < 3)]
  · intro x hx hleft
    have hpow := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 8)
      (by linarith : (8 : Real) ≤ x)
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    norm_num at hpow ⊢
    exact hpow
  · norm_num

theorem dusartLemma33FiniteRowsCover_ten_twentyfour :
    DusartLemma33FiniteRowsCover
      [dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
        dusartLemma33FiniteRow_three, dusartLemma33FiniteRow_four,
        dusartLemma33FiniteRow_five, dusartLemma33FiniteRow_six,
        dusartLemma33FiniteRow_seven, dusartLemma33FiniteRow_eight,
        dusartLemma33FiniteRow_nine, dusartLemma33FiniteRow_ten_twentyfour] 24 := by
  intro x hx hX
  by_cases hsmall : x < 2
  · refine ⟨dusartLemma33FiniteRow_zero_one, by simp, ?_, ?_⟩
    · norm_num [dusartLemma33FiniteRow_zero_one]
      exact hx.le
    · norm_num [dusartLemma33FiniteRow_zero_one]
      linarith
  · by_cases htwo : x < 3
    · refine ⟨dusartLemma33FiniteRow_two, by simp, ?_, ?_⟩
      · norm_num [dusartLemma33FiniteRow_two]
        exact le_of_not_gt hsmall
      · norm_num [dusartLemma33FiniteRow_two]
        linarith
    · by_cases hthree : x < 4
      · refine ⟨dusartLemma33FiniteRow_three, by simp, ?_, ?_⟩
        · norm_num [dusartLemma33FiniteRow_three]
          exact le_of_not_gt htwo
        · norm_num [dusartLemma33FiniteRow_three]
          linarith
      · by_cases hfour : x < 5
        · refine ⟨dusartLemma33FiniteRow_four, by simp, ?_, ?_⟩
          · norm_num [dusartLemma33FiniteRow_four]
            exact le_of_not_gt hthree
          · norm_num [dusartLemma33FiniteRow_four]
            linarith
        · by_cases hfive : x < 6
          · refine ⟨dusartLemma33FiniteRow_five, by simp, ?_, ?_⟩
            · norm_num [dusartLemma33FiniteRow_five]
              exact le_of_not_gt hfour
            · norm_num [dusartLemma33FiniteRow_five]
              linarith
          · by_cases hsix : x < 7
            · refine ⟨dusartLemma33FiniteRow_six, by simp, ?_, ?_⟩
              · norm_num [dusartLemma33FiniteRow_six]
                exact le_of_not_gt hfive
              · norm_num [dusartLemma33FiniteRow_six]
                linarith
            · by_cases hseven : x < 8
              · refine ⟨dusartLemma33FiniteRow_seven, by simp, ?_, ?_⟩
                · norm_num [dusartLemma33FiniteRow_seven]
                  exact le_of_not_gt hsix
                · norm_num [dusartLemma33FiniteRow_seven]
                  linarith
              · by_cases height : x < 9
                · refine ⟨dusartLemma33FiniteRow_eight, by simp, ?_, ?_⟩
                  · norm_num [dusartLemma33FiniteRow_eight]
                    exact le_of_not_gt hseven
                  · norm_num [dusartLemma33FiniteRow_eight]
                    linarith
                · by_cases hnine : x < 10
                  · refine ⟨dusartLemma33FiniteRow_nine, by simp, ?_, ?_⟩
                    · norm_num [dusartLemma33FiniteRow_nine]
                      exact le_of_not_gt height
                    · norm_num [dusartLemma33FiniteRow_nine]
                      linarith
                  · refine ⟨dusartLemma33FiniteRow_ten_twentyfour, by simp, ?_, ?_⟩
                    · norm_num [dusartLemma33FiniteRow_ten_twentyfour]
                      exact le_of_not_gt hnine
                    · norm_num [dusartLemma33FiniteRow_ten_twentyfour]
                      linarith

def dusartLemma33FiniteRow_twentyfive_thirtyfive : DusartLemma33FiniteRow :=
  { left := 25
    right := 35
    left_le_right := by norm_num
    valid := by
      intro x hx hleft hright
      have hx25 : (25 : Real) ≤ x := by exact_mod_cast hleft
      have hx36 : x < 36 := by norm_num at hright ⊢; exact hright
      have htransport : Chebyshev.psi x - Chebyshev.theta x =
          Chebyshev.psi (⌊x⌋₊ : Real) - Chebyshev.theta (⌊x⌋₊ : Real) := by
        rw [Chebyshev.psi_eq_psi_coe_floor,
          Chebyshev.theta_eq_theta_coe_floor]
      have hfloor : (⌊x⌋₊ : Real) ≤ 35 := by
        exact_mod_cast Nat.le_of_lt_succ
          ((Nat.floor_lt hx.le).2 (by norm_num; exact hx36))
      have hleft : Chebyshev.psi x - Chebyshev.theta x < 8 := by
        rw [htransport]
        exact (psi_sub_theta_mono hfloor).trans_lt psi_sub_theta_nat_35_lt_eight
      have hsqrt : (5 : Real) ≤ Real.sqrt x := by
        nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
      have htheta_mono : Chebyshev.theta 5 ≤
          Chebyshev.theta (Real.sqrt x) :=
        Chebyshev.theta_mono hsqrt
      have htheta_five := Chebyshev.theta_eq_sum_primesLE_log 5
      have hp5 : Nat.primesLE 5 = {2, 3, 5} := by decide
      rw [hp5] at htheta_five
      norm_num [Nat.log, Nat.log.go] at htheta_five
      have htheta_lower : (3 : Real) < Chebyshev.theta 5 := by
        nlinarith [htheta_five, Real.log_two_gt_d9,
          Real.log_three_gt_d9, Real.log_five_gt_d9]
      have hbase : ((14 / 5 : Real) ^ (3 : Nat)) ≤ x := by
        norm_num
        linarith
      have hpow := Real.rpow_le_rpow (by positivity :
          (0 : Real) ≤ (14 / 5 : Real) ^ (3 : Nat)) hbase
        (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      have hpow_const : (14 / 5 : Real) ≤ x ^ (1 / 3 : Real) := by
        calc
          (14 / 5 : Real) = ((14 / 5 : Real) ^ (3 : Nat)) ^
              (1 / 3 : Real) := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
                norm_num
          _ ≤ x ^ (1 / 3 : Real) := hpow
      nlinarith [hleft, htheta_mono, htheta_lower, hpow_const] }

def dusartLemma33FiniteRow_thirtysix_sixtythree : DusartLemma33FiniteRow :=
  { left := 36
    right := 63
    left_le_right := by norm_num
    valid := by
      intro x hx hleft hright
      have hx36 : (36 : Real) ≤ x := by exact_mod_cast hleft
      have hx64 : x < 64 := by norm_num at hright ⊢; exact hright
      have htransport : Chebyshev.psi x - Chebyshev.theta x =
          Chebyshev.psi (⌊x⌋₊ : Real) - Chebyshev.theta (⌊x⌋₊ : Real) := by
        rw [Chebyshev.psi_eq_psi_coe_floor,
          Chebyshev.theta_eq_theta_coe_floor]
      have hfloor : (⌊x⌋₊ : Real) ≤ 63 := by
        exact_mod_cast Nat.le_of_lt_succ
          ((Nat.floor_lt hx.le).2 (by norm_num; exact hx64))
      have hleft : Chebyshev.psi x - Chebyshev.theta x < 9 := by
        rw [htransport]
        exact (psi_sub_theta_mono hfloor).trans_lt psi_sub_theta_nat_63_lt_nine
      have hsqrt : (6 : Real) ≤ Real.sqrt x := by
        nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
      have htheta_mono : Chebyshev.theta 6 ≤
          Chebyshev.theta (Real.sqrt x) :=
        Chebyshev.theta_mono hsqrt
      have htheta_six := Chebyshev.theta_eq_sum_primesLE_log 6
      have hp6 : Nat.primesLE 6 = {2, 3, 5} := by decide
      rw [hp6] at htheta_six
      norm_num [Nat.log, Nat.log.go] at htheta_six
      have htheta_lower : (3 : Real) < Chebyshev.theta 6 := by
        nlinarith [htheta_six, Real.log_two_gt_d9,
          Real.log_three_gt_d9, Real.log_five_gt_d9]
      have hbase : ((16 / 5 : Real) ^ (3 : Nat)) ≤ x := by
        norm_num
        linarith
      have hpow := Real.rpow_le_rpow (by positivity :
          (0 : Real) ≤ (16 / 5 : Real) ^ (3 : Nat)) hbase
        (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      have hpow_const : (16 / 5 : Real) ≤ x ^ (1 / 3 : Real) := by
        calc
          (16 / 5 : Real) = ((16 / 5 : Real) ^ (3 : Nat)) ^
              (1 / 3 : Real) := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
                norm_num
          _ ≤ x ^ (1 / 3 : Real) := hpow
      nlinarith [hleft, htheta_mono, htheta_lower, hpow_const] }

theorem dusartLemma33FiniteRowsCover_sixtythree :
    DusartLemma33FiniteRowsCover
      [dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
        dusartLemma33FiniteRow_three, dusartLemma33FiniteRow_four,
        dusartLemma33FiniteRow_five, dusartLemma33FiniteRow_six,
        dusartLemma33FiniteRow_seven, dusartLemma33FiniteRow_eight,
        dusartLemma33FiniteRow_nine, dusartLemma33FiniteRow_ten_twentyfour,
        dusartLemma33FiniteRow_twentyfive_thirtyfive,
        dusartLemma33FiniteRow_thirtysix_sixtythree] 63 := by
  intro x hx hX
  by_cases hsmall : x < 2
  · refine ⟨dusartLemma33FiniteRow_zero_one, by simp, ?_, ?_⟩
    · norm_num [dusartLemma33FiniteRow_zero_one]
      exact hx.le
    · norm_num [dusartLemma33FiniteRow_zero_one]
      linarith
  · by_cases htwo : x < 3
    · refine ⟨dusartLemma33FiniteRow_two, by simp, ?_, ?_⟩
      · norm_num [dusartLemma33FiniteRow_two]
        exact le_of_not_gt hsmall
      · norm_num [dusartLemma33FiniteRow_two]
        linarith
    · by_cases hthree : x < 4
      · refine ⟨dusartLemma33FiniteRow_three, by simp, ?_, ?_⟩
        · norm_num [dusartLemma33FiniteRow_three]
          exact le_of_not_gt htwo
        · norm_num [dusartLemma33FiniteRow_three]
          linarith
      · by_cases hfour : x < 5
        · refine ⟨dusartLemma33FiniteRow_four, by simp, ?_, ?_⟩
          · norm_num [dusartLemma33FiniteRow_four]
            exact le_of_not_gt hthree
          · norm_num [dusartLemma33FiniteRow_four]
            linarith
        · by_cases hfive : x < 6
          · refine ⟨dusartLemma33FiniteRow_five, by simp, ?_, ?_⟩
            · norm_num [dusartLemma33FiniteRow_five]
              exact le_of_not_gt hfour
            · norm_num [dusartLemma33FiniteRow_five]
              linarith
          · by_cases hsix : x < 7
            · refine ⟨dusartLemma33FiniteRow_six, by simp, ?_, ?_⟩
              · norm_num [dusartLemma33FiniteRow_six]
                exact le_of_not_gt hfive
              · norm_num [dusartLemma33FiniteRow_six]
                linarith
            · by_cases hseven : x < 8
              · refine ⟨dusartLemma33FiniteRow_seven, by simp, ?_, ?_⟩
                · norm_num [dusartLemma33FiniteRow_seven]
                  exact le_of_not_gt hsix
                · norm_num [dusartLemma33FiniteRow_seven]
                  linarith
              · by_cases height : x < 9
                · refine ⟨dusartLemma33FiniteRow_eight, by simp, ?_, ?_⟩
                  · norm_num [dusartLemma33FiniteRow_eight]
                    exact le_of_not_gt hseven
                  · norm_num [dusartLemma33FiniteRow_eight]
                    linarith
                · by_cases hnine : x < 10
                  · refine ⟨dusartLemma33FiniteRow_nine, by simp, ?_, ?_⟩
                    · norm_num [dusartLemma33FiniteRow_nine]
                      exact le_of_not_gt height
                    · norm_num [dusartLemma33FiniteRow_nine]
                      linarith
                  · by_cases htwentyfour : x < 25
                    · refine ⟨dusartLemma33FiniteRow_ten_twentyfour, by simp, ?_, ?_⟩
                      · norm_num [dusartLemma33FiniteRow_ten_twentyfour]
                        exact le_of_not_gt hnine
                      · norm_num [dusartLemma33FiniteRow_ten_twentyfour]
                        linarith
                    · by_cases hthirtyfive : x < 36
                      · refine ⟨dusartLemma33FiniteRow_twentyfive_thirtyfive, by simp, ?_, ?_⟩
                        · norm_num [dusartLemma33FiniteRow_twentyfive_thirtyfive]
                          exact le_of_not_gt htwentyfour
                        · norm_num [dusartLemma33FiniteRow_twentyfive_thirtyfive]
                          linarith
                      · refine ⟨dusartLemma33FiniteRow_thirtysix_sixtythree, by simp, ?_, ?_⟩
                        · norm_num [dusartLemma33FiniteRow_thirtysix_sixtythree]
                          exact le_of_not_gt hthirtyfive
                        · norm_num [dusartLemma33FiniteRow_thirtysix_sixtythree]
                          linarith

theorem psi_sub_theta_nat_120_lt_ten :
    Chebyshev.psi (120 : Real) - Chebyshev.theta 120 < 10 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 120
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 120
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 121,
      ↑(Nat.log p 120) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 121, Real.log ↑p < 10
  have hp : Nat.primesBelow 121 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt]

def dusartLemma33FiniteRow_sixtyfour_onetwenty : DusartLemma33FiniteRow := by
  have htheta_eight := Chebyshev.theta_eq_sum_primesLE_log 8
  have hp8 : Nat.primesLE 8 = {2, 3, 5, 7} := by decide
  rw [hp8] at htheta_eight
  norm_num [Nat.log, Nat.log.go] at htheta_eight
  apply dusartLemma33FiniteRow_of_endpoint_bounds 64 120 8 10 5 4
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_120_lt_ten
  · nlinarith [htheta_eight, Real.log_two_gt_d9, Real.log_three_gt_d9,
      Real.log_five_gt_d9, LogTables.log_7_gt]
  · intro x hx hleft
    have hpow := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 64)
      hleft (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    norm_num at hpow ⊢
    exact hpow
  · norm_num

theorem dusartLemma33FiniteRowsCover_onetwenty :
    DusartLemma33FiniteRowsCover
      ([dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
        dusartLemma33FiniteRow_three, dusartLemma33FiniteRow_four,
        dusartLemma33FiniteRow_five, dusartLemma33FiniteRow_six,
        dusartLemma33FiniteRow_seven, dusartLemma33FiniteRow_eight,
        dusartLemma33FiniteRow_nine, dusartLemma33FiniteRow_ten_twentyfour,
        dusartLemma33FiniteRow_twentyfive_thirtyfive,
        dusartLemma33FiniteRow_thirtysix_sixtythree] ++
        [dusartLemma33FiniteRow_sixtyfour_onetwenty]) 120 := by
  intro x hx hX
  by_cases hle : x ≤ 63
  · obtain ⟨row, hrow, hleft, hright⟩ :=
      dusartLemma33FiniteRowsCover_sixtythree x hx hle
    exact ⟨row, by simp [hrow], hleft, hright⟩
  · refine ⟨dusartLemma33FiniteRow_sixtyfour_onetwenty, by simp, ?_, ?_⟩
    · exact le_of_not_ge hle
    · norm_num
      linarith

theorem dusartLemma33FiniteRowsCover_onetwenty_compact :
    DusartLemma33FiniteRowsCover
      ([dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
        dusartLemma33FiniteRow_three, dusartLemma33FiniteRow_four,
        dusartLemma33FiniteRow_five, dusartLemma33FiniteRow_six,
        dusartLemma33FiniteRow_seven, dusartLemma33FiniteRow_eight,
        dusartLemma33FiniteRow_nine, dusartLemma33FiniteRow_ten_twentyfour,
        dusartLemma33FiniteRow_twentyfive_thirtyfive,
        dusartLemma33FiniteRow_thirtysix_sixtythree] ++
        [dusartLemma33FiniteRow_sixtyfour_onetwenty]) 120 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_sixtythree
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem psi_sub_theta_nat_167_lt_sixteen :
    Chebyshev.psi (167 : Real) - Chebyshev.theta 167 < 16 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 167
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 167
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 168,
      ↑(Nat.log p 167) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 168, Real.log ↑p < 16
  have hp : Nat.primesBelow 168 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
        127, 131, 137, 139, 149, 151, 157, 163, 167} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt, ElementaryLogBounds.log_11_lt]

def dusartLemma33FiniteRow_onetwentyone_onehundredsixtyseven :
    DusartLemma33FiniteRow := by
  have htheta_eleven := Chebyshev.theta_eq_sum_primesLE_log 11
  have hp11 : Nat.primesLE 11 = {2, 3, 5, 7, 11} := by decide
  rw [hp11] at htheta_eleven
  norm_num [Nat.log, Nat.log.go] at htheta_eleven
  have hlog10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [show (10 : Real) = 2 * 5 by norm_num, Real.log_mul]
    · norm_num
    all_goals positivity
  have hlog10_le : Real.log 10 ≤ Real.log 11 :=
    Real.log_le_log (by norm_num) (by norm_num)
  apply dusartLemma33FiniteRow_of_endpoint_bounds 121 167 11 16 (15 / 2) (49 / 10)
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_167_lt_sixteen
  · nlinarith [htheta_eleven, hlog10, hlog10_le,
      Real.log_two_gt_d9, Real.log_three_gt_d9,
      Real.log_five_gt_d9, LogTables.log_7_gt]
  · intro x hx hleft
    have hbase : ((49 / 10 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (49 / 10 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (49 / 10 : Real) = ((49 / 10 : Real) ^ (3 : Nat)) ^
          (1 / 3 : Real) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

theorem dusartLemma33FiniteRowsCover_onehundredsixtyseven :
    DusartLemma33FiniteRowsCover
      ([dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
        dusartLemma33FiniteRow_three, dusartLemma33FiniteRow_four,
        dusartLemma33FiniteRow_five, dusartLemma33FiniteRow_six,
        dusartLemma33FiniteRow_seven, dusartLemma33FiniteRow_eight,
        dusartLemma33FiniteRow_nine, dusartLemma33FiniteRow_ten_twentyfour,
        dusartLemma33FiniteRow_twentyfive_thirtyfive,
        dusartLemma33FiniteRow_thirtysix_sixtythree,
        dusartLemma33FiniteRow_sixtyfour_onetwenty] ++
        [dusartLemma33FiniteRow_onetwentyone_onehundredsixtyseven]) 167 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_onetwenty_compact
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem psi_sub_theta_nat_168_lt_sixteen :
    Chebyshev.psi (168 : Real) - Chebyshev.theta 168 < 16 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 168
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 168
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 169,
      ↑(Nat.log p 168) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 169, Real.log ↑p < 16
  have hp : Nat.primesBelow 169 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
        127, 131, 137, 139, 149, 151, 157, 163, 167} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt, ElementaryLogBounds.log_11_lt]

def dusartLemma33FiniteRow_onehundredsixtyeight : DusartLemma33FiniteRow := by
  have htheta_eleven := Chebyshev.theta_eq_sum_primesLE_log 11
  have hp11 : Nat.primesLE 11 = {2, 3, 5, 7, 11} := by decide
  rw [hp11] at htheta_eleven
  norm_num [Nat.log, Nat.log.go] at htheta_eleven
  have hlog10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [show (10 : Real) = 2 * 5 by norm_num, Real.log_mul]
    · norm_num
    all_goals positivity
  have hlog10_le : Real.log 10 ≤ Real.log 11 :=
    Real.log_le_log (by norm_num) (by norm_num)
  apply dusartLemma33FiniteRow_of_endpoint_bounds 168 168 11 16 (15 / 2) (11 / 2)
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_168_lt_sixteen
  · nlinarith [htheta_eleven, hlog10, hlog10_le,
      Real.log_two_gt_d9, Real.log_three_gt_d9,
      Real.log_five_gt_d9, LogTables.log_7_gt]
  · intro x hx hleft
    have hbase : ((11 / 2 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (11 / 2 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (11 / 2 : Real) = ((11 / 2 : Real) ^ (3 : Nat)) ^
          (1 / 3 : Real) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

theorem psi_sub_theta_nat_255_lt_nineteen :
    Chebyshev.psi (255 : Real) - Chebyshev.theta 255 < (187 : Real) / 10 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 255
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 255
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 256,
      ↑(Nat.log p 255) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 256, Real.log ↑p < (187 : Real) / 10
  have hp : Nat.primesBelow 256 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
        127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
        191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt,
    ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt]

def dusartLemma33FiniteRow_onenine_sixtythree : DusartLemma33FiniteRow := by
  have htheta_thirteen := Chebyshev.theta_eq_sum_primesLE_log 13
  have hp13 : Nat.primesLE 13 = {2, 3, 5, 7, 11, 13} := by decide
  rw [hp13] at htheta_thirteen
  norm_num [Nat.log, Nat.log.go] at htheta_thirteen
  have hlog10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [show (10 : Real) = 2 * 5 by norm_num, Real.log_mul]
    · norm_num
    all_goals positivity
  have hlog10_le11 : Real.log 10 ≤ Real.log 11 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hlog10_le13 : Real.log 10 ≤ Real.log 13 :=
    Real.log_le_log (by norm_num) (by norm_num)
  apply dusartLemma33FiniteRow_of_endpoint_bounds 169 255 13
    ((187 : Real) / 10) 10 (49 / 10)
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_255_lt_nineteen
  · nlinarith [htheta_thirteen, hlog10, hlog10_le11, hlog10_le13,
      Real.log_two_gt_d9, Real.log_three_gt_d9,
      Real.log_five_gt_d9, LogTables.log_7_gt]
  · intro x hx hleft
    have hbase : ((49 / 10 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (49 / 10 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (49 / 10 : Real) = ((49 / 10 : Real) ^ (3 : Nat)) ^
          (1 / 3 : Real) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

theorem dusartLemma33FiniteRowsCover_twohundredfiftyfive :
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
        dusartLemma33FiniteRow_onehundredsixtyeight] ++
        [dusartLemma33FiniteRow_onenine_sixtythree]) 255 := by
  apply dusartLemma33FiniteRowsCover_append_row
  · apply dusartLemma33FiniteRowsCover_append_row
      dusartLemma33FiniteRowsCover_onehundredsixtyseven
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

theorem psi_sub_theta_nat_288_lt_twenty :
    Chebyshev.psi (288 : Real) - Chebyshev.theta 288 < 20 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 288
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 288
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 289,
      ↑(Nat.log p 288) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 289, Real.log ↑p < 20
  have hp : Nat.primesBelow 289 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
        127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
        191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
        257, 263, 269, 271, 277, 281, 283} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt,
    ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt]

def dusartLemma33FiniteRow_twohundredfiftysix_twohundredeightyeight :
    DusartLemma33FiniteRow := by
  have htheta_sixteen := Chebyshev.theta_eq_sum_primesLE_log 16
  have hp16 : Nat.primesLE 16 = {2, 3, 5, 7, 11, 13} := by decide
  rw [hp16] at htheta_sixteen
  norm_num [Nat.log, Nat.log.go] at htheta_sixteen
  have hlog10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [show (10 : Real) = 2 * 5 by norm_num, Real.log_mul]
    · norm_num
    all_goals positivity
  have hlog10_le11 : Real.log 10 ≤ Real.log 11 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hlog10_le13 : Real.log 10 ≤ Real.log 13 :=
    Real.log_le_log (by norm_num) (by norm_num)
  apply dusartLemma33FiniteRow_of_endpoint_bounds 256 288 16 20 9 (63 / 10)
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_288_lt_twenty
  · nlinarith [htheta_sixteen, hlog10, hlog10_le11, hlog10_le13,
      Real.log_two_gt_d9, Real.log_three_gt_d9,
      Real.log_five_gt_d9, LogTables.log_7_gt]
  · intro x hx hleft
    have hbase : ((63 / 10 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (63 / 10 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (63 / 10 : Real) = ((63 / 10 : Real) ^ (3 : Nat)) ^
          (1 / 3 : Real) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

theorem dusartLemma33FiniteRowsCover_twohundredeightyeight :
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
        dusartLemma33FiniteRow_onenine_sixtythree] ++
        [dusartLemma33FiniteRow_twohundredfiftysix_twohundredeightyeight]) 288 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_twohundredfiftyfive
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem psi_sub_theta_nat_342_lt_twenty_three :
    Chebyshev.psi (342 : Real) - Chebyshev.theta 342 < 23 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 342
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 342
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 343,
      ↑(Nat.log p 342) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 343, Real.log ↑p < 23
  have hp : Nat.primesBelow 343 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
        127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
        191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
        257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
        331, 337} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt,
    ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
    ElementaryLogBounds.log_17_lt]

end

end PrimeFactorUnimodality
