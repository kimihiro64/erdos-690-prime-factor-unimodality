import PrimeFactorUnimodality.Helpers.Analytic.RelativePsiTheta
import PrimeFactorUnimodality.Helpers.Analytic.ElementaryChebyshevConsequences
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitThetaBounds
import PrimeFactorUnimodality.Helpers.Analytic.ElementaryLogBounds
import PrimeFactorUnimodality.Helpers.Analytic.DusartFiniteRows
import PrimeFactorUnimodality.Helpers.Analytic.ZetaExplicitBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import LeanCert.Tactic.IntervalAuto

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem psi_sub_theta_mono {x y : Real} (hxy : x ≤ y) :
    Chebyshev.psi x - Chebyshev.theta x ≤
      Chebyshev.psi y - Chebyshev.theta y := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,
    Chebyshev.psi_sub_theta_eq_sum_not_prime]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    exact ⟨⟨hn.1.1, hn.1.2.trans (Nat.floor_mono hxy)⟩, hn.2⟩
  · intro n hn hns
    exact ArithmeticFunction.vonMangoldt_nonneg

def dusartLemma33FiniteRow_of_endpoint_bounds
    (left right root : Nat) (B L P : Real)
    (hleft : left ≤ right)
    (hroot : ∀ x : Real, 0 < x → (left : Real) ≤ x →
      x < (right : Real) + 1 → (root : Real) ≤ Real.sqrt x)
    (hpsi : Chebyshev.psi (right : Real) - Chebyshev.theta right < B)
    (htheta : L < Chebyshev.theta root)
    (hpow : ∀ x : Real, 0 < x → (left : Real) ≤ x →
      P ≤ x ^ (1 / (3 : Real)))
    (hmargin : B - L < (1777745 : Real) / 1000000 * P) :
    DusartLemma33FiniteRow :=
  { left := left
    right := right
    left_le_right := hleft
    valid := by
      intro x hx hleft_x hright_x
      have htransport : Chebyshev.psi x - Chebyshev.theta x =
          Chebyshev.psi (⌊x⌋₊ : Real) - Chebyshev.theta (⌊x⌋₊ : Real) := by
        rw [Chebyshev.psi_eq_psi_coe_floor,
          Chebyshev.theta_eq_theta_coe_floor]
      have hfloor : (⌊x⌋₊ : Real) ≤ right := by
        exact_mod_cast Nat.le_of_lt_succ
          ((Nat.floor_lt hx.le).2 (by simpa using hright_x))
      have hleft_bound : Chebyshev.psi x - Chebyshev.theta x < B := by
        rw [htransport]
        exact (psi_sub_theta_mono hfloor).trans_lt hpsi
      have htheta_bound : L < Chebyshev.theta (Real.sqrt x) :=
        lt_of_lt_of_le htheta (Chebyshev.theta_mono
          (hroot x hx hleft_x hright_x))
      have hpow_bound := hpow x hx hleft_x
      nlinarith }

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

theorem log_47_lt_three_point_eight_eight : Real.log 47 < (388 : Real) / 100 := by
  have h := Real.log_lt_log (by norm_num : (0 : Real) < 47)
    (by norm_num : (47 : Real) < 48)
  rw [show (48 : Real) = 2 ^ (4 : Nat) * 3 by norm_num,
    Real.log_mul, Real.log_pow] at h
  · nlinarith [LogTables.log_2_lt, LogTables.log_3_lt]
  all_goals positivity

theorem psi_sub_theta_nat_2400_lt_sixtythree :
    Chebyshev.psi (2400 : Real) - Chebyshev.theta 2400 < 63 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 2400
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 2400
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 2401,
      ↑(Nat.log p 2400) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 2401, Real.log ↑p < 63
  have hp : Nat.primesBelow 2401 =
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
        2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239,
        2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309,
        2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381,
        2383, 2389, 2393, 2399} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt,
    ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
    ElementaryLogBounds.log_17_lt, ElementaryLogBounds.log_19_lt,
    ElementaryLogBounds.log_23_lt, ElementaryLogBounds.log_29_lt,
    log_31_lt_three_point_four_seven, log_37_lt_three_point_seven,
    log_41_lt_three_point_eight, log_43_lt_three_point_nine,
    log_47_lt_three_point_eight_eight]

theorem dusart_lemma_3_3_at_2401 :
    Chebyshev.psi (2401 : Real) - Chebyshev.theta 2401 -
        Chebyshev.theta (49 : Real) <
      (1777745 : Real) / 1000000 * (2401 : Real) ^ (1 / (3 : Real)) := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 2401
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 2401
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  norm_num [Nat.log, Nat.log.go]
  interval_decide

def dusartLemma33FiniteRow_twothousandtwohundrednine_twothousandfourhundred :
    DusartLemma33FiniteRow := by
  have htheta_fortyseven := Chebyshev.theta_eq_sum_primesLE_log 47
  have hp47 : Nat.primesLE 47 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} := by decide
  rw [hp47] at htheta_fortyseven
  norm_num [Nat.log, Nat.log.go] at htheta_fortyseven
  have hlog42_le47 : Real.log 42 ≤ Real.log 47 :=
    Real.log_le_log (by norm_num) (by norm_num)
  apply dusartLemma33FiniteRow_of_endpoint_bounds 2209 2400 47
    (63 : Real) 40 13
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_2400_lt_sixtythree
  · nlinarith [htheta_fortyseven, hlog42_le47,
      LogTables.log_30_gt, Real.log_two_gt_d9, Real.log_three_gt_d9,
      Real.log_five_gt_d9, LogTables.log_7_gt]
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

def dusartLemma33FiniteRow_exact_twofourzeroone : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_integer_endpoint 2401 dusart_lemma_3_3_at_2401

theorem psi_sub_theta_nat_2047_lt_fiftysix :
    Chebyshev.psi (2047 : Real) - Chebyshev.theta 2047 < 56 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 2047
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 2047
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 2048,
      ↑(Nat.log p 2047) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 2048, Real.log ↑p < 56
  have hp : Nat.primesBelow 2048 =
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
        2003, 2011, 2017, 2027, 2029, 2039} := by
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

def dusartLemma33FiniteRow_eighteenfortynine_twothousandfortyseven :
    DusartLemma33FiniteRow := by
  have htheta_fortythree := Chebyshev.theta_eq_sum_primesLE_log 43
  have hp43 : Nat.primesLE 43 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43} := by decide
  rw [hp43] at htheta_fortythree
  norm_num [Nat.log, Nat.log.go] at htheta_fortythree
  apply dusartLemma33FiniteRow_of_endpoint_bounds 1849 2047 43
    (56 : Real) 36 (61 / 5)
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_2047_lt_fiftysix
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
    have hbase : ((61 / 5 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (61 / 5 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (61 / 5 : Real) = ((61 / 5 : Real) ^ (3 : Nat)) ^
          (1 / 3 : Real) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

theorem psi_sub_theta_nat_1848_lt_fiftytwo :
    Chebyshev.psi (1848 : Real) - Chebyshev.theta 1848 < 52 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 1848
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 1848
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 1849,
      ↑(Nat.log p 1848) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 1849, Real.log ↑p < 52
  have hp : Nat.primesBelow 1849 =
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
        1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt,
    ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
    ElementaryLogBounds.log_17_lt, ElementaryLogBounds.log_19_lt,
    ElementaryLogBounds.log_23_lt, ElementaryLogBounds.log_29_lt,
    log_31_lt_three_point_four_seven, log_37_lt_three_point_seven,
    log_41_lt_three_point_eight]

def dusartLemma33FiniteRow_sixteeneighty_one_eighteenfortyeight :
    DusartLemma33FiniteRow := by
  have htheta_fortyone := Chebyshev.theta_eq_sum_primesLE_log 41
  have hp41 : Nat.primesLE 41 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41} := by decide
  rw [hp41] at htheta_fortyone
  norm_num [Nat.log, Nat.log.go] at htheta_fortyone
  apply dusartLemma33FiniteRow_of_endpoint_bounds 1681 1848 41
    (52 : Real) 32 (59 / 5)
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_1848_lt_fiftytwo
  · have hlog29_le31 : Real.log 29 ≤ Real.log 31 :=
      Real.log_le_log (by norm_num) (by norm_num)
    have hlog29_le37 : Real.log 29 ≤ Real.log 37 :=
      Real.log_le_log (by norm_num) (by norm_num)
    have hlog29_le41 : Real.log 29 ≤ Real.log 41 :=
      Real.log_le_log (by norm_num) (by norm_num)
    nlinarith [htheta_fortyone, Real.log_two_gt_d9,
      Real.log_three_gt_d9, Real.log_five_gt_d9, LogTables.log_7_gt,
      LogTables.log_11_gt, LogTables.log_13_gt, LogTables.log_17_gt,
      LogTables.log_19_gt, LogTables.log_23_gt, LogTables.log_29_gt,
      hlog29_le31, hlog29_le37, hlog29_le41]
  · intro x hx hleft
    have hbase : ((59 / 5 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (59 / 5 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (59 / 5 : Real) = ((59 / 5 : Real) ^ (3 : Nat)) ^
          (1 / 3 : Real) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

theorem psi_sub_theta_nat_1680_lt_fortyeight :
    Chebyshev.psi (1680 : Real) - Chebyshev.theta 1680 < 48 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 1680
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 1680
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 1681,
      ↑(Nat.log p 1680) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 1681, Real.log ↑p < 48
  have hp : Nat.primesBelow 1681 =
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
        1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt,
    ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
    ElementaryLogBounds.log_17_lt, ElementaryLogBounds.log_19_lt,
    ElementaryLogBounds.log_23_lt, ElementaryLogBounds.log_29_lt,
    log_31_lt_three_point_four_seven, log_37_lt_three_point_seven]

def dusartLemma33FiniteRow_thirteenhundredsixtynine_sixteeneighty :
    DusartLemma33FiniteRow := by
  have htheta_thirtyseven := Chebyshev.theta_eq_sum_primesLE_log 37
  have hp37 : Nat.primesLE 37 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37} := by decide
  rw [hp37] at htheta_thirtyseven
  norm_num [Nat.log, Nat.log.go] at htheta_thirtyseven
  apply dusartLemma33FiniteRow_of_endpoint_bounds 1369 1680 37
    (48 : Real) 29 (111 / 10)
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_1680_lt_fortyeight
  · have hlog29_le31 : Real.log 29 ≤ Real.log 31 :=
      Real.log_le_log (by norm_num) (by norm_num)
    have hlog29_le37 : Real.log 29 ≤ Real.log 37 :=
      Real.log_le_log (by norm_num) (by norm_num)
    nlinarith [htheta_thirtyseven, Real.log_two_gt_d9,
      Real.log_three_gt_d9, Real.log_five_gt_d9, LogTables.log_7_gt,
      LogTables.log_11_gt, LogTables.log_13_gt, LogTables.log_17_gt,
      LogTables.log_19_gt, LogTables.log_23_gt, LogTables.log_29_gt,
      hlog29_le31, hlog29_le37]
  · intro x hx hleft
    have hbase : ((111 / 10 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (111 / 10 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (111 / 10 : Real) = ((111 / 10 : Real) ^ (3 : Nat)) ^
          (1 / 3 : Real) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

theorem psi_sub_theta_nat_1368_lt_fortythree_point_seven :
    Chebyshev.psi (1368 : Real) - Chebyshev.theta 1368 < (437 : Real) / 10 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 1368
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 1368
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 1369,
      ↑(Nat.log p 1368) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 1369, Real.log ↑p < (437 : Real) / 10
  have hp : Nat.primesBelow 1369 =
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
        1307, 1319, 1321, 1327, 1361, 1367} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt,
    ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
    ElementaryLogBounds.log_17_lt, ElementaryLogBounds.log_19_lt,
    ElementaryLogBounds.log_23_lt, ElementaryLogBounds.log_29_lt,
    log_31_lt_three_point_four_seven]

def dusartLemma33FiniteRow_tenthousandtwentyfour_thirteenhundredsixtyeight :
    DusartLemma33FiniteRow := by
  have htheta_thirtyone := Chebyshev.theta_eq_sum_primesLE_log 31
  have hp31 : Nat.primesLE 31 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by decide
  rw [hp31] at htheta_thirtyone
  norm_num [Nat.log, Nat.log.go] at htheta_thirtyone
  apply dusartLemma33FiniteRow_of_endpoint_bounds 1024 1368 32
    ((437 : Real) / 10) 26 10
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_1368_lt_fortythree_point_seven
  · have hlog29_le31 : Real.log 29 ≤ Real.log 31 :=
      Real.log_le_log (by norm_num) (by norm_num)
    nlinarith [htheta_thirtyone, Real.log_two_gt_d9,
      Real.log_three_gt_d9, Real.log_five_gt_d9, LogTables.log_7_gt,
      LogTables.log_11_gt, LogTables.log_13_gt, LogTables.log_17_gt,
      LogTables.log_19_gt, LogTables.log_23_gt, LogTables.log_29_gt,
      hlog29_le31]
  · intro x hx hleft
    have hbase : ((10 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (10 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (10 : Real) = ((10 : Real) ^ (3 : Nat)) ^ (1 / 3 : Real) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

theorem psi_sub_theta_nat_1023_lt_fortyone :
    Chebyshev.psi (1023 : Real) - Chebyshev.theta 1023 < 41 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 1023
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 1023
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 1024,
      ↑(Nat.log p 1023) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 1024, Real.log ↑p < 41
  have hp : Nat.primesBelow 1024 =
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
        967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt,
    ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
    ElementaryLogBounds.log_17_lt, ElementaryLogBounds.log_19_lt,
    ElementaryLogBounds.log_23_lt, ElementaryLogBounds.log_29_lt,
    log_31_lt_three_point_four_seven]

def dusartLemma33FiniteRow_ninehundredsixtyone_tenthousandtwentythree :
    DusartLemma33FiniteRow := by
  have htheta_thirtyone := Chebyshev.theta_eq_sum_primesLE_log 31
  have hp31 : Nat.primesLE 31 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by decide
  rw [hp31] at htheta_thirtyone
  norm_num [Nat.log, Nat.log.go] at htheta_thirtyone
  apply dusartLemma33FiniteRow_of_endpoint_bounds 961 1023 31
    (41 : Real) 24 (49 / 5)
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_1023_lt_fortyone
  · have hlog29_le31 : Real.log 29 ≤ Real.log 31 :=
      Real.log_le_log (by norm_num) (by norm_num)
    nlinarith [htheta_thirtyone, Real.log_two_gt_d9,
      Real.log_three_gt_d9, Real.log_five_gt_d9, LogTables.log_7_gt,
      LogTables.log_11_gt, LogTables.log_13_gt, LogTables.log_17_gt,
      LogTables.log_19_gt, LogTables.log_23_gt, LogTables.log_29_gt,
      hlog29_le31]
  · intro x hx hleft
    have hbase : ((49 / 5 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (49 / 5 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (49 / 5 : Real) = ((49 / 5 : Real) ^ (3 : Nat)) ^
          (1 / 3 : Real) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

theorem psi_sub_theta_nat_575_lt_thirty :
    Chebyshev.psi (575 : Real) - Chebyshev.theta 575 < 30 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 575
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 575
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 576,
      ↑(Nat.log p 575) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 576, Real.log ↑p < 30
  have hp : Nat.primesBelow 576 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
        127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
        191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
        257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
        331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397,
        401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
        467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
        563, 569, 571} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt,
    ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
    ElementaryLogBounds.log_17_lt, ElementaryLogBounds.log_19_lt,
    ElementaryLogBounds.log_23_lt]

def dusartLemma33FiniteRow_fivehundredtwentynine_fivehundredseventyfive :
    DusartLemma33FiniteRow := by
  have htheta_twentytwo := Chebyshev.theta_eq_sum_primesLE_log 22
  have hp22 : Nat.primesLE 22 = {2, 3, 5, 7, 11, 13, 17, 19} := by decide
  rw [hp22] at htheta_twentytwo
  norm_num [Nat.log, Nat.log.go] at htheta_twentytwo
  apply dusartLemma33FiniteRow_of_endpoint_bounds 529 575 23
    (30 : Real) 16 8
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_575_lt_thirty
  · have hmono : Chebyshev.theta (22 : Real) ≤ Chebyshev.theta 23 := by
      apply Chebyshev.theta_mono
      norm_num
    exact lt_of_lt_of_le (by
      nlinarith [htheta_twentytwo, Real.log_two_gt_d9,
        Real.log_three_gt_d9, Real.log_five_gt_d9, LogTables.log_7_gt]) hmono
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

def dusartLemma33FiniteRow_threehundredsixtyone_fivehundredeleven :
    DusartLemma33FiniteRow := by
  have htheta_nineteen := Chebyshev.theta_eq_sum_primesLE_log 19
  have hp19 : Nat.primesLE 19 = {2, 3, 5, 7, 11, 13, 17, 19} := by decide
  rw [hp19] at htheta_nineteen
  norm_num [Nat.log, Nat.log.go] at htheta_nineteen
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
  have hlog10_le19 : Real.log 10 ≤ Real.log 19 :=
    Real.log_le_log (by norm_num) (by norm_num)
  apply dusartLemma33FiniteRow_of_endpoint_bounds 361 511 19
    ((271 : Real) / 10) (29 / 2) (71 / 10)
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_511_lt_twentyseven_point_one
  · nlinarith [htheta_nineteen, hlog10, hlog10_le11, hlog10_le13,
      hlog10_le17, hlog10_le19, Real.log_two_gt_d9,
      Real.log_three_gt_d9, Real.log_five_gt_d9, LogTables.log_7_gt]
  · intro x hx hleft
    have hbase : ((71 / 10 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (71 / 10 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (71 / 10 : Real) = ((71 / 10 : Real) ^ (3 : Nat)) ^
          (1 / 3 : Real) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

theorem dusartLemma33FiniteRowsCover_fivehundredeleven :
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
        dusartLemma33FiniteRow_twohundredfiftysix_twohundredeightyeight,
        dusartLemma33FiniteRow_twohundredeightynine_threehundredfortytwo,
        dusartLemma33FiniteRow_threehundredfortythree_threehundredsixty] ++
        [dusartLemma33FiniteRow_threehundredsixtyone_fivehundredeleven]) 511 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_threesixty
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_fivehundredeight :
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
        dusartLemma33FiniteRow_twohundredfiftysix_twohundredeightyeight,
        dusartLemma33FiniteRow_twohundredeightynine_threehundredfortytwo,
        dusartLemma33FiniteRow_threehundredfortythree_threehundredsixty,
        dusartLemma33FiniteRow_threehundredsixtyone_fivehundredeleven] ++
        [dusartLemma33FiniteRow_fivehundredtwelve_fivehundredeight]) 528 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_fivehundredeleven
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_fivehundredseventyfive :
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
        dusartLemma33FiniteRow_twohundredfiftysix_twohundredeightyeight,
        dusartLemma33FiniteRow_twohundredeightynine_threehundredfortytwo,
        dusartLemma33FiniteRow_threehundredfortythree_threehundredsixty,
        dusartLemma33FiniteRow_threehundredsixtyone_fivehundredeleven,
        dusartLemma33FiniteRow_fivehundredtwelve_fivehundredeight] ++
        [dusartLemma33FiniteRow_fivehundredtwentynine_fivehundredseventyfive]) 575 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_fivehundredeight
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_sixhundredtwentyfour :
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
        dusartLemma33FiniteRow_twohundredfiftysix_twohundredeightyeight,
        dusartLemma33FiniteRow_twohundredeightynine_threehundredfortytwo,
        dusartLemma33FiniteRow_threehundredfortythree_threehundredsixty,
        dusartLemma33FiniteRow_threehundredsixtyone_fivehundredeleven,
        dusartLemma33FiniteRow_fivehundredtwelve_fivehundredeight,
        dusartLemma33FiniteRow_fivehundredtwentynine_fivehundredseventyfive] ++
        [dusartLemma33FiniteRow_fivehundredseventysix_sixhundredtwentyfour]) 624 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_fivehundredseventyfive
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_sixhundredseventyfive :
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
        dusartLemma33FiniteRow_twohundredfiftysix_twohundredeightyeight,
        dusartLemma33FiniteRow_twohundredeightynine_threehundredfortytwo,
        dusartLemma33FiniteRow_threehundredfortythree_threehundredsixty,
        dusartLemma33FiniteRow_threehundredsixtyone_fivehundredeleven,
        dusartLemma33FiniteRow_fivehundredtwelve_fivehundredeight,
        dusartLemma33FiniteRow_fivehundredtwentynine_fivehundredseventyfive,
        dusartLemma33FiniteRow_fivehundredseventysix_sixhundredtwentyfour] ++
        [dusartLemma33FiniteRow_sixhundredtwentyfive_sixhundredseventyfive]) 675 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_sixhundredtwentyfour
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_sevenhundredtwentyeight :
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
        dusartLemma33FiniteRow_twohundredfiftysix_twohundredeightyeight,
        dusartLemma33FiniteRow_twohundredeightynine_threehundredfortytwo,
        dusartLemma33FiniteRow_threehundredfortythree_threehundredsixty,
        dusartLemma33FiniteRow_threehundredsixtyone_fivehundredeleven,
        dusartLemma33FiniteRow_fivehundredtwelve_fivehundredeight,
        dusartLemma33FiniteRow_fivehundredtwentynine_fivehundredseventyfive,
        dusartLemma33FiniteRow_fivehundredseventysix_sixhundredtwentyfour,
        dusartLemma33FiniteRow_sixhundredtwentyfive_sixhundredseventyfive] ++
        [dusartLemma33FiniteRow_sixhundredseventysix_sevenhundredtwentyeight]) 728 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_sixhundredseventyfive
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_eighthundredforty :
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
        dusartLemma33FiniteRow_twohundredfiftysix_twohundredeightyeight,
        dusartLemma33FiniteRow_twohundredeightynine_threehundredfortytwo,
        dusartLemma33FiniteRow_threehundredfortythree_threehundredsixty,
        dusartLemma33FiniteRow_threehundredsixtyone_fivehundredeleven,
        dusartLemma33FiniteRow_fivehundredtwelve_fivehundredeight,
        dusartLemma33FiniteRow_fivehundredtwentynine_fivehundredseventyfive,
        dusartLemma33FiniteRow_fivehundredseventysix_sixhundredtwentyfour,
        dusartLemma33FiniteRow_sixhundredtwentyfive_sixhundredseventyfive,
        dusartLemma33FiniteRow_sixhundredseventysix_sevenhundredtwentyeight] ++
        [dusartLemma33FiniteRow_sevenhundredtwentynine_eighthundredforty]) 840 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_sevenhundredtwentyeight
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_ninehundredsixty :
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
        dusartLemma33FiniteRow_twohundredfiftysix_twohundredeightyeight,
        dusartLemma33FiniteRow_twohundredeightynine_threehundredfortytwo,
        dusartLemma33FiniteRow_threehundredfortythree_threehundredsixty,
        dusartLemma33FiniteRow_threehundredsixtyone_fivehundredeleven,
        dusartLemma33FiniteRow_fivehundredtwelve_fivehundredeight,
        dusartLemma33FiniteRow_fivehundredtwentynine_fivehundredseventyfive,
        dusartLemma33FiniteRow_fivehundredseventysix_sixhundredtwentyfour,
        dusartLemma33FiniteRow_sixhundredtwentyfive_sixhundredseventyfive,
        dusartLemma33FiniteRow_sixhundredseventysix_sevenhundredtwentyeight,
        dusartLemma33FiniteRow_sevenhundredtwentynine_eighthundredforty] ++
        [dusartLemma33FiniteRow_eighthundredfortyone_ninehundredsixty]) 960 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_eighthundredforty
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_tenthousandtwentythree :
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
        dusartLemma33FiniteRow_twohundredfiftysix_twohundredeightyeight,
        dusartLemma33FiniteRow_twohundredeightynine_threehundredfortytwo,
        dusartLemma33FiniteRow_threehundredfortythree_threehundredsixty,
        dusartLemma33FiniteRow_threehundredsixtyone_fivehundredeleven,
        dusartLemma33FiniteRow_fivehundredtwelve_fivehundredeight,
        dusartLemma33FiniteRow_fivehundredtwentynine_fivehundredseventyfive,
        dusartLemma33FiniteRow_fivehundredseventysix_sixhundredtwentyfour,
        dusartLemma33FiniteRow_sixhundredtwentyfive_sixhundredseventyfive,
        dusartLemma33FiniteRow_sixhundredseventysix_sevenhundredtwentyeight,
        dusartLemma33FiniteRow_sevenhundredtwentynine_eighthundredforty,
        dusartLemma33FiniteRow_eighthundredfortyone_ninehundredsixty] ++
        [dusartLemma33FiniteRow_ninehundredsixtyone_tenthousandtwentythree]) 1023 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_ninehundredsixty
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_thirteenhundredsixtyeight :
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
        dusartLemma33FiniteRow_twohundredfiftysix_twohundredeightyeight,
        dusartLemma33FiniteRow_twohundredeightynine_threehundredfortytwo,
        dusartLemma33FiniteRow_threehundredfortythree_threehundredsixty,
        dusartLemma33FiniteRow_threehundredsixtyone_fivehundredeleven,
        dusartLemma33FiniteRow_fivehundredtwelve_fivehundredeight,
        dusartLemma33FiniteRow_fivehundredtwentynine_fivehundredseventyfive,
        dusartLemma33FiniteRow_fivehundredseventysix_sixhundredtwentyfour,
        dusartLemma33FiniteRow_sixhundredtwentyfive_sixhundredseventyfive,
        dusartLemma33FiniteRow_sixhundredseventysix_sevenhundredtwentyeight,
        dusartLemma33FiniteRow_sevenhundredtwentynine_eighthundredforty,
        dusartLemma33FiniteRow_eighthundredfortyone_ninehundredsixty,
        dusartLemma33FiniteRow_ninehundredsixtyone_tenthousandtwentythree] ++
        [dusartLemma33FiniteRow_tenthousandtwentyfour_thirteenhundredsixtyeight]) 1368 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_tenthousandtwentythree
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_sixteeneighty :
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
        dusartLemma33FiniteRow_twohundredfiftysix_twohundredeightyeight,
        dusartLemma33FiniteRow_twohundredeightynine_threehundredfortytwo,
        dusartLemma33FiniteRow_threehundredfortythree_threehundredsixty,
        dusartLemma33FiniteRow_threehundredsixtyone_fivehundredeleven,
        dusartLemma33FiniteRow_fivehundredtwelve_fivehundredeight,
        dusartLemma33FiniteRow_fivehundredtwentynine_fivehundredseventyfive,
        dusartLemma33FiniteRow_fivehundredseventysix_sixhundredtwentyfour,
        dusartLemma33FiniteRow_sixhundredtwentyfive_sixhundredseventyfive,
        dusartLemma33FiniteRow_sixhundredseventysix_sevenhundredtwentyeight,
        dusartLemma33FiniteRow_sevenhundredtwentynine_eighthundredforty,
        dusartLemma33FiniteRow_eighthundredfortyone_ninehundredsixty,
        dusartLemma33FiniteRow_ninehundredsixtyone_tenthousandtwentythree,
        dusartLemma33FiniteRow_tenthousandtwentyfour_thirteenhundredsixtyeight] ++
        [dusartLemma33FiniteRow_thirteenhundredsixtynine_sixteeneighty]) 1680 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_thirteenhundredsixtyeight
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_eighteenfortyeight :
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
        dusartLemma33FiniteRow_twohundredfiftysix_twohundredeightyeight,
        dusartLemma33FiniteRow_twohundredeightynine_threehundredfortytwo,
        dusartLemma33FiniteRow_threehundredfortythree_threehundredsixty,
        dusartLemma33FiniteRow_threehundredsixtyone_fivehundredeleven,
        dusartLemma33FiniteRow_fivehundredtwelve_fivehundredeight,
        dusartLemma33FiniteRow_fivehundredtwentynine_fivehundredseventyfive,
        dusartLemma33FiniteRow_fivehundredseventysix_sixhundredtwentyfour,
        dusartLemma33FiniteRow_sixhundredtwentyfive_sixhundredseventyfive,
        dusartLemma33FiniteRow_sixhundredseventysix_sevenhundredtwentyeight,
        dusartLemma33FiniteRow_sevenhundredtwentynine_eighthundredforty,
        dusartLemma33FiniteRow_eighthundredfortyone_ninehundredsixty,
        dusartLemma33FiniteRow_ninehundredsixtyone_tenthousandtwentythree,
        dusartLemma33FiniteRow_tenthousandtwentyfour_thirteenhundredsixtyeight,
        dusartLemma33FiniteRow_thirteenhundredsixtynine_sixteeneighty] ++
        [dusartLemma33FiniteRow_sixteeneighty_one_eighteenfortyeight]) 1848 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_sixteeneighty
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_twothousandfortyseven :
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
        dusartLemma33FiniteRow_twohundredfiftysix_twohundredeightyeight,
        dusartLemma33FiniteRow_twohundredeightynine_threehundredfortytwo,
        dusartLemma33FiniteRow_threehundredfortythree_threehundredsixty,
        dusartLemma33FiniteRow_threehundredsixtyone_fivehundredeleven,
        dusartLemma33FiniteRow_fivehundredtwelve_fivehundredeight,
        dusartLemma33FiniteRow_fivehundredtwentynine_fivehundredseventyfive,
        dusartLemma33FiniteRow_fivehundredseventysix_sixhundredtwentyfour,
        dusartLemma33FiniteRow_sixhundredtwentyfive_sixhundredseventyfive,
        dusartLemma33FiniteRow_sixhundredseventysix_sevenhundredtwentyeight,
        dusartLemma33FiniteRow_sevenhundredtwentynine_eighthundredforty,
        dusartLemma33FiniteRow_eighthundredfortyone_ninehundredsixty,
        dusartLemma33FiniteRow_ninehundredsixtyone_tenthousandtwentythree,
        dusartLemma33FiniteRow_tenthousandtwentyfour_thirteenhundredsixtyeight,
        dusartLemma33FiniteRow_thirteenhundredsixtynine_sixteeneighty,
        dusartLemma33FiniteRow_sixteeneighty_one_eighteenfortyeight] ++
        [dusartLemma33FiniteRow_eighteenfortynine_twothousandfortyseven]) 2047 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_eighteenfortyeight
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_twothousandonehundredninetysix :
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
        dusartLemma33FiniteRow_twohundredfiftysix_twohundredeightyeight,
        dusartLemma33FiniteRow_twohundredeightynine_threehundredfortytwo,
        dusartLemma33FiniteRow_threehundredfortythree_threehundredsixty,
        dusartLemma33FiniteRow_threehundredsixtyone_fivehundredeleven,
        dusartLemma33FiniteRow_fivehundredtwelve_fivehundredeight,
        dusartLemma33FiniteRow_fivehundredtwentynine_fivehundredseventyfive,
        dusartLemma33FiniteRow_fivehundredseventysix_sixhundredtwentyfour,
        dusartLemma33FiniteRow_sixhundredtwentyfive_sixhundredseventyfive,
        dusartLemma33FiniteRow_sixhundredseventysix_sevenhundredtwentyeight,
        dusartLemma33FiniteRow_sevenhundredtwentynine_eighthundredforty,
        dusartLemma33FiniteRow_eighthundredfortyone_ninehundredsixty,
        dusartLemma33FiniteRow_ninehundredsixtyone_tenthousandtwentythree,
        dusartLemma33FiniteRow_tenthousandtwentyfour_thirteenhundredsixtyeight,
        dusartLemma33FiniteRow_thirteenhundredsixtynine_sixteeneighty,
        dusartLemma33FiniteRow_sixteeneighty_one_eighteenfortyeight,
        dusartLemma33FiniteRow_eighteenfortynine_twothousandfortyseven] ++
        [dusartLemma33FiniteRow_twothousandtwentyfive_twothousandonehundredninetysix]) 2196 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_twothousandfortyseven
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_twothousandtwohundredeight :
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
        dusartLemma33FiniteRow_twohundredfiftysix_twohundredeightyeight,
        dusartLemma33FiniteRow_twohundredeightynine_threehundredfortytwo,
        dusartLemma33FiniteRow_threehundredfortythree_threehundredsixty,
        dusartLemma33FiniteRow_threehundredsixtyone_fivehundredeleven,
        dusartLemma33FiniteRow_fivehundredtwelve_fivehundredeight,
        dusartLemma33FiniteRow_fivehundredtwentynine_fivehundredseventyfive,
        dusartLemma33FiniteRow_fivehundredseventysix_sixhundredtwentyfour,
        dusartLemma33FiniteRow_sixhundredtwentyfive_sixhundredseventyfive,
        dusartLemma33FiniteRow_sixhundredseventysix_sevenhundredtwentyeight,
        dusartLemma33FiniteRow_sevenhundredtwentynine_eighthundredforty,
        dusartLemma33FiniteRow_eighthundredfortyone_ninehundredsixty,
        dusartLemma33FiniteRow_ninehundredsixtyone_tenthousandtwentythree,
        dusartLemma33FiniteRow_tenthousandtwentyfour_thirteenhundredsixtyeight,
        dusartLemma33FiniteRow_thirteenhundredsixtynine_sixteeneighty,
        dusartLemma33FiniteRow_sixteeneighty_one_eighteenfortyeight,
        dusartLemma33FiniteRow_eighteenfortynine_twothousandfortyseven,
        dusartLemma33FiniteRow_twothousandtwentyfive_twothousandonehundredninetysix] ++
        [dusartLemma33FiniteRow_twothousandonehundredninetyseven_twothousandtwohundredeight]) 2208 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_twothousandonehundredninetysix
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_twothousandfourhundred :
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
        dusartLemma33FiniteRow_twohundredfiftysix_twohundredeightyeight,
        dusartLemma33FiniteRow_twohundredeightynine_threehundredfortytwo,
        dusartLemma33FiniteRow_threehundredfortythree_threehundredsixty,
        dusartLemma33FiniteRow_threehundredsixtyone_fivehundredeleven,
        dusartLemma33FiniteRow_fivehundredtwelve_fivehundredeight,
        dusartLemma33FiniteRow_fivehundredtwentynine_fivehundredseventyfive,
        dusartLemma33FiniteRow_fivehundredseventysix_sixhundredtwentyfour,
        dusartLemma33FiniteRow_sixhundredtwentyfive_sixhundredseventyfive,
        dusartLemma33FiniteRow_sixhundredseventysix_sevenhundredtwentyeight,
        dusartLemma33FiniteRow_sevenhundredtwentynine_eighthundredforty,
        dusartLemma33FiniteRow_eighthundredfortyone_ninehundredsixty,
        dusartLemma33FiniteRow_ninehundredsixtyone_tenthousandtwentythree,
        dusartLemma33FiniteRow_tenthousandtwentyfour_thirteenhundredsixtyeight,
        dusartLemma33FiniteRow_thirteenhundredsixtynine_sixteeneighty,
        dusartLemma33FiniteRow_sixteeneighty_one_eighteenfortyeight,
        dusartLemma33FiniteRow_eighteenfortynine_twothousandfortyseven,
        dusartLemma33FiniteRow_twothousandtwentyfive_twothousandonehundredninetysix,
        dusartLemma33FiniteRow_twothousandonehundredninetyseven_twothousandtwohundredeight] ++
        [dusartLemma33FiniteRow_twothousandtwohundrednine_twothousandfourhundred]) 2400 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_twothousandtwohundredeight
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_twofourzeroone :
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
        dusartLemma33FiniteRow_twohundredfiftysix_twohundredeightyeight,
        dusartLemma33FiniteRow_twohundredeightynine_threehundredfortytwo,
        dusartLemma33FiniteRow_threehundredfortythree_threehundredsixty,
        dusartLemma33FiniteRow_threehundredsixtyone_fivehundredeleven,
        dusartLemma33FiniteRow_fivehundredtwelve_fivehundredeight,
        dusartLemma33FiniteRow_fivehundredtwentynine_fivehundredseventyfive,
        dusartLemma33FiniteRow_fivehundredseventysix_sixhundredtwentyfour,
        dusartLemma33FiniteRow_sixhundredtwentyfive_sixhundredseventyfive,
        dusartLemma33FiniteRow_sixhundredseventysix_sevenhundredtwentyeight,
        dusartLemma33FiniteRow_sevenhundredtwentynine_eighthundredforty,
        dusartLemma33FiniteRow_eighthundredfortyone_ninehundredsixty,
        dusartLemma33FiniteRow_ninehundredsixtyone_tenthousandtwentythree,
        dusartLemma33FiniteRow_tenthousandtwentyfour_thirteenhundredsixtyeight,
        dusartLemma33FiniteRow_thirteenhundredsixtynine_sixteeneighty,
        dusartLemma33FiniteRow_sixteeneighty_one_eighteenfortyeight,
        dusartLemma33FiniteRow_eighteenfortynine_twothousandfortyseven,
        dusartLemma33FiniteRow_twothousandtwentyfive_twothousandonehundredninetysix,
        dusartLemma33FiniteRow_twothousandonehundredninetyseven_twothousandtwohundredeight,
        dusartLemma33FiniteRow_twothousandtwohundrednine_twothousandfourhundred] ++
        [dusartLemma33FiniteRow_exact_twofourzeroone]) 2401 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_twothousandfourhundred
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusart_lemma_3_3_finite_120 :
    ∀ x : Real, 0 < x → x ≤ 120 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_onetwenty_compact

theorem dusart_lemma_3_3_finite_255 :
    ∀ x : Real, 0 < x → x ≤ 255 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_twohundredfiftyfive

theorem dusart_lemma_3_3_finite_288 :
    ∀ x : Real, 0 < x → x ≤ 288 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_twohundredeightyeight

theorem dusart_lemma_3_3_finite_360 :
    ∀ x : Real, 0 < x → x ≤ 360 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_threesixty

theorem dusart_lemma_3_3_finite_511 :
    ∀ x : Real, 0 < x → x ≤ 511 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_fivehundredeleven

theorem dusart_lemma_3_3_finite_624 :
    ∀ x : Real, 0 < x → x ≤ 624 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_sixhundredtwentyfour

theorem dusart_lemma_3_3_finite_675 :
    ∀ x : Real, 0 < x → x ≤ 675 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_sixhundredseventyfive

theorem dusart_lemma_3_3_finite_728 :
    ∀ x : Real, 0 < x → x ≤ 728 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_sevenhundredtwentyeight

theorem dusart_lemma_3_3_finite_840 :
    ∀ x : Real, 0 < x → x ≤ 840 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_eighthundredforty

theorem dusart_lemma_3_3_finite_960 :
    ∀ x : Real, 0 < x → x ≤ 960 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_ninehundredsixty

theorem dusart_lemma_3_3_finite_1023 :
    ∀ x : Real, 0 < x → x ≤ 1023 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_tenthousandtwentythree

theorem dusart_lemma_3_3_finite_1368 :
    ∀ x : Real, 0 < x → x ≤ 1368 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_thirteenhundredsixtyeight

theorem dusart_lemma_3_3_finite_1680 :
    ∀ x : Real, 0 < x → x ≤ 1680 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_sixteeneighty

theorem dusart_lemma_3_3_finite_1848 :
    ∀ x : Real, 0 < x → x ≤ 1848 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_eighteenfortyeight

theorem dusart_lemma_3_3_finite_2047 :
    ∀ x : Real, 0 < x → x ≤ 2047 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_twothousandfortyseven

theorem dusart_lemma_3_3_finite_2196 :
    ∀ x : Real, 0 < x → x ≤ 2196 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_twothousandonehundredninetysix

theorem dusart_lemma_3_3_finite_2208 :
    ∀ x : Real, 0 < x → x ≤ 2208 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_twothousandtwohundredeight

theorem dusart_lemma_3_3_finite_2400 :
    ∀ x : Real, 0 < x → x ≤ 2400 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_twothousandfourhundred

theorem dusart_lemma_3_3_finite_2401 :
    ∀ x : Real, 0 < x → x ≤ 2401 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_rows
    dusartLemma33FiniteRowsCover_twofourzeroone

theorem dusart_proposition_3_2_small_64
    {x : Real} (hx : 0 < x) (hx64 : x < 64) :
    Chebyshev.psi x - Chebyshev.theta x <
      (100007 : Real) / 100000 * Real.sqrt x +
        (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  have htransport : Chebyshev.psi x - Chebyshev.theta x =
      Chebyshev.psi (⌊x⌋₊ : Real) - Chebyshev.theta (⌊x⌋₊ : Real) := by
    rw [Chebyshev.psi_eq_psi_coe_floor, Chebyshev.theta_eq_theta_coe_floor]
  by_cases h9 : x < 9
  · by_cases h4 : x < 4
    · have hzero : Chebyshev.psi x - Chebyshev.theta x = 0 := by
        have hf : ⌊x⌋₊ < 4 := (Nat.floor_lt hx.le).2 h4
        have hfloor : (⌊x⌋₊ : Real) ≤ 3 := by
          exact_mod_cast Nat.le_of_lt_succ hf
        have hupper : Chebyshev.psi x - Chebyshev.theta x ≤ 0 := by
          rw [htransport]
          exact (psi_sub_theta_mono hfloor).trans_eq
            psi_sub_theta_nat_3_eq_zero
        have hnonneg : 0 ≤ Chebyshev.psi x - Chebyshev.theta x := by
          exact sub_nonneg.mpr (Chebyshev.theta_le_psi x)
        exact le_antisymm hupper hnonneg
      rw [hzero]
      positivity
    · have hx4 : (4 : Real) ≤ x := le_of_not_gt h4
      have hfloor : (⌊x⌋₊ : Real) ≤ 8 := by
        exact_mod_cast Nat.le_of_lt_succ
          ((Nat.floor_lt hx.le).2 (by norm_num; exact h9))
      have hleft : Chebyshev.psi x - Chebyshev.theta x < 2 := by
        rw [htransport]
        exact (psi_sub_theta_mono hfloor).trans_lt psi_sub_theta_nat_8_lt_two
      have hsqrt : (2 : Real) ≤ Real.sqrt x := by
        nlinarith [Real.sq_sqrt (show 0 ≤ x by linarith), Real.sqrt_nonneg x]
      nlinarith [hleft, hsqrt,
        Real.rpow_nonneg (show 0 ≤ x by linarith) (1 / 3 : Real)]
  · have hx9 : (9 : Real) ≤ x := le_of_not_gt h9
    by_cases h25 : x < 25
    · have hfloor : (⌊x⌋₊ : Real) ≤ 24 := by
        exact_mod_cast Nat.le_of_lt_succ
          ((Nat.floor_lt hx.le).2 (by norm_num; exact h25))
      have hleft : Chebyshev.psi x - Chebyshev.theta x < 4 := by
        rw [htransport]
        exact (psi_sub_theta_mono hfloor).trans_lt psi_sub_theta_nat_24_lt_four
      have hsqrt : (3 : Real) ≤ Real.sqrt x := by
        nlinarith [Real.sq_sqrt (show 0 ≤ x by linarith), Real.sqrt_nonneg x]
      have hcuberoot : (2 : Real) ≤ x ^ (1 / 3 : Real) := by
        have hpow := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 8)
          (by linarith : (8 : Real) ≤ x)
          (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
        norm_num at hpow ⊢
        exact hpow
      nlinarith [hleft, hsqrt, hcuberoot]
    · have hx25 : (25 : Real) ≤ x := le_of_not_gt h25
      by_cases h36 : x < 36
      · have hfloor : (⌊x⌋₊ : Real) ≤ 35 := by
          exact_mod_cast Nat.le_of_lt_succ
            ((Nat.floor_lt hx.le).2 (by norm_num; exact h36))
        have hleft : Chebyshev.psi x - Chebyshev.theta x < 8 := by
          rw [htransport]
          exact (psi_sub_theta_mono hfloor).trans_lt psi_sub_theta_nat_35_lt_eight
        have hsqrt : (5 : Real) ≤ Real.sqrt x := by
          nlinarith [Real.sq_sqrt (show 0 ≤ x by linarith), Real.sqrt_nonneg x]
        have hcuberoot : (2 : Real) ≤ x ^ (1 / 3 : Real) := by
          have hpow := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 8)
            (by linarith : (8 : Real) ≤ x)
            (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
          norm_num at hpow ⊢
          exact hpow
        nlinarith [hleft, hsqrt, hcuberoot]
      · have hx36 : (36 : Real) ≤ x := le_of_not_gt h36
        have hfloor : (⌊x⌋₊ : Real) ≤ 63 := by
          exact_mod_cast Nat.le_of_lt_succ
            ((Nat.floor_lt hx.le).2 (by norm_num; exact hx64))
        have hleft : Chebyshev.psi x - Chebyshev.theta x < 9 := by
          rw [htransport]
          exact (psi_sub_theta_mono hfloor).trans_lt psi_sub_theta_nat_63_lt_nine
        have hsqrt : (6 : Real) ≤ Real.sqrt x := by
          nlinarith [Real.sq_sqrt (show 0 ≤ x by linarith), Real.sqrt_nonneg x]
        have hcuberoot : (2 : Real) ≤ x ^ (1 / 3 : Real) := by
          have hpow := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 8)
            (by linarith : (8 : Real) ≤ x)
            (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
          norm_num at hpow ⊢
          exact hpow
        nlinarith [hleft, hsqrt, hcuberoot]

theorem exp_twentyEight_lt_dusart_endpoint :
    Real.exp 28 < (1446257067000 : Real) := by
  rw [show (28 : Real) = (28 : Nat) * 1 by norm_num,
    Real.exp_nat_mul]
  have hpow : (Real.exp 1) ^ (28 : Nat) <
      (2.7182818286 : Real) ^ (28 : Nat) := by
    exact pow_lt_pow_left₀ Real.exp_one_lt_d9
      (Real.exp_pos 1).le (by norm_num)
  have hnum : (2.7182818286 : Real) ^ (28 : Nat) <
      (1446257067000 : Real) := by norm_num
  exact hpow.trans hnum

/-! The numerical tail step used in Dusart's theta estimate. -/
theorem theta_le_one_plus_dusart_error_of_psi_upper_and_gap
    {x : Real}
    (hpsi : Chebyshev.psi x ≤ (100002841 : Real) / 100000000 * x)
    (hgap : (9999 : Real) / 10000 * Real.sqrt x ≤
      Chebyshev.psi x - Chebyshev.theta x) :
    Chebyshev.theta x ≤
      (100002841 : Real) / 100000000 * x -
        (9999 : Real) / 10000 * Real.sqrt x := by
  linarith

theorem dusart_gap_from_theta_root_lower
    {x : Real} (hx : 2 ≤ x)
    (hroot : (9999 : Real) / 10000 * Real.sqrt x ≤
      Chebyshev.theta (x ^ (1 / 2 : Real))) :
    (9999 : Real) / 10000 * Real.sqrt x ≤
      Chebyshev.psi x - Chebyshev.theta x := by
  have hdecomp := psi_sub_theta_ge_theta_sqrt hx
  have hroot' : (9999 : Real) / 10000 * x ^ (1 / 2 : Real) ≤
      Chebyshev.theta (x ^ (1 / 2 : Real)) := by
    simpa only [Real.sqrt_eq_rpow] using hroot
  simpa only [Real.sqrt_eq_rpow] using hroot'.trans hdecomp

theorem theta_lower_9999_of_logFourth_error_at_large
    {y : Real} (hy : (4e18 : Real) ≤ y)
    (herror : |Chebyshev.theta y - y| ≤
      (648 : Real) / 1000 * y / (Real.log y) ^ 4) :
    (9999 : Real) / 10000 * y ≤ Chebyshev.theta y := by
  have hy_pos : 0 < y := by linarith
  have hlog : (42 : Real) ≤ Real.log y := by
    exact forty_two_lt_log_four_e18.le.trans
      (Real.log_le_log (by norm_num) hy)
  have hlog_pos : 0 < Real.log y := by linarith
  have hpow : (42 : Real) ^ (4 : Nat) ≤ (Real.log y) ^ (4 : Nat) := by
    exact pow_le_pow_left₀ (by norm_num) hlog 4
  have hscaled : y / (Real.log y) ^ 4 ≤ y / (42 : Real) ^ 4 := by
    exact div_le_div_of_nonneg_left hy_pos.le (by positivity) hpow
  have hscaled' : (648 : Real) / 1000 * y / (Real.log y) ^ 4 ≤
      (648 : Real) / 1000 * y / (42 : Real) ^ 4 := by
    calc
      (648 : Real) / 1000 * y / (Real.log y) ^ 4 =
          (648 : Real) / 1000 * (y / (Real.log y) ^ 4) := by ring
      _ ≤ (648 : Real) / 1000 * (y / (42 : Real) ^ 4) :=
        mul_le_mul_of_nonneg_left hscaled (by norm_num)
      _ = (648 : Real) / 1000 * y / (42 : Real) ^ 4 := by ring
  have hlow := (abs_le.mp herror).1
  nlinarith [hscaled']

theorem theta_lower_9999_of_strict_logFourth_error_at_large
    {y : Real} (hy : (4e18 : Real) ≤ y)
    (herror : |Chebyshev.theta y - y| <
      (648 : Real) / 1000 * y / (Real.log y) ^ 4) :
    (9999 : Real) / 10000 * y < Chebyshev.theta y := by
  have hy_pos : 0 < y := by linarith
  have hlog : (42 : Real) ≤ Real.log y := by
    exact forty_two_lt_log_four_e18.le.trans
      (Real.log_le_log (by norm_num) hy)
  have hlog_pos : 0 < Real.log y := by linarith
  have hpow : (42 : Real) ^ (4 : Nat) ≤ (Real.log y) ^ (4 : Nat) := by
    exact pow_le_pow_left₀ (by norm_num) hlog 4
  have hscaled : y / (Real.log y) ^ 4 ≤ y / (42 : Real) ^ 4 := by
    exact div_le_div_of_nonneg_left hy_pos.le (by positivity) hpow
  have hscaled' : (648 : Real) / 1000 * y / (Real.log y) ^ 4 ≤
      (648 : Real) / 1000 * y / (42 : Real) ^ 4 := by
    calc
      (648 : Real) / 1000 * y / (Real.log y) ^ 4 =
          (648 : Real) / 1000 * (y / (Real.log y) ^ 4) := by ring
      _ ≤ (648 : Real) / 1000 * (y / (42 : Real) ^ 4) :=
        mul_le_mul_of_nonneg_left hscaled (by norm_num)
      _ = (648 : Real) / 1000 * y / (42 : Real) ^ 4 := by ring
  have hlow := (abs_lt.mp herror).1
  nlinarith [hscaled']

theorem dusart_gap_from_strict_theta_root_lower
    {x : Real} (hx : 2 ≤ x)
    (hroot : (9999 : Real) / 10000 * Real.sqrt x <
      Chebyshev.theta (x ^ (1 / 2 : Real))) :
    (9999 : Real) / 10000 * Real.sqrt x <
      Chebyshev.psi x - Chebyshev.theta x := by
  have hdecomp := psi_sub_theta_ge_theta_sqrt hx
  have hroot' : (9999 : Real) / 10000 * x ^ (1 / 2 : Real) <
      Chebyshev.theta (x ^ (1 / 2 : Real)) := by
    simpa only [Real.sqrt_eq_rpow] using hroot
  have hgap' : (9999 : Real) / 10000 * x ^ (1 / 2 : Real) <
      Chebyshev.psi x - Chebyshev.theta x :=
    hroot'.trans_le hdecomp
  simpa only [Real.sqrt_eq_rpow] using hgap'

theorem psi_sub_theta_ge_9999_sqrt_of_large_theta_error
    {x : Real} (hx : (4e18 : Real) ^ 2 ≤ x)
    (herror : ∀ y : Real, (4e18 : Real) ≤ y →
      |Chebyshev.theta y - y| ≤
        (648 : Real) / 1000 * y / (Real.log y) ^ 4) :
    (9999 : Real) / 10000 * Real.sqrt x ≤
      Chebyshev.psi x - Chebyshev.theta x := by
  have hx_pos : 0 < x := by
    have hcut : (0 : Real) < (4e18 : Real) ^ 2 := by positivity
    linarith
  have hroot_cut : (4e18 : Real) ≤ Real.sqrt x := by
    apply (Real.le_sqrt' (by positivity : (0 : Real) < (4e18 : Real))).2
    nlinarith
  have hroot := theta_lower_9999_of_logFourth_error_at_large
    hroot_cut (herror (Real.sqrt x) hroot_cut)
  have hroot' : (9999 : Real) / 10000 * Real.sqrt x ≤
      Chebyshev.theta (x ^ (1 / 2 : Real)) := by
    simpa only [Real.sqrt_eq_rpow] using hroot
  exact dusart_gap_from_theta_root_lower (by linarith) hroot'

theorem psi_sub_theta_gt_9999_sqrt_of_large_strict_theta_error
    {x : Real} (hx : (4e18 : Real) ^ 2 ≤ x)
    (herror : ∀ y : Real, (4e18 : Real) ≤ y →
      |Chebyshev.theta y - y| <
        (648 : Real) / 1000 * y / (Real.log y) ^ 4) :
    (9999 : Real) / 10000 * Real.sqrt x <
      Chebyshev.psi x - Chebyshev.theta x := by
  have hx_pos : 0 < x := by
    have hcut : (0 : Real) < (4e18 : Real) ^ 2 := by positivity
    linarith
  have hroot_cut : (4e18 : Real) ≤ Real.sqrt x := by
    apply (Real.le_sqrt' (by positivity : (0 : Real) < (4e18 : Real))).2
    nlinarith
  have hroot := theta_lower_9999_of_strict_logFourth_error_at_large
    hroot_cut (herror (Real.sqrt x) hroot_cut)
  have hroot' : (9999 : Real) / 10000 * Real.sqrt x <
      Chebyshev.theta (x ^ (1 / 2 : Real)) := by
    simpa only [Real.sqrt_eq_rpow] using hroot
  exact dusart_gap_from_strict_theta_root_lower (by linarith) hroot'

/-! Global form of Dusart's Proposition 3.1.  The finite interval ending at
the square of the explicit theta cutoff is kept as a separate input; above it
the square-root substitution and the theta error prove the estimate directly. -/
theorem dusart_proposition_3_1_of_finite_and_strict_theta_error
    (finite : ∀ x : Real, (121 : Real) < x →
      x < (4e18 : Real) ^ 2 →
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x)
    (herror : ∀ y : Real, (4e18 : Real) ≤ y →
      |Chebyshev.theta y - y| <
        (648 : Real) / 1000 * y / (Real.log y) ^ 4) :
    ∀ x : Real, (121 : Real) < x →
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x := by
  intro x hx
  by_cases hlarge : (4e18 : Real) ^ 2 ≤ x
  · exact psi_sub_theta_gt_9999_sqrt_of_large_strict_theta_error
      hlarge herror
  · exact finite x hx (lt_of_not_ge hlarge)

/-! The same Proposition 3.1 split in the exact tail interface used by the
provider modules. -/
theorem dusart_proposition_3_1_of_finite_and_thetaErrorAbove
    (finite : ∀ x : Real, (121 : Real) < x →
      x < (4e18 : Real) ^ 2 →
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x)
    (thetaError : HasThetaLogFourthErrorAbove
      (648 / 1000 : Real) (4e18 : Real)) :
    ∀ x : Real, (121 : Real) < x →
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x := by
  apply dusart_proposition_3_1_of_finite_and_strict_theta_error finite
  intro y hy
  exact thetaError y hy

theorem psi_sub_theta_le_of_root_bound
    {x c : Real} (hx : 0 ≤ x) (hc : 0 ≤ c)
    (hroot : ∀ y : Real, 0 ≤ y → Chebyshev.psi y ≤ c * y) :
    Chebyshev.psi x - Chebyshev.theta x ≤
      c * (x ^ (1 / 2 : Real) + x ^ (1 / 3 : Real) +
        x ^ (1 / 5 : Real)) := by
  have hdecomp := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have h2 := hroot (x ^ (2 : Real)⁻¹) (by positivity)
  have h3 := hroot (x ^ (3 : Real)⁻¹) (by positivity)
  have h5 := hroot (x ^ (5 : Real)⁻¹) (by positivity)
  have h2' : Chebyshev.psi (x ^ (2 : Real)⁻¹) ≤
      c * x ^ (1 / 2 : Real) := by
    convert h2 using 1 <;> norm_num
  have h3' : Chebyshev.psi (x ^ (3 : Real)⁻¹) ≤
      c * x ^ (1 / 3 : Real) := by
    convert h3 using 1 <;> norm_num
  have h5' : Chebyshev.psi (x ^ (5 : Real)⁻¹) ≤
      c * x ^ (1 / 5 : Real) := by
    convert h5 using 1 <;> norm_num
  nlinarith [hdecomp, h2', h3', h5']

theorem psi_sub_theta_lt_of_root_bound
    {x c : Real} (hx : 0 ≤ x) (hc : 0 ≤ c)
    (hroot : ∀ y : Real, 0 ≤ y → Chebyshev.psi y < c * y) :
    Chebyshev.psi x - Chebyshev.theta x <
      c * (x ^ (1 / 2 : Real) + x ^ (1 / 3 : Real) +
        x ^ (1 / 5 : Real)) := by
  have hdecomp := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have h2 := hroot (x ^ (2 : Real)⁻¹) (by positivity)
  have h3 := hroot (x ^ (3 : Real)⁻¹) (by positivity)
  have h5 := hroot (x ^ (5 : Real)⁻¹) (by positivity)
  have h2' : Chebyshev.psi (x ^ (2 : Real)⁻¹) <
      c * x ^ (1 / 2 : Real) := by
    convert h2 using 1 <;> norm_num
  have h3' : Chebyshev.psi (x ^ (3 : Real)⁻¹) <
      c * x ^ (1 / 3 : Real) := by
    convert h3 using 1 <;> norm_num
  have h5' : Chebyshev.psi (x ^ (5 : Real)⁻¹) <
      c * x ^ (1 / 5 : Real) := by
    convert h5 using 1 <;> norm_num
  nlinarith [hdecomp, h2', h3', h5']

theorem psi_sub_theta_le_of_three_root_bounds
    {x c : Real} (hx : 0 ≤ x) (hc : 0 ≤ c)
    (h2 : Chebyshev.psi (x ^ (2 : Real)⁻¹) ≤
      c * x ^ (1 / 2 : Real))
    (h3 : Chebyshev.psi (x ^ (3 : Real)⁻¹) ≤
      c * x ^ (1 / 3 : Real))
    (h5 : Chebyshev.psi (x ^ (5 : Real)⁻¹) ≤
      c * x ^ (1 / 5 : Real)) :
    Chebyshev.psi x - Chebyshev.theta x ≤
      c * (x ^ (1 / 2 : Real) + x ^ (1 / 3 : Real) +
        x ^ (1 / 5 : Real)) := by
  have hdecomp := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  nlinarith [hdecomp, h2, h3, h5]

theorem fifth_rpow_le_three_fifths_cube_rpow
    {x : Real} (hx : (64 : Real) ≤ x) :
    x ^ (1 / 5 : Real) ≤ (3 : Real) / 5 * x ^ (1 / 3 : Real) := by
  have hx_pos : 0 < x := by linarith
  have hpow : ((13 : Real) / 10) ^ (15 : Nat) ≤ x := by
    have hnum : ((13 : Real) / 10) ^ (15 : Nat) ≤ 64 := by norm_num
    exact hnum.trans hx
  have hlog := Real.log_le_log
    (by positivity : (0 : Real) < ((13 : Real) / 10) ^ (15 : Nat)) hpow
  rw [Real.log_pow] at hlog
  have ha : (13 : Real) / 10 ≤ x ^ (1 / 15 : Real) := by
    apply Real.le_rpow_of_log_le hx_pos
    nlinarith
  have ha_pos : 0 < x ^ (1 / 15 : Real) := by positivity
  have h5 : x ^ (1 / 5 : Real) =
      (x ^ (1 / 15 : Real)) ^ (3 : Nat) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hx_pos)]
    norm_num
  have h3 : x ^ (1 / 3 : Real) =
      (x ^ (1 / 15 : Real)) ^ (5 : Nat) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hx_pos)]
    norm_num
  rw [h5, h3]
  let a : Real := x ^ (1 / 15 : Real)
  have ha2 : (5 : Real) / 3 ≤ a ^ 2 := by
    dsimp [a]
    nlinarith [sq_nonneg (x ^ (1 / 15 : Real) - 13 / 10)]
  have hunit : (1 : Real) ≤ (3 / 5 : Real) * a ^ 2 := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hunit (by positivity : 0 ≤ a ^ 3)
  dsimp [a] at hmul ⊢
  nlinarith

/-! This is Dusart's Proposition 3.2 after the root estimate has been
supplied.  The root estimate is kept explicit so this theorem records the
actual prime-power argument rather than importing Proposition 3.2. -/
theorem dusart_proposition_3_2_of_uniform_strict_root_bound
    {x : Real} (hx : (64 : Real) ≤ x)
    (hroot : ∀ y : Real, 0 ≤ y →
      Chebyshev.psi y < (100007 : Real) / 100000 * y) :
    Chebyshev.psi x - Chebyshev.theta x <
      (100007 : Real) / 100000 * Real.sqrt x +
        (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  have hdecomp := psi_sub_theta_lt_of_root_bound
    (x := x) (c := (100007 : Real) / 100000) (by linarith) (by norm_num)
    hroot
  have hfive := fifth_rpow_le_three_fifths_cube_rpow hx
  have hscaled := mul_le_mul_of_nonneg_left hfive
    (by norm_num : (0 : Real) ≤ (100007 : Real) / 100000)
  have hsqrt : x ^ (1 / 2 : Real) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
  rw [hsqrt] at hdecomp
  have hscaled' : (100007 : Real) / 100000 * x ^ (1 / 5 : Real) ≤
      (100007 : Real) / 100000 * (3 / 5 : Real) *
        x ^ (1 / 3 : Real) := by
    nlinarith [hscaled]
  have hcuberoot : 0 ≤ x ^ (1 / 3 : Real) := by positivity
  have hcoeff : (100007 : Real) / 100000 * x ^ (1 / 3 : Real) +
      (100007 : Real) / 100000 * (3 / 5 : Real) *
        x ^ (1 / 3 : Real) ≤ (178 : Real) / 100 *
          x ^ (1 / 3 : Real) := by
    nlinarith
  nlinarith [hdecomp, hscaled', hcoeff]

/-! The published proposition is global.  Its proof has a finite endpoint
check below `64` and the prime-power argument above that endpoint; keeping
those two inputs separate makes the exact scope of the remaining finite check
visible to the final provider. -/
theorem dusart_proposition_3_2_of_uniform_strict_root_bound_all
    (small : ∀ x : Real, 0 < x → x < 64 →
      Chebyshev.psi x - Chebyshev.theta x <
        (100007 : Real) / 100000 * Real.sqrt x +
          (178 : Real) / 100 * x ^ (1 / 3 : Real))
    (hroot : ∀ y : Real, 0 ≤ y →
      Chebyshev.psi y < (100007 : Real) / 100000 * y) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x <
        (100007 : Real) / 100000 * Real.sqrt x +
          (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  intro x hx
  by_cases hsmall : x < 64
  · exact small x hx hsmall
  · exact dusart_proposition_3_2_of_uniform_strict_root_bound
      (le_of_not_gt hsmall) hroot

theorem dusart_proposition_3_2_of_uniform_strict_root_bound_all_closed
    (hroot : ∀ y : Real, 0 ≤ y →
      Chebyshev.psi y < (100007 : Real) / 100000 * y) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x <
        (100007 : Real) / 100000 * Real.sqrt x +
          (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  intro x hx
  exact dusart_proposition_3_2_of_uniform_strict_root_bound_all
    (fun y hy hy64 => dusart_proposition_3_2_small_64 hy hy64) hroot x hx

/-! This is the numerical composition used in the paper: Lemma 3.3 controls
the prime-power tail after the square-root term, while Proposition 5.1
controls that square-root theta term. -/
theorem dusart_proposition_3_2_of_lemma_3_3_and_theta_upper
    {x : Real} (hx : 0 < x)
    (hlemma : Chebyshev.psi x - Chebyshev.theta x -
        Chebyshev.theta (Real.sqrt x) <
      (1777745 : Real) / 1000000 * x ^ (1 / 3 : Real))
    (htheta : Chebyshev.theta (Real.sqrt x) <
      (100007 : Real) / 100000 * Real.sqrt x) :
    Chebyshev.psi x - Chebyshev.theta x <
      (100007 : Real) / 100000 * Real.sqrt x +
        (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  have hcuberoot : 0 ≤ x ^ (1 / 3 : Real) := by positivity
  nlinarith

theorem dusart_proposition_3_2_of_lemma_3_3_and_dusart_theta_upper
    {x : Real} (hx : 0 < x)
    (hlemma : Chebyshev.psi x - Chebyshev.theta x -
        Chebyshev.theta (Real.sqrt x) <
      (1777745 : Real) / 1000000 * x ^ (1 / 3 : Real))
    (htheta : ∀ y : Real, 0 < y →
      Chebyshev.theta y - y < y / 36260) :
    Chebyshev.psi x - Chebyshev.theta x <
      (100007 : Real) / 100000 * Real.sqrt x +
        (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have htheta' := htheta (Real.sqrt x) hsqrt_pos
  have htheta'' : Chebyshev.theta (Real.sqrt x) <
      (100007 : Real) / 100000 * Real.sqrt x := by
    nlinarith [Real.sqrt_nonneg x]
  exact dusart_proposition_3_2_of_lemma_3_3_and_theta_upper
    hx hlemma htheta''

theorem dusart_theta_upper_100007_of_bounds
    (thetaBounds : HasDusartThetaBounds) :
    ∀ y : Real, 0 < y →
      Chebyshev.theta y < (100007 : Real) / 100000 * y := by
  intro y hy
  have hupper := thetaBounds.1 y hy
  nlinarith

/-! The paper's global Proposition 3.2 assembly.  The input `lemma` is the
uniform Lemma 3.3 estimate, including its bounded direct-computation range;
the second input is the global Proposition 5.1 theta upper bound. -/
theorem dusart_proposition_3_2_of_paper_lemma_and_theta_upper
    (hlemma : ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / 3 : Real))
    (theta_upper : ∀ y : Real, 0 < y →
      Chebyshev.theta y - y < y / 36260) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x <
        (100007 : Real) / 100000 * Real.sqrt x +
          (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  intro x hx
  exact dusart_proposition_3_2_of_lemma_3_3_and_dusart_theta_upper
    hx (hlemma x hx) theta_upper

theorem dusart_proposition_3_2_of_paper_lemma_and_theta_bounds
    (hlemma : ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / 3 : Real))
    (thetaBounds : HasDusartThetaBounds) :
    ∀ x : Real, 0 < x →
          Chebyshev.psi x - Chebyshev.theta x <
        (100007 : Real) / 100000 * Real.sqrt x +
          (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  intro x hx
  exact dusart_proposition_3_2_of_lemma_3_3_and_theta_upper hx
    (hlemma x hx)
    (dusart_theta_upper_100007_of_bounds thetaBounds
      (Real.sqrt x) (Real.sqrt_pos.2 hx))

/-! The prime-power part of Dusart's Lemma 3.3.  For the large range the
floor in the Chebyshev decomposition is at least two, so the square-root
term can be split off exactly and only exponents `k ≥ 3` remain. -/
theorem dusart_lemma_3_3_prime_power_decomposition
    {x : Real} (hx : (9 : Real) ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x -
        Chebyshev.theta (Real.sqrt x) =
      ∑ k ∈ Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊,
        Chebyshev.theta (x ^ (1 / (k : Real))) := by
  have hx2 : (2 : Real) ≤ x := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hN : 2 ≤ ⌊Real.log x / Real.log 2⌋₊ := by
    apply Nat.le_floor
    apply (le_div_iff₀ hlog2).2
    have hlog : Real.log 4 ≤ Real.log x := by
      apply Real.log_le_log (by norm_num)
      linarith
    rw [show (4 : Real) = 2 ^ (2 : Nat) by norm_num,
      Real.log_pow] at hlog
    norm_num at hlog ⊢
    linarith
  have hsplit :
      ∑ k ∈ Finset.Icc 2 ⌊Real.log x / Real.log 2⌋₊,
          Chebyshev.theta (x ^ (1 / (k : Real))) =
        Chebyshev.theta (x ^ ((1 : Real) / 2)) +
          ∑ k ∈ Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊,
            Chebyshev.theta (x ^ (1 / (k : Real))) := by
    rw [← Finset.add_sum_Ioc_eq_sum_Icc hN,
      ← Finset.Icc_add_one_left_eq_Ioc]
    ring_nf
  have hdecomp := Chebyshev.psi_eq_theta_add_sum_theta hx2
  have hsqrt : x ^ ((1 : Real) / 2) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
  rw [hsplit, hsqrt] at hdecomp
  linarith

/-! A reusable elementary estimate for the real-power sum occurring after the
decomposition.  The only input is monotonicity of `x^a` in the exponent when
`x ≥ 1`; the finite cardinality calculation is kept explicit. -/
theorem dusart_prime_power_rpow_sum_le
    {x : Real} (hx : (1 : Real) ≤ x) {N : Nat} (hN : 3 ≤ N) :
    ∑ k ∈ Finset.Icc 3 N, x ^ (1 / (k : Real)) ≤
      x ^ (1 / (3 : Real)) +
        ((N : Real) - 3) * x ^ (1 / (4 : Real)) := by
  have hunion : Finset.Icc 3 N = {3} ∪ Finset.Icc 4 N := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_singleton, Finset.mem_union]
    omega
  rw [hunion, Finset.sum_union]
  · simp only [Finset.sum_singleton]
    calc
      x ^ (1 / (3 : Real)) + ∑ k ∈ Finset.Icc 4 N, x ^ (1 / (k : Real)) ≤
          x ^ (1 / (3 : Real)) +
            (Finset.Icc 4 N).card • x ^ (1 / (4 : Real)) := by
        gcongr
        apply Finset.sum_le_card_nsmul
        intro k hk
        have hk4 : 4 ≤ k := (Finset.mem_Icc.mp hk).1
        have hkr : (4 : Real) ≤ (k : Real) := by exact_mod_cast hk4
        have hexp : (1 / (k : Real) : Real) ≤ 1 / 4 := by
          exact one_div_le_one_div_of_le (by norm_num) hkr
        exact Real.rpow_le_rpow_of_exponent_le hx hexp
      _ = x ^ (1 / (3 : Real)) +
          ((N : Real) - 3) * x ^ (1 / (4 : Real)) := by
        rw [nsmul_eq_mul, Nat.card_Icc]
        have hsub : 4 ≤ N + 1 := by omega
        rw [Nat.cast_sub hsub]
        push_cast
        ring
  · apply Finset.disjoint_left.mpr
    intro k hk₁ hk₂
    simp only [Finset.mem_singleton] at hk₁
    simp only [Finset.mem_Icc] at hk₂
    omega

/-! The numerical coefficient in Lemma 3.3 depends only on the number of
exponents, not on the way that count was obtained.  Keeping this conversion
separate lets a later explicit endpoint argument replace the coarse logarithmic
count without repeating the prime-power estimate. -/
theorem dusart_prime_power_rpow_sum_le_of_count
    {x : Real} (hx : (1 : Real) ≤ x) {N : Nat} (hN : 3 ≤ N)
    (hcount : (N : Real) ≤ (7 : Real) / 10 * x ^ (1 / (12 : Real))) :
    ∑ k ∈ Finset.Icc 3 N, x ^ (1 / (k : Real)) ≤
      (17 : Real) / 10 * x ^ (1 / (3 : Real)) := by
  have hsum := dusart_prime_power_rpow_sum_le hx hN
  have hNnonneg : 0 ≤ (N : Real) - 3 := by
    exact_mod_cast Nat.zero_le (N - 3)
  have hpow4 : 0 ≤ x ^ (1 / (4 : Real)) := by positivity
  have htail : ((N : Real) - 3) * x ^ (1 / (4 : Real)) ≤
      (7 : Real) / 10 * x ^ (1 / (3 : Real)) := by
    calc
      ((N : Real) - 3) * x ^ (1 / (4 : Real)) ≤
          (N : Real) * x ^ (1 / (4 : Real)) := by
        gcongr
        norm_num
      _ ≤ ((7 : Real) / 10 * x ^ (1 / (12 : Real))) *
          x ^ (1 / (4 : Real)) :=
        mul_le_mul_of_nonneg_right hcount hpow4
      _ = (7 : Real) / 10 *
          (x ^ (1 / (12 : Real)) * x ^ (1 / (4 : Real))) := by ring
      _ = (7 : Real) / 10 * x ^ (1 / (3 : Real)) := by
        rw [← Real.rpow_add (by positivity : 0 < x)]
        congr 1
        norm_num
  calc
    ∑ k ∈ Finset.Icc 3 N, x ^ (1 / (k : Real)) ≤
        x ^ (1 / (3 : Real)) +
          ((N : Real) - 3) * x ^ (1 / (4 : Real)) := hsum
    _ ≤ x ^ (1 / (3 : Real)) +
        (7 : Real) / 10 * x ^ (1 / (3 : Real)) :=
      add_le_add le_rfl htail
    _ = (17 : Real) / 10 * x ^ (1 / (3 : Real)) := by ring

/-! The logarithmic count of exponents is negligible at Dusart's large
cutoff.  This is the elementary monotonicity estimate used to turn the
finite sum above into a fixed multiple of `x^(1/3)`. -/
theorem dusart_floor_log_div_two_le_rpow
    {x : Real} (hx : (10 ^ 11 : Real) ^ 3 ≤ x) :
    (⌊Real.log x / Real.log 2⌋₊ : Real) ≤
      (7 : Real) / 10 * x ^ (1 / (12 : Real)) := by
  have hx0 : (10 : Real) ^ 33 ≤ x := by
    convert hx using 1
    norm_num [pow_mul]
  have hx0_pos : 0 < (10 : Real) ^ 33 := by positivity
  have hx_pos : 0 < x := hx0_pos.trans_le hx0
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx_pos : 0 < Real.log x := by
    apply Real.log_pos
    have : (1 : Real) < (10 : Real) ^ 33 := by norm_num
    exact this.trans_le hx0
  have hthreshold : Real.exp ((1 / (12 : Real))⁻¹) ≤ (10 : Real) ^ 33 := by
    rw [show (1 / (12 : Real))⁻¹ = 12 by norm_num]
    have hexp : Real.exp (12 : Real) < (3 : Real) ^ 12 := by
      rw [show (12 : Real) = (12 : Nat) * 1 by norm_num,
        Real.exp_nat_mul]
      exact pow_lt_pow_left₀ Real.exp_one_lt_three
        (Real.exp_pos 1).le (by norm_num)
    linarith
  have hratio_mono := Real.log_div_self_rpow_antitoneOn
    (a := (1 / (12 : Real))) (by norm_num)
    hthreshold (le_trans hthreshold hx0) hx0
  have hpow160 : (160 : Real) ≤ ((10 : Real) ^ 33) ^ (1 / (12 : Real)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    apply Real.le_rpow_of_log_le (by norm_num)
    rw [show (160 : Real) = 2 ^ (4 : Nat) * 10 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    have hlog2_10 : 16 * Real.log 2 ≤ 7 * Real.log 10 := by
      have hpow : (2 : Real) ^ 16 ≤ (10 : Real) ^ 7 := by norm_num
      have := Real.log_le_log (by positivity) hpow
      rw [Real.log_pow, Real.log_pow] at this
      exact this
    have hlog10_pos : 0 < Real.log 10 := Real.log_pos (by norm_num)
    have hlog160 : Real.log 160 = 4 * Real.log 2 + Real.log 10 := by
      rw [show (160 : Real) = 2 ^ (4 : Nat) * 10 by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
      norm_num
    nlinarith [hlog2_10]
  have hlog10_lt : Real.log 10 < (231 : Real) / 100 := by
    have hexp : (10 : Real) < Real.exp ((231 : Real) / 100) := by
      have h := Real.sum_le_exp_of_nonneg (x := (231 : Real) / 100)
        (by norm_num) 8
      norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
      nlinarith
    exact (Real.log_lt_iff_lt_exp (x := (10 : Real))
      (y := (231 : Real) / 100) (by norm_num)).2 hexp
  have hratio : Real.log x / x ^ (1 / (12 : Real)) ≤
      (7 : Real) / 10 * Real.log 2 := by
    have hden : 0 < x ^ (1 / (12 : Real)) := by positivity
    have hmono : Real.log x / x ^ (1 / (12 : Real)) ≤
        Real.log ((10 : Real) ^ 33) / ((10 : Real) ^ 33) ^ (1 / (12 : Real)) := by
      simpa using hratio_mono
    have hnum : Real.log ((10 : Real) ^ 33) ≤ (33 : Real) * ((231 : Real) / 100) := by
      rw [Real.log_pow]
      nlinarith
    have hquot : Real.log ((10 : Real) ^ 33) /
        ((10 : Real) ^ 33) ^ (1 / (12 : Real)) ≤
        ((33 : Real) * ((231 : Real) / 100)) / 160 := by
      calc
        Real.log ((10 : Real) ^ 33) /
            ((10 : Real) ^ 33) ^ (1 / (12 : Real)) ≤
            ((33 : Real) * ((231 : Real) / 100)) /
              ((10 : Real) ^ 33) ^ (1 / (12 : Real)) :=
          div_le_div_of_nonneg_right hnum (by positivity)
        _ ≤ ((33 : Real) * ((231 : Real) / 100)) / 160 :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpow160
    have hlog2_lower : (69 : Real) / 100 < Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    nlinarith [hmono, hquot]
  have hfloor : (⌊Real.log x / Real.log 2⌋₊ : Real) ≤
      Real.log x / Real.log 2 := by
    exact_mod_cast Nat.floor_le (div_nonneg hlogx_pos.le hlog2.le)
  have hcount : Real.log x / Real.log 2 ≤
      (7 : Real) / 10 * x ^ (1 / (12 : Real)) := by
    have hden : 0 < x ^ (1 / (12 : Real)) := by positivity
    apply (div_le_iff₀ hlog2).2
    have h := (div_le_iff₀ hden).1 hratio
    nlinarith
  exact hfloor.trans hcount

/-! Large-range form of Dusart's Lemma 3.3.  The remaining finite range is
handled separately by the paper's direct computation; this theorem contains
the complete analytic tail argument. -/
theorem dusart_lemma_3_3_large_of_count
    {x : Real} (hx : (10 ^ 11 : Real) ^ 3 ≤ x)
    (hcount : (⌊Real.log x / Real.log 2⌋₊ : Real) ≤
      (7 : Real) / 10 * x ^ (1 / (12 : Real)))
    (theta_upper : ∀ y : Real, 0 < y →
      Chebyshev.theta y < (1000081 : Real) / 1000000 * y) :
    Chebyshev.psi x - Chebyshev.theta x -
        Chebyshev.theta (Real.sqrt x) <
      (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  have hx9 : (9 : Real) ≤ x := by
    have : (9 : Real) ≤ (10 ^ 11 : Real) ^ 3 := by norm_num
    exact this.trans hx
  have hdecomp := dusart_lemma_3_3_prime_power_decomposition hx9
  let N : Nat := ⌊Real.log x / Real.log 2⌋₊
  have hN3 : 3 ≤ N := by
    dsimp [N]
    apply Nat.le_floor
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    apply (le_div_iff₀ hlog2).2
    have hlog : Real.log 8 ≤ Real.log x := by
      apply Real.log_le_log (by norm_num)
      exact (show (8 : Real) ≤ (10 ^ 11 : Real) ^ 3 by norm_num).trans hx
    rw [show (8 : Real) = 2 ^ (3 : Nat) by norm_num,
      Real.log_pow] at hlog
    norm_num at hlog ⊢
    linarith
  have hsum17 := dusart_prime_power_rpow_sum_le_of_count
    (x := x) (by linarith [hx]) hN3 hcount
  have htheta_sum :
      (∑ k ∈ Finset.Icc 3 N,
        Chebyshev.theta (x ^ (1 / (k : Real)))) <
      (1000081 : Real) / 1000000 *
        (∑ k ∈ Finset.Icc 3 N, x ^ (1 / (k : Real))) := by
    calc
      (∑ k ∈ Finset.Icc 3 N,
          Chebyshev.theta (x ^ (1 / (k : Real)))) <
          ∑ k ∈ Finset.Icc 3 N,
            (1000081 : Real) / 1000000 * x ^ (1 / (k : Real)) := by
        apply Finset.sum_lt_sum_of_nonempty
        · simp [hN3]
        · intro k hk
          apply theta_upper
          positivity
      _ = (1000081 : Real) / 1000000 *
          (∑ k ∈ Finset.Icc 3 N, x ^ (1 / (k : Real))) := by
        rw [Finset.mul_sum]
  have hcoef :
      (1000081 : Real) / 1000000 * (17 / 10 : Real) <
        (1777745 : Real) / 1000000 := by norm_num
  dsimp [N] at hdecomp htheta_sum hsum17
  calc
    Chebyshev.psi x - Chebyshev.theta x -
        Chebyshev.theta (Real.sqrt x) =
      ∑ k ∈ Finset.Icc 3 N,
        Chebyshev.theta (x ^ (1 / (k : Real))) := hdecomp
    _ < (1000081 : Real) / 1000000 *
        (∑ k ∈ Finset.Icc 3 N, x ^ (1 / (k : Real))) := htheta_sum
    _ ≤ (1000081 : Real) / 1000000 *
        ((17 : Real) / 10 * x ^ (1 / (3 : Real))) :=
      mul_le_mul_of_nonneg_left hsum17 (by norm_num)
    _ = ((1000081 : Real) / 1000000 * (17 / 10 : Real)) *
        x ^ (1 / (3 : Real)) := by ring
    _ < (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) :=
      mul_lt_mul_of_pos_right hcoef (by positivity)

/-! The published large-range theorem supplies the count estimate by the
elementary logarithmic argument, while the preceding theorem keeps that
numerical step replaceable by an independent explicit estimate. -/
theorem dusart_lemma_3_3_large
    {x : Real} (hx : (10 ^ 11 : Real) ^ 3 ≤ x)
    (theta_upper : ∀ y : Real, 0 < y →
      Chebyshev.theta y < (1000081 : Real) / 1000000 * y) :
    Chebyshev.psi x - Chebyshev.theta x -
        Chebyshev.theta (Real.sqrt x) <
      (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_large_of_count hx
    (dusart_floor_log_div_two_le_rpow hx) theta_upper

/-! Global Lemma 3.3 assembled from the paper's bounded direct computation
and the analytic tail above. -/
theorem dusart_lemma_3_3_of_finite_and_theta_upper
    {X : Real} (hX : (10 ^ 11 : Real) ^ 3 ≤ X)
    (finite : ∀ x : Real, 0 < x → x ≤ X →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)))
    (theta_upper : ∀ y : Real, 0 < y →
      Chebyshev.theta y < (1000081 : Real) / 1000000 * y) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  intro x hx
  by_cases hle : x ≤ X
  · exact finite x hx hle
  · have hcut : ¬ x ≤ (10 ^ 11 : Real) ^ 3 := by
      intro hcut
      exact hle (hcut.trans hX)
    exact dusart_lemma_3_3_large (le_of_not_ge hcut) theta_upper

theorem dusart_lemma_3_3_of_rows_and_theta_upper
    {rows : List DusartLemma33FiniteRow} {X : Real}
    (hX : (10 ^ 11 : Real) ^ 3 ≤ X)
    (cover : DusartLemma33FiniteRowsCover rows X)
    (theta_upper : ∀ y : Real, 0 < y →
      Chebyshev.theta y < (1000081 : Real) / 1000000 * y) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_of_finite_and_theta_upper hX
    (dusart_lemma_3_3_finite_of_rows cover) theta_upper

/-! The upper half of Proposition 5.1 is stronger than the relaxed uniform
estimate used in the large-range part of Lemma 3.3.  Export the numerical
conversion once so downstream source proofs use the paper's displayed
constant rather than repeating an arithmetic adapter. -/
theorem dusart_theta_upper_1000081_of_bounds
    (thetaBounds : HasDusartThetaBounds) :
    ∀ y : Real, 0 < y →
      Chebyshev.theta y < (1000081 : Real) / 1000000 * y := by
  intro y hy
  have hupper := thetaBounds.1 y hy
  nlinarith

/-! The paper's theta hypothesis is exported in the project's bundled
Proposition 5.1 interface.  This adapter keeps the Lemma 3.3 proof connected
to that interface without weakening the finite-range obligation. -/
theorem dusart_lemma_3_3_of_rows_and_theta_bounds
    {rows : List DusartLemma33FiniteRow} {X : Real}
    (hX : (10 ^ 11 : Real) ^ 3 ≤ X)
    (cover : DusartLemma33FiniteRowsCover rows X)
    (thetaBounds : HasDusartThetaBounds) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x -
        Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  apply dusart_lemma_3_3_of_rows_and_theta_upper hX cover
  exact dusart_theta_upper_1000081_of_bounds thetaBounds

/-! Indexed form for the compact bounded computation.  The proof is kept at
the source boundary so a generated table can be assembled from reusable rows
without first materializing an equivalent list. -/
theorem dusart_lemma_3_3_of_indexed_rows_and_theta_bounds
    {n : Nat} {rows : Fin n → DusartLemma33FiniteRow} {X : Real}
    (hX : (10 ^ 11 : Real) ^ 3 ≤ X)
    (cover : DusartLemma33FiniteRowsIndexedCover rows X)
    (thetaBounds : HasDusartThetaBounds) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_of_finite_and_theta_upper hX
    (dusart_lemma_3_3_finite_of_indexed_rows cover) (by
      intro y hy
      have hupper := thetaBounds.1 y hy
      nlinarith)

/-! This is the exact finite/analytic split stated in Dusart's proof: the
bounded computation ends at `(10^11)^3`, while the displayed power-sum
estimate handles the tail. -/
theorem dusart_lemma_3_3_of_paper_finite_check
    (finite : ∀ x : Real, 0 < x →
      x ≤ (10 ^ 11 : Real) ^ 3 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)))
    (thetaBounds : HasDusartThetaBounds) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_of_finite_and_theta_upper
    (by norm_num) finite (by
      intro y hy
      have hupper := thetaBounds.1 y hy
      nlinarith)

/-! The paper-shaped finite obligation can be supplied by integer endpoint
checks.  This is the boundary consumed by a compact bounded computation. -/
theorem dusart_lemma_3_3_of_paper_integer_endpoint_check
    (endpoint : ∀ n : Nat, 1 ≤ n →
      (n : Real) ≤ (10 ^ 11 : Real) ^ 3 →
      Chebyshev.psi (n : Real) - Chebyshev.theta n -
          Chebyshev.theta (Real.sqrt n) <
        (1777745 : Real) / 1000000 * (n : Real) ^ (1 / (3 : Real)))
    (thetaBounds : HasDusartThetaBounds) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x -
      Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_of_paper_finite_check
    (dusart_lemma_3_3_finite_of_integer_endpoints endpoint) thetaBounds

/-! Proposition 3.2 can now consume the paper-shaped finite Lemma 3.3 input
and the bundled Proposition 5.1 theta estimate directly. -/
theorem dusart_proposition_3_2_of_paper_finite_lemma_and_theta_bounds
    (finite : ∀ x : Real, 0 < x →
      x ≤ (10 ^ 11 : Real) ^ 3 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)))
    (thetaBounds : HasDusartThetaBounds) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x <
        (100007 : Real) / 100000 * Real.sqrt x +
          (178 : Real) / 100 * x ^ (1 / (3 : Real)) := by
  exact dusart_proposition_3_2_of_paper_lemma_and_theta_bounds
    (dusart_lemma_3_3_of_paper_finite_check finite thetaBounds) thetaBounds

/-! Compact-row form of the paper's Proposition 3.2 boundary. The indexed
Lemma 3.3 rows discharge only the bounded computation; the theta provider is
still an explicit theorem input and the analytic tail is supplied by
`dusart_lemma_3_3_large`. -/
theorem dusart_proposition_3_2_of_indexed_rows_and_theta_bounds
    {n : Nat} {rows : Fin n → DusartLemma33FiniteRow} {X : Real}
    (hX : (10 ^ 11 : Real) ^ 3 ≤ X)
    (cover : DusartLemma33FiniteRowsIndexedCover rows X)
    (thetaBounds : HasDusartThetaBounds) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x <
        (100007 : Real) / 100000 * Real.sqrt x +
          (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  exact dusart_proposition_3_2_of_paper_finite_lemma_and_theta_bounds
    (fun x hx hX' => dusart_lemma_3_3_finite_of_indexed_rows cover x hx hX')
    thetaBounds

theorem dusart_proposition_3_2_of_paper_integer_endpoint_check
    (endpoint : ∀ n : Nat, 1 ≤ n →
      (n : Real) ≤ (10 ^ 11 : Real) ^ 3 →
      Chebyshev.psi (n : Real) - Chebyshev.theta n -
          Chebyshev.theta (Real.sqrt n) <
        (1777745 : Real) / 1000000 * (n : Real) ^ (1 / (3 : Real)))
    (thetaBounds : HasDusartThetaBounds) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x <
        (100007 : Real) / 100000 * Real.sqrt x +
          (178 : Real) / 100 * x ^ (1 / (3 : Real)) := by
  exact dusart_proposition_3_2_of_paper_finite_lemma_and_theta_bounds
    (fun x hx hX =>
      dusart_lemma_3_3_finite_of_integer_endpoints endpoint x hx hX)
    thetaBounds

theorem dusart_proposition_3_2_of_finite_lemma_and_theta_upper
    {X : Real} (hX : (10 ^ 11 : Real) ^ 3 ≤ X)
    (finite : ∀ x : Real, 0 < x → x ≤ X →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)))
    (theta_error : ∀ y : Real, 0 < y →
      Chebyshev.theta y - y < y / 36260) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x <
        (100007 : Real) / 100000 * Real.sqrt x +
          (178 : Real) / 100 * x ^ (1 / (3 : Real)) := by
  apply dusart_proposition_3_2_of_paper_lemma_and_theta_upper
  · apply dusart_lemma_3_3_of_finite_and_theta_upper hX finite
    intro y hy
    have h := theta_error y hy
    nlinarith
  · exact theta_error

theorem dusart_gap_upper_from_uniform_root_bound
    {x : Real} (hx : (64 : Real) ≤ x)
    (hroot : ∀ y : Real, 0 ≤ y →
      Chebyshev.psi y ≤ (100007 : Real) / 100000 * y) :
    Chebyshev.psi x - Chebyshev.theta x ≤
      (100007 : Real) / 100000 * Real.sqrt x +
        (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  have hdecomp := psi_sub_theta_le_of_root_bound
    (x := x) (c := (100007 : Real) / 100000) (by linarith) (by norm_num) hroot
  have hfive := fifth_rpow_le_three_fifths_cube_rpow hx
  have hscaled := mul_le_mul_of_nonneg_left hfive
    (by norm_num : (0 : Real) ≤ (100007 : Real) / 100000)
  have hsqrt : x ^ (1 / 2 : Real) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
  rw [hsqrt] at hdecomp
  have hdecomp' : Chebyshev.psi x - Chebyshev.theta x ≤
      (100007 : Real) / 100000 * Real.sqrt x +
        (100007 : Real) / 100000 * x ^ (1 / 3 : Real) +
        (100007 : Real) / 100000 * x ^ (1 / 5 : Real) := by
    nlinarith [hdecomp]
  have hscaled' : (100007 : Real) / 100000 * x ^ (1 / 5 : Real) ≤
      (100007 : Real) / 100000 * (3 / 5 : Real) *
        x ^ (1 / 3 : Real) := by
    nlinarith [hscaled]
  have hcuberoot : 0 ≤ x ^ (1 / 3 : Real) := by positivity
  have hcoeff : (100007 : Real) / 100000 * x ^ (1 / 3 : Real) +
      (100007 : Real) / 100000 * (3 / 5 : Real) *
        x ^ (1 / 3 : Real) ≤ (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
    nlinarith
  nlinarith [hdecomp', hscaled', hcoeff]

theorem psi_upper_of_theta_upper_at_large
    {y : Real} (hy : (4e18 : Real) ≤ y)
    (htheta : Chebyshev.theta y ≤ y + y / 36260) :
    Chebyshev.psi y ≤ (100007 : Real) / 100000 * y := by
  have hy_pos : 0 < y := by linarith
  have hlog : (42 : Real) ≤ Real.log y := by
    exact forty_two_lt_log_four_e18.le.trans
      (Real.log_le_log (by norm_num) hy)
  have hlog_pos : 0 < Real.log y := by linarith
  have hpow : (42 : Real) ^ (4 : Nat) ≤ (Real.log y) ^ (4 : Nat) := by
    exact pow_le_pow_left₀ (by norm_num) hlog 4
  have hcor : Chebyshev.psi y - Chebyshev.theta y ≤
      y / (Real.log y) ^ 4 := by
    have habs := theta_sub_psi_abs_le_logFourth hy
    have hnonneg : 0 ≤ Chebyshev.psi y - Chebyshev.theta y := by
      linarith [Chebyshev.theta_le_psi y]
    rw [abs_sub_comm, abs_of_nonneg hnonneg] at habs
    exact habs
  have hscaled : y / (Real.log y) ^ 4 ≤ y / (42 : Real) ^ 4 := by
    exact div_le_div_of_nonneg_left hy_pos.le (by positivity) hpow
  nlinarith [hcor, hscaled, htheta]

theorem psi_upper_of_strict_theta_upper_at_large
    {y : Real} (hy : (4e18 : Real) ≤ y)
    (htheta : Chebyshev.theta y < y + y / 36260) :
    Chebyshev.psi y < (100007 : Real) / 100000 * y := by
  have hy_pos : 0 < y := by linarith
  have hlog : (42 : Real) ≤ Real.log y := by
    exact forty_two_lt_log_four_e18.le.trans
      (Real.log_le_log (by norm_num) hy)
  have hlog_pos : 0 < Real.log y := by linarith
  have hpow : (42 : Real) ^ (4 : Nat) ≤ (Real.log y) ^ (4 : Nat) := by
    exact pow_le_pow_left₀ (by norm_num) hlog 4
  have hcor : Chebyshev.psi y - Chebyshev.theta y ≤
      y / (Real.log y) ^ 4 := by
    have habs := theta_sub_psi_abs_le_logFourth hy
    have hnonneg : 0 ≤ Chebyshev.psi y - Chebyshev.theta y := by
      linarith [Chebyshev.theta_le_psi y]
    rw [abs_sub_comm, abs_of_nonneg hnonneg] at habs
    exact habs
  have hscaled : y / (Real.log y) ^ 4 ≤ y / (42 : Real) ^ 4 := by
    exact div_le_div_of_nonneg_left hy_pos.le (by positivity) hpow
  have hsum : Chebyshev.psi y <
      y + y / 36260 + y / (42 : Real) ^ 4 := by
    nlinarith [hcor, hscaled]
  have hbound : y + y / 36260 + y / (42 : Real) ^ 4 ≤
      (100007 : Real) / 100000 * y := by
    nlinarith [hy_pos]
  exact hsum.trans_le hbound

theorem dusart_gap_upper_from_three_large_theta_bounds
    {x : Real} (hx : (64 : Real) ≤ x)
    (h2cut : (4e18 : Real) ≤ x ^ (2 : Real)⁻¹)
    (h3cut : (4e18 : Real) ≤ x ^ (3 : Real)⁻¹)
    (h5cut : (4e18 : Real) ≤ x ^ (5 : Real)⁻¹)
    (h2theta : Chebyshev.theta (x ^ (2 : Real)⁻¹) ≤
      x ^ (2 : Real)⁻¹ + x ^ (2 : Real)⁻¹ / 36260)
    (h3theta : Chebyshev.theta (x ^ (3 : Real)⁻¹) ≤
      x ^ (3 : Real)⁻¹ + x ^ (3 : Real)⁻¹ / 36260)
    (h5theta : Chebyshev.theta (x ^ (5 : Real)⁻¹) ≤
      x ^ (5 : Real)⁻¹ + x ^ (5 : Real)⁻¹ / 36260) :
    Chebyshev.psi x - Chebyshev.theta x ≤
      (100007 : Real) / 100000 * Real.sqrt x +
        (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  have h2psi := psi_upper_of_theta_upper_at_large h2cut h2theta
  have h3psi := psi_upper_of_theta_upper_at_large h3cut h3theta
  have h5psi := psi_upper_of_theta_upper_at_large h5cut h5theta
  have h2psi' : Chebyshev.psi (x ^ (2 : Real)⁻¹) ≤
      (100007 : Real) / 100000 * x ^ (1 / 2 : Real) := by
    simpa only [show (2 : Real)⁻¹ = 1 / 2 by norm_num] using h2psi
  have h3psi' : Chebyshev.psi (x ^ (3 : Real)⁻¹) ≤
      (100007 : Real) / 100000 * x ^ (1 / 3 : Real) := by
    simpa only [show (3 : Real)⁻¹ = 1 / 3 by norm_num] using h3psi
  have h5psi' : Chebyshev.psi (x ^ (5 : Real)⁻¹) ≤
      (100007 : Real) / 100000 * x ^ (1 / 5 : Real) := by
    simpa only [show (5 : Real)⁻¹ = 1 / 5 by norm_num] using h5psi
  have hdecomp := psi_sub_theta_le_of_three_root_bounds
    (x := x) (c := (100007 : Real) / 100000) (by linarith) (by norm_num)
    h2psi' h3psi' h5psi'
  have hfive := fifth_rpow_le_three_fifths_cube_rpow hx
  have hscaled := mul_le_mul_of_nonneg_left hfive
    (by norm_num : (0 : Real) ≤ (100007 : Real) / 100000)
  have hsqrt : x ^ (1 / 2 : Real) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
  rw [hsqrt] at hdecomp
  have hdecomp' : Chebyshev.psi x - Chebyshev.theta x ≤
      (100007 : Real) / 100000 * Real.sqrt x +
        (100007 : Real) / 100000 * x ^ (1 / 3 : Real) +
        (100007 : Real) / 100000 * x ^ (1 / 5 : Real) := by
    nlinarith [hdecomp]
  have hscaled' : (100007 : Real) / 100000 * x ^ (1 / 5 : Real) ≤
      (100007 : Real) / 100000 * (3 / 5 : Real) *
        x ^ (1 / 3 : Real) := by
    nlinarith [hscaled]
  have hcuberoot : 0 ≤ x ^ (1 / 3 : Real) := by positivity
  have hcoeff : (100007 : Real) / 100000 * x ^ (1 / 3 : Real) +
      (100007 : Real) / 100000 * (3 / 5 : Real) *
        x ^ (1 / 3 : Real) ≤ (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
    nlinarith
  nlinarith [hdecomp', hscaled', hcoeff]

theorem dusart_gap_upper_from_three_strict_large_theta_bounds
    {x : Real} (hx : (64 : Real) ≤ x)
    (h2cut : (4e18 : Real) ≤ x ^ (2 : Real)⁻¹)
    (h3cut : (4e18 : Real) ≤ x ^ (3 : Real)⁻¹)
    (h5cut : (4e18 : Real) ≤ x ^ (5 : Real)⁻¹)
    (h2theta : Chebyshev.theta (x ^ (2 : Real)⁻¹) <
      x ^ (2 : Real)⁻¹ + x ^ (2 : Real)⁻¹ / 36260)
    (h3theta : Chebyshev.theta (x ^ (3 : Real)⁻¹) <
      x ^ (3 : Real)⁻¹ + x ^ (3 : Real)⁻¹ / 36260)
    (h5theta : Chebyshev.theta (x ^ (5 : Real)⁻¹) <
      x ^ (5 : Real)⁻¹ + x ^ (5 : Real)⁻¹ / 36260) :
    Chebyshev.psi x - Chebyshev.theta x <
      (100007 : Real) / 100000 * Real.sqrt x +
        (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  have h2psi := psi_upper_of_strict_theta_upper_at_large h2cut h2theta
  have h3psi := psi_upper_of_strict_theta_upper_at_large h3cut h3theta
  have h5psi := psi_upper_of_strict_theta_upper_at_large h5cut h5theta
  have h2psi' : Chebyshev.psi (x ^ (2 : Real)⁻¹) <
      (100007 : Real) / 100000 * x ^ (1 / 2 : Real) := by
    simpa only [show (2 : Real)⁻¹ = 1 / 2 by norm_num] using h2psi
  have h3psi' : Chebyshev.psi (x ^ (3 : Real)⁻¹) <
      (100007 : Real) / 100000 * x ^ (1 / 3 : Real) := by
    simpa only [show (3 : Real)⁻¹ = 1 / 3 by norm_num] using h3psi
  have h5psi' : Chebyshev.psi (x ^ (5 : Real)⁻¹) <
      (100007 : Real) / 100000 * x ^ (1 / 5 : Real) := by
    simpa only [show (5 : Real)⁻¹ = 1 / 5 by norm_num] using h5psi
  have hdecomp := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have hfive := fifth_rpow_le_three_fifths_cube_rpow hx
  have hscaled := mul_le_mul_of_nonneg_left hfive
    (by norm_num : (0 : Real) ≤ (100007 : Real) / 100000)
  have hsqrt : x ^ (1 / 2 : Real) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
  have hdecomp'' : Chebyshev.psi x - Chebyshev.theta x <
      (100007 : Real) / 100000 * x ^ (1 / 2 : Real) +
        (100007 : Real) / 100000 * x ^ (1 / 3 : Real) +
        (100007 : Real) / 100000 * x ^ (1 / 5 : Real) := by
    nlinarith [hdecomp, h2psi', h3psi', h5psi']
  have hdecomp' : Chebyshev.psi x - Chebyshev.theta x <
      (100007 : Real) / 100000 * Real.sqrt x +
        (100007 : Real) / 100000 * x ^ (1 / 3 : Real) +
        (100007 : Real) / 100000 * x ^ (1 / 5 : Real) := by
    simpa only [hsqrt] using hdecomp''
  have hscaled' : (100007 : Real) / 100000 * x ^ (1 / 5 : Real) ≤
      (100007 : Real) / 100000 * (3 / 5 : Real) *
        x ^ (1 / 3 : Real) := by
    nlinarith [hscaled]
  have hcuberoot : 0 ≤ x ^ (1 / 3 : Real) := by positivity
  have hcoeff : (100007 : Real) / 100000 * x ^ (1 / 3 : Real) +
      (100007 : Real) / 100000 * (3 / 5 : Real) *
        x ^ (1 / 3 : Real) ≤ (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
    nlinarith
  nlinarith [hdecomp', hscaled', hcoeff]

theorem psi_sub_theta_ge_elementary_sqrt_gap
    {x : Real} (hx : (62500000000 : Real) ≤ x) :
    (86 : Real) / 100 * Real.sqrt x ≤
      Chebyshev.psi x - Chebyshev.theta x := by
  have hx_pos : 0 < x := by linarith
  have hroot_lower : (250000 : Real) ≤ Real.sqrt x := by
    apply (Real.le_sqrt' (by norm_num : (0 : Real) < 250000)).2
    nlinarith
  have htheta := elementary_theta_lower_from_250000 hroot_lower
  have hdecomp := psi_sub_theta_ge_theta_sqrt (by linarith : (2 : Real) ≤ x)
  have htheta' : (86 : Real) / 100 * Real.sqrt x ≤
      Chebyshev.theta (Real.sqrt x) := by
    simpa only [Real.sqrt_eq_rpow] using htheta
  have hdecomp' : Chebyshev.theta (Real.sqrt x) ≤
      Chebyshev.psi x - Chebyshev.theta x := by
    simpa only [Real.sqrt_eq_rpow] using hdecomp
  exact htheta'.trans hdecomp'

theorem dusart_theta_upper_tail_step
    {x : Real} (hx : (8e11 : Real) ≤ x)
    (hx_upper : x ≤ (1446257067000 : Real))
    (hpsi : Chebyshev.psi x ≤ (100002841 : Real) / 100000000 * x)
    (hgap : (9999 : Real) / 10000 * Real.sqrt x ≤
      Chebyshev.psi x - Chebyshev.theta x) :
    Chebyshev.theta x - x ≤ x / 36260 := by
  have hx_pos : 0 < x := by linarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsqrt_sq : (Real.sqrt x) ^ 2 = x := by
    simpa using Real.sq_sqrt (le_of_lt hx_pos)
  have hmain := theta_le_one_plus_dusart_error_of_psi_upper_and_gap hpsi hgap
  have hlinear :
      (100002841 : Real) / 100000000 * x -
          (9999 : Real) / 10000 * Real.sqrt x - x ≤ x / 36260 := by
    have hsqrt_lower : (894000 : Real) ≤ Real.sqrt x := by
      apply (Real.le_sqrt' (by norm_num : (0 : Real) < 894000)).2
      nlinarith
    have hsqrt_upper : Real.sqrt x ≤ (12026689 : Real) / 10 := by
      apply (Real.sqrt_le_iff).2
      constructor
      · norm_num
      · nlinarith
    have hxs : x ≤ (12026689 : Real) / 10 * Real.sqrt x := by
      calc
        x = Real.sqrt x * Real.sqrt x := by nlinarith [hsqrt_sq]
        _ ≤ (12026689 : Real) / 10 * Real.sqrt x :=
          mul_le_mul_of_nonneg_right hsqrt_upper hsqrt_nonneg
    nlinarith
  linarith

theorem dusart_theta_upper_e28_step
    {x : Real} (hx : (8e11 : Real) ≤ x)
    (hx_exp : x ≤ Real.exp 28)
    (hpsi : Chebyshev.psi x ≤ (100002841 : Real) / 100000000 * x)
    (hgap : (9999 : Real) / 10000 * Real.sqrt x ≤
      Chebyshev.psi x - Chebyshev.theta x) :
    Chebyshev.theta x - x ≤ x / 36260 := by
  apply dusart_theta_upper_tail_step hx ?_ hpsi hgap
  exact hx_exp.trans (le_of_lt exp_twentyEight_lt_dusart_endpoint)

theorem dusart_theta_upper_e28_from_absolute_psi_error
    {x : Real} (hx : (8e11 : Real) ≤ x)
    (hx_exp : x ≤ Real.exp 28)
    (hpsi_error : |Chebyshev.psi x - x| ≤
      (2841 : Real) / 100000000 * x)
    (hgap : (9999 : Real) / 10000 * Real.sqrt x ≤
      Chebyshev.psi x - Chebyshev.theta x) :
    Chebyshev.theta x - x ≤ x / 36260 := by
  have hpsi : Chebyshev.psi x ≤
      (100002841 : Real) / 100000000 * x := by
    have hupper := (abs_le.mp hpsi_error).2
    nlinarith
  exact dusart_theta_upper_e28_step hx hx_exp hpsi hgap

/-! The strict form is the one consumed by the published theta interface.
The paper's two strict input estimates are retained here instead of being
weakened to a closed inequality at this boundary. -/
theorem dusart_theta_upper_e28_step_strict
    {x : Real} (hx : (8e11 : Real) ≤ x)
    (hx_exp : x ≤ Real.exp 28)
    (hpsi : Chebyshev.psi x < (100002841 : Real) / 100000000 * x)
    (hgap : (9999 : Real) / 10000 * Real.sqrt x <
      Chebyshev.psi x - Chebyshev.theta x) :
    Chebyshev.theta x - x < x / 36260 := by
  have hx_pos : 0 < x := by linarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsqrt_sq : (Real.sqrt x) ^ 2 = x := by
    simpa using Real.sq_sqrt (le_of_lt hx_pos)
  have hx_upper : x ≤ (1446257067000 : Real) := by
    exact hx_exp.trans (le_of_lt exp_twentyEight_lt_dusart_endpoint)
  have hsqrt_lower : (894000 : Real) ≤ Real.sqrt x := by
    apply (Real.le_sqrt' (by norm_num : (0 : Real) < 894000)).2
    nlinarith
  have hsqrt_upper : Real.sqrt x ≤ (12026689 : Real) / 10 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · nlinarith
  have hxs : x ≤ (12026689 : Real) / 10 * Real.sqrt x := by
    calc
      x = Real.sqrt x * Real.sqrt x := by nlinarith [hsqrt_sq]
      _ ≤ (12026689 : Real) / 10 * Real.sqrt x :=
        mul_le_mul_of_nonneg_right hsqrt_upper hsqrt_nonneg
  have hlinear :
      (100002841 : Real) / 100000000 * x -
          (9999 : Real) / 10000 * Real.sqrt x - x ≤ x / 36260 := by
    nlinarith
  have hmain : Chebyshev.theta x - x <
      (100002841 : Real) / 100000000 * x -
        (9999 : Real) / 10000 * Real.sqrt x - x := by
    linarith
  exact hmain.trans_le hlinear

end
end PrimeFactorUnimodality
