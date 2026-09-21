import PrimeFactorUnimodality.Helpers.Analytic.DusartLemma33MidrangeEndpointsPart10

/-! Generated endpoint proof shard 11 for Dusart's Lemma 3.3. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PrimeFactorUnimodality

noncomputable section
theorem dusart_lemma33_row_endpoint_83521_94248 :
    Chebyshev.psi (94248 : Real) - Chebyshev.theta 94248 -
        Chebyshev.theta (Real.sqrt (94248 : Real)) <
      (1777745 : Real) / 1000000 * (83521 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (94248 : Real) / Real.log 2⌋₊ ≤ 16 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (94248 : Real) < Real.log ((2 : Real) ^ 17) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 2) (r := 306) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(94248 : Real) ^ (1 / (2 : Real))⌋₊ = 306 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((94248 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (306 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 3) (r := 45) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(94248 : Real) ^ (1 / (3 : Real))⌋₊ = 45 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((94248 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (45 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 4) (r := 17) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(94248 : Real) ^ (1 / (4 : Real))⌋₊ = 17 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((94248 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (17 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 5) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(94248 : Real) ^ (1 / (5 : Real))⌋₊ = 9 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((94248 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 6) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(94248 : Real) ^ (1 / (6 : Real))⌋₊ = 6 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((94248 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(94248 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((94248 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(94248 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((94248 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(94248 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((94248 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(94248 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((94248 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(94248 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((94248 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(94248 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((94248 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(94248 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((94248 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(94248 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((94248 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(94248 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((94248 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 94248) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(94248 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((94248 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (94248 : Real)) =
      Chebyshev.theta (306 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (94248 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, hsqrt]
  rw [dusart_theta_nat_306, dusart_theta_nat_45, dusart_theta_nat_17, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_94249_97968 :
    Chebyshev.psi (97968 : Real) - Chebyshev.theta 97968 -
        Chebyshev.theta (Real.sqrt (97968 : Real)) <
      (1777745 : Real) / 1000000 * (94249 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (97968 : Real) / Real.log 2⌋₊ ≤ 16 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (97968 : Real) < Real.log ((2 : Real) ^ 17) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 2) (r := 312) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(97968 : Real) ^ (1 / (2 : Real))⌋₊ = 312 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((97968 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (312 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 3) (r := 46) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(97968 : Real) ^ (1 / (3 : Real))⌋₊ = 46 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((97968 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (46 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 4) (r := 17) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(97968 : Real) ^ (1 / (4 : Real))⌋₊ = 17 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((97968 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (17 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 5) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(97968 : Real) ^ (1 / (5 : Real))⌋₊ = 9 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((97968 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 6) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(97968 : Real) ^ (1 / (6 : Real))⌋₊ = 6 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((97968 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(97968 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((97968 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(97968 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((97968 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(97968 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((97968 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(97968 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((97968 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(97968 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((97968 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(97968 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((97968 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(97968 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((97968 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(97968 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((97968 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(97968 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((97968 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 97968) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(97968 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((97968 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (97968 : Real)) =
      Chebyshev.theta (312 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (97968 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, hsqrt]
  rw [dusart_theta_nat_312, dusart_theta_nat_46, dusart_theta_nat_17, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_97969_109560 :
    Chebyshev.psi (109560 : Real) - Chebyshev.theta 109560 -
        Chebyshev.theta (Real.sqrt (109560 : Real)) <
      (1777745 : Real) / 1000000 * (97969 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (109560 : Real) / Real.log 2⌋₊ ≤ 16 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (109560 : Real) < Real.log ((2 : Real) ^ 17) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 2) (r := 330) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(109560 : Real) ^ (1 / (2 : Real))⌋₊ = 330 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((109560 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (330 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 3) (r := 47) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(109560 : Real) ^ (1 / (3 : Real))⌋₊ = 47 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((109560 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (47 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 4) (r := 18) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(109560 : Real) ^ (1 / (4 : Real))⌋₊ = 18 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((109560 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (18 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 5) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(109560 : Real) ^ (1 / (5 : Real))⌋₊ = 10 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((109560 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 6) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(109560 : Real) ^ (1 / (6 : Real))⌋₊ = 6 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((109560 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(109560 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((109560 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(109560 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((109560 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(109560 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((109560 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(109560 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((109560 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(109560 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((109560 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(109560 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((109560 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(109560 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((109560 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(109560 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((109560 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(109560 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((109560 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 109560) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(109560 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((109560 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (109560 : Real)) =
      Chebyshev.theta (330 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (109560 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, hsqrt]
  rw [dusart_theta_nat_330, dusart_theta_nat_47, dusart_theta_nat_18, dusart_theta_nat_10, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_109561_120408 :
    Chebyshev.psi (120408 : Real) - Chebyshev.theta 120408 -
        Chebyshev.theta (Real.sqrt (120408 : Real)) <
      (1777745 : Real) / 1000000 * (109561 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (120408 : Real) / Real.log 2⌋₊ ≤ 16 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (120408 : Real) < Real.log ((2 : Real) ^ 17) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 2) (r := 346) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(120408 : Real) ^ (1 / (2 : Real))⌋₊ = 346 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((120408 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (346 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 3) (r := 49) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(120408 : Real) ^ (1 / (3 : Real))⌋₊ = 49 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((120408 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (49 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 4) (r := 18) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(120408 : Real) ^ (1 / (4 : Real))⌋₊ = 18 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((120408 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (18 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 5) (r := 10) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(120408 : Real) ^ (1 / (5 : Real))⌋₊ = 10 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((120408 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (10 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 6) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(120408 : Real) ^ (1 / (6 : Real))⌋₊ = 7 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((120408 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 7) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(120408 : Real) ^ (1 / (7 : Real))⌋₊ = 5 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((120408 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 8) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(120408 : Real) ^ (1 / (8 : Real))⌋₊ = 4 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((120408 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(120408 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((120408 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(120408 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((120408 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(120408 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((120408 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(120408 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((120408 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(120408 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((120408 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(120408 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((120408 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(120408 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((120408 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 120408) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(120408 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((120408 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (120408 : Real)) =
      Chebyshev.theta (346 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (120408 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, hsqrt]
  rw [dusart_theta_nat_346, dusart_theta_nat_49, dusart_theta_nat_18, dusart_theta_nat_10, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

end

end PrimeFactorUnimodality
