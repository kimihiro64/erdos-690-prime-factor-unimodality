import PrimeFactorUnimodality.Helpers.Analytic.DusartLemma33MidrangeEndpointsPart01

/-! Generated endpoint proof shard 02 for Dusart's Lemma 3.3. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PrimeFactorUnimodality

noncomputable section
theorem dusart_lemma33_row_endpoint_3721_4488 :
    Chebyshev.psi (4488 : Real) - Chebyshev.theta 4488 -
        Chebyshev.theta (Real.sqrt (4488 : Real)) <
      (1777745 : Real) / 1000000 * (3721 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (4488 : Real) / Real.log 2⌋₊ ≤ 12 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (4488 : Real) < Real.log ((2 : Real) ^ 13) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4488) (k := 2) (r := 66) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(4488 : Real) ^ (1 / (2 : Real))⌋₊ = 66 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((4488 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (66 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4488) (k := 3) (r := 16) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(4488 : Real) ^ (1 / (3 : Real))⌋₊ = 16 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((4488 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (16 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4488) (k := 4) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(4488 : Real) ^ (1 / (4 : Real))⌋₊ = 8 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((4488 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4488) (k := 5) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(4488 : Real) ^ (1 / (5 : Real))⌋₊ = 5 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((4488 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4488) (k := 6) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(4488 : Real) ^ (1 / (6 : Real))⌋₊ = 4 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((4488 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4488) (k := 7) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(4488 : Real) ^ (1 / (7 : Real))⌋₊ = 3 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((4488 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4488) (k := 8) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(4488 : Real) ^ (1 / (8 : Real))⌋₊ = 2 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((4488 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4488) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(4488 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((4488 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4488) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(4488 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((4488 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4488) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(4488 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((4488 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 4488) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(4488 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((4488 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (4488 : Real)) =
      Chebyshev.theta (66 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (4488 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, hsqrt]
  rw [dusart_theta_nat_66, dusart_theta_nat_16, dusart_theta_nat_8, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_4489_5040 :
    Chebyshev.psi (5040 : Real) - Chebyshev.theta 5040 -
        Chebyshev.theta (Real.sqrt (5040 : Real)) <
      (1777745 : Real) / 1000000 * (4489 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (5040 : Real) / Real.log 2⌋₊ ≤ 12 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (5040 : Real) < Real.log ((2 : Real) ^ 13) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5040) (k := 2) (r := 70) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(5040 : Real) ^ (1 / (2 : Real))⌋₊ = 70 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((5040 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (70 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5040) (k := 3) (r := 17) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(5040 : Real) ^ (1 / (3 : Real))⌋₊ = 17 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((5040 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (17 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5040) (k := 4) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(5040 : Real) ^ (1 / (4 : Real))⌋₊ = 8 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((5040 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5040) (k := 5) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(5040 : Real) ^ (1 / (5 : Real))⌋₊ = 5 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((5040 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5040) (k := 6) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(5040 : Real) ^ (1 / (6 : Real))⌋₊ = 4 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((5040 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5040) (k := 7) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(5040 : Real) ^ (1 / (7 : Real))⌋₊ = 3 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((5040 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5040) (k := 8) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(5040 : Real) ^ (1 / (8 : Real))⌋₊ = 2 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((5040 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5040) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(5040 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((5040 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5040) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(5040 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((5040 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5040) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(5040 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((5040 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5040) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(5040 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((5040 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (5040 : Real)) =
      Chebyshev.theta (70 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (5040 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, hsqrt]
  rw [dusart_theta_nat_70, dusart_theta_nat_17, dusart_theta_nat_8, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_5041_5328 :
    Chebyshev.psi (5328 : Real) - Chebyshev.theta 5328 -
        Chebyshev.theta (Real.sqrt (5328 : Real)) <
      (1777745 : Real) / 1000000 * (5041 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (5328 : Real) / Real.log 2⌋₊ ≤ 12 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (5328 : Real) < Real.log ((2 : Real) ^ 13) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5328) (k := 2) (r := 72) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(5328 : Real) ^ (1 / (2 : Real))⌋₊ = 72 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((5328 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (72 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5328) (k := 3) (r := 17) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(5328 : Real) ^ (1 / (3 : Real))⌋₊ = 17 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((5328 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (17 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5328) (k := 4) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(5328 : Real) ^ (1 / (4 : Real))⌋₊ = 8 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((5328 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5328) (k := 5) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(5328 : Real) ^ (1 / (5 : Real))⌋₊ = 5 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((5328 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5328) (k := 6) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(5328 : Real) ^ (1 / (6 : Real))⌋₊ = 4 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((5328 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5328) (k := 7) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(5328 : Real) ^ (1 / (7 : Real))⌋₊ = 3 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((5328 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5328) (k := 8) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(5328 : Real) ^ (1 / (8 : Real))⌋₊ = 2 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((5328 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5328) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(5328 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((5328 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5328) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(5328 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((5328 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5328) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(5328 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((5328 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 5328) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(5328 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((5328 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (5328 : Real)) =
      Chebyshev.theta (72 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (5328 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, hsqrt]
  rw [dusart_theta_nat_72, dusart_theta_nat_17, dusart_theta_nat_8, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_5329_6240 :
    Chebyshev.psi (6240 : Real) - Chebyshev.theta 6240 -
        Chebyshev.theta (Real.sqrt (6240 : Real)) <
      (1777745 : Real) / 1000000 * (5329 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (6240 : Real) / Real.log 2⌋₊ ≤ 12 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (6240 : Real) < Real.log ((2 : Real) ^ 13) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6240) (k := 2) (r := 78) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(6240 : Real) ^ (1 / (2 : Real))⌋₊ = 78 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((6240 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (78 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6240) (k := 3) (r := 18) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(6240 : Real) ^ (1 / (3 : Real))⌋₊ = 18 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((6240 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (18 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6240) (k := 4) (r := 8) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(6240 : Real) ^ (1 / (4 : Real))⌋₊ = 8 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((6240 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (8 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6240) (k := 5) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(6240 : Real) ^ (1 / (5 : Real))⌋₊ = 5 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((6240 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6240) (k := 6) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(6240 : Real) ^ (1 / (6 : Real))⌋₊ = 4 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((6240 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6240) (k := 7) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(6240 : Real) ^ (1 / (7 : Real))⌋₊ = 3 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((6240 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6240) (k := 8) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(6240 : Real) ^ (1 / (8 : Real))⌋₊ = 2 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((6240 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6240) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(6240 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((6240 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6240) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(6240 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((6240 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6240) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(6240 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((6240 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6240) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(6240 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((6240 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (6240 : Real)) =
      Chebyshev.theta (78 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (6240 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, hsqrt]
  rw [dusart_theta_nat_78, dusart_theta_nat_18, dusart_theta_nat_8, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

end

end PrimeFactorUnimodality
