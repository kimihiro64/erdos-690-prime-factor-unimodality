import PrimeFactorUnimodality.Helpers.Analytic.DusartLemma33MidrangeEndpointsPart05

/-! Generated endpoint proof shard 06 for Dusart's Lemma 3.3. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PrimeFactorUnimodality

noncomputable section
theorem dusart_lemma33_row_endpoint_19321_22200 :
    Chebyshev.psi (22200 : Real) - Chebyshev.theta 22200 -
        Chebyshev.theta (Real.sqrt (22200 : Real)) <
      (1777745 : Real) / 1000000 * (19321 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (22200 : Real) / Real.log 2⌋₊ ≤ 14 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (22200 : Real) < Real.log ((2 : Real) ^ 15) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 22200) (k := 2) (r := 148) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(22200 : Real) ^ (1 / (2 : Real))⌋₊ = 148 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((22200 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (148 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 22200) (k := 3) (r := 28) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(22200 : Real) ^ (1 / (3 : Real))⌋₊ = 28 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((22200 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (28 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 22200) (k := 4) (r := 12) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(22200 : Real) ^ (1 / (4 : Real))⌋₊ = 12 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((22200 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (12 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 22200) (k := 5) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(22200 : Real) ^ (1 / (5 : Real))⌋₊ = 7 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((22200 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 22200) (k := 6) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(22200 : Real) ^ (1 / (6 : Real))⌋₊ = 5 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((22200 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 22200) (k := 7) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(22200 : Real) ^ (1 / (7 : Real))⌋₊ = 4 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((22200 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 22200) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(22200 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((22200 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 22200) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(22200 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((22200 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 22200) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(22200 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((22200 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 22200) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(22200 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((22200 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 22200) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(22200 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((22200 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 22200) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(22200 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((22200 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 22200) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(22200 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((22200 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (22200 : Real)) =
      Chebyshev.theta (148 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (22200 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, hsqrt]
  rw [dusart_theta_nat_148, dusart_theta_nat_28, dusart_theta_nat_12, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_22201_24388 :
    Chebyshev.psi (24388 : Real) - Chebyshev.theta 24388 -
        Chebyshev.theta (Real.sqrt (24388 : Real)) <
      (1777745 : Real) / 1000000 * (22201 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (24388 : Real) / Real.log 2⌋₊ ≤ 14 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (24388 : Real) < Real.log ((2 : Real) ^ 15) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24388) (k := 2) (r := 156) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(24388 : Real) ^ (1 / (2 : Real))⌋₊ = 156 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((24388 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (156 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24388) (k := 3) (r := 28) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(24388 : Real) ^ (1 / (3 : Real))⌋₊ = 28 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((24388 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (28 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24388) (k := 4) (r := 12) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(24388 : Real) ^ (1 / (4 : Real))⌋₊ = 12 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((24388 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (12 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24388) (k := 5) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(24388 : Real) ^ (1 / (5 : Real))⌋₊ = 7 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((24388 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24388) (k := 6) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(24388 : Real) ^ (1 / (6 : Real))⌋₊ = 5 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((24388 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24388) (k := 7) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(24388 : Real) ^ (1 / (7 : Real))⌋₊ = 4 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((24388 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24388) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(24388 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((24388 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24388) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(24388 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((24388 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24388) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(24388 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((24388 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24388) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(24388 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((24388 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24388) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(24388 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((24388 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24388) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(24388 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((24388 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24388) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(24388 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((24388 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (24388 : Real)) =
      Chebyshev.theta (156 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (24388 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, hsqrt]
  rw [dusart_theta_nat_156, dusart_theta_nat_28, dusart_theta_nat_12, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_24389_24648 :
    Chebyshev.psi (24648 : Real) - Chebyshev.theta 24648 -
        Chebyshev.theta (Real.sqrt (24648 : Real)) <
      (1777745 : Real) / 1000000 * (24389 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (24648 : Real) / Real.log 2⌋₊ ≤ 14 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (24648 : Real) < Real.log ((2 : Real) ^ 15) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24648) (k := 2) (r := 156) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(24648 : Real) ^ (1 / (2 : Real))⌋₊ = 156 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((24648 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (156 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24648) (k := 3) (r := 29) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(24648 : Real) ^ (1 / (3 : Real))⌋₊ = 29 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((24648 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (29 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24648) (k := 4) (r := 12) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(24648 : Real) ^ (1 / (4 : Real))⌋₊ = 12 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((24648 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (12 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24648) (k := 5) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(24648 : Real) ^ (1 / (5 : Real))⌋₊ = 7 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((24648 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24648) (k := 6) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(24648 : Real) ^ (1 / (6 : Real))⌋₊ = 5 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((24648 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24648) (k := 7) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(24648 : Real) ^ (1 / (7 : Real))⌋₊ = 4 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((24648 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24648) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(24648 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((24648 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24648) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(24648 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((24648 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24648) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(24648 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((24648 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24648) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(24648 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((24648 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24648) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(24648 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((24648 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24648) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(24648 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((24648 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 24648) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(24648 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((24648 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (24648 : Real)) =
      Chebyshev.theta (156 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (24648 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, hsqrt]
  rw [dusart_theta_nat_156, dusart_theta_nat_29, dusart_theta_nat_12, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_24649_26568 :
    Chebyshev.psi (26568 : Real) - Chebyshev.theta 26568 -
        Chebyshev.theta (Real.sqrt (26568 : Real)) <
      (1777745 : Real) / 1000000 * (24649 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (26568 : Real) / Real.log 2⌋₊ ≤ 14 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (26568 : Real) < Real.log ((2 : Real) ^ 15) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 26568) (k := 2) (r := 162) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(26568 : Real) ^ (1 / (2 : Real))⌋₊ = 162 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((26568 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (162 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 26568) (k := 3) (r := 29) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(26568 : Real) ^ (1 / (3 : Real))⌋₊ = 29 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((26568 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (29 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 26568) (k := 4) (r := 12) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(26568 : Real) ^ (1 / (4 : Real))⌋₊ = 12 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((26568 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (12 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 26568) (k := 5) (r := 7) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(26568 : Real) ^ (1 / (5 : Real))⌋₊ = 7 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((26568 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (7 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 26568) (k := 6) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(26568 : Real) ^ (1 / (6 : Real))⌋₊ = 5 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((26568 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 26568) (k := 7) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(26568 : Real) ^ (1 / (7 : Real))⌋₊ = 4 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((26568 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 26568) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(26568 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((26568 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 26568) (k := 9) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(26568 : Real) ^ (1 / (9 : Real))⌋₊ = 3 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((26568 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 26568) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(26568 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((26568 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 26568) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(26568 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((26568 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 26568) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(26568 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((26568 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 26568) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(26568 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((26568 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 26568) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(26568 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((26568 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (26568 : Real)) =
      Chebyshev.theta (162 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (26568 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, hsqrt]
  rw [dusart_theta_nat_162, dusart_theta_nat_29, dusart_theta_nat_12, dusart_theta_nat_7, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

end

end PrimeFactorUnimodality
