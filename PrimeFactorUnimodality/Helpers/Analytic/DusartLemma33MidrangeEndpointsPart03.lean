import PrimeFactorUnimodality.Helpers.Analytic.DusartLemma33MidrangeEndpointsPart02

/-! Generated endpoint proof shard 03 for Dusart's Lemma 3.3. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PrimeFactorUnimodality

noncomputable section
theorem dusart_lemma33_row_endpoint_6241_6858 :
    Chebyshev.psi (6858 : Real) - Chebyshev.theta 6858 -
        Chebyshev.theta (Real.sqrt (6858 : Real)) <
      (1777745 : Real) / 1000000 * (6241 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (6858 : Real) / Real.log 2⌋₊ ≤ 12 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (6858 : Real) < Real.log ((2 : Real) ^ 13) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6858) (k := 2) (r := 82) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(6858 : Real) ^ (1 / (2 : Real))⌋₊ = 82 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((6858 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (82 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6858) (k := 3) (r := 18) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(6858 : Real) ^ (1 / (3 : Real))⌋₊ = 18 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((6858 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (18 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6858) (k := 4) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(6858 : Real) ^ (1 / (4 : Real))⌋₊ = 9 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((6858 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6858) (k := 5) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(6858 : Real) ^ (1 / (5 : Real))⌋₊ = 5 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((6858 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6858) (k := 6) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(6858 : Real) ^ (1 / (6 : Real))⌋₊ = 4 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((6858 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6858) (k := 7) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(6858 : Real) ^ (1 / (7 : Real))⌋₊ = 3 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((6858 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6858) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(6858 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((6858 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6858) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(6858 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((6858 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6858) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(6858 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((6858 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6858) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(6858 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((6858 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6858) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(6858 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((6858 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (6858 : Real)) =
      Chebyshev.theta (82 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (6858 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, hsqrt]
  rw [dusart_theta_nat_82, dusart_theta_nat_18, dusart_theta_nat_9, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_6859_6888 :
    Chebyshev.psi (6888 : Real) - Chebyshev.theta 6888 -
        Chebyshev.theta (Real.sqrt (6888 : Real)) <
      (1777745 : Real) / 1000000 * (6859 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (6888 : Real) / Real.log 2⌋₊ ≤ 12 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (6888 : Real) < Real.log ((2 : Real) ^ 13) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6888) (k := 2) (r := 82) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(6888 : Real) ^ (1 / (2 : Real))⌋₊ = 82 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((6888 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (82 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6888) (k := 3) (r := 19) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(6888 : Real) ^ (1 / (3 : Real))⌋₊ = 19 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((6888 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (19 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6888) (k := 4) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(6888 : Real) ^ (1 / (4 : Real))⌋₊ = 9 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((6888 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6888) (k := 5) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(6888 : Real) ^ (1 / (5 : Real))⌋₊ = 5 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((6888 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6888) (k := 6) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(6888 : Real) ^ (1 / (6 : Real))⌋₊ = 4 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((6888 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6888) (k := 7) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(6888 : Real) ^ (1 / (7 : Real))⌋₊ = 3 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((6888 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6888) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(6888 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((6888 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6888) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(6888 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((6888 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6888) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(6888 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((6888 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6888) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(6888 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((6888 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 6888) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(6888 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((6888 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (6888 : Real)) =
      Chebyshev.theta (82 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (6888 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, hsqrt]
  rw [dusart_theta_nat_82, dusart_theta_nat_19, dusart_theta_nat_9, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_6889_7920 :
    Chebyshev.psi (7920 : Real) - Chebyshev.theta 7920 -
        Chebyshev.theta (Real.sqrt (7920 : Real)) <
      (1777745 : Real) / 1000000 * (6889 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (7920 : Real) / Real.log 2⌋₊ ≤ 12 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (7920 : Real) < Real.log ((2 : Real) ^ 13) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7920) (k := 2) (r := 88) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(7920 : Real) ^ (1 / (2 : Real))⌋₊ = 88 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((7920 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (88 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7920) (k := 3) (r := 19) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(7920 : Real) ^ (1 / (3 : Real))⌋₊ = 19 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((7920 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (19 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7920) (k := 4) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(7920 : Real) ^ (1 / (4 : Real))⌋₊ = 9 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((7920 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7920) (k := 5) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(7920 : Real) ^ (1 / (5 : Real))⌋₊ = 6 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((7920 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7920) (k := 6) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(7920 : Real) ^ (1 / (6 : Real))⌋₊ = 4 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((7920 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7920) (k := 7) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(7920 : Real) ^ (1 / (7 : Real))⌋₊ = 3 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((7920 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7920) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(7920 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((7920 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7920) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(7920 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((7920 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7920) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(7920 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((7920 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7920) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(7920 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((7920 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 7920) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(7920 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((7920 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (7920 : Real)) =
      Chebyshev.theta (88 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (7920 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, hsqrt]
  rw [dusart_theta_nat_88, dusart_theta_nat_19, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_7921_9408 :
    Chebyshev.psi (9408 : Real) - Chebyshev.theta 9408 -
        Chebyshev.theta (Real.sqrt (9408 : Real)) <
      (1777745 : Real) / 1000000 * (7921 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (9408 : Real) / Real.log 2⌋₊ ≤ 13 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (9408 : Real) < Real.log ((2 : Real) ^ 14) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9408) (k := 2) (r := 96) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(9408 : Real) ^ (1 / (2 : Real))⌋₊ = 96 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((9408 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (96 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9408) (k := 3) (r := 21) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(9408 : Real) ^ (1 / (3 : Real))⌋₊ = 21 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((9408 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (21 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9408) (k := 4) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(9408 : Real) ^ (1 / (4 : Real))⌋₊ = 9 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((9408 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9408) (k := 5) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(9408 : Real) ^ (1 / (5 : Real))⌋₊ = 6 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((9408 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9408) (k := 6) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(9408 : Real) ^ (1 / (6 : Real))⌋₊ = 4 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((9408 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9408) (k := 7) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(9408 : Real) ^ (1 / (7 : Real))⌋₊ = 3 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((9408 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9408) (k := 8) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(9408 : Real) ^ (1 / (8 : Real))⌋₊ = 3 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((9408 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9408) (k := 9) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(9408 : Real) ^ (1 / (9 : Real))⌋₊ = 2 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((9408 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9408) (k := 10) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(9408 : Real) ^ (1 / (10 : Real))⌋₊ = 2 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((9408 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9408) (k := 11) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(9408 : Real) ^ (1 / (11 : Real))⌋₊ = 2 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((9408 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9408) (k := 12) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(9408 : Real) ^ (1 / (12 : Real))⌋₊ = 2 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((9408 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 9408) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(9408 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((9408 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (9408 : Real)) =
      Chebyshev.theta (96 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (9408 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, hsqrt]
  rw [dusart_theta_nat_96, dusart_theta_nat_21, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

end

end PrimeFactorUnimodality
