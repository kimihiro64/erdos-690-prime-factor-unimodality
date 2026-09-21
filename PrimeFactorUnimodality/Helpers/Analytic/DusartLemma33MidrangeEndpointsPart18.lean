import PrimeFactorUnimodality.Helpers.Analytic.DusartLemma33MidrangeEndpointsPart17

/-! Generated endpoint proof shard 18 for Dusart's Lemma 3.3. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PrimeFactorUnimodality

noncomputable section
theorem dusart_lemma33_row_endpoint_537289_571786 :
    Chebyshev.psi (571786 : Real) - Chebyshev.theta 571786 -
        Chebyshev.theta (Real.sqrt (571786 : Real)) <
      (1777745 : Real) / 1000000 * (537289 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (571786 : Real) / Real.log 2⌋₊ ≤ 19 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (571786 : Real) < Real.log ((2 : Real) ^ 20) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 2) (r := 756) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(571786 : Real) ^ (1 / (2 : Real))⌋₊ = 756 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((571786 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (756 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 3) (r := 82) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(571786 : Real) ^ (1 / (3 : Real))⌋₊ = 82 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((571786 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (82 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 4) (r := 27) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(571786 : Real) ^ (1 / (4 : Real))⌋₊ = 27 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((571786 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (27 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 5) (r := 14) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(571786 : Real) ^ (1 / (5 : Real))⌋₊ = 14 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((571786 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (14 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 6) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(571786 : Real) ^ (1 / (6 : Real))⌋₊ = 9 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((571786 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 7) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(571786 : Real) ^ (1 / (7 : Real))⌋₊ = 6 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((571786 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(571786 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((571786 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(571786 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((571786 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(571786 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((571786 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(571786 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((571786 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(571786 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((571786 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(571786 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((571786 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(571786 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((571786 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(571786 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((571786 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(571786 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((571786 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(571786 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((571786 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(571786 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((571786 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 571786) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(571786 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((571786 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (571786 : Real)) =
      Chebyshev.theta (756 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (571786 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, hsqrt]
  rw [dusart_theta_nat_756, dusart_theta_nat_82, dusart_theta_nat_27, dusart_theta_nat_14, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_571787_591360 :
    Chebyshev.psi (591360 : Real) - Chebyshev.theta 591360 -
        Chebyshev.theta (Real.sqrt (591360 : Real)) <
      (1777745 : Real) / 1000000 * (571787 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (591360 : Real) / Real.log 2⌋₊ ≤ 19 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (591360 : Real) < Real.log ((2 : Real) ^ 20) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 2) (r := 768) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(591360 : Real) ^ (1 / (2 : Real))⌋₊ = 768 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((591360 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (768 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 3) (r := 83) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(591360 : Real) ^ (1 / (3 : Real))⌋₊ = 83 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((591360 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (83 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 4) (r := 27) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(591360 : Real) ^ (1 / (4 : Real))⌋₊ = 27 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((591360 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (27 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 5) (r := 14) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(591360 : Real) ^ (1 / (5 : Real))⌋₊ = 14 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((591360 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (14 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 6) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(591360 : Real) ^ (1 / (6 : Real))⌋₊ = 9 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((591360 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 7) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(591360 : Real) ^ (1 / (7 : Real))⌋₊ = 6 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((591360 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(591360 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((591360 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(591360 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((591360 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(591360 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((591360 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(591360 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((591360 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(591360 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((591360 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(591360 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((591360 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(591360 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((591360 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(591360 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((591360 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(591360 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((591360 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(591360 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((591360 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(591360 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((591360 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 591360) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(591360 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((591360 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (591360 : Real)) =
      Chebyshev.theta (768 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (591360 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, hsqrt]
  rw [dusart_theta_nat_768, dusart_theta_nat_83, dusart_theta_nat_27, dusart_theta_nat_14, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_591361_654480 :
    Chebyshev.psi (654480 : Real) - Chebyshev.theta 654480 -
        Chebyshev.theta (Real.sqrt (654480 : Real)) <
      (1777745 : Real) / 1000000 * (591361 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (654480 : Real) / Real.log 2⌋₊ ≤ 19 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (654480 : Real) < Real.log ((2 : Real) ^ 20) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 2) (r := 808) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(654480 : Real) ^ (1 / (2 : Real))⌋₊ = 808 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((654480 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (808 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 3) (r := 86) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(654480 : Real) ^ (1 / (3 : Real))⌋₊ = 86 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((654480 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (86 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 4) (r := 28) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(654480 : Real) ^ (1 / (4 : Real))⌋₊ = 28 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((654480 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (28 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 5) (r := 14) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(654480 : Real) ^ (1 / (5 : Real))⌋₊ = 14 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((654480 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (14 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 6) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(654480 : Real) ^ (1 / (6 : Real))⌋₊ = 9 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((654480 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 7) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(654480 : Real) ^ (1 / (7 : Real))⌋₊ = 6 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((654480 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(654480 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((654480 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(654480 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((654480 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(654480 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((654480 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(654480 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((654480 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(654480 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((654480 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(654480 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((654480 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(654480 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((654480 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(654480 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((654480 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(654480 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((654480 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(654480 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((654480 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(654480 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((654480 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 654480) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(654480 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((654480 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (654480 : Real)) =
      Chebyshev.theta (808 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (654480 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, hsqrt]
  rw [dusart_theta_nat_808, dusart_theta_nat_86, dusart_theta_nat_28, dusart_theta_nat_14, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

theorem dusart_lemma33_row_endpoint_654481_683928 :
    Chebyshev.psi (683928 : Real) - Chebyshev.theta 683928 -
        Chebyshev.theta (Real.sqrt (683928 : Real)) <
      (1777745 : Real) / 1000000 * (654481 : Real) ^ (1 / (3 : Real)) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hN : ⌊Real.log (683928 : Real) / Real.log 2⌋₊ ≤ 19 := by
    apply Nat.le_of_lt_succ
    apply (Nat.floor_lt (by positivity)).2
    have hlog : Real.log (683928 : Real) < Real.log ((2 : Real) ^ 20) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    apply (div_lt_iff₀ hlog2).2
    exact hlog
  have hroot_2 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 2) (r := 826) (by norm_num) (by norm_num) (by norm_num)
  have hroot_2' : ⌊(683928 : Real) ^ (1 / (2 : Real))⌋₊ = 826 := by
    simpa using hroot_2
  have htheta_2 : Chebyshev.theta ((683928 : Real) ^ (1 / (2 : Real))) =
      Chebyshev.theta (826 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_2']
    norm_num
  have hroot_3 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 3) (r := 88) (by norm_num) (by norm_num) (by norm_num)
  have hroot_3' : ⌊(683928 : Real) ^ (1 / (3 : Real))⌋₊ = 88 := by
    simpa using hroot_3
  have htheta_3 : Chebyshev.theta ((683928 : Real) ^ (1 / (3 : Real))) =
      Chebyshev.theta (88 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_3']
    norm_num
  have hroot_4 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 4) (r := 28) (by norm_num) (by norm_num) (by norm_num)
  have hroot_4' : ⌊(683928 : Real) ^ (1 / (4 : Real))⌋₊ = 28 := by
    simpa using hroot_4
  have htheta_4 : Chebyshev.theta ((683928 : Real) ^ (1 / (4 : Real))) =
      Chebyshev.theta (28 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_4']
    norm_num
  have hroot_5 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 5) (r := 14) (by norm_num) (by norm_num) (by norm_num)
  have hroot_5' : ⌊(683928 : Real) ^ (1 / (5 : Real))⌋₊ = 14 := by
    simpa using hroot_5
  have htheta_5 : Chebyshev.theta ((683928 : Real) ^ (1 / (5 : Real))) =
      Chebyshev.theta (14 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_5']
    norm_num
  have hroot_6 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 6) (r := 9) (by norm_num) (by norm_num) (by norm_num)
  have hroot_6' : ⌊(683928 : Real) ^ (1 / (6 : Real))⌋₊ = 9 := by
    simpa using hroot_6
  have htheta_6 : Chebyshev.theta ((683928 : Real) ^ (1 / (6 : Real))) =
      Chebyshev.theta (9 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_6']
    norm_num
  have hroot_7 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 7) (r := 6) (by norm_num) (by norm_num) (by norm_num)
  have hroot_7' : ⌊(683928 : Real) ^ (1 / (7 : Real))⌋₊ = 6 := by
    simpa using hroot_7
  have htheta_7 : Chebyshev.theta ((683928 : Real) ^ (1 / (7 : Real))) =
      Chebyshev.theta (6 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_7']
    norm_num
  have hroot_8 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 8) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hroot_8' : ⌊(683928 : Real) ^ (1 / (8 : Real))⌋₊ = 5 := by
    simpa using hroot_8
  have htheta_8 : Chebyshev.theta ((683928 : Real) ^ (1 / (8 : Real))) =
      Chebyshev.theta (5 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_8']
    norm_num
  have hroot_9 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 9) (r := 4) (by norm_num) (by norm_num) (by norm_num)
  have hroot_9' : ⌊(683928 : Real) ^ (1 / (9 : Real))⌋₊ = 4 := by
    simpa using hroot_9
  have htheta_9 : Chebyshev.theta ((683928 : Real) ^ (1 / (9 : Real))) =
      Chebyshev.theta (4 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_9']
    norm_num
  have hroot_10 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 10) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_10' : ⌊(683928 : Real) ^ (1 / (10 : Real))⌋₊ = 3 := by
    simpa using hroot_10
  have htheta_10 : Chebyshev.theta ((683928 : Real) ^ (1 / (10 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_10']
    norm_num
  have hroot_11 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 11) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_11' : ⌊(683928 : Real) ^ (1 / (11 : Real))⌋₊ = 3 := by
    simpa using hroot_11
  have htheta_11 : Chebyshev.theta ((683928 : Real) ^ (1 / (11 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_11']
    norm_num
  have hroot_12 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 12) (r := 3) (by norm_num) (by norm_num) (by norm_num)
  have hroot_12' : ⌊(683928 : Real) ^ (1 / (12 : Real))⌋₊ = 3 := by
    simpa using hroot_12
  have htheta_12 : Chebyshev.theta ((683928 : Real) ^ (1 / (12 : Real))) =
      Chebyshev.theta (3 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_12']
    norm_num
  have hroot_13 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 13) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_13' : ⌊(683928 : Real) ^ (1 / (13 : Real))⌋₊ = 2 := by
    simpa using hroot_13
  have htheta_13 : Chebyshev.theta ((683928 : Real) ^ (1 / (13 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_13']
    norm_num
  have hroot_14 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 14) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_14' : ⌊(683928 : Real) ^ (1 / (14 : Real))⌋₊ = 2 := by
    simpa using hroot_14
  have htheta_14 : Chebyshev.theta ((683928 : Real) ^ (1 / (14 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_14']
    norm_num
  have hroot_15 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 15) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_15' : ⌊(683928 : Real) ^ (1 / (15 : Real))⌋₊ = 2 := by
    simpa using hroot_15
  have htheta_15 : Chebyshev.theta ((683928 : Real) ^ (1 / (15 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_15']
    norm_num
  have hroot_16 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 16) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_16' : ⌊(683928 : Real) ^ (1 / (16 : Real))⌋₊ = 2 := by
    simpa using hroot_16
  have htheta_16 : Chebyshev.theta ((683928 : Real) ^ (1 / (16 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_16']
    norm_num
  have hroot_17 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 17) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_17' : ⌊(683928 : Real) ^ (1 / (17 : Real))⌋₊ = 2 := by
    simpa using hroot_17
  have htheta_17 : Chebyshev.theta ((683928 : Real) ^ (1 / (17 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_17']
    norm_num
  have hroot_18 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 18) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_18' : ⌊(683928 : Real) ^ (1 / (18 : Real))⌋₊ = 2 := by
    simpa using hroot_18
  have htheta_18 : Chebyshev.theta ((683928 : Real) ^ (1 / (18 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_18']
    norm_num
  have hroot_19 := nat_floor_rpow_eq_of_pow_le_pow_lt
    (n := 683928) (k := 19) (r := 2) (by norm_num) (by norm_num) (by norm_num)
  have hroot_19' : ⌊(683928 : Real) ^ (1 / (19 : Real))⌋₊ = 2 := by
    simpa using hroot_19
  have htheta_19 : Chebyshev.theta ((683928 : Real) ^ (1 / (19 : Real))) =
      Chebyshev.theta (2 : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hroot_19']
    norm_num
  have hsqrt : Chebyshev.theta (Real.sqrt (683928 : Real)) =
      Chebyshev.theta (826 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact htheta_2
  have hpsi := Chebyshev.psi_eq_theta_add_sum_theta' (x := (683928 : Real))
    (by norm_num) hN
  rw [hpsi]
  norm_num [Finset.sum_Icc_succ_top]
  rw [htheta_2, htheta_3, htheta_4, htheta_5, htheta_6, htheta_7, htheta_8, htheta_9, htheta_10, htheta_11, htheta_12, htheta_13, htheta_14, htheta_15, htheta_16, htheta_17, htheta_18, htheta_19, hsqrt]
  rw [dusart_theta_nat_826, dusart_theta_nat_88, dusart_theta_nat_28, dusart_theta_nat_14, dusart_theta_nat_9, dusart_theta_nat_6, dusart_theta_nat_5, dusart_theta_nat_4, dusart_theta_nat_3, dusart_theta_nat_2]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Nat.log, Nat.log.go]
  interval_decide

end

end PrimeFactorUnimodality
