import PrimeFactorUnimodality.Helpers.Analytic.PrimeWeightSum
import PrimeFactorUnimodality.Helpers.Analytic.SharpThetaBounds
import PrimeFactorUnimodality.Helpers.PrimeSequence.AverageGap

set_option autoImplicit false

/-! # A later small gap from elementary theta bounds -/

namespace PrimeFactorUnimodality

open Real Finset

theorem theta_sub_le_card_primesIoc_mul_log (a b : Nat) (hab : a <= b) :
    Chebyshev.theta b - Chebyshev.theta a <= (primesIoc a b).card * log b := by
  have hsub : Nat.primesLE a <= Nat.primesLE b := by
    intro p hp
    have h := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr (And.intro (h.1.trans hab) h.2)
  have hs : Nat.primesLE b \ Nat.primesLE a = primesIoc a b := by
    ext p
    simp only [Finset.mem_sdiff, Nat.mem_primesLE, mem_primesIoc]
    constructor
    next =>
      intro h
      have hpa : a < p := by
        by_contra hnot
        exact h.2 (And.intro (by omega) h.1.2)
      exact And.intro h.1.2 (And.intro hpa h.1.1)
    next =>
      intro h
      exact And.intro (And.intro h.2.2 h.1) (by omega)
  have heq := Finset.sum_sdiff_eq_sub (f := fun p : Nat => log (p : Real)) hsub
  rw [hs, <- Chebyshev.theta_eq_sum_primesLE_log, <- Chebyshev.theta_eq_sum_primesLE_log] at heq
  rw [<- heq]
  calc
    (primesIoc a b).sum (fun p => log (p : Real)) <=
        (primesIoc a b).sum (fun _ => log (b : Real)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact log_le_log (by exact_mod_cast (primesIoc_prime hp).pos)
        (by exact_mod_cast primesIoc_upper hp)
    _ = (primesIoc a b).card * log b := by simp

theorem log_fourHundred_mul_lt_fifth (P : Nat) (hP : (2 : Nat)^30 <= P) :
    log (400 * (P : Real)) < (P : Real) / 5 := by
  have hPr : (1073741824 : Real) <= P := by exact_mod_cast hP
  have hPpos : (0 : Real) < P := by linarith
  have hlogP := Chebyshev.log_le_seven_thousandths_mul P (by linarith)
  have hlog400 : log (400 : Real) < 6 := by
    rw [show (400 : Real) = 2^(4 : Nat) * 5^(2 : Nat) by norm_num,
      log_mul (by positivity) (by positivity), log_pow, log_pow]
    norm_num
    linarith [LogTables.log_2_lt, LogTables.log_5_lt]
  rw [log_mul (by norm_num) hPpos.ne']
  linarith

theorem exists_later_elementary_small_gap (P : Nat) (hP : (2 : Nat)^30 <= P) :
    Exists (fun j : Nat => And (Nat.primeCounting (4 * P) <= j)
      (And (primeAt j <= 400 * P)
        ((primeGap j : Real) + 1 < 1.09 * log (400 * (P : Real)) + 2))) := by
  let N := Nat.primeCounting (400 * P) - Nat.primeCounting (4 * P)
  let G := Nat.ceil (1.09 * log (400 * (P : Real)))
  have hPr : (1073741824 : Real) <= P := by exact_mod_cast hP
  have hPpos : (0 : Real) < P := by linarith
  have hlogpos : 0 < log (400 * (P : Real)) := log_pos (by linarith)
  have hlogsmall := log_fourHundred_mul_lt_fifth P hP
  have hthetaLo := Chebyshev.theta_lower_092_from_pow30 (400 * (P : Real)) (by
    norm_num
    linarith)
  have hthetaHi := Chebyshev.theta_upper_112_from_2000 (4 * (P : Real)) (by linarith)
  have hcount := theta_sub_le_card_primesIoc_mul_log (4 * P) (400 * P) (by omega)
  rw [card_primesIoc _ _ (by omega)] at hcount
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hcount
  have hNlog : 363.52 * (P : Real) <= (N : Real) * log (400 * (P : Real)) := by
    change Chebyshev.theta (400 * (P : Real)) - Chebyshev.theta (4 * (P : Real)) <=
      (N : Real) * log (400 * (P : Real)) at hcount
    linarith
  have hN : 2 <= N := by
    by_contra hnot
    have hsmall : (N : Real) <= 1 := by exact_mod_cast (by omega : N <= 1)
    have hmul := mul_le_mul_of_nonneg_right hsmall hlogpos.le
    nlinarith
  have hG : 1.09 * log (400 * (P : Real)) <= (G : Real) := Nat.le_ceil _
  have hpred : ((N - 1 : Nat) : Real) = (N : Real) - 1 := by
    rw [Nat.cast_sub (by omega : 1 <= N), Nat.cast_one]
  have hwidthReal : (396 : Real) * P < ((N - 1 : Nat) : Real) * (G : Real) := by
    have hmul := mul_le_mul_of_nonneg_left hG (Nat.cast_nonneg (N - 1))
    rw [hpred] at hmul
    rw [hpred]
    nlinarith
  have hwidth : 400 * P - 4 * P < (N - 1) * G := by
    have heq : 400 * P - 4 * P = 396 * P := by omega
    rw [heq]
    exact_mod_cast hwidthReal
  cases exists_primeGap_lt_of_count (4 * P) (400 * P) G hN hwidth with
  | intro i hi =>
    let j := Nat.primeCounting (4 * P) + i
    have hj : Nat.primeCounting (4 * P) <= j := by dsimp only [j]; omega
    have hiN : i < N := by have h := hi.1; omega
    have hupper : primeAt j <= 400 * P := primeAt_primeCounting_add_le_upper hiN
    have hgap : (primeGap j : Real) < (G : Real) := by exact_mod_cast hi.2
    have hceil : (G : Real) < 1.09 * log (400 * (P : Real)) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    exact Exists.intro j (And.intro hj (And.intro hupper (by linarith)))

end PrimeFactorUnimodality
