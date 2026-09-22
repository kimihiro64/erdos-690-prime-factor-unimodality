import Mathlib.NumberTheory.Chebyshev
import PrimeFactorUnimodality.Helpers.Analytic.ElementaryLogBounds
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitThetaBounds

set_option autoImplicit false

/-! # Dusart's prime-power decomposition and large exponent range

Analytic power-sum proofs independent of finite endpoint and coefficient tables.
-/

namespace PrimeFactorUnimodality

noncomputable section

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

/- Integer-power certificates can bound each real power in the intermediate
   exponent range without asking the kernel to approximate an irrational root. -/
theorem dusart_rpow_ratio_bound
    {x b q : Real} {k : Nat}
    (hb : 1 ≤ b) (hbx : b ≤ x) (hk : 3 ≤ k)
    (hq0 : 0 ≤ q)
    (hq : 1 ≤ q ^ (3 * k) * b ^ (k - 3)) :
    x ^ (1 / (k : Real)) ≤ q * x ^ (1 / (3 : Real)) := by
  have hx : 0 < x := lt_of_lt_of_le (by linarith) hbx
  have hpow_base : b ^ (k - 3) ≤ x ^ (k - 3) := by
    exact pow_le_pow_left₀ (by linarith) hbx _
  have hprod : 1 ≤ q ^ (3 * k) * x ^ (k - 3) := by
    calc
      (1 : Real) ≤ q ^ (3 * k) * b ^ (k - 3) := hq
      _ ≤ q ^ (3 * k) * x ^ (k - 3) := by
        gcongr
  have hpow_nat : x ^ 3 ≤ q ^ (3 * k) * x ^ k := by
    calc
      x ^ 3 = x ^ 3 * 1 := by ring
      _ ≤ x ^ 3 * (q ^ (3 * k) * x ^ (k - 3)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = q ^ (3 * k) * x ^ (3 + (k - 3)) := by rw [pow_add]; ring
      _ = q ^ (3 * k) * x ^ k := by rw [show 3 + (k - 3) = k by omega]
  have hk0 : (k : Real) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hleft : (x ^ (1 / (k : Real))) ^ (3 * k) = x ^ (3 : Nat) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    rw [show (1 / (k : Real)) * ((3 * k : Nat) : Real) = 3 by
      push_cast; field_simp]
    norm_num
  have hright : (x ^ (1 / (3 : Real))) ^ (3 * k) = x ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    rw [show (1 / (3 : Real)) * ((3 * k : Nat) : Real) = k by push_cast; ring]
    exact Real.rpow_natCast x k
  have hpow :
      (x ^ (1 / (k : Real))) ^ (3 * k) ≤
        (q * x ^ (1 / (3 : Real))) ^ (3 * k) := by
    rw [hleft, mul_pow, hright]
    exact hpow_nat
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity)
    (show 3 * k ≠ 0 by omega)).mp hpow

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

theorem dusart_lemma_3_3_large
    {x : Real} (hx : (10 ^ 11 : Real) ^ 3 ≤ x)
    (theta_upper : ∀ y : Real, 0 < y →
      Chebyshev.theta y < (1000081 : Real) / 1000000 * y) :
    Chebyshev.psi x - Chebyshev.theta x -
        Chebyshev.theta (Real.sqrt x) <
      (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_large_of_count hx
    (dusart_floor_log_div_two_le_rpow hx) theta_upper

end

end PrimeFactorUnimodality
