import PrimeFactorUnimodality.Helpers.Analytic.ExplicitPrimeCountingPart02


set_option autoImplicit false

/-! # Interfaces for explicit prime-counting estimates -/

namespace PrimeFactorUnimodality

noncomputable section

/-- Dusart's lower comparison function
`x / log x * (1 + 1 / log x)`. -/

/-! # ExplicitPrimeCounting source part 03

This module is a sequential source split of the analytic development.
-/

theorem explicit_integral_core_bound_at_large_cutoff
    {A X : Real} (hX : (4e18 : Real) ≤ X)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) :
    4000 +
        720 * ((999998 : Real) / Real.log 2 ^ 7 +
          (X / Real.log X ^ 7) /
            (1 - 7 / Real.log (1000000 : Real))) +
        A * ((999998 : Real) / Real.log 2 ^ 6 +
          (X / Real.log X ^ 6) /
            (1 - 6 / Real.log (1000000 : Real))) ≤
      (3 / 5 : Real) * X / Real.log X ^ 4 := by
  have hlog2 : (69 : Real) / 100 ≤ Real.log 2 := by
    exact (by norm_num : (69 : Real) / 100 < 0.6931471803).le.trans
      Real.log_two_gt_d9.le
  have hlogMillion : (13 : Real) ≤ Real.log (1000000 : Real) := by
    apply (Real.le_log_iff_exp_le (by positivity)).2
    have hexp : Real.exp 13 < (2.72 : Real) ^ 13 := by
      rw [show (13 : Real) = (13 : ℕ) * 1 by norm_num,
        Real.exp_nat_mul]
      exact pow_lt_pow_left₀ (by linarith [Real.exp_one_lt_d9])
        (Real.exp_pos 1).le (by norm_num)
    exact hexp.le.trans (by norm_num)
  have hlogCut : (42 : Real) ≤ Real.log (4e18 : Real) := by
    exact (by
      apply (le_of_lt ?_)
      apply (Real.lt_log_iff_exp_lt (by norm_num)).2
      have hexp : Real.exp 42 < (2.72 : Real) ^ 42 := by
        rw [show (42 : Real) = (42 : ℕ) * 1 by norm_num,
          Real.exp_nat_mul]
        exact pow_lt_pow_left₀ (by
          linarith [Real.exp_one_lt_d9]) (Real.exp_pos 1).le (by norm_num)
      exact hexp.trans (by norm_num))
  have hstrong := explicit_integral_core_bound_of_log_margins hX hA0 hA1 hlog2
    hlogMillion hlogCut (lower_bound_div_log_four_of_four_e18_le hX)
  linarith

theorem explicit_integral_core_bound_at_large_cutoff_with_10000
    {A X : Real} (hX : (4e18 : Real) ≤ X)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) :
    4000 +
        720 * ((999998 : Real) / Real.log 2 ^ 7 +
          (X / Real.log X ^ 7) /
            (1 - 7 / Real.log (1000000 : Real))) +
        A * ((999998 : Real) / Real.log 2 ^ 6 +
          (X / Real.log X ^ 6) /
            (1 - 6 / Real.log (1000000 : Real))) + 10000 ≤
      (3 / 5 : Real) * X / Real.log X ^ 4 := by
  have hlog2 : (69 : Real) / 100 ≤ Real.log 2 := by
    exact (by norm_num : (69 : Real) / 100 < 0.6931471803).le.trans
      Real.log_two_gt_d9.le
  have hlogMillion : (13 : Real) ≤ Real.log (1000000 : Real) := by
    apply (Real.le_log_iff_exp_le (by positivity)).2
    have hexp : Real.exp 13 < (2.72 : Real) ^ 13 := by
      rw [show (13 : Real) = (13 : ℕ) * 1 by norm_num,
        Real.exp_nat_mul]
      exact pow_lt_pow_left₀ (by linarith [Real.exp_one_lt_d9])
        (Real.exp_pos 1).le (by norm_num)
    exact hexp.le.trans (by norm_num)
  have hlogCut : (42 : Real) ≤ Real.log (4e18 : Real) := by
    exact (by
      apply (le_of_lt ?_)
      apply (Real.lt_log_iff_exp_lt (by norm_num)).2
      have hexp : Real.exp 42 < (2.72 : Real) ^ 42 := by
        rw [show (42 : Real) = (42 : ℕ) * 1 by norm_num,
          Real.exp_nat_mul]
        exact pow_lt_pow_left₀ (by
          linarith [Real.exp_one_lt_d9]) (Real.exp_pos 1).le (by norm_num)
      exact hexp.trans (by norm_num))
  exact explicit_integral_core_bound_of_log_margins hX hA0 hA1 hlog2
    hlogMillion hlogCut (lower_bound_div_log_four_of_four_e18_le hX)

theorem explicit_reserved_integral_core_at_599
    {A X : Real} (hX : (4e18 : Real) ≤ X)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) :
    4000 + 720 * (∫ t in (2 : Real)..X, 1 / Real.log t ^ 7) +
        10000 + A * (∫ t in (599 : Real)..X, 1 / Real.log t ^ 6) ≤
      (3 / 5 : Real) * X / Real.log X ^ 4 := by
  have hXmillion : (1000000 : Real) ≤ X := by
    norm_num at hX ⊢
    linarith
  have hseven := integral_inv_log_seven_le_explicit hXmillion
  have hsix := integral_inv_log_six_tail_from_599_le_explicit hXmillion
  have hmargin := explicit_integral_core_bound_at_large_cutoff_with_10000
    hX hA0 hA1
  have hseven' : (0 : Real) ≤ 720 := by norm_num
  have hsix' := mul_le_mul_of_nonneg_left hsix hA0
  nlinarith [mul_le_mul_of_nonneg_left hseven hseven']

theorem abs_integral_inv_log_pow_succ_le
    {n : Nat} {a b : Real} (ha : 1 < a) (hab : a ≤ b)
    (hcoef : (n + 1 : Real) < Real.log a) :
    |∫ t in a..b, 1 / Real.log t ^ (n + 1)| ≤
      (b / Real.log b ^ (n + 1)) /
        (1 - (n + 1 : Real) / Real.log a) := by
  have hfi : IntervalIntegrable
      (fun t : Real => 1 / Real.log t ^ (n + 1))
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.div continuousOn_const
    · exact (Real.continuousOn_log.mono fun y hy =>
        ne_of_gt (by linarith [hy.1])).pow _
    · intro y hy
      exact pow_ne_zero _ (ne_of_gt (Real.log_pos (by linarith [hy.1])))
  have hnonneg : ∀ t ∈ Set.Icc a b,
      0 ≤ 1 / Real.log t ^ (n + 1) := by
    intro t ht
    have hlog : 0 < Real.log t := Real.log_pos (lt_of_lt_of_le ha ht.1)
    exact one_div_nonneg.mpr (le_of_lt (pow_pos hlog _))
  have hpos : 0 ≤ ∫ t in a..b, 1 / Real.log t ^ (n + 1) := by
    have hzero : IntervalIntegrable (fun _ : Real => (0 : Real))
        MeasureTheory.volume a b := intervalIntegrable_const
    simpa using intervalIntegral.integral_mono_on hab hzero hfi hnonneg
  rw [abs_of_nonneg hpos]
  exact integral_inv_log_pow_succ_le ha hab hcoef

theorem theta_remainder_integral_tail_le_of_logFourthError
    {A X x : Real} (hX : 1 < X) (hA : 0 ≤ A)
    (error : HasThetaLogFourthError A X) (hax : X ≤ x)
    (hcoef : (6 : Real) < Real.log X) :
    |∫ t in X..x,
        (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
          1 / (Real.log t) ^ 2)| ≤
      A * (x / Real.log x ^ 6) /
        (1 - 6 / Real.log X) := by
  have htheta : IntervalIntegrable
      (fun t : Real => Chebyshev.theta t / (t * (Real.log t) ^ 2))
      MeasureTheory.volume X x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hax]
    have hX2 : 2 < X := by
      apply (Real.log_lt_log_iff (by norm_num) (by linarith [hX])).mp
      exact (Real.log_lt_sub_one_of_pos (by norm_num) (by norm_num)).trans
        (by linarith [hcoef])
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq x).mono_set
      (by
        intro y hy
        exact ⟨by linarith [hy.1, hX2], hy.2⟩)
  have hbase : IntervalIntegrable
      (fun t : Real => 1 / (Real.log t) ^ 2)
      MeasureTheory.volume X x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hax]
    apply ContinuousOn.div continuousOn_const
    · exact (Real.continuousOn_log.mono fun y hy =>
        ne_of_gt (by linarith [hy.1])).pow _
    · intro y hy
      exact pow_ne_zero _ (ne_of_gt (Real.log_pos (by linarith [hy.1])))
  let r : Real → Real := fun t =>
    Chebyshev.theta t / (t * (Real.log t) ^ 2) - 1 / (Real.log t) ^ 2
  have hr : IntervalIntegrable r MeasureTheory.volume X x := by
    simpa [r] using htheta.sub hbase
  have hmajor : IntervalIntegrable
      (fun t : Real => A / (Real.log t) ^ 6)
      MeasureTheory.volume X x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hax]
    apply ContinuousOn.div continuousOn_const
    · exact (Real.continuousOn_log.mono fun y hy =>
        ne_of_gt (by linarith [hy.1])).pow _
    · intro y hy
      exact pow_ne_zero _ (ne_of_gt (Real.log_pos (by linarith [hy.1])))
  have hmajor_bound : ∀ t ∈ Set.Icc X x, |r t| ≤ A / (Real.log t) ^ 6 := by
    intro t ht
    change |Chebyshev.theta t / (t * (Real.log t) ^ 2) -
      1 / (Real.log t) ^ 2| ≤ A / (Real.log t) ^ 6
    have htpos : 0 < t := by linarith [ht.1]
    have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hlogtne : Real.log t ≠ 0 := ne_of_gt hlogtpos
    have herr := error t ht.1
    have hrewrite :
        Chebyshev.theta t / (t * (Real.log t) ^ 2) -
            1 / (Real.log t) ^ 2 =
          (Chebyshev.theta t - t) / (t * (Real.log t) ^ 2) := by
      field_simp [ne_of_gt htpos, hlogtne]
    rw [hrewrite, abs_div]
    have hden : 0 ≤ t * (Real.log t) ^ 2 := by positivity
    rw [abs_of_nonneg hden]
    calc
      |Chebyshev.theta t - t| / (t * (Real.log t) ^ 2) ≤
          (A * t / (Real.log t) ^ 4) / (t * (Real.log t) ^ 2) :=
        div_le_div_of_nonneg_right herr hden
      _ = A / (Real.log t) ^ 6 := by
        field_simp [ne_of_gt htpos, hlogtne]
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    (μ := MeasureTheory.volume) (f := r) hax
  have hmono := intervalIntegral.integral_mono_on hax hr.norm hmajor hmajor_bound
  have hcoef' : (5 + 1 : Real) < Real.log X := by
    norm_num
    exact hcoef
  have htail := integral_inv_log_pow_succ_le (n := 5) hX hax hcoef'
  change |∫ t in X..x, r t| ≤ A * (x / Real.log x ^ 6) /
    (1 - 6 / Real.log X)
  calc
    |∫ t in X..x, r t| ≤ ∫ t in X..x, |r t| := hnorm
    _ ≤ ∫ t in X..x, A / (Real.log t) ^ 6 := hmono
    _ = A * (∫ t in X..x, 1 / (Real.log t) ^ 6) := by
      rw [show (fun t : Real => A / (Real.log t) ^ 6) =
        (fun t => A * (1 / (Real.log t) ^ 6)) by
          funext t
          ring]
      rw [intervalIntegral.integral_const_mul]
    _ ≤ A * ((x / Real.log x ^ 6) /
        (1 - 6 / Real.log X)) := by
      have hfactor : 0 ≤ A := hA
      convert mul_le_mul_of_nonneg_left htail hfactor using 1 <;> norm_num
    _ = A * (x / Real.log x ^ 6) /
        (1 - 6 / Real.log X) := by ring

theorem primeCounting_explicit_tail_le_of_logFourthError
    {A X x : Real} (hX : 1 < X) (hA : 0 ≤ A)
    (error : HasThetaLogFourthError A X) (hax : X ≤ x)
    (hcoef : (7 : Real) < Real.log X) :
    |720 * (∫ t in X..x, 1 / Real.log t ^ 7) +
        ∫ t in X..x,
          (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
            1 / (Real.log t) ^ 2)| ≤
      720 * ((x / Real.log x ^ 7) /
        (1 - 7 / Real.log X)) +
        A * (x / Real.log x ^ 6) /
          (1 - 6 / Real.log X) := by
  have hlog0 := abs_integral_inv_log_pow_succ_le (n := 6) hX hax (by
    norm_num
    exact hcoef)
  have hlog : |∫ t in X..x, 1 / Real.log t ^ 7| ≤
      (x / Real.log x ^ 7) / (1 - 7 / Real.log X) := by
    convert hlog0 using 1 <;> norm_num
  have htheta := theta_remainder_integral_tail_le_of_logFourthError
    hX hA error hax (by linarith)
  calc
    |720 * (∫ t in X..x, 1 / Real.log t ^ 7) +
          ∫ t in X..x,
            (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
              1 / (Real.log t) ^ 2)| ≤
        |720 * (∫ t in X..x, 1 / Real.log t ^ 7)| +
          |∫ t in X..x,
            (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
              1 / (Real.log t) ^ 2)| := abs_add_le _ _
    _ = 720 * |∫ t in X..x, 1 / Real.log t ^ 7| +
          |∫ t in X..x,
            (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
              1 / (Real.log t) ^ 2)| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 720)]
    _ ≤ 720 * ((x / Real.log x ^ 7) /
          (1 - 7 / Real.log X)) +
          A * (x / Real.log x ^ 6) /
            (1 - 6 / Real.log X) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hlog (by norm_num)) htheta

theorem integral_inv_log_sq_expansion_five
    {x : Real} (hx : 2 ≤ x) :
    ∫ t in Set.Icc 2 x, 1 / Real.log t ^ 2 =
      x / Real.log x ^ 2 + 2 * x / Real.log x ^ 3 +
        6 * x / Real.log x ^ 4 + 24 * x / Real.log x ^ 5 +
          120 * x / Real.log x ^ 6 -
        2 * (1 / Real.log 2 ^ 2 + 2 / Real.log 2 ^ 3 +
          6 / Real.log 2 ^ 4 + 24 / Real.log 2 ^ 5 +
          120 / Real.log 2 ^ 6) +
        720 * ∫ t in Set.Icc 2 x, 1 / Real.log t ^ 7 := by
  rw [integral_inv_log_pow_succ_eq (n := 1) hx,
    integral_inv_log_pow_succ_eq (n := 2) hx,
    integral_inv_log_pow_succ_eq (n := 3) hx,
    integral_inv_log_pow_succ_eq (n := 4) hx,
    integral_inv_log_pow_succ_eq (n := 5) hx]
  ring_nf

theorem integral_inv_log_sq_expansion_five_interval
    {x : Real} (hx : 2 ≤ x) :
    ∫ t in (2 : Real)..x, 1 / Real.log t ^ 2 =
      x / Real.log x ^ 2 + 2 * x / Real.log x ^ 3 +
        6 * x / Real.log x ^ 4 + 24 * x / Real.log x ^ 5 +
          120 * x / Real.log x ^ 6 -
        2 * (1 / Real.log 2 ^ 2 + 2 / Real.log 2 ^ 3 +
          6 / Real.log 2 ^ 4 + 24 / Real.log 2 ^ 5 +
          120 / Real.log 2 ^ 6) +
        720 * ∫ t in (2 : Real)..x, 1 / Real.log t ^ 7 := by
  simpa only [MeasureTheory.integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hx] using
    integral_inv_log_sq_expansion_five hx

theorem theta_integral_split
    {x : Real} (hx : 2 ≤ x) :
    (∫ t in (2 : Real)..x,
        Chebyshev.theta t / (t * (Real.log t) ^ 2)) =
      (∫ t in (2 : Real)..x, 1 / (Real.log t) ^ 2) +
        ∫ t in (2 : Real)..x,
          (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
            1 / (Real.log t) ^ 2) := by
  have htheta : IntervalIntegrable
      (fun t : Real => Chebyshev.theta t / (t * (Real.log t) ^ 2))
      MeasureTheory.volume 2 x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq x).mono_set
      (Set.Ioc_subset_Icc_self)
  have hbase : IntervalIntegrable
      (fun t : Real => 1 / (Real.log t) ^ 2) MeasureTheory.volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    apply ContinuousOn.div continuousOn_const
    · exact (Real.continuousOn_log.mono fun y hy =>
        ne_of_gt (by linarith [hy.1])).pow _
    · intro y hy
      exact pow_ne_zero _ (ne_of_gt (Real.log_pos (by linarith [hy.1])))
  have hsub := intervalIntegral.integral_sub htheta hbase
  have hpoint : (fun t : Real =>
      Chebyshev.theta t / (t * (Real.log t) ^ 2) - 1 / (Real.log t) ^ 2) =
      (fun t : Real => Chebyshev.theta t / (t * (Real.log t) ^ 2) -
        1 / (Real.log t) ^ 2) := rfl
  rw [hpoint] at hsub
  linarith

theorem primeCounting_from_theta_expansion_five
    {x : Real} (hx : 2 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : Real) =
      Chebyshev.theta x / Real.log x +
        x / Real.log x ^ 2 + 2 * x / Real.log x ^ 3 +
          6 * x / Real.log x ^ 4 + 24 * x / Real.log x ^ 5 +
            120 * x / Real.log x ^ 6 -
          2 * (1 / Real.log 2 ^ 2 + 2 / Real.log 2 ^ 3 +
            6 / Real.log 2 ^ 4 + 24 / Real.log 2 ^ 5 +
            120 / Real.log 2 ^ 6) +
          720 * (∫ t in (2 : Real)..x, 1 / Real.log t ^ 7) +
        ∫ t in (2 : Real)..x,
          (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
            1 / (Real.log t) ^ 2) := by
  calc
    (Nat.primeCounting ⌊x⌋₊ : Real) =
        Chebyshev.theta x / Real.log x +
          ∫ t in (2 : Real)..x,
            Chebyshev.theta t / (t * (Real.log t) ^ 2) :=
      primeCounting_from_theta_integral hx
    _ = Chebyshev.theta x / Real.log x +
          ((∫ t in (2 : Real)..x, 1 / (Real.log t) ^ 2) +
            ∫ t in (2 : Real)..x,
              (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
                1 / (Real.log t) ^ 2)) := by
      rw [theta_integral_split hx]
    _ = Chebyshev.theta x / Real.log x +
        x / Real.log x ^ 2 + 2 * x / Real.log x ^ 3 +
          6 * x / Real.log x ^ 4 + 24 * x / Real.log x ^ 5 +
            120 * x / Real.log x ^ 6 -
          2 * (1 / Real.log 2 ^ 2 + 2 / Real.log 2 ^ 3 +
            6 / Real.log 2 ^ 4 + 24 / Real.log 2 ^ 5 +
            120 / Real.log 2 ^ 6) +
          720 * (∫ t in (2 : Real)..x, 1 / Real.log t ^ 7) +
        ∫ t in (2 : Real)..x,
          (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
            1 / (Real.log t) ^ 2) := by
      have hmain := integral_inv_log_sq_expansion_five_interval hx
      calc
        Chebyshev.theta x / Real.log x +
              ((∫ t in (2 : Real)..x, 1 / (Real.log t) ^ 2) +
                ∫ t in (2 : Real)..x,
                  (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
                    1 / (Real.log t) ^ 2)) =
            Chebyshev.theta x / Real.log x +
              ((x / Real.log x ^ 2 + 2 * x / Real.log x ^ 3 +
                6 * x / Real.log x ^ 4 + 24 * x / Real.log x ^ 5 +
                120 * x / Real.log x ^ 6 -
                2 * (1 / Real.log 2 ^ 2 + 2 / Real.log 2 ^ 3 +
                  6 / Real.log 2 ^ 4 + 24 / Real.log 2 ^ 5 +
                  120 / Real.log 2 ^ 6) +
                720 * ∫ t in (2 : Real)..x, 1 / Real.log t ^ 7) +
                ∫ t in (2 : Real)..x,
                  (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
                    1 / (Real.log t) ^ 2)) := by
          exact congrArg (fun z : Real =>
            Chebyshev.theta x / Real.log x +
              (z + ∫ t in (2 : Real)..x,
                (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
                  1 / (Real.log t) ^ 2))) hmain
        _ = _ := by ring

/-! The expansion can be split at any explicit threshold.  This is the
non-numerical interface used by the later Dusart estimate: the interval
`2..X` is a fixed core, while all dependence on `x ≥ X` is in the two tails.
-/
theorem integral_inv_log_seven_split
    {X x : Real} (h2X : 2 ≤ X) (hXx : X ≤ x) :
    (∫ t in (2 : Real)..x, 1 / Real.log t ^ 7) =
      (∫ t in (2 : Real)..X, 1 / Real.log t ^ 7) +
        ∫ t in X..x, 1 / Real.log t ^ 7 := by
  have hcont : ContinuousOn (fun t : Real => 1 / Real.log t ^ 7)
      (Set.Icc 2 x) := by
    apply ContinuousOn.div continuousOn_const
    · exact (Real.continuousOn_log.mono fun y hy =>
        ne_of_gt (by linarith [hy.1])).pow _
    · intro y hy
      exact pow_ne_zero _ (ne_of_gt (Real.log_pos (by linarith [hy.1])))
  have hleft : IntervalIntegrable (fun t : Real => 1 / Real.log t ^ 7)
      MeasureTheory.volume 2 X := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h2X]
    exact hcont.mono (Set.Icc_subset_Icc le_rfl hXx)
  have hright : IntervalIntegrable (fun t : Real => 1 / Real.log t ^ 7)
      MeasureTheory.volume X x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hXx]
    exact hcont.mono (Set.Icc_subset_Icc h2X le_rfl)
  exact (intervalIntegral.integral_add_adjacent_intervals hleft hright).symm

theorem theta_remainder_integral_split
    {X x : Real} (h2X : 2 ≤ X) (hXx : X ≤ x) :
    (∫ t in (2 : Real)..x,
        (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
          1 / (Real.log t) ^ 2)) =
      (∫ t in (2 : Real)..X,
        (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
          1 / (Real.log t) ^ 2)) +
        ∫ t in X..x,
          (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
            1 / (Real.log t) ^ 2) := by
  have htheta : ∀ y : Real, 2 ≤ y →
      IntervalIntegrable
        (fun t : Real => Chebyshev.theta t / (t * (Real.log t) ^ 2))
        MeasureTheory.volume 2 y := by
    intro y hy
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hy]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq y).mono_set
      (Set.Ioc_subset_Icc_self)
  have hbase : ∀ y : Real, 2 ≤ y →
      IntervalIntegrable (fun t : Real => 1 / (Real.log t) ^ 2)
        MeasureTheory.volume 2 y := by
    intro y hy
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hy]
    apply ContinuousOn.div continuousOn_const
    · exact (Real.continuousOn_log.mono fun z hz =>
        ne_of_gt (by linarith [hz.1])).pow _
    · intro z hz
      exact pow_ne_zero _ (ne_of_gt (Real.log_pos (by linarith [hz.1])))
  have hrem : ∀ y : Real, 2 ≤ y →
      IntervalIntegrable
        (fun t : Real =>
          Chebyshev.theta t / (t * (Real.log t) ^ 2) -
            1 / (Real.log t) ^ 2)
        MeasureTheory.volume 2 y := by
    intro y hy
    exact (htheta y hy).sub (hbase y hy)
  have hright : IntervalIntegrable
      (fun t : Real =>
        Chebyshev.theta t / (t * (Real.log t) ^ 2) -
          1 / (Real.log t) ^ 2)
      MeasureTheory.volume X x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hXx]
    exact (hrem x (h2X.trans hXx)).1.mono_set (by
      intro z hz
      exact ⟨by linarith [hz.1, h2X], hz.2⟩)
  exact (intervalIntegral.integral_add_adjacent_intervals
    (hrem X h2X) hright).symm

theorem primeCounting_from_theta_expansion_five_split
    {X x : Real} (h2X : 2 ≤ X) (hXx : X ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : Real) =
      Chebyshev.theta x / Real.log x +
        x / Real.log x ^ 2 + 2 * x / Real.log x ^ 3 +
          6 * x / Real.log x ^ 4 + 24 * x / Real.log x ^ 5 +
            120 * x / Real.log x ^ 6 -
          2 * (1 / Real.log 2 ^ 2 + 2 / Real.log 2 ^ 3 +
            6 / Real.log 2 ^ 4 + 24 / Real.log 2 ^ 5 +
            120 / Real.log 2 ^ 6) +
          720 * ((∫ t in (2 : Real)..X, 1 / Real.log t ^ 7) +
            ∫ t in X..x, 1 / Real.log t ^ 7) +
        ((∫ t in (2 : Real)..X,
            (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
              1 / (Real.log t) ^ 2)) +
          ∫ t in X..x,
            (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
              1 / (Real.log t) ^ 2)) := by
  rw [primeCounting_from_theta_expansion_five (h2X.trans hXx),
    integral_inv_log_seven_split h2X hXx,
    theta_remainder_integral_split h2X hXx]

/-! A remainder-normalized form of the split expansion.  No estimate is hidden
here: this is just the exact identity in the shape needed for Dusart's
fourth-order error bound. -/
theorem primeCounting_remainder_split
    {X x : Real} (h2X : 2 ≤ X) (hXx : X ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : Real) -
        (x / Real.log x + x / Real.log x ^ 2 +
          2 * x / Real.log x ^ 3) =
      (Chebyshev.theta x - x) / Real.log x +
        6 * x / Real.log x ^ 4 + 24 * x / Real.log x ^ 5 +
          120 * x / Real.log x ^ 6 -
        2 * (1 / Real.log 2 ^ 2 + 2 / Real.log 2 ^ 3 +
          6 / Real.log 2 ^ 4 + 24 / Real.log 2 ^ 5 +
          120 / Real.log 2 ^ 6) +
        720 * ((∫ t in (2 : Real)..X, 1 / Real.log t ^ 7) +
          ∫ t in X..x, 1 / Real.log t ^ 7) +
        ((∫ t in (2 : Real)..X,
            (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
              1 / (Real.log t) ^ 2)) +
          ∫ t in X..x,
            (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
              1 / (Real.log t) ^ 2)) := by
  have hx : 2 ≤ x := h2X.trans hXx
  have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  rw [primeCounting_from_theta_expansion_five_split h2X hXx]
  field_simp [hlogx]
  ring

/-! The part independent of `x` after the threshold split.  Naming it makes
the remaining finite verification explicit rather than burying it in a
long asymptotic expression. -/
def primeCountingCore (X : Real) : Real :=
  -2 * (1 / Real.log 2 ^ 2 + 2 / Real.log 2 ^ 3 +
    6 / Real.log 2 ^ 4 + 24 / Real.log 2 ^ 5 +
    120 / Real.log 2 ^ 6) +
    720 * (∫ t in (2 : Real)..X, 1 / Real.log t ^ 7) +
    ∫ t in (2 : Real)..X,
      (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
        1 / (Real.log t) ^ 2)

/-! The core is separated into the three quantities that must be bounded in
the finite Abel estimate.  This is purely structural; no explicit prime
number theorem is hidden in the decomposition. -/
theorem primeCountingCore_abs_le (X : Real) :
    |primeCountingCore X| ≤
      2 * |1 / Real.log 2 ^ 2 + 2 / Real.log 2 ^ 3 +
        6 / Real.log 2 ^ 4 + 24 / Real.log 2 ^ 5 +
        120 / Real.log 2 ^ 6| +
      720 * |∫ t in (2 : Real)..X, 1 / Real.log t ^ 7| +
      |∫ t in (2 : Real)..X,
        (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
          1 / (Real.log t) ^ 2)| := by
  let k : Real := 1 / Real.log 2 ^ 2 + 2 / Real.log 2 ^ 3 +
    6 / Real.log 2 ^ 4 + 24 / Real.log 2 ^ 5 +
    120 / Real.log 2 ^ 6
  let i : Real := ∫ t in (2 : Real)..X, 1 / Real.log t ^ 7
  let j : Real := ∫ t in (2 : Real)..X,
    (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
      1 / (Real.log t) ^ 2)
  change |-2 * k + 720 * i + j| ≤ 2 * |k| + 720 * |i| + |j|
  calc
    |-2 * k + 720 * i + j| ≤ |-2 * k + 720 * i| + |j| :=
      abs_add_le _ _
    _ ≤ (|-2 * k| + |720 * i|) + |j| := by
      exact add_le_add_left (abs_add_le (-2 * k) (720 * i)) |j|
    _ = 2 * |k| + 720 * |i| + |j| := by
      rw [abs_mul, abs_mul]
      norm_num

theorem primeCountingCore_fixed_term_le :
    1 / Real.log 2 ^ 2 + 2 / Real.log 2 ^ 3 +
        6 / Real.log 2 ^ 4 + 24 / Real.log 2 ^ 5 +
        120 / Real.log 2 ^ 6 ≤ (2000 : Real) := by
  have hlog : (69 : Real) / 100 < Real.log 2 := by
    exact (by norm_num : (69 : Real) / 100 < 0.6931471803).trans
      Real.log_two_gt_d9
  have hp2 : ((69 : Real) / 100) ^ 2 ≤ (Real.log 2) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hlog.le 2
  have hp3 : ((69 : Real) / 100) ^ 3 ≤ (Real.log 2) ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hlog.le 3
  have hp4 : ((69 : Real) / 100) ^ 4 ≤ (Real.log 2) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) hlog.le 4
  have hp5 : ((69 : Real) / 100) ^ 5 ≤ (Real.log 2) ^ 5 :=
    pow_le_pow_left₀ (by norm_num) hlog.le 5
  have hp6 : ((69 : Real) / 100) ^ 6 ≤ (Real.log 2) ^ 6 :=
    pow_le_pow_left₀ (by norm_num) hlog.le 6
  have hi2 : 1 / (Real.log 2) ^ 2 ≤ 1 / ((69 : Real) / 100) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) hp2
  have hi3 : 1 / (Real.log 2) ^ 3 ≤ 1 / ((69 : Real) / 100) ^ 3 :=
    one_div_le_one_div_of_le (by positivity) hp3
  have hi4 : 1 / (Real.log 2) ^ 4 ≤ 1 / ((69 : Real) / 100) ^ 4 :=
    one_div_le_one_div_of_le (by positivity) hp4
  have hi5 : 1 / (Real.log 2) ^ 5 ≤ 1 / ((69 : Real) / 100) ^ 5 :=
    one_div_le_one_div_of_le (by positivity) hp5
  have hi6 : 1 / (Real.log 2) ^ 6 ≤ 1 / ((69 : Real) / 100) ^ 6 :=
    one_div_le_one_div_of_le (by positivity) hp6
  calc
    1 / Real.log 2 ^ 2 + 2 / Real.log 2 ^ 3 +
          6 / Real.log 2 ^ 4 + 24 / Real.log 2 ^ 5 +
          120 / Real.log 2 ^ 6 ≤
        1 / ((69 : Real) / 100) ^ 2 +
          2 / ((69 : Real) / 100) ^ 3 +
          6 / ((69 : Real) / 100) ^ 4 +
          24 / ((69 : Real) / 100) ^ 5 +
          120 / ((69 : Real) / 100) ^ 6 := by
      gcongr
    _ ≤ (2000 : Real) := by norm_num [div_eq_mul_inv]

theorem integral_inv_log_seven_nonneg {X : Real} (hX : (2 : Real) ≤ X) :
    0 ≤ ∫ t in (2 : Real)..X, 1 / Real.log t ^ 7 := by
  apply intervalIntegral.integral_nonneg hX
  intro t ht
  have hlog : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
  positivity

theorem primeCountingCore_abs_le_of_two_le {X : Real}
    (hX : (2 : Real) ≤ X) :
    |primeCountingCore X| ≤
      4000 + 720 * (∫ t in (2 : Real)..X, 1 / Real.log t ^ 7) +
      |∫ t in (2 : Real)..X,
        (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
          1 / (Real.log t) ^ 2)| := by
  have hk : 0 ≤ 1 / Real.log 2 ^ 2 + 2 / Real.log 2 ^ 3 +
      6 / Real.log 2 ^ 4 + 24 / Real.log 2 ^ 5 +
      120 / Real.log 2 ^ 6 := by positivity
  have hi : 0 ≤ ∫ t in (2 : Real)..X, 1 / Real.log t ^ 7 :=
    integral_inv_log_seven_nonneg hX
  have hdecomp := primeCountingCore_abs_le X
  rw [abs_of_nonneg hk, abs_of_nonneg hi] at hdecomp
  have hfixed := primeCountingCore_fixed_term_le
  nlinarith

/-! The Abel decomposition only consumes the absolute value of its integral
remainder.  Exposing that fact separately lets a finite certificate split the
small interval from the range where a sharp logarithmic theta estimate is
valid; it does not force the sharp estimate to hold at `x = 2`. -/
theorem primeCountingCore_abs_le_of_integral_remainder {X R : Real}
    (hX : (2 : Real) ≤ X)
    (hrem : |∫ t in (2 : Real)..X,
        (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
          1 / (Real.log t) ^ 2)| ≤
      R) :
    |primeCountingCore X| ≤
      4000 + 720 * (∫ t in (2 : Real)..X, 1 / Real.log t ^ 7) + R := by
  exact (primeCountingCore_abs_le_of_two_le hX).trans (by linarith)

theorem small_integral_remainder_le_ten_mul
    {x₀ : Real} (h2x₀ : (2 : Real) ≤ x₀) :
    |∫ t in (2 : Real)..x₀,
        (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
          1 / (Real.log t) ^ 2)| ≤ 10 * x₀ := by
  have htheta : IntervalIntegrable
      (fun t : Real => Chebyshev.theta t /
        (t * (Real.log t) ^ 2))
      MeasureTheory.volume 2 x₀ := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h2x₀]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq x₀).mono_set
      (by intro t ht; exact ⟨by linarith [ht.1], ht.2⟩)
  have hbase : IntervalIntegrable
      (fun t : Real => 1 / (Real.log t) ^ 2)
      MeasureTheory.volume 2 x₀ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h2x₀]
    apply ContinuousOn.div continuousOn_const
    · exact (Real.continuousOn_log.mono fun t ht =>
        ne_of_gt (by linarith [ht.1])).pow _
    · intro t ht
      exact pow_ne_zero _
        (ne_of_gt (Real.log_pos (by linarith [ht.1])))
  let r : Real → Real := fun t =>
    Chebyshev.theta t / (t * (Real.log t) ^ 2) -
      1 / (Real.log t) ^ 2
  have hr : IntervalIntegrable r MeasureTheory.volume 2 x₀ := by
    simpa [r] using htheta.sub hbase
  have hbound : ∀ t ∈ Set.Icc (2 : Real) x₀, |r t| ≤ 10 := by
    intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    have hlogpos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hlog2 : (69 : Real) / 100 ≤ Real.log 2 := by
      exact (by norm_num : (69 : Real) / 100 < 0.6931471803).le.trans
        Real.log_two_gt_d9.le
    have hlogmono : Real.log 2 ≤ Real.log t :=
      Real.log_le_log (by norm_num) ht.1
    have hloglower : (69 : Real) / 100 ≤ Real.log t := hlog2.trans hlogmono
    have hlog4 : Real.log 4 ≤ 2 := by
      rw [show (4 : Real) = 2 ^ (2 : Nat) by norm_num, Real.log_pow]
      norm_num
      nlinarith [Real.log_two_lt_d9]
    have hlogsq : (0 : Real) < (Real.log t) ^ 2 := sq_pos_of_pos hlogpos
    have hsquare : ((69 : Real) / 100) ^ 2 ≤ (Real.log t) ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self (by norm_num) hloglower
    have hinv : 1 / (Real.log t) ^ 2 ≤ 3 := by
      apply (div_le_iff₀ hlogsq).2
      nlinarith [hsquare]
    have htheta_upper := Chebyshev.theta_le_log4_mul_x (by linarith : 0 ≤ t)
    have hterm : 0 ≤ Chebyshev.theta t /
        (t * (Real.log t) ^ 2) := by positivity
    have hterm_upper : Chebyshev.theta t /
        (t * (Real.log t) ^ 2) ≤ 6 := by
      apply (div_le_iff₀ (mul_pos htpos hlogsq)).2
      have hcoef : Real.log 4 ≤ 6 * (Real.log t) ^ 2 := by
        nlinarith [hsquare, hlog4]
      have hscaled := mul_le_mul_of_nonneg_right hcoef
        (by linarith : (0 : Real) ≤ t)
      nlinarith [htheta_upper, hscaled]
    rw [show r t = Chebyshev.theta t /
      (t * (Real.log t) ^ 2) - 1 / (Real.log t) ^ 2 by rfl]
    have habs := abs_sub_le
      (Chebyshev.theta t / (t * (Real.log t) ^ 2)) 0
      (1 / (Real.log t) ^ 2)
    have habs' : |Chebyshev.theta t / (t * (Real.log t) ^ 2) -
        1 / (Real.log t) ^ 2| ≤
        Chebyshev.theta t / (t * (Real.log t) ^ 2) +
          1 / (Real.log t) ^ 2 := by
      calc
        |Chebyshev.theta t / (t * (Real.log t) ^ 2) -
            1 / (Real.log t) ^ 2| ≤
            |Chebyshev.theta t / (t * (Real.log t) ^ 2) - 0| +
              |0 - 1 / (Real.log t) ^ 2| := habs
        _ = Chebyshev.theta t / (t * (Real.log t) ^ 2) +
              1 / (Real.log t) ^ 2 := by
          rw [sub_zero, abs_of_nonneg hterm, zero_sub, abs_neg,
            abs_of_nonneg (by positivity)]
    calc
      |Chebyshev.theta t / (t * (Real.log t) ^ 2) -
          1 / (Real.log t) ^ 2| ≤
          Chebyshev.theta t / (t * (Real.log t) ^ 2) +
            1 / (Real.log t) ^ 2 := habs'
      _ ≤ (6 : Real) + 3 := add_le_add hterm_upper hinv
      _ ≤ 10 := by norm_num
  have hconst : IntervalIntegrable (fun _ : Real => (10 : Real))
      MeasureTheory.volume 2 x₀ := intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on
    h2x₀ hr.norm hconst hbound
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    (μ := MeasureTheory.volume) (f := r) h2x₀
  calc
    |∫ t in (2 : Real)..x₀, r t| ≤
        ∫ t in (2 : Real)..x₀, |r t| := hnorm
    _ ≤ ∫ t in (2 : Real)..x₀, (10 : Real) := hmono
    _ = 10 * (x₀ - 2) := by rw [intervalIntegral.integral_const]; ring
    _ ≤ 10 * x₀ := by nlinarith

theorem small_integral_remainder_le_5990 :
    |∫ t in (2 : Real)..(599 : Real),
        (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
          1 / (Real.log t) ^ 2)| ≤ (5990 : Real) := by
  convert small_integral_remainder_le_ten_mul (x₀ := (599 : Real))
    (by norm_num) using 1 <;> norm_num

end

end PrimeFactorUnimodality
