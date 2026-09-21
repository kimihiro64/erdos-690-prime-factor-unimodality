import PrimeFactorUnimodality.Helpers.Analytic.ExplicitPrimeCountingPart03


set_option autoImplicit false

/-! # Interfaces for explicit prime-counting estimates -/

namespace PrimeFactorUnimodality

noncomputable section

/-- Dusart's lower comparison function
`x / log x * (1 + 1 / log x)`. -/

theorem integral_remainder_abs_le_of_split_theta_error
    {A X x₀ R : Real} (h2x₀ : (2 : Real) ≤ x₀) (hx₀X : x₀ ≤ X)
    (hsmall : |∫ t in (2 : Real)..x₀,
        (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
          1 / (Real.log t) ^ 2)| ≤ R)
    (hA : 0 ≤ A)
    (error : HasThetaLogFourthErrorAbove A x₀) :
    |∫ t in (2 : Real)..X,
        (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
          1 / (Real.log t) ^ 2)| ≤
      R + A * (∫ t in x₀..X, 1 / Real.log t ^ 6) := by
  have h2X : (2 : Real) ≤ X := h2x₀.trans hx₀X
  have htheta : IntervalIntegrable
      (fun t : Real => Chebyshev.theta t /
        (t * (Real.log t) ^ 2))
      MeasureTheory.volume 2 X := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h2X]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq X).mono_set
      (by intro t ht; exact ⟨by linarith [ht.1], ht.2⟩)
  have hbase : IntervalIntegrable
      (fun t : Real => 1 / (Real.log t) ^ 2)
      MeasureTheory.volume 2 X := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h2X]
    apply ContinuousOn.div continuousOn_const
    · exact (Real.continuousOn_log.mono fun t ht =>
        ne_of_gt (by linarith [ht.1])).pow _
    · intro t ht
      exact pow_ne_zero _
        (ne_of_gt (Real.log_pos (by linarith [ht.1])))
  let r : Real → Real := fun t =>
    Chebyshev.theta t / (t * (Real.log t) ^ 2) -
      1 / (Real.log t) ^ 2
  have hr : IntervalIntegrable r MeasureTheory.volume 2 X := by
    simpa [r] using htheta.sub hbase
  have hsubset : Set.uIcc x₀ X ⊆ Set.uIcc (2 : Real) X := by
    rw [Set.uIcc_of_le hx₀X, Set.uIcc_of_le h2X]
    intro t ht
    exact ⟨h2x₀.trans ht.1, ht.2⟩
  have hrTail : IntervalIntegrable r MeasureTheory.volume x₀ X :=
    hr.mono_set hsubset
  have hmajor : IntervalIntegrable
      (fun t : Real => A / (Real.log t) ^ 6)
      MeasureTheory.volume x₀ X := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx₀X]
    apply ContinuousOn.div continuousOn_const
    · exact (Real.continuousOn_log.mono fun t ht =>
        ne_of_gt (by linarith [h2x₀.trans ht.1])).pow _
    · intro t ht
      exact pow_ne_zero _
        (ne_of_gt (Real.log_pos (by linarith [h2x₀.trans ht.1])))
  have hmajor_bound : ∀ t ∈ Set.Icc x₀ X,
      |r t| ≤ A / (Real.log t) ^ 6 := by
    intro t ht
    have htpos : 0 < t := by linarith [h2x₀, ht.1]
    have hlogpos : 0 < Real.log t := Real.log_pos (by linarith [h2x₀, ht.1])
    have herr := error t ht.1
    have hrewrite :
        Chebyshev.theta t / (t * (Real.log t) ^ 2) -
            1 / (Real.log t) ^ 2 =
          (Chebyshev.theta t - t) /
            (t * (Real.log t) ^ 2) := by
      field_simp [ne_of_gt htpos, ne_of_gt hlogpos]
    rw [show r t = (Chebyshev.theta t - t) /
      (t * (Real.log t) ^ 2) by exact hrewrite, abs_div]
    have hden : 0 ≤ t * (Real.log t) ^ 2 := by positivity
    rw [abs_of_nonneg hden]
    calc
      |Chebyshev.theta t - t| / (t * (Real.log t) ^ 2) ≤
          (A * t / (Real.log t) ^ 4) /
            (t * (Real.log t) ^ 2) :=
        div_le_div_of_nonneg_right herr hden
      _ = A / (Real.log t) ^ 6 := by
        field_simp [ne_of_gt htpos, ne_of_gt hlogpos]
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    (μ := MeasureTheory.volume) (f := r) hx₀X
  have hmono := intervalIntegral.integral_mono_on
    hx₀X hrTail.norm hmajor hmajor_bound
  have htail : |∫ t in x₀..X, r t| ≤
      A * (∫ t in x₀..X, 1 / Real.log t ^ 6) := by
    calc
      |∫ t in x₀..X, r t| ≤ ∫ t in x₀..X, |r t| := hnorm
      _ ≤ ∫ t in x₀..X, A / (Real.log t) ^ 6 := hmono
      _ = A * (∫ t in x₀..X, 1 / Real.log t ^ 6) := by
        rw [show (fun t : Real => A / (Real.log t) ^ 6) =
          (fun t : Real => A * (1 / (Real.log t) ^ 6)) by
            funext t; ring]
        rw [intervalIntegral.integral_const_mul]
  have hrPrefix : IntervalIntegrable r MeasureTheory.volume 2 x₀ :=
    hr.mono_set (by
      rw [Set.uIcc_of_le h2x₀, Set.uIcc_of_le h2X]
      intro t ht
      exact ⟨ht.1, ht.2.trans hx₀X⟩)
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    hrPrefix hrTail
  have hsmall' : |∫ t in (2 : Real)..x₀, r t| ≤ R := by
    simpa [r] using hsmall
  change |∫ t in (2 : Real)..X, r t| ≤ _
  rw [← hadd]
  exact (abs_add_le _ _).trans (add_le_add hsmall' htail)

theorem primeCountingCore_abs_le_of_split_theta_error
    {A X x₀ R : Real} (h2x₀ : (2 : Real) ≤ x₀) (hx₀X : x₀ ≤ X)
    (hsmall : |∫ t in (2 : Real)..x₀,
        (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
          1 / (Real.log t) ^ 2)| ≤ R)
    (hA : 0 ≤ A)
    (error : HasThetaLogFourthErrorAbove A x₀) :
    |primeCountingCore X| ≤
      4000 + 720 * (∫ t in (2 : Real)..X, 1 / Real.log t ^ 7) +
        R + A * (∫ t in x₀..X, 1 / Real.log t ^ 6) := by
  have hrem := integral_remainder_abs_le_of_split_theta_error
    h2x₀ hx₀X hsmall hA error
  have hcore := primeCountingCore_abs_le_of_integral_remainder
    (h2x₀.trans hx₀X) hrem
  linarith

theorem primeCountingCore_abs_le_of_finite_theta_error
    {A X : Real} (hX : (2 : Real) ≤ X) (hA : 0 ≤ A)
    (error : HasThetaLogFourthErrorBelow A X) :
    |primeCountingCore X| ≤
      4000 + 720 * (∫ t in (2 : Real)..X, 1 / Real.log t ^ 7) +
      A * (∫ t in (2 : Real)..X, 1 / Real.log t ^ 6) := by
  have htheta : IntervalIntegrable
      (fun t : Real => Chebyshev.theta t /
        (t * (Real.log t) ^ 2))
      MeasureTheory.volume 2 X := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hX]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq X).mono_set
      (by intro t ht; exact ⟨by linarith [ht.1], ht.2⟩)
  have hbase : IntervalIntegrable
      (fun t : Real => 1 / (Real.log t) ^ 2)
      MeasureTheory.volume 2 X := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hX]
    apply ContinuousOn.div continuousOn_const
    · exact (Real.continuousOn_log.mono fun t ht =>
        ne_of_gt (by linarith [ht.1])).pow _
    · intro t ht
      exact pow_ne_zero _
        (ne_of_gt (Real.log_pos (by linarith [ht.1])))
  let r : Real → Real := fun t =>
    Chebyshev.theta t / (t * (Real.log t) ^ 2) -
      1 / (Real.log t) ^ 2
  have hr : IntervalIntegrable r MeasureTheory.volume 2 X := by
    simpa [r] using htheta.sub hbase
  have hmajor : IntervalIntegrable
      (fun t : Real => A / (Real.log t) ^ 6)
      MeasureTheory.volume 2 X := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hX]
    apply ContinuousOn.div continuousOn_const
    · exact (Real.continuousOn_log.mono fun t ht =>
        ne_of_gt (by linarith [ht.1])).pow _
    · intro t ht
      exact pow_ne_zero _
        (ne_of_gt (Real.log_pos (by linarith [ht.1])))
  have hmajor_bound : ∀ t ∈ Set.Icc (2 : Real) X,
      |r t| ≤ A / (Real.log t) ^ 6 := by
    intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    have hlogpos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have herr := error t ht.1 ht.2
    have hrewrite :
        Chebyshev.theta t / (t * (Real.log t) ^ 2) -
            1 / (Real.log t) ^ 2 =
          (Chebyshev.theta t - t) /
            (t * (Real.log t) ^ 2) := by
      field_simp [ne_of_gt htpos, ne_of_gt hlogpos]
    rw [show r t = (Chebyshev.theta t - t) /
      (t * (Real.log t) ^ 2) by exact hrewrite, abs_div]
    have hden : 0 ≤ t * (Real.log t) ^ 2 := by positivity
    rw [abs_of_nonneg hden]
    calc
      |Chebyshev.theta t - t| / (t * (Real.log t) ^ 2) ≤
          (A * t / (Real.log t) ^ 4) /
            (t * (Real.log t) ^ 2) :=
        div_le_div_of_nonneg_right herr hden
      _ = A / (Real.log t) ^ 6 := by
        field_simp [ne_of_gt htpos, ne_of_gt hlogpos]
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    (μ := MeasureTheory.volume) (f := r) hX
  have hmono := intervalIntegral.integral_mono_on hX hr.norm hmajor hmajor_bound
  have hrem :
      |∫ t in (2 : Real)..X,
        (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
          1 / (Real.log t) ^ 2)| ≤
        A * (∫ t in (2 : Real)..X, 1 / Real.log t ^ 6) := by
    calc
      |∫ t in (2 : Real)..X, r t| ≤
          ∫ t in (2 : Real)..X, |r t| := hnorm
      _ ≤ ∫ t in (2 : Real)..X, A / (Real.log t) ^ 6 := hmono
      _ = A * (∫ t in (2 : Real)..X, 1 / Real.log t ^ 6) := by
        rw [show (fun t : Real => A / (Real.log t) ^ 6) =
          (fun t : Real => A * (1 / (Real.log t) ^ 6)) by
            funext t; ring]
        rw [intervalIntegral.integral_const_mul]
  have hdecomp := primeCountingCore_abs_le_of_two_le hX
  nlinarith

theorem primeCountingCore_abs_le_of_finite_theta_error_explicit
    {A X : Real} (hX : (1000000 : Real) ≤ X) (hA : 0 ≤ A)
    (error : HasThetaLogFourthErrorBelow A X) :
    |primeCountingCore X| ≤
      4000 +
        720 * ((999998 : Real) / Real.log 2 ^ 7 +
          (X / Real.log X ^ 7) /
            (1 - 7 / Real.log (1000000 : Real))) +
        A * ((999998 : Real) / Real.log 2 ^ 6 +
          (X / Real.log X ^ 6) /
            (1 - 6 / Real.log (1000000 : Real))) := by
  have hcore := primeCountingCore_abs_le_of_finite_theta_error
    (by linarith [hX]) hA error
  have hseven := integral_inv_log_seven_le_explicit hX
  have hsix := integral_inv_log_six_le_explicit hX
  have hseven' : (0 : Real) ≤ 720 := by norm_num
  exact hcore.trans (by
    nlinarith [mul_le_mul_of_nonneg_left hseven hseven',
      mul_le_mul_of_nonneg_left hsix hA])

/-! The finite theta estimate and the numerical integral margin now compose
into the exact core hypothesis consumed by the all-`k` Dusart assembly. -/
theorem primeCountingCore_abs_le_at_large_cutoff_of_theta_error
    {A X : Real} (hX : (4e18 : Real) ≤ X)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (error : HasThetaLogFourthErrorBelow A X) :
    |primeCountingCore X| ≤ (3 / 5 : Real) * X / Real.log X ^ 4 := by
  have hXmillion : (1000000 : Real) ≤ X := by
    norm_num at hX ⊢
    linarith
  exact (primeCountingCore_abs_le_of_finite_theta_error_explicit
      hXmillion hA0 error).trans
    (explicit_integral_core_bound_at_large_cutoff hX hA0 hA1)

theorem primeCountingCore_abs_plus_10000_le_at_large_cutoff_of_theta_error
    {A X : Real} (hX : (4e18 : Real) ≤ X)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (error : HasThetaLogFourthErrorBelow A X) :
    |primeCountingCore X| + 10000 ≤
      (3 / 5 : Real) * X / Real.log X ^ 4 := by
  have hXmillion : (1000000 : Real) ≤ X := by
    norm_num at hX ⊢
    linarith
  have hcore := primeCountingCore_abs_le_of_finite_theta_error_explicit
    hXmillion hA0 error
  have hmargin := explicit_integral_core_bound_at_large_cutoff_with_10000
    hX hA0 hA1
  nlinarith

theorem primeCountingCore_scale_le
    {C X x : Real} (hX : 1 < X) (hXx : X ≤ x)
    (hlogX : (4 : Real) < Real.log X) (hC : 0 ≤ C)
    (hcore : |primeCountingCore X| ≤ C * X / Real.log X ^ 4) :
    |primeCountingCore X| ≤ C * x / Real.log x ^ 4 := by
  have hkernel := id_div_log_pow_le_of_le (n := 3) hX hXx (by
    norm_num
    exact hlogX)
  calc
    |primeCountingCore X| ≤ C * X / Real.log X ^ 4 := hcore
    _ = C * (X / Real.log X ^ 4) := by ring
    _ ≤ C * (x / Real.log x ^ 4) :=
      mul_le_mul_of_nonneg_left hkernel hC
    _ = C * x / Real.log x ^ 4 := by ring

theorem primeCounting_remainder_core_tail_decomposition
    {X x : Real} (h2X : 2 ≤ X) (hXx : X ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : Real) -
        (x / Real.log x + x / Real.log x ^ 2 +
          2 * x / Real.log x ^ 3) =
      (Chebyshev.theta x - x) / Real.log x +
        6 * x / Real.log x ^ 4 + 24 * x / Real.log x ^ 5 +
          120 * x / Real.log x ^ 6 + primeCountingCore X +
        720 * (∫ t in X..x, 1 / Real.log t ^ 7) +
        ∫ t in X..x,
          (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
            1 / (Real.log t) ^ 2) := by
  rw [primeCounting_remainder_split h2X hXx]
  unfold primeCountingCore
  ring

theorem primeCounting_boundary_remainder_le
    {A X x : Real} (hX : 1 < X) (hXx : X ≤ x) (hA : 0 ≤ A)
    (herror : |Chebyshev.theta x - x| ≤ A * x / (Real.log x) ^ 4) :
    |(Chebyshev.theta x - x) / Real.log x +
        6 * x / Real.log x ^ 4 + 24 * x / Real.log x ^ 5 +
          120 * x / Real.log x ^ 6| ≤
      A * x / Real.log x ^ 5 + 6 * x / Real.log x ^ 4 +
        24 * x / Real.log x ^ 5 + 120 * x / Real.log x ^ 6 := by
  have hxpos : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have htheta :
      |(Chebyshev.theta x - x) / Real.log x| ≤
        A * x / Real.log x ^ 5 := by
    rw [abs_div, abs_of_pos hlogx]
    calc
      |Chebyshev.theta x - x| / Real.log x ≤
          (A * x / Real.log x ^ 4) / Real.log x :=
        div_le_div_of_nonneg_right herror hlogx.le
      _ = A * x / Real.log x ^ 5 := by
        field_simp [ne_of_gt hlogx]
  have h6 : 0 ≤ 6 * x / Real.log x ^ 4 := by positivity
  have h24 : 0 ≤ 24 * x / Real.log x ^ 5 := by positivity
  have h120 : 0 ≤ 120 * x / Real.log x ^ 6 := by positivity
  calc
    |(Chebyshev.theta x - x) / Real.log x +
          6 * x / Real.log x ^ 4 + 24 * x / Real.log x ^ 5 +
            120 * x / Real.log x ^ 6| ≤
        |(Chebyshev.theta x - x) / Real.log x| +
          |6 * x / Real.log x ^ 4 + 24 * x / Real.log x ^ 5 +
            120 * x / Real.log x ^ 6| := by
      calc
        |(Chebyshev.theta x - x) / Real.log x +
              6 * x / Real.log x ^ 4 + 24 * x / Real.log x ^ 5 +
                120 * x / Real.log x ^ 6| =
            |(Chebyshev.theta x - x) / Real.log x +
              (6 * x / Real.log x ^ 4 + 24 * x / Real.log x ^ 5 +
                120 * x / Real.log x ^ 6)| := by
                  congr 1
                  ring
        _ ≤ |(Chebyshev.theta x - x) / Real.log x| +
              |6 * x / Real.log x ^ 4 + 24 * x / Real.log x ^ 5 +
                120 * x / Real.log x ^ 6| := abs_add_le _ _
    _ = |(Chebyshev.theta x - x) / Real.log x| +
          (6 * x / Real.log x ^ 4 + 24 * x / Real.log x ^ 5 +
            120 * x / Real.log x ^ 6) := by
      rw [abs_of_nonneg (by linarith :
        0 ≤ 6 * x / Real.log x ^ 4 + 24 * x / Real.log x ^ 5 +
          120 * x / Real.log x ^ 6)]
    _ ≤ A * x / Real.log x ^ 5 + 6 * x / Real.log x ^ 4 +
          24 * x / Real.log x ^ 5 + 120 * x / Real.log x ^ 6 := by
      linarith

theorem primeCounting_remainder_abs_le_of_core_and_theta_error
    {A X x : Real} (hX : 1 < X) (h2X : 2 ≤ X) (hXx : X ≤ x)
    (hA : 0 ≤ A) (herror : |Chebyshev.theta x - x| ≤
      A * x / (Real.log x) ^ 4)
    (error : HasThetaLogFourthError A X)
    (hcoef : (7 : Real) < Real.log X) :
    |(Nat.primeCounting ⌊x⌋₊ : Real) -
        (x / Real.log x + x / Real.log x ^ 2 +
          2 * x / Real.log x ^ 3)| ≤
      A * x / Real.log x ^ 5 + 6 * x / Real.log x ^ 4 +
        24 * x / Real.log x ^ 5 + 120 * x / Real.log x ^ 6 +
        |primeCountingCore X| +
        720 * ((x / Real.log x ^ 7) /
          (1 - 7 / Real.log X)) +
        A * (x / Real.log x ^ 6) /
          (1 - 6 / Real.log X) := by
  have hboundary := primeCounting_boundary_remainder_le hX hXx hA herror
  have htail := primeCounting_explicit_tail_le_of_logFourthError
    hX hA error hXx hcoef
  calc
    |(Nat.primeCounting ⌊x⌋₊ : Real) -
          (x / Real.log x + x / Real.log x ^ 2 +
            2 * x / Real.log x ^ 3)| =
        |((Chebyshev.theta x - x) / Real.log x +
            6 * x / Real.log x ^ 4 + 24 * x / Real.log x ^ 5 +
              120 * x / Real.log x ^ 6) + primeCountingCore X +
          (720 * (∫ t in X..x, 1 / Real.log t ^ 7) +
            ∫ t in X..x,
          (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
                1 / (Real.log t) ^ 2))| := by
          rw [primeCounting_remainder_core_tail_decomposition h2X hXx]
          congr 1
          ring
    _ = |((Chebyshev.theta x - x) / Real.log x +
            6 * x / Real.log x ^ 4 + 24 * x / Real.log x ^ 5 +
              120 * x / Real.log x ^ 6) +
          (primeCountingCore X +
            (720 * (∫ t in X..x, 1 / Real.log t ^ 7) +
              ∫ t in X..x,
                (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
                  1 / (Real.log t) ^ 2)))| := by
          congr 1
          ring
    _ ≤ |(Chebyshev.theta x - x) / Real.log x +
          6 * x / Real.log x ^ 4 + 24 * x / Real.log x ^ 5 +
            120 * x / Real.log x ^ 6| +
          |primeCountingCore X +
            (720 * (∫ t in X..x, 1 / Real.log t ^ 7) +
              ∫ t in X..x,
                (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
                  1 / (Real.log t) ^ 2))| := by
          exact abs_add_le _ _
    _ ≤ |(Chebyshev.theta x - x) / Real.log x +
          6 * x / Real.log x ^ 4 + 24 * x / Real.log x ^ 5 +
            120 * x / Real.log x ^ 6| +
          (|primeCountingCore X| +
            |720 * (∫ t in X..x, 1 / Real.log t ^ 7) +
              ∫ t in X..x,
                (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
                  1 / (Real.log t) ^ 2)|) := by
          have hsplit := abs_add_le
            (primeCountingCore X)
            (720 * (∫ t in X..x, 1 / Real.log t ^ 7) +
              ∫ t in X..x,
                (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
                  1 / (Real.log t) ^ 2))
          exact add_le_add_right hsplit _
    _ = |(Chebyshev.theta x - x) / Real.log x +
          6 * x / Real.log x ^ 4 + 24 * x / Real.log x ^ 5 +
            120 * x / Real.log x ^ 6| +
          |primeCountingCore X| +
          |720 * (∫ t in X..x, 1 / Real.log t ^ 7) +
            ∫ t in X..x,
              (Chebyshev.theta t / (t * (Real.log t) ^ 2) -
                1 / (Real.log t) ^ 2)| := by
          ring
    _ ≤ A * x / Real.log x ^ 5 + 6 * x / Real.log x ^ 4 +
          24 * x / Real.log x ^ 5 + 120 * x / Real.log x ^ 6 +
          |primeCountingCore X| +
          720 * ((x / Real.log x ^ 7) /
            (1 - 7 / Real.log X)) +
          A * (x / Real.log x ^ 6) /
            (1 - 6 / Real.log X) := by
          linarith

theorem primeCounting_remainder_abs_le_of_core_and_logFourthError
    {A X x : Real} (hX : 1 < X) (h2X : 2 ≤ X) (hXx : X ≤ x)
    (hA : 0 ≤ A) (error : HasThetaLogFourthError A X)
    (hcoef : (7 : Real) < Real.log X) :
    |(Nat.primeCounting ⌊x⌋₊ : Real) -
        (x / Real.log x + x / Real.log x ^ 2 +
          2 * x / Real.log x ^ 3)| ≤
      A * x / Real.log x ^ 5 + 6 * x / Real.log x ^ 4 +
        24 * x / Real.log x ^ 5 + 120 * x / Real.log x ^ 6 +
        |primeCountingCore X| +
        720 * ((x / Real.log x ^ 7) /
          (1 - 7 / Real.log X)) +
        A * (x / Real.log x ^ 6) /
          (1 - 6 / Real.log X) := by
  exact primeCounting_remainder_abs_le_of_core_and_theta_error
    hX h2X hXx hA (error x hXx) error hcoef

theorem primeCounting_remainder_abs_le_of_scaled_core
    {A C X x : Real} (hX : 1 < X) (h2X : 2 ≤ X) (hXx : X ≤ x)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hlogX : (4 : Real) < Real.log X)
    (hcore : |primeCountingCore X| ≤ C * X / Real.log X ^ 4)
    (error : HasThetaLogFourthError A X)
    (hcoef : (7 : Real) < Real.log X) :
    |(Nat.primeCounting ⌊x⌋₊ : Real) -
        (x / Real.log x + x / Real.log x ^ 2 +
          2 * x / Real.log x ^ 3)| ≤
      A * x / Real.log x ^ 5 + 6 * x / Real.log x ^ 4 +
        24 * x / Real.log x ^ 5 + 120 * x / Real.log x ^ 6 +
        C * x / Real.log x ^ 4 +
        720 * ((x / Real.log x ^ 7) /
          (1 - 7 / Real.log X)) +
        A * (x / Real.log x ^ 6) /
          (1 - 6 / Real.log X) := by
  have hraw := primeCounting_remainder_abs_le_of_core_and_logFourthError
    hX h2X hXx hA error hcoef
  have hcore' := primeCountingCore_scale_le hX hXx hlogX hC hcore
  linarith

theorem primeCounting_remainder_abs_le_of_log_coefficient
    {A C X x : Real} (hX : 1 < X) (h2X : 2 ≤ X) (hXx : X ≤ x)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hlogX : (7 : Real) < Real.log X)
    (hcore : |primeCountingCore X| ≤ C * X / Real.log X ^ 4)
    (error : HasThetaLogFourthError A X) :
    |(Nat.primeCounting ⌊x⌋₊ : Real) -
        (x / Real.log x + x / Real.log x ^ 2 +
          2 * x / Real.log x ^ 3)| ≤
      (A / Real.log X) * (x / Real.log x ^ 4) +
        6 * (x / Real.log x ^ 4) +
        (24 / Real.log X) * (x / Real.log x ^ 4) +
        (120 / Real.log X ^ 2) * (x / Real.log x ^ 4) +
        C * (x / Real.log x ^ 4) +
        (720 / (Real.log X ^ 3 * (1 - 7 / Real.log X))) *
          (x / Real.log x ^ 4) +
        (A / (Real.log X ^ 2 * (1 - 6 / Real.log X))) *
          (x / Real.log x ^ 4) := by
  have hlogXpos : 0 < Real.log X := Real.log_pos hX
  have hcoef4 : (4 : Real) < Real.log X := by linarith
  have hraw := primeCounting_remainder_abs_le_of_scaled_core
    hX h2X hXx hA hC hcoef4 hcore error hlogX
  have hpow1 := id_div_log_pow_add_le (m := 1) hX hXx
  have hpow2 := id_div_log_pow_add_le (m := 2) hX hXx
  have hpow3 := id_div_log_pow_add_le (m := 3) hX hXx
  have hden7 : 0 < 1 - 7 / Real.log X := by
    rw [sub_pos]
    exact (div_lt_iff₀ hlogXpos).2 (by linarith)
  have hden6 : 0 < 1 - 6 / Real.log X := by
    rw [sub_pos]
    exact (div_lt_iff₀ hlogXpos).2 (by linarith)
  have h1 : A * x / Real.log x ^ 5 ≤
      (A / Real.log X) * (x / Real.log x ^ 4) := by
    have h := mul_le_mul_of_nonneg_left hpow1 hA
    convert h using 1 <;> norm_num <;> ring
  have h24 : 24 * x / Real.log x ^ 5 ≤
      (24 / Real.log X) * (x / Real.log x ^ 4) := by
    have h := mul_le_mul_of_nonneg_left hpow1 (by norm_num : (0 : Real) ≤ 24)
    convert h using 1 <;> norm_num <;> ring
  have h120 : 120 * x / Real.log x ^ 6 ≤
      (120 / Real.log X ^ 2) * (x / Real.log x ^ 4) := by
    have h := mul_le_mul_of_nonneg_left hpow2 (by norm_num : (0 : Real) ≤ 120)
    convert h using 1 <;> norm_num <;> ring
  have h720 : 720 * ((x / Real.log x ^ 7) /
        (1 - 7 / Real.log X)) ≤
      (720 / (Real.log X ^ 3 * (1 - 7 / Real.log X))) *
        (x / Real.log x ^ 4) := by
    have hfactor : 0 ≤ 720 / (1 - 7 / Real.log X) := by positivity
    have h := mul_le_mul_of_nonneg_left hpow3 hfactor
    convert h using 1 <;> norm_num <;>
      field_simp [ne_of_gt hlogXpos, ne_of_gt hden7] <;> ring
  have hAtail : A * (x / Real.log x ^ 6) /
        (1 - 6 / Real.log X) ≤
      (A / (Real.log X ^ 2 * (1 - 6 / Real.log X))) *
        (x / Real.log x ^ 4) := by
    have hfactor : 0 ≤ A / (1 - 6 / Real.log X) := by positivity
    have h := mul_le_mul_of_nonneg_left hpow2 hfactor
    convert h using 1 <;> norm_num <;>
      field_simp [ne_of_gt hlogXpos, ne_of_gt hden6] <;> ring
  have hcore' := primeCountingCore_scale_le hX hXx hcoef4 hC hcore
  ring_nf at hraw h1 h24 h120 h720 hAtail hcore' ⊢
  linarith

theorem log_coefficient_le_732
    {A C X : Real} (hA0 : 0 ≤ A) (hA : A ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hlog : (42 : Real) ≤ Real.log X) :
    A / Real.log X + 6 + 24 / Real.log X +
        120 / Real.log X ^ 2 + C +
        720 / (Real.log X ^ 3 * (1 - 7 / Real.log X)) +
        A / (Real.log X ^ 2 * (1 - 6 / Real.log X)) ≤
      (732 : Real) / 100 := by
  have hlogpos : 0 < Real.log X := lt_of_lt_of_le (by norm_num) hlog
  have h1 : A / Real.log X ≤ (1 : Real) / 42 := by
    calc
      A / Real.log X ≤ 1 / Real.log X :=
        div_le_div_of_nonneg_right hA hlogpos.le
      _ ≤ (1 : Real) / 42 :=
        one_div_le_one_div_of_le (by norm_num) hlog
  have h24 : 24 / Real.log X ≤ (24 : Real) / 42 := by
    exact div_le_div_of_nonneg_left
      (by norm_num) (by norm_num) hlog
  have hsq : (42 : Real) ^ 2 ≤ Real.log X ^ 2 := by
    exact pow_le_pow_left₀ (by norm_num) hlog 2
  have h120 : 120 / Real.log X ^ 2 ≤ (120 : Real) / 42 ^ 2 := by
    have hinv := one_div_le_one_div_of_le (by norm_num) hsq
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsq
  have h7div : 7 / Real.log X ≤ (1 : Real) / 6 := by
    apply (div_le_iff₀ hlogpos).2
    nlinarith
  have h6div : 6 / Real.log X ≤ (1 : Real) / 7 := by
    apply (div_le_iff₀ hlogpos).2
    nlinarith
  have hden7 : (5 : Real) / 6 ≤ 1 - 7 / Real.log X := by linarith
  have hden6 : (6 : Real) / 7 ≤ 1 - 6 / Real.log X := by linarith
  have hL3 : (42 : Real) ^ 3 ≤ Real.log X ^ 3 := by
    exact pow_le_pow_left₀ (by norm_num) hlog 3
  have hprod7 : (42 : Real) ^ 3 * (5 / 6 : Real) ≤
      Real.log X ^ 3 * (1 - 7 / Real.log X) := by
    exact mul_le_mul hL3 hden7 (by positivity) (by positivity)
  have hprod6 : (42 : Real) ^ 2 * (6 / 7 : Real) ≤
      Real.log X ^ 2 * (1 - 6 / Real.log X) := by
    exact mul_le_mul hsq hden6 (by positivity) (by positivity)
  have htail7 : 720 / (Real.log X ^ 3 * (1 - 7 / Real.log X)) ≤
      720 / ((42 : Real) ^ 3 * (5 / 6 : Real)) := by
    have h := one_div_le_one_div_of_le
      (by positivity : (0 : Real) < 42 ^ 3 * (5 / 6 : Real)) hprod7
    have hm := mul_le_mul_of_nonneg_left h (by norm_num : (0 : Real) ≤ 720)
    convert hm using 1 <;> ring
  have htailA : A / (Real.log X ^ 2 * (1 - 6 / Real.log X)) ≤
      1 / ((42 : Real) ^ 2 * (6 / 7 : Real)) := by
    calc
      A / (Real.log X ^ 2 * (1 - 6 / Real.log X)) ≤
          1 / (Real.log X ^ 2 * (1 - 6 / Real.log X)) := by
        exact div_le_div_of_nonneg_right hA
          (by positivity)
      _ ≤ 1 / ((42 : Real) ^ 2 * (6 / 7 : Real)) := by
        exact one_div_le_one_div_of_le
          (by positivity : (0 : Real) < 42 ^ 2 * (6 / 7 : Real)) hprod6
  norm_num at h1 h24 h120 htail7 htailA
  linarith

theorem primeCounting_remainder_abs_le_732
    {A C X x : Real} (hX : 1 < X) (h2X : 2 ≤ X) (hXx : X ≤ x)
    (hA0 : 0 ≤ A) (hA : A ≤ 1) (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hlog : (42 : Real) ≤ Real.log X)
    (hcore : |primeCountingCore X| ≤ C * X / Real.log X ^ 4)
    (error : HasThetaLogFourthError A X) :
    |(Nat.primeCounting ⌊x⌋₊ : Real) -
        (x / Real.log x + x / Real.log x ^ 2 +
          2 * x / Real.log x ^ 3)| ≤
      (732 : Real) / 100 * x / Real.log x ^ 4 := by
  have henv := primeCounting_remainder_abs_le_of_log_coefficient
    hX h2X hXx hA0 hC0 (by linarith) hcore error
  have hcoef := log_coefficient_le_732 hA0 hA hC0 hC hlog
  have hxpos : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hbase : 0 ≤ x / Real.log x ^ 4 := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hcoef hbase
  calc
    |(Nat.primeCounting ⌊x⌋₊ : Real) -
          (x / Real.log x + x / Real.log x ^ 2 +
            2 * x / Real.log x ^ 3)| ≤
        (A / Real.log X) * (x / Real.log x ^ 4) +
          6 * (x / Real.log x ^ 4) +
          (24 / Real.log X) * (x / Real.log x ^ 4) +
          (120 / Real.log X ^ 2) * (x / Real.log x ^ 4) +
          C * (x / Real.log x ^ 4) +
          (720 / (Real.log X ^ 3 * (1 - 7 / Real.log X))) *
            (x / Real.log x ^ 4) +
          (A / (Real.log X ^ 2 * (1 - 6 / Real.log X))) *
            (x / Real.log x ^ 4) := henv
    _ ≤ (732 : Real) / 100 * x / Real.log x ^ 4 := by
      convert hscaled using 1 <;> ring

theorem theta_remainder_pointwise_le_of_logFourthError
    {A X x : Real} (hX : 1 < X)
    (error : HasThetaLogFourthError A X) (hx : X ≤ x) :
    |Chebyshev.theta x / (x * (Real.log x) ^ 2) -
        1 / (Real.log x) ^ 2| ≤ A / (Real.log x) ^ 6 := by
  have hx_pos : 0 < x := by linarith
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogx_ne : Real.log x ≠ 0 := ne_of_gt hlogx_pos
  have herror := error x hx
  have hrewrite :
      Chebyshev.theta x / (x * (Real.log x) ^ 2) -
        1 / (Real.log x) ^ 2 =
        (Chebyshev.theta x - x) / (x * (Real.log x) ^ 2) := by
    field_simp [ne_of_gt hx_pos, hlogx_ne]
  rw [hrewrite, abs_div]
  have hden : 0 ≤ x * (Real.log x) ^ 2 := by positivity
  rw [abs_of_nonneg hden]
  calc
    |Chebyshev.theta x - x| / (x * (Real.log x) ^ 2) ≤
        (A * x / (Real.log x) ^ 4) / (x * (Real.log x) ^ 2) :=
      div_le_div_of_nonneg_right herror hden
    _ = A / (Real.log x) ^ 6 := by
      field_simp [ne_of_gt hx_pos, hlogx_ne]

/-- The exact explicit prime-counting statements needed downstream.  This
interface lets the structural argument compile independently of the eventual
proof of the analytic provider. -/
def HasDusartPrimeCountingBounds : Prop :=
  (∀ n : Nat, 599 ≤ n →
    dusartPiLower n ≤ (Nat.primeCounting n : Real)) ∧
  (∀ n : Nat, 2 ≤ n →
    (Nat.primeCounting n : Real) ≤ dusartPiUpper n)

/-! A real-variable form is convenient when importing an explicit analytic
estimate stated for `π x`.  The final tail lemmas use the natural-number form
above, so this adapter is kept here rather than repeated at each call site. -/
def HasDusartRealPrimeCountingBounds : Prop :=
  (∀ x : Real, 599 ≤ x →
    dusartPiLower x ≤ (Nat.primeCounting ⌊x⌋₊ : Real)) ∧
  (∀ x : Real, 2 ≤ x →
    (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x)

def HasDusartRealPrimeCountingBoundsBelow (X : Real) : Prop :=
  (∀ x : Real, 599 ≤ x → x ≤ X →
    dusartPiLower x ≤ (Nat.primeCounting ⌊x⌋₊ : Real)) ∧
  (∀ x : Real, 2 ≤ x → x ≤ X →
    (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x)

theorem hasDusartRealPrimeCountingBoundsBelow_mono
    {X Y : Real} (hXY : X ≤ Y)
    (finite : HasDusartRealPrimeCountingBoundsBelow Y) :
    HasDusartRealPrimeCountingBoundsBelow X := by
  constructor
  · intro x hx hX
    exact finite.1 x hx (hX.trans hXY)
  · intro x hx hX
    exact finite.2 x hx (hX.trans hXY)

def HasDusartRealPrimeCountingBoundsAbove (X : Real) : Prop :=
  (∀ x : Real, X ≤ x →
    dusartPiLower x ≤ (Nat.primeCounting ⌊x⌋₊ : Real)) ∧
  (∀ x : Real, X ≤ x →
    (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x)

/-! The prime-counting estimates are recorded in the paper in the simpler
denominator form below.  Keep that published interface separate from the
stronger comparison functions consumed by the tail proof; the conversion is
elementary and therefore belongs in the formalization rather than being
silently folded into an analytic assumption. -/
def HasDusartPublishedPrimeCountingBounds : Prop :=
  (∀ x : Real, (5393 : Real) < x →
    x / (Real.log x - 1) ≤ (Nat.primeCounting ⌊x⌋₊ : Real)) ∧
  (∀ x : Real, (60184 : Real) < x →
    (Nat.primeCounting ⌊x⌋₊ : Real) ≤ x / (Real.log x - (11 / 10 : Real)))

def HasDusartPublishedPrimeCountingBoundsBelow (X : Real) : Prop :=
  (∀ x : Real, (5393 : Real) < x → x ≤ X →
    x / (Real.log x - 1) ≤ (Nat.primeCounting ⌊x⌋₊ : Real)) ∧
  (∀ x : Real, (60184 : Real) < x → x ≤ X →
    (Nat.primeCounting ⌊x⌋₊ : Real) ≤ x / (Real.log x - (11 / 10 : Real)))

theorem hasDusartRealPrimeCountingBoundsAbove_of_published
    (published : HasDusartPublishedPrimeCountingBounds) :
    HasDusartRealPrimeCountingBoundsAbove (4e18 : Real) := by
  constructor
  · intro x hx
    have hx5393 : (5393 : Real) < x := by
      norm_num at hx ⊢
      linarith
    have hpublished := published.1 x hx5393
    have hlog := log_large_x_gt_ten hx
    have hlog_pos : 0 < Real.log x := by linarith
    have hx_pos : 0 < x := by linarith
    have hcomparison : dusartPiLower x ≤ x / (Real.log x - 1) := by
      dsimp [dusartPiLower]
      have hden : 0 < Real.log x - 1 := by linarith
      have hrewrite :
          x / Real.log x * (1 + 1 / Real.log x) =
            x * (Real.log x + 1) / (Real.log x) ^ 2 := by
        field_simp [ne_of_gt hlog_pos]
      rw [hrewrite]
      apply (div_le_div_iff₀ (sq_pos_of_pos hlog_pos) hden).2
      nlinarith [sq_nonneg (Real.log x - 1)]
    exact hcomparison.trans hpublished
  · intro x hx
    have hx60184 : (60184 : Real) < x := by
      norm_num at hx ⊢
      linarith
    have hpublished := published.2 x hx60184
    have hlog := log_large_x_gt_ten hx
    have hlog_pos : 0 < Real.log x := by linarith
    have hx_pos : 0 < x := by linarith
    have hcomparison : x / (Real.log x - (11 / 10 : Real)) ≤ dusartPiUpper x := by
      dsimp [dusartPiUpper]
      have hden : 0 < Real.log x - (11 / 10 : Real) := by linarith
      have hrewrite :
          x / (Real.log x - (11 / 10 : Real)) ≤
            x * (Real.log x + (6381 / 5000 : Real)) / (Real.log x) ^ 2 := by
        apply (div_le_div_iff₀ hden (sq_pos_of_pos hlog_pos)).2
        nlinarith [sq_nonneg (Real.log x - 1)]
      convert hrewrite using 1 <;> field_simp <;> ring
    exact hpublished.trans hcomparison

/-! A provider form matching Dusart's explicit asymptotic formula.  The
reduction below is deliberately arithmetic: once the asymptotic remainder is
kernel-checked, it supplies the two comparison bounds used by the tail. -/

end

end PrimeFactorUnimodality
