import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.PrimeCounting
import PrimeFactorUnimodality.Helpers.PrimeSequence.AverageGap
import PrimeFactorUnimodality.Helpers.Analytic.ShortIntervalPrime

set_option autoImplicit false

/-! # Interfaces for explicit prime-counting estimates -/

namespace PrimeFactorUnimodality

noncomputable section

/-- Dusart's lower comparison function
`x / log x * (1 + 1 / log x)`. -/
def dusartPiLower (x : Real) : Real :=
  x / Real.log x * (1 + 1 / Real.log x)

/-- Dusart's upper comparison function
`x / log x * (1 + 1.2762 / log x)`, with the decimal represented exactly. -/
def dusartPiUpper (x : Real) : Real :=
  x / Real.log x * (1 + (6381 / 5000 : Real) / Real.log x)

/-! The exact Abel-summation identity underlying the prime-counting
asymptotic.  Keeping the identity in this namespace makes the later
remainder estimates explicit instead of treating `π` as an opaque provider. -/
theorem primeCounting_from_theta_integral {x : Real} (hx : 2 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : Real) =
      Chebyshev.theta x / Real.log x +
        ∫ t in (2 : Real)..x,
          Chebyshev.theta t / (t * (Real.log t) ^ 2) := by
  exact Chebyshev.primeCounting_eq_theta_div_log_add_integral hx

/-! A first explicit integration-by-parts identity.  This is the analytic
piece needed to turn the exact Abel identity above into a finite asymptotic
expansion; it is proved here rather than imported from an estimate library. -/
theorem integral_inv_log_sq_eq
    {x : Real} (hx : 2 ≤ x) :
    ∫ t in Set.Icc 2 x, 1 / Real.log t ^ 2 =
      x / Real.log x ^ 2 - 2 / Real.log 2 ^ 2 +
        2 * ∫ t in Set.Icc 2 x, 1 / Real.log t ^ 3 := by
  suffices h_ibp : ∀ a b : Real, 2 ≤ a → a ≤ b →
      ∫ t in a..b, (1 / (Real.log t) ^ 2) =
        (b / (Real.log b) ^ 2) - (a / (Real.log a) ^ 2) +
          2 * ∫ t in a..b, (1 / (Real.log t) ^ 3) by
    simpa only [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hx] using h_ibp 2 x (by norm_num) hx
  intro a b ha hab
  have h_deriv : ∀ t ∈ Set.Icc a b,
      deriv (fun t ↦ t / (Real.log t) ^ 2) t =
        1 / (Real.log t) ^ 2 - 2 * (1 / (Real.log t) ^ 3) := by
    intro t ht
    norm_num [Real.differentiableAt_log,
      ne_of_gt (show 0 < Real.log t from Real.log_pos <| by linarith [ht.1]),
      ne_of_gt (show 0 < t from by linarith [ht.1])]
    ring_nf
    grind
  have h_ftc : ∫ t in a..b, deriv (fun t ↦ t / (Real.log t) ^ 2) t =
      (b / (Real.log b) ^ 2) - (a / (Real.log a) ^ 2) := by
    rw [intervalIntegral.integral_deriv_eq_sub']
    · rfl
    · exact fun y hy ↦ DifferentiableAt.div differentiableAt_id
        (DifferentiableAt.pow (Real.differentiableAt_log
          (by cases Set.mem_uIcc.mp hy <;> linarith)) _)
        (pow_ne_zero _ <| ne_of_gt <| Real.log_pos <|
          by cases Set.mem_uIcc.mp hy <;> linarith)
    · rw [Set.uIcc_of_le hab]
      have hlog_cont := Real.continuousOn_log.mono fun y (hy : y ∈ Set.Icc a b) ↦
        ne_of_gt <| by linarith [hy.1]
      have hpow_ne : ∀ n : Nat, ∀ y ∈ Set.Icc a b,
          Real.log y ^ n ≠ 0 :=
        fun n y hy ↦ pow_ne_zero n <| ne_of_gt <| Real.log_pos <|
          by linarith [hy.1]
      exact ContinuousOn.congr (ContinuousOn.sub
        (continuousOn_const.div (hlog_cont.pow _) (hpow_ne _))
        (continuousOn_const.mul <| continuousOn_const.div
          (hlog_cont.pow _) (hpow_ne _))) h_deriv
  rw [← h_ftc, intervalIntegral.integral_congr fun t ht =>
    h_deriv t <| by simpa [hab] using ht]
  rw [intervalIntegral.integral_sub]
  · norm_num
  · exact ContinuousOn.intervalIntegrable (continuousOn_of_forall_continuousAt
      fun y hy ↦ ContinuousAt.div continuousAt_const
        (ContinuousAt.pow (Real.continuousAt_log
          (by linarith [Set.mem_Icc.mp (by simpa [hab] using hy)])) _)
        (ne_of_gt (pow_pos (Real.log_pos
          (by linarith [Set.mem_Icc.mp (by simpa [hab] using hy)])) _)))
  · exact ContinuousOn.intervalIntegrable
      (continuousOn_const.mul <| continuousOn_of_forall_continuousAt
        fun y hy ↦ ContinuousAt.div continuousAt_const
          (ContinuousAt.pow (Real.continuousAt_log
            (by linarith [Set.mem_Icc.mp (by simpa [hab] using hy)])) _)
          (ne_of_gt (pow_pos (Real.log_pos
            (by linarith [Set.mem_Icc.mp (by simpa [hab] using hy)])) _)))

theorem integral_inv_log_cubed_eq
    {x : Real} (hx : 2 ≤ x) :
    ∫ t in Set.Icc 2 x, 1 / Real.log t ^ 3 =
      x / Real.log x ^ 3 - 2 / Real.log 2 ^ 3 +
        3 * ∫ t in Set.Icc 2 x, 1 / Real.log t ^ 4 := by
  suffices h_ibp : ∀ a b : Real, 2 ≤ a → a ≤ b →
      ∫ t in a..b, (1 / (Real.log t) ^ 3) =
        (b / (Real.log b) ^ 3) - (a / (Real.log a) ^ 3) +
          3 * ∫ t in a..b, (1 / (Real.log t) ^ 4) by
    simpa only [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hx] using h_ibp 2 x (by norm_num) hx
  intro a b ha hab
  have h_deriv : ∀ t ∈ Set.Icc a b,
      deriv (fun t ↦ t / (Real.log t) ^ 3) t =
        1 / (Real.log t) ^ 3 - 3 * (1 / (Real.log t) ^ 4) := by
    intro t ht
    norm_num [Real.differentiableAt_log,
      ne_of_gt (show 0 < Real.log t from Real.log_pos <| by linarith [ht.1]),
      ne_of_gt (show 0 < t from by linarith [ht.1])]
    ring_nf
    grind
  have h_ftc : ∫ t in a..b, deriv (fun t ↦ t / (Real.log t) ^ 3) t =
      (b / (Real.log b) ^ 3) - (a / (Real.log a) ^ 3) := by
    rw [intervalIntegral.integral_deriv_eq_sub']
    · rfl
    · exact fun y hy ↦ DifferentiableAt.div differentiableAt_id
        (DifferentiableAt.pow (Real.differentiableAt_log
          (by cases Set.mem_uIcc.mp hy <;> linarith)) _)
        (pow_ne_zero _ <| ne_of_gt <| Real.log_pos <|
          by cases Set.mem_uIcc.mp hy <;> linarith)
    · rw [Set.uIcc_of_le hab]
      have hlog_cont := Real.continuousOn_log.mono fun y (hy : y ∈ Set.Icc a b) ↦
        ne_of_gt <| by linarith [hy.1]
      have hpow_ne : ∀ n : Nat, ∀ y ∈ Set.Icc a b,
          Real.log y ^ n ≠ 0 :=
        fun n y hy ↦ pow_ne_zero n <| ne_of_gt <| Real.log_pos <|
          by linarith [hy.1]
      exact ContinuousOn.congr (ContinuousOn.sub
        (continuousOn_const.div (hlog_cont.pow _) (hpow_ne _))
        (continuousOn_const.mul <| continuousOn_const.div
          (hlog_cont.pow _) (hpow_ne _))) h_deriv
  rw [← h_ftc, intervalIntegral.integral_congr fun t ht =>
    h_deriv t <| by simpa [hab] using ht]
  rw [intervalIntegral.integral_sub]
  · norm_num
  · exact ContinuousOn.intervalIntegrable (continuousOn_of_forall_continuousAt
      fun y hy ↦ ContinuousAt.div continuousAt_const
        (ContinuousAt.pow (Real.continuousAt_log
          (by linarith [Set.mem_Icc.mp (by simpa [hab] using hy)])) _)
        (ne_of_gt (pow_pos (Real.log_pos
          (by linarith [Set.mem_Icc.mp (by simpa [hab] using hy)])) _)))
  · exact ContinuousOn.intervalIntegrable
      (continuousOn_const.mul <| continuousOn_of_forall_continuousAt
        fun y hy ↦ ContinuousAt.div continuousAt_const
          (ContinuousAt.pow (Real.continuousAt_log
            (by linarith [Set.mem_Icc.mp (by simpa [hab] using hy)])) _)
          (ne_of_gt (pow_pos (Real.log_pos
            (by linarith [Set.mem_Icc.mp (by simpa [hab] using hy)])) _)))

theorem deriv_log_power_kernel
    {n : Nat} {t : Real} (ht : 1 < t) :
    deriv (fun y : Real => y / (Real.log y) ^ (n + 1)) t =
      1 / (Real.log t) ^ (n + 1) -
        (n + 1 : Real) * (1 / (Real.log t) ^ (n + 2)) := by
  have htpos : 0 < t := by linarith
  have hlogpos : 0 < Real.log t := Real.log_pos ht
  have hlogne : Real.log t ≠ 0 := ne_of_gt hlogpos
  have hderiv := (hasDerivAt_id t).div
    ((Real.hasDerivAt_log (ne_of_gt htpos)).pow (n + 1))
    (pow_ne_zero _ hlogne)
  convert hderiv.deriv using 1
  · rfl
  · simp only [id_eq, Pi.pow_apply]
    rw [show n + 1 - 1 = n by omega]
    field_simp [hlogne]
    rw [pow_succ]
    ring_nf
    norm_num [Nat.cast_add, Nat.cast_one]
    ring

theorem integral_inv_log_pow_succ_eq
    {n : Nat} {x : Real} (hx : 2 ≤ x) :
    ∫ t in Set.Icc 2 x, 1 / Real.log t ^ (n + 1) =
      x / Real.log x ^ (n + 1) - 2 / Real.log 2 ^ (n + 1) +
        (n + 1 : Real) *
          ∫ t in Set.Icc 2 x, 1 / Real.log t ^ (n + 2) := by
  suffices h_ibp : ∀ a b : Real, 2 ≤ a → a ≤ b →
      ∫ t in a..b, (1 / (Real.log t) ^ (n + 1)) =
        (b / (Real.log b) ^ (n + 1)) -
          (a / (Real.log a) ^ (n + 1)) +
          (n + 1 : Real) *
            ∫ t in a..b, (1 / (Real.log t) ^ (n + 2)) by
    simpa only [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hx] using h_ibp 2 x (by norm_num) hx
  intro a b ha hab
  have h_deriv : ∀ t ∈ Set.Icc a b,
      deriv (fun t ↦ t / (Real.log t) ^ (n + 1)) t =
        1 / (Real.log t) ^ (n + 1) -
          (n + 1 : Real) * (1 / (Real.log t) ^ (n + 2)) := by
    intro t ht
    exact deriv_log_power_kernel (n := n) (by linarith [ht.1])
  have h_ftc : ∫ t in a..b,
      deriv (fun t ↦ t / (Real.log t) ^ (n + 1)) t =
      (b / (Real.log b) ^ (n + 1)) -
        (a / (Real.log a) ^ (n + 1)) := by
    rw [intervalIntegral.integral_deriv_eq_sub']
    · rfl
    · exact fun y hy ↦ DifferentiableAt.div differentiableAt_id
        (DifferentiableAt.pow (Real.differentiableAt_log
          (by cases Set.mem_uIcc.mp hy <;> linarith)) _)
        (pow_ne_zero _ <| ne_of_gt <| Real.log_pos <|
          by cases Set.mem_uIcc.mp hy <;> linarith)
    · rw [Set.uIcc_of_le hab]
      have hlog_cont := Real.continuousOn_log.mono
        fun y (hy : y ∈ Set.Icc a b) ↦ ne_of_gt <| by linarith [hy.1]
      have hpow_ne : ∀ m : Nat, ∀ y ∈ Set.Icc a b,
          Real.log y ^ m ≠ 0 :=
        fun m y hy ↦ pow_ne_zero m <| ne_of_gt <| Real.log_pos <|
          by linarith [hy.1]
      exact ContinuousOn.congr (ContinuousOn.sub
        (continuousOn_const.div (hlog_cont.pow _) (hpow_ne _))
        (continuousOn_const.mul <| continuousOn_const.div
          (hlog_cont.pow _) (hpow_ne _))) h_deriv
  rw [← h_ftc, intervalIntegral.integral_congr fun t ht =>
    h_deriv t <| by simpa [hab] using ht]
  rw [intervalIntegral.integral_sub]
  · norm_num
  · exact ContinuousOn.intervalIntegrable (continuousOn_of_forall_continuousAt
      fun y hy ↦ ContinuousAt.div continuousAt_const
        (ContinuousAt.pow (Real.continuousAt_log
          (by linarith [Set.mem_Icc.mp (by simpa [hab] using hy)])) _)
        (ne_of_gt (pow_pos (Real.log_pos
          (by linarith [Set.mem_Icc.mp (by simpa [hab] using hy)])) _)))
  · exact ContinuousOn.intervalIntegrable
      (continuousOn_const.mul <| continuousOn_of_forall_continuousAt
        fun y hy ↦ ContinuousAt.div continuousAt_const
          (ContinuousAt.pow (Real.continuousAt_log
            (by linarith [Set.mem_Icc.mp (by simpa [hab] using hy)])) _)
          (ne_of_gt (pow_pos (Real.log_pos
            (by linarith [Set.mem_Icc.mp (by simpa [hab] using hy)])) _)))

theorem integral_inv_log_pow_succ_eq_interval
    {n : Nat} {a b : Real} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, 1 / Real.log t ^ (n + 1) =
      b / Real.log b ^ (n + 1) - a / Real.log a ^ (n + 1) +
        (n + 1 : Real) *
          ∫ t in a..b, 1 / Real.log t ^ (n + 2) := by
  have h_deriv : ∀ t ∈ Set.Icc a b,
      deriv (fun t ↦ t / (Real.log t) ^ (n + 1)) t =
        1 / (Real.log t) ^ (n + 1) -
          (n + 1 : Real) * (1 / (Real.log t) ^ (n + 2)) := by
    intro t ht
    exact deriv_log_power_kernel (n := n) (by linarith [ht.1])
  have h_ftc : ∫ t in a..b,
      deriv (fun t ↦ t / (Real.log t) ^ (n + 1)) t =
      (b / (Real.log b) ^ (n + 1)) -
        (a / (Real.log a) ^ (n + 1)) := by
    rw [intervalIntegral.integral_deriv_eq_sub']
    · rfl
    · exact fun y hy ↦ DifferentiableAt.div differentiableAt_id
        (DifferentiableAt.pow (Real.differentiableAt_log
          (by cases Set.mem_uIcc.mp hy <;> linarith)) _)
        (pow_ne_zero _ <| ne_of_gt <| Real.log_pos <|
          by cases Set.mem_uIcc.mp hy <;> linarith)
    · rw [Set.uIcc_of_le hab]
      have hlog_cont := Real.continuousOn_log.mono
        fun y (hy : y ∈ Set.Icc a b) ↦ ne_of_gt <| by linarith [hy.1]
      have hpow_ne : ∀ m : Nat, ∀ y ∈ Set.Icc a b,
          Real.log y ^ m ≠ 0 :=
        fun m y hy ↦ pow_ne_zero m <| ne_of_gt <| Real.log_pos <|
          by linarith [hy.1]
      exact ContinuousOn.congr (ContinuousOn.sub
        (continuousOn_const.div (hlog_cont.pow _) (hpow_ne _))
        (continuousOn_const.mul <| continuousOn_const.div
          (hlog_cont.pow _) (hpow_ne _))) h_deriv
  rw [← h_ftc, intervalIntegral.integral_congr fun t ht =>
    h_deriv t <| by simpa [hab] using ht]
  rw [intervalIntegral.integral_sub]
  · norm_num
  · exact ContinuousOn.intervalIntegrable (continuousOn_of_forall_continuousAt
      fun y hy ↦ ContinuousAt.div continuousAt_const
        (ContinuousAt.pow (Real.continuousAt_log
          (by linarith [Set.mem_Icc.mp (by simpa [hab] using hy)])) _)
        (ne_of_gt (pow_pos (Real.log_pos
          (by linarith [Set.mem_Icc.mp (by simpa [hab] using hy)])) _)))
  · exact ContinuousOn.intervalIntegrable
      (continuousOn_const.mul <| continuousOn_of_forall_continuousAt
        fun y hy ↦ ContinuousAt.div continuousAt_const
          (ContinuousAt.pow (Real.continuousAt_log
            (by linarith [Set.mem_Icc.mp (by simpa [hab] using hy)])) _)
          (ne_of_gt (pow_pos (Real.log_pos
            (by linarith [Set.mem_Icc.mp (by simpa [hab] using hy)])) _)))

theorem strictMonoOn_id_div_log_pow
    {n : Nat} {a : Real} (ha : 1 < a)
    (hcoef : (n + 1 : Real) < Real.log a) :
    StrictMonoOn (fun t : Real => t / Real.log t ^ (n + 1)) (Set.Ici a) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici a)
  · apply ContinuousOn.div continuousOn_id
    · exact (Real.continuousOn_log.mono (fun y hy =>
        have hy' : a ≤ y := hy
        ne_of_gt (by linarith [ha, hy']))).pow _
    · intro y hy
      have hy' : a ≤ y := hy
      exact pow_ne_zero _
        (ne_of_gt (Real.log_pos (lt_of_lt_of_le ha hy')))
  · intro t ht
    have hta : a < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
    have hlog : 0 < Real.log t := Real.log_pos (lt_trans ha hta)
    have hlog_gt : (n + 1 : Real) < Real.log t :=
      lt_of_lt_of_le hcoef (Real.log_le_log (by linarith) hta.le)
    rw [deriv_log_power_kernel (n := n) (by linarith)]
    have hnum : 0 < Real.log t - (n + 1 : Real) := by linarith
    field_simp [ne_of_gt hlog]
    have hp : 0 < Real.log t ^ n * Real.log t :=
      mul_pos (pow_pos hlog n) hlog
    simpa [pow_succ] using (mul_lt_mul_of_pos_left hlog_gt hp)

theorem id_div_log_pow_le_of_le
    {n : Nat} {a b : Real} (ha : 1 < a) (hab : a ≤ b)
    (hcoef : (n + 1 : Real) < Real.log a) :
    a / Real.log a ^ (n + 1) ≤ b / Real.log b ^ (n + 1) := by
  rcases hab.eq_or_lt with rfl | hlt
  · rfl
  · exact (strictMonoOn_id_div_log_pow ha hcoef
      (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hab) hlt).le

theorem inv_log_pow_le_of_le
    {m : Nat} {X x : Real} (hX : 1 < X) (hXx : X ≤ x) :
    1 / Real.log x ^ m ≤ 1 / Real.log X ^ m := by
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hlog_le : Real.log X ≤ Real.log x :=
    Real.log_le_log (by linarith) hXx
  have hlogx : 0 < Real.log x := lt_of_lt_of_le hlogX hlog_le
  have hinv : 1 / Real.log x ≤ 1 / Real.log X :=
    one_div_le_one_div_of_le hlogX hlog_le
  have hqx : 0 ≤ 1 / Real.log x := one_div_nonneg.mpr hlogx.le
  have hpow : (1 / Real.log x) ^ m ≤ (1 / Real.log X) ^ m := by
    exact pow_le_pow_left₀ hqx hinv m
  simpa [div_pow] using hpow

theorem id_div_log_pow_add_le
    {m : Nat} {X x : Real} (hX : 1 < X) (hXx : X ≤ x) :
    x / Real.log x ^ (4 + m) ≤
      (x / Real.log x ^ 4) / Real.log X ^ m := by
  have hxpos : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hbase : 0 ≤ x / Real.log x ^ 4 :=
    div_nonneg hxpos.le (pow_nonneg hlogx.le _)
  have hpow := inv_log_pow_le_of_le (m := m) hX hXx
  calc
    x / Real.log x ^ (4 + m) =
        (x / Real.log x ^ 4) * (1 / Real.log x ^ m) := by
      field_simp [ne_of_gt hlogx]
      rw [pow_add]
    _ ≤ (x / Real.log x ^ 4) * (1 / Real.log X ^ m) :=
      mul_le_mul_of_nonneg_left hpow hbase
    _ = (x / Real.log x ^ 4) / Real.log X ^ m := by ring

theorem integral_inv_log_pow_succ_le_of_next_bound
    {n : Nat} {a b : Real} (ha : 1 < a) (hab : a ≤ b)
    (hnext : (∫ t in a..b, 1 / Real.log t ^ (n + 2)) ≤
      (∫ t in a..b, 1 / Real.log t ^ (n + 1)) / Real.log a)
    (hcoef : (n + 1 : Real) < Real.log a) :
    (∫ t in a..b, 1 / Real.log t ^ (n + 1)) ≤
      (b / Real.log b ^ (n + 1)) /
        (1 - (n + 1 : Real) / Real.log a) := by
  have hloga : 0 < Real.log a := Real.log_pos ha
  have hden : 0 < 1 - (n + 1 : Real) / Real.log a := by
    rw [sub_pos]
    apply (div_lt_iff₀ hloga).2
    nlinarith [hcoef]
  have hleft : 0 ≤ a / Real.log a ^ (n + 1) := by positivity
  have hidentity := integral_inv_log_pow_succ_eq_interval
    (n := n) ha hab
  have hcoef_nonneg : 0 ≤ (n + 1 : Real) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hnext hcoef_nonneg
  have hineq :
      (∫ t in a..b, 1 / Real.log t ^ (n + 1)) ≤
        b / Real.log b ^ (n + 1) +
          (n + 1 : Real) *
            ((∫ t in a..b, 1 / Real.log t ^ (n + 1)) /
              Real.log a) := by
    calc
      (∫ t in a..b, 1 / Real.log t ^ (n + 1)) =
          b / Real.log b ^ (n + 1) - a / Real.log a ^ (n + 1) +
            (n + 1 : Real) *
              ∫ t in a..b, 1 / Real.log t ^ (n + 2) := hidentity
      _ ≤ b / Real.log b ^ (n + 1) +
            (n + 1 : Real) *
              ∫ t in a..b, 1 / Real.log t ^ (n + 2) := by
        nlinarith
      _ ≤ b / Real.log b ^ (n + 1) +
            (n + 1 : Real) *
              ((∫ t in a..b, 1 / Real.log t ^ (n + 1)) /
                Real.log a) := by
        simpa [add_comm] using add_le_add_left hmul
          (b / Real.log b ^ (n + 1))
  apply (le_div_iff₀ hden).2
  have htarget := hineq
  field_simp [ne_of_gt hloga] at htarget ⊢
  nlinarith

theorem integral_inv_log_pow_next_bound
    {n : Nat} {a b : Real} (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, 1 / Real.log t ^ (n + 2)) ≤
      (∫ t in a..b, 1 / Real.log t ^ (n + 1)) / Real.log a := by
  have hcont : ∀ m : Nat, ContinuousOn
      (fun t : Real => 1 / Real.log t ^ m) (Set.uIcc a b) := by
    intro m
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.div continuousOn_const
    · exact (Real.continuousOn_log.mono fun y hy =>
        ne_of_gt (by linarith [hy.1])).pow _
    · intro y hy
      exact pow_ne_zero _ (ne_of_gt (Real.log_pos (by linarith [hy.1])))
  have hfi : IntervalIntegrable
      (fun t : Real => 1 / Real.log t ^ (n + 2))
      MeasureTheory.volume a b := (hcont (n + 2)).intervalIntegrable
  have hgi : IntervalIntegrable
      (fun t : Real => (1 / Real.log a) * (1 / Real.log t ^ (n + 1)))
      MeasureTheory.volume a b :=
    ((continuousOn_const.mul (hcont (n + 1))).intervalIntegrable)
  have hmono : ∀ t ∈ Set.Icc a b,
      1 / Real.log t ^ (n + 2) ≤
        (1 / Real.log a) * (1 / Real.log t ^ (n + 1)) := by
    intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    have hloga : 0 < Real.log a := Real.log_pos ha
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hlog_le : Real.log a ≤ Real.log t :=
      Real.log_le_log (by linarith) ht.1
    have hinv : 1 / Real.log t ≤ 1 / Real.log a :=
      (one_div_le_one_div_of_le hloga hlog_le)
    have hpow : 0 ≤ 1 / Real.log t ^ (n + 1) := by positivity
    calc
      1 / Real.log t ^ (n + 2) =
          (1 / Real.log t ^ (n + 1)) * (1 / Real.log t) := by
            field_simp [ne_of_gt hlogt]
            rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, pow_succ,
              pow_succ]
      _ ≤ (1 / Real.log t ^ (n + 1)) * (1 / Real.log a) :=
        mul_le_mul_of_nonneg_left hinv hpow
      _ = (1 / Real.log a) * (1 / Real.log t ^ (n + 1)) := by ring
  have hintegral := intervalIntegral.integral_mono_on hab hfi hgi hmono
  simpa [div_eq_mul_inv, mul_comm] using hintegral

theorem integral_inv_log_pow_succ_le
    {n : Nat} {a b : Real} (ha : 1 < a) (hab : a ≤ b)
    (hcoef : (n + 1 : Real) < Real.log a) :
    (∫ t in a..b, 1 / Real.log t ^ (n + 1)) ≤
      (b / Real.log b ^ (n + 1)) /
        (1 - (n + 1 : Real) / Real.log a) :=
  integral_inv_log_pow_succ_le_of_next_bound ha hab
    (integral_inv_log_pow_next_bound ha hab) hcoef

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
def HasDusartPrimeCountingAsymptoticAbove (X : Real) : Prop :=
  ∀ x : Real, X ≤ x →
    ∃ E : Real,
      (Nat.primeCounting ⌊x⌋₊ : Real) =
        x / Real.log x *
          (1 + 1 / Real.log x + 2 / (Real.log x) ^ 2 + E) ∧
        |E| ≤ (732 : Real) / 100 / (Real.log x) ^ 3

/-! The remaining quantitative statement can be supplied in the natural
unnormalized form produced by Abel summation.  This theorem performs the
normalization into Dusart's published `E` form entirely in Lean. -/
theorem hasDusartPrimeCountingAsymptoticAbove_of_explicitRemainder
    {X : Real} (hXpos : 0 < X) (hlogX : (20 : Real) < Real.log X)
    (hbound : ∀ x : Real, X ≤ x →
      |(Nat.primeCounting ⌊x⌋₊ : Real) -
          (x / Real.log x + x / (Real.log x) ^ 2 +
            2 * x / (Real.log x) ^ 3)| ≤
        (732 : Real) / 100 * x / (Real.log x) ^ 4) :
    HasDusartPrimeCountingAsymptoticAbove X := by
  intro x hx
  have hx_pos : 0 < x := by linarith
  have hlog_pos : 0 < Real.log x := by
    have hlogx : (20 : Real) < Real.log x :=
      lt_of_lt_of_le hlogX (Real.log_le_log hXpos hx)
    linarith
  let E : Real :=
    ((Nat.primeCounting ⌊x⌋₊ : Real) -
      (x / Real.log x + x / (Real.log x) ^ 2 +
        2 * x / (Real.log x) ^ 3)) * Real.log x / x
  refine ⟨E, ?_, ?_⟩
  · dsimp [E]
    field_simp [ne_of_gt hx_pos, ne_of_gt hlog_pos]
    ring
  · have hmain := hbound x hx
    have hscale : 0 ≤ Real.log x / x := by positivity
    have hscaled := mul_le_mul_of_nonneg_right hmain hscale
    dsimp [E]
    rw [abs_div, abs_mul, abs_of_pos hlog_pos, abs_of_pos hx_pos]
    calc
      |(Nat.primeCounting ⌊x⌋₊ : Real) -
          (x / Real.log x + x / (Real.log x) ^ 2 +
            2 * x / (Real.log x) ^ 3)| * Real.log x / x ≤
          ((732 : Real) / 100 * x / (Real.log x) ^ 4) *
            (Real.log x / x) := by
              convert hscaled using 1 <;> ring
      _ = (732 : Real) / 100 / (Real.log x) ^ 3 := by
        field_simp [ne_of_gt hx_pos, ne_of_gt hlog_pos]

/-! The Abel-summation argument supplies the all-`x` remainder bound from the
explicit theta error and the finite core estimate.  This is the theorem that
connects those two analytic obligations to the Dusart asymptotic interface;
the latter is not imported as an external black box. -/
theorem hasDusartPrimeCountingAsymptoticAbove_of_core_and_theta_error
    {A C X : Real}
    (hXpos : 0 < X) (h2X : 2 ≤ X)
    (hA0 : 0 ≤ A) (hA : A ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hlog : (42 : Real) ≤ Real.log X)
    (hcore : |primeCountingCore X| ≤ C * X / Real.log X ^ 4)
    (error : HasThetaLogFourthError A X) :
    HasDusartPrimeCountingAsymptoticAbove X := by
  have hX : 1 < X := by
    have hlog_pos : 0 < Real.log X := lt_of_lt_of_le (by norm_num) hlog
    exact (Real.log_pos_iff hXpos.le).mp hlog_pos
  apply hasDusartPrimeCountingAsymptoticAbove_of_explicitRemainder
    hXpos (by linarith [hlog])
  intro x hx
  exact primeCounting_remainder_abs_le_732
    hX h2X hx hA0 hA hC0 hC hlog hcore error

def HasDusartPublishedPrimeCountingBoundsAbove (X : Real) : Prop :=
  (∀ x : Real, X ≤ x →
    x / (Real.log x - 1) ≤ (Nat.primeCounting ⌊x⌋₊ : Real)) ∧
  (∀ x : Real, X ≤ x →
    (Nat.primeCounting ⌊x⌋₊ : Real) ≤
      x / (Real.log x - (11 / 10 : Real)))

theorem hasDusartPublishedPrimeCountingBoundsAbove_of_asymptotic_from
    {X : Real} (hlogX : (20 : Real) < Real.log X)
    (asymptotic : HasDusartPrimeCountingAsymptoticAbove X) :
    HasDusartPublishedPrimeCountingBoundsAbove X := by
  constructor
  · intro x hx
    obtain ⟨E, hformula, hE⟩ := asymptotic x hx
    have hlog : (20 : Real) < Real.log x :=
      lt_of_lt_of_le hlogX (Real.log_le_log (by linarith) hx)
    have hlog_pos : 0 < Real.log x := by linarith
    have hx_pos : 0 < x := by linarith
    rw [hformula]
    have hE_lower : -(732 : Real) / 100 / (Real.log x) ^ 3 ≤ E := by
      convert neg_le_of_abs_le hE using 1 <;> ring
    have hbracket :
        1 + 1 / Real.log x + 2 / (Real.log x) ^ 2 + E ≥
          Real.log x / (Real.log x - 1) := by
      have hden : 0 < Real.log x - 1 := by linarith
      apply (div_le_iff₀ hden).2
      have hlog_cube : (0 : Real) < (Real.log x) ^ 3 := by positivity
      have hE_lower' : -(732 : Real) / 100 ≤ E * (Real.log x) ^ 3 :=
        (div_le_iff₀ hlog_cube).mp hE_lower
      have hE_prod := mul_le_mul_of_nonneg_right hE_lower' hden.le
      field_simp [hlog_pos.ne', hden.ne']
      nlinarith [hE_prod, sq_nonneg (Real.log x - 20)]
    have hfactor : 0 ≤ x / Real.log x := by positivity
    have hmul := mul_le_mul_of_nonneg_left hbracket hfactor
    have htarget : x / Real.log x * (Real.log x / (Real.log x - 1)) =
        x / (Real.log x - 1) := by
      field_simp [hlog_pos.ne', (by linarith : Real.log x - 1 ≠ 0)]
    rw [htarget] at hmul
    exact hmul
  · intro x hx
    obtain ⟨E, hformula, hE⟩ := asymptotic x hx
    have hlog : (20 : Real) < Real.log x :=
      lt_of_lt_of_le hlogX (Real.log_le_log (by linarith) hx)
    have hlog_pos : 0 < Real.log x := by linarith
    have hx_pos : 0 < x := by linarith
    rw [hformula]
    have hE_upper : E ≤ (732 : Real) / 100 / (Real.log x) ^ 3 :=
      le_of_abs_le hE
    have hbracket :
        1 + 1 / Real.log x + 2 / (Real.log x) ^ 2 + E ≤
          Real.log x / (Real.log x - (11 / 10 : Real)) := by
      have hden : 0 < Real.log x - (11 / 10 : Real) := by linarith
      apply (le_div_iff₀ hden).2
      have hlog_cube : (0 : Real) < (Real.log x) ^ 3 := by positivity
      have hE_upper' : E * (Real.log x) ^ 3 ≤ (732 : Real) / 100 :=
        (le_div_iff₀ hlog_cube).mp hE_upper
      have hE_prod := mul_le_mul_of_nonneg_right hE_upper' hden.le
      field_simp [hlog_pos.ne', hden.ne']
      nlinarith [hE_prod, sq_nonneg (Real.log x - 20)]
    have hfactor : 0 ≤ x / Real.log x := by positivity
    have hmul := mul_le_mul_of_nonneg_left hbracket hfactor
    have htarget : x / Real.log x *
        (Real.log x / (Real.log x - (11 / 10 : Real))) =
        x / (Real.log x - (11 / 10 : Real)) := by
      field_simp [hlog_pos.ne', (by linarith : Real.log x - (11 / 10 : Real) ≠ 0)]
    rw [htarget] at hmul
    exact hmul

theorem hasDusartPublishedPrimeCountingBoundsAbove_of_asymptotic
    (asymptotic : HasDusartPrimeCountingAsymptoticAbove (4e9 : Real)) :
    HasDusartPublishedPrimeCountingBoundsAbove (4e9 : Real) :=
  hasDusartPublishedPrimeCountingBoundsAbove_of_asymptotic_from
    (by
      apply (Real.lt_log_iff_exp_lt (by norm_num)).2
      have hexp_three : Real.exp 20 < (3 : Real) ^ 20 := by
        rw [show (20 : Real) = (20 : ℕ) * 1 by norm_num,
          Real.exp_nat_mul]
        exact pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le
          (by norm_num)
      have hthree : (3 : Real) ^ 20 < (4e9 : Real) := by norm_num
      exact hexp_three.trans hthree)
    asymptotic

theorem hasDusartPublishedPrimeCountingBounds_of_below_and_above
    {X : Real} (finite : HasDusartPublishedPrimeCountingBoundsBelow X)
    (tail : HasDusartPublishedPrimeCountingBoundsAbove X) :
    HasDusartPublishedPrimeCountingBounds := by
  constructor
  · intro x hx
    by_cases hsmall : x ≤ X
    · exact finite.1 x hx hsmall
    · exact tail.1 x (le_of_lt (lt_of_not_ge hsmall))
  · intro x hx
    by_cases hsmall : x ≤ X
    · exact finite.2 x hx hsmall
    · exact tail.2 x (le_of_lt (lt_of_not_ge hsmall))

theorem hasDusartPublishedPrimeCountingBounds_of_finite_and_asymptotic
    (finite : HasDusartPublishedPrimeCountingBoundsBelow (4e9 : Real))
    (asymptotic : HasDusartPrimeCountingAsymptoticAbove (4e9 : Real)) :
    HasDusartPublishedPrimeCountingBounds := by
  exact hasDusartPublishedPrimeCountingBounds_of_below_and_above finite
    (hasDusartPublishedPrimeCountingBoundsAbove_of_asymptotic asymptotic)

theorem hasDusartRealPrimeCountingBoundsAbove_of_asymptotic_from
    {X Y : Real} (hlogX : (20 : Real) < Real.log X) (hXY : X ≤ Y)
    (asymptotic : HasDusartPrimeCountingAsymptoticAbove X) :
    HasDusartRealPrimeCountingBoundsAbove Y := by
  constructor
  · intro x hx
    have hXx : X ≤ x := hXY.trans hx
    obtain ⟨E, hformula, hE⟩ := asymptotic x hXx
    have hlog : (10 : Real) < Real.log x := by
      have hlog' := lt_of_lt_of_le hlogX (Real.log_le_log (by linarith) hXx)
      linarith
    have hlog_pos : 0 < Real.log x := by linarith
    have hx_pos : 0 < x := by linarith
    have hlog_sq : (100 : Real) < (Real.log x) ^ 2 := by
      nlinarith [mul_self_lt_mul_self (by norm_num : (0 : Real) ≤ 10) hlog]
    have hlog_cube : (1000 : Real) < (Real.log x) ^ 3 := by
      nlinarith [mul_self_lt_mul_self (by norm_num : (0 : Real) ≤ 10) hlog,
        mul_pos hlog_pos (show 0 < (Real.log x) ^ 2 by positivity)]
    rw [hformula]
    have hElower : -(732 : Real) / 100 / (Real.log x) ^ 3 ≤ E := by
      convert neg_le_of_abs_le hE using 1 <;> ring
    have hmain : (1 : Real) + 1 / Real.log x + 2 / (Real.log x) ^ 2 + E ≥
        1 + 1 / Real.log x := by
      have hrem : (732 : Real) / 100 / (Real.log x) ^ 3 ≤
          2 / (Real.log x) ^ 2 := by
        field_simp
        nlinarith [hlog_cube]
      have hElower' : -(2 / (Real.log x) ^ 2) ≤ E := by
        calc
          -(2 / (Real.log x) ^ 2) ≤
              -((732 : Real) / 100 / (Real.log x) ^ 3) := by
                linarith
          _ ≤ E := by convert hElower using 1 <;> ring
      linarith
    have hfactor : 0 ≤ x / Real.log x := by positivity
    have := mul_le_mul_of_nonneg_left hmain.le hfactor
    convert this using 1 <;> dsimp [dusartPiLower] <;> field_simp <;> ring
  · intro x hx
    have hXx : X ≤ x := hXY.trans hx
    obtain ⟨E, hformula, hE⟩ := asymptotic x hXx
    have hlog : (10 : Real) < Real.log x := by
      have hlog' := lt_of_lt_of_le hlogX (Real.log_le_log (by linarith) hXx)
      linarith
    have hlog_pos : 0 < Real.log x := by linarith
    have hx_pos : 0 < x := by linarith
    have hupper : (1 : Real) + 1 / Real.log x + 2 / (Real.log x) ^ 2 + E ≤
        1 + (6381 : Real) / 5000 / Real.log x := by
      have hEupper : E ≤ (732 : Real) / 100 / (Real.log x) ^ 3 :=
        le_of_abs_le hE
      have hlog_sq : (100 : Real) < (Real.log x) ^ 2 := by
        nlinarith [mul_self_lt_mul_self (by norm_num : (0 : Real) ≤ 10) hlog]
      have hlog_pos' : 0 ≤ Real.log x := hlog_pos.le
      have hcoef :
          2 / (Real.log x) ^ 2 + (732 : Real) / 100 / (Real.log x) ^ 3 ≤
            (1381 : Real) / 5000 / Real.log x := by
        field_simp
        nlinarith
      calc
        1 + 1 / Real.log x + 2 / (Real.log x) ^ 2 + E =
            1 + 1 / Real.log x + (2 / (Real.log x) ^ 2 + E) := by ring
        _ ≤ 1 + 1 / Real.log x +
            (2 / (Real.log x) ^ 2 + (732 : Real) / 100 /
              (Real.log x) ^ 3) := by linarith
        _ ≤ 1 + 1 / Real.log x + (1381 : Real) / 5000 / Real.log x :=
          by
            convert add_le_add_left hcoef (1 + 1 / Real.log x) using 1 <;> ring
        _ = 1 + (6381 : Real) / 5000 / Real.log x := by ring
    rw [hformula]
    dsimp [dusartPiUpper]
    have hfactor : 0 ≤ x / Real.log x := by positivity
    have := mul_le_mul_of_nonneg_left hupper hfactor
    convert this using 1 <;> dsimp [dusartPiUpper] <;> field_simp <;> ring

theorem hasDusartRealPrimeCountingBoundsAbove_of_asymptotic
    (asymptotic : HasDusartPrimeCountingAsymptoticAbove (4e9 : Real)) :
    HasDusartRealPrimeCountingBoundsAbove (4e18 : Real) :=
  hasDusartRealPrimeCountingBoundsAbove_of_asymptotic_from
    (by
      apply (Real.lt_log_iff_exp_lt (by norm_num)).2
      have hexp_three : Real.exp 20 < (3 : Real) ^ 20 := by
        rw [show (20 : Real) = (20 : ℕ) * 1 by norm_num,
          Real.exp_nat_mul]
        exact pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le
          (by norm_num)
      have hthree : (3 : Real) ^ 20 < (4e9 : Real) := by norm_num
      exact hexp_three.trans hthree)
    (by norm_num) asymptotic

theorem hasDusartRealPrimeCountingBounds_of_below_and_above
    {X : Real} (finite : HasDusartRealPrimeCountingBoundsBelow X)
    (tail : HasDusartRealPrimeCountingBoundsAbove X) :
    HasDusartRealPrimeCountingBounds := by
  constructor
  · intro x hx
    by_cases hsmall : x ≤ X
    · exact finite.1 x hx hsmall
    · exact tail.1 x (le_of_lt (lt_of_not_ge hsmall))
  · intro x hx
    by_cases hsmall : x ≤ X
    · exact finite.2 x hx hsmall
    · exact tail.2 x (le_of_lt (lt_of_not_ge hsmall))

theorem hasDusartRealPrimeCountingBounds_of_finite_and_asymptotic
    (finite : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real))
    (asymptotic : HasDusartPrimeCountingAsymptoticAbove (4e9 : Real)) :
    HasDusartRealPrimeCountingBounds :=
  hasDusartRealPrimeCountingBounds_of_below_and_above finite
    (hasDusartRealPrimeCountingBoundsAbove_of_asymptotic asymptotic)

theorem hasDusartRealPrimeCountingBounds_of_finite_published_and_asymptotic
    (finite : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real))
    (finitePublished : HasDusartPublishedPrimeCountingBoundsBelow (4e9 : Real))
    (asymptotic : HasDusartPrimeCountingAsymptoticAbove (4e9 : Real)) :
    HasDusartRealPrimeCountingBounds := by
  have published : HasDusartPublishedPrimeCountingBounds :=
    hasDusartPublishedPrimeCountingBounds_of_finite_and_asymptotic
      finitePublished asymptotic
  exact hasDusartRealPrimeCountingBounds_of_below_and_above finite
    (hasDusartRealPrimeCountingBoundsAbove_of_published published)

theorem hasDusartRealPrimeCountingBounds_of_below_and_above_at_cutoff
    (finite : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real))
    (tail : HasDusartRealPrimeCountingBoundsAbove (4e18 : Real)) :
    HasDusartRealPrimeCountingBounds :=
  hasDusartRealPrimeCountingBounds_of_below_and_above finite tail

theorem hasDusartPrimeCountingBounds_of_real
    (bounds : HasDusartRealPrimeCountingBounds) :
    HasDusartPrimeCountingBounds := by
  constructor
  · intro n hn
    simpa only [Nat.floor_natCast] using
      bounds.1 (n : Real) (by exact_mod_cast hn)
  · intro n hn
    simpa only [Nat.floor_natCast] using
      bounds.2 (n : Real) (by exact_mod_cast hn)

theorem primeCounting_sub_lower_of_dusart
    (bounds : HasDusartPrimeCountingBounds)
    {x y : Nat} (hx : 2 ≤ x) (hy : 599 ≤ y) (hxy : x ≤ y) :
    dusartPiLower y - dusartPiUpper x ≤
      (Nat.primeCounting y - Nat.primeCounting x : Nat) := by
  have lower := bounds.1 y hy
  have upper := bounds.2 x hx
  have countMono := Nat.monotone_primeCounting hxy
  rw [Nat.cast_sub countMono]
  exact sub_le_sub lower upper

/-- A real lower bound exceeding a natural target yields the corresponding
natural lower bound on the number of primes in a shell. -/
theorem nat_le_primeCounting_sub_of_lt_dusart
    (bounds : HasDusartPrimeCountingBounds)
    {x y target : Nat} (hx : 2 ≤ x) (hy : 599 ≤ y) (hxy : x ≤ y)
    (numeric : (target : Real) < dusartPiLower y - dusartPiUpper x) :
    target + 1 ≤ Nat.primeCounting y - Nat.primeCounting x := by
  have lower := numeric.trans_le
    (primeCounting_sub_lower_of_dusart bounds hx hy hxy)
  exact_mod_cast lower

/-- A lower bound for a prime-counting shell, expressed in the same units as
an intended average-gap bound, directly supplies both discrete hypotheses of
the average-gap lemma.  This avoids introducing a rounded auxiliary target. -/
theorem count_and_width_of_dusart
    (bounds : HasDusartPrimeCountingBounds)
    {x y width bound : Nat} (hx : 2 ≤ x) (hy : 599 ≤ y) (hxy : x ≤ y)
    (bound_pos : 1 ≤ bound)
    (numeric : (width : Real) / bound + 1 <
      dusartPiLower y - dusartPiUpper x) :
    2 ≤ Nat.primeCounting y - Nat.primeCounting x ∧
      width < (Nat.primeCounting y - Nat.primeCounting x - 1) * bound := by
  let count := Nat.primeCounting y - Nat.primeCounting x
  have shellLower := primeCounting_sub_lower_of_dusart bounds hx hy hxy
  have countBound : (width : Real) / bound + 1 < (count : Real) := by
    exact numeric.trans_le (by simpa only [count] using shellLower)
  have boundRealPos : (0 : Real) < bound := by exact_mod_cast bound_pos
  have countGtOne : (1 : Real) < count := by
    have widthNonneg : (0 : Real) ≤ width := by positivity
    have divNonneg : (0 : Real) ≤ (width : Real) / bound :=
      div_nonneg widthNonneg boundRealPos.le
    linarith
  have countTwo : 2 ≤ count := by exact_mod_cast countGtOne
  refine ⟨by simpa only [count] using countTwo, ?_⟩
  have productBound : (width : Real) < ((count - 1) * bound : Nat) := by
    have divided : (width : Real) / bound < (count : Real) - 1 := by
      linarith
    rw [div_lt_iff₀ boundRealPos] at divided
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ count)]
    norm_num
    exact divided
  exact_mod_cast productBound

/-- A numerical lower bound for Dusart's comparison function converts
directly into an upper bound for an indexed prime. -/
theorem primeAt_le_of_dusart_lower
    (bounds : HasDusartPrimeCountingBounds) {i upper : Nat}
    (upper_large : 599 ≤ upper)
    (numeric : ((i + 1 : Nat) : Real) ≤ dusartPiLower upper) :
    primeAt i ≤ upper := by
  apply primeAt_le_of_succ_le_primeCounting'
  have castCount : ((i + 1 : Nat) : Real) ≤ Nat.primeCounting upper :=
    numeric.trans (bounds.1 upper upper_large)
  have natCount : i + 1 ≤ Nat.primeCounting upper := by exact_mod_cast castCount
  simpa only [Nat.primeCounting] using natCount

end

end PrimeFactorUnimodality
