import Mathlib.Analysis.SpecialFunctions.Sqrt
import PrimeFactorUnimodality.Helpers.Analytic.ShortIntervalPrime

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

/-! The prime-power correction is kept separate from the analytic estimate for
`psi`.  This is the elementary bridge used in Dusart's theta argument. -/

def HasPsiLogFourthError (A X : Real) : Prop :=
  ∀ x : Real, X ≤ x →
    |Chebyshev.psi x - x| ≤ A * x / (Real.log x) ^ 4

def HasPsiLogCubedError (C X : Real) : Prop :=
  ∀ x : Real, X ≤ x →
    |Chebyshev.psi x - x| ≤ C * x / (Real.log x) ^ 3

private def logPowFiveDivSqrt (x : Real) : Real :=
  (Real.log x) ^ 5 / Real.sqrt x

private theorem logPowFiveDivSqrt_antitoneOn :
    AntitoneOn logPowFiveDivSqrt (Set.Ici (4e18 : Real)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici (4e18 : Real))
  · apply ContinuousOn.div
    · exact (continuousOn_id.log (by
        intro x hx
        have : (0 : Real) < x := by
          norm_num at hx ⊢
          linarith
        exact this.ne')).pow 5
    · exact continuousOn_id.sqrt
    · intro x hx
      have : (0 : Real) < x := by
        norm_num at hx ⊢
        linarith
      exact (Real.sqrt_pos.2 this).ne'
  · apply DifferentiableOn.div
    · exact (differentiableOn_id.log (by
        intro x hx
        have : (0 : Real) < x := by
          norm_num at hx ⊢
          linarith
        exact this.ne')).pow 5
    · exact DifferentiableOn.sqrt differentiableOn_id (by
        intro x hx
        have : (0 : Real) < x := by
          norm_num at hx ⊢
          linarith
        exact this.ne')
    · intro x hx
      have : (0 : Real) < x := by
        norm_num at hx ⊢
        linarith
      exact (Real.sqrt_pos.2 this).ne'
  · intro x hx
    simp only [interior_Ici, Set.mem_Ioi] at hx
    have hx_pos : 0 < x := by
      norm_num at hx ⊢
      linarith
    have hx_ne : x ≠ 0 := hx_pos.ne'
    have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx_pos
    have hderiv := ((Real.hasDerivAt_log hx_ne).pow 5).div
      (Real.hasDerivAt_sqrt hx_ne) hsqrt_pos.ne'
    change deriv logPowFiveDivSqrt x ≤ 0
    change deriv ((fun y : Real => (Real.log y) ^ 5) /
      (fun y : Real => Real.sqrt y)) x ≤ 0
    have hfun : (Real.log ^ 5 / (fun y : Real => Real.sqrt y)) =
        ((fun y : Real => (Real.log y) ^ 5) /
          (fun y : Real => Real.sqrt y)) := by
      funext y
      rfl
    rw [← hfun, hderiv.deriv]
    simp only [Pi.pow_apply] at *
    have hden : 0 < (Real.sqrt x) ^ 2 := sq_pos_of_pos hsqrt_pos
    apply (div_le_iff₀ hden).2
    field_simp [hx_ne, hlog_pos.ne', hsqrt_pos.ne']
    rw [Real.sq_sqrt hx_pos.le]
    have hlog_gt_ten : (10 : Real) < Real.log x := by
      apply (Real.lt_log_iff_exp_lt hx_pos).2
      have hexp : Real.exp 10 < (3 : Real) ^ 10 := by
        rw [show (10 : Real) = (10 : ℕ) * 1 by norm_num,
          Real.exp_nat_mul]
        exact pow_lt_pow_left₀ Real.exp_one_lt_three
          (Real.exp_pos 1).le (by norm_num)
      have hpow : (3 : Real) ^ 10 < x := by
        norm_num at hx ⊢
        linarith
      exact hexp.trans hpow
    have hlog_four : 0 ≤ (Real.log x) ^ 4 := by positivity
    have hx_one : (1 : Real) ≤ x := by linarith
    have hxl : (10 : Real) ≤ x * Real.log x := by
      nlinarith [mul_le_mul_of_nonneg_right hx_one hlog_pos.le]
    have hxl_scaled := mul_le_mul_of_nonneg_right hxl hlog_four
    norm_num at *
    nlinarith [hxl_scaled]

private theorem logPowFiveDivSqrt_cutoff_le
    {x : Real} (hx : (4e18 : Real) ≤ x) :
    logPowFiveDivSqrt x ≤ (43 : Real) ^ 5 / 2000000000 := by
  have hanti : AntitoneOn logPowFiveDivSqrt (Set.Ici (4e18 : Real)) :=
    logPowFiveDivSqrt_antitoneOn
  have hbase : (4e18 : Real) ∈ Set.Ici (4e18 : Real) := by norm_num
  have hxmem : x ∈ Set.Ici (4e18 : Real) := by exact hx
  have hmono : logPowFiveDivSqrt x ≤ logPowFiveDivSqrt (4e18 : Real) :=
    hanti hbase hxmem hx
  calc
    logPowFiveDivSqrt x ≤ logPowFiveDivSqrt (4e18 : Real) := hmono
    _ ≤ (43 : Real) ^ 5 / 2000000000 := by
      unfold logPowFiveDivSqrt
      have hlog : Real.log (4e18 : Real) < 43 := by
        apply (Real.log_lt_iff_lt_exp (by norm_num)).2
        have hexp : (4e18 : Real) < Real.exp 43 := by
          rw [show (43 : Real) = (43 : ℕ) * 1 by norm_num,
            Real.exp_nat_mul]
          have hnum : (4e18 : Real) < (2.718 : Real) ^ (43 : Nat) := by
            norm_num
          have hbase : (2.718 : Real) < Real.exp 1 :=
            (by norm_num : (2.718 : Real) < 2.7182818283).trans
              Real.exp_one_gt_d9
          exact hnum.trans (pow_lt_pow_left₀ (n := 43) hbase
            (by norm_num) (by norm_num))
        exact hexp
      have hsqrt : Real.sqrt (4e18 : Real) = 2000000000 := by
        rw [show (4e18 : Real) = (2000000000 : Real) ^ 2 by norm_num,
          Real.sqrt_sq_eq_abs, abs_of_nonneg]
        norm_num
      rw [hsqrt]
      have hlog_nonneg : 0 ≤ Real.log (4e18 : Real) :=
        Real.log_nonneg (by norm_num)
      have hpow : (Real.log (4e18 : Real)) ^ 5 ≤ (43 : Real) ^ 5 := by
        exact pow_le_pow_left₀ hlog_nonneg hlog.le 5
      gcongr

private theorem primePowerCorrection_le_logFourth
    {x : Real} (hx : (4e18 : Real) ≤ x) :
    2 * Real.sqrt x * Real.log x ≤ x / (Real.log x) ^ 4 := by
  have hx_pos : 0 < x := by linarith
  have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx_pos
  have hratio := logPowFiveDivSqrt_cutoff_le hx
  have hratio' : (Real.log x) ^ 5 / Real.sqrt x ≤
      (43 : Real) ^ 5 / 2000000000 := hratio
  have hnum : 2 * (43 : Real) ^ 5 < 2000000000 := by norm_num
  have hmain : 2 * (Real.log x) ^ 5 / Real.sqrt x ≤ 1 := by
    calc
      2 * (Real.log x) ^ 5 / Real.sqrt x ≤
          2 * ((43 : Real) ^ 5 / 2000000000) := by
            rw [show 2 * (Real.log x) ^ 5 / Real.sqrt x =
              2 * ((Real.log x) ^ 5 / Real.sqrt x) by ring]
            exact mul_le_mul_of_nonneg_left hratio' (by norm_num)
      _ ≤ 1 := by nlinarith
  have hmain' : 2 * (Real.log x) ^ 5 ≤ Real.sqrt x := by
    simpa using (div_le_iff₀ hsqrt_pos).mp hmain
  apply (le_div_iff₀ (by positivity : 0 < (Real.log x) ^ 4)).2
  calc
    2 * Real.sqrt x * Real.log x * (Real.log x) ^ 4 =
        (2 * (Real.log x) ^ 5) * Real.sqrt x := by ring
    _ ≤ Real.sqrt x * Real.sqrt x :=
      mul_le_mul_of_nonneg_right hmain' hsqrt_pos.le
    _ = x := by simpa [pow_two] using Real.sq_sqrt hx_pos.le

theorem hasThetaLogCubedError_of_psiLogCubedError
    {C X : Real} (hX : (4e18 : Real) ≤ X)
    (hlogX : 0 < Real.log X)
    (psiError : HasPsiLogCubedError C X) :
    HasThetaLogCubedError (C + 1 / Real.log X) X := by
  intro x hx
  have hx_cutoff : (4e18 : Real) ≤ x := hX.trans hx
  have hx_pos : 0 < x := by linarith
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog_mono : Real.log X ≤ Real.log x := by
    have hXpos : 0 < X := by
      linarith [hX]
    exact Real.log_le_log hXpos hx
  have hpsi := psiError x hx
  have hcorrection := primePowerCorrection_le_logFourth hx_cutoff
  have hcorrection_cubic :
      2 * Real.sqrt x * Real.log x ≤
        (1 / Real.log X) * x / (Real.log x) ^ 3 := by
    calc
      2 * Real.sqrt x * Real.log x ≤ x / (Real.log x) ^ 4 := hcorrection
      _ = (x / (Real.log x) ^ 3) / Real.log x := by
        field_simp [hlogx_pos.ne']
      _ ≤ (x / (Real.log x) ^ 3) / Real.log X := by
        have hbase : 0 ≤ x / (Real.log x) ^ 3 := by positivity
        exact div_le_div_of_nonneg_left hbase hlogX hlog_mono
      _ = (1 / Real.log X) * x / (Real.log x) ^ 3 := by
        field_simp [hlogX.ne']
  have hdiff := Chebyshev.psi_sub_theta_le (x := x) (by linarith)
  have htheta_le_psi := Chebyshev.theta_le_psi x
  have hcorrection_abs :
      |Chebyshev.theta x - Chebyshev.psi x| ≤
        2 * Real.sqrt x * Real.log x := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr htheta_le_psi)]
    linarith
  calc
    |Chebyshev.theta x - x| ≤
        |Chebyshev.theta x - Chebyshev.psi x| +
          |Chebyshev.psi x - x| := by
      rw [show Chebyshev.theta x - x =
        (Chebyshev.theta x - Chebyshev.psi x) +
          (Chebyshev.psi x - x) by ring]
      exact abs_add_le _ _
    _ ≤ (1 / Real.log X) * x / (Real.log x) ^ 3 +
          C * x / (Real.log x) ^ 3 :=
      add_le_add (hcorrection_abs.trans hcorrection_cubic) hpsi
    _ = (C + 1 / Real.log X) * x / (Real.log x) ^ 3 := by ring

theorem hasThetaLogFourthError_of_psiLogFourthError
    {A X : Real} (hX : (4e18 : Real) ≤ X)
    (psiError : HasPsiLogFourthError A X) :
    HasThetaLogFourthError (A + 1) X := by
  intro x hx
  have hx_cutoff : (4e18 : Real) ≤ x := hX.trans hx
  have hx_pos : 0 < x := by linarith
  have hpsi := psiError x hx
  have hcorrection := primePowerCorrection_le_logFourth hx_cutoff
  have hdiff := Chebyshev.psi_sub_theta_le (x := x) (by linarith)
  have htheta_le_psi := Chebyshev.theta_le_psi x
  have hcorrection_abs :
      |Chebyshev.theta x - Chebyshev.psi x| ≤
        2 * Real.sqrt x * Real.log x := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr htheta_le_psi)]
    linarith
  calc
    |Chebyshev.theta x - x| ≤
        |Chebyshev.theta x - Chebyshev.psi x| +
          |Chebyshev.psi x - x| := by
      rw [show Chebyshev.theta x - x =
        (Chebyshev.theta x - Chebyshev.psi x) +
          (Chebyshev.psi x - x) by ring]
      exact abs_add_le _ _
    _ ≤ 2 * Real.sqrt x * Real.log x +
          A * x / (Real.log x) ^ 4 :=
      add_le_add hcorrection_abs hpsi
    _ ≤ (A + 1) * x / (Real.log x) ^ 4 := by
      calc
        _ ≤ x / (Real.log x) ^ 4 + A * x / (Real.log x) ^ 4 :=
          add_le_add hcorrection le_rfl
        _ = (A + 1) * x / (Real.log x) ^ 4 := by ring

theorem hasThetaLogFourthError_of_psiLogFourthError_sharp
    {A X : Real} (hX : (4e18 : Real) ≤ X)
    (psiError : HasPsiLogFourthError A X) :
    HasThetaLogFourthError (A + 148 / 1000) X := by
  intro x hx
  have hx_cutoff : (4e18 : Real) ≤ x := hX.trans hx
  have hx_pos : 0 < x := by linarith
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx_pos
  have hpsi := psiError x hx
  have hratio := logPowFiveDivSqrt_cutoff_le hx_cutoff
  have hratio' : (Real.log x) ^ 5 / Real.sqrt x ≤
      (43 : Real) ^ 5 / 2000000000 := hratio
  have hscaled : 2 * (Real.log x) ^ 5 / Real.sqrt x ≤
      (148 / 1000 : Real) := by
    calc
      2 * (Real.log x) ^ 5 / Real.sqrt x ≤
          2 * ((43 : Real) ^ 5 / 2000000000) := by
        rw [show 2 * (Real.log x) ^ 5 / Real.sqrt x =
          2 * ((Real.log x) ^ 5 / Real.sqrt x) by ring]
        exact mul_le_mul_of_nonneg_left hratio' (by norm_num)
      _ ≤ (148 / 1000 : Real) := by norm_num
  have hscaled' : 2 * (Real.log x) ^ 5 ≤
      (148 / 1000 : Real) * Real.sqrt x := by
    exact (div_le_iff₀ hsqrt_pos).mp hscaled
  have hcorrection_sharp :
      2 * Real.sqrt x * Real.log x ≤
        (148 / 1000 : Real) * x / (Real.log x) ^ 4 := by
    apply (le_div_iff₀ (by positivity : 0 < (Real.log x) ^ 4)).2
    calc
      2 * Real.sqrt x * Real.log x * (Real.log x) ^ 4 =
          (2 * (Real.log x) ^ 5) * Real.sqrt x := by ring
      _ ≤ (148 / 1000 : Real) * Real.sqrt x * Real.sqrt x :=
        mul_le_mul_of_nonneg_right hscaled' hsqrt_pos.le
      _ = (148 / 1000 : Real) * x := by
        calc
          (148 / 1000 : Real) * Real.sqrt x * Real.sqrt x =
              (148 / 1000 : Real) * (Real.sqrt x * Real.sqrt x) := by ring
          _ = (148 / 1000 : Real) * x := by
            rw [show Real.sqrt x * Real.sqrt x = x by
              simpa [pow_two] using Real.sq_sqrt hx_pos.le]
  have hdiff := Chebyshev.psi_sub_theta_le (x := x) (by linarith)
  have htheta_le_psi := Chebyshev.theta_le_psi x
  have hcorrection_abs :
      |Chebyshev.theta x - Chebyshev.psi x| ≤
        2 * Real.sqrt x * Real.log x := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr htheta_le_psi)]
    linarith
  calc
    |Chebyshev.theta x - x| ≤
        |Chebyshev.theta x - Chebyshev.psi x| +
          |Chebyshev.psi x - x| := by
      rw [show Chebyshev.theta x - x =
        (Chebyshev.theta x - Chebyshev.psi x) +
          (Chebyshev.psi x - x) by ring]
      exact abs_add_le _ _
    _ ≤ (148 / 1000 : Real) * x / (Real.log x) ^ 4 +
          A * x / (Real.log x) ^ 4 :=
      add_le_add (hcorrection_abs.trans hcorrection_sharp) hpsi
    _ = (A + 148 / 1000) * x / (Real.log x) ^ 4 := by ring

end

end PrimeFactorUnimodality
