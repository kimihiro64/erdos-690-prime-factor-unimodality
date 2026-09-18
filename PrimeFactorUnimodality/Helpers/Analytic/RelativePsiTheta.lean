import Mathlib.NumberTheory.Chebyshev
import PrimeFactorUnimodality.Helpers.Analytic.ThetaFromPsi

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

def HasPsiRelativeError (ε : Real → Real) : Prop :=
  ∀ b : Real, 0 ≤ b → ∀ x : Real, Real.exp b ≤ x →
    |Chebyshev.psi x - x| ≤ ε b * x

/-! A tail log-fourth estimate supplies the relative form used by the
  prime-power correction argument.  The cutoff is kept explicit: below the
  cutoff a separate finite provider is required. -/
theorem psi_relative_error_of_logFourthError
    {A X b x : Real}
    (hXpos : 0 < X) (hlogX : 0 < Real.log X)
    (hb : Real.log X ≤ b) (hxb : Real.exp b ≤ x)
    (psiError : HasPsiLogFourthError A X) :
    |Chebyshev.psi x - x| ≤ (A / b ^ 4) * x := by
  have hX : X ≤ x := by
    calc
      X = Real.exp (Real.log X) := by rw [Real.exp_log hXpos]
      _ ≤ Real.exp b := Real.exp_le_exp.mpr hb
      _ ≤ x := hxb
  have hlogX_nonneg : 0 ≤ Real.log X := hlogX.le
  have hb_nonneg : 0 ≤ b := hlogX_nonneg.trans hb
  have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos b) hxb
  have hlogx : b ≤ Real.log x := by
    exact (Real.le_log_iff_exp_le hx_pos).2 hxb
  have hpow : b ^ 4 ≤ (Real.log x) ^ 4 := by
    exact pow_le_pow_left₀ hb_nonneg hlogx 4
  have hpow_pos : 0 < b ^ 4 := pow_pos (lt_of_lt_of_le hlogX hb) 4
  have hscaled := psiError x hX
  have hAprod : 0 ≤ A * (X / (Real.log X) ^ 4) := by
    have hcut := psiError X le_rfl
    have hnonneg := abs_nonneg (Chebyshev.psi X - X)
    exact le_trans hnonneg (by simpa [div_eq_mul_inv, mul_assoc] using hcut)
  have hA : 0 ≤ A := by
    by_contra hAneg
    have hA_lt : A < 0 := lt_of_not_ge hAneg
    have hfactor : 0 < X / (Real.log X) ^ 4 :=
      div_pos hXpos (pow_pos hlogX 4)
    have : A * (X / (Real.log X) ^ 4) < 0 :=
      mul_neg_of_neg_of_pos hA_lt hfactor
    linarith
  have hratio : x / (Real.log x) ^ 4 ≤ x / b ^ 4 := by
    exact div_le_div_of_nonneg_left hx_pos.le hpow_pos hpow
  calc
    |Chebyshev.psi x - x| ≤ A * x / (Real.log x) ^ 4 := hscaled
    _ ≤ A * (x / b ^ 4) := by
      calc
        A * x / (Real.log x) ^ 4 = A * (x / (Real.log x) ^ 4) := by ring
        _ ≤ A * (x / b ^ 4) := mul_le_mul_of_nonneg_left hratio hA
    _ = (A / b ^ 4) * x := by ring

/-! The elementary Chebyshev bound also controls the absolute error, not just
  `psi` from above.  This is the finite-side branch of the global provider
  below. -/
theorem psi_abs_error_le_elementary
    {x : Real} (hx : 0 ≤ x) :
    |Chebyshev.psi x - x| ≤ (Real.log 4 + 4) * x := by
  have hpsi := Chebyshev.psi_le_const_mul_self hx
  have hnonneg := Chebyshev.psi_nonneg x
  have hlog : 0 ≤ Real.log (4 : Real) := by positivity
  have hcoef : 1 ≤ Real.log 4 + 4 := by linarith
  rw [abs_le]
  constructor <;> nlinarith

/-! The unconditional, non-decaying provider.  It is not strong enough for
  Dusart's sharp tail, but records the complete elementary baseline in the
  same interface and supplies the small-side branch independently. -/
theorem hasPsiRelativeError_elementary :
    HasPsiRelativeError (fun _ : Real => Real.log 4 + 4) := by
  intro b hb x hxb
  exact psi_abs_error_le_elementary (le_trans (Real.exp_pos b).le hxb)

/-! Package a tail log-fourth estimate as a global relative-error function.
  Below the cutoff the function deliberately uses the unconditional
  Chebyshev constant; above it, it is exactly the decaying analytic error. -/
theorem hasPsiRelativeError_of_logFourthError
    {A X : Real} (hXpos : 0 < X) (hlogX : 0 < Real.log X)
    (psiError : HasPsiLogFourthError A X) :
    HasPsiRelativeError (fun b : Real =>
      if Real.log X ≤ b then A / b ^ 4 else Real.log 4 + 4) := by
  intro b hb x hxb
  by_cases hcut : Real.log X ≤ b
  · change |Chebyshev.psi x - x| ≤
      (if Real.log X ≤ b then A / b ^ 4 else Real.log 4 + 4) * x
    simp only [if_pos hcut]
    exact psi_relative_error_of_logFourthError
      hXpos hlogX hcut hxb psiError
  · change |Chebyshev.psi x - x| ≤
      (if Real.log X ≤ b then A / b ^ 4 else Real.log 4 + 4) * x
    simp only [if_neg hcut]
    exact psi_abs_error_le_elementary (le_trans (Real.exp_pos b).le hxb)

/-! Conversely, a relative ψ theorem with a logarithmic decay estimate gives
  the tail predicate consumed by the explicit theta and prime-counting
  interfaces.  This is the exact provider boundary for an independently
  formalized BKLNW/Dusart estimate. -/
theorem hasPsiLogFourthError_of_relativeError_decay
    {ε : Real → Real} {A X : Real}
    (hXpos : 0 < X) (hlogX : 0 < Real.log X)
    (hε : HasPsiRelativeError ε)
    (hdecay : ∀ b : Real, Real.log X ≤ b → ε b ≤ A / b ^ 4) :
    HasPsiLogFourthError A X := by
  intro x hx
  have hx_pos : 0 < x := lt_of_lt_of_le hXpos hx
  have hXgt1 : 1 < X := (Real.log_pos_iff hXpos.le).mp hlogX
  have hlogx_pos : 0 < Real.log x :=
    Real.log_pos (lt_of_lt_of_le hXgt1 hx)
  have hlogX_le : Real.log X ≤ Real.log x :=
    Real.log_le_log hXpos hx
  have hrel : |Chebyshev.psi x - x| ≤ ε (Real.log x) * x := by
    simpa [Real.exp_log hx_pos] using
      hε (Real.log x) hlogx_pos.le x (le_of_eq (Real.exp_log hx_pos))
  have hdec := hdecay (Real.log x) hlogX_le
  calc
    |Chebyshev.psi x - x| ≤ ε (Real.log x) * x := hrel
    _ ≤ (A / (Real.log x) ^ 4) * x :=
      mul_le_mul_of_nonneg_right hdec hx_pos.le
    _ = A * x / (Real.log x) ^ 4 := by ring

theorem theta_upper_of_psi_relative_error
    {x ε : Real}
    (hpsi : |Chebyshev.psi x - x| ≤ ε * x) :
    Chebyshev.theta x ≤ (1 + ε) * x := by
  have hupper : Chebyshev.psi x ≤ (1 + ε) * x := by
    have habs := (abs_le.mp hpsi).2
    linarith
  exact (Chebyshev.theta_le_psi x).trans hupper

/-! The lower half of the standard `psi`-to-`theta` argument.  The analytic
input is deliberately a relative error for `psi`; the only additional input
is a uniform upper bound for `psi` at the three prime-power roots. -/
theorem theta_lower_of_psi_relative_error
    {b x ε c : Real} (hx : Real.exp b ≤ x)
    (hpsi : |Chebyshev.psi x - x| ≤ ε * x)
    (hroot : ∀ y : Real, 0 ≤ y → Chebyshev.psi y ≤ c * y)
    (hc : 0 ≤ c) :
    (1 - ε - c * (Real.exp (-b / 2) + Real.exp (-2 * b / 3) +
      Real.exp (-4 * b / 5))) * x ≤ Chebyshev.theta x := by
  have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos b) hx
  have hhalf := hroot (x ^ (1 / 2 : Real)) (by positivity)
  have hthird := hroot (x ^ (1 / 3 : Real)) (by positivity)
  have hfifth := hroot (x ^ (1 / 5 : Real)) (by positivity)
  have hpsi_lower : (1 - ε) * x ≤ Chebyshev.psi x := by
    have habs := (abs_le.mp hpsi).1
    linarith
  have hprimepowers :=
    Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have htheta_upper :
      Chebyshev.psi x ≤ Chebyshev.theta x +
        Chebyshev.psi (x ^ (2 : Real)⁻¹) +
        Chebyshev.psi (x ^ (3 : Real)⁻¹) +
        Chebyshev.psi (x ^ (5 : Real)⁻¹) := by
    linarith
  have hlog_x : b ≤ Real.log x := by
    rw [← Real.log_exp b]
    exact Real.log_le_log (Real.exp_pos b) hx
  have hhalf_scale : x ^ (1 / 2 : Real) ≤ x * Real.exp (-b / 2) := by
    rw [← Real.log_le_log_iff (by positivity) (mul_pos hx_pos (Real.exp_pos _))]
    rw [Real.log_rpow hx_pos, Real.log_mul hx_pos.ne' (Real.exp_pos _).ne',
      Real.log_exp]
    nlinarith
  have hthird_scale : x ^ (1 / 3 : Real) ≤ x * Real.exp (-2 * b / 3) := by
    rw [← Real.log_le_log_iff (by positivity) (mul_pos hx_pos (Real.exp_pos _))]
    rw [Real.log_rpow hx_pos, Real.log_mul hx_pos.ne' (Real.exp_pos _).ne',
      Real.log_exp]
    nlinarith
  have hfifth_scale : x ^ (1 / 5 : Real) ≤ x * Real.exp (-4 * b / 5) := by
    rw [← Real.log_le_log_iff (by positivity) (mul_pos hx_pos (Real.exp_pos _))]
    rw [Real.log_rpow hx_pos, Real.log_mul hx_pos.ne' (Real.exp_pos _).ne',
      Real.log_exp]
    nlinarith
  have hroot_sum :
      Chebyshev.psi (x ^ (2 : Real)⁻¹) +
        Chebyshev.psi (x ^ (3 : Real)⁻¹) +
        Chebyshev.psi (x ^ (5 : Real)⁻¹) ≤
      c * x * (Real.exp (-b / 2) + Real.exp (-2 * b / 3) +
        Real.exp (-4 * b / 5)) := by
    have hhalf' : Chebyshev.psi (x ^ (2 : Real)⁻¹) ≤
        c * (x ^ (1 / 2 : Real)) := by simpa [one_div] using hhalf
    have hthird' : Chebyshev.psi (x ^ (3 : Real)⁻¹) ≤
        c * (x ^ (1 / 3 : Real)) := by simpa [one_div] using hthird
    have hfifth' : Chebyshev.psi (x ^ (5 : Real)⁻¹) ≤
        c * (x ^ (1 / 5 : Real)) := by simpa [one_div] using hfifth
    nlinarith [mul_le_mul_of_nonneg_left hhalf_scale hc,
      mul_le_mul_of_nonneg_left hthird_scale hc,
      mul_le_mul_of_nonneg_left hfifth_scale hc]
  linarith

/-! Mathlib's elementary Chebyshev estimate is enough for the uniform root
  bound used in the prime-power correction.  This is intentionally separate
  from the sharp relative error theorem: the latter is the genuine Dusart
  obligation, while this auxiliary bound is already proved unconditionally. -/
theorem psi_root_bound_elementary :
    ∀ y : Real, 0 ≤ y →
      Chebyshev.psi y ≤ (Real.log 4 + 4) * y := by
  intro y hy
  exact Chebyshev.psi_le_const_mul_self hy

/-! A lower prime-power correction used in Dusart's theta estimates.  This is
  obtained directly from Mathlib's Costa--Pereira decomposition of `psi`; no
  explicit Dusart estimate is involved. -/
theorem psi_sub_theta_ge_theta_sqrt {x : Real} (hx : 2 ≤ x) :
    Chebyshev.theta (x ^ (1 / 2 : Real)) ≤
      Chebyshev.psi x - Chebyshev.theta x := by
  have hdecomp := Chebyshev.psi_sub_theta_ge_psi_add_psi_add_psi
    (x := x) (by linarith)
  have hroot := Chebyshev.theta_le_psi (x ^ (1 / 2 : Real))
  have hroot' : Chebyshev.theta (x ^ (1 / 2 : Real)) ≤
      Chebyshev.psi (x ^ (2 : Real)⁻¹) := by
    simpa [one_div] using hroot
  linarith [Chebyshev.psi_nonneg (x ^ (3 : Real)⁻¹),
    Chebyshev.psi_nonneg (x ^ (7 : Real)⁻¹)]

/-! The first numerical lower comparison in Dusart's Proposition 4.3 is
  elementary at its stated cutoff. -/
theorem psi_sub_theta_ge_one_sub_log_sqrt {x : Real} (hx : 121 ≤ x) :
    1 - (4 * Real.log 2) / Real.log x * Real.sqrt x ≤
      Chebyshev.psi x - Chebyshev.theta x := by
  have hx_pos : 0 < x := by linarith
  have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx_pos
  have hlog_le : Real.log x ≤ 2 * Real.sqrt x := by
    have h := Real.log_le_rpow_div (x := x) (ε := (1 / 2 : Real))
      hx_pos.le (by norm_num)
    simpa [Real.sqrt_eq_rpow, mul_comm] using h
  have hlog2 : (1 : Real) / 2 < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hratio : 1 ≤ (4 * Real.log 2) / Real.log x * Real.sqrt x := by
    rw [show (4 * Real.log 2) / Real.log x * Real.sqrt x =
      (4 * Real.log 2 * Real.sqrt x) / Real.log x by ring]
    apply (le_div_iff₀ hlog_pos).2
    nlinarith
  have hnonneg : 0 ≤ Chebyshev.psi x - Chebyshev.theta x := by
    linarith [Chebyshev.theta_le_psi x]
  linarith

/-! The same correction, with Mathlib's explicit elementary lower estimate for
  `theta (sqrt x)` left visible. -/
theorem psi_sub_theta_ge_elementary_sqrt_lower {x : Real} (hx : 121 ≤ x) :
    (Real.sqrt x - 1) * Real.log 2 - Real.log (Real.sqrt x + 2) -
        2 * Real.sqrt (Real.sqrt x) * Real.log (Real.sqrt x) ≤
      Chebyshev.psi x - Chebyshev.theta x := by
  have hx_two : 2 ≤ x := by linarith
  have hsqrt_two : 1 ≤ Real.sqrt x := by
    have hsquare : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (by positivity)
    have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    nlinarith
  have htheta := Chebyshev.theta_ge' hsqrt_two
  have hcorr := psi_sub_theta_ge_theta_sqrt hx_two
  have hrewrite : x ^ (1 / 2 : Real) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
  rw [hrewrite] at hcorr
  exact htheta.trans hcorr

/-! The pointwise form is the one needed for a decaying explicit error: use
  the logarithm of the current argument rather than freezing the error at a
  cutoff. -/
theorem theta_lower_of_psi_relative_error_at_log
    {x c : Real} {ε : Real → Real}
    (hε : HasPsiRelativeError ε)
    (hroot : ∀ y : Real, 0 ≤ y → Chebyshev.psi y ≤ c * y)
    (hc : 0 ≤ c) (hx : 1 < x) :
    (1 - ε (Real.log x) - c *
      (Real.exp (-Real.log x / 2) +
        Real.exp (-2 * Real.log x / 3) +
        Real.exp (-4 * Real.log x / 5))) * x ≤
      Chebyshev.theta x := by
  have hx_pos : 0 < x := by linarith
  have hlogx_nonneg : 0 ≤ Real.log x := (Real.log_pos hx).le
  have hpsi := hε (Real.log x) hlogx_nonneg x
    (le_of_eq (Real.exp_log hx_pos))
  exact theta_lower_of_psi_relative_error
    (b := Real.log x) (x := x) (ε := ε (Real.log x))
    (c := c) (le_of_eq (Real.exp_log hx_pos)) hpsi hroot hc

theorem theta_lower_of_psi_relative_error_elementary
    {b x ε : Real} (hx : Real.exp b ≤ x)
    (hpsi : |Chebyshev.psi x - x| ≤ ε * x) :
    (1 - ε - (Real.log 4 + 4) *
      (Real.exp (-b / 2) + Real.exp (-2 * b / 3) +
        Real.exp (-4 * b / 5))) * x ≤ Chebyshev.theta x := by
  apply theta_lower_of_psi_relative_error hx hpsi
  · intro y hy
    exact Chebyshev.psi_le_const_mul_self hy
  · positivity

theorem theta_bounds_of_psi_relative_error_elementary
    {ε : Real → Real} {b x : Real}
    (hε : HasPsiRelativeError ε) (hb : 0 ≤ b)
    (hx : Real.exp b ≤ x) :
    (1 - ε b - (Real.log 4 + 4) *
      (Real.exp (-b / 2) + Real.exp (-2 * b / 3) +
        Real.exp (-4 * b / 5))) * x ≤ Chebyshev.theta x ∧
      Chebyshev.theta x ≤ (1 + ε b) * x := by
  refine ⟨theta_lower_of_psi_relative_error_elementary hx (hε b hb x hx), ?_⟩
  exact theta_upper_of_psi_relative_error (hε b hb x hx)

theorem theta_bounds_of_psi_relative_error
    {ε : Real → Real} {b x c : Real}
    (hε : HasPsiRelativeError ε) (hb : 0 ≤ b)
    (hx : Real.exp b ≤ x)
    (hroot : ∀ y : Real, 0 ≤ y → Chebyshev.psi y ≤ c * y)
    (hc : 0 ≤ c) :
    (1 - ε b - c * (Real.exp (-b / 2) + Real.exp (-2 * b / 3) +
      Real.exp (-4 * b / 5))) * x ≤ Chebyshev.theta x ∧
      Chebyshev.theta x ≤ (1 + ε b) * x := by
  refine ⟨theta_lower_of_psi_relative_error hx (hε b hb x hx) hroot hc, ?_⟩
  exact theta_upper_of_psi_relative_error (hε b hb x hx)

end

end PrimeFactorUnimodality
