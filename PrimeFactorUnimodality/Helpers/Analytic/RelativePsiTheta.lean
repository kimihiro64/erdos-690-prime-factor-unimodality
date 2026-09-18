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
