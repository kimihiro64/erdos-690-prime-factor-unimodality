import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.CorrectionMonotonicity

set_option autoImplicit false

/-! # Formula bounds for a Dusart theta-table interval

These non-certificate definitions and monotonicity lemmas are independent
of generated prime-interval rows. Endpoint transport applies to sufficiently
small subintervals, not automatically to an entire published table range.
-/

namespace PrimeFactorUnimodality

noncomputable section

structure DusartThetaTable66CoefficientData where
  left : Nat
  right : Nat
  a0 : Real
  b0 : Real
  a1 : Real
  b1 : Real
  a2 : Real
  b2 : Real

/-! All six published Table 6.6 inequalities for one coefficient row are
    carried together.  This keeps the row certificate data independent of the
    common finite-range assembler. -/
structure DusartThetaTable66FormulaBounds
    (data : DusartThetaTable66CoefficientData) : Prop where
  lower_zero : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
    data.a0 * x ≤ Chebyshev.theta x
  upper_zero : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
    Chebyshev.theta x ≤ data.b0 * x
  lower_one : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
    x - data.a1 * x / Real.log x ≤ Chebyshev.theta x
  upper_one : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
    Chebyshev.theta x ≤ x + data.b1 * x / Real.log x
  lower_two : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
    x - data.a2 * x / Real.log x ^ 2 ≤ Chebyshev.theta x
  upper_two : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      Chebyshev.theta x ≤ x + data.b2 * x / Real.log x ^ 2

/-! The constant-coefficient columns can be transported from endpoint bounds
    using only monotonicity of `theta`.  The logarithmic correction columns
    retain their own interval arguments. -/
theorem dusartThetaTable66_constant_bounds_of_endpoints
    (data : DusartThetaTable66CoefficientData)
    (ha0 : 0 ≤ data.a0) (hb0 : 0 ≤ data.b0)
    (lower_endpoint : data.a0 * (data.right : Real) ≤
      Chebyshev.theta data.left)
    (upper_endpoint : Chebyshev.theta data.right ≤
      data.b0 * (data.left : Real)) :
    (∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      data.a0 * x ≤ Chebyshev.theta x) ∧
    (∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      Chebyshev.theta x ≤ data.b0 * x) := by
  constructor
  · intro x hleft hright
    have hleft_le_theta : Chebyshev.theta data.left ≤
        Chebyshev.theta x := Chebyshev.theta_mono hleft
    have hscale : data.a0 * x ≤ data.a0 * (data.right : Real) := by
      exact mul_le_mul_of_nonneg_left hright ha0
    exact hscale.trans (lower_endpoint.trans hleft_le_theta)
  · intro x hleft hright
    have hright_theta : Chebyshev.theta x ≤
        Chebyshev.theta data.right := Chebyshev.theta_mono hright
    have hscale : data.b0 * (data.left : Real) ≤ data.b0 * x := by
      exact mul_le_mul_of_nonneg_left hleft hb0
    exact hright_theta.trans (upper_endpoint.trans hscale)

/-! The four logarithmic columns have the same endpoint shape once their
    correction functions have been shown monotone on the row.  This keeps
    the finite numerical input to one pair of endpoint inequalities per
    column; the monotonicity proofs remain ordinary real analysis. -/
theorem dusartThetaTable66_formula_bounds_of_monotone_corrections
    (data : DusartThetaTable66CoefficientData)
    (hle : data.left ≤ data.right)
    (lower_zero : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      data.a0 * x ≤ Chebyshev.theta x)
    (upper_zero : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      Chebyshev.theta x ≤ data.b0 * x)
    (lower_one_mono : MonotoneOn
      (fun x : Real => x - data.a1 * x / Real.log x)
      (Set.Icc (data.left : Real) (data.right : Real)))
    (upper_one_mono : MonotoneOn
      (fun x : Real => x + data.b1 * x / Real.log x)
      (Set.Icc (data.left : Real) (data.right : Real)))
    (lower_two_mono : MonotoneOn
      (fun x : Real => x - data.a2 * x / Real.log x ^ 2)
      (Set.Icc (data.left : Real) (data.right : Real)))
    (upper_two_mono : MonotoneOn
      (fun x : Real => x + data.b2 * x / Real.log x ^ 2)
      (Set.Icc (data.left : Real) (data.right : Real)))
    (lower_one_endpoint :
      data.right - data.a1 * data.right / Real.log data.right ≤
        Chebyshev.theta data.left)
    (upper_one_endpoint :
      Chebyshev.theta data.right ≤
        data.left + data.b1 * data.left / Real.log data.left)
    (lower_two_endpoint :
      data.right - data.a2 * data.right / Real.log data.right ^ 2 ≤
        Chebyshev.theta data.left)
    (upper_two_endpoint :
      Chebyshev.theta data.right ≤
        data.left + data.b2 * data.left / Real.log data.left ^ 2) :
    DusartThetaTable66FormulaBounds data := by
  refine {
    lower_zero := lower_zero
    upper_zero := upper_zero
    lower_one := ?_
    upper_one := ?_
    lower_two := ?_
    upper_two := ?_ }
  · intro x hleft hright
    have hxmem : x ∈ Set.Icc (data.left : Real) (data.right : Real) :=
      ⟨hleft, hright⟩
    have hrightmem : (data.right : Real) ∈
        Set.Icc (data.left : Real) (data.right : Real) := by
      exact ⟨by exact_mod_cast hle, le_rfl⟩
    have hmono := lower_one_mono hxmem hrightmem hright
    have htheta := Chebyshev.theta_mono hleft
    exact hmono.trans (lower_one_endpoint.trans htheta)
  · intro x hleft hright
    have hxmem : x ∈ Set.Icc (data.left : Real) (data.right : Real) :=
      ⟨hleft, hright⟩
    have hleftmem : (data.left : Real) ∈
        Set.Icc (data.left : Real) (data.right : Real) := by
      exact ⟨le_rfl, by exact_mod_cast hle⟩
    have hmono := upper_one_mono hleftmem hxmem hleft
    have htheta := Chebyshev.theta_mono hright
    exact htheta.trans (upper_one_endpoint.trans hmono)
  · intro x hleft hright
    have hxmem : x ∈ Set.Icc (data.left : Real) (data.right : Real) :=
      ⟨hleft, hright⟩
    have hrightmem : (data.right : Real) ∈
        Set.Icc (data.left : Real) (data.right : Real) := by
      exact ⟨by exact_mod_cast hle, le_rfl⟩
    have hmono := lower_two_mono hxmem hrightmem hright
    have htheta := Chebyshev.theta_mono hleft
    exact hmono.trans (lower_two_endpoint.trans htheta)
  · intro x hleft hright
    have hxmem : x ∈ Set.Icc (data.left : Real) (data.right : Real) :=
      ⟨hleft, hright⟩
    have hleftmem : (data.left : Real) ∈
        Set.Icc (data.left : Real) (data.right : Real) := by
      exact ⟨le_rfl, by exact_mod_cast hle⟩
    have hmono := upper_two_mono hleftmem hxmem hleft
    have htheta := Chebyshev.theta_mono hright
    exact htheta.trans (upper_two_endpoint.trans hmono)

theorem dusartThetaTable66_formula_bounds_of_endpoints
    (data : DusartThetaTable66CoefficientData)
    (hle : data.left ≤ data.right)
    (hleft : (1 : Real) < data.left)
    (hlog_left : (2 : Real) ≤ Real.log data.left)
    (lower_zero : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      data.a0 * x ≤ Chebyshev.theta x)
    (upper_zero : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      Chebyshev.theta x ≤ data.b0 * x)
    (hcoeff : 0 ≤ data.a1 ∧ data.a1 ≤ 1 ∧ -1 ≤ data.b1 ∧ data.b1 ≤ 0 ∧
      0 ≤ data.a2 ∧ data.a2 ≤ 1 ∧ -1 ≤ data.b2 ∧ data.b2 ≤ 0)
    (lower_one_endpoint :
      data.right - data.a1 * data.right / Real.log data.right ≤
        Chebyshev.theta data.left)
    (upper_one_endpoint :
      Chebyshev.theta data.right ≤
        data.left + data.b1 * data.left / Real.log data.left)
    (lower_two_endpoint :
      data.right - data.a2 * data.right / Real.log data.right ^ 2 ≤
        Chebyshev.theta data.left)
    (upper_two_endpoint :
      Chebyshev.theta data.right ≤
        data.left + data.b2 * data.left / Real.log data.left ^ 2) :
    DusartThetaTable66FormulaBounds data := by
  have hmono_lower_one := id_sub_mul_id_div_log_monotoneOn
    (a := (data.left : Real)) (c := data.a1) hleft (by linarith)
      hcoeff.1 hcoeff.2.1
  have hmono_upper_one := id_add_mul_id_div_log_monotoneOn
    (a := (data.left : Real)) (b := data.b1) hleft (by linarith)
      hcoeff.2.2.1 hcoeff.2.2.2.1
  have hmono_lower_two := id_sub_mul_id_div_log_sq_monotoneOn
    (a := (data.left : Real)) (c := data.a2) hleft hlog_left
      hcoeff.2.2.2.2.1 hcoeff.2.2.2.2.2.1
  have hmono_upper_two := id_add_mul_id_div_log_sq_monotoneOn
    (a := (data.left : Real)) (b := data.b2) hleft hlog_left
      hcoeff.2.2.2.2.2.2.1 hcoeff.2.2.2.2.2.2.2
  apply dusartThetaTable66_formula_bounds_of_monotone_corrections data hle
    lower_zero upper_zero
  · intro x hx y hy hxy
    exact hmono_lower_one hx.1 hy.1 hxy
  · intro x hx y hy hxy
    exact hmono_upper_one hx.1 hy.1 hxy
  · intro x hx y hy hxy
    exact hmono_lower_two hx.1 hy.1 hxy
  · intro x hx y hy hxy
    exact hmono_upper_two hx.1 hy.1 hxy
  · exact lower_one_endpoint
  · exact upper_one_endpoint
  · exact lower_two_endpoint
  · exact upper_two_endpoint

theorem log_ge_two_of_eight_le {x : Real} (hx : (8 : Real) ≤ x) :
    (2 : Real) ≤ Real.log x := by
  have hlog8 : Real.log (8 : Real) ≤ Real.log x := by
    exact Real.log_le_log (by norm_num) hx
  rw [show (8 : Real) = 2 ^ (3 : Nat) by norm_num, Real.log_pow] at hlog8
  norm_num at hlog8
  nlinarith [Real.log_two_gt_d9]

end

end PrimeFactorUnimodality
