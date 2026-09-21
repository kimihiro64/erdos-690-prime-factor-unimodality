import Mathlib.NumberTheory.Chebyshev
import PrimeFactorUnimodality.Helpers.Analytic.DecayToLogFourth
import PrimeFactorUnimodality.Helpers.Analytic.PrimorialLogBounds
import PrimeFactorUnimodality.Helpers.Analytic.RelativePsiTheta
import PrimeFactorUnimodality.Helpers.Analytic.ShortIntervalPrime
import PrimeFactorUnimodality.Helpers.Analytic.ThetaFromPsi

set_option autoImplicit false

/-! # Interfaces for explicit Chebyshev-theta estimates -/

namespace PrimeFactorUnimodality

noncomputable section

/-- The two Dusart theta estimates used by Wang--Crapis.  Their analytic
provider is intentionally separated from all downstream primorial algebra. -/
def HasDusartThetaBounds : Prop :=
  (∀ x : Real, 0 < x →
    Chebyshev.theta x < x * (1 + 1 / 36260)) ∧
  (∀ x : Real, 2 < x →
    x * (1 - (12323 / 10000 : Real) / Real.log x) <
      Chebyshev.theta x)

/-! Published theta estimates are often supplied as a symmetric error bound.
The small-`x` upper estimate is one-sided: a symmetric absolute estimate there
would be false (for example, `theta 1 = 0`).  The second component is the
symmetric estimate on the range where the published lower bound starts. -/
def HasDusartSymmetricThetaBounds : Prop :=
  (∀ x : Real, 0 < x →
    Chebyshev.theta x - x < x / 36260) ∧
  (∀ x : Real, 2 < x →
    |Chebyshev.theta x - x| <
      (12323 / 10000 : Real) * x / Real.log x)

/-! A finite-range presentation of the same estimates.  This is useful for
the explicit provider because the logarithm-cubed error theorem handles the
unbounded tail, while the remaining interval is a bounded numerical check. -/
def HasDusartSymmetricThetaBoundsBelow (X : Real) : Prop :=
  (∀ x : Real, 0 < x → x ≤ X →
    Chebyshev.theta x - x < x / 36260) ∧
  (∀ x : Real, 2 < x → x ≤ X →
    |Chebyshev.theta x - x| <
      (12323 / 10000 : Real) * x / Real.log x)

/-! Schoenfeld's finite prefix is naturally stronger than the published
upper-error budget.  Keep that input separate so the finite computation can
prove `theta x < x` directly and the analytic tail can provide the relaxed
global constant. -/
def HasStrictThetaUpperBelow (X : Real) : Prop :=
  ∀ x : Real, 0 < x → x ≤ X → Chebyshev.theta x < x

theorem hasDusartSymmetricThetaBoundsBelow_of_strict_theta_prefix
    {X : Real} (upperPrefix : HasStrictThetaUpperBelow X)
    (lower : ∀ x : Real, 2 < x → x ≤ X →
      |Chebyshev.theta x - x| <
        (12323 / 10000 : Real) * x / Real.log x) :
    HasDusartSymmetricThetaBoundsBelow X := by
  constructor
  · intro x hx hX
    have hstrict := upperPrefix x hx hX
    nlinarith
  · exact lower

/-! A finite fourth-power error certificate can supply the same symmetric
finite theta interface once its numerical scale is checked on the suffix.
The strict upper prefix is kept separate because the published upper bound
is one-sided below the logarithmic cutoff. -/
theorem hasDusartSymmetricThetaBoundsBelow_of_strict_prefix_and_fourth_error
    {A X x₀ : Real}
    (h2x₀ : (2 : Real) ≤ x₀)
    (upperPrefix : HasStrictThetaUpperBelow x₀)
    (lowerPrefix : ∀ x : Real, 2 < x → x ≤ x₀ →
      |Chebyshev.theta x - x| <
        (12323 / 10000 : Real) * x / Real.log x)
    (error : HasThetaLogFourthErrorBelow A X)
    (upperScale : ∀ x : Real, x₀ ≤ x → x ≤ X →
      A / (Real.log x) ^ 4 < (1 : Real) / 36260)
    (lowerScale : ∀ x : Real, 2 < x → x₀ ≤ x → x ≤ X →
      A / (Real.log x) ^ 4 <
        (12323 / 10000 : Real) / Real.log x) :
    HasDusartSymmetricThetaBoundsBelow X := by
  constructor
  · intro x hx hX
    by_cases hsmall : x ≤ x₀
    · have hstrict := upperPrefix x hx hsmall
      nlinarith
    · have hleft : x₀ ≤ x := le_of_not_ge hsmall
      have herror := error x (by linarith) hX
      have hscale := upperScale x hleft hX
      have hxpos : 0 < x := by linarith
      have herror' : |Chebyshev.theta x - x| < x / 36260 := by
        calc
          |Chebyshev.theta x - x| ≤
              A * x / (Real.log x) ^ 4 := herror
          _ = (A / (Real.log x) ^ 4) * x := by ring
          _ < ((1 : Real) / 36260) * x :=
            mul_lt_mul_of_pos_right hscale hxpos
          _ = x / 36260 := by ring
      exact (le_abs_self (Chebyshev.theta x - x)).trans_lt herror'
  · intro x hx hX
    by_cases hsmall : x ≤ x₀
    · exact (hasDusartSymmetricThetaBoundsBelow_of_strict_theta_prefix
        upperPrefix lowerPrefix).2 x hx hsmall
    · have hleft : x₀ ≤ x := le_of_not_ge hsmall
      have herror := error x (by linarith) hX
      have hscale := lowerScale x hx hleft hX
      have hxpos : 0 < x := by linarith
      have herror' : |Chebyshev.theta x - x| <
          (12323 / 10000 : Real) * x / Real.log x := by
        calc
          |Chebyshev.theta x - x| ≤
              A * x / (Real.log x) ^ 4 := herror
          _ = (A / (Real.log x) ^ 4) * x := by ring
          _ < ((12323 / 10000 : Real) / Real.log x) * x :=
            mul_lt_mul_of_pos_right hscale hxpos
          _ = (12323 / 10000 : Real) * x / Real.log x := by ring
      exact herror'

/-! The unbounded half of the published theta estimate.  Keeping this as a
tail-only predicate lets the source-level PNT proof discharge the analytic
tail independently of the finite endpoint table. -/
def HasDusartSymmetricThetaBoundsAbove (X : Real) : Prop :=
  (∀ x : Real, X ≤ x →
    Chebyshev.theta x - x < x / 36260) ∧
  (∀ x : Real, 2 < x → X ≤ x →
    |Chebyshev.theta x - x| <
      (12323 / 10000 : Real) * x / Real.log x)

theorem hasDusartSymmetricThetaBoundsBelow_mono
    {X Y : Real} (hXY : X ≤ Y)
    (finite : HasDusartSymmetricThetaBoundsBelow Y) :
    HasDusartSymmetricThetaBoundsBelow X := by
  constructor
  · intro x hx hX
    exact finite.1 x hx (hX.trans hXY)
  · intro x hx hX
    exact finite.2 x hx (hX.trans hXY)

theorem hasDusartSymmetricThetaBoundsAbove_of_logFourthError
    {A X : Real} (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (hA0 : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthErrorAbove A X) :
    HasDusartSymmetricThetaBoundsAbove X := by
  have hXone : (1 : Real) < X := by
    exact (Real.log_pos_iff hXpos.le).mp (by linarith)
  have hfull : HasThetaLogFourthError A X := by
    intro x hx
    exact thetaError x hx
  have hcube := hasThetaLogCubedError_of_logFourthError
    hXone hA0 hfull
  constructor
  · intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le hXpos hx
    have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hlogx : (10 : Real) < Real.log x := by
      exact hlogX.trans_le (Real.log_le_log hXpos hx)
    have htheta := hcube x hx
    have hfactor : 0 ≤ x / (Real.log x) ^ 3 := by
      exact div_nonneg hx_pos.le (pow_pos hlogx_pos 3).le
    have htheta' :
        |Chebyshev.theta x - x| ≤
          (12167 / 500000 : Real) * x / (Real.log x) ^ 3 := by
      calc
        |Chebyshev.theta x - x| ≤
            (A / Real.log X) * x / (Real.log x) ^ 3 := htheta
        _ = (A / Real.log X) * (x / (Real.log x) ^ 3) := by ring
        _ ≤ (12167 / 500000 : Real) *
            (x / (Real.log x) ^ 3) :=
          mul_le_mul_of_nonneg_right hA hfactor
        _ = (12167 / 500000 : Real) * x / (Real.log x) ^ 3 := by ring
    have hratio :
        (12167 / 500000 : Real) * x / (Real.log x) ^ 3 <
          x / 36260 := by
      rw [div_lt_div_iff₀ (pow_pos hlogx_pos 3) (by norm_num)]
      have hsq : (10 : Real) ^ 2 < (Real.log x) ^ 2 := by
        nlinarith [sq_nonneg (Real.log x - 10)]
      have hcube : (10 : Real) ^ 3 < (Real.log x) ^ 3 := by
        have hmul := mul_lt_mul_of_pos_left hsq hlogx_pos
        nlinarith
      have hconstant :
          (12167 / 500000 : Real) * 36260 < (10 : Real) ^ 3 := by
        norm_num
      have hscaled :
          (12167 / 500000 : Real) * 36260 < (Real.log x) ^ 3 :=
        hconstant.trans hcube
      convert (mul_lt_mul_of_pos_left hscaled hx_pos) using 1 <;> ring
    exact (le_abs_self (Chebyshev.theta x - x)).trans_lt
      (htheta'.trans_lt hratio)
  · intro x _hx2 hx
    have hx_pos : 0 < x := lt_of_lt_of_le hXpos hx
    have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hlogx : (10 : Real) < Real.log x := by
      exact hlogX.trans_le (Real.log_le_log hXpos hx)
    have htheta := hcube x hx
    have hfactor : 0 ≤ x / (Real.log x) ^ 3 := by
      exact div_nonneg hx_pos.le (pow_pos hlogx_pos 3).le
    have htheta' :
        |Chebyshev.theta x - x| ≤
          (12167 / 500000 : Real) * x / (Real.log x) ^ 3 := by
      calc
        |Chebyshev.theta x - x| ≤
            (A / Real.log X) * x / (Real.log x) ^ 3 := htheta
        _ = (A / Real.log X) * (x / (Real.log x) ^ 3) := by ring
        _ ≤ (12167 / 500000 : Real) *
            (x / (Real.log x) ^ 3) :=
          mul_le_mul_of_nonneg_right hA hfactor
        _ = (12167 / 500000 : Real) * x / (Real.log x) ^ 3 := by ring
    have hratio :
        (12167 / 500000 : Real) * x / (Real.log x) ^ 3 <
          (12323 / 10000 : Real) * x / Real.log x := by
      rw [div_lt_div_iff₀ (by positivity) hlogx_pos]
      have hlog_sq : (100 : Real) < (Real.log x) ^ 2 := by
        nlinarith [mul_self_lt_mul_self (by norm_num : (0 : Real) ≤ 10) hlogx]
      have hcoef : (12167 / 500000 : Real) <
          (12323 / 10000 : Real) * (Real.log x) ^ 2 := by
        nlinarith
      have hpos : 0 < x * Real.log x := mul_pos hx_pos hlogx_pos
      calc
        (12167 / 500000 : Real) * x * Real.log x =
            (12167 / 500000 : Real) * (x * Real.log x) := by ring
        _ < ((12323 / 10000 : Real) * (Real.log x) ^ 2) *
            (x * Real.log x) := mul_lt_mul_of_pos_right hcoef hpos
        _ = (12323 / 10000 : Real) * x * (Real.log x) ^ 3 := by ring
    exact htheta'.trans_lt hratio

/-! Normalized paper form of the theta error estimate.  This is the exact
`Eθ` statement used in Dusart's Theorem 4.2; the division by `x` is proved
here rather than left to a definitional conversion at a certificate boundary. -/
theorem dusartThetaTheorem4_2_normalized_of_logFourthError
    {A X : Real} (hXpos : 0 < X)
    (thetaError : HasThetaLogFourthErrorAbove A X) :
    ∀ x : Real, X ≤ x →
      |Chebyshev.theta x - x| / x ≤ A / (Real.log x) ^ (4 : ℕ) := by
  intro x hx
  have hx_pos : 0 < x := lt_of_lt_of_le hXpos hx
  have herror := thetaError x hx
  calc
    |Chebyshev.theta x - x| / x ≤
        (A * x / (Real.log x) ^ (4 : ℕ)) / x :=
      div_le_div_of_nonneg_right herror hx_pos.le
    _ = A / (Real.log x) ^ (4 : ℕ) := by
      field_simp [hx_pos.ne']

theorem hasDusartSymmetricThetaBounds_of_below_and_above
    {X : Real}
    (finite : HasDusartSymmetricThetaBoundsBelow X)
    (tail : HasDusartSymmetricThetaBoundsAbove X) :
    HasDusartSymmetricThetaBounds := by
  constructor
  · intro x hx
    by_cases hle : x ≤ X
    · exact finite.1 x hx hle
    · exact tail.1 x (le_of_lt (lt_of_not_ge hle))
  · intro x hx
    by_cases hle : x ≤ X
    · exact finite.2 x hx hle
    · exact tail.2 x hx (le_of_lt (lt_of_not_ge hle))

/-! The interval below `2` is not part of the numerical certificate.  The
theta sum is zero there, so its one-sided upper estimate is elementary. -/
theorem hasDusartSymmetricThetaBoundsBelow_of_upper_lower
    {X : Real}
    (upper : ∀ x : Real, 2 ≤ x → x ≤ X →
      Chebyshev.theta x - x < x / 36260)
    (lower : ∀ x : Real, 2 < x → x ≤ X →
      |Chebyshev.theta x - x| <
        (12323 / 10000 : Real) * x / Real.log x) :
    HasDusartSymmetricThetaBoundsBelow X := by
  constructor
  · intro x hx hxx
    by_cases hsmall : x < 2
    · rw [Chebyshev.theta_eq_zero_of_lt_two hsmall]
      nlinarith
    · exact upper x (le_of_not_gt hsmall) hxx
  · exact lower

theorem hasDusartSymmetricThetaBounds_of_below_and_logCubed_from
    {X : Real} (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (finite : HasDusartSymmetricThetaBoundsBelow X)
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) X) :
    HasDusartSymmetricThetaBounds := by
  constructor
  · intro x hx
    by_cases hsmall : x ≤ X
    · exact finite.1 x hx hsmall
    · have hlarge : X ≤ x := le_of_lt (lt_of_not_ge hsmall)
      have hlog := lt_of_lt_of_le hlogX (Real.log_le_log hXpos hlarge)
      have hlog_pos : 0 < Real.log x := by linarith
      have hlog_cube : (1000 : Real) < (Real.log x) ^ 3 := by
        nlinarith [mul_self_lt_mul_self (by norm_num : (0 : Real) ≤ 10) hlog,
          mul_pos (show (0 : Real) < Real.log x by linarith)
            (show (0 : Real) < (Real.log x) ^ 2 by positivity)]
      have htail := thetaError x hlarge
      have hratio :
          (12167 / 500000 : Real) * x / (Real.log x) ^ 3 < x / 36260 := by
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      exact (le_abs_self (Chebyshev.theta x - x)).trans_lt
        (htail.trans_lt hratio)
  · intro x hx
    by_cases hsmall : x ≤ X
    · exact finite.2 x hx hsmall
    · have hlarge : X ≤ x := le_of_lt (lt_of_not_ge hsmall)
      have hlog := lt_of_lt_of_le hlogX (Real.log_le_log hXpos hlarge)
      have hlog_pos : 0 < Real.log x := by linarith
      have htail := thetaError x hlarge
      have hratio :
          (12167 / 500000 : Real) * x / (Real.log x) ^ 3 <
            (12323 / 10000 : Real) * x / Real.log x := by
        rw [div_lt_div_iff₀ (by positivity) hlog_pos]
        have hlog_sq : (100 : Real) < (Real.log x) ^ 2 := by
          nlinarith [mul_self_lt_mul_self (by norm_num : (0 : Real) ≤ 10) hlog]
        have hcoef : (12167 / 500000 : Real) <
            (12323 / 10000 : Real) * (Real.log x) ^ 2 := by
          nlinarith
        have hpos : 0 < x * Real.log x := mul_pos (by linarith) hlog_pos
        calc
          (12167 / 500000 : Real) * x * Real.log x =
              (12167 / 500000 : Real) * (x * Real.log x) := by ring
          _ <
              ((12323 / 10000 : Real) * (Real.log x) ^ 2) *
                (x * Real.log x) := mul_lt_mul_of_pos_right hcoef hpos
          _ = (12323 / 10000 : Real) * x * (Real.log x) ^ 3 := by ring
      exact htail.trans_lt hratio

theorem hasDusartSymmetricThetaBounds_of_below_and_logCubed
    (finite : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    HasDusartSymmetricThetaBounds :=
  hasDusartSymmetricThetaBounds_of_below_and_logCubed_from
    (by norm_num) (log_large_x_gt_ten le_rfl) finite thetaError

theorem hasDusartSymmetricThetaBounds_of_below_and_logFourth
    {A : Real} (finite : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log (4e18 : Real) ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthError A (4e18 : Real)) :
    HasDusartSymmetricThetaBounds := by
  apply hasDusartSymmetricThetaBounds_of_below_and_logCubed finite
  intro x hx
  have hconverted := hasThetaLogCubedError_of_logFourthError
    (A := A) (X := (4e18 : Real)) (by norm_num) (by
      have hlog_pos : 0 < Real.log (4e18 : Real) := by
        exact Real.log_pos (by norm_num)
      exact hA_nonneg) thetaError
  exact (hconverted x hx).trans (by
    have hlog_pos : 0 < Real.log (4e18 : Real) := by
      exact Real.log_pos (by norm_num)
    have hx_pos : 0 < x := by linarith
    have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hfactor : 0 ≤ x / (Real.log x) ^ 3 := by
      exact div_nonneg hx_pos.le (pow_pos hlogx_pos 3).le
    calc
      (A / Real.log (4e18 : Real)) * x / (Real.log x) ^ 3 =
          (A / Real.log (4e18 : Real)) *
            (x / (Real.log x) ^ 3) := by ring
      _ ≤ (12167 / 500000 : Real) *
            (x / (Real.log x) ^ 3) :=
        mul_le_mul_of_nonneg_right hA hfactor
      _ = (12167 / 500000 : Real) * x / (Real.log x) ^ 3 := by ring)

theorem forty_two_lt_log_four_e18 :
    (42 : Real) < Real.log (4e18 : Real) := by
  have hbase : Real.exp 1 < (2.72 : Real) := by
    linarith [Real.exp_one_lt_d9]
  have hexp : Real.exp 42 < (4e18 : Real) := by
    calc
      Real.exp 42 = Real.exp 1 ^ 42 := by
        rw [show (42 : Real) = (42 : ℕ) * 1 by norm_num,
          Real.exp_nat_mul]
      _ < (2.72 : Real) ^ 42 := by
        exact pow_lt_pow_left₀ hbase (Real.exp_pos 1).le (by norm_num)
      _ < (4e18 : Real) := by norm_num
  have hlog : (42 : Real) < Real.log (4e18 : Real) := by
    exact (Real.lt_log_iff_exp_lt (by norm_num)).2 hexp
  exact hlog

theorem dusart_fourth_error_scale_at_four_e18
    {x : Real} (hx : (4e18 : Real) ≤ x) :
    (648 / 1000 : Real) / (Real.log x) ^ 4 < (1 : Real) / 36260 ∧
      (648 / 1000 : Real) / (Real.log x) ^ 4 <
        (12323 / 10000 : Real) / Real.log x := by
  have hlog : (42 : Real) < Real.log x :=
    forty_two_lt_log_four_e18.trans_le
      (Real.log_le_log (by norm_num) hx)
  have hlog_pos : 0 < Real.log x := by linarith
  have hsq : (42 : Real) ^ 2 ≤ (Real.log x) ^ 2 := by
    nlinarith [sq_nonneg (Real.log x - 42)]
  have hfour : (42 : Real) ^ 4 ≤ (Real.log x) ^ 4 := by
    nlinarith [sq_nonneg ((Real.log x) ^ 2 - 42 ^ 2)]
  constructor
  · apply (div_lt_iff₀ (by positivity : 0 < (Real.log x) ^ 4)).2
    nlinarith
  · apply (div_lt_div_iff₀ (by positivity : 0 < (Real.log x) ^ 4) hlog_pos).2
    nlinarith

theorem one_div_log_four_e18_le_dusart_constant :
    1 / Real.log (4e18 : Real) ≤ (12167 / 500000 : Real) := by
  have hlog := forty_two_lt_log_four_e18
  have hlog_pos : 0 < Real.log (4e18 : Real) := by linarith
  apply (div_le_iff₀ hlog_pos).2
  nlinarith

theorem hasDusartSymmetricThetaBounds_of_unit_logFourth
    (finite : HasDusartSymmetricThetaBoundsBelow (4e18 : Real))
    (thetaError : HasThetaLogFourthError 1 (4e18 : Real)) :
    HasDusartSymmetricThetaBounds :=
  hasDusartSymmetricThetaBounds_of_below_and_logFourth finite
    (by norm_num)
    one_div_log_four_e18_le_dusart_constant
    thetaError

theorem hasDusartSymmetricThetaBounds_of_below_and_logFourth_from
    {A X : Real} (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (finite : HasDusartSymmetricThetaBoundsBelow X)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthError A X) :
    HasDusartSymmetricThetaBounds := by
  have hX : 1 < X := by
    exact (Real.log_pos_iff hXpos.le).mp (by linarith [hlogX])
  apply hasDusartSymmetricThetaBounds_of_below_and_logCubed_from
    hXpos hlogX finite
  intro x hx
  have hconverted := hasThetaLogCubedError_of_logFourthError
    (A := A) (X := X) hX hA_nonneg thetaError
  exact (hconverted x hx).trans (by
    have hlog_pos : 0 < Real.log X := by linarith [hlogX]
    have hx_pos : 0 < x := by linarith
    have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hfactor : 0 ≤ x / (Real.log x) ^ 3 := by
      exact div_nonneg hx_pos.le (pow_pos hlogx_pos 3).le
    calc
      (A / Real.log X) * x / (Real.log x) ^ 3 =
          (A / Real.log X) * (x / (Real.log x) ^ 3) := by ring
      _ ≤ (12167 / 500000 : Real) *
            (x / (Real.log x) ^ 3) :=
        mul_le_mul_of_nonneg_right hA hfactor
      _ = (12167 / 500000 : Real) * x / (Real.log x) ^ 3 := by ring)

/-! The same adapter can start from the analytic estimate for `psi`.  The
prime-power correction is proved in `ThetaFromPsi`; this declaration keeps
that reduction visible at the Dusart provider boundary. -/
theorem hasDusartSymmetricThetaBounds_of_psiLogFourthError
    {A X : Real} (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (finite : HasDusartSymmetricThetaBoundsBelow X)
    (hXcutoff : (4e18 : Real) ≤ X)
    (hA_nonneg : 0 ≤ A)
    (hA_log : (A + 1) / Real.log X ≤ 12167 / 500000)
    (psiError : HasPsiLogFourthError A X) :
    HasDusartSymmetricThetaBounds := by
  apply hasDusartSymmetricThetaBounds_of_below_and_logFourth_from
    hXpos hlogX finite (by linarith) hA_log
  exact hasThetaLogFourthError_of_psiLogFourthError hXcutoff psiError

/-! Exact-cutoff provider form for a directly proved logarithmic-power decay
estimate.  The envelope is the only numerical tail obligation; the conversion
to the published theta constants is fully kernel-checked here. -/
theorem hasDusartSymmetricThetaBounds_of_logRpowDecay_of_envelope
    {c α X : Real} (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (finite : HasDusartSymmetricThetaBoundsBelow X)
    (hXcutoff : (4e18 : Real) ≤ X)
    (hA_log : (2 : Real) / Real.log X ≤ 12167 / 500000)
    (hdecay : HasPsiLogRpowDecay 1 c α X)
    (henvelope : ∀ x : Real, X ≤ x →
      Real.exp (-c * (Real.log x) ^ α) ≤
        1 / (Real.log x) ^ (4 : ℕ)) :
    HasDusartSymmetricThetaBounds := by
  apply hasDusartSymmetricThetaBounds_of_psiLogFourthError (A := 1)
    hXpos hlogX finite hXcutoff (by norm_num) (by
      convert hA_log using 1 <;> norm_num)
  exact hasPsiLogFourthError_of_logRpowDecay_of_envelope
    hXpos hdecay (by
      intro x hx
      simpa using henvelope x hx)

theorem hasDusartSymmetricThetaBounds_of_psiLogFourthError_sharp
    {A X : Real} (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (finite : HasDusartSymmetricThetaBoundsBelow X)
    (hXcutoff : (4e18 : Real) ≤ X)
    (hA_nonneg : 0 ≤ A)
    (hA_log : (A + 148 / 1000) / Real.log X ≤ 12167 / 500000)
    (psiError : HasPsiLogFourthError A X) :
    HasDusartSymmetricThetaBounds := by
  apply hasDusartSymmetricThetaBounds_of_below_and_logFourth_from
    hXpos hlogX finite (by linarith) hA_log
  exact hasThetaLogFourthError_of_psiLogFourthError_sharp hXcutoff psiError

theorem hasDusartSymmetricThetaBounds_of_psiLogCubedError
    {C X : Real} (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (finite : HasDusartSymmetricThetaBoundsBelow X)
    (hXcutoff : (4e18 : Real) ≤ X)
    (hC_log : C + 1 / Real.log X ≤ 12167 / 500000)
    (psiError : HasPsiLogCubedError C X) :
    HasDusartSymmetricThetaBounds := by
  apply hasDusartSymmetricThetaBounds_of_below_and_logCubed_from
    hXpos hlogX finite
  intro x hx
  have htheta := hasThetaLogCubedError_of_psiLogCubedError
    hXcutoff (by linarith [hlogX]) psiError
  have hx_pos : 0 < x := by linarith
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hfactor : 0 ≤ x / (Real.log x) ^ 3 := by
    exact div_nonneg hx_pos.le (pow_pos hlogx_pos 3).le
  calc
    |Chebyshev.theta x - x| ≤
        (C + 1 / Real.log X) * x / (Real.log x) ^ 3 := htheta x hx
    _ ≤ (12167 / 500000 : Real) * x / (Real.log x) ^ 3 := by
      calc
        (C + 1 / Real.log X) * x / (Real.log x) ^ 3 =
            (C + 1 / Real.log X) * (x / (Real.log x) ^ 3) := by ring
        _ ≤ (12167 / 500000 : Real) * (x / (Real.log x) ^ 3) :=
          mul_le_mul_of_nonneg_right hC_log hfactor
        _ = (12167 / 500000 : Real) * x / (Real.log x) ^ 3 := by ring

theorem dusartPrimeInInterval_of_psiLogCubedError_from
    {C X : Real} (hXpos : 0 < X) (h2X : 2 ≤ X)
    (hlogX : (10 : Real) < Real.log X)
    (hXcutoff : (4e18 : Real) ≤ X)
    (hC_log : C + 1 / Real.log X ≤ 12167 / 500000)
    (psiError : HasPsiLogCubedError C X) :
    ∀ x : Real, X ≤ x →
      ∃ q : Nat, q.Prime ∧ x < q ∧
        (q : Real) ≤ x * (1 + 1 / (Real.log x) ^ 3) := by
  have thetaError : HasThetaLogCubedError
      (12167 / 500000 : Real) X := by
    intro x hx
    have htheta := hasThetaLogCubedError_of_psiLogCubedError
      hXcutoff (by linarith [hlogX]) psiError
    have hx_pos : 0 < x := by linarith
    have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hfactor : 0 ≤ x / (Real.log x) ^ 3 := by
      exact div_nonneg hx_pos.le (pow_pos hlogx_pos 3).le
    calc
      |Chebyshev.theta x - x| ≤
          (C + 1 / Real.log X) * x / (Real.log x) ^ 3 := htheta x hx
      _ ≤ (12167 / 500000 : Real) * x / (Real.log x) ^ 3 := by
        calc
          (C + 1 / Real.log X) * x / (Real.log x) ^ 3 =
              (C + 1 / Real.log X) * (x / (Real.log x) ^ 3) := by ring
          _ ≤ (12167 / 500000 : Real) * (x / (Real.log x) ^ 3) :=
            mul_le_mul_of_nonneg_right hC_log hfactor
          _ = (12167 / 500000 : Real) * x / (Real.log x) ^ 3 := by ring
  exact dusartPrimeInInterval_of_thetaLogCubedError_from
    hXpos h2X hlogX thetaError

theorem dusartPrimeInInterval_of_psiLogFourthError_sharp
    {A X : Real} (hXpos : 0 < X) (h2X : 2 ≤ X)
    (hlogX : (10 : Real) < Real.log X)
    (hXcutoff : (4e18 : Real) ≤ X)
    (hA_nonneg : 0 ≤ A)
    (hA_log : (A + 148 / 1000) / Real.log X ≤ 12167 / 500000)
    (psiError : HasPsiLogFourthError A X) :
    ∀ x : Real, X ≤ x →
      ∃ q : Nat, q.Prime ∧ x < q ∧
        (q : Real) ≤ x * (1 + 1 / (Real.log x) ^ 3) := by
  have thetaError : HasThetaLogCubedError
      (12167 / 500000 : Real) X := by
    have htheta := hasThetaLogCubedError_of_psiLogFourthError_sharp
      hXcutoff hA_nonneg psiError
    intro x hx
    have hx_pos : 0 < x := by linarith
    have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hfactor : 0 ≤ x / (Real.log x) ^ 3 := by
      exact div_nonneg hx_pos.le (pow_pos hlogx_pos 3).le
    calc
      |Chebyshev.theta x - x| ≤
          ((A + 148 / 1000) / Real.log X) * x /
            (Real.log x) ^ 3 := htheta x hx
      _ ≤ (12167 / 500000 : Real) * x / (Real.log x) ^ 3 := by
        calc
          ((A + 148 / 1000) / Real.log X) * x /
              (Real.log x) ^ 3 =
              ((A + 148 / 1000) / Real.log X) *
                (x / (Real.log x) ^ 3) := by ring
          _ ≤ (12167 / 500000 : Real) *
                (x / (Real.log x) ^ 3) :=
            mul_le_mul_of_nonneg_right hA_log hfactor
          _ = (12167 / 500000 : Real) * x /
                (Real.log x) ^ 3 := by ring
  exact dusartPrimeInInterval_of_thetaLogCubedError_from
    hXpos h2X hlogX thetaError

/-! The unbounded part of Dusart's theta estimate is a theorem, not an
assumption: once the explicit logarithm-cubed error estimate is proved, the
two published theta inequalities follow by elementary real arithmetic. -/
theorem dusartThetaBounds_of_logCubedError_tail_from
    {X : Real} (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (thetaError : HasThetaLogCubedError
      (12167 / 500000 : Real) X) :
    ∀ x : Real, X ≤ x →
      x * (1 - (12323 / 10000 : Real) / Real.log x) <
        Chebyshev.theta x ∧
      Chebyshev.theta x < x * (1 + 1 / 36260) := by
  intro x hx
  have hx_pos : 0 < x := by linarith
  have hlog := lt_of_lt_of_le hlogX (Real.log_le_log hXpos hx)
  have hlog_pos : 0 < Real.log x := by linarith
  have htail := thetaError x hx
  have hlog_sq : (100 : Real) < (Real.log x) ^ 2 := by
    nlinarith [mul_self_lt_mul_self (by norm_num : (0 : Real) ≤ 10) hlog]
  have hlog_cube : (1000 : Real) < (Real.log x) ^ 3 := by
    have hmul := mul_lt_mul_of_pos_right hlog_sq hlog_pos
    nlinarith
  have hupper :
      (12167 / 500000 : Real) * x / (Real.log x) ^ 3 < x / 36260 := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hlower :
      (12167 / 500000 : Real) * x / (Real.log x) ^ 3 <
        (12323 / 10000 : Real) * x / Real.log x := by
    rw [div_lt_div_iff₀ (by positivity) hlog_pos]
    have hcoef : (12167 / 500000 : Real) <
        (12323 / 10000 : Real) * (Real.log x) ^ 2 := by
      nlinarith
    have hpos : 0 < x * Real.log x := mul_pos hx_pos hlog_pos
    calc
      (12167 / 500000 : Real) * x * Real.log x =
          (12167 / 500000 : Real) * (x * Real.log x) := by ring
      _ < ((12323 / 10000 : Real) * (Real.log x) ^ 2) *
          (x * Real.log x) := mul_lt_mul_of_pos_right hcoef hpos
      _ = (12323 / 10000 : Real) * x * (Real.log x) ^ 3 := by ring
  constructor
  · have habs := neg_abs_le (Chebyshev.theta x - x)
    have hlow := htail.trans_lt hlower
    have htarget :
        x * (1 - (12323 / 10000 : Real) / Real.log x) =
      x - (12323 / 10000 : Real) * x / Real.log x := by
      field_simp [hlog_pos.ne']
    rw [htarget]
    linarith
  · have habs := le_abs_self (Chebyshev.theta x - x)
    have hupp := htail.trans_lt hupper
    linarith

theorem dusartThetaBounds_of_logCubedError_tail
    (thetaError : HasThetaLogCubedError
      (12167 / 500000 : Real) (4e18 : Real)) :
    ∀ x : Real, (4e18 : Real) ≤ x →
      x * (1 - (12323 / 10000 : Real) / Real.log x) <
        Chebyshev.theta x ∧
      Chebyshev.theta x < x * (1 + 1 / 36260) :=
  dusartThetaBounds_of_logCubedError_tail_from
    (by norm_num) (log_large_x_gt_ten le_rfl) thetaError

theorem dusartThetaBounds_of_relativePsiError_tail_from
    {ε : Real → Real} {c X : Real}
    (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (hε : HasPsiRelativeError ε)
    (hroot : ∀ y : Real, 0 ≤ y → Chebyshev.psi y ≤ c * y)
    (hc : 0 ≤ c)
    (upperMargin : ∀ x : Real, X ≤ x →
      (1 + ε (Real.log X)) * x < x * (1 + 1 / 36260))
    (lowerMargin : ∀ x : Real, X ≤ x →
      x * (1 - (12323 / 10000 : Real) / Real.log x) <
        (1 - ε (Real.log X) - c *
          (Real.exp (-Real.log X / 2) +
            Real.exp (-2 * Real.log X / 3) +
            Real.exp (-4 * Real.log X / 5))) * x) :
    ∀ x : Real, X ≤ x →
      x * (1 - (12323 / 10000 : Real) / Real.log x) <
        Chebyshev.theta x ∧
      Chebyshev.theta x < x * (1 + 1 / 36260) := by
  intro x hx
  have hlogX_nonneg : 0 ≤ Real.log X := by linarith [hlogX]
  have hExp : Real.exp (Real.log X) ≤ x := by
    rw [Real.exp_log hXpos]
    exact hx
  have hbounds := theta_bounds_of_psi_relative_error
    hε hlogX_nonneg hExp hroot hc
  constructor
  · exact (lowerMargin x hx).trans_le hbounds.1
  · exact hbounds.2.trans_lt (upperMargin x hx)

/-! Direct provider boundary for a decaying relative ψ estimate.  The margins
  are pointwise in `x`, so an eventual explicit BKLNW/Dusart estimate can be
  inserted without losing its logarithmic decay at a fixed cutoff. -/
theorem hasDusartThetaBounds_of_relativePsiError_at_log
    {ε : Real → Real} {c : Real}
    (hε : HasPsiRelativeError ε)
    (hroot : ∀ y : Real, 0 ≤ y → Chebyshev.psi y ≤ c * y)
    (hc : 0 ≤ c)
    (upperMargin : ∀ x : Real, 2 ≤ x →
      (1 + ε (Real.log x)) * x < x * (1 + 1 / 36260))
    (lowerMargin : ∀ x : Real, 2 < x →
      x * (1 - (12323 / 10000 : Real) / Real.log x) <
        (1 - ε (Real.log x) - c *
          (Real.exp (-Real.log x / 2) +
            Real.exp (-2 * Real.log x / 3) +
            Real.exp (-4 * Real.log x / 5))) * x) :
    HasDusartThetaBounds := by
  constructor
  · intro x hx
    by_cases hsmall : x < 2
    · rw [Chebyshev.theta_eq_zero_of_lt_two hsmall]
      have : 0 < x * (1 + 1 / 36260) := by positivity
      exact this
    · have hx2 : 2 ≤ x := le_of_not_gt hsmall
      have hlogx_nonneg : 0 ≤ Real.log x :=
        (Real.log_pos (by linarith)).le
      have hpsi := hε (Real.log x) hlogx_nonneg x
        (le_of_eq (Real.exp_log (by linarith)))
      exact (theta_upper_of_psi_relative_error hpsi).trans_lt
        (upperMargin x hx2)
  · intro x hx
    exact (lowerMargin x hx).trans_le
      (theta_lower_of_psi_relative_error_at_log hε hroot hc (by linarith))

/-! The root estimate needed by the preceding provider is elementary and does
not belong in the sharp Dusart input.  Exposing this specialization keeps the
provider boundary faithful to the actual analytic obligation: a relative
error estimate for `psi`, together with the two numerical margin checks. -/
theorem hasDusartThetaBounds_of_relativePsiError_at_log_elementary
    {ε : Real → Real}
    (hε : HasPsiRelativeError ε)
    (upperMargin : ∀ x : Real, 2 ≤ x →
      (1 + ε (Real.log x)) * x < x * (1 + 1 / 36260))
    (lowerMargin : ∀ x : Real, 2 < x →
      x * (1 - (12323 / 10000 : Real) / Real.log x) <
        (1 - ε (Real.log x) - (Real.log 4 + 4) *
          (Real.exp (-Real.log x / 2) +
            Real.exp (-2 * Real.log x / 3) +
            Real.exp (-4 * Real.log x / 5))) * x) :
    HasDusartThetaBounds := by
  exact hasDusartThetaBounds_of_relativePsiError_at_log hε
    psi_root_bound_elementary
    (by positivity) upperMargin lowerMargin

theorem hasDusartThetaBounds_of_symmetric
    (bounds : HasDusartSymmetricThetaBounds) :
    HasDusartThetaBounds := by
  constructor
  · intro x hx
    have h := bounds.1 x hx
    nlinarith
  · intro x hx
    have log_pos : 0 < Real.log x :=
      Real.log_pos (by linarith)
    have h := bounds.2 x hx
    rw [abs_lt] at h
    have hleft := h.1
    ring_nf at hleft ⊢
    linarith

theorem hasDusartThetaBounds_of_below_and_above
    {X : Real}
    (finite : HasDusartSymmetricThetaBoundsBelow X)
    (tail : HasDusartSymmetricThetaBoundsAbove X) :
    HasDusartThetaBounds :=
  hasDusartThetaBounds_of_symmetric
    (hasDusartSymmetricThetaBounds_of_below_and_above finite tail)

theorem hasDusartThetaBounds_of_finite_and_logCubed_from
    {X : Real} (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (finite : HasDusartSymmetricThetaBoundsBelow X)
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) X) :
    HasDusartThetaBounds :=
  hasDusartThetaBounds_of_symmetric
    (hasDusartSymmetricThetaBounds_of_below_and_logCubed_from
      hXpos hlogX finite thetaError)

theorem hasDusartThetaBounds_of_finite_and_logFourth_from
    {A X : Real} (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (finite : HasDusartSymmetricThetaBoundsBelow X)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthError A X) :
    HasDusartThetaBounds :=
  hasDusartThetaBounds_of_symmetric
    (hasDusartSymmetricThetaBounds_of_below_and_logFourth_from
      hXpos hlogX finite hA_nonneg hA thetaError)

theorem log_primorial_lt_of_dusart
    (bounds : HasDusartThetaBounds) (q : Nat) (q_pos : 0 < q) :
    Real.log (primorial q) <
      (q : Real) * (1 + 1 / 36260) := by
  rw [log_primorial_eq_theta]
  exact bounds.1 q (by exact_mod_cast q_pos)

theorem dusart_lower_lt_log_primorial
    (bounds : HasDusartThetaBounds) (q : Nat) (q_gt_two : 2 < q) :
    (q : Real) * (1 - (12323 / 10000 : Real) / Real.log q) <
      Real.log (primorial q) := by
  rw [log_primorial_eq_theta]
  exact bounds.2 q (by exact_mod_cast q_gt_two)

theorem log_eight_mul_primorial_lt_of_dusart
    (bounds : HasDusartThetaBounds) (q : Nat) (q_pos : 0 < q) :
    Real.log (8 * primorial q) <
      Real.log 8 + (q : Real) * (1 + 1 / 36260) := by
  calc
    Real.log (8 * primorial q) =
        Real.log 8 + Real.log (primorial q) :=
      log_mul_primorial 8 q (by omega)
    _ < Real.log 8 + (q : Real) * (1 + 1 / 36260) :=
      add_lt_add_right (log_primorial_lt_of_dusart bounds q q_pos) _

end

end PrimeFactorUnimodality
