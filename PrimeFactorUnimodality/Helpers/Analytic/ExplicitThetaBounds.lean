import Mathlib.NumberTheory.Chebyshev
import PrimeFactorUnimodality.Helpers.Analytic.PrimorialLogBounds
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
This interface records exactly the two error scales needed below and the
adapter separates that analytic presentation from the asymmetric inequalities
used by the primorial arguments. -/
def HasDusartSymmetricThetaBounds : Prop :=
  (∀ x : Real, 0 < x →
    |Chebyshev.theta x - x| < x / 36260) ∧
  (∀ x : Real, 2 < x →
    |Chebyshev.theta x - x| <
      (12323 / 10000 : Real) * x / Real.log x)

/-! A finite-range presentation of the same estimates.  This is useful for
the explicit provider because the logarithm-cubed error theorem handles the
unbounded tail, while the remaining interval is a bounded numerical check. -/
def HasDusartSymmetricThetaBoundsBelow (X : Real) : Prop :=
  (∀ x : Real, 0 < x → x ≤ X →
    |Chebyshev.theta x - x| < x / 36260) ∧
  (∀ x : Real, 2 < x → x ≤ X →
    |Chebyshev.theta x - x| <
      (12323 / 10000 : Real) * x / Real.log x)

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
      exact htail.trans_lt hratio

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

theorem hasDusartThetaBounds_of_symmetric
    (bounds : HasDusartSymmetricThetaBounds) :
    HasDusartThetaBounds := by
  constructor
  · intro x hx
    have h := bounds.1 x hx
    rw [abs_lt] at h
    nlinarith
  · intro x hx
    have log_pos : 0 < Real.log x :=
      Real.log_pos (by linarith)
    have h := bounds.2 x hx
    rw [abs_lt] at h
    have hleft := h.1
    ring_nf at hleft ⊢
    linarith

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
