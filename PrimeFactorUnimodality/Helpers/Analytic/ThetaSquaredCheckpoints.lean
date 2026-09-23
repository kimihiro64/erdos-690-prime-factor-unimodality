import Mathlib.NumberTheory.Chebyshev

/-! # Rational checkpoint margins for a log-square theta bound

Each endpoint stores its theta and logarithm enclosures once. A pair of
endpoints has a rational margin test. Monotonicity of theta and the logarithm
then proves the required inequality throughout the entire real interval,
including both endpoints. There is no enumeration of its interior integers.
-/

set_option autoImplicit false

namespace PrimeFactorUnimodality

/-- Shared endpoint data; actual enclosures are checked separately from rational margins. -/
structure ThetaSquaredCheckpoint where
  point : ℕ
  lower : ℚ
  upper : ℚ
  logUpper : ℚ

namespace ThetaSquaredCheckpoint

/-- Analytic meaning of one reusable endpoint enclosure. -/
def Valid (p : ThetaSquaredCheckpoint) : Prop :=
  2 ≤ p.point ∧ 0 < p.logUpper ∧ (p.lower : ℝ) ≤ Chebyshev.theta p.point ∧
    Chebyshev.theta p.point ≤ p.upper ∧ Real.log p.point ≤ p.logUpper

/-- A purely rational test sufficient for every real point between two checkpoints. -/
def Step (c : ℚ) (p q : ThetaSquaredCheckpoint) : Prop :=
  p.point ≤ q.point ∧
    q.upper - (p.point : ℚ) ≤ c * p.point / q.logUpper ^ 2 ∧
    (q.point : ℚ) - p.lower ≤ c * p.point / q.logUpper ^ 2

/-- The margin predicate is decidable without evaluating a real logarithm or theta sum. -/
instance (c : ℚ) (p q : ThetaSquaredCheckpoint) : Decidable (Step c p q) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Rational pair margins imply the exact log-square error at every intervening real value. -/
theorem Step.bound {c : ℚ} (hc : 0 ≤ c) {p q : ThetaSquaredCheckpoint}
    (hp : p.Valid) (hq : q.Valid) (hstep : Step c p q) {x : ℝ}
    (hpx : (p.point : ℝ) ≤ x) (hxq : x ≤ q.point) :
    |Chebyshev.theta x - x| ≤ (c : ℝ) * x / Real.log x ^ 2 := by
  have hp2 : (2 : ℝ) ≤ p.point := by exact_mod_cast hp.1
  have hx1 : 1 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hcx : (0 : ℝ) ≤ c := by exact_mod_cast hc
  have hlog : Real.log x ≤ (q.logUpper : ℝ) :=
    (Real.log_le_log (by linarith) hxq).trans hq.2.2.2.2
  have hpow : Real.log x ^ 2 ≤ (q.logUpper : ℝ) ^ 2 :=
    pow_le_pow_left₀ hlogx.le hlog 2
  have hratio : (c : ℝ) * p.point / (q.logUpper : ℝ) ^ 2 ≤
      (c : ℝ) * x / Real.log x ^ 2 := by
    calc
      _ ≤ (c : ℝ) * x / (q.logUpper : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpx hcx) (sq_nonneg _)
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hcx (by linarith))
        (pow_pos hlogx 2) hpow
  have hlower : (p.lower : ℝ) ≤ Chebyshev.theta x :=
    hp.2.2.1.trans (Chebyshev.theta_mono hpx)
  have hupper : Chebyshev.theta x ≤ (q.upper : ℝ) :=
    (Chebyshev.theta_mono hxq).trans hq.2.2.2.1
  have hupperMargin : (q.upper : ℝ) - p.point ≤
      (c : ℝ) * p.point / (q.logUpper : ℝ) ^ 2 := by
    exact_mod_cast hstep.2.1
  have hlowerMargin : (q.point : ℝ) - p.lower ≤
      (c : ℝ) * p.point / (q.logUpper : ℝ) ^ 2 := by
    exact_mod_cast hstep.2.2
  apply abs_le.mpr
  constructor <;> linarith

end ThetaSquaredCheckpoint

end PrimeFactorUnimodality
