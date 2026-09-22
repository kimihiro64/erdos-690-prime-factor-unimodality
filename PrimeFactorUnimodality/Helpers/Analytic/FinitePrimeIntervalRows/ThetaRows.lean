import PrimeFactorUnimodality.Helpers.Analytic.ExplicitThetaBounds
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Table66Bounds

set_option autoImplicit false

/-! # Theta-row bounds and their finite-range assemblers

The published constant upper column is at most one. The logarithmic lower
column is used pointwise, without replacing its logarithm by an endpoint.
These proofs have no generated certificate dependencies.
-/

namespace PrimeFactorUnimodality

noncomputable section

structure DusartThetaBoundsRow where
  left : Nat
  right : Nat
  left_large : 2 ≤ left
  left_le_right : left ≤ right
  upper : ∀ x : Real, (left : Real) ≤ x → x ≤ right →
    Chebyshev.theta x - x < x / 36260
  lower : ∀ x : Real, 2 < x → (left : Real) ≤ x → x ≤ right →
    |Chebyshev.theta x - x| < (12323 / 10000 : Real) * x / Real.log x

structure DusartThetaRelativeRow where
  left : Nat
  right : Nat
  left_large : 2 ≤ left
  left_le_right : left ≤ right
  lower_coeff : Real
  upper_coeff : Real
  lower_bound : ∀ x : Real, (left : Real) ≤ x → x ≤ right →
    lower_coeff * x ≤ Chebyshev.theta x
  upper_bound : ∀ x : Real, (left : Real) ≤ x → x ≤ right →
    Chebyshev.theta x ≤ upper_coeff * x
  upper_coeff_le_one : upper_coeff ≤ 1
  lower_error : ∀ x : Real, 2 < x → (left : Real) ≤ x → x ≤ right →
    x - Chebyshev.theta x < (12323 / 10000 : Real) * x / Real.log x

def dusartThetaRelativeRow_provides
    (row : DusartThetaRelativeRow) : DusartThetaBoundsRow where
  left := row.left
  right := row.right
  left_large := row.left_large
  left_le_right := row.left_le_right
  upper := by
    intro x hl hr
    have hleft : (2 : Real) ≤ row.left := by exact_mod_cast row.left_large
    have hx : 0 < x := by linarith
    have hu : Chebyshev.theta x ≤ x := by
      calc
        Chebyshev.theta x ≤ row.upper_coeff * x := row.upper_bound x hl hr
        _ ≤ 1 * x := mul_le_mul_of_nonneg_right row.upper_coeff_le_one hx.le
        _ = x := one_mul x
    have : 0 < x / (36260 : Real) := by positivity
    linarith
  lower := by
    intro x hx hl hr
    have hxpos : 0 < x := by linarith
    have hu : Chebyshev.theta x ≤ x := by
      calc
        Chebyshev.theta x ≤ row.upper_coeff * x := row.upper_bound x hl hr
        _ ≤ 1 * x := mul_le_mul_of_nonneg_right row.upper_coeff_le_one hxpos.le
        _ = x := one_mul x
    rw [abs_of_nonpos (sub_nonpos.mpr hu)]
    linarith [row.lower_error x hx hl hr]

def dusartThetaRelativeRow_to_bounds
    (row : DusartThetaRelativeRow) : DusartThetaBoundsRow :=
  dusartThetaRelativeRow_provides row

/-- Convert already proved constant bounds and their numerical margin. -/
def DusartThetaRelativeRow.of_coefficients
    {left right : Nat} {a b : Real} (hl : 2 ≤ left) (hle : left ≤ right)
    (hb : b ≤ 1)
    (lower : ∀ x : Real, (left : Real) ≤ x → x ≤ right → a * x ≤ Chebyshev.theta x)
    (upper : ∀ x : Real, (left : Real) ≤ x → x ≤ right → Chebyshev.theta x ≤ b * x)
    (margin : ∀ x : Real, 2 < x → (left : Real) ≤ x → x ≤ right →
      (1 - a) * x < (12323 / 10000 : Real) * x / Real.log x) :
    DusartThetaRelativeRow where
  left := left
  right := right
  left_large := hl
  left_le_right := hle
  lower_coeff := a
  upper_coeff := b
  lower_bound := lower
  upper_bound := upper
  upper_coeff_le_one := hb
  lower_error := by
    intro x hx hleft hright
    have hlo := lower x hleft hright
    have hm := margin x hx hleft hright
    nlinarith

/-- The logarithmic lower bound remains pointwise throughout this conversion. -/
def DusartThetaTable66FormulaBounds.toRelativeRow
    {data : DusartThetaTable66CoefficientData}
    (formula : DusartThetaTable66FormulaBounds data)
    (hl : 2 ≤ data.left) (hle : data.left ≤ data.right)
    (hb : data.b0 ≤ 1) (ha : data.a1 < (12323 : Real) / 10000) :
    DusartThetaRelativeRow where
  left := data.left
  right := data.right
  left_large := hl
  left_le_right := hle
  lower_coeff := data.a0
  upper_coeff := data.b0
  lower_bound := formula.lower_zero
  upper_bound := formula.upper_zero
  upper_coeff_le_one := hb
  lower_error := by
    intro x hx hleft hright
    have hxpos : 0 < x := by linarith
    have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
    have hmargin : data.a1 * x / Real.log x <
        (12323 / 10000 : Real) * x / Real.log x :=
      div_lt_div_of_pos_right (mul_lt_mul_of_pos_right ha hxpos) hlogpos
    have hlower := formula.lower_one x hleft hright
    linarith

/-- The whole real interval is proved directly, including the jump at three. -/
theorem dusartThetaBoundsBelow_three :
    HasDusartSymmetricThetaBoundsBelow (3 : Real) := by
  have htheta3 : Chebyshev.theta (3 : Real) < 2 := by
    have hsum := Chebyshev.theta_eq_sum_primesLE_log 3
    have hp : Nat.primesLE 3 = {2, 3} := by decide
    rw [hp] at hsum
    have heq : Chebyshev.theta (3 : Real) = Real.log 2 + Real.log 3 := by
      simpa using hsum
    nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9]
  constructor
  · intro x hx hx3
    by_cases hsmall : x < 2
    · rw [Chebyshev.theta_eq_zero_of_lt_two hsmall]
      have : 0 < x / (36260 : Real) := by positivity
      linarith
    · have hu := (Chebyshev.theta_mono hx3).trans_lt htheta3
      have : 0 < x / (36260 : Real) := by positivity
      linarith
  · intro x hx hx3
    have hxpos : 0 < x := by linarith
    have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
    have hlog : Real.log x < (12323 : Real) / 10000 := by
      have := Real.log_le_log hxpos hx3
      linarith [Real.log_three_lt_d9]
    have hu : Chebyshev.theta x ≤ x := by
      have := (Chebyshev.theta_mono hx3).trans_lt htheta3
      linarith
    have ht : x < (12323 / 10000 : Real) * x / Real.log x := by
      apply (lt_div_iff₀ hlogpos).mpr
      simpa only [mul_comm] using mul_lt_mul_of_pos_left hlog hxpos
    rw [abs_of_nonpos (sub_nonpos.mpr hu)]
    linarith [Chebyshev.theta_nonneg x]

def DusartThetaRelativeRowsCoverUpTo
    (rows : List DusartThetaRelativeRow) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

theorem hasDusartSymmetricThetaBoundsBelow_of_relative_rows
    {X : Real} {rows : List DusartThetaRelativeRow}
    (cover : DusartThetaRelativeRowsCoverUpTo rows X) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_upper_lower
  · intro x hx hX
    by_cases hsmall : x < 2
    · rw [Chebyshev.theta_eq_zero_of_lt_two hsmall]
      have : 0 < x / (36260 : Real) := by positivity
      linarith
    · obtain ⟨row, _, hl, hr⟩ := cover x (le_of_not_gt hsmall) hX
      exact (dusartThetaRelativeRow_provides row).upper x hl hr
  · intro x hx hX
    obtain ⟨row, _, hl, hr⟩ := cover x (by linarith) hX
    exact (dusartThetaRelativeRow_provides row).lower x hx hl hr

def DusartThetaRelativeIndexedCoverUpTo {n : Nat}
    (rows : Fin n → DusartThetaRelativeRow) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ i : Fin n, (rows i).left ≤ x ∧ x ≤ (rows i).right

theorem hasDusartSymmetricThetaBoundsBelow_of_indexed_relative_rows
    {n : Nat} {X : Real} {rows : Fin n → DusartThetaRelativeRow}
    (cover : DusartThetaRelativeIndexedCoverUpTo rows X) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_upper_lower
  · intro x hx hX
    by_cases hsmall : x < 2
    · rw [Chebyshev.theta_eq_zero_of_lt_two hsmall]
      have : 0 < x / (36260 : Real) := by positivity
      linarith
    · obtain ⟨i, hl, hr⟩ := cover x (le_of_not_gt hsmall) hX
      exact (dusartThetaRelativeRow_provides (rows i)).upper x hl hr
  · intro x hx hX
    obtain ⟨i, hl, hr⟩ := cover x (by linarith) hX
    exact (dusartThetaRelativeRow_provides (rows i)).lower x hx hl hr

end

end PrimeFactorUnimodality
