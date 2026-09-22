import PrimeFactorUnimodality.Helpers.Analytic.ExplicitPrimeCounting

set_option autoImplicit false

/-! # Rational logarithm enclosures for prime-counting rows

Both comparison functions decrease when their positive logarithm argument
increases. These lemmas leave only rational arithmetic to the row checker.
-/

namespace PrimeFactorUnimodality

theorem dusartPiLower_le_of_log_lower {x L count : Real}
    (hx : 0 ≤ x) (hL : 0 < L) (hlog : L ≤ Real.log x)
    (numeric : x / L * (1 + 1 / L) ≤ count) :
    dusartPiLower x ≤ count := by
  apply le_trans _ numeric
  exact mul_le_mul (div_le_div_of_nonneg_left hx hL hlog)
    (add_le_add le_rfl
      (div_le_div_of_nonneg_left (by norm_num : (0 : Real) ≤ 1) hL hlog))
    (by have := hL.trans_le hlog; positivity)
    (div_nonneg hx hL.le)

theorem le_dusartPiUpper_of_log_upper {x U count : Real}
    (hx : 0 ≤ x) (hlog : 0 < Real.log x) (hU : Real.log x ≤ U)
    (numeric : count ≤ x / U * (1 + (6381 / 5000 : Real) / U)) :
    count ≤ dusartPiUpper x := by
  apply numeric.trans
  exact mul_le_mul (div_le_div_of_nonneg_left hx hlog hU)
    (add_le_add le_rfl
      (div_le_div_of_nonneg_left (by norm_num : (0 : Real) ≤ 6381 / 5000) hlog hU))
    (by have := hlog.trans_le hU; positivity)
    (div_nonneg hx hlog.le)

end PrimeFactorUnimodality
