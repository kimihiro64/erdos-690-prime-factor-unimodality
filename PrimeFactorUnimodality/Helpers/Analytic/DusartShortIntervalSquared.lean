import PrimeFactorUnimodality.Helpers.Analytic.ShortIntervalPrime
import PrimeFactorUnimodality.Helpers.Analytic.ThetaLogSquaredError

/-! # The requested short interval from a log-square theta error

The actual endpoint increment of theta supplies a prime. With theta
coefficient one fifth, the width x/(2 log(x)^2) has a strict positive
margin as soon as log(x)>=2. This proves precisely the requested width;
no log-cubed short-interval theorem is needed for the analytic tail.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- The log-square error at both endpoints forces the required theta increment. -/
theorem dusartPrimeInInterval_of_thetaLogSquared {X x : ℝ}
    (error : HasThetaLogSquaredError (1 / 5) X)
    (hx : X ≤ x) (hx1 : 1 < x) (hlog : 2 ≤ Real.log x) :
    ∃ q : ℕ, q.Prime ∧ x < q ∧
      (q : ℝ) ≤ x * (1 + 1 / (2 * Real.log x ^ 2)) := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx1
  have hlpos : 0 < Real.log x := Real.log_pos hx1
  let h := x / (2 * Real.log x ^ 2)
  have hh : 0 < h := by dsimp [h]; positivity
  have hxy : x ≤ x + h := by linarith
  have hlogmono := Real.log_le_log hxpos hxy
  have hpow := pow_le_pow_left₀ hlpos.le hlogmono 2
  have hthetaX := (abs_le.mp (error x hx)).2
  have hthetaY := (abs_le.mp (error (x + h) (hx.trans hxy))).1
  have herrorY : (1 / 5 : ℝ) * (x + h) / Real.log (x + h) ^ 2 ≤
      (1 / 5 : ℝ) * (x + h) / Real.log x ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (pow_pos hlpos 2) hpow
  have hmargin : (1 / 5 : ℝ) * x / Real.log x ^ 2 +
      (1 / 5 : ℝ) * (x + h) / Real.log x ^ 2 < h := by
    have hsquare : 4 ≤ Real.log x ^ 2 := by nlinarith
    have heq : h - ((1 / 5 : ℝ) * x / Real.log x ^ 2 +
        (1 / 5 : ℝ) * (x + h) / Real.log x ^ 2) =
        x * (Real.log x ^ 2 - 1) / (10 * Real.log x ^ 4) := by
      dsimp [h]
      field_simp
      ring
    apply lt_of_sub_pos
    rw [heq]
    exact div_pos (mul_pos hxpos (by linarith)) (by positivity)
  have hincr : Chebyshev.theta x < Chebyshev.theta (x + h) := by linarith
  obtain ⟨q, hq, hqx, hqxy⟩ := exists_prime_of_theta_increment hxpos.le hh hincr
  refine ⟨q, hq, hqx, hqxy.trans_eq ?_⟩
  dsimp [h]
  ring

/-- A bounded prefix and this weaker theta error give the exact global short-interval provider. -/
theorem hasDusartShortIntervalPrime_of_thetaLogSquared {X : ℝ}
    (hX : 1 < X) (hlogX : 2 ≤ Real.log X)
    (finite : HasDusartShortIntervalPrimeBelow X)
    (error : HasThetaLogSquaredError (1 / 5) X) : HasDusartShortIntervalPrime := by
  intro x hx
  by_cases hprefix : x ≤ X
  · exact finite x hx hprefix
  · have htail : X ≤ x := (lt_of_not_ge hprefix).le
    exact dusartPrimeInInterval_of_thetaLogSquared error htail (hX.trans_le htail)
      (hlogX.trans (Real.log_le_log (by linarith : 0 < X) htail))

end

end PrimeFactorUnimodality
