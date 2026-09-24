import PrimeFactorUnimodality.Helpers.Analytic.ExplicitThetaBounds
import PrimeFactorUnimodality.Helpers.Analytic.ThetaLogSquaredError

set_option autoImplicit false

/-! # The theta precision actually needed by the uniform tail

The selected prime is at least 3501. On that domain the tail only needs the
upper coefficient `1.001`, together with the existing lower theta estimate.
The log-square error with coefficient `1/5` supplies both inequalities above
3,594,641. Thus the stronger all-real Dusart upper estimate need not be proved
separately to close the classification. The original Dusart interface remains
unchanged and implies this weaker, consumer-specific interface.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- The two pointwise inequalities at a possible selected prime. -/
def TailThetaAt (q : Nat) : Prop :=
  Chebyshev.theta q < (1001 / 1000 : Real) * q ∧
    (q : Real) * (1 - (12323 / 10000 : Real) / Real.log q) < Chebyshev.theta q

/-- No theta estimates below 3501 are used by the uniform tail. -/
def HasTailThetaBounds : Prop := ∀ q : Nat, 3501 ≤ q → TailThetaAt q

/-- The published estimates supply the weaker bounds without extra inputs. -/
theorem hasTailThetaBounds_of_dusart (bounds : HasDusartThetaBounds) :
    HasTailThetaBounds := by
  intro q hq
  have positive : (0 : Real) < q := by exact_mod_cast (show 0 < q by omega)
  constructor
  · have upper := bounds.1 q positive
    nlinarith
  · exact bounds.2 q (by exact_mod_cast (show 2 < q by omega))

theorem tailTheta_log_primorial_upper (bounds : HasTailThetaBounds)
    {q : Nat} (hq : 3501 ≤ q) :
    Real.log (primorial q) < (1001 / 1000 : Real) * q := by
  rw [log_primorial_eq_theta]
  exact (bounds q hq).1

theorem tailTheta_log_primorial_lower (bounds : HasTailThetaBounds)
    {q : Nat} (hq : 3501 ≤ q) :
    (q : Real) * (1 - (12323 / 10000 : Real) / Real.log q) <
      Real.log (primorial q) := by
  rw [log_primorial_eq_theta]
  exact (bounds q hq).2

private theorem log_gt_fifteen_of_theta_endpoint {x : Real} (hx : 3594641 ≤ x) :
    (15 : Real) < Real.log x := by
  have small : (2 : Real) ^ 17 * 3 ^ 3 < x := by norm_num; linarith
  have logged := Real.log_lt_log (by positivity) small
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at logged
  norm_num at logged ⊢
  nlinarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

/-- The squared error supplies both tail inequalities, including the first
endpoint; there is no separate trillion-scale theta upper obligation here. -/
theorem tailThetaAt_of_logSquared
    (error : HasThetaLogSquaredError (1 / 5) 3594641)
    {q : Nat} (hq : 3594641 ≤ q) : TailThetaAt q := by
  have realLower : (3594641 : Real) ≤ q := by exact_mod_cast hq
  have positive : (0 : Real) < q := by linarith
  have logLower := log_gt_fifteen_of_theta_endpoint realLower
  have logPos : (0 : Real) < Real.log q := by linarith
  have squarePos : (0 : Real) < (Real.log q) ^ 2 := by positivity
  have upperCoeff : (1 / 5 : Real) / (Real.log q) ^ 2 < 1 / 1000 := by
    rw [div_lt_iff₀ squarePos]
    nlinarith
  have lowerCoeff : (1 / 5 : Real) / (Real.log q) ^ 2 <
      (12323 / 10000 : Real) / Real.log q := by
    rw [div_lt_div_iff₀ squarePos logPos]
    nlinarith [mul_pos logPos (show (0 : Real) < Real.log q - 15 by linarith)]
  have upperError : (1 / 5 : Real) * q / (Real.log q) ^ 2 <
      (q : Real) / 1000 := by
    calc
      _ = (q : Real) * ((1 / 5 : Real) / (Real.log q) ^ 2) := by ring
      _ < (q : Real) * (1 / 1000) := mul_lt_mul_of_pos_left upperCoeff positive
      _ = _ := by ring
  have lowerError : (1 / 5 : Real) * q / (Real.log q) ^ 2 <
      (q : Real) * ((12323 / 10000 : Real) / Real.log q) := by
    calc
      _ = (q : Real) * ((1 / 5 : Real) / (Real.log q) ^ 2) := by ring
      _ < _ := mul_lt_mul_of_pos_left lowerCoeff positive
  have estimate := abs_le.mp (error q realLower)
  constructor
  · nlinarith [estimate.2]
  · nlinarith [estimate.1]

/-- The only finite theta prefix needed with the squared-error provider ends
at 3,594,641, and starts at the least possible selected prime. -/
theorem hasTailThetaBounds_of_logSquared
    (finite : ∀ q : Nat, 3501 ≤ q → q < 3594641 → TailThetaAt q)
    (error : HasThetaLogSquaredError (1 / 5) 3594641) : HasTailThetaBounds := by
  intro q hq
  by_cases small : q < 3594641
  · exact finite q hq small
  · exact tailThetaAt_of_logSquared error (by omega)

end

end PrimeFactorUnimodality
