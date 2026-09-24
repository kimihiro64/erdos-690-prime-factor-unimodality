import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.PrimeCountingHalfOpen
import PrimeFactorUnimodality.Helpers.Analytic.TailThetaBounds
import PrimeFactorUnimodality.Helpers.Arithmetic.SievePrimeCountIncrements
import PrimeFactorUnimodality.Mathlib.NumberTheory.Chebyshev.Intervals

set_option autoImplicit false

/-! # Compact theta transport using count increments and smooth logarithms

Exact local prime counts bound the newly added logarithm sum using only the
endpoint logarithms. Checked rational enclosures retain earlier computations;
strict endpoint margins then give the actual theta inequalities on a cell.
-/

namespace PrimeFactorUnimodality

/-- One retained exact count and rational theta enclosure. -/
structure DusartThetaState where
  point : Nat
  count : Nat
  lower : Rat
  upper : Rat
  deriving DecidableEq

def DusartThetaState.Valid (s : DusartThetaState) : Prop :=
  0 < s.point ∧ Nat.primeCounting s.point = s.count ∧
    (s.lower : Real) ≤ Chebyshev.theta s.point ∧ Chebyshev.theta s.point ≤ (s.upper : Real)

/-- The next state and two exact smooth-power logarithm witnesses. -/
structure DusartThetaSieveStep where
  next : DusartThetaState
  lowerPower : DusartSmoothLogPower
  upperPower : DusartSmoothLogPower

def DusartThetaSieveStep.check (row : DusartThetaSieveStep)
    (N k bits : Nat) (s : DusartThetaState) : Bool :=
  decide (s.point ≤ row.next.point ∧
    0 < row.lowerPower.s ∧ 0 < row.upperPower.s ∧
    row.lowerPower.value ≤ s.point ^ row.lowerPower.s ∧
    row.next.point ^ row.upperPower.s ≤ row.upperPower.value ∧
    row.next.lower ≤ s.lower + (row.next.count - s.count : Nat) * row.lowerPower.lower ∧
    s.upper + (row.next.count - s.count : Nat) * row.upperPower.upper ≤ row.next.upper) &&
      checkSieveCountStep N k bits s.point s.count row.next.point row.next.count

theorem DusartThetaSieveStep.provides (row : DusartThetaSieveStep)
    {N k bits : Nat} (sieve : PrimeCert.Sieve.IsSieve N bits)
    {s : DusartThetaState} (state : s.Valid)
    (valid : row.check N k bits s = true) : row.next.Valid := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at valid
  obtain ⟨order, hsl, hsu, hpl, hpu, lower, upper⟩ := valid.1
  have nextCount := primeCounting_eq_of_sieve_step sieve state.2.1 valid.2
  have nextPos := state.1.trans_le order
  have logLower := row.lowerPower.lower_le_log hsl hpl
  have logUpper := row.upperPower.log_le_upper nextPos hsu hpu
  have thetaLower := Chebyshev.primeCounting_sub_mul_log_le_theta_sub state.1 order
  have thetaUpper := Chebyshev.theta_sub_le_primeCounting_sub_mul_log order
  rw [state.2.1, nextCount] at thetaLower thetaUpper
  have deltaPos : (0 : Real) ≤ (row.next.count - s.count : Nat) := Nat.cast_nonneg _
  have lowerProduct := mul_le_mul_of_nonneg_left logLower deltaPos
  have upperProduct := mul_le_mul_of_nonneg_left logUpper deltaPos
  have lowerCast : (row.next.lower : Real) ≤ s.lower +
      (row.next.count - s.count : Nat) * (row.lowerPower.lower : Real) := by
    exact_mod_cast lower
  have upperCast : (s.upper : Real) +
      (row.next.count - s.count : Nat) * (row.upperPower.upper : Real) ≤ row.next.upper := by
    exact_mod_cast upper
  refine ⟨nextPos, nextCount, ?_, ?_⟩
  · linarith only [lowerCast, lowerProduct, thetaLower, state.2.2.1]
  · linarith only [upperCast, upperProduct, thetaUpper, state.2.2.2]

def DusartThetaSieveStep.checkTail (row : DusartThetaSieveStep) (s : DusartThetaState) : Bool :=
  decide ((12323 / 10000 : Rat) ≤ row.upperPower.upper ∧
    row.next.upper < (1001 / 1000 : Rat) * s.point ∧
    (row.next.point : Rat) * (1 - (12323 / 10000 : Rat) / row.upperPower.upper) < s.lower)

theorem DusartThetaSieveStep.provides_tail (row : DusartThetaSieveStep)
    {s : DusartThetaState} (state : s.Valid) (nextState : row.next.Valid)
    (logBound : Real.log row.next.point ≤ (row.upperPower.upper : Real))
    (margins : row.checkTail s = true) {q : Nat} (hq : 3501 ≤ q)
    (left : s.point ≤ q) (right : q ≤ row.next.point) : TailThetaAt q := by
  simp only [checkTail, decide_eq_true_eq] at margins
  have hCoefficient : (12323 / 10000 : Real) ≤ row.upperPower.upper := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using Rat.cast_mono (K := Real) margins.1
  have hLpos : (0 : Real) < row.upperPower.upper := by linarith
  have upper : (row.next.upper : Real) < (1001 / 1000 : Real) * s.point := by
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] using
      Rat.cast_strictMono (K := Real) margins.2.1
  have lower : (row.next.point : Real) *
      (1 - (12323 / 10000 : Real) / row.upperPower.upper) < s.lower := by
    simpa only [Rat.cast_mul, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat,
      Rat.cast_one, Rat.cast_natCast] using Rat.cast_strictMono (K := Real) margins.2.2
  have leftReal : (s.point : Real) ≤ q := by exact_mod_cast left
  have rightReal : (q : Real) ≤ row.next.point := by exact_mod_cast right
  have positive : (0 : Real) < q := by exact_mod_cast (show 0 < q by omega)
  have logPositive : 0 < Real.log (q : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have logUpper := (Real.log_le_log positive rightReal).trans logBound
  have ratio := div_le_div_of_nonneg_left (by norm_num : (0 : Real) ≤ 12323 / 10000)
    logPositive logUpper
  have coefficient : (0 : Real) ≤ 1 - (12323 / 10000 : Real) / row.upperPower.upper := by
    have := (div_le_one hLpos).mpr hCoefficient
    linarith
  constructor
  · exact ((Chebyshev.theta_mono rightReal).trans nextState.2.2.2).trans_lt
      (upper.trans_le (mul_le_mul_of_nonneg_left leftReal (by norm_num)))
  · calc
      (q : Real) * (1 - (12323 / 10000 : Real) / Real.log q) ≤
          (q : Real) * (1 - (12323 / 10000 : Real) / row.upperPower.upper) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_left ratio 1) positive.le
      _ ≤ (row.next.point : Real) *
          (1 - (12323 / 10000 : Real) / row.upperPower.upper) :=
        mul_le_mul_of_nonneg_right rightReal coefficient
      _ < (s.lower : Real) := lower
      _ ≤ Chebyshev.theta s.point := state.2.2.1
      _ ≤ Chebyshev.theta q := Chebyshev.theta_mono leftReal

end PrimeFactorUnimodality
