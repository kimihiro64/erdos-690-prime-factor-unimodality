import PrimeFactorUnimodality.Helpers.Analytic.PrimorialLogBounds
import PrimeFactorUnimodality.Proof.LargeRange.ElementaryTailSelection

set_option autoImplicit false

/-!
# Elementary primorial bounds at the tail scale

These statements connect the closed prime selector to the closed Chebyshev
bounds, replacing the theta interface used by the earlier Dusart reduction.
-/

namespace PrimeFactorUnimodality

noncomputable section

theorem elementary_tail_log_primorial_lower
    {r q : Nat} (hr : 8600001 ≤ r)
    (scaleLtQ : elementaryTailScale r < q) :
    (86 : Real) / 100 * q ≤ Real.log (primorial q) := by
  rw [log_primorial_eq_theta]
  apply elementary_theta_lower_from_250000
  have large : 325000 ≤ q :=
    (elementaryTailScale_ge_threeHundredTwentyFiveThousand hr).trans scaleLtQ.le
  have : 250000 ≤ q := by omega
  exact_mod_cast this

theorem elementary_tail_log_primorial_upper
    {r q : Nat} (hr : 8600001 ≤ r)
    (scaleLtQ : elementaryTailScale r < q) :
    Real.log (primorial q) ≤ (111 : Real) / 100 * q := by
  rw [log_primorial_eq_theta]
  apply elementary_theta_upper_from_250000
  have large : 325000 ≤ q :=
    (elementaryTailScale_ge_threeHundredTwentyFiveThousand hr).trans scaleLtQ.le
  have : 250000 ≤ q := by omega
  exact_mod_cast this

theorem elementary_tail_log_primorial_lower_sharp
    {r q : Nat} (hr : 33554432 ≤ r)
    (scaleLtQ : elementaryTailScale r < q) :
    (89 : Real) / 100 * q ≤ Real.log (primorial q) := by
  rw [log_primorial_eq_theta]
  apply elementary_theta_lower
  have large : 1250000 ≤ q :=
    (elementaryTailScale_ge_oneMillionTwoHundredFiftyThousand hr).trans scaleLtQ.le
  have : 1000000 ≤ q := by omega
  exact_mod_cast this

theorem elementary_tail_log_primorial_upper_sharp
    {r q : Nat} (hr : 33554432 ≤ r)
    (scaleLtQ : elementaryTailScale r < q) :
    Real.log (primorial q) ≤ (1107 : Real) / 1000 * q := by
  rw [log_primorial_eq_theta]
  apply elementary_theta_upper
  have large : 1250000 ≤ q :=
    (elementaryTailScale_ge_oneMillionTwoHundredFiftyThousand hr).trans scaleLtQ.le
  have : 1000000 ≤ q := by omega
  exact_mod_cast this

/-- All closed elementary inputs for the coarse post-record prime pair,
packaged in the units used by the remaining tail inequalities. -/
theorem exists_elementary_tail_pair_with_primorial_bounds {r : Nat}
    (hr : 8600001 ≤ r) :
    ∃ qPrev q : Nat,
      ConsecutivePrimes qPrev q ∧
      (69 / 130 : Real) * r / Real.log r - 10 / 13 < qPrev ∧
      elementaryTailScale r < q ∧
      (q : Real) < (546 / 575 : Real) * r / Real.log r ∧
      (86 : Real) / 100 * q ≤ Real.log (primorial q) ∧
      Real.log (primorial q) ≤ (111 : Real) / 100 * q := by
  obtain ⟨qPrev, q, consecutive, prevLower, scaleLtQ, qUpper⟩ :=
    exists_elementary_tail_consecutive_primes_real hr
  exact ⟨qPrev, q, consecutive, prevLower, scaleLtQ, qUpper,
    elementary_tail_log_primorial_lower hr scaleLtQ,
    elementary_tail_log_primorial_upper hr scaleLtQ⟩

/-- The sharper closed elementary package beyond `2^25`. -/
theorem exists_elementary_tail_pair_with_primorial_bounds_sharp {r : Nat}
    (hr : 33554432 ≤ r) :
    ∃ qPrev q : Nat,
      ConsecutivePrimes qPrev q ∧
      (69 / 125 : Real) * r / Real.log r - 4 / 5 < qPrev ∧
      elementaryTailScale r < q ∧
      (q : Real) < (21 / 23 : Real) * r / Real.log r ∧
      (89 : Real) / 100 * q ≤ Real.log (primorial q) ∧
      Real.log (primorial q) ≤ (1107 : Real) / 1000 * q := by
  obtain ⟨qPrev, q, consecutive, prevLower, scaleLtQ, qUpper⟩ :=
    exists_elementary_tail_consecutive_primes_sharp_real hr
  exact ⟨qPrev, q, consecutive, prevLower, scaleLtQ, qUpper,
    elementary_tail_log_primorial_lower_sharp hr scaleLtQ,
    elementary_tail_log_primorial_upper_sharp hr scaleLtQ⟩

end
end PrimeFactorUnimodality
