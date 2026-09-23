import PrimeFactorUnimodality.Helpers.Analytic.RadixTwiddleChecks

/-! # Rational checks and exact interface regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset Fourier ZMod

open LeanCert.Core LeanCert.Core.IntervalRat

example : Real.pi ∈ twiddlePi := by
  exact PrimeFactorUnimodality.pi_mem_twiddlePi

example (n k : ℕ) :
    2 * Real.pi * k / (2 ^ n) ∈ twiddleAngle n k := by
  exact PrimeFactorUnimodality.angle_mem_twiddleAngle n k

example {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (q : ℚ) :
    |x - (q : ℝ)| ≤ (intervalPointRadius I q : ℝ) := by
  exact PrimeFactorUnimodality.abs_sub_le_intervalPointRadius hx q

example (n k order : ℕ) (q : RationalPoint) (e : ℚ)
    (h : checkTwiddle n k order q e = true) :
    ‖radixRoot n ^ k - q.toComplex‖ ≤ (e : ℝ) := by
  exact PrimeFactorUnimodality.checkTwiddle_sound n k order q e h

example (p : RationalTwiddles) (depth order : ℕ)
    (h : checkTwiddleTables p depth order = true) : p.Valid depth := by
  exact PrimeFactorUnimodality.checkTwiddleTables_sound p depth order h

def zeroTwiddles : RationalTwiddles :=
  ⟨fun n => Vector.replicate (2 ^ (n + 1)) ⟨0, 0⟩, fun _ => 2⟩

example : checkTwiddle 0 0 0 ⟨1, 0⟩ 0 = true := by decide +kernel
example : checkTwiddle 0 0 0 ⟨0, 0⟩ 0 = false := by decide +kernel
example : checkTwiddleTables zeroTwiddles 1 0 = true := by decide +kernel
example : checkTwiddleTables zeroTwiddles 0 0 = true := by decide +kernel

end

end PrimeFactorUnimodality.Tests
