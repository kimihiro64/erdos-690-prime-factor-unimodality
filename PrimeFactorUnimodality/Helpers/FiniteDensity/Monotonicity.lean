import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import PrimeFactorUnimodality.Helpers.FiniteDensity.Permutation
import PrimeFactorUnimodality.Helpers.PrimeSequence.Basic

set_option autoImplicit false

/-! # Monotonicity infrastructure for the finite density recurrence -/

namespace PrimeFactorUnimodality

noncomputable section

theorem finiteDensity_nonneg (entries : List Nat) (r : Nat) :
    0 ≤ finiteDensity entries r := by
  induction entries generalizing r with
  | nil => cases r <;> simp [finiteDensity]
  | cons p entries ih =>
      cases r with
      | zero =>
          rw [finiteDensity]
          exact mul_nonneg (div_nonneg (by positivity) (by positivity)) (ih 0)
      | succ r =>
          rw [finiteDensity]
          exact add_nonneg
            (mul_nonneg (div_nonneg (by positivity) (by positivity)) (ih (r + 1)))
            (mul_nonneg (div_nonneg (by positivity) (by positivity)) (ih r))

/-- Density of choosing exactly `r` primes strictly before the prime at index
`i`. -/
def prefixDensity (r i : Nat) : Rat :=
  finiteDensity (primesBelow (primeAt i)) r

/-- Probability that an integer is not divisible by the prime at index `i`. -/
def primeRetention (i : Nat) : Rat :=
  ((primeAt i - 1 : Nat) : Rat) / primeAt i

theorem primeRetention_nonneg (i : Nat) : 0 ≤ primeRetention i := by
  unfold primeRetention
  exact div_nonneg (by positivity) (by positivity)

theorem primeRetention_le_one (i : Nat) : primeRetention i ≤ 1 := by
  unfold primeRetention
  have hp : (0 : Rat) < primeAt i := by
    exact_mod_cast (prime_primeAt i).pos
  rw [div_le_iff₀ hp]
  norm_cast
  simpa only [one_mul] using Nat.sub_le (primeAt i) 1

theorem one_sub_primeRetention (i : Nat) :
    1 - primeRetention i = 1 / (primeAt i : Rat) := by
  unfold primeRetention
  have hpNat : primeAt i ≠ 0 := (prime_primeAt i).ne_zero
  have hp : (primeAt i : Rat) ≠ 0 := by exact_mod_cast hpNat
  have hone : 1 ≤ primeAt i := (prime_primeAt i).one_lt.le
  rw [Nat.cast_sub hone]
  field_simp
  ring

theorem prefixDensity_succ (r i : Nat) :
    prefixDensity (r + 1) (i + 1) =
      primeRetention i * prefixDensity (r + 1) i +
        (1 - primeRetention i) * prefixDensity r i := by
  rw [prefixDensity, prefixDensity,
    finiteDensity_perm (primesBelow_primeAt_succ_perm i)]
  rw [finiteDensity, one_sub_primeRetention]
  rfl

theorem prefixDensity_zero_succ (i : Nat) :
    prefixDensity 0 (i + 1) = primeRetention i * prefixDensity 0 i := by
  rw [prefixDensity, prefixDensity,
    finiteDensity_perm (primesBelow_primeAt_succ_perm i)]
  rfl

theorem prefixDensity_zero_antitone :
    ∀ i, prefixDensity 0 (i + 1) ≤ prefixDensity 0 i := by
  intro i
  rw [prefixDensity_zero_succ]
  exact mul_le_of_le_one_left (finiteDensity_nonneg _ _)
    (primeRetention_le_one i)

theorem primeFactorDensity_eq_prefixDensity_div (r i : Nat) :
    primeFactorDensity (r + 1) i = prefixDensity r i / (primeAt i : Rat) := by
  simp [primeFactorDensity, prefixDensity, prescribedFactorDensity]

theorem primeFactorDensity_step_le_of_prefixDensity_step_le
    (r i : Nat) (h : prefixDensity r (i + 1) ≤ prefixDensity r i) :
    primeFactorDensity (r + 1) (i + 1) ≤ primeFactorDensity (r + 1) i := by
  rw [primeFactorDensity_eq_prefixDensity_div,
    primeFactorDensity_eq_prefixDensity_div]
  apply div_le_div₀ (finiteDensity_nonneg _ _) h
  · exact_mod_cast (prime_primeAt i).pos
  · exact_mod_cast (primeAt_strictMono (Nat.lt_succ_self i)).le

end

end PrimeFactorUnimodality
