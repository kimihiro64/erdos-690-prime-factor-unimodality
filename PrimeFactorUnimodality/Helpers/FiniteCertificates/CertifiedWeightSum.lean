import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import PrimeFactorUnimodality.Helpers.FiniteCertificates.ComputablePrimePrefix

set_option autoImplicit false

/-! # Fixed-point certificates for finite reciprocal-prime sums

The integer sums in this file are deliberately transparent.  Generated
certificate modules can evaluate them without constructing enormous rational
common denominators.
-/

namespace PrimeFactorUnimodality

/-- Sum of fixed-point lower approximations to reciprocal prime weights. -/
def scaledWeightLower (scale : Nat) (entries : List Nat) : Nat :=
  (entries.map fun p => scale / (p - 1)).sum

/-- Sum of fixed-point upper approximations to reciprocal prime weights. -/
def scaledWeightUpper (scale : Nat) (entries : List Nat) : Nat :=
  (entries.map fun p => scale / (p - 1) + 1).sum

/-- Update both fixed-point accumulators when `n` passes the transparent
primality test. -/
def fixedWeightStep (scale n : Nat) (state : Nat × Nat) : Nat × Nat :=
  if isPrimeTrial n then
    (state.1 + scale / (n - 1), state.2 + (scale / (n - 1) + 1))
  else state

/-- Scan every natural below a cutoff and accumulate certified lower and upper
reciprocal-prime sums. -/
def fixedWeightSums (scale : Nat) : Nat → Nat × Nat
  | 0 => (0, 0)
  | n + 1 => fixedWeightStep scale n (fixedWeightSums scale n)

/-- Evaluate a consecutive block of fixed-weight scan steps from a supplied
accumulator state. -/
def iterateFixedWeightSteps (scale start : Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, state => state
  | count + 1, state =>
      fixedWeightStep scale (start + count)
        (iterateFixedWeightSteps scale start count state)

theorem fixedWeightSums_add (scale start count : Nat) :
    fixedWeightSums scale (start + count) =
      iterateFixedWeightSteps scale start count (fixedWeightSums scale start) := by
  induction count with
  | zero => simp [iterateFixedWeightSteps]
  | succ count ih =>
      rw [Nat.add_succ, fixedWeightSums, iterateFixedWeightSteps, ih]

theorem fixedWeightSums_fst (scale n : Nat) :
    (fixedWeightSums scale n).1 = scaledWeightLower scale (computablePrimesBelow n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [fixedWeightSums, show computablePrimesBelow (n + 1) =
        computablePrimesBelow n ++ [n].filter isPrimeTrial by
          simp [computablePrimesBelow, List.range_succ]]
      by_cases hprime : isPrimeTrial n = true
      · simp [fixedWeightStep, hprime, scaledWeightLower, ih, Nat.add_comm]
      · have hfalse : isPrimeTrial n = false := Bool.eq_false_of_not_eq_true hprime
        simp [fixedWeightStep, hfalse, scaledWeightLower, ih]

theorem fixedWeightSums_snd (scale n : Nat) :
    (fixedWeightSums scale n).2 = scaledWeightUpper scale (computablePrimesBelow n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [fixedWeightSums, show computablePrimesBelow (n + 1) =
        computablePrimesBelow n ++ [n].filter isPrimeTrial by
          simp [computablePrimesBelow, List.range_succ]]
      by_cases hprime : isPrimeTrial n = true
      · simp [fixedWeightStep, hprime, scaledWeightUpper, ih, Nat.add_assoc, Nat.add_comm]
      · have hfalse : isPrimeTrial n = false := Bool.eq_false_of_not_eq_true hprime
        simp [fixedWeightStep, hfalse, scaledWeightUpper, ih]

private theorem scaledWeightLower_term
    (scale p : Nat) (hscale : 0 < scale) (hp : 1 < p) :
    ((scale / (p - 1) : Nat) : Rat) / scale ≤ primeWeight p := by
  have hdNat : 0 < p - 1 := Nat.sub_pos_of_lt hp
  have hscaleRat : (0 : Rat) < scale := by exact_mod_cast hscale
  have hdRat : (0 : Rat) < ((p - 1 : Nat) : Rat) := by exact_mod_cast hdNat
  rw [primeWeight]
  apply (div_le_div_iff₀ hscaleRat hdRat).2
  norm_cast
  simpa [Nat.mul_comm] using Nat.div_mul_le_self scale (p - 1)

private theorem scaledWeightUpper_term
    (scale p : Nat) (hscale : 0 < scale) (hp : 1 < p) :
    primeWeight p ≤ ((scale / (p - 1) + 1 : Nat) : Rat) / scale := by
  have hdNat : 0 < p - 1 := Nat.sub_pos_of_lt hp
  have hscaleRat : (0 : Rat) < scale := by exact_mod_cast hscale
  have hdRat : (0 : Rat) < ((p - 1 : Nat) : Rat) := by exact_mod_cast hdNat
  rw [primeWeight]
  apply (div_le_div_iff₀ hdRat hscaleRat).2
  norm_cast
  simpa [Nat.mul_comm] using (Nat.lt_mul_div_succ scale hdNat).le

theorem scaledWeightLower_le_weightSum
    (scale : Nat) (entries : List Nat) (hscale : 0 < scale)
    (hentries : ∀ p ∈ entries, 1 < p) :
    ((scaledWeightLower scale entries : Nat) : Rat) / scale ≤ weightSum entries := by
  induction entries with
  | nil => simp [scaledWeightLower, weightSum]
  | cons p entries ih =>
      have hp : 1 < p := hentries p (by simp)
      have htail : ∀ q ∈ entries, 1 < q := by
        intro q hq
        exact hentries q (by simp [hq])
      rw [scaledWeightLower, weightSum]
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, add_div]
      exact add_le_add (scaledWeightLower_term scale p hscale hp) (ih htail)

theorem weightSum_le_scaledWeightUpper
    (scale : Nat) (entries : List Nat) (hscale : 0 < scale)
    (hentries : ∀ p ∈ entries, 1 < p) :
    weightSum entries ≤ ((scaledWeightUpper scale entries : Nat) : Rat) / scale := by
  induction entries with
  | nil => simp [scaledWeightUpper, weightSum]
  | cons p entries ih =>
      have hp : 1 < p := hentries p (by simp)
      have htail : ∀ q ∈ entries, 1 < q := by
        intro q hq
        exact hentries q (by simp [hq])
      rw [scaledWeightUpper, weightSum]
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, add_div]
      exact add_le_add (by
        simpa [Nat.cast_add, add_div] using scaledWeightUpper_term scale p hscale hp)
        (ih htail)

/-- A computed first accumulator supplies a rational lower bound for the
canonical reciprocal-prime sum. -/
theorem fixedWeightSums_lower_bound
    (scale p lower upper : Nat) (hscale : 0 < scale)
    (hcertificate : fixedWeightSums scale p = (lower, upper)) :
    ((lower : Nat) : Rat) / scale ≤ weightSum (primesBelow p) := by
  rw [primesBelow_eq_computablePrimesBelow]
  have hbound := scaledWeightLower_le_weightSum scale (computablePrimesBelow p)
    hscale (computablePrimesBelow_gt_one p)
  rw [← fixedWeightSums_fst] at hbound
  rw [hcertificate] at hbound
  exact hbound

/-- A computed second accumulator supplies a rational upper bound for the
canonical reciprocal-prime sum. -/
theorem fixedWeightSums_upper_bound
    (scale p lower upper : Nat) (hscale : 0 < scale)
    (hcertificate : fixedWeightSums scale p = (lower, upper)) :
    weightSum (primesBelow p) ≤ ((upper : Nat) : Rat) / scale := by
  rw [primesBelow_eq_computablePrimesBelow]
  have hbound := weightSum_le_scaledWeightUpper scale (computablePrimesBelow p)
    hscale (computablePrimesBelow_gt_one p)
  rw [← fixedWeightSums_snd] at hbound
  rw [hcertificate] at hbound
  exact hbound

end PrimeFactorUnimodality
