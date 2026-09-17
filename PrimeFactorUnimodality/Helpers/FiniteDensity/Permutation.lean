import Mathlib.Tactic.Ring
import PrimeFactorUnimodality.Definitions.FiniteDensity

set_option autoImplicit false

/-!
# Order invariance of the finite density
-/

namespace PrimeFactorUnimodality

theorem finiteDensity_swap (p q : Nat) (entries : List Nat) (r : Nat) :
    finiteDensity (p :: q :: entries) r = finiteDensity (q :: p :: entries) r := by
  cases r with
  | zero =>
      simp only [finiteDensity]
      ring
  | succ r =>
      cases r <;> simp only [finiteDensity] <;> ring

theorem finiteDensity_perm {entries entries' : List Nat}
    (hperm : entries.Perm entries') (r : Nat) :
    finiteDensity entries r = finiteDensity entries' r := by
  induction hperm generalizing r with
  | nil => rfl
  | cons p hperm ih =>
      cases r with
      | zero => simp only [finiteDensity, ih]
      | succ r => simp only [finiteDensity, ih]
  | swap p q entries => exact finiteDensity_swap q p entries r
  | trans hleft hright ihLeft ihRight =>
      exact (ihLeft r).trans (ihRight r)

theorem prescribedFactorDensity_perm {entries entries' : List Nat}
    (hperm : entries.Perm entries') (k p : Nat) :
    prescribedFactorDensity entries k p = prescribedFactorDensity entries' k p := by
  rw [prescribedFactorDensity, prescribedFactorDensity, finiteDensity_perm hperm]

theorem densityRatio_perm {entries entries' : List Nat}
    (hperm : entries.Perm entries') (r : Nat) :
    densityRatio entries r = densityRatio entries' r := by
  rw [densityRatio, densityRatio, finiteDensity_perm hperm,
    finiteDensity_perm hperm]

end PrimeFactorUnimodality
