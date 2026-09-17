import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimeFactorUnimodality.Definitions.FiniteDensity

set_option autoImplicit false

/-!
# Elementary-symmetric form of the finite density

This module rewrites the finite Bernoulli recursion as an Euler-product
factor times an elementary symmetric sum.  The entries are kept abstract:
primality and ordering are not needed, only that every denominator is larger
than one.
-/

namespace PrimeFactorUnimodality

/-- The reciprocal weight attached to a possible prime divisor `p`. -/
def primeWeight (p : Nat) : Rat := 1 / ((p - 1 : Nat) : Rat)

/-- The product of the complementary divisibility probabilities. -/
def densityBase (entries : List Nat) : Rat :=
  (entries.map fun p => ((p - 1 : Nat) : Rat) / (p : Rat)).prod

/-- The elementary symmetric sum of degree `r` in the reciprocal weights. -/
def weightEsymm (entries : List Nat) (r : Nat) : Rat :=
  ((entries.map primeWeight : List Rat) : Multiset Rat).esymm r

theorem esymm_cons_succ (a : Rat) (s : Multiset Rat) (r : Nat) :
    (a ::ₘ s).esymm (r + 1) = s.esymm (r + 1) + a * s.esymm r := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]

theorem selectionFactor_mul_primeWeight (p : Nat) (hp : 1 < p) :
    (((p - 1 : Nat) : Rat) / (p : Rat)) * primeWeight p = 1 / (p : Rat) := by
  have hpNat : p ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt hp)
  have hpm1Nat : p - 1 ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hp)
  have hp0 : (p : Rat) ≠ 0 := by exact_mod_cast hpNat
  have hpm10 : ((p - 1 : Nat) : Rat) ≠ 0 := by exact_mod_cast hpm1Nat
  change (((p - 1 : Nat) : Rat) / (p : Rat)) *
      (1 / ((p - 1 : Nat) : Rat)) = 1 / (p : Rat)
  field_simp

/-- The recursive density is exactly its Euler-product base multiplied by an
elementary symmetric sum in the weights `1 / (p - 1)`. -/
theorem finiteDensity_eq_densityBase_mul_weightEsymm
    (entries : List Nat) (hentries : ∀ p ∈ entries, 1 < p) (r : Nat) :
    finiteDensity entries r = densityBase entries * weightEsymm entries r := by
  induction entries generalizing r with
  | nil =>
      cases r with
      | zero => simp [finiteDensity, densityBase, weightEsymm]
      | succ r =>
          rw [finiteDensity]
          simp only [densityBase, weightEsymm, List.map_nil, List.prod_nil,
            one_mul]
          have hnil : (↑([] : List Rat) : Multiset Rat) = 0 := rfl
          rw [hnil]
          rw [Multiset.esymm_of_card_lt (by simp)]
  | cons p entries ih =>
      have hp : 1 < p := hentries p (by simp)
      have htail : ∀ q ∈ entries, 1 < q := by
        intro q hq
        exact hentries q (by simp [hq])
      cases r with
      | zero =>
          rw [finiteDensity, ih htail 0]
          simp [densityBase, weightEsymm]
      | succ r =>
          rw [finiteDensity, ih htail (r + 1), ih htail r]
          simp only [densityBase, weightEsymm, List.map_cons, List.prod_cons,
            ]
          have hcons :
              (↑(primeWeight p :: List.map primeWeight entries) : Multiset Rat) =
                primeWeight p ::ₘ (↑(List.map primeWeight entries) : Multiset Rat) := rfl
          rw [hcons]
          rw [esymm_cons_succ]
          rw [← selectionFactor_mul_primeWeight p hp]
          ring

end PrimeFactorUnimodality
