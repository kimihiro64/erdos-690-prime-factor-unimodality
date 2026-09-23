import PrimeFactorUnimodality.Helpers.Arithmetic.SievePrimeCounting

/-! # Local prime-count increments without replaying prefixes

Consecutive endpoints consume only their intervening sieve bits. The two
exceptional primes have already been counted when the left endpoint is at
least three. Exact addition assembles the new count, independently of the
numerical size of the earlier prefix.
-/

namespace PrimeFactorUnimodality

open Finset PrimeCert.Sieve

/-- Increasing endpoints cannot remove wheel candidates. -/
theorem wheelLength_mono : Monotone wheelLength := by
  intro a b hab
  unfold wheelLength
  split_ifs <;> omega

/-- Every endpoint at least three includes the wheel value one. -/
theorem one_le_wheelLength {a : ℕ} (ha : 3 ≤ a) : 1 ≤ wheelLength a := by
  unfold wheelLength
  split_ifs <;> omega

/-- The exact prefix count uses only two exceptions and the retained wheel-index set. -/
theorem primeCounting_eq_two_add_wheelCard {N a bits : ℕ} (h : IsSieve N bits)
    (ha : 3 ≤ a) (haN : a ≤ N) :
    Nat.primeCounting a = 2 + (wheelPrimeIndices a bits).card := by
  rw [← Nat.primesLE_card_eq_primeCounting, ← sievePrimeSet_eq (isSieve_restrict h haN),
    sievePrimeSet_card]
  simp only [ite_eq_left ha, ite_eq_left (show 2 ≤ a by omega)]

/-- Adjacent wheel-index sets contribute precisely the bits in the intervening block. -/
theorem wheelPrimeIndices_card_add {a b bits : ℕ} (ha : 3 ≤ a) (hab : a ≤ b) :
    (wheelPrimeIndices b bits).card = (wheelPrimeIndices a bits).card +
      ((range (wheelLength b - wheelLength a)).filter
        (fun i => bits.testBit (wheelLength a + i))).card := by
  have hmono := wheelLength_mono hab
  have hpos := one_le_wheelLength ha
  have hwidth : wheelLength b - 1 =
      (wheelLength a - 1) + (wheelLength b - wheelLength a) := by omega
  simp only [wheelPrimeIndices, card_filter]
  rw [hwidth, sum_range_add]
  congr 1
  apply sum_congr rfl
  intro i hi
  have heq : wheelLength a - 1 + i + 1 = wheelLength a + i := by omega
  rw [heq]

/-- A certified sieve supplies an exact local increment, with depth needed only for that block. -/
theorem primeCounting_add_bitCountBlock {N a b bits k : ℕ} (h : IsSieve N bits)
    (ha : 3 ≤ a) (hab : a ≤ b) (hbN : b ≤ N)
    (hk : wheelLength b - wheelLength a ≤ 2 ^ k) :
    Nat.primeCounting a + Nat.bitCountBlock k bits (wheelLength a)
      (wheelLength b - wheelLength a) = Nat.primeCounting b := by
  rw [primeCounting_eq_two_add_wheelCard h ha (hab.trans hbN),
    primeCounting_eq_two_add_wheelCard h (ha.trans hab) hbN,
    wheelPrimeIndices_card_add ha hab, Nat.bitCountBlock_eq_card _ _ _ _ hk]
  omega

/-- The local row checks coverage, sufficient depth and exact addition to the retained old count. -/
def checkSieveCountStep (N k bits a oldCount b newCount : ℕ) : Bool :=
  decide (3 ≤ a ∧ a ≤ b ∧ b ≤ N ∧ wheelLength b - wheelLength a ≤ 2 ^ k ∧
    oldCount + Nat.bitCountBlock k bits (wheelLength a)
      (wheelLength b - wheelLength a) = newCount)

/-- A checked local count row advances the actual prime-counting function. -/
theorem primeCounting_eq_of_sieve_step {N k bits a oldCount b newCount : ℕ}
    (h : IsSieve N bits) (ha : Nat.primeCounting a = oldCount)
    (hc : checkSieveCountStep N k bits a oldCount b newCount = true) :
    Nat.primeCounting b = newCount := by
  simp only [checkSieveCountStep, decide_eq_true_eq] at hc
  rw [← primeCounting_add_bitCountBlock h hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1, ha]
  exact hc.2.2.2.2

end PrimeFactorUnimodality
