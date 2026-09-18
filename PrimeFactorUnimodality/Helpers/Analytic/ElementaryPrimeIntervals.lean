import PrimeFactorUnimodality.Helpers.Analytic.ElementaryChebyshevConsequences
import PrimeFactorUnimodality.Helpers.PrimeSequence.Consecutive

set_option autoImplicit false

/-!
# An elementary prime in a fixed-ratio interval

The proved Chebyshev bounds force a prime between `n` and `⌊13n/10⌋` once
`n ≥ 250000`.  This is deliberately coarser than the unformalized Dusart
short-interval interface, but it is sufficient for a redesigned uniform tail.
-/

namespace PrimeFactorUnimodality

noncomputable section

theorem exists_prime_of_theta_lt {n m : Nat}
    (hnm : n ≤ m) (hTheta : Chebyshev.theta n < Chebyshev.theta m) :
    ∃ p : Nat, p.Prime ∧ n < p ∧ p ≤ m := by
  by_contra! noPrime
  have primeSets : Nat.primesLE n = Nat.primesLE m := by
    apply Finset.Subset.antisymm (Nat.primesLE_mono hnm)
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    have notAbove : ¬n < p := by
      intro above
      have aboveM := noPrime p hp.2 above
      omega
    exact ⟨not_lt.mp notAbove, hp.2⟩
  rw [Chebyshev.theta_eq_sum_primesLE_log,
    Chebyshev.theta_eq_sum_primesLE_log, primeSets] at hTheta
  exact (lt_irrefl _ hTheta)

theorem exists_prime_between_one_and_thirteenTenths (n : Nat)
    (hn : 250000 ≤ n) :
    ∃ p : Nat, p.Prime ∧ n < p ∧ p ≤ 13 * n / 10 := by
  let m := 13 * n / 10
  have nLeM : n ≤ m := by
    dsimp only [m]
    omega
  have mLarge : 250000 ≤ m := hn.trans nLeM
  have thetaUpper := elementary_theta_upper_from_250000
    (x := (n : Real)) (by exact_mod_cast hn)
  have thetaLower := elementary_theta_lower_from_250000
    (x := (m : Real)) (by exact_mod_cast mLarge)
  have division : 13 * n < 10 * (m + 1) := by
    dsimp only [m]
    omega
  have divisionReal : (13 : Real) * n < 10 * (m + 1) := by
    exact_mod_cast division
  have hnReal : (250000 : Real) ≤ n := by exact_mod_cast hn
  have scale : (111 : Real) / 100 * n < (86 : Real) / 100 * m := by
    nlinarith [hnReal]
  have thetaLt : Chebyshev.theta n < Chebyshev.theta m := by
    exact thetaUpper.trans_lt (scale.trans_le thetaLower)
  exact exists_prime_of_theta_lt nLeM thetaLt

/-- The elementary fixed-ratio interval theorem also supplies a consecutive
prime pair straddling `n`.  The predecessor retains a division-free lower
bound, which is the form needed by the uniform CRT construction. -/
theorem exists_consecutive_primes_near_elementary (n : Nat)
    (hn : 325000 ≤ n) :
    ∃ qPrev q : Nat,
      ConsecutivePrimes qPrev q ∧
      10 * n / 13 < qPrev ∧
      n < q ∧
      q ≤ 13 * n / 10 := by
  let lower := 10 * n / 13
  have lowerLarge : 250000 ≤ lower := by
    dsimp only [lower]
    omega
  obtain ⟨q, qPrime, nLtQ, qUpper⟩ :=
    exists_prime_between_one_and_thirteenTenths n (by omega)
  obtain ⟨s, sPrime, lowerLtS, sUpper⟩ :=
    exists_prime_between_one_and_thirteenTenths lower lowerLarge
  have sLeN : s ≤ n := by
    apply sUpper.trans
    dsimp only [lower]
    omega
  have sLtQ : s < q := sLeN.trans_lt nLtQ
  have qGtTwo : 2 < q := by omega
  let qPrev := primeAt (Nat.primeCounting' q - 1)
  have consecutive : ConsecutivePrimes qPrev q :=
    consecutivePrimes_predecessor qPrime qGtTwo
  have sLePrev : s ≤ qPrev := by
    dsimp only [qPrev]
    exact prime_le_primeAt_primeCounting'_sub_one sPrime sLtQ
  exact ⟨qPrev, q, consecutive, lowerLtS.trans_le sLePrev, nLtQ, qUpper⟩

/-- Above one million, the sharper elementary theta bounds improve the fixed
ratio from `13/10` to `5/4`. -/
theorem exists_prime_between_one_and_fiveFourths (n : Nat)
    (hn : 1000000 ≤ n) :
    ∃ p : Nat, p.Prime ∧ n < p ∧ p ≤ 5 * n / 4 := by
  let m := 5 * n / 4
  have nLeM : n ≤ m := by
    dsimp only [m]
    omega
  have mLarge : 1000000 ≤ m := hn.trans nLeM
  have thetaUpper := elementary_theta_upper
    (x := (n : Real)) (by exact_mod_cast hn)
  have thetaLower := elementary_theta_lower
    (x := (m : Real)) (by exact_mod_cast mLarge)
  have division : 5 * n < 4 * (m + 1) := by
    dsimp only [m]
    omega
  have divisionReal : (5 : Real) * n < 4 * (m + 1) := by
    exact_mod_cast division
  have hnReal : (1000000 : Real) ≤ n := by exact_mod_cast hn
  have scale : (1107 : Real) / 1000 * n < (89 : Real) / 100 * m := by
    nlinarith
  have thetaLt : Chebyshev.theta n < Chebyshev.theta m :=
    thetaUpper.trans_lt (scale.trans_le thetaLower)
  exact exists_prime_of_theta_lt nLeM thetaLt

/-- A consecutive prime pair around `n` with the sharper `5/4` upper ratio
and `4/5` predecessor ratio. -/
theorem exists_consecutive_primes_near_elementary_sharp (n : Nat)
    (hn : 1250000 ≤ n) :
    ∃ qPrev q : Nat,
      ConsecutivePrimes qPrev q ∧
      4 * n / 5 < qPrev ∧
      n < q ∧
      q ≤ 5 * n / 4 := by
  let lower := 4 * n / 5
  have lowerLarge : 1000000 ≤ lower := by
    dsimp only [lower]
    omega
  obtain ⟨q, qPrime, nLtQ, qUpper⟩ :=
    exists_prime_between_one_and_fiveFourths n (by omega)
  obtain ⟨s, sPrime, lowerLtS, sUpper⟩ :=
    exists_prime_between_one_and_fiveFourths lower lowerLarge
  have sLeN : s ≤ n := by
    apply sUpper.trans
    dsimp only [lower]
    omega
  have sLtQ : s < q := sLeN.trans_lt nLtQ
  have qGtTwo : 2 < q := by omega
  let qPrev := primeAt (Nat.primeCounting' q - 1)
  have consecutive : ConsecutivePrimes qPrev q :=
    consecutivePrimes_predecessor qPrime qGtTwo
  have sLePrev : s ≤ qPrev := by
    dsimp only [qPrev]
    exact prime_le_primeAt_primeCounting'_sub_one sPrime sLtQ
  exact ⟨qPrev, q, consecutive, lowerLtS.trans_le sLePrev, nLtQ, qUpper⟩

end

end PrimeFactorUnimodality
