import PrimeFactorUnimodality.Helpers.FirstDifference.PrimeSequence
import PrimeFactorUnimodality.Helpers.PrimeSequence.Consecutive
import PrimeFactorUnimodality.Helpers.Unimodality.Obstruction

set_option autoImplicit false

/-!
# Finite certificates for non-unimodality
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- Data sufficient to certify a strict density descent followed by a later
strict ascent at prime indices. -/
structure RatioValleyCertificate (r : Nat) where
  /-- Index of the strict descending step. -/
  descentIndex : Nat
  /-- Index of the later strict ascending step. -/
  ascentIndex : Nat
  ratioDefinedAtDescent : r + 1 ≤ descentIndex
  ratioDefinedAtAscent : r + 1 ≤ ascentIndex
  descentBeforeAscent : descentIndex < ascentIndex
  descentRatio :
    densityRatio (primesBelow (primeAt descentIndex)) (r + 1) <
      (primeGap descentIndex + 1 : Nat)
  ascentRatio :
    densityRatio (primesBelow (primeAt ascentIndex)) (r + 1) >
      (primeGap ascentIndex + 1 : Nat)

/-- A ratio certificate expressed using concrete consecutive primes rather
than their indices. -/
structure ExplicitRatioValleyCertificate (r : Nat) where
  /-- Prime at the strict descending step. -/
  descentPrime : Nat
  /-- Prime immediately following `descentPrime`. -/
  descentNext : Nat
  /-- Prime at the later strict ascending step. -/
  ascentPrime : Nat
  /-- Prime immediately following `ascentPrime`. -/
  ascentNext : Nat
  descentConsecutive : ConsecutivePrimes descentPrime descentNext
  ascentConsecutive : ConsecutivePrimes ascentPrime ascentNext
  descentBeforeAscent : descentPrime < ascentPrime
  ratioDefinedAtDescent : r + 1 ≤ Nat.primeCounting' descentPrime
  ratioDefinedAtAscent : r + 1 ≤ Nat.primeCounting' ascentPrime
  descentRatio :
    densityRatio (primesBelow descentPrime) (r + 1) <
      (descentNext - descentPrime + 1 : Nat)
  ascentRatio :
    densityRatio (primesBelow ascentPrime) (r + 1) >
      (ascentNext - ascentPrime + 1 : Nat)

/-- Convert a certificate at concrete consecutive primes to its indexed-prime
form. -/
def ExplicitRatioValleyCertificate.toRatioValley
    {r : Nat} (certificate : ExplicitRatioValleyCertificate r) :
    RatioValleyCertificate r where
  descentIndex := Nat.primeCounting' certificate.descentPrime
  ascentIndex := Nat.primeCounting' certificate.ascentPrime
  ratioDefinedAtDescent := certificate.ratioDefinedAtDescent
  ratioDefinedAtAscent := certificate.ratioDefinedAtAscent
  descentBeforeAscent := primeCounting'_lt_of_prime_lt
    certificate.descentConsecutive.left_prime
    certificate.ascentConsecutive.left_prime certificate.descentBeforeAscent
  descentRatio := by
    rw [primeAt_primeCounting' _ certificate.descentConsecutive.left_prime,
      certificate.descentConsecutive.primeGap_eq]
    exact certificate.descentRatio
  ascentRatio := by
    rw [primeAt_primeCounting' _ certificate.ascentConsecutive.left_prime,
      certificate.ascentConsecutive.primeGap_eq]
    exact certificate.ascentRatio

theorem RatioValleyCertificate.not_isUnimodal
    {r : Nat} (certificate : RatioValleyCertificate r) :
    ¬ IsUnimodal (primeFactorDensity (r + 2)) := by
  apply not_isUnimodal_of_descent_before_ascent
    (primeFactorDensity (r + 2)) certificate.descentIndex certificate.ascentIndex
    certificate.descentBeforeAscent
  · exact (primeDensityStep_lt_iff_ratio_lt_gap r certificate.descentIndex
      certificate.ratioDefinedAtDescent).2 certificate.descentRatio
  · exact (primeDensityStep_iff_ratio_gap r certificate.ascentIndex
      certificate.ratioDefinedAtAscent).2 certificate.ascentRatio

theorem ExplicitRatioValleyCertificate.not_isUnimodal
    {r : Nat} (certificate : ExplicitRatioValleyCertificate r) :
    ¬ IsUnimodal (primeFactorDensity (r + 2)) :=
  certificate.toRatioValley.not_isUnimodal

end

end PrimeFactorUnimodality
