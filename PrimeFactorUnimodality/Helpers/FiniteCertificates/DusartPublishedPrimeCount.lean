import PrimeFactorUnimodality.Helpers.Arithmetic.SievePrimeCounting

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Exact prime count at the published log-square cutoff

One packed wheel sieve certifies the count used by both Abel anchors. The
kernel evaluates the sieve and packed count directly, so no list of primes
or externally computed bitmap needs to be stored in the source tree.
-/

namespace PrimeFactorUnimodality

private noncomputable def publishedSieve : Nat := PrimeCert.Sieve.sieveK 3594641 1896

private theorem publishedSieve_valid : PrimeCert.Sieve.IsSieve 3594641 publishedSieve :=
  PrimeCert.Sieve.isSieve_of_sieveK_eq
    (show PrimeCert.Sieve.sieveK 3594641 1896 = publishedSieve from rfl)
    (by decide) (by decide)

set_option maxHeartbeats 0 in
-- The fixed sieve and packed count are replayed entirely by the kernel.
/-- The closed, inclusive prime count needed at Dusart's log-square cutoff. -/
theorem dusart_published_prime_count : Nat.primeCounting 3594641 = 256357 :=
  primeCounting_eq_of_sieve_check publishedSieve_valid
    (k := 21) (by decide +kernel)

end PrimeFactorUnimodality
