import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Assembly.Part12

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-lower-seed.json` (semantic SHA-256 `3ce105dad06099400dfd2e30c65d47c6e02828915452a8459553c3bb0eb78b73`, excluding elapsed time). Parallel tail-chain facade. -/

namespace PrimeFactorUnimodality

def recordLowerSeed : BLSPrimality.X7 recordLower := recordLowerSeedTailChunk463State

set_option maxHeartbeats 0 in
-- Normalization checks that the complete chunk prefix is the shared exponent.
theorem recordLower_seedExponent_eq_prefix :
    recordSeedExponent = recordLowerSeedTailPrefix463 := by
  rfl

theorem recordLower_seed_pow :
    (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordSeedExponent = recordLowerSeed := by
  rw [recordLower_seedExponent_eq_prefix, recordLowerSeed]
  exact recordLowerSeedTailGroup12_semantic.symm

end PrimeFactorUnimodality
