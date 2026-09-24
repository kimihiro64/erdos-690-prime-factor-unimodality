import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Assembly.Part12

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-upper-seed-base11.json` (semantic SHA-256 `493791f7b41de1500c4b830f254f9f92fd9c5d50d639b62aa2b46ca48591321f`, excluding elapsed time). Parallel tail-chain facade. -/

namespace PrimeFactorUnimodality

def recordUpperSeed : ZMod recordUpper := recordUpperSeedTailChunk463State

set_option maxHeartbeats 0 in
-- Normalization checks that the complete chunk prefix is the shared exponent.
theorem recordUpper_seedExponent_eq_prefix :
    recordSeedExponent = recordUpperSeedTailPrefix463 := by
  rfl

theorem recordUpper_seed_pow :
    (recordUpperWitnessBase : ZMod recordUpper) ^ recordSeedExponent = recordUpperSeed := by
  rw [recordUpper_seedExponent_eq_prefix, recordUpperSeed]
  exact recordUpperSeedTailGroup12_semantic.symm

end PrimeFactorUnimodality
