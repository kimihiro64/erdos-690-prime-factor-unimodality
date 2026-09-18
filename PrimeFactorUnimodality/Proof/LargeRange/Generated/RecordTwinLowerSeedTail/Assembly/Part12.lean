import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Assembly.Part11
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part441
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part442
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part443
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part444
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part445
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part446
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part447
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part448
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part449
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part450
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part451
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part452
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part453
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part454
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part455
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part456
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part457
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part458
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part459
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part460
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part461
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part462
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part463

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-lower-seed.json` (semantic SHA-256 `3ce105dad06099400dfd2e30c65d47c6e02828915452a8459553c3bb0eb78b73`, excluding elapsed time). Semantic tail assembly group 12. -/

namespace PrimeFactorUnimodality

theorem recordLowerSeedTailGroup12_semantic :
    recordLowerSeedTailChunk463State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix463 := by
  have h441 : recordLowerSeedTailChunk441State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix441 := by
    have prior : recordLowerSeedTailChunk441Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix440 := by
      simpa only [
        recordLowerSeedTailChunk441Before,
        recordLowerSeedTailChunk440State] using recordLowerSeedTailGroup11_semantic
    simpa only [recordLowerSeedTailPrefix441] using
      recordLowerSeedTailChunk441Step.certifies prior
  have h442 : recordLowerSeedTailChunk442State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix442 := by
    have prior : recordLowerSeedTailChunk442Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix441 := by
      simpa only [
        recordLowerSeedTailChunk442Before,
        recordLowerSeedTailChunk441State] using h441
    simpa only [recordLowerSeedTailPrefix442] using
      recordLowerSeedTailChunk442Step.certifies prior
  have h443 : recordLowerSeedTailChunk443State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix443 := by
    have prior : recordLowerSeedTailChunk443Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix442 := by
      simpa only [
        recordLowerSeedTailChunk443Before,
        recordLowerSeedTailChunk442State] using h442
    simpa only [recordLowerSeedTailPrefix443] using
      recordLowerSeedTailChunk443Step.certifies prior
  have h444 : recordLowerSeedTailChunk444State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix444 := by
    have prior : recordLowerSeedTailChunk444Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix443 := by
      simpa only [
        recordLowerSeedTailChunk444Before,
        recordLowerSeedTailChunk443State] using h443
    simpa only [recordLowerSeedTailPrefix444] using
      recordLowerSeedTailChunk444Step.certifies prior
  have h445 : recordLowerSeedTailChunk445State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix445 := by
    have prior : recordLowerSeedTailChunk445Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix444 := by
      simpa only [
        recordLowerSeedTailChunk445Before,
        recordLowerSeedTailChunk444State] using h444
    simpa only [recordLowerSeedTailPrefix445] using
      recordLowerSeedTailChunk445Step.certifies prior
  have h446 : recordLowerSeedTailChunk446State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix446 := by
    have prior : recordLowerSeedTailChunk446Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix445 := by
      simpa only [
        recordLowerSeedTailChunk446Before,
        recordLowerSeedTailChunk445State] using h445
    simpa only [recordLowerSeedTailPrefix446] using
      recordLowerSeedTailChunk446Step.certifies prior
  have h447 : recordLowerSeedTailChunk447State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix447 := by
    have prior : recordLowerSeedTailChunk447Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix446 := by
      simpa only [
        recordLowerSeedTailChunk447Before,
        recordLowerSeedTailChunk446State] using h446
    simpa only [recordLowerSeedTailPrefix447] using
      recordLowerSeedTailChunk447Step.certifies prior
  have h448 : recordLowerSeedTailChunk448State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix448 := by
    have prior : recordLowerSeedTailChunk448Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix447 := by
      simpa only [
        recordLowerSeedTailChunk448Before,
        recordLowerSeedTailChunk447State] using h447
    simpa only [recordLowerSeedTailPrefix448] using
      recordLowerSeedTailChunk448Step.certifies prior
  have h449 : recordLowerSeedTailChunk449State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix449 := by
    have prior : recordLowerSeedTailChunk449Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix448 := by
      simpa only [
        recordLowerSeedTailChunk449Before,
        recordLowerSeedTailChunk448State] using h448
    simpa only [recordLowerSeedTailPrefix449] using
      recordLowerSeedTailChunk449Step.certifies prior
  have h450 : recordLowerSeedTailChunk450State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix450 := by
    have prior : recordLowerSeedTailChunk450Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix449 := by
      simpa only [
        recordLowerSeedTailChunk450Before,
        recordLowerSeedTailChunk449State] using h449
    simpa only [recordLowerSeedTailPrefix450] using
      recordLowerSeedTailChunk450Step.certifies prior
  have h451 : recordLowerSeedTailChunk451State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix451 := by
    have prior : recordLowerSeedTailChunk451Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix450 := by
      simpa only [
        recordLowerSeedTailChunk451Before,
        recordLowerSeedTailChunk450State] using h450
    simpa only [recordLowerSeedTailPrefix451] using
      recordLowerSeedTailChunk451Step.certifies prior
  have h452 : recordLowerSeedTailChunk452State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix452 := by
    have prior : recordLowerSeedTailChunk452Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix451 := by
      simpa only [
        recordLowerSeedTailChunk452Before,
        recordLowerSeedTailChunk451State] using h451
    simpa only [recordLowerSeedTailPrefix452] using
      recordLowerSeedTailChunk452Step.certifies prior
  have h453 : recordLowerSeedTailChunk453State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix453 := by
    have prior : recordLowerSeedTailChunk453Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix452 := by
      simpa only [
        recordLowerSeedTailChunk453Before,
        recordLowerSeedTailChunk452State] using h452
    simpa only [recordLowerSeedTailPrefix453] using
      recordLowerSeedTailChunk453Step.certifies prior
  have h454 : recordLowerSeedTailChunk454State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix454 := by
    have prior : recordLowerSeedTailChunk454Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix453 := by
      simpa only [
        recordLowerSeedTailChunk454Before,
        recordLowerSeedTailChunk453State] using h453
    simpa only [recordLowerSeedTailPrefix454] using
      recordLowerSeedTailChunk454Step.certifies prior
  have h455 : recordLowerSeedTailChunk455State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix455 := by
    have prior : recordLowerSeedTailChunk455Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix454 := by
      simpa only [
        recordLowerSeedTailChunk455Before,
        recordLowerSeedTailChunk454State] using h454
    simpa only [recordLowerSeedTailPrefix455] using
      recordLowerSeedTailChunk455Step.certifies prior
  have h456 : recordLowerSeedTailChunk456State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix456 := by
    have prior : recordLowerSeedTailChunk456Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix455 := by
      simpa only [
        recordLowerSeedTailChunk456Before,
        recordLowerSeedTailChunk455State] using h455
    simpa only [recordLowerSeedTailPrefix456] using
      recordLowerSeedTailChunk456Step.certifies prior
  have h457 : recordLowerSeedTailChunk457State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix457 := by
    have prior : recordLowerSeedTailChunk457Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix456 := by
      simpa only [
        recordLowerSeedTailChunk457Before,
        recordLowerSeedTailChunk456State] using h456
    simpa only [recordLowerSeedTailPrefix457] using
      recordLowerSeedTailChunk457Step.certifies prior
  have h458 : recordLowerSeedTailChunk458State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix458 := by
    have prior : recordLowerSeedTailChunk458Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix457 := by
      simpa only [
        recordLowerSeedTailChunk458Before,
        recordLowerSeedTailChunk457State] using h457
    simpa only [recordLowerSeedTailPrefix458] using
      recordLowerSeedTailChunk458Step.certifies prior
  have h459 : recordLowerSeedTailChunk459State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix459 := by
    have prior : recordLowerSeedTailChunk459Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix458 := by
      simpa only [
        recordLowerSeedTailChunk459Before,
        recordLowerSeedTailChunk458State] using h458
    simpa only [recordLowerSeedTailPrefix459] using
      recordLowerSeedTailChunk459Step.certifies prior
  have h460 : recordLowerSeedTailChunk460State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix460 := by
    have prior : recordLowerSeedTailChunk460Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix459 := by
      simpa only [
        recordLowerSeedTailChunk460Before,
        recordLowerSeedTailChunk459State] using h459
    simpa only [recordLowerSeedTailPrefix460] using
      recordLowerSeedTailChunk460Step.certifies prior
  have h461 : recordLowerSeedTailChunk461State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix461 := by
    have prior : recordLowerSeedTailChunk461Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix460 := by
      simpa only [
        recordLowerSeedTailChunk461Before,
        recordLowerSeedTailChunk460State] using h460
    simpa only [recordLowerSeedTailPrefix461] using
      recordLowerSeedTailChunk461Step.certifies prior
  have h462 : recordLowerSeedTailChunk462State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix462 := by
    have prior : recordLowerSeedTailChunk462Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix461 := by
      simpa only [
        recordLowerSeedTailChunk462Before,
        recordLowerSeedTailChunk461State] using h461
    simpa only [recordLowerSeedTailPrefix462] using
      recordLowerSeedTailChunk462Step.certifies prior
  have h463 : recordLowerSeedTailChunk463State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix463 := by
    have prior : recordLowerSeedTailChunk463Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix462 := by
      simpa only [
        recordLowerSeedTailChunk463Before,
        recordLowerSeedTailChunk462State] using h462
    simpa only [recordLowerSeedTailPrefix463] using
      recordLowerSeedTailChunk463Step.certifies prior
  exact h463

end PrimeFactorUnimodality
