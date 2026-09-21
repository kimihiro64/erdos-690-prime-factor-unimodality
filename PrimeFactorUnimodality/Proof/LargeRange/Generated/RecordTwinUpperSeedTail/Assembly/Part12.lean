import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Assembly.Part11
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part463

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-upper-seed-base11.json` (semantic SHA-256 `493791f7b41de1500c4b830f254f9f92fd9c5d50d639b62aa2b46ca48591321f`, excluding elapsed time). Semantic tail assembly group 12. -/

namespace PrimeFactorUnimodality

theorem recordUpperSeedTailGroup12_semantic :
    recordUpperSeedTailChunk463State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix463 := by
  have h441 : recordUpperSeedTailChunk441State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix441 := by
    have prior : recordUpperSeedTailChunk441Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix440 := by
      simpa only [
        recordUpperSeedTailChunk441Before,
        recordUpperSeedTailChunk440State] using recordUpperSeedTailGroup11_semantic
    simpa only [recordUpperSeedTailPrefix441] using
      recordUpperSeedTailChunk441Step.certifies prior
  have h442 : recordUpperSeedTailChunk442State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix442 := by
    have prior : recordUpperSeedTailChunk442Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix441 := by
      simpa only [
        recordUpperSeedTailChunk442Before,
        recordUpperSeedTailChunk441State] using h441
    simpa only [recordUpperSeedTailPrefix442] using
      recordUpperSeedTailChunk442Step.certifies prior
  have h443 : recordUpperSeedTailChunk443State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix443 := by
    have prior : recordUpperSeedTailChunk443Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix442 := by
      simpa only [
        recordUpperSeedTailChunk443Before,
        recordUpperSeedTailChunk442State] using h442
    simpa only [recordUpperSeedTailPrefix443] using
      recordUpperSeedTailChunk443Step.certifies prior
  have h444 : recordUpperSeedTailChunk444State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix444 := by
    have prior : recordUpperSeedTailChunk444Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix443 := by
      simpa only [
        recordUpperSeedTailChunk444Before,
        recordUpperSeedTailChunk443State] using h443
    simpa only [recordUpperSeedTailPrefix444] using
      recordUpperSeedTailChunk444Step.certifies prior
  have h445 : recordUpperSeedTailChunk445State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix445 := by
    have prior : recordUpperSeedTailChunk445Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix444 := by
      simpa only [
        recordUpperSeedTailChunk445Before,
        recordUpperSeedTailChunk444State] using h444
    simpa only [recordUpperSeedTailPrefix445] using
      recordUpperSeedTailChunk445Step.certifies prior
  have h446 : recordUpperSeedTailChunk446State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix446 := by
    have prior : recordUpperSeedTailChunk446Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix445 := by
      simpa only [
        recordUpperSeedTailChunk446Before,
        recordUpperSeedTailChunk445State] using h445
    simpa only [recordUpperSeedTailPrefix446] using
      recordUpperSeedTailChunk446Step.certifies prior
  have h447 : recordUpperSeedTailChunk447State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix447 := by
    have prior : recordUpperSeedTailChunk447Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix446 := by
      simpa only [
        recordUpperSeedTailChunk447Before,
        recordUpperSeedTailChunk446State] using h446
    simpa only [recordUpperSeedTailPrefix447] using
      recordUpperSeedTailChunk447Step.certifies prior
  have h448 : recordUpperSeedTailChunk448State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix448 := by
    have prior : recordUpperSeedTailChunk448Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix447 := by
      simpa only [
        recordUpperSeedTailChunk448Before,
        recordUpperSeedTailChunk447State] using h447
    simpa only [recordUpperSeedTailPrefix448] using
      recordUpperSeedTailChunk448Step.certifies prior
  have h449 : recordUpperSeedTailChunk449State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix449 := by
    have prior : recordUpperSeedTailChunk449Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix448 := by
      simpa only [
        recordUpperSeedTailChunk449Before,
        recordUpperSeedTailChunk448State] using h448
    simpa only [recordUpperSeedTailPrefix449] using
      recordUpperSeedTailChunk449Step.certifies prior
  have h450 : recordUpperSeedTailChunk450State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix450 := by
    have prior : recordUpperSeedTailChunk450Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix449 := by
      simpa only [
        recordUpperSeedTailChunk450Before,
        recordUpperSeedTailChunk449State] using h449
    simpa only [recordUpperSeedTailPrefix450] using
      recordUpperSeedTailChunk450Step.certifies prior
  have h451 : recordUpperSeedTailChunk451State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix451 := by
    have prior : recordUpperSeedTailChunk451Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix450 := by
      simpa only [
        recordUpperSeedTailChunk451Before,
        recordUpperSeedTailChunk450State] using h450
    simpa only [recordUpperSeedTailPrefix451] using
      recordUpperSeedTailChunk451Step.certifies prior
  have h452 : recordUpperSeedTailChunk452State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix452 := by
    have prior : recordUpperSeedTailChunk452Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix451 := by
      simpa only [
        recordUpperSeedTailChunk452Before,
        recordUpperSeedTailChunk451State] using h451
    simpa only [recordUpperSeedTailPrefix452] using
      recordUpperSeedTailChunk452Step.certifies prior
  have h453 : recordUpperSeedTailChunk453State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix453 := by
    have prior : recordUpperSeedTailChunk453Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix452 := by
      simpa only [
        recordUpperSeedTailChunk453Before,
        recordUpperSeedTailChunk452State] using h452
    simpa only [recordUpperSeedTailPrefix453] using
      recordUpperSeedTailChunk453Step.certifies prior
  have h454 : recordUpperSeedTailChunk454State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix454 := by
    have prior : recordUpperSeedTailChunk454Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix453 := by
      simpa only [
        recordUpperSeedTailChunk454Before,
        recordUpperSeedTailChunk453State] using h453
    simpa only [recordUpperSeedTailPrefix454] using
      recordUpperSeedTailChunk454Step.certifies prior
  have h455 : recordUpperSeedTailChunk455State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix455 := by
    have prior : recordUpperSeedTailChunk455Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix454 := by
      simpa only [
        recordUpperSeedTailChunk455Before,
        recordUpperSeedTailChunk454State] using h454
    simpa only [recordUpperSeedTailPrefix455] using
      recordUpperSeedTailChunk455Step.certifies prior
  have h456 : recordUpperSeedTailChunk456State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix456 := by
    have prior : recordUpperSeedTailChunk456Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix455 := by
      simpa only [
        recordUpperSeedTailChunk456Before,
        recordUpperSeedTailChunk455State] using h455
    simpa only [recordUpperSeedTailPrefix456] using
      recordUpperSeedTailChunk456Step.certifies prior
  have h457 : recordUpperSeedTailChunk457State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix457 := by
    have prior : recordUpperSeedTailChunk457Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix456 := by
      simpa only [
        recordUpperSeedTailChunk457Before,
        recordUpperSeedTailChunk456State] using h456
    simpa only [recordUpperSeedTailPrefix457] using
      recordUpperSeedTailChunk457Step.certifies prior
  have h458 : recordUpperSeedTailChunk458State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix458 := by
    have prior : recordUpperSeedTailChunk458Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix457 := by
      simpa only [
        recordUpperSeedTailChunk458Before,
        recordUpperSeedTailChunk457State] using h457
    simpa only [recordUpperSeedTailPrefix458] using
      recordUpperSeedTailChunk458Step.certifies prior
  have h459 : recordUpperSeedTailChunk459State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix459 := by
    have prior : recordUpperSeedTailChunk459Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix458 := by
      simpa only [
        recordUpperSeedTailChunk459Before,
        recordUpperSeedTailChunk458State] using h458
    simpa only [recordUpperSeedTailPrefix459] using
      recordUpperSeedTailChunk459Step.certifies prior
  have h460 : recordUpperSeedTailChunk460State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix460 := by
    have prior : recordUpperSeedTailChunk460Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix459 := by
      simpa only [
        recordUpperSeedTailChunk460Before,
        recordUpperSeedTailChunk459State] using h459
    simpa only [recordUpperSeedTailPrefix460] using
      recordUpperSeedTailChunk460Step.certifies prior
  have h461 : recordUpperSeedTailChunk461State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix461 := by
    have prior : recordUpperSeedTailChunk461Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix460 := by
      simpa only [
        recordUpperSeedTailChunk461Before,
        recordUpperSeedTailChunk460State] using h460
    simpa only [recordUpperSeedTailPrefix461] using
      recordUpperSeedTailChunk461Step.certifies prior
  have h462 : recordUpperSeedTailChunk462State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix462 := by
    have prior : recordUpperSeedTailChunk462Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix461 := by
      simpa only [
        recordUpperSeedTailChunk462Before,
        recordUpperSeedTailChunk461State] using h461
    simpa only [recordUpperSeedTailPrefix462] using
      recordUpperSeedTailChunk462Step.certifies prior
  have h463 : recordUpperSeedTailChunk463State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix463 := by
    have prior : recordUpperSeedTailChunk463Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix462 := by
      simpa only [
        recordUpperSeedTailChunk463Before,
        recordUpperSeedTailChunk462State] using h462
    simpa only [recordUpperSeedTailPrefix463] using
      recordUpperSeedTailChunk463Step.certifies prior
  exact h463

end PrimeFactorUnimodality
