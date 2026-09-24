import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Assembly.Part11
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part463

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-upper-seed-base11.json` (semantic SHA-256 `493791f7b41de1500c4b830f254f9f92fd9c5d50d639b62aa2b46ca48591321f`, excluding elapsed time). Semantic tail assembly group 12. -/

namespace PrimeFactorUnimodality

theorem recordUpperSeedTailGroup12_semantic :
    recordUpperSeedTailChunk463State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix463 := by
  have h441 : recordUpperSeedTailChunk441State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix441 := by
    have boundary : recordUpperSeedTailChunk441Before =
        recordUpperSeedTailChunk440State := by rfl
    exact recordUpperSeedTailChunk441Step.certifies
      (boundary.trans recordUpperSeedTailGroup11_semantic)
  have h442 : recordUpperSeedTailChunk442State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix442 := by
    have boundary : recordUpperSeedTailChunk442Before =
        recordUpperSeedTailChunk441State := by rfl
    exact recordUpperSeedTailChunk442Step.certifies
      (boundary.trans h441)
  have h443 : recordUpperSeedTailChunk443State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix443 := by
    have boundary : recordUpperSeedTailChunk443Before =
        recordUpperSeedTailChunk442State := by rfl
    exact recordUpperSeedTailChunk443Step.certifies
      (boundary.trans h442)
  have h444 : recordUpperSeedTailChunk444State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix444 := by
    have boundary : recordUpperSeedTailChunk444Before =
        recordUpperSeedTailChunk443State := by rfl
    exact recordUpperSeedTailChunk444Step.certifies
      (boundary.trans h443)
  have h445 : recordUpperSeedTailChunk445State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix445 := by
    have boundary : recordUpperSeedTailChunk445Before =
        recordUpperSeedTailChunk444State := by rfl
    exact recordUpperSeedTailChunk445Step.certifies
      (boundary.trans h444)
  have h446 : recordUpperSeedTailChunk446State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix446 := by
    have boundary : recordUpperSeedTailChunk446Before =
        recordUpperSeedTailChunk445State := by rfl
    exact recordUpperSeedTailChunk446Step.certifies
      (boundary.trans h445)
  have h447 : recordUpperSeedTailChunk447State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix447 := by
    have boundary : recordUpperSeedTailChunk447Before =
        recordUpperSeedTailChunk446State := by rfl
    exact recordUpperSeedTailChunk447Step.certifies
      (boundary.trans h446)
  have h448 : recordUpperSeedTailChunk448State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix448 := by
    have boundary : recordUpperSeedTailChunk448Before =
        recordUpperSeedTailChunk447State := by rfl
    exact recordUpperSeedTailChunk448Step.certifies
      (boundary.trans h447)
  have h449 : recordUpperSeedTailChunk449State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix449 := by
    have boundary : recordUpperSeedTailChunk449Before =
        recordUpperSeedTailChunk448State := by rfl
    exact recordUpperSeedTailChunk449Step.certifies
      (boundary.trans h448)
  have h450 : recordUpperSeedTailChunk450State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix450 := by
    have boundary : recordUpperSeedTailChunk450Before =
        recordUpperSeedTailChunk449State := by rfl
    exact recordUpperSeedTailChunk450Step.certifies
      (boundary.trans h449)
  have h451 : recordUpperSeedTailChunk451State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix451 := by
    have boundary : recordUpperSeedTailChunk451Before =
        recordUpperSeedTailChunk450State := by rfl
    exact recordUpperSeedTailChunk451Step.certifies
      (boundary.trans h450)
  have h452 : recordUpperSeedTailChunk452State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix452 := by
    have boundary : recordUpperSeedTailChunk452Before =
        recordUpperSeedTailChunk451State := by rfl
    exact recordUpperSeedTailChunk452Step.certifies
      (boundary.trans h451)
  have h453 : recordUpperSeedTailChunk453State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix453 := by
    have boundary : recordUpperSeedTailChunk453Before =
        recordUpperSeedTailChunk452State := by rfl
    exact recordUpperSeedTailChunk453Step.certifies
      (boundary.trans h452)
  have h454 : recordUpperSeedTailChunk454State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix454 := by
    have boundary : recordUpperSeedTailChunk454Before =
        recordUpperSeedTailChunk453State := by rfl
    exact recordUpperSeedTailChunk454Step.certifies
      (boundary.trans h453)
  have h455 : recordUpperSeedTailChunk455State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix455 := by
    have boundary : recordUpperSeedTailChunk455Before =
        recordUpperSeedTailChunk454State := by rfl
    exact recordUpperSeedTailChunk455Step.certifies
      (boundary.trans h454)
  have h456 : recordUpperSeedTailChunk456State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix456 := by
    have boundary : recordUpperSeedTailChunk456Before =
        recordUpperSeedTailChunk455State := by rfl
    exact recordUpperSeedTailChunk456Step.certifies
      (boundary.trans h455)
  have h457 : recordUpperSeedTailChunk457State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix457 := by
    have boundary : recordUpperSeedTailChunk457Before =
        recordUpperSeedTailChunk456State := by rfl
    exact recordUpperSeedTailChunk457Step.certifies
      (boundary.trans h456)
  have h458 : recordUpperSeedTailChunk458State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix458 := by
    have boundary : recordUpperSeedTailChunk458Before =
        recordUpperSeedTailChunk457State := by rfl
    exact recordUpperSeedTailChunk458Step.certifies
      (boundary.trans h457)
  have h459 : recordUpperSeedTailChunk459State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix459 := by
    have boundary : recordUpperSeedTailChunk459Before =
        recordUpperSeedTailChunk458State := by rfl
    exact recordUpperSeedTailChunk459Step.certifies
      (boundary.trans h458)
  have h460 : recordUpperSeedTailChunk460State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix460 := by
    have boundary : recordUpperSeedTailChunk460Before =
        recordUpperSeedTailChunk459State := by rfl
    exact recordUpperSeedTailChunk460Step.certifies
      (boundary.trans h459)
  have h461 : recordUpperSeedTailChunk461State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix461 := by
    have boundary : recordUpperSeedTailChunk461Before =
        recordUpperSeedTailChunk460State := by rfl
    exact recordUpperSeedTailChunk461Step.certifies
      (boundary.trans h460)
  have h462 : recordUpperSeedTailChunk462State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix462 := by
    have boundary : recordUpperSeedTailChunk462Before =
        recordUpperSeedTailChunk461State := by rfl
    exact recordUpperSeedTailChunk462Step.certifies
      (boundary.trans h461)
  have h463 : recordUpperSeedTailChunk463State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix463 := by
    have boundary : recordUpperSeedTailChunk463Before =
        recordUpperSeedTailChunk462State := by rfl
    exact recordUpperSeedTailChunk463Step.certifies
      (boundary.trans h462)
  exact h463

end PrimeFactorUnimodality
