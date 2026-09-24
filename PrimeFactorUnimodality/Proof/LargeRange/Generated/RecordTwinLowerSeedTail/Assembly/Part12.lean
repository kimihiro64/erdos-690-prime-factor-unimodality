import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Assembly.Part11
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part463

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-lower-seed.json` (semantic SHA-256 `3ce105dad06099400dfd2e30c65d47c6e02828915452a8459553c3bb0eb78b73`, excluding elapsed time). Semantic tail assembly group 12. -/

namespace PrimeFactorUnimodality

theorem recordLowerSeedTailGroup12_semantic :
    recordLowerSeedTailChunk463State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix463 := by
  have h441 : recordLowerSeedTailChunk441State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix441 := by
    have boundary : recordLowerSeedTailChunk441Before =
        recordLowerSeedTailChunk440State := by rfl
    exact recordLowerSeedTailChunk441Step.certifies
      (boundary.trans recordLowerSeedTailGroup11_semantic)
  have h442 : recordLowerSeedTailChunk442State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix442 := by
    have boundary : recordLowerSeedTailChunk442Before =
        recordLowerSeedTailChunk441State := by rfl
    exact recordLowerSeedTailChunk442Step.certifies
      (boundary.trans h441)
  have h443 : recordLowerSeedTailChunk443State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix443 := by
    have boundary : recordLowerSeedTailChunk443Before =
        recordLowerSeedTailChunk442State := by rfl
    exact recordLowerSeedTailChunk443Step.certifies
      (boundary.trans h442)
  have h444 : recordLowerSeedTailChunk444State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix444 := by
    have boundary : recordLowerSeedTailChunk444Before =
        recordLowerSeedTailChunk443State := by rfl
    exact recordLowerSeedTailChunk444Step.certifies
      (boundary.trans h443)
  have h445 : recordLowerSeedTailChunk445State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix445 := by
    have boundary : recordLowerSeedTailChunk445Before =
        recordLowerSeedTailChunk444State := by rfl
    exact recordLowerSeedTailChunk445Step.certifies
      (boundary.trans h444)
  have h446 : recordLowerSeedTailChunk446State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix446 := by
    have boundary : recordLowerSeedTailChunk446Before =
        recordLowerSeedTailChunk445State := by rfl
    exact recordLowerSeedTailChunk446Step.certifies
      (boundary.trans h445)
  have h447 : recordLowerSeedTailChunk447State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix447 := by
    have boundary : recordLowerSeedTailChunk447Before =
        recordLowerSeedTailChunk446State := by rfl
    exact recordLowerSeedTailChunk447Step.certifies
      (boundary.trans h446)
  have h448 : recordLowerSeedTailChunk448State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix448 := by
    have boundary : recordLowerSeedTailChunk448Before =
        recordLowerSeedTailChunk447State := by rfl
    exact recordLowerSeedTailChunk448Step.certifies
      (boundary.trans h447)
  have h449 : recordLowerSeedTailChunk449State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix449 := by
    have boundary : recordLowerSeedTailChunk449Before =
        recordLowerSeedTailChunk448State := by rfl
    exact recordLowerSeedTailChunk449Step.certifies
      (boundary.trans h448)
  have h450 : recordLowerSeedTailChunk450State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix450 := by
    have boundary : recordLowerSeedTailChunk450Before =
        recordLowerSeedTailChunk449State := by rfl
    exact recordLowerSeedTailChunk450Step.certifies
      (boundary.trans h449)
  have h451 : recordLowerSeedTailChunk451State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix451 := by
    have boundary : recordLowerSeedTailChunk451Before =
        recordLowerSeedTailChunk450State := by rfl
    exact recordLowerSeedTailChunk451Step.certifies
      (boundary.trans h450)
  have h452 : recordLowerSeedTailChunk452State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix452 := by
    have boundary : recordLowerSeedTailChunk452Before =
        recordLowerSeedTailChunk451State := by rfl
    exact recordLowerSeedTailChunk452Step.certifies
      (boundary.trans h451)
  have h453 : recordLowerSeedTailChunk453State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix453 := by
    have boundary : recordLowerSeedTailChunk453Before =
        recordLowerSeedTailChunk452State := by rfl
    exact recordLowerSeedTailChunk453Step.certifies
      (boundary.trans h452)
  have h454 : recordLowerSeedTailChunk454State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix454 := by
    have boundary : recordLowerSeedTailChunk454Before =
        recordLowerSeedTailChunk453State := by rfl
    exact recordLowerSeedTailChunk454Step.certifies
      (boundary.trans h453)
  have h455 : recordLowerSeedTailChunk455State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix455 := by
    have boundary : recordLowerSeedTailChunk455Before =
        recordLowerSeedTailChunk454State := by rfl
    exact recordLowerSeedTailChunk455Step.certifies
      (boundary.trans h454)
  have h456 : recordLowerSeedTailChunk456State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix456 := by
    have boundary : recordLowerSeedTailChunk456Before =
        recordLowerSeedTailChunk455State := by rfl
    exact recordLowerSeedTailChunk456Step.certifies
      (boundary.trans h455)
  have h457 : recordLowerSeedTailChunk457State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix457 := by
    have boundary : recordLowerSeedTailChunk457Before =
        recordLowerSeedTailChunk456State := by rfl
    exact recordLowerSeedTailChunk457Step.certifies
      (boundary.trans h456)
  have h458 : recordLowerSeedTailChunk458State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix458 := by
    have boundary : recordLowerSeedTailChunk458Before =
        recordLowerSeedTailChunk457State := by rfl
    exact recordLowerSeedTailChunk458Step.certifies
      (boundary.trans h457)
  have h459 : recordLowerSeedTailChunk459State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix459 := by
    have boundary : recordLowerSeedTailChunk459Before =
        recordLowerSeedTailChunk458State := by rfl
    exact recordLowerSeedTailChunk459Step.certifies
      (boundary.trans h458)
  have h460 : recordLowerSeedTailChunk460State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix460 := by
    have boundary : recordLowerSeedTailChunk460Before =
        recordLowerSeedTailChunk459State := by rfl
    exact recordLowerSeedTailChunk460Step.certifies
      (boundary.trans h459)
  have h461 : recordLowerSeedTailChunk461State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix461 := by
    have boundary : recordLowerSeedTailChunk461Before =
        recordLowerSeedTailChunk460State := by rfl
    exact recordLowerSeedTailChunk461Step.certifies
      (boundary.trans h460)
  have h462 : recordLowerSeedTailChunk462State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix462 := by
    have boundary : recordLowerSeedTailChunk462Before =
        recordLowerSeedTailChunk461State := by rfl
    exact recordLowerSeedTailChunk462Step.certifies
      (boundary.trans h461)
  have h463 : recordLowerSeedTailChunk463State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix463 := by
    have boundary : recordLowerSeedTailChunk463Before =
        recordLowerSeedTailChunk462State := by rfl
    exact recordLowerSeedTailChunk463Step.certifies
      (boundary.trans h462)
  exact h463

end PrimeFactorUnimodality
