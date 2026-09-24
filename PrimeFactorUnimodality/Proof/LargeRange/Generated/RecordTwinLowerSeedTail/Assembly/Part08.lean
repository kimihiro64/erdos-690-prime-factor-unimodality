import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Assembly.Part07
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part320

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-lower-seed.json` (semantic SHA-256 `3ce105dad06099400dfd2e30c65d47c6e02828915452a8459553c3bb0eb78b73`, excluding elapsed time). Semantic tail assembly group 8. -/

namespace PrimeFactorUnimodality

theorem recordLowerSeedTailGroup08_semantic :
    recordLowerSeedTailChunk320State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix320 := by
  have h281 : recordLowerSeedTailChunk281State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix281 := by
    have boundary : recordLowerSeedTailChunk281Before =
        recordLowerSeedTailChunk280State := by rfl
    exact recordLowerSeedTailChunk281Step.certifies
      (boundary.trans recordLowerSeedTailGroup07_semantic)
  have h282 : recordLowerSeedTailChunk282State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix282 := by
    have boundary : recordLowerSeedTailChunk282Before =
        recordLowerSeedTailChunk281State := by rfl
    exact recordLowerSeedTailChunk282Step.certifies
      (boundary.trans h281)
  have h283 : recordLowerSeedTailChunk283State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix283 := by
    have boundary : recordLowerSeedTailChunk283Before =
        recordLowerSeedTailChunk282State := by rfl
    exact recordLowerSeedTailChunk283Step.certifies
      (boundary.trans h282)
  have h284 : recordLowerSeedTailChunk284State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix284 := by
    have boundary : recordLowerSeedTailChunk284Before =
        recordLowerSeedTailChunk283State := by rfl
    exact recordLowerSeedTailChunk284Step.certifies
      (boundary.trans h283)
  have h285 : recordLowerSeedTailChunk285State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix285 := by
    have boundary : recordLowerSeedTailChunk285Before =
        recordLowerSeedTailChunk284State := by rfl
    exact recordLowerSeedTailChunk285Step.certifies
      (boundary.trans h284)
  have h286 : recordLowerSeedTailChunk286State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix286 := by
    have boundary : recordLowerSeedTailChunk286Before =
        recordLowerSeedTailChunk285State := by rfl
    exact recordLowerSeedTailChunk286Step.certifies
      (boundary.trans h285)
  have h287 : recordLowerSeedTailChunk287State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix287 := by
    have boundary : recordLowerSeedTailChunk287Before =
        recordLowerSeedTailChunk286State := by rfl
    exact recordLowerSeedTailChunk287Step.certifies
      (boundary.trans h286)
  have h288 : recordLowerSeedTailChunk288State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix288 := by
    have boundary : recordLowerSeedTailChunk288Before =
        recordLowerSeedTailChunk287State := by rfl
    exact recordLowerSeedTailChunk288Step.certifies
      (boundary.trans h287)
  have h289 : recordLowerSeedTailChunk289State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix289 := by
    have boundary : recordLowerSeedTailChunk289Before =
        recordLowerSeedTailChunk288State := by rfl
    exact recordLowerSeedTailChunk289Step.certifies
      (boundary.trans h288)
  have h290 : recordLowerSeedTailChunk290State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix290 := by
    have boundary : recordLowerSeedTailChunk290Before =
        recordLowerSeedTailChunk289State := by rfl
    exact recordLowerSeedTailChunk290Step.certifies
      (boundary.trans h289)
  have h291 : recordLowerSeedTailChunk291State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix291 := by
    have boundary : recordLowerSeedTailChunk291Before =
        recordLowerSeedTailChunk290State := by rfl
    exact recordLowerSeedTailChunk291Step.certifies
      (boundary.trans h290)
  have h292 : recordLowerSeedTailChunk292State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix292 := by
    have boundary : recordLowerSeedTailChunk292Before =
        recordLowerSeedTailChunk291State := by rfl
    exact recordLowerSeedTailChunk292Step.certifies
      (boundary.trans h291)
  have h293 : recordLowerSeedTailChunk293State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix293 := by
    have boundary : recordLowerSeedTailChunk293Before =
        recordLowerSeedTailChunk292State := by rfl
    exact recordLowerSeedTailChunk293Step.certifies
      (boundary.trans h292)
  have h294 : recordLowerSeedTailChunk294State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix294 := by
    have boundary : recordLowerSeedTailChunk294Before =
        recordLowerSeedTailChunk293State := by rfl
    exact recordLowerSeedTailChunk294Step.certifies
      (boundary.trans h293)
  have h295 : recordLowerSeedTailChunk295State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix295 := by
    have boundary : recordLowerSeedTailChunk295Before =
        recordLowerSeedTailChunk294State := by rfl
    exact recordLowerSeedTailChunk295Step.certifies
      (boundary.trans h294)
  have h296 : recordLowerSeedTailChunk296State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix296 := by
    have boundary : recordLowerSeedTailChunk296Before =
        recordLowerSeedTailChunk295State := by rfl
    exact recordLowerSeedTailChunk296Step.certifies
      (boundary.trans h295)
  have h297 : recordLowerSeedTailChunk297State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix297 := by
    have boundary : recordLowerSeedTailChunk297Before =
        recordLowerSeedTailChunk296State := by rfl
    exact recordLowerSeedTailChunk297Step.certifies
      (boundary.trans h296)
  have h298 : recordLowerSeedTailChunk298State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix298 := by
    have boundary : recordLowerSeedTailChunk298Before =
        recordLowerSeedTailChunk297State := by rfl
    exact recordLowerSeedTailChunk298Step.certifies
      (boundary.trans h297)
  have h299 : recordLowerSeedTailChunk299State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix299 := by
    have boundary : recordLowerSeedTailChunk299Before =
        recordLowerSeedTailChunk298State := by rfl
    exact recordLowerSeedTailChunk299Step.certifies
      (boundary.trans h298)
  have h300 : recordLowerSeedTailChunk300State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix300 := by
    have boundary : recordLowerSeedTailChunk300Before =
        recordLowerSeedTailChunk299State := by rfl
    exact recordLowerSeedTailChunk300Step.certifies
      (boundary.trans h299)
  have h301 : recordLowerSeedTailChunk301State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix301 := by
    have boundary : recordLowerSeedTailChunk301Before =
        recordLowerSeedTailChunk300State := by rfl
    exact recordLowerSeedTailChunk301Step.certifies
      (boundary.trans h300)
  have h302 : recordLowerSeedTailChunk302State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix302 := by
    have boundary : recordLowerSeedTailChunk302Before =
        recordLowerSeedTailChunk301State := by rfl
    exact recordLowerSeedTailChunk302Step.certifies
      (boundary.trans h301)
  have h303 : recordLowerSeedTailChunk303State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix303 := by
    have boundary : recordLowerSeedTailChunk303Before =
        recordLowerSeedTailChunk302State := by rfl
    exact recordLowerSeedTailChunk303Step.certifies
      (boundary.trans h302)
  have h304 : recordLowerSeedTailChunk304State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix304 := by
    have boundary : recordLowerSeedTailChunk304Before =
        recordLowerSeedTailChunk303State := by rfl
    exact recordLowerSeedTailChunk304Step.certifies
      (boundary.trans h303)
  have h305 : recordLowerSeedTailChunk305State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix305 := by
    have boundary : recordLowerSeedTailChunk305Before =
        recordLowerSeedTailChunk304State := by rfl
    exact recordLowerSeedTailChunk305Step.certifies
      (boundary.trans h304)
  have h306 : recordLowerSeedTailChunk306State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix306 := by
    have boundary : recordLowerSeedTailChunk306Before =
        recordLowerSeedTailChunk305State := by rfl
    exact recordLowerSeedTailChunk306Step.certifies
      (boundary.trans h305)
  have h307 : recordLowerSeedTailChunk307State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix307 := by
    have boundary : recordLowerSeedTailChunk307Before =
        recordLowerSeedTailChunk306State := by rfl
    exact recordLowerSeedTailChunk307Step.certifies
      (boundary.trans h306)
  have h308 : recordLowerSeedTailChunk308State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix308 := by
    have boundary : recordLowerSeedTailChunk308Before =
        recordLowerSeedTailChunk307State := by rfl
    exact recordLowerSeedTailChunk308Step.certifies
      (boundary.trans h307)
  have h309 : recordLowerSeedTailChunk309State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix309 := by
    have boundary : recordLowerSeedTailChunk309Before =
        recordLowerSeedTailChunk308State := by rfl
    exact recordLowerSeedTailChunk309Step.certifies
      (boundary.trans h308)
  have h310 : recordLowerSeedTailChunk310State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix310 := by
    have boundary : recordLowerSeedTailChunk310Before =
        recordLowerSeedTailChunk309State := by rfl
    exact recordLowerSeedTailChunk310Step.certifies
      (boundary.trans h309)
  have h311 : recordLowerSeedTailChunk311State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix311 := by
    have boundary : recordLowerSeedTailChunk311Before =
        recordLowerSeedTailChunk310State := by rfl
    exact recordLowerSeedTailChunk311Step.certifies
      (boundary.trans h310)
  have h312 : recordLowerSeedTailChunk312State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix312 := by
    have boundary : recordLowerSeedTailChunk312Before =
        recordLowerSeedTailChunk311State := by rfl
    exact recordLowerSeedTailChunk312Step.certifies
      (boundary.trans h311)
  have h313 : recordLowerSeedTailChunk313State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix313 := by
    have boundary : recordLowerSeedTailChunk313Before =
        recordLowerSeedTailChunk312State := by rfl
    exact recordLowerSeedTailChunk313Step.certifies
      (boundary.trans h312)
  have h314 : recordLowerSeedTailChunk314State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix314 := by
    have boundary : recordLowerSeedTailChunk314Before =
        recordLowerSeedTailChunk313State := by rfl
    exact recordLowerSeedTailChunk314Step.certifies
      (boundary.trans h313)
  have h315 : recordLowerSeedTailChunk315State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix315 := by
    have boundary : recordLowerSeedTailChunk315Before =
        recordLowerSeedTailChunk314State := by rfl
    exact recordLowerSeedTailChunk315Step.certifies
      (boundary.trans h314)
  have h316 : recordLowerSeedTailChunk316State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix316 := by
    have boundary : recordLowerSeedTailChunk316Before =
        recordLowerSeedTailChunk315State := by rfl
    exact recordLowerSeedTailChunk316Step.certifies
      (boundary.trans h315)
  have h317 : recordLowerSeedTailChunk317State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix317 := by
    have boundary : recordLowerSeedTailChunk317Before =
        recordLowerSeedTailChunk316State := by rfl
    exact recordLowerSeedTailChunk317Step.certifies
      (boundary.trans h316)
  have h318 : recordLowerSeedTailChunk318State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix318 := by
    have boundary : recordLowerSeedTailChunk318Before =
        recordLowerSeedTailChunk317State := by rfl
    exact recordLowerSeedTailChunk318Step.certifies
      (boundary.trans h317)
  have h319 : recordLowerSeedTailChunk319State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix319 := by
    have boundary : recordLowerSeedTailChunk319Before =
        recordLowerSeedTailChunk318State := by rfl
    exact recordLowerSeedTailChunk319Step.certifies
      (boundary.trans h318)
  have h320 : recordLowerSeedTailChunk320State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix320 := by
    have boundary : recordLowerSeedTailChunk320Before =
        recordLowerSeedTailChunk319State := by rfl
    exact recordLowerSeedTailChunk320Step.certifies
      (boundary.trans h319)
  exact h320

end PrimeFactorUnimodality
