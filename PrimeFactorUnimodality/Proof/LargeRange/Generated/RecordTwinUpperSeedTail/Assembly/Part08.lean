import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Assembly.Part07
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part320

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-upper-seed-base11.json` (semantic SHA-256 `493791f7b41de1500c4b830f254f9f92fd9c5d50d639b62aa2b46ca48591321f`, excluding elapsed time). Semantic tail assembly group 8. -/

namespace PrimeFactorUnimodality

theorem recordUpperSeedTailGroup08_semantic :
    recordUpperSeedTailChunk320State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix320 := by
  have h281 : recordUpperSeedTailChunk281State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix281 := by
    have boundary : recordUpperSeedTailChunk281Before =
        recordUpperSeedTailChunk280State := by rfl
    exact recordUpperSeedTailChunk281Step.certifies
      (boundary.trans recordUpperSeedTailGroup07_semantic)
  have h282 : recordUpperSeedTailChunk282State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix282 := by
    have boundary : recordUpperSeedTailChunk282Before =
        recordUpperSeedTailChunk281State := by rfl
    exact recordUpperSeedTailChunk282Step.certifies
      (boundary.trans h281)
  have h283 : recordUpperSeedTailChunk283State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix283 := by
    have boundary : recordUpperSeedTailChunk283Before =
        recordUpperSeedTailChunk282State := by rfl
    exact recordUpperSeedTailChunk283Step.certifies
      (boundary.trans h282)
  have h284 : recordUpperSeedTailChunk284State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix284 := by
    have boundary : recordUpperSeedTailChunk284Before =
        recordUpperSeedTailChunk283State := by rfl
    exact recordUpperSeedTailChunk284Step.certifies
      (boundary.trans h283)
  have h285 : recordUpperSeedTailChunk285State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix285 := by
    have boundary : recordUpperSeedTailChunk285Before =
        recordUpperSeedTailChunk284State := by rfl
    exact recordUpperSeedTailChunk285Step.certifies
      (boundary.trans h284)
  have h286 : recordUpperSeedTailChunk286State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix286 := by
    have boundary : recordUpperSeedTailChunk286Before =
        recordUpperSeedTailChunk285State := by rfl
    exact recordUpperSeedTailChunk286Step.certifies
      (boundary.trans h285)
  have h287 : recordUpperSeedTailChunk287State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix287 := by
    have boundary : recordUpperSeedTailChunk287Before =
        recordUpperSeedTailChunk286State := by rfl
    exact recordUpperSeedTailChunk287Step.certifies
      (boundary.trans h286)
  have h288 : recordUpperSeedTailChunk288State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix288 := by
    have boundary : recordUpperSeedTailChunk288Before =
        recordUpperSeedTailChunk287State := by rfl
    exact recordUpperSeedTailChunk288Step.certifies
      (boundary.trans h287)
  have h289 : recordUpperSeedTailChunk289State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix289 := by
    have boundary : recordUpperSeedTailChunk289Before =
        recordUpperSeedTailChunk288State := by rfl
    exact recordUpperSeedTailChunk289Step.certifies
      (boundary.trans h288)
  have h290 : recordUpperSeedTailChunk290State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix290 := by
    have boundary : recordUpperSeedTailChunk290Before =
        recordUpperSeedTailChunk289State := by rfl
    exact recordUpperSeedTailChunk290Step.certifies
      (boundary.trans h289)
  have h291 : recordUpperSeedTailChunk291State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix291 := by
    have boundary : recordUpperSeedTailChunk291Before =
        recordUpperSeedTailChunk290State := by rfl
    exact recordUpperSeedTailChunk291Step.certifies
      (boundary.trans h290)
  have h292 : recordUpperSeedTailChunk292State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix292 := by
    have boundary : recordUpperSeedTailChunk292Before =
        recordUpperSeedTailChunk291State := by rfl
    exact recordUpperSeedTailChunk292Step.certifies
      (boundary.trans h291)
  have h293 : recordUpperSeedTailChunk293State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix293 := by
    have boundary : recordUpperSeedTailChunk293Before =
        recordUpperSeedTailChunk292State := by rfl
    exact recordUpperSeedTailChunk293Step.certifies
      (boundary.trans h292)
  have h294 : recordUpperSeedTailChunk294State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix294 := by
    have boundary : recordUpperSeedTailChunk294Before =
        recordUpperSeedTailChunk293State := by rfl
    exact recordUpperSeedTailChunk294Step.certifies
      (boundary.trans h293)
  have h295 : recordUpperSeedTailChunk295State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix295 := by
    have boundary : recordUpperSeedTailChunk295Before =
        recordUpperSeedTailChunk294State := by rfl
    exact recordUpperSeedTailChunk295Step.certifies
      (boundary.trans h294)
  have h296 : recordUpperSeedTailChunk296State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix296 := by
    have boundary : recordUpperSeedTailChunk296Before =
        recordUpperSeedTailChunk295State := by rfl
    exact recordUpperSeedTailChunk296Step.certifies
      (boundary.trans h295)
  have h297 : recordUpperSeedTailChunk297State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix297 := by
    have boundary : recordUpperSeedTailChunk297Before =
        recordUpperSeedTailChunk296State := by rfl
    exact recordUpperSeedTailChunk297Step.certifies
      (boundary.trans h296)
  have h298 : recordUpperSeedTailChunk298State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix298 := by
    have boundary : recordUpperSeedTailChunk298Before =
        recordUpperSeedTailChunk297State := by rfl
    exact recordUpperSeedTailChunk298Step.certifies
      (boundary.trans h297)
  have h299 : recordUpperSeedTailChunk299State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix299 := by
    have boundary : recordUpperSeedTailChunk299Before =
        recordUpperSeedTailChunk298State := by rfl
    exact recordUpperSeedTailChunk299Step.certifies
      (boundary.trans h298)
  have h300 : recordUpperSeedTailChunk300State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix300 := by
    have boundary : recordUpperSeedTailChunk300Before =
        recordUpperSeedTailChunk299State := by rfl
    exact recordUpperSeedTailChunk300Step.certifies
      (boundary.trans h299)
  have h301 : recordUpperSeedTailChunk301State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix301 := by
    have boundary : recordUpperSeedTailChunk301Before =
        recordUpperSeedTailChunk300State := by rfl
    exact recordUpperSeedTailChunk301Step.certifies
      (boundary.trans h300)
  have h302 : recordUpperSeedTailChunk302State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix302 := by
    have boundary : recordUpperSeedTailChunk302Before =
        recordUpperSeedTailChunk301State := by rfl
    exact recordUpperSeedTailChunk302Step.certifies
      (boundary.trans h301)
  have h303 : recordUpperSeedTailChunk303State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix303 := by
    have boundary : recordUpperSeedTailChunk303Before =
        recordUpperSeedTailChunk302State := by rfl
    exact recordUpperSeedTailChunk303Step.certifies
      (boundary.trans h302)
  have h304 : recordUpperSeedTailChunk304State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix304 := by
    have boundary : recordUpperSeedTailChunk304Before =
        recordUpperSeedTailChunk303State := by rfl
    exact recordUpperSeedTailChunk304Step.certifies
      (boundary.trans h303)
  have h305 : recordUpperSeedTailChunk305State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix305 := by
    have boundary : recordUpperSeedTailChunk305Before =
        recordUpperSeedTailChunk304State := by rfl
    exact recordUpperSeedTailChunk305Step.certifies
      (boundary.trans h304)
  have h306 : recordUpperSeedTailChunk306State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix306 := by
    have boundary : recordUpperSeedTailChunk306Before =
        recordUpperSeedTailChunk305State := by rfl
    exact recordUpperSeedTailChunk306Step.certifies
      (boundary.trans h305)
  have h307 : recordUpperSeedTailChunk307State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix307 := by
    have boundary : recordUpperSeedTailChunk307Before =
        recordUpperSeedTailChunk306State := by rfl
    exact recordUpperSeedTailChunk307Step.certifies
      (boundary.trans h306)
  have h308 : recordUpperSeedTailChunk308State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix308 := by
    have boundary : recordUpperSeedTailChunk308Before =
        recordUpperSeedTailChunk307State := by rfl
    exact recordUpperSeedTailChunk308Step.certifies
      (boundary.trans h307)
  have h309 : recordUpperSeedTailChunk309State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix309 := by
    have boundary : recordUpperSeedTailChunk309Before =
        recordUpperSeedTailChunk308State := by rfl
    exact recordUpperSeedTailChunk309Step.certifies
      (boundary.trans h308)
  have h310 : recordUpperSeedTailChunk310State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix310 := by
    have boundary : recordUpperSeedTailChunk310Before =
        recordUpperSeedTailChunk309State := by rfl
    exact recordUpperSeedTailChunk310Step.certifies
      (boundary.trans h309)
  have h311 : recordUpperSeedTailChunk311State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix311 := by
    have boundary : recordUpperSeedTailChunk311Before =
        recordUpperSeedTailChunk310State := by rfl
    exact recordUpperSeedTailChunk311Step.certifies
      (boundary.trans h310)
  have h312 : recordUpperSeedTailChunk312State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix312 := by
    have boundary : recordUpperSeedTailChunk312Before =
        recordUpperSeedTailChunk311State := by rfl
    exact recordUpperSeedTailChunk312Step.certifies
      (boundary.trans h311)
  have h313 : recordUpperSeedTailChunk313State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix313 := by
    have boundary : recordUpperSeedTailChunk313Before =
        recordUpperSeedTailChunk312State := by rfl
    exact recordUpperSeedTailChunk313Step.certifies
      (boundary.trans h312)
  have h314 : recordUpperSeedTailChunk314State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix314 := by
    have boundary : recordUpperSeedTailChunk314Before =
        recordUpperSeedTailChunk313State := by rfl
    exact recordUpperSeedTailChunk314Step.certifies
      (boundary.trans h313)
  have h315 : recordUpperSeedTailChunk315State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix315 := by
    have boundary : recordUpperSeedTailChunk315Before =
        recordUpperSeedTailChunk314State := by rfl
    exact recordUpperSeedTailChunk315Step.certifies
      (boundary.trans h314)
  have h316 : recordUpperSeedTailChunk316State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix316 := by
    have boundary : recordUpperSeedTailChunk316Before =
        recordUpperSeedTailChunk315State := by rfl
    exact recordUpperSeedTailChunk316Step.certifies
      (boundary.trans h315)
  have h317 : recordUpperSeedTailChunk317State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix317 := by
    have boundary : recordUpperSeedTailChunk317Before =
        recordUpperSeedTailChunk316State := by rfl
    exact recordUpperSeedTailChunk317Step.certifies
      (boundary.trans h316)
  have h318 : recordUpperSeedTailChunk318State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix318 := by
    have boundary : recordUpperSeedTailChunk318Before =
        recordUpperSeedTailChunk317State := by rfl
    exact recordUpperSeedTailChunk318Step.certifies
      (boundary.trans h317)
  have h319 : recordUpperSeedTailChunk319State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix319 := by
    have boundary : recordUpperSeedTailChunk319Before =
        recordUpperSeedTailChunk318State := by rfl
    exact recordUpperSeedTailChunk319Step.certifies
      (boundary.trans h318)
  have h320 : recordUpperSeedTailChunk320State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix320 := by
    have boundary : recordUpperSeedTailChunk320Before =
        recordUpperSeedTailChunk319State := by rfl
    exact recordUpperSeedTailChunk320Step.certifies
      (boundary.trans h319)
  exact h320

end PrimeFactorUnimodality
