import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Assembly.Part07
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part320

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-upper-seed-base11.json` (semantic SHA-256 `493791f7b41de1500c4b830f254f9f92fd9c5d50d639b62aa2b46ca48591321f`, excluding elapsed time). Semantic tail assembly group 8. -/

namespace PrimeFactorUnimodality

theorem recordUpperSeedTailGroup08_semantic :
    recordUpperSeedTailChunk320State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix320 := by
  have h281 : recordUpperSeedTailChunk281State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix281 := by
    have prior : recordUpperSeedTailChunk281Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix280 := by
      simpa only [
        recordUpperSeedTailChunk281Before,
        recordUpperSeedTailChunk280State] using recordUpperSeedTailGroup07_semantic
    simpa only [recordUpperSeedTailPrefix281] using
      recordUpperSeedTailChunk281Step.certifies prior
  have h282 : recordUpperSeedTailChunk282State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix282 := by
    have prior : recordUpperSeedTailChunk282Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix281 := by
      simpa only [
        recordUpperSeedTailChunk282Before,
        recordUpperSeedTailChunk281State] using h281
    simpa only [recordUpperSeedTailPrefix282] using
      recordUpperSeedTailChunk282Step.certifies prior
  have h283 : recordUpperSeedTailChunk283State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix283 := by
    have prior : recordUpperSeedTailChunk283Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix282 := by
      simpa only [
        recordUpperSeedTailChunk283Before,
        recordUpperSeedTailChunk282State] using h282
    simpa only [recordUpperSeedTailPrefix283] using
      recordUpperSeedTailChunk283Step.certifies prior
  have h284 : recordUpperSeedTailChunk284State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix284 := by
    have prior : recordUpperSeedTailChunk284Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix283 := by
      simpa only [
        recordUpperSeedTailChunk284Before,
        recordUpperSeedTailChunk283State] using h283
    simpa only [recordUpperSeedTailPrefix284] using
      recordUpperSeedTailChunk284Step.certifies prior
  have h285 : recordUpperSeedTailChunk285State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix285 := by
    have prior : recordUpperSeedTailChunk285Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix284 := by
      simpa only [
        recordUpperSeedTailChunk285Before,
        recordUpperSeedTailChunk284State] using h284
    simpa only [recordUpperSeedTailPrefix285] using
      recordUpperSeedTailChunk285Step.certifies prior
  have h286 : recordUpperSeedTailChunk286State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix286 := by
    have prior : recordUpperSeedTailChunk286Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix285 := by
      simpa only [
        recordUpperSeedTailChunk286Before,
        recordUpperSeedTailChunk285State] using h285
    simpa only [recordUpperSeedTailPrefix286] using
      recordUpperSeedTailChunk286Step.certifies prior
  have h287 : recordUpperSeedTailChunk287State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix287 := by
    have prior : recordUpperSeedTailChunk287Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix286 := by
      simpa only [
        recordUpperSeedTailChunk287Before,
        recordUpperSeedTailChunk286State] using h286
    simpa only [recordUpperSeedTailPrefix287] using
      recordUpperSeedTailChunk287Step.certifies prior
  have h288 : recordUpperSeedTailChunk288State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix288 := by
    have prior : recordUpperSeedTailChunk288Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix287 := by
      simpa only [
        recordUpperSeedTailChunk288Before,
        recordUpperSeedTailChunk287State] using h287
    simpa only [recordUpperSeedTailPrefix288] using
      recordUpperSeedTailChunk288Step.certifies prior
  have h289 : recordUpperSeedTailChunk289State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix289 := by
    have prior : recordUpperSeedTailChunk289Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix288 := by
      simpa only [
        recordUpperSeedTailChunk289Before,
        recordUpperSeedTailChunk288State] using h288
    simpa only [recordUpperSeedTailPrefix289] using
      recordUpperSeedTailChunk289Step.certifies prior
  have h290 : recordUpperSeedTailChunk290State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix290 := by
    have prior : recordUpperSeedTailChunk290Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix289 := by
      simpa only [
        recordUpperSeedTailChunk290Before,
        recordUpperSeedTailChunk289State] using h289
    simpa only [recordUpperSeedTailPrefix290] using
      recordUpperSeedTailChunk290Step.certifies prior
  have h291 : recordUpperSeedTailChunk291State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix291 := by
    have prior : recordUpperSeedTailChunk291Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix290 := by
      simpa only [
        recordUpperSeedTailChunk291Before,
        recordUpperSeedTailChunk290State] using h290
    simpa only [recordUpperSeedTailPrefix291] using
      recordUpperSeedTailChunk291Step.certifies prior
  have h292 : recordUpperSeedTailChunk292State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix292 := by
    have prior : recordUpperSeedTailChunk292Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix291 := by
      simpa only [
        recordUpperSeedTailChunk292Before,
        recordUpperSeedTailChunk291State] using h291
    simpa only [recordUpperSeedTailPrefix292] using
      recordUpperSeedTailChunk292Step.certifies prior
  have h293 : recordUpperSeedTailChunk293State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix293 := by
    have prior : recordUpperSeedTailChunk293Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix292 := by
      simpa only [
        recordUpperSeedTailChunk293Before,
        recordUpperSeedTailChunk292State] using h292
    simpa only [recordUpperSeedTailPrefix293] using
      recordUpperSeedTailChunk293Step.certifies prior
  have h294 : recordUpperSeedTailChunk294State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix294 := by
    have prior : recordUpperSeedTailChunk294Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix293 := by
      simpa only [
        recordUpperSeedTailChunk294Before,
        recordUpperSeedTailChunk293State] using h293
    simpa only [recordUpperSeedTailPrefix294] using
      recordUpperSeedTailChunk294Step.certifies prior
  have h295 : recordUpperSeedTailChunk295State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix295 := by
    have prior : recordUpperSeedTailChunk295Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix294 := by
      simpa only [
        recordUpperSeedTailChunk295Before,
        recordUpperSeedTailChunk294State] using h294
    simpa only [recordUpperSeedTailPrefix295] using
      recordUpperSeedTailChunk295Step.certifies prior
  have h296 : recordUpperSeedTailChunk296State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix296 := by
    have prior : recordUpperSeedTailChunk296Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix295 := by
      simpa only [
        recordUpperSeedTailChunk296Before,
        recordUpperSeedTailChunk295State] using h295
    simpa only [recordUpperSeedTailPrefix296] using
      recordUpperSeedTailChunk296Step.certifies prior
  have h297 : recordUpperSeedTailChunk297State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix297 := by
    have prior : recordUpperSeedTailChunk297Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix296 := by
      simpa only [
        recordUpperSeedTailChunk297Before,
        recordUpperSeedTailChunk296State] using h296
    simpa only [recordUpperSeedTailPrefix297] using
      recordUpperSeedTailChunk297Step.certifies prior
  have h298 : recordUpperSeedTailChunk298State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix298 := by
    have prior : recordUpperSeedTailChunk298Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix297 := by
      simpa only [
        recordUpperSeedTailChunk298Before,
        recordUpperSeedTailChunk297State] using h297
    simpa only [recordUpperSeedTailPrefix298] using
      recordUpperSeedTailChunk298Step.certifies prior
  have h299 : recordUpperSeedTailChunk299State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix299 := by
    have prior : recordUpperSeedTailChunk299Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix298 := by
      simpa only [
        recordUpperSeedTailChunk299Before,
        recordUpperSeedTailChunk298State] using h298
    simpa only [recordUpperSeedTailPrefix299] using
      recordUpperSeedTailChunk299Step.certifies prior
  have h300 : recordUpperSeedTailChunk300State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix300 := by
    have prior : recordUpperSeedTailChunk300Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix299 := by
      simpa only [
        recordUpperSeedTailChunk300Before,
        recordUpperSeedTailChunk299State] using h299
    simpa only [recordUpperSeedTailPrefix300] using
      recordUpperSeedTailChunk300Step.certifies prior
  have h301 : recordUpperSeedTailChunk301State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix301 := by
    have prior : recordUpperSeedTailChunk301Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix300 := by
      simpa only [
        recordUpperSeedTailChunk301Before,
        recordUpperSeedTailChunk300State] using h300
    simpa only [recordUpperSeedTailPrefix301] using
      recordUpperSeedTailChunk301Step.certifies prior
  have h302 : recordUpperSeedTailChunk302State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix302 := by
    have prior : recordUpperSeedTailChunk302Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix301 := by
      simpa only [
        recordUpperSeedTailChunk302Before,
        recordUpperSeedTailChunk301State] using h301
    simpa only [recordUpperSeedTailPrefix302] using
      recordUpperSeedTailChunk302Step.certifies prior
  have h303 : recordUpperSeedTailChunk303State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix303 := by
    have prior : recordUpperSeedTailChunk303Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix302 := by
      simpa only [
        recordUpperSeedTailChunk303Before,
        recordUpperSeedTailChunk302State] using h302
    simpa only [recordUpperSeedTailPrefix303] using
      recordUpperSeedTailChunk303Step.certifies prior
  have h304 : recordUpperSeedTailChunk304State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix304 := by
    have prior : recordUpperSeedTailChunk304Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix303 := by
      simpa only [
        recordUpperSeedTailChunk304Before,
        recordUpperSeedTailChunk303State] using h303
    simpa only [recordUpperSeedTailPrefix304] using
      recordUpperSeedTailChunk304Step.certifies prior
  have h305 : recordUpperSeedTailChunk305State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix305 := by
    have prior : recordUpperSeedTailChunk305Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix304 := by
      simpa only [
        recordUpperSeedTailChunk305Before,
        recordUpperSeedTailChunk304State] using h304
    simpa only [recordUpperSeedTailPrefix305] using
      recordUpperSeedTailChunk305Step.certifies prior
  have h306 : recordUpperSeedTailChunk306State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix306 := by
    have prior : recordUpperSeedTailChunk306Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix305 := by
      simpa only [
        recordUpperSeedTailChunk306Before,
        recordUpperSeedTailChunk305State] using h305
    simpa only [recordUpperSeedTailPrefix306] using
      recordUpperSeedTailChunk306Step.certifies prior
  have h307 : recordUpperSeedTailChunk307State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix307 := by
    have prior : recordUpperSeedTailChunk307Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix306 := by
      simpa only [
        recordUpperSeedTailChunk307Before,
        recordUpperSeedTailChunk306State] using h306
    simpa only [recordUpperSeedTailPrefix307] using
      recordUpperSeedTailChunk307Step.certifies prior
  have h308 : recordUpperSeedTailChunk308State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix308 := by
    have prior : recordUpperSeedTailChunk308Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix307 := by
      simpa only [
        recordUpperSeedTailChunk308Before,
        recordUpperSeedTailChunk307State] using h307
    simpa only [recordUpperSeedTailPrefix308] using
      recordUpperSeedTailChunk308Step.certifies prior
  have h309 : recordUpperSeedTailChunk309State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix309 := by
    have prior : recordUpperSeedTailChunk309Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix308 := by
      simpa only [
        recordUpperSeedTailChunk309Before,
        recordUpperSeedTailChunk308State] using h308
    simpa only [recordUpperSeedTailPrefix309] using
      recordUpperSeedTailChunk309Step.certifies prior
  have h310 : recordUpperSeedTailChunk310State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix310 := by
    have prior : recordUpperSeedTailChunk310Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix309 := by
      simpa only [
        recordUpperSeedTailChunk310Before,
        recordUpperSeedTailChunk309State] using h309
    simpa only [recordUpperSeedTailPrefix310] using
      recordUpperSeedTailChunk310Step.certifies prior
  have h311 : recordUpperSeedTailChunk311State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix311 := by
    have prior : recordUpperSeedTailChunk311Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix310 := by
      simpa only [
        recordUpperSeedTailChunk311Before,
        recordUpperSeedTailChunk310State] using h310
    simpa only [recordUpperSeedTailPrefix311] using
      recordUpperSeedTailChunk311Step.certifies prior
  have h312 : recordUpperSeedTailChunk312State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix312 := by
    have prior : recordUpperSeedTailChunk312Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix311 := by
      simpa only [
        recordUpperSeedTailChunk312Before,
        recordUpperSeedTailChunk311State] using h311
    simpa only [recordUpperSeedTailPrefix312] using
      recordUpperSeedTailChunk312Step.certifies prior
  have h313 : recordUpperSeedTailChunk313State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix313 := by
    have prior : recordUpperSeedTailChunk313Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix312 := by
      simpa only [
        recordUpperSeedTailChunk313Before,
        recordUpperSeedTailChunk312State] using h312
    simpa only [recordUpperSeedTailPrefix313] using
      recordUpperSeedTailChunk313Step.certifies prior
  have h314 : recordUpperSeedTailChunk314State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix314 := by
    have prior : recordUpperSeedTailChunk314Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix313 := by
      simpa only [
        recordUpperSeedTailChunk314Before,
        recordUpperSeedTailChunk313State] using h313
    simpa only [recordUpperSeedTailPrefix314] using
      recordUpperSeedTailChunk314Step.certifies prior
  have h315 : recordUpperSeedTailChunk315State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix315 := by
    have prior : recordUpperSeedTailChunk315Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix314 := by
      simpa only [
        recordUpperSeedTailChunk315Before,
        recordUpperSeedTailChunk314State] using h314
    simpa only [recordUpperSeedTailPrefix315] using
      recordUpperSeedTailChunk315Step.certifies prior
  have h316 : recordUpperSeedTailChunk316State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix316 := by
    have prior : recordUpperSeedTailChunk316Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix315 := by
      simpa only [
        recordUpperSeedTailChunk316Before,
        recordUpperSeedTailChunk315State] using h315
    simpa only [recordUpperSeedTailPrefix316] using
      recordUpperSeedTailChunk316Step.certifies prior
  have h317 : recordUpperSeedTailChunk317State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix317 := by
    have prior : recordUpperSeedTailChunk317Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix316 := by
      simpa only [
        recordUpperSeedTailChunk317Before,
        recordUpperSeedTailChunk316State] using h316
    simpa only [recordUpperSeedTailPrefix317] using
      recordUpperSeedTailChunk317Step.certifies prior
  have h318 : recordUpperSeedTailChunk318State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix318 := by
    have prior : recordUpperSeedTailChunk318Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix317 := by
      simpa only [
        recordUpperSeedTailChunk318Before,
        recordUpperSeedTailChunk317State] using h317
    simpa only [recordUpperSeedTailPrefix318] using
      recordUpperSeedTailChunk318Step.certifies prior
  have h319 : recordUpperSeedTailChunk319State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix319 := by
    have prior : recordUpperSeedTailChunk319Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix318 := by
      simpa only [
        recordUpperSeedTailChunk319Before,
        recordUpperSeedTailChunk318State] using h318
    simpa only [recordUpperSeedTailPrefix319] using
      recordUpperSeedTailChunk319Step.certifies prior
  have h320 : recordUpperSeedTailChunk320State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix320 := by
    have prior : recordUpperSeedTailChunk320Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix319 := by
      simpa only [
        recordUpperSeedTailChunk320Before,
        recordUpperSeedTailChunk319State] using h319
    simpa only [recordUpperSeedTailPrefix320] using
      recordUpperSeedTailChunk320Step.certifies prior
  exact h320

end PrimeFactorUnimodality
