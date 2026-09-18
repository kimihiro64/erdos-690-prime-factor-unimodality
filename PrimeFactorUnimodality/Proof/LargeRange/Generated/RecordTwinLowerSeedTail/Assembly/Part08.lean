import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Assembly.Part07
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part281
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part282
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part283
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part284
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part285
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part286
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part287
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part288
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part289
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part290
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part291
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part292
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part293
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part294
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part295
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part296
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part297
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part298
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part299
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part300
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part301
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part302
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part303
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part304
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part305
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part306
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part307
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part308
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part309
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part310
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part311
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part312
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part313
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part314
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part315
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part316
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part317
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part318
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part319
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part320

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-lower-seed.json` (semantic SHA-256 `3ce105dad06099400dfd2e30c65d47c6e02828915452a8459553c3bb0eb78b73`, excluding elapsed time). Semantic tail assembly group 8. -/

namespace PrimeFactorUnimodality

theorem recordLowerSeedTailGroup08_semantic :
    recordLowerSeedTailChunk320State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix320 := by
  have h281 : recordLowerSeedTailChunk281State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix281 := by
    have prior : recordLowerSeedTailChunk281Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix280 := by
      simpa only [
        recordLowerSeedTailChunk281Before,
        recordLowerSeedTailChunk280State] using recordLowerSeedTailGroup07_semantic
    simpa only [recordLowerSeedTailPrefix281] using
      recordLowerSeedTailChunk281Step.certifies prior
  have h282 : recordLowerSeedTailChunk282State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix282 := by
    have prior : recordLowerSeedTailChunk282Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix281 := by
      simpa only [
        recordLowerSeedTailChunk282Before,
        recordLowerSeedTailChunk281State] using h281
    simpa only [recordLowerSeedTailPrefix282] using
      recordLowerSeedTailChunk282Step.certifies prior
  have h283 : recordLowerSeedTailChunk283State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix283 := by
    have prior : recordLowerSeedTailChunk283Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix282 := by
      simpa only [
        recordLowerSeedTailChunk283Before,
        recordLowerSeedTailChunk282State] using h282
    simpa only [recordLowerSeedTailPrefix283] using
      recordLowerSeedTailChunk283Step.certifies prior
  have h284 : recordLowerSeedTailChunk284State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix284 := by
    have prior : recordLowerSeedTailChunk284Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix283 := by
      simpa only [
        recordLowerSeedTailChunk284Before,
        recordLowerSeedTailChunk283State] using h283
    simpa only [recordLowerSeedTailPrefix284] using
      recordLowerSeedTailChunk284Step.certifies prior
  have h285 : recordLowerSeedTailChunk285State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix285 := by
    have prior : recordLowerSeedTailChunk285Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix284 := by
      simpa only [
        recordLowerSeedTailChunk285Before,
        recordLowerSeedTailChunk284State] using h284
    simpa only [recordLowerSeedTailPrefix285] using
      recordLowerSeedTailChunk285Step.certifies prior
  have h286 : recordLowerSeedTailChunk286State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix286 := by
    have prior : recordLowerSeedTailChunk286Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix285 := by
      simpa only [
        recordLowerSeedTailChunk286Before,
        recordLowerSeedTailChunk285State] using h285
    simpa only [recordLowerSeedTailPrefix286] using
      recordLowerSeedTailChunk286Step.certifies prior
  have h287 : recordLowerSeedTailChunk287State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix287 := by
    have prior : recordLowerSeedTailChunk287Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix286 := by
      simpa only [
        recordLowerSeedTailChunk287Before,
        recordLowerSeedTailChunk286State] using h286
    simpa only [recordLowerSeedTailPrefix287] using
      recordLowerSeedTailChunk287Step.certifies prior
  have h288 : recordLowerSeedTailChunk288State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix288 := by
    have prior : recordLowerSeedTailChunk288Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix287 := by
      simpa only [
        recordLowerSeedTailChunk288Before,
        recordLowerSeedTailChunk287State] using h287
    simpa only [recordLowerSeedTailPrefix288] using
      recordLowerSeedTailChunk288Step.certifies prior
  have h289 : recordLowerSeedTailChunk289State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix289 := by
    have prior : recordLowerSeedTailChunk289Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix288 := by
      simpa only [
        recordLowerSeedTailChunk289Before,
        recordLowerSeedTailChunk288State] using h288
    simpa only [recordLowerSeedTailPrefix289] using
      recordLowerSeedTailChunk289Step.certifies prior
  have h290 : recordLowerSeedTailChunk290State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix290 := by
    have prior : recordLowerSeedTailChunk290Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix289 := by
      simpa only [
        recordLowerSeedTailChunk290Before,
        recordLowerSeedTailChunk289State] using h289
    simpa only [recordLowerSeedTailPrefix290] using
      recordLowerSeedTailChunk290Step.certifies prior
  have h291 : recordLowerSeedTailChunk291State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix291 := by
    have prior : recordLowerSeedTailChunk291Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix290 := by
      simpa only [
        recordLowerSeedTailChunk291Before,
        recordLowerSeedTailChunk290State] using h290
    simpa only [recordLowerSeedTailPrefix291] using
      recordLowerSeedTailChunk291Step.certifies prior
  have h292 : recordLowerSeedTailChunk292State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix292 := by
    have prior : recordLowerSeedTailChunk292Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix291 := by
      simpa only [
        recordLowerSeedTailChunk292Before,
        recordLowerSeedTailChunk291State] using h291
    simpa only [recordLowerSeedTailPrefix292] using
      recordLowerSeedTailChunk292Step.certifies prior
  have h293 : recordLowerSeedTailChunk293State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix293 := by
    have prior : recordLowerSeedTailChunk293Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix292 := by
      simpa only [
        recordLowerSeedTailChunk293Before,
        recordLowerSeedTailChunk292State] using h292
    simpa only [recordLowerSeedTailPrefix293] using
      recordLowerSeedTailChunk293Step.certifies prior
  have h294 : recordLowerSeedTailChunk294State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix294 := by
    have prior : recordLowerSeedTailChunk294Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix293 := by
      simpa only [
        recordLowerSeedTailChunk294Before,
        recordLowerSeedTailChunk293State] using h293
    simpa only [recordLowerSeedTailPrefix294] using
      recordLowerSeedTailChunk294Step.certifies prior
  have h295 : recordLowerSeedTailChunk295State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix295 := by
    have prior : recordLowerSeedTailChunk295Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix294 := by
      simpa only [
        recordLowerSeedTailChunk295Before,
        recordLowerSeedTailChunk294State] using h294
    simpa only [recordLowerSeedTailPrefix295] using
      recordLowerSeedTailChunk295Step.certifies prior
  have h296 : recordLowerSeedTailChunk296State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix296 := by
    have prior : recordLowerSeedTailChunk296Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix295 := by
      simpa only [
        recordLowerSeedTailChunk296Before,
        recordLowerSeedTailChunk295State] using h295
    simpa only [recordLowerSeedTailPrefix296] using
      recordLowerSeedTailChunk296Step.certifies prior
  have h297 : recordLowerSeedTailChunk297State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix297 := by
    have prior : recordLowerSeedTailChunk297Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix296 := by
      simpa only [
        recordLowerSeedTailChunk297Before,
        recordLowerSeedTailChunk296State] using h296
    simpa only [recordLowerSeedTailPrefix297] using
      recordLowerSeedTailChunk297Step.certifies prior
  have h298 : recordLowerSeedTailChunk298State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix298 := by
    have prior : recordLowerSeedTailChunk298Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix297 := by
      simpa only [
        recordLowerSeedTailChunk298Before,
        recordLowerSeedTailChunk297State] using h297
    simpa only [recordLowerSeedTailPrefix298] using
      recordLowerSeedTailChunk298Step.certifies prior
  have h299 : recordLowerSeedTailChunk299State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix299 := by
    have prior : recordLowerSeedTailChunk299Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix298 := by
      simpa only [
        recordLowerSeedTailChunk299Before,
        recordLowerSeedTailChunk298State] using h298
    simpa only [recordLowerSeedTailPrefix299] using
      recordLowerSeedTailChunk299Step.certifies prior
  have h300 : recordLowerSeedTailChunk300State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix300 := by
    have prior : recordLowerSeedTailChunk300Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix299 := by
      simpa only [
        recordLowerSeedTailChunk300Before,
        recordLowerSeedTailChunk299State] using h299
    simpa only [recordLowerSeedTailPrefix300] using
      recordLowerSeedTailChunk300Step.certifies prior
  have h301 : recordLowerSeedTailChunk301State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix301 := by
    have prior : recordLowerSeedTailChunk301Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix300 := by
      simpa only [
        recordLowerSeedTailChunk301Before,
        recordLowerSeedTailChunk300State] using h300
    simpa only [recordLowerSeedTailPrefix301] using
      recordLowerSeedTailChunk301Step.certifies prior
  have h302 : recordLowerSeedTailChunk302State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix302 := by
    have prior : recordLowerSeedTailChunk302Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix301 := by
      simpa only [
        recordLowerSeedTailChunk302Before,
        recordLowerSeedTailChunk301State] using h301
    simpa only [recordLowerSeedTailPrefix302] using
      recordLowerSeedTailChunk302Step.certifies prior
  have h303 : recordLowerSeedTailChunk303State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix303 := by
    have prior : recordLowerSeedTailChunk303Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix302 := by
      simpa only [
        recordLowerSeedTailChunk303Before,
        recordLowerSeedTailChunk302State] using h302
    simpa only [recordLowerSeedTailPrefix303] using
      recordLowerSeedTailChunk303Step.certifies prior
  have h304 : recordLowerSeedTailChunk304State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix304 := by
    have prior : recordLowerSeedTailChunk304Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix303 := by
      simpa only [
        recordLowerSeedTailChunk304Before,
        recordLowerSeedTailChunk303State] using h303
    simpa only [recordLowerSeedTailPrefix304] using
      recordLowerSeedTailChunk304Step.certifies prior
  have h305 : recordLowerSeedTailChunk305State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix305 := by
    have prior : recordLowerSeedTailChunk305Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix304 := by
      simpa only [
        recordLowerSeedTailChunk305Before,
        recordLowerSeedTailChunk304State] using h304
    simpa only [recordLowerSeedTailPrefix305] using
      recordLowerSeedTailChunk305Step.certifies prior
  have h306 : recordLowerSeedTailChunk306State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix306 := by
    have prior : recordLowerSeedTailChunk306Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix305 := by
      simpa only [
        recordLowerSeedTailChunk306Before,
        recordLowerSeedTailChunk305State] using h305
    simpa only [recordLowerSeedTailPrefix306] using
      recordLowerSeedTailChunk306Step.certifies prior
  have h307 : recordLowerSeedTailChunk307State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix307 := by
    have prior : recordLowerSeedTailChunk307Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix306 := by
      simpa only [
        recordLowerSeedTailChunk307Before,
        recordLowerSeedTailChunk306State] using h306
    simpa only [recordLowerSeedTailPrefix307] using
      recordLowerSeedTailChunk307Step.certifies prior
  have h308 : recordLowerSeedTailChunk308State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix308 := by
    have prior : recordLowerSeedTailChunk308Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix307 := by
      simpa only [
        recordLowerSeedTailChunk308Before,
        recordLowerSeedTailChunk307State] using h307
    simpa only [recordLowerSeedTailPrefix308] using
      recordLowerSeedTailChunk308Step.certifies prior
  have h309 : recordLowerSeedTailChunk309State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix309 := by
    have prior : recordLowerSeedTailChunk309Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix308 := by
      simpa only [
        recordLowerSeedTailChunk309Before,
        recordLowerSeedTailChunk308State] using h308
    simpa only [recordLowerSeedTailPrefix309] using
      recordLowerSeedTailChunk309Step.certifies prior
  have h310 : recordLowerSeedTailChunk310State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix310 := by
    have prior : recordLowerSeedTailChunk310Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix309 := by
      simpa only [
        recordLowerSeedTailChunk310Before,
        recordLowerSeedTailChunk309State] using h309
    simpa only [recordLowerSeedTailPrefix310] using
      recordLowerSeedTailChunk310Step.certifies prior
  have h311 : recordLowerSeedTailChunk311State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix311 := by
    have prior : recordLowerSeedTailChunk311Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix310 := by
      simpa only [
        recordLowerSeedTailChunk311Before,
        recordLowerSeedTailChunk310State] using h310
    simpa only [recordLowerSeedTailPrefix311] using
      recordLowerSeedTailChunk311Step.certifies prior
  have h312 : recordLowerSeedTailChunk312State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix312 := by
    have prior : recordLowerSeedTailChunk312Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix311 := by
      simpa only [
        recordLowerSeedTailChunk312Before,
        recordLowerSeedTailChunk311State] using h311
    simpa only [recordLowerSeedTailPrefix312] using
      recordLowerSeedTailChunk312Step.certifies prior
  have h313 : recordLowerSeedTailChunk313State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix313 := by
    have prior : recordLowerSeedTailChunk313Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix312 := by
      simpa only [
        recordLowerSeedTailChunk313Before,
        recordLowerSeedTailChunk312State] using h312
    simpa only [recordLowerSeedTailPrefix313] using
      recordLowerSeedTailChunk313Step.certifies prior
  have h314 : recordLowerSeedTailChunk314State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix314 := by
    have prior : recordLowerSeedTailChunk314Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix313 := by
      simpa only [
        recordLowerSeedTailChunk314Before,
        recordLowerSeedTailChunk313State] using h313
    simpa only [recordLowerSeedTailPrefix314] using
      recordLowerSeedTailChunk314Step.certifies prior
  have h315 : recordLowerSeedTailChunk315State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix315 := by
    have prior : recordLowerSeedTailChunk315Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix314 := by
      simpa only [
        recordLowerSeedTailChunk315Before,
        recordLowerSeedTailChunk314State] using h314
    simpa only [recordLowerSeedTailPrefix315] using
      recordLowerSeedTailChunk315Step.certifies prior
  have h316 : recordLowerSeedTailChunk316State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix316 := by
    have prior : recordLowerSeedTailChunk316Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix315 := by
      simpa only [
        recordLowerSeedTailChunk316Before,
        recordLowerSeedTailChunk315State] using h315
    simpa only [recordLowerSeedTailPrefix316] using
      recordLowerSeedTailChunk316Step.certifies prior
  have h317 : recordLowerSeedTailChunk317State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix317 := by
    have prior : recordLowerSeedTailChunk317Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix316 := by
      simpa only [
        recordLowerSeedTailChunk317Before,
        recordLowerSeedTailChunk316State] using h316
    simpa only [recordLowerSeedTailPrefix317] using
      recordLowerSeedTailChunk317Step.certifies prior
  have h318 : recordLowerSeedTailChunk318State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix318 := by
    have prior : recordLowerSeedTailChunk318Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix317 := by
      simpa only [
        recordLowerSeedTailChunk318Before,
        recordLowerSeedTailChunk317State] using h317
    simpa only [recordLowerSeedTailPrefix318] using
      recordLowerSeedTailChunk318Step.certifies prior
  have h319 : recordLowerSeedTailChunk319State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix319 := by
    have prior : recordLowerSeedTailChunk319Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix318 := by
      simpa only [
        recordLowerSeedTailChunk319Before,
        recordLowerSeedTailChunk318State] using h318
    simpa only [recordLowerSeedTailPrefix319] using
      recordLowerSeedTailChunk319Step.certifies prior
  have h320 : recordLowerSeedTailChunk320State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix320 := by
    have prior : recordLowerSeedTailChunk320Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix319 := by
      simpa only [
        recordLowerSeedTailChunk320Before,
        recordLowerSeedTailChunk319State] using h319
    simpa only [recordLowerSeedTailPrefix320] using
      recordLowerSeedTailChunk320Step.certifies prior
  exact h320

end PrimeFactorUnimodality
