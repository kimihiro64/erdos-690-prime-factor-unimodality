import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Assembly.Part09
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part361
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part362
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part363
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part364
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part365
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part366
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part367
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part368
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part369
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part370
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part371
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part372
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part373
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part374
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part375
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part376
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part377
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part378
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part379
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part380
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part381
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part382
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part383
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part384
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part385
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part386
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part387
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part388
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part389
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part390
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part391
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part392
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part393
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part394
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part395
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part396
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part397
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part398
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part399
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part400

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-lower-seed.json` (semantic SHA-256 `3ce105dad06099400dfd2e30c65d47c6e02828915452a8459553c3bb0eb78b73`, excluding elapsed time). Semantic tail assembly group 10. -/

namespace PrimeFactorUnimodality

theorem recordLowerSeedTailGroup10_semantic :
    recordLowerSeedTailChunk400State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix400 := by
  have h361 : recordLowerSeedTailChunk361State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix361 := by
    have prior : recordLowerSeedTailChunk361Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix360 := by
      simpa only [
        recordLowerSeedTailChunk361Before,
        recordLowerSeedTailChunk360State] using recordLowerSeedTailGroup09_semantic
    simpa only [recordLowerSeedTailPrefix361] using
      recordLowerSeedTailChunk361Step.certifies prior
  have h362 : recordLowerSeedTailChunk362State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix362 := by
    have prior : recordLowerSeedTailChunk362Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix361 := by
      simpa only [
        recordLowerSeedTailChunk362Before,
        recordLowerSeedTailChunk361State] using h361
    simpa only [recordLowerSeedTailPrefix362] using
      recordLowerSeedTailChunk362Step.certifies prior
  have h363 : recordLowerSeedTailChunk363State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix363 := by
    have prior : recordLowerSeedTailChunk363Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix362 := by
      simpa only [
        recordLowerSeedTailChunk363Before,
        recordLowerSeedTailChunk362State] using h362
    simpa only [recordLowerSeedTailPrefix363] using
      recordLowerSeedTailChunk363Step.certifies prior
  have h364 : recordLowerSeedTailChunk364State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix364 := by
    have prior : recordLowerSeedTailChunk364Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix363 := by
      simpa only [
        recordLowerSeedTailChunk364Before,
        recordLowerSeedTailChunk363State] using h363
    simpa only [recordLowerSeedTailPrefix364] using
      recordLowerSeedTailChunk364Step.certifies prior
  have h365 : recordLowerSeedTailChunk365State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix365 := by
    have prior : recordLowerSeedTailChunk365Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix364 := by
      simpa only [
        recordLowerSeedTailChunk365Before,
        recordLowerSeedTailChunk364State] using h364
    simpa only [recordLowerSeedTailPrefix365] using
      recordLowerSeedTailChunk365Step.certifies prior
  have h366 : recordLowerSeedTailChunk366State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix366 := by
    have prior : recordLowerSeedTailChunk366Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix365 := by
      simpa only [
        recordLowerSeedTailChunk366Before,
        recordLowerSeedTailChunk365State] using h365
    simpa only [recordLowerSeedTailPrefix366] using
      recordLowerSeedTailChunk366Step.certifies prior
  have h367 : recordLowerSeedTailChunk367State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix367 := by
    have prior : recordLowerSeedTailChunk367Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix366 := by
      simpa only [
        recordLowerSeedTailChunk367Before,
        recordLowerSeedTailChunk366State] using h366
    simpa only [recordLowerSeedTailPrefix367] using
      recordLowerSeedTailChunk367Step.certifies prior
  have h368 : recordLowerSeedTailChunk368State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix368 := by
    have prior : recordLowerSeedTailChunk368Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix367 := by
      simpa only [
        recordLowerSeedTailChunk368Before,
        recordLowerSeedTailChunk367State] using h367
    simpa only [recordLowerSeedTailPrefix368] using
      recordLowerSeedTailChunk368Step.certifies prior
  have h369 : recordLowerSeedTailChunk369State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix369 := by
    have prior : recordLowerSeedTailChunk369Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix368 := by
      simpa only [
        recordLowerSeedTailChunk369Before,
        recordLowerSeedTailChunk368State] using h368
    simpa only [recordLowerSeedTailPrefix369] using
      recordLowerSeedTailChunk369Step.certifies prior
  have h370 : recordLowerSeedTailChunk370State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix370 := by
    have prior : recordLowerSeedTailChunk370Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix369 := by
      simpa only [
        recordLowerSeedTailChunk370Before,
        recordLowerSeedTailChunk369State] using h369
    simpa only [recordLowerSeedTailPrefix370] using
      recordLowerSeedTailChunk370Step.certifies prior
  have h371 : recordLowerSeedTailChunk371State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix371 := by
    have prior : recordLowerSeedTailChunk371Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix370 := by
      simpa only [
        recordLowerSeedTailChunk371Before,
        recordLowerSeedTailChunk370State] using h370
    simpa only [recordLowerSeedTailPrefix371] using
      recordLowerSeedTailChunk371Step.certifies prior
  have h372 : recordLowerSeedTailChunk372State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix372 := by
    have prior : recordLowerSeedTailChunk372Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix371 := by
      simpa only [
        recordLowerSeedTailChunk372Before,
        recordLowerSeedTailChunk371State] using h371
    simpa only [recordLowerSeedTailPrefix372] using
      recordLowerSeedTailChunk372Step.certifies prior
  have h373 : recordLowerSeedTailChunk373State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix373 := by
    have prior : recordLowerSeedTailChunk373Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix372 := by
      simpa only [
        recordLowerSeedTailChunk373Before,
        recordLowerSeedTailChunk372State] using h372
    simpa only [recordLowerSeedTailPrefix373] using
      recordLowerSeedTailChunk373Step.certifies prior
  have h374 : recordLowerSeedTailChunk374State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix374 := by
    have prior : recordLowerSeedTailChunk374Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix373 := by
      simpa only [
        recordLowerSeedTailChunk374Before,
        recordLowerSeedTailChunk373State] using h373
    simpa only [recordLowerSeedTailPrefix374] using
      recordLowerSeedTailChunk374Step.certifies prior
  have h375 : recordLowerSeedTailChunk375State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix375 := by
    have prior : recordLowerSeedTailChunk375Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix374 := by
      simpa only [
        recordLowerSeedTailChunk375Before,
        recordLowerSeedTailChunk374State] using h374
    simpa only [recordLowerSeedTailPrefix375] using
      recordLowerSeedTailChunk375Step.certifies prior
  have h376 : recordLowerSeedTailChunk376State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix376 := by
    have prior : recordLowerSeedTailChunk376Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix375 := by
      simpa only [
        recordLowerSeedTailChunk376Before,
        recordLowerSeedTailChunk375State] using h375
    simpa only [recordLowerSeedTailPrefix376] using
      recordLowerSeedTailChunk376Step.certifies prior
  have h377 : recordLowerSeedTailChunk377State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix377 := by
    have prior : recordLowerSeedTailChunk377Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix376 := by
      simpa only [
        recordLowerSeedTailChunk377Before,
        recordLowerSeedTailChunk376State] using h376
    simpa only [recordLowerSeedTailPrefix377] using
      recordLowerSeedTailChunk377Step.certifies prior
  have h378 : recordLowerSeedTailChunk378State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix378 := by
    have prior : recordLowerSeedTailChunk378Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix377 := by
      simpa only [
        recordLowerSeedTailChunk378Before,
        recordLowerSeedTailChunk377State] using h377
    simpa only [recordLowerSeedTailPrefix378] using
      recordLowerSeedTailChunk378Step.certifies prior
  have h379 : recordLowerSeedTailChunk379State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix379 := by
    have prior : recordLowerSeedTailChunk379Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix378 := by
      simpa only [
        recordLowerSeedTailChunk379Before,
        recordLowerSeedTailChunk378State] using h378
    simpa only [recordLowerSeedTailPrefix379] using
      recordLowerSeedTailChunk379Step.certifies prior
  have h380 : recordLowerSeedTailChunk380State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix380 := by
    have prior : recordLowerSeedTailChunk380Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix379 := by
      simpa only [
        recordLowerSeedTailChunk380Before,
        recordLowerSeedTailChunk379State] using h379
    simpa only [recordLowerSeedTailPrefix380] using
      recordLowerSeedTailChunk380Step.certifies prior
  have h381 : recordLowerSeedTailChunk381State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix381 := by
    have prior : recordLowerSeedTailChunk381Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix380 := by
      simpa only [
        recordLowerSeedTailChunk381Before,
        recordLowerSeedTailChunk380State] using h380
    simpa only [recordLowerSeedTailPrefix381] using
      recordLowerSeedTailChunk381Step.certifies prior
  have h382 : recordLowerSeedTailChunk382State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix382 := by
    have prior : recordLowerSeedTailChunk382Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix381 := by
      simpa only [
        recordLowerSeedTailChunk382Before,
        recordLowerSeedTailChunk381State] using h381
    simpa only [recordLowerSeedTailPrefix382] using
      recordLowerSeedTailChunk382Step.certifies prior
  have h383 : recordLowerSeedTailChunk383State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix383 := by
    have prior : recordLowerSeedTailChunk383Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix382 := by
      simpa only [
        recordLowerSeedTailChunk383Before,
        recordLowerSeedTailChunk382State] using h382
    simpa only [recordLowerSeedTailPrefix383] using
      recordLowerSeedTailChunk383Step.certifies prior
  have h384 : recordLowerSeedTailChunk384State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix384 := by
    have prior : recordLowerSeedTailChunk384Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix383 := by
      simpa only [
        recordLowerSeedTailChunk384Before,
        recordLowerSeedTailChunk383State] using h383
    simpa only [recordLowerSeedTailPrefix384] using
      recordLowerSeedTailChunk384Step.certifies prior
  have h385 : recordLowerSeedTailChunk385State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix385 := by
    have prior : recordLowerSeedTailChunk385Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix384 := by
      simpa only [
        recordLowerSeedTailChunk385Before,
        recordLowerSeedTailChunk384State] using h384
    simpa only [recordLowerSeedTailPrefix385] using
      recordLowerSeedTailChunk385Step.certifies prior
  have h386 : recordLowerSeedTailChunk386State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix386 := by
    have prior : recordLowerSeedTailChunk386Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix385 := by
      simpa only [
        recordLowerSeedTailChunk386Before,
        recordLowerSeedTailChunk385State] using h385
    simpa only [recordLowerSeedTailPrefix386] using
      recordLowerSeedTailChunk386Step.certifies prior
  have h387 : recordLowerSeedTailChunk387State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix387 := by
    have prior : recordLowerSeedTailChunk387Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix386 := by
      simpa only [
        recordLowerSeedTailChunk387Before,
        recordLowerSeedTailChunk386State] using h386
    simpa only [recordLowerSeedTailPrefix387] using
      recordLowerSeedTailChunk387Step.certifies prior
  have h388 : recordLowerSeedTailChunk388State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix388 := by
    have prior : recordLowerSeedTailChunk388Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix387 := by
      simpa only [
        recordLowerSeedTailChunk388Before,
        recordLowerSeedTailChunk387State] using h387
    simpa only [recordLowerSeedTailPrefix388] using
      recordLowerSeedTailChunk388Step.certifies prior
  have h389 : recordLowerSeedTailChunk389State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix389 := by
    have prior : recordLowerSeedTailChunk389Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix388 := by
      simpa only [
        recordLowerSeedTailChunk389Before,
        recordLowerSeedTailChunk388State] using h388
    simpa only [recordLowerSeedTailPrefix389] using
      recordLowerSeedTailChunk389Step.certifies prior
  have h390 : recordLowerSeedTailChunk390State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix390 := by
    have prior : recordLowerSeedTailChunk390Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix389 := by
      simpa only [
        recordLowerSeedTailChunk390Before,
        recordLowerSeedTailChunk389State] using h389
    simpa only [recordLowerSeedTailPrefix390] using
      recordLowerSeedTailChunk390Step.certifies prior
  have h391 : recordLowerSeedTailChunk391State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix391 := by
    have prior : recordLowerSeedTailChunk391Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix390 := by
      simpa only [
        recordLowerSeedTailChunk391Before,
        recordLowerSeedTailChunk390State] using h390
    simpa only [recordLowerSeedTailPrefix391] using
      recordLowerSeedTailChunk391Step.certifies prior
  have h392 : recordLowerSeedTailChunk392State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix392 := by
    have prior : recordLowerSeedTailChunk392Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix391 := by
      simpa only [
        recordLowerSeedTailChunk392Before,
        recordLowerSeedTailChunk391State] using h391
    simpa only [recordLowerSeedTailPrefix392] using
      recordLowerSeedTailChunk392Step.certifies prior
  have h393 : recordLowerSeedTailChunk393State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix393 := by
    have prior : recordLowerSeedTailChunk393Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix392 := by
      simpa only [
        recordLowerSeedTailChunk393Before,
        recordLowerSeedTailChunk392State] using h392
    simpa only [recordLowerSeedTailPrefix393] using
      recordLowerSeedTailChunk393Step.certifies prior
  have h394 : recordLowerSeedTailChunk394State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix394 := by
    have prior : recordLowerSeedTailChunk394Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix393 := by
      simpa only [
        recordLowerSeedTailChunk394Before,
        recordLowerSeedTailChunk393State] using h393
    simpa only [recordLowerSeedTailPrefix394] using
      recordLowerSeedTailChunk394Step.certifies prior
  have h395 : recordLowerSeedTailChunk395State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix395 := by
    have prior : recordLowerSeedTailChunk395Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix394 := by
      simpa only [
        recordLowerSeedTailChunk395Before,
        recordLowerSeedTailChunk394State] using h394
    simpa only [recordLowerSeedTailPrefix395] using
      recordLowerSeedTailChunk395Step.certifies prior
  have h396 : recordLowerSeedTailChunk396State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix396 := by
    have prior : recordLowerSeedTailChunk396Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix395 := by
      simpa only [
        recordLowerSeedTailChunk396Before,
        recordLowerSeedTailChunk395State] using h395
    simpa only [recordLowerSeedTailPrefix396] using
      recordLowerSeedTailChunk396Step.certifies prior
  have h397 : recordLowerSeedTailChunk397State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix397 := by
    have prior : recordLowerSeedTailChunk397Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix396 := by
      simpa only [
        recordLowerSeedTailChunk397Before,
        recordLowerSeedTailChunk396State] using h396
    simpa only [recordLowerSeedTailPrefix397] using
      recordLowerSeedTailChunk397Step.certifies prior
  have h398 : recordLowerSeedTailChunk398State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix398 := by
    have prior : recordLowerSeedTailChunk398Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix397 := by
      simpa only [
        recordLowerSeedTailChunk398Before,
        recordLowerSeedTailChunk397State] using h397
    simpa only [recordLowerSeedTailPrefix398] using
      recordLowerSeedTailChunk398Step.certifies prior
  have h399 : recordLowerSeedTailChunk399State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix399 := by
    have prior : recordLowerSeedTailChunk399Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix398 := by
      simpa only [
        recordLowerSeedTailChunk399Before,
        recordLowerSeedTailChunk398State] using h398
    simpa only [recordLowerSeedTailPrefix399] using
      recordLowerSeedTailChunk399Step.certifies prior
  have h400 : recordLowerSeedTailChunk400State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix400 := by
    have prior : recordLowerSeedTailChunk400Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix399 := by
      simpa only [
        recordLowerSeedTailChunk400Before,
        recordLowerSeedTailChunk399State] using h399
    simpa only [recordLowerSeedTailPrefix400] using
      recordLowerSeedTailChunk400Step.certifies prior
  exact h400

end PrimeFactorUnimodality
