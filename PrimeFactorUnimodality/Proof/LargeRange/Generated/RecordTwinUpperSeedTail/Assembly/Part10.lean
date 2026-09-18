import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Assembly.Part09
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part361
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part362
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part363
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part364
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part365
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part366
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part367
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part368
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part369
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part370
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part371
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part372
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part373
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part374
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part375
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part376
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part377
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part378
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part379
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part380
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part381
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part382
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part383
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part384
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part385
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part386
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part387
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part388
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part389
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part390
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part391
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part392
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part393
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part394
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part395
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part396
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part397
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part398
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part399
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part400

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-upper-seed-base11.json` (semantic SHA-256 `493791f7b41de1500c4b830f254f9f92fd9c5d50d639b62aa2b46ca48591321f`, excluding elapsed time). Semantic tail assembly group 10. -/

namespace PrimeFactorUnimodality

theorem recordUpperSeedTailGroup10_semantic :
    recordUpperSeedTailChunk400State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix400 := by
  have h361 : recordUpperSeedTailChunk361State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix361 := by
    have prior : recordUpperSeedTailChunk361Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix360 := by
      simpa only [
        recordUpperSeedTailChunk361Before,
        recordUpperSeedTailChunk360State] using recordUpperSeedTailGroup09_semantic
    simpa only [recordUpperSeedTailPrefix361] using
      recordUpperSeedTailChunk361Step.certifies prior
  have h362 : recordUpperSeedTailChunk362State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix362 := by
    have prior : recordUpperSeedTailChunk362Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix361 := by
      simpa only [
        recordUpperSeedTailChunk362Before,
        recordUpperSeedTailChunk361State] using h361
    simpa only [recordUpperSeedTailPrefix362] using
      recordUpperSeedTailChunk362Step.certifies prior
  have h363 : recordUpperSeedTailChunk363State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix363 := by
    have prior : recordUpperSeedTailChunk363Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix362 := by
      simpa only [
        recordUpperSeedTailChunk363Before,
        recordUpperSeedTailChunk362State] using h362
    simpa only [recordUpperSeedTailPrefix363] using
      recordUpperSeedTailChunk363Step.certifies prior
  have h364 : recordUpperSeedTailChunk364State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix364 := by
    have prior : recordUpperSeedTailChunk364Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix363 := by
      simpa only [
        recordUpperSeedTailChunk364Before,
        recordUpperSeedTailChunk363State] using h363
    simpa only [recordUpperSeedTailPrefix364] using
      recordUpperSeedTailChunk364Step.certifies prior
  have h365 : recordUpperSeedTailChunk365State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix365 := by
    have prior : recordUpperSeedTailChunk365Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix364 := by
      simpa only [
        recordUpperSeedTailChunk365Before,
        recordUpperSeedTailChunk364State] using h364
    simpa only [recordUpperSeedTailPrefix365] using
      recordUpperSeedTailChunk365Step.certifies prior
  have h366 : recordUpperSeedTailChunk366State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix366 := by
    have prior : recordUpperSeedTailChunk366Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix365 := by
      simpa only [
        recordUpperSeedTailChunk366Before,
        recordUpperSeedTailChunk365State] using h365
    simpa only [recordUpperSeedTailPrefix366] using
      recordUpperSeedTailChunk366Step.certifies prior
  have h367 : recordUpperSeedTailChunk367State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix367 := by
    have prior : recordUpperSeedTailChunk367Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix366 := by
      simpa only [
        recordUpperSeedTailChunk367Before,
        recordUpperSeedTailChunk366State] using h366
    simpa only [recordUpperSeedTailPrefix367] using
      recordUpperSeedTailChunk367Step.certifies prior
  have h368 : recordUpperSeedTailChunk368State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix368 := by
    have prior : recordUpperSeedTailChunk368Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix367 := by
      simpa only [
        recordUpperSeedTailChunk368Before,
        recordUpperSeedTailChunk367State] using h367
    simpa only [recordUpperSeedTailPrefix368] using
      recordUpperSeedTailChunk368Step.certifies prior
  have h369 : recordUpperSeedTailChunk369State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix369 := by
    have prior : recordUpperSeedTailChunk369Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix368 := by
      simpa only [
        recordUpperSeedTailChunk369Before,
        recordUpperSeedTailChunk368State] using h368
    simpa only [recordUpperSeedTailPrefix369] using
      recordUpperSeedTailChunk369Step.certifies prior
  have h370 : recordUpperSeedTailChunk370State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix370 := by
    have prior : recordUpperSeedTailChunk370Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix369 := by
      simpa only [
        recordUpperSeedTailChunk370Before,
        recordUpperSeedTailChunk369State] using h369
    simpa only [recordUpperSeedTailPrefix370] using
      recordUpperSeedTailChunk370Step.certifies prior
  have h371 : recordUpperSeedTailChunk371State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix371 := by
    have prior : recordUpperSeedTailChunk371Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix370 := by
      simpa only [
        recordUpperSeedTailChunk371Before,
        recordUpperSeedTailChunk370State] using h370
    simpa only [recordUpperSeedTailPrefix371] using
      recordUpperSeedTailChunk371Step.certifies prior
  have h372 : recordUpperSeedTailChunk372State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix372 := by
    have prior : recordUpperSeedTailChunk372Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix371 := by
      simpa only [
        recordUpperSeedTailChunk372Before,
        recordUpperSeedTailChunk371State] using h371
    simpa only [recordUpperSeedTailPrefix372] using
      recordUpperSeedTailChunk372Step.certifies prior
  have h373 : recordUpperSeedTailChunk373State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix373 := by
    have prior : recordUpperSeedTailChunk373Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix372 := by
      simpa only [
        recordUpperSeedTailChunk373Before,
        recordUpperSeedTailChunk372State] using h372
    simpa only [recordUpperSeedTailPrefix373] using
      recordUpperSeedTailChunk373Step.certifies prior
  have h374 : recordUpperSeedTailChunk374State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix374 := by
    have prior : recordUpperSeedTailChunk374Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix373 := by
      simpa only [
        recordUpperSeedTailChunk374Before,
        recordUpperSeedTailChunk373State] using h373
    simpa only [recordUpperSeedTailPrefix374] using
      recordUpperSeedTailChunk374Step.certifies prior
  have h375 : recordUpperSeedTailChunk375State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix375 := by
    have prior : recordUpperSeedTailChunk375Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix374 := by
      simpa only [
        recordUpperSeedTailChunk375Before,
        recordUpperSeedTailChunk374State] using h374
    simpa only [recordUpperSeedTailPrefix375] using
      recordUpperSeedTailChunk375Step.certifies prior
  have h376 : recordUpperSeedTailChunk376State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix376 := by
    have prior : recordUpperSeedTailChunk376Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix375 := by
      simpa only [
        recordUpperSeedTailChunk376Before,
        recordUpperSeedTailChunk375State] using h375
    simpa only [recordUpperSeedTailPrefix376] using
      recordUpperSeedTailChunk376Step.certifies prior
  have h377 : recordUpperSeedTailChunk377State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix377 := by
    have prior : recordUpperSeedTailChunk377Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix376 := by
      simpa only [
        recordUpperSeedTailChunk377Before,
        recordUpperSeedTailChunk376State] using h376
    simpa only [recordUpperSeedTailPrefix377] using
      recordUpperSeedTailChunk377Step.certifies prior
  have h378 : recordUpperSeedTailChunk378State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix378 := by
    have prior : recordUpperSeedTailChunk378Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix377 := by
      simpa only [
        recordUpperSeedTailChunk378Before,
        recordUpperSeedTailChunk377State] using h377
    simpa only [recordUpperSeedTailPrefix378] using
      recordUpperSeedTailChunk378Step.certifies prior
  have h379 : recordUpperSeedTailChunk379State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix379 := by
    have prior : recordUpperSeedTailChunk379Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix378 := by
      simpa only [
        recordUpperSeedTailChunk379Before,
        recordUpperSeedTailChunk378State] using h378
    simpa only [recordUpperSeedTailPrefix379] using
      recordUpperSeedTailChunk379Step.certifies prior
  have h380 : recordUpperSeedTailChunk380State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix380 := by
    have prior : recordUpperSeedTailChunk380Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix379 := by
      simpa only [
        recordUpperSeedTailChunk380Before,
        recordUpperSeedTailChunk379State] using h379
    simpa only [recordUpperSeedTailPrefix380] using
      recordUpperSeedTailChunk380Step.certifies prior
  have h381 : recordUpperSeedTailChunk381State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix381 := by
    have prior : recordUpperSeedTailChunk381Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix380 := by
      simpa only [
        recordUpperSeedTailChunk381Before,
        recordUpperSeedTailChunk380State] using h380
    simpa only [recordUpperSeedTailPrefix381] using
      recordUpperSeedTailChunk381Step.certifies prior
  have h382 : recordUpperSeedTailChunk382State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix382 := by
    have prior : recordUpperSeedTailChunk382Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix381 := by
      simpa only [
        recordUpperSeedTailChunk382Before,
        recordUpperSeedTailChunk381State] using h381
    simpa only [recordUpperSeedTailPrefix382] using
      recordUpperSeedTailChunk382Step.certifies prior
  have h383 : recordUpperSeedTailChunk383State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix383 := by
    have prior : recordUpperSeedTailChunk383Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix382 := by
      simpa only [
        recordUpperSeedTailChunk383Before,
        recordUpperSeedTailChunk382State] using h382
    simpa only [recordUpperSeedTailPrefix383] using
      recordUpperSeedTailChunk383Step.certifies prior
  have h384 : recordUpperSeedTailChunk384State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix384 := by
    have prior : recordUpperSeedTailChunk384Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix383 := by
      simpa only [
        recordUpperSeedTailChunk384Before,
        recordUpperSeedTailChunk383State] using h383
    simpa only [recordUpperSeedTailPrefix384] using
      recordUpperSeedTailChunk384Step.certifies prior
  have h385 : recordUpperSeedTailChunk385State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix385 := by
    have prior : recordUpperSeedTailChunk385Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix384 := by
      simpa only [
        recordUpperSeedTailChunk385Before,
        recordUpperSeedTailChunk384State] using h384
    simpa only [recordUpperSeedTailPrefix385] using
      recordUpperSeedTailChunk385Step.certifies prior
  have h386 : recordUpperSeedTailChunk386State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix386 := by
    have prior : recordUpperSeedTailChunk386Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix385 := by
      simpa only [
        recordUpperSeedTailChunk386Before,
        recordUpperSeedTailChunk385State] using h385
    simpa only [recordUpperSeedTailPrefix386] using
      recordUpperSeedTailChunk386Step.certifies prior
  have h387 : recordUpperSeedTailChunk387State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix387 := by
    have prior : recordUpperSeedTailChunk387Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix386 := by
      simpa only [
        recordUpperSeedTailChunk387Before,
        recordUpperSeedTailChunk386State] using h386
    simpa only [recordUpperSeedTailPrefix387] using
      recordUpperSeedTailChunk387Step.certifies prior
  have h388 : recordUpperSeedTailChunk388State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix388 := by
    have prior : recordUpperSeedTailChunk388Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix387 := by
      simpa only [
        recordUpperSeedTailChunk388Before,
        recordUpperSeedTailChunk387State] using h387
    simpa only [recordUpperSeedTailPrefix388] using
      recordUpperSeedTailChunk388Step.certifies prior
  have h389 : recordUpperSeedTailChunk389State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix389 := by
    have prior : recordUpperSeedTailChunk389Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix388 := by
      simpa only [
        recordUpperSeedTailChunk389Before,
        recordUpperSeedTailChunk388State] using h388
    simpa only [recordUpperSeedTailPrefix389] using
      recordUpperSeedTailChunk389Step.certifies prior
  have h390 : recordUpperSeedTailChunk390State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix390 := by
    have prior : recordUpperSeedTailChunk390Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix389 := by
      simpa only [
        recordUpperSeedTailChunk390Before,
        recordUpperSeedTailChunk389State] using h389
    simpa only [recordUpperSeedTailPrefix390] using
      recordUpperSeedTailChunk390Step.certifies prior
  have h391 : recordUpperSeedTailChunk391State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix391 := by
    have prior : recordUpperSeedTailChunk391Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix390 := by
      simpa only [
        recordUpperSeedTailChunk391Before,
        recordUpperSeedTailChunk390State] using h390
    simpa only [recordUpperSeedTailPrefix391] using
      recordUpperSeedTailChunk391Step.certifies prior
  have h392 : recordUpperSeedTailChunk392State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix392 := by
    have prior : recordUpperSeedTailChunk392Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix391 := by
      simpa only [
        recordUpperSeedTailChunk392Before,
        recordUpperSeedTailChunk391State] using h391
    simpa only [recordUpperSeedTailPrefix392] using
      recordUpperSeedTailChunk392Step.certifies prior
  have h393 : recordUpperSeedTailChunk393State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix393 := by
    have prior : recordUpperSeedTailChunk393Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix392 := by
      simpa only [
        recordUpperSeedTailChunk393Before,
        recordUpperSeedTailChunk392State] using h392
    simpa only [recordUpperSeedTailPrefix393] using
      recordUpperSeedTailChunk393Step.certifies prior
  have h394 : recordUpperSeedTailChunk394State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix394 := by
    have prior : recordUpperSeedTailChunk394Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix393 := by
      simpa only [
        recordUpperSeedTailChunk394Before,
        recordUpperSeedTailChunk393State] using h393
    simpa only [recordUpperSeedTailPrefix394] using
      recordUpperSeedTailChunk394Step.certifies prior
  have h395 : recordUpperSeedTailChunk395State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix395 := by
    have prior : recordUpperSeedTailChunk395Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix394 := by
      simpa only [
        recordUpperSeedTailChunk395Before,
        recordUpperSeedTailChunk394State] using h394
    simpa only [recordUpperSeedTailPrefix395] using
      recordUpperSeedTailChunk395Step.certifies prior
  have h396 : recordUpperSeedTailChunk396State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix396 := by
    have prior : recordUpperSeedTailChunk396Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix395 := by
      simpa only [
        recordUpperSeedTailChunk396Before,
        recordUpperSeedTailChunk395State] using h395
    simpa only [recordUpperSeedTailPrefix396] using
      recordUpperSeedTailChunk396Step.certifies prior
  have h397 : recordUpperSeedTailChunk397State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix397 := by
    have prior : recordUpperSeedTailChunk397Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix396 := by
      simpa only [
        recordUpperSeedTailChunk397Before,
        recordUpperSeedTailChunk396State] using h396
    simpa only [recordUpperSeedTailPrefix397] using
      recordUpperSeedTailChunk397Step.certifies prior
  have h398 : recordUpperSeedTailChunk398State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix398 := by
    have prior : recordUpperSeedTailChunk398Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix397 := by
      simpa only [
        recordUpperSeedTailChunk398Before,
        recordUpperSeedTailChunk397State] using h397
    simpa only [recordUpperSeedTailPrefix398] using
      recordUpperSeedTailChunk398Step.certifies prior
  have h399 : recordUpperSeedTailChunk399State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix399 := by
    have prior : recordUpperSeedTailChunk399Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix398 := by
      simpa only [
        recordUpperSeedTailChunk399Before,
        recordUpperSeedTailChunk398State] using h398
    simpa only [recordUpperSeedTailPrefix399] using
      recordUpperSeedTailChunk399Step.certifies prior
  have h400 : recordUpperSeedTailChunk400State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix400 := by
    have prior : recordUpperSeedTailChunk400Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix399 := by
      simpa only [
        recordUpperSeedTailChunk400Before,
        recordUpperSeedTailChunk399State] using h399
    simpa only [recordUpperSeedTailPrefix400] using
      recordUpperSeedTailChunk400Step.certifies prior
  exact h400

end PrimeFactorUnimodality
