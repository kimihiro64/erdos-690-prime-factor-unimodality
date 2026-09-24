import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Assembly.Part09
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part400

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-upper-seed-base11.json` (semantic SHA-256 `493791f7b41de1500c4b830f254f9f92fd9c5d50d639b62aa2b46ca48591321f`, excluding elapsed time). Semantic tail assembly group 10. -/

namespace PrimeFactorUnimodality

theorem recordUpperSeedTailGroup10_semantic :
    recordUpperSeedTailChunk400State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix400 := by
  have h361 : recordUpperSeedTailChunk361State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix361 := by
    have boundary : recordUpperSeedTailChunk361Before =
        recordUpperSeedTailChunk360State := by rfl
    exact recordUpperSeedTailChunk361Step.certifies
      (boundary.trans recordUpperSeedTailGroup09_semantic)
  have h362 : recordUpperSeedTailChunk362State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix362 := by
    have boundary : recordUpperSeedTailChunk362Before =
        recordUpperSeedTailChunk361State := by rfl
    exact recordUpperSeedTailChunk362Step.certifies
      (boundary.trans h361)
  have h363 : recordUpperSeedTailChunk363State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix363 := by
    have boundary : recordUpperSeedTailChunk363Before =
        recordUpperSeedTailChunk362State := by rfl
    exact recordUpperSeedTailChunk363Step.certifies
      (boundary.trans h362)
  have h364 : recordUpperSeedTailChunk364State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix364 := by
    have boundary : recordUpperSeedTailChunk364Before =
        recordUpperSeedTailChunk363State := by rfl
    exact recordUpperSeedTailChunk364Step.certifies
      (boundary.trans h363)
  have h365 : recordUpperSeedTailChunk365State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix365 := by
    have boundary : recordUpperSeedTailChunk365Before =
        recordUpperSeedTailChunk364State := by rfl
    exact recordUpperSeedTailChunk365Step.certifies
      (boundary.trans h364)
  have h366 : recordUpperSeedTailChunk366State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix366 := by
    have boundary : recordUpperSeedTailChunk366Before =
        recordUpperSeedTailChunk365State := by rfl
    exact recordUpperSeedTailChunk366Step.certifies
      (boundary.trans h365)
  have h367 : recordUpperSeedTailChunk367State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix367 := by
    have boundary : recordUpperSeedTailChunk367Before =
        recordUpperSeedTailChunk366State := by rfl
    exact recordUpperSeedTailChunk367Step.certifies
      (boundary.trans h366)
  have h368 : recordUpperSeedTailChunk368State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix368 := by
    have boundary : recordUpperSeedTailChunk368Before =
        recordUpperSeedTailChunk367State := by rfl
    exact recordUpperSeedTailChunk368Step.certifies
      (boundary.trans h367)
  have h369 : recordUpperSeedTailChunk369State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix369 := by
    have boundary : recordUpperSeedTailChunk369Before =
        recordUpperSeedTailChunk368State := by rfl
    exact recordUpperSeedTailChunk369Step.certifies
      (boundary.trans h368)
  have h370 : recordUpperSeedTailChunk370State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix370 := by
    have boundary : recordUpperSeedTailChunk370Before =
        recordUpperSeedTailChunk369State := by rfl
    exact recordUpperSeedTailChunk370Step.certifies
      (boundary.trans h369)
  have h371 : recordUpperSeedTailChunk371State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix371 := by
    have boundary : recordUpperSeedTailChunk371Before =
        recordUpperSeedTailChunk370State := by rfl
    exact recordUpperSeedTailChunk371Step.certifies
      (boundary.trans h370)
  have h372 : recordUpperSeedTailChunk372State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix372 := by
    have boundary : recordUpperSeedTailChunk372Before =
        recordUpperSeedTailChunk371State := by rfl
    exact recordUpperSeedTailChunk372Step.certifies
      (boundary.trans h371)
  have h373 : recordUpperSeedTailChunk373State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix373 := by
    have boundary : recordUpperSeedTailChunk373Before =
        recordUpperSeedTailChunk372State := by rfl
    exact recordUpperSeedTailChunk373Step.certifies
      (boundary.trans h372)
  have h374 : recordUpperSeedTailChunk374State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix374 := by
    have boundary : recordUpperSeedTailChunk374Before =
        recordUpperSeedTailChunk373State := by rfl
    exact recordUpperSeedTailChunk374Step.certifies
      (boundary.trans h373)
  have h375 : recordUpperSeedTailChunk375State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix375 := by
    have boundary : recordUpperSeedTailChunk375Before =
        recordUpperSeedTailChunk374State := by rfl
    exact recordUpperSeedTailChunk375Step.certifies
      (boundary.trans h374)
  have h376 : recordUpperSeedTailChunk376State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix376 := by
    have boundary : recordUpperSeedTailChunk376Before =
        recordUpperSeedTailChunk375State := by rfl
    exact recordUpperSeedTailChunk376Step.certifies
      (boundary.trans h375)
  have h377 : recordUpperSeedTailChunk377State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix377 := by
    have boundary : recordUpperSeedTailChunk377Before =
        recordUpperSeedTailChunk376State := by rfl
    exact recordUpperSeedTailChunk377Step.certifies
      (boundary.trans h376)
  have h378 : recordUpperSeedTailChunk378State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix378 := by
    have boundary : recordUpperSeedTailChunk378Before =
        recordUpperSeedTailChunk377State := by rfl
    exact recordUpperSeedTailChunk378Step.certifies
      (boundary.trans h377)
  have h379 : recordUpperSeedTailChunk379State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix379 := by
    have boundary : recordUpperSeedTailChunk379Before =
        recordUpperSeedTailChunk378State := by rfl
    exact recordUpperSeedTailChunk379Step.certifies
      (boundary.trans h378)
  have h380 : recordUpperSeedTailChunk380State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix380 := by
    have boundary : recordUpperSeedTailChunk380Before =
        recordUpperSeedTailChunk379State := by rfl
    exact recordUpperSeedTailChunk380Step.certifies
      (boundary.trans h379)
  have h381 : recordUpperSeedTailChunk381State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix381 := by
    have boundary : recordUpperSeedTailChunk381Before =
        recordUpperSeedTailChunk380State := by rfl
    exact recordUpperSeedTailChunk381Step.certifies
      (boundary.trans h380)
  have h382 : recordUpperSeedTailChunk382State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix382 := by
    have boundary : recordUpperSeedTailChunk382Before =
        recordUpperSeedTailChunk381State := by rfl
    exact recordUpperSeedTailChunk382Step.certifies
      (boundary.trans h381)
  have h383 : recordUpperSeedTailChunk383State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix383 := by
    have boundary : recordUpperSeedTailChunk383Before =
        recordUpperSeedTailChunk382State := by rfl
    exact recordUpperSeedTailChunk383Step.certifies
      (boundary.trans h382)
  have h384 : recordUpperSeedTailChunk384State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix384 := by
    have boundary : recordUpperSeedTailChunk384Before =
        recordUpperSeedTailChunk383State := by rfl
    exact recordUpperSeedTailChunk384Step.certifies
      (boundary.trans h383)
  have h385 : recordUpperSeedTailChunk385State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix385 := by
    have boundary : recordUpperSeedTailChunk385Before =
        recordUpperSeedTailChunk384State := by rfl
    exact recordUpperSeedTailChunk385Step.certifies
      (boundary.trans h384)
  have h386 : recordUpperSeedTailChunk386State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix386 := by
    have boundary : recordUpperSeedTailChunk386Before =
        recordUpperSeedTailChunk385State := by rfl
    exact recordUpperSeedTailChunk386Step.certifies
      (boundary.trans h385)
  have h387 : recordUpperSeedTailChunk387State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix387 := by
    have boundary : recordUpperSeedTailChunk387Before =
        recordUpperSeedTailChunk386State := by rfl
    exact recordUpperSeedTailChunk387Step.certifies
      (boundary.trans h386)
  have h388 : recordUpperSeedTailChunk388State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix388 := by
    have boundary : recordUpperSeedTailChunk388Before =
        recordUpperSeedTailChunk387State := by rfl
    exact recordUpperSeedTailChunk388Step.certifies
      (boundary.trans h387)
  have h389 : recordUpperSeedTailChunk389State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix389 := by
    have boundary : recordUpperSeedTailChunk389Before =
        recordUpperSeedTailChunk388State := by rfl
    exact recordUpperSeedTailChunk389Step.certifies
      (boundary.trans h388)
  have h390 : recordUpperSeedTailChunk390State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix390 := by
    have boundary : recordUpperSeedTailChunk390Before =
        recordUpperSeedTailChunk389State := by rfl
    exact recordUpperSeedTailChunk390Step.certifies
      (boundary.trans h389)
  have h391 : recordUpperSeedTailChunk391State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix391 := by
    have boundary : recordUpperSeedTailChunk391Before =
        recordUpperSeedTailChunk390State := by rfl
    exact recordUpperSeedTailChunk391Step.certifies
      (boundary.trans h390)
  have h392 : recordUpperSeedTailChunk392State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix392 := by
    have boundary : recordUpperSeedTailChunk392Before =
        recordUpperSeedTailChunk391State := by rfl
    exact recordUpperSeedTailChunk392Step.certifies
      (boundary.trans h391)
  have h393 : recordUpperSeedTailChunk393State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix393 := by
    have boundary : recordUpperSeedTailChunk393Before =
        recordUpperSeedTailChunk392State := by rfl
    exact recordUpperSeedTailChunk393Step.certifies
      (boundary.trans h392)
  have h394 : recordUpperSeedTailChunk394State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix394 := by
    have boundary : recordUpperSeedTailChunk394Before =
        recordUpperSeedTailChunk393State := by rfl
    exact recordUpperSeedTailChunk394Step.certifies
      (boundary.trans h393)
  have h395 : recordUpperSeedTailChunk395State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix395 := by
    have boundary : recordUpperSeedTailChunk395Before =
        recordUpperSeedTailChunk394State := by rfl
    exact recordUpperSeedTailChunk395Step.certifies
      (boundary.trans h394)
  have h396 : recordUpperSeedTailChunk396State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix396 := by
    have boundary : recordUpperSeedTailChunk396Before =
        recordUpperSeedTailChunk395State := by rfl
    exact recordUpperSeedTailChunk396Step.certifies
      (boundary.trans h395)
  have h397 : recordUpperSeedTailChunk397State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix397 := by
    have boundary : recordUpperSeedTailChunk397Before =
        recordUpperSeedTailChunk396State := by rfl
    exact recordUpperSeedTailChunk397Step.certifies
      (boundary.trans h396)
  have h398 : recordUpperSeedTailChunk398State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix398 := by
    have boundary : recordUpperSeedTailChunk398Before =
        recordUpperSeedTailChunk397State := by rfl
    exact recordUpperSeedTailChunk398Step.certifies
      (boundary.trans h397)
  have h399 : recordUpperSeedTailChunk399State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix399 := by
    have boundary : recordUpperSeedTailChunk399Before =
        recordUpperSeedTailChunk398State := by rfl
    exact recordUpperSeedTailChunk399Step.certifies
      (boundary.trans h398)
  have h400 : recordUpperSeedTailChunk400State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix400 := by
    have boundary : recordUpperSeedTailChunk400Before =
        recordUpperSeedTailChunk399State := by rfl
    exact recordUpperSeedTailChunk400Step.certifies
      (boundary.trans h399)
  exact h400

end PrimeFactorUnimodality
