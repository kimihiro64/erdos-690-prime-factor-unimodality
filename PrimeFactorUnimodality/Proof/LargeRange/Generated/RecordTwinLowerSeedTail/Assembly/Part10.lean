import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Assembly.Part09
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part400

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-lower-seed.json` (semantic SHA-256 `3ce105dad06099400dfd2e30c65d47c6e02828915452a8459553c3bb0eb78b73`, excluding elapsed time). Semantic tail assembly group 10. -/

namespace PrimeFactorUnimodality

theorem recordLowerSeedTailGroup10_semantic :
    recordLowerSeedTailChunk400State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix400 := by
  have h361 : recordLowerSeedTailChunk361State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix361 := by
    have boundary : recordLowerSeedTailChunk361Before =
        recordLowerSeedTailChunk360State := by rfl
    exact recordLowerSeedTailChunk361Step.certifies
      (boundary.trans recordLowerSeedTailGroup09_semantic)
  have h362 : recordLowerSeedTailChunk362State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix362 := by
    have boundary : recordLowerSeedTailChunk362Before =
        recordLowerSeedTailChunk361State := by rfl
    exact recordLowerSeedTailChunk362Step.certifies
      (boundary.trans h361)
  have h363 : recordLowerSeedTailChunk363State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix363 := by
    have boundary : recordLowerSeedTailChunk363Before =
        recordLowerSeedTailChunk362State := by rfl
    exact recordLowerSeedTailChunk363Step.certifies
      (boundary.trans h362)
  have h364 : recordLowerSeedTailChunk364State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix364 := by
    have boundary : recordLowerSeedTailChunk364Before =
        recordLowerSeedTailChunk363State := by rfl
    exact recordLowerSeedTailChunk364Step.certifies
      (boundary.trans h363)
  have h365 : recordLowerSeedTailChunk365State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix365 := by
    have boundary : recordLowerSeedTailChunk365Before =
        recordLowerSeedTailChunk364State := by rfl
    exact recordLowerSeedTailChunk365Step.certifies
      (boundary.trans h364)
  have h366 : recordLowerSeedTailChunk366State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix366 := by
    have boundary : recordLowerSeedTailChunk366Before =
        recordLowerSeedTailChunk365State := by rfl
    exact recordLowerSeedTailChunk366Step.certifies
      (boundary.trans h365)
  have h367 : recordLowerSeedTailChunk367State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix367 := by
    have boundary : recordLowerSeedTailChunk367Before =
        recordLowerSeedTailChunk366State := by rfl
    exact recordLowerSeedTailChunk367Step.certifies
      (boundary.trans h366)
  have h368 : recordLowerSeedTailChunk368State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix368 := by
    have boundary : recordLowerSeedTailChunk368Before =
        recordLowerSeedTailChunk367State := by rfl
    exact recordLowerSeedTailChunk368Step.certifies
      (boundary.trans h367)
  have h369 : recordLowerSeedTailChunk369State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix369 := by
    have boundary : recordLowerSeedTailChunk369Before =
        recordLowerSeedTailChunk368State := by rfl
    exact recordLowerSeedTailChunk369Step.certifies
      (boundary.trans h368)
  have h370 : recordLowerSeedTailChunk370State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix370 := by
    have boundary : recordLowerSeedTailChunk370Before =
        recordLowerSeedTailChunk369State := by rfl
    exact recordLowerSeedTailChunk370Step.certifies
      (boundary.trans h369)
  have h371 : recordLowerSeedTailChunk371State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix371 := by
    have boundary : recordLowerSeedTailChunk371Before =
        recordLowerSeedTailChunk370State := by rfl
    exact recordLowerSeedTailChunk371Step.certifies
      (boundary.trans h370)
  have h372 : recordLowerSeedTailChunk372State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix372 := by
    have boundary : recordLowerSeedTailChunk372Before =
        recordLowerSeedTailChunk371State := by rfl
    exact recordLowerSeedTailChunk372Step.certifies
      (boundary.trans h371)
  have h373 : recordLowerSeedTailChunk373State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix373 := by
    have boundary : recordLowerSeedTailChunk373Before =
        recordLowerSeedTailChunk372State := by rfl
    exact recordLowerSeedTailChunk373Step.certifies
      (boundary.trans h372)
  have h374 : recordLowerSeedTailChunk374State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix374 := by
    have boundary : recordLowerSeedTailChunk374Before =
        recordLowerSeedTailChunk373State := by rfl
    exact recordLowerSeedTailChunk374Step.certifies
      (boundary.trans h373)
  have h375 : recordLowerSeedTailChunk375State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix375 := by
    have boundary : recordLowerSeedTailChunk375Before =
        recordLowerSeedTailChunk374State := by rfl
    exact recordLowerSeedTailChunk375Step.certifies
      (boundary.trans h374)
  have h376 : recordLowerSeedTailChunk376State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix376 := by
    have boundary : recordLowerSeedTailChunk376Before =
        recordLowerSeedTailChunk375State := by rfl
    exact recordLowerSeedTailChunk376Step.certifies
      (boundary.trans h375)
  have h377 : recordLowerSeedTailChunk377State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix377 := by
    have boundary : recordLowerSeedTailChunk377Before =
        recordLowerSeedTailChunk376State := by rfl
    exact recordLowerSeedTailChunk377Step.certifies
      (boundary.trans h376)
  have h378 : recordLowerSeedTailChunk378State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix378 := by
    have boundary : recordLowerSeedTailChunk378Before =
        recordLowerSeedTailChunk377State := by rfl
    exact recordLowerSeedTailChunk378Step.certifies
      (boundary.trans h377)
  have h379 : recordLowerSeedTailChunk379State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix379 := by
    have boundary : recordLowerSeedTailChunk379Before =
        recordLowerSeedTailChunk378State := by rfl
    exact recordLowerSeedTailChunk379Step.certifies
      (boundary.trans h378)
  have h380 : recordLowerSeedTailChunk380State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix380 := by
    have boundary : recordLowerSeedTailChunk380Before =
        recordLowerSeedTailChunk379State := by rfl
    exact recordLowerSeedTailChunk380Step.certifies
      (boundary.trans h379)
  have h381 : recordLowerSeedTailChunk381State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix381 := by
    have boundary : recordLowerSeedTailChunk381Before =
        recordLowerSeedTailChunk380State := by rfl
    exact recordLowerSeedTailChunk381Step.certifies
      (boundary.trans h380)
  have h382 : recordLowerSeedTailChunk382State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix382 := by
    have boundary : recordLowerSeedTailChunk382Before =
        recordLowerSeedTailChunk381State := by rfl
    exact recordLowerSeedTailChunk382Step.certifies
      (boundary.trans h381)
  have h383 : recordLowerSeedTailChunk383State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix383 := by
    have boundary : recordLowerSeedTailChunk383Before =
        recordLowerSeedTailChunk382State := by rfl
    exact recordLowerSeedTailChunk383Step.certifies
      (boundary.trans h382)
  have h384 : recordLowerSeedTailChunk384State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix384 := by
    have boundary : recordLowerSeedTailChunk384Before =
        recordLowerSeedTailChunk383State := by rfl
    exact recordLowerSeedTailChunk384Step.certifies
      (boundary.trans h383)
  have h385 : recordLowerSeedTailChunk385State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix385 := by
    have boundary : recordLowerSeedTailChunk385Before =
        recordLowerSeedTailChunk384State := by rfl
    exact recordLowerSeedTailChunk385Step.certifies
      (boundary.trans h384)
  have h386 : recordLowerSeedTailChunk386State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix386 := by
    have boundary : recordLowerSeedTailChunk386Before =
        recordLowerSeedTailChunk385State := by rfl
    exact recordLowerSeedTailChunk386Step.certifies
      (boundary.trans h385)
  have h387 : recordLowerSeedTailChunk387State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix387 := by
    have boundary : recordLowerSeedTailChunk387Before =
        recordLowerSeedTailChunk386State := by rfl
    exact recordLowerSeedTailChunk387Step.certifies
      (boundary.trans h386)
  have h388 : recordLowerSeedTailChunk388State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix388 := by
    have boundary : recordLowerSeedTailChunk388Before =
        recordLowerSeedTailChunk387State := by rfl
    exact recordLowerSeedTailChunk388Step.certifies
      (boundary.trans h387)
  have h389 : recordLowerSeedTailChunk389State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix389 := by
    have boundary : recordLowerSeedTailChunk389Before =
        recordLowerSeedTailChunk388State := by rfl
    exact recordLowerSeedTailChunk389Step.certifies
      (boundary.trans h388)
  have h390 : recordLowerSeedTailChunk390State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix390 := by
    have boundary : recordLowerSeedTailChunk390Before =
        recordLowerSeedTailChunk389State := by rfl
    exact recordLowerSeedTailChunk390Step.certifies
      (boundary.trans h389)
  have h391 : recordLowerSeedTailChunk391State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix391 := by
    have boundary : recordLowerSeedTailChunk391Before =
        recordLowerSeedTailChunk390State := by rfl
    exact recordLowerSeedTailChunk391Step.certifies
      (boundary.trans h390)
  have h392 : recordLowerSeedTailChunk392State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix392 := by
    have boundary : recordLowerSeedTailChunk392Before =
        recordLowerSeedTailChunk391State := by rfl
    exact recordLowerSeedTailChunk392Step.certifies
      (boundary.trans h391)
  have h393 : recordLowerSeedTailChunk393State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix393 := by
    have boundary : recordLowerSeedTailChunk393Before =
        recordLowerSeedTailChunk392State := by rfl
    exact recordLowerSeedTailChunk393Step.certifies
      (boundary.trans h392)
  have h394 : recordLowerSeedTailChunk394State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix394 := by
    have boundary : recordLowerSeedTailChunk394Before =
        recordLowerSeedTailChunk393State := by rfl
    exact recordLowerSeedTailChunk394Step.certifies
      (boundary.trans h393)
  have h395 : recordLowerSeedTailChunk395State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix395 := by
    have boundary : recordLowerSeedTailChunk395Before =
        recordLowerSeedTailChunk394State := by rfl
    exact recordLowerSeedTailChunk395Step.certifies
      (boundary.trans h394)
  have h396 : recordLowerSeedTailChunk396State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix396 := by
    have boundary : recordLowerSeedTailChunk396Before =
        recordLowerSeedTailChunk395State := by rfl
    exact recordLowerSeedTailChunk396Step.certifies
      (boundary.trans h395)
  have h397 : recordLowerSeedTailChunk397State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix397 := by
    have boundary : recordLowerSeedTailChunk397Before =
        recordLowerSeedTailChunk396State := by rfl
    exact recordLowerSeedTailChunk397Step.certifies
      (boundary.trans h396)
  have h398 : recordLowerSeedTailChunk398State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix398 := by
    have boundary : recordLowerSeedTailChunk398Before =
        recordLowerSeedTailChunk397State := by rfl
    exact recordLowerSeedTailChunk398Step.certifies
      (boundary.trans h397)
  have h399 : recordLowerSeedTailChunk399State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix399 := by
    have boundary : recordLowerSeedTailChunk399Before =
        recordLowerSeedTailChunk398State := by rfl
    exact recordLowerSeedTailChunk399Step.certifies
      (boundary.trans h398)
  have h400 : recordLowerSeedTailChunk400State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix400 := by
    have boundary : recordLowerSeedTailChunk400Before =
        recordLowerSeedTailChunk399State := by rfl
    exact recordLowerSeedTailChunk400Step.certifies
      (boundary.trans h399)
  exact h400

end PrimeFactorUnimodality
