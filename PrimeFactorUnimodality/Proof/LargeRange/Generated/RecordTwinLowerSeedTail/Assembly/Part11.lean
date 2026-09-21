import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Assembly.Part10
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part440

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-lower-seed.json` (semantic SHA-256 `3ce105dad06099400dfd2e30c65d47c6e02828915452a8459553c3bb0eb78b73`, excluding elapsed time). Semantic tail assembly group 11. -/

namespace PrimeFactorUnimodality

theorem recordLowerSeedTailGroup11_semantic :
    recordLowerSeedTailChunk440State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix440 := by
  have h401 : recordLowerSeedTailChunk401State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix401 := by
    have prior : recordLowerSeedTailChunk401Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix400 := by
      simpa only [
        recordLowerSeedTailChunk401Before,
        recordLowerSeedTailChunk400State] using recordLowerSeedTailGroup10_semantic
    simpa only [recordLowerSeedTailPrefix401] using
      recordLowerSeedTailChunk401Step.certifies prior
  have h402 : recordLowerSeedTailChunk402State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix402 := by
    have prior : recordLowerSeedTailChunk402Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix401 := by
      simpa only [
        recordLowerSeedTailChunk402Before,
        recordLowerSeedTailChunk401State] using h401
    simpa only [recordLowerSeedTailPrefix402] using
      recordLowerSeedTailChunk402Step.certifies prior
  have h403 : recordLowerSeedTailChunk403State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix403 := by
    have prior : recordLowerSeedTailChunk403Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix402 := by
      simpa only [
        recordLowerSeedTailChunk403Before,
        recordLowerSeedTailChunk402State] using h402
    simpa only [recordLowerSeedTailPrefix403] using
      recordLowerSeedTailChunk403Step.certifies prior
  have h404 : recordLowerSeedTailChunk404State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix404 := by
    have prior : recordLowerSeedTailChunk404Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix403 := by
      simpa only [
        recordLowerSeedTailChunk404Before,
        recordLowerSeedTailChunk403State] using h403
    simpa only [recordLowerSeedTailPrefix404] using
      recordLowerSeedTailChunk404Step.certifies prior
  have h405 : recordLowerSeedTailChunk405State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix405 := by
    have prior : recordLowerSeedTailChunk405Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix404 := by
      simpa only [
        recordLowerSeedTailChunk405Before,
        recordLowerSeedTailChunk404State] using h404
    simpa only [recordLowerSeedTailPrefix405] using
      recordLowerSeedTailChunk405Step.certifies prior
  have h406 : recordLowerSeedTailChunk406State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix406 := by
    have prior : recordLowerSeedTailChunk406Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix405 := by
      simpa only [
        recordLowerSeedTailChunk406Before,
        recordLowerSeedTailChunk405State] using h405
    simpa only [recordLowerSeedTailPrefix406] using
      recordLowerSeedTailChunk406Step.certifies prior
  have h407 : recordLowerSeedTailChunk407State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix407 := by
    have prior : recordLowerSeedTailChunk407Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix406 := by
      simpa only [
        recordLowerSeedTailChunk407Before,
        recordLowerSeedTailChunk406State] using h406
    simpa only [recordLowerSeedTailPrefix407] using
      recordLowerSeedTailChunk407Step.certifies prior
  have h408 : recordLowerSeedTailChunk408State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix408 := by
    have prior : recordLowerSeedTailChunk408Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix407 := by
      simpa only [
        recordLowerSeedTailChunk408Before,
        recordLowerSeedTailChunk407State] using h407
    simpa only [recordLowerSeedTailPrefix408] using
      recordLowerSeedTailChunk408Step.certifies prior
  have h409 : recordLowerSeedTailChunk409State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix409 := by
    have prior : recordLowerSeedTailChunk409Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix408 := by
      simpa only [
        recordLowerSeedTailChunk409Before,
        recordLowerSeedTailChunk408State] using h408
    simpa only [recordLowerSeedTailPrefix409] using
      recordLowerSeedTailChunk409Step.certifies prior
  have h410 : recordLowerSeedTailChunk410State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix410 := by
    have prior : recordLowerSeedTailChunk410Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix409 := by
      simpa only [
        recordLowerSeedTailChunk410Before,
        recordLowerSeedTailChunk409State] using h409
    simpa only [recordLowerSeedTailPrefix410] using
      recordLowerSeedTailChunk410Step.certifies prior
  have h411 : recordLowerSeedTailChunk411State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix411 := by
    have prior : recordLowerSeedTailChunk411Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix410 := by
      simpa only [
        recordLowerSeedTailChunk411Before,
        recordLowerSeedTailChunk410State] using h410
    simpa only [recordLowerSeedTailPrefix411] using
      recordLowerSeedTailChunk411Step.certifies prior
  have h412 : recordLowerSeedTailChunk412State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix412 := by
    have prior : recordLowerSeedTailChunk412Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix411 := by
      simpa only [
        recordLowerSeedTailChunk412Before,
        recordLowerSeedTailChunk411State] using h411
    simpa only [recordLowerSeedTailPrefix412] using
      recordLowerSeedTailChunk412Step.certifies prior
  have h413 : recordLowerSeedTailChunk413State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix413 := by
    have prior : recordLowerSeedTailChunk413Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix412 := by
      simpa only [
        recordLowerSeedTailChunk413Before,
        recordLowerSeedTailChunk412State] using h412
    simpa only [recordLowerSeedTailPrefix413] using
      recordLowerSeedTailChunk413Step.certifies prior
  have h414 : recordLowerSeedTailChunk414State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix414 := by
    have prior : recordLowerSeedTailChunk414Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix413 := by
      simpa only [
        recordLowerSeedTailChunk414Before,
        recordLowerSeedTailChunk413State] using h413
    simpa only [recordLowerSeedTailPrefix414] using
      recordLowerSeedTailChunk414Step.certifies prior
  have h415 : recordLowerSeedTailChunk415State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix415 := by
    have prior : recordLowerSeedTailChunk415Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix414 := by
      simpa only [
        recordLowerSeedTailChunk415Before,
        recordLowerSeedTailChunk414State] using h414
    simpa only [recordLowerSeedTailPrefix415] using
      recordLowerSeedTailChunk415Step.certifies prior
  have h416 : recordLowerSeedTailChunk416State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix416 := by
    have prior : recordLowerSeedTailChunk416Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix415 := by
      simpa only [
        recordLowerSeedTailChunk416Before,
        recordLowerSeedTailChunk415State] using h415
    simpa only [recordLowerSeedTailPrefix416] using
      recordLowerSeedTailChunk416Step.certifies prior
  have h417 : recordLowerSeedTailChunk417State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix417 := by
    have prior : recordLowerSeedTailChunk417Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix416 := by
      simpa only [
        recordLowerSeedTailChunk417Before,
        recordLowerSeedTailChunk416State] using h416
    simpa only [recordLowerSeedTailPrefix417] using
      recordLowerSeedTailChunk417Step.certifies prior
  have h418 : recordLowerSeedTailChunk418State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix418 := by
    have prior : recordLowerSeedTailChunk418Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix417 := by
      simpa only [
        recordLowerSeedTailChunk418Before,
        recordLowerSeedTailChunk417State] using h417
    simpa only [recordLowerSeedTailPrefix418] using
      recordLowerSeedTailChunk418Step.certifies prior
  have h419 : recordLowerSeedTailChunk419State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix419 := by
    have prior : recordLowerSeedTailChunk419Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix418 := by
      simpa only [
        recordLowerSeedTailChunk419Before,
        recordLowerSeedTailChunk418State] using h418
    simpa only [recordLowerSeedTailPrefix419] using
      recordLowerSeedTailChunk419Step.certifies prior
  have h420 : recordLowerSeedTailChunk420State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix420 := by
    have prior : recordLowerSeedTailChunk420Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix419 := by
      simpa only [
        recordLowerSeedTailChunk420Before,
        recordLowerSeedTailChunk419State] using h419
    simpa only [recordLowerSeedTailPrefix420] using
      recordLowerSeedTailChunk420Step.certifies prior
  have h421 : recordLowerSeedTailChunk421State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix421 := by
    have prior : recordLowerSeedTailChunk421Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix420 := by
      simpa only [
        recordLowerSeedTailChunk421Before,
        recordLowerSeedTailChunk420State] using h420
    simpa only [recordLowerSeedTailPrefix421] using
      recordLowerSeedTailChunk421Step.certifies prior
  have h422 : recordLowerSeedTailChunk422State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix422 := by
    have prior : recordLowerSeedTailChunk422Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix421 := by
      simpa only [
        recordLowerSeedTailChunk422Before,
        recordLowerSeedTailChunk421State] using h421
    simpa only [recordLowerSeedTailPrefix422] using
      recordLowerSeedTailChunk422Step.certifies prior
  have h423 : recordLowerSeedTailChunk423State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix423 := by
    have prior : recordLowerSeedTailChunk423Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix422 := by
      simpa only [
        recordLowerSeedTailChunk423Before,
        recordLowerSeedTailChunk422State] using h422
    simpa only [recordLowerSeedTailPrefix423] using
      recordLowerSeedTailChunk423Step.certifies prior
  have h424 : recordLowerSeedTailChunk424State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix424 := by
    have prior : recordLowerSeedTailChunk424Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix423 := by
      simpa only [
        recordLowerSeedTailChunk424Before,
        recordLowerSeedTailChunk423State] using h423
    simpa only [recordLowerSeedTailPrefix424] using
      recordLowerSeedTailChunk424Step.certifies prior
  have h425 : recordLowerSeedTailChunk425State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix425 := by
    have prior : recordLowerSeedTailChunk425Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix424 := by
      simpa only [
        recordLowerSeedTailChunk425Before,
        recordLowerSeedTailChunk424State] using h424
    simpa only [recordLowerSeedTailPrefix425] using
      recordLowerSeedTailChunk425Step.certifies prior
  have h426 : recordLowerSeedTailChunk426State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix426 := by
    have prior : recordLowerSeedTailChunk426Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix425 := by
      simpa only [
        recordLowerSeedTailChunk426Before,
        recordLowerSeedTailChunk425State] using h425
    simpa only [recordLowerSeedTailPrefix426] using
      recordLowerSeedTailChunk426Step.certifies prior
  have h427 : recordLowerSeedTailChunk427State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix427 := by
    have prior : recordLowerSeedTailChunk427Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix426 := by
      simpa only [
        recordLowerSeedTailChunk427Before,
        recordLowerSeedTailChunk426State] using h426
    simpa only [recordLowerSeedTailPrefix427] using
      recordLowerSeedTailChunk427Step.certifies prior
  have h428 : recordLowerSeedTailChunk428State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix428 := by
    have prior : recordLowerSeedTailChunk428Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix427 := by
      simpa only [
        recordLowerSeedTailChunk428Before,
        recordLowerSeedTailChunk427State] using h427
    simpa only [recordLowerSeedTailPrefix428] using
      recordLowerSeedTailChunk428Step.certifies prior
  have h429 : recordLowerSeedTailChunk429State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix429 := by
    have prior : recordLowerSeedTailChunk429Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix428 := by
      simpa only [
        recordLowerSeedTailChunk429Before,
        recordLowerSeedTailChunk428State] using h428
    simpa only [recordLowerSeedTailPrefix429] using
      recordLowerSeedTailChunk429Step.certifies prior
  have h430 : recordLowerSeedTailChunk430State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix430 := by
    have prior : recordLowerSeedTailChunk430Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix429 := by
      simpa only [
        recordLowerSeedTailChunk430Before,
        recordLowerSeedTailChunk429State] using h429
    simpa only [recordLowerSeedTailPrefix430] using
      recordLowerSeedTailChunk430Step.certifies prior
  have h431 : recordLowerSeedTailChunk431State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix431 := by
    have prior : recordLowerSeedTailChunk431Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix430 := by
      simpa only [
        recordLowerSeedTailChunk431Before,
        recordLowerSeedTailChunk430State] using h430
    simpa only [recordLowerSeedTailPrefix431] using
      recordLowerSeedTailChunk431Step.certifies prior
  have h432 : recordLowerSeedTailChunk432State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix432 := by
    have prior : recordLowerSeedTailChunk432Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix431 := by
      simpa only [
        recordLowerSeedTailChunk432Before,
        recordLowerSeedTailChunk431State] using h431
    simpa only [recordLowerSeedTailPrefix432] using
      recordLowerSeedTailChunk432Step.certifies prior
  have h433 : recordLowerSeedTailChunk433State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix433 := by
    have prior : recordLowerSeedTailChunk433Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix432 := by
      simpa only [
        recordLowerSeedTailChunk433Before,
        recordLowerSeedTailChunk432State] using h432
    simpa only [recordLowerSeedTailPrefix433] using
      recordLowerSeedTailChunk433Step.certifies prior
  have h434 : recordLowerSeedTailChunk434State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix434 := by
    have prior : recordLowerSeedTailChunk434Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix433 := by
      simpa only [
        recordLowerSeedTailChunk434Before,
        recordLowerSeedTailChunk433State] using h433
    simpa only [recordLowerSeedTailPrefix434] using
      recordLowerSeedTailChunk434Step.certifies prior
  have h435 : recordLowerSeedTailChunk435State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix435 := by
    have prior : recordLowerSeedTailChunk435Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix434 := by
      simpa only [
        recordLowerSeedTailChunk435Before,
        recordLowerSeedTailChunk434State] using h434
    simpa only [recordLowerSeedTailPrefix435] using
      recordLowerSeedTailChunk435Step.certifies prior
  have h436 : recordLowerSeedTailChunk436State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix436 := by
    have prior : recordLowerSeedTailChunk436Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix435 := by
      simpa only [
        recordLowerSeedTailChunk436Before,
        recordLowerSeedTailChunk435State] using h435
    simpa only [recordLowerSeedTailPrefix436] using
      recordLowerSeedTailChunk436Step.certifies prior
  have h437 : recordLowerSeedTailChunk437State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix437 := by
    have prior : recordLowerSeedTailChunk437Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix436 := by
      simpa only [
        recordLowerSeedTailChunk437Before,
        recordLowerSeedTailChunk436State] using h436
    simpa only [recordLowerSeedTailPrefix437] using
      recordLowerSeedTailChunk437Step.certifies prior
  have h438 : recordLowerSeedTailChunk438State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix438 := by
    have prior : recordLowerSeedTailChunk438Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix437 := by
      simpa only [
        recordLowerSeedTailChunk438Before,
        recordLowerSeedTailChunk437State] using h437
    simpa only [recordLowerSeedTailPrefix438] using
      recordLowerSeedTailChunk438Step.certifies prior
  have h439 : recordLowerSeedTailChunk439State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix439 := by
    have prior : recordLowerSeedTailChunk439Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix438 := by
      simpa only [
        recordLowerSeedTailChunk439Before,
        recordLowerSeedTailChunk438State] using h438
    simpa only [recordLowerSeedTailPrefix439] using
      recordLowerSeedTailChunk439Step.certifies prior
  have h440 : recordLowerSeedTailChunk440State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix440 := by
    have prior : recordLowerSeedTailChunk440Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix439 := by
      simpa only [
        recordLowerSeedTailChunk440Before,
        recordLowerSeedTailChunk439State] using h439
    simpa only [recordLowerSeedTailPrefix440] using
      recordLowerSeedTailChunk440Step.certifies prior
  exact h440

end PrimeFactorUnimodality
