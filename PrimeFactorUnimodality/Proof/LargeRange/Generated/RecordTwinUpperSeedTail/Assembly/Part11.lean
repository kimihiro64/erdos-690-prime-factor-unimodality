import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Assembly.Part10
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part401
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part402
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part403
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part404
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part405
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part406
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part407
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part408
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part409
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part410
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part411
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part412
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part413
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part414
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part415
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part416
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part417
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part418
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part419
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part420
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part421
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part422
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part423
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part424
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part425
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part426
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part427
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part428
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part429
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part430
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part431
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part432
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part433
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part434
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part435
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part436
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part437
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part438
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part439
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part440

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-upper-seed-base11.json` (semantic SHA-256 `493791f7b41de1500c4b830f254f9f92fd9c5d50d639b62aa2b46ca48591321f`, excluding elapsed time). Semantic tail assembly group 11. -/

namespace PrimeFactorUnimodality

theorem recordUpperSeedTailGroup11_semantic :
    recordUpperSeedTailChunk440State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix440 := by
  have h401 : recordUpperSeedTailChunk401State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix401 := by
    have prior : recordUpperSeedTailChunk401Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix400 := by
      simpa only [
        recordUpperSeedTailChunk401Before,
        recordUpperSeedTailChunk400State] using recordUpperSeedTailGroup10_semantic
    simpa only [recordUpperSeedTailPrefix401] using
      recordUpperSeedTailChunk401Step.certifies prior
  have h402 : recordUpperSeedTailChunk402State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix402 := by
    have prior : recordUpperSeedTailChunk402Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix401 := by
      simpa only [
        recordUpperSeedTailChunk402Before,
        recordUpperSeedTailChunk401State] using h401
    simpa only [recordUpperSeedTailPrefix402] using
      recordUpperSeedTailChunk402Step.certifies prior
  have h403 : recordUpperSeedTailChunk403State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix403 := by
    have prior : recordUpperSeedTailChunk403Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix402 := by
      simpa only [
        recordUpperSeedTailChunk403Before,
        recordUpperSeedTailChunk402State] using h402
    simpa only [recordUpperSeedTailPrefix403] using
      recordUpperSeedTailChunk403Step.certifies prior
  have h404 : recordUpperSeedTailChunk404State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix404 := by
    have prior : recordUpperSeedTailChunk404Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix403 := by
      simpa only [
        recordUpperSeedTailChunk404Before,
        recordUpperSeedTailChunk403State] using h403
    simpa only [recordUpperSeedTailPrefix404] using
      recordUpperSeedTailChunk404Step.certifies prior
  have h405 : recordUpperSeedTailChunk405State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix405 := by
    have prior : recordUpperSeedTailChunk405Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix404 := by
      simpa only [
        recordUpperSeedTailChunk405Before,
        recordUpperSeedTailChunk404State] using h404
    simpa only [recordUpperSeedTailPrefix405] using
      recordUpperSeedTailChunk405Step.certifies prior
  have h406 : recordUpperSeedTailChunk406State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix406 := by
    have prior : recordUpperSeedTailChunk406Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix405 := by
      simpa only [
        recordUpperSeedTailChunk406Before,
        recordUpperSeedTailChunk405State] using h405
    simpa only [recordUpperSeedTailPrefix406] using
      recordUpperSeedTailChunk406Step.certifies prior
  have h407 : recordUpperSeedTailChunk407State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix407 := by
    have prior : recordUpperSeedTailChunk407Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix406 := by
      simpa only [
        recordUpperSeedTailChunk407Before,
        recordUpperSeedTailChunk406State] using h406
    simpa only [recordUpperSeedTailPrefix407] using
      recordUpperSeedTailChunk407Step.certifies prior
  have h408 : recordUpperSeedTailChunk408State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix408 := by
    have prior : recordUpperSeedTailChunk408Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix407 := by
      simpa only [
        recordUpperSeedTailChunk408Before,
        recordUpperSeedTailChunk407State] using h407
    simpa only [recordUpperSeedTailPrefix408] using
      recordUpperSeedTailChunk408Step.certifies prior
  have h409 : recordUpperSeedTailChunk409State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix409 := by
    have prior : recordUpperSeedTailChunk409Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix408 := by
      simpa only [
        recordUpperSeedTailChunk409Before,
        recordUpperSeedTailChunk408State] using h408
    simpa only [recordUpperSeedTailPrefix409] using
      recordUpperSeedTailChunk409Step.certifies prior
  have h410 : recordUpperSeedTailChunk410State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix410 := by
    have prior : recordUpperSeedTailChunk410Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix409 := by
      simpa only [
        recordUpperSeedTailChunk410Before,
        recordUpperSeedTailChunk409State] using h409
    simpa only [recordUpperSeedTailPrefix410] using
      recordUpperSeedTailChunk410Step.certifies prior
  have h411 : recordUpperSeedTailChunk411State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix411 := by
    have prior : recordUpperSeedTailChunk411Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix410 := by
      simpa only [
        recordUpperSeedTailChunk411Before,
        recordUpperSeedTailChunk410State] using h410
    simpa only [recordUpperSeedTailPrefix411] using
      recordUpperSeedTailChunk411Step.certifies prior
  have h412 : recordUpperSeedTailChunk412State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix412 := by
    have prior : recordUpperSeedTailChunk412Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix411 := by
      simpa only [
        recordUpperSeedTailChunk412Before,
        recordUpperSeedTailChunk411State] using h411
    simpa only [recordUpperSeedTailPrefix412] using
      recordUpperSeedTailChunk412Step.certifies prior
  have h413 : recordUpperSeedTailChunk413State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix413 := by
    have prior : recordUpperSeedTailChunk413Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix412 := by
      simpa only [
        recordUpperSeedTailChunk413Before,
        recordUpperSeedTailChunk412State] using h412
    simpa only [recordUpperSeedTailPrefix413] using
      recordUpperSeedTailChunk413Step.certifies prior
  have h414 : recordUpperSeedTailChunk414State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix414 := by
    have prior : recordUpperSeedTailChunk414Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix413 := by
      simpa only [
        recordUpperSeedTailChunk414Before,
        recordUpperSeedTailChunk413State] using h413
    simpa only [recordUpperSeedTailPrefix414] using
      recordUpperSeedTailChunk414Step.certifies prior
  have h415 : recordUpperSeedTailChunk415State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix415 := by
    have prior : recordUpperSeedTailChunk415Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix414 := by
      simpa only [
        recordUpperSeedTailChunk415Before,
        recordUpperSeedTailChunk414State] using h414
    simpa only [recordUpperSeedTailPrefix415] using
      recordUpperSeedTailChunk415Step.certifies prior
  have h416 : recordUpperSeedTailChunk416State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix416 := by
    have prior : recordUpperSeedTailChunk416Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix415 := by
      simpa only [
        recordUpperSeedTailChunk416Before,
        recordUpperSeedTailChunk415State] using h415
    simpa only [recordUpperSeedTailPrefix416] using
      recordUpperSeedTailChunk416Step.certifies prior
  have h417 : recordUpperSeedTailChunk417State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix417 := by
    have prior : recordUpperSeedTailChunk417Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix416 := by
      simpa only [
        recordUpperSeedTailChunk417Before,
        recordUpperSeedTailChunk416State] using h416
    simpa only [recordUpperSeedTailPrefix417] using
      recordUpperSeedTailChunk417Step.certifies prior
  have h418 : recordUpperSeedTailChunk418State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix418 := by
    have prior : recordUpperSeedTailChunk418Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix417 := by
      simpa only [
        recordUpperSeedTailChunk418Before,
        recordUpperSeedTailChunk417State] using h417
    simpa only [recordUpperSeedTailPrefix418] using
      recordUpperSeedTailChunk418Step.certifies prior
  have h419 : recordUpperSeedTailChunk419State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix419 := by
    have prior : recordUpperSeedTailChunk419Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix418 := by
      simpa only [
        recordUpperSeedTailChunk419Before,
        recordUpperSeedTailChunk418State] using h418
    simpa only [recordUpperSeedTailPrefix419] using
      recordUpperSeedTailChunk419Step.certifies prior
  have h420 : recordUpperSeedTailChunk420State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix420 := by
    have prior : recordUpperSeedTailChunk420Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix419 := by
      simpa only [
        recordUpperSeedTailChunk420Before,
        recordUpperSeedTailChunk419State] using h419
    simpa only [recordUpperSeedTailPrefix420] using
      recordUpperSeedTailChunk420Step.certifies prior
  have h421 : recordUpperSeedTailChunk421State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix421 := by
    have prior : recordUpperSeedTailChunk421Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix420 := by
      simpa only [
        recordUpperSeedTailChunk421Before,
        recordUpperSeedTailChunk420State] using h420
    simpa only [recordUpperSeedTailPrefix421] using
      recordUpperSeedTailChunk421Step.certifies prior
  have h422 : recordUpperSeedTailChunk422State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix422 := by
    have prior : recordUpperSeedTailChunk422Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix421 := by
      simpa only [
        recordUpperSeedTailChunk422Before,
        recordUpperSeedTailChunk421State] using h421
    simpa only [recordUpperSeedTailPrefix422] using
      recordUpperSeedTailChunk422Step.certifies prior
  have h423 : recordUpperSeedTailChunk423State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix423 := by
    have prior : recordUpperSeedTailChunk423Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix422 := by
      simpa only [
        recordUpperSeedTailChunk423Before,
        recordUpperSeedTailChunk422State] using h422
    simpa only [recordUpperSeedTailPrefix423] using
      recordUpperSeedTailChunk423Step.certifies prior
  have h424 : recordUpperSeedTailChunk424State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix424 := by
    have prior : recordUpperSeedTailChunk424Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix423 := by
      simpa only [
        recordUpperSeedTailChunk424Before,
        recordUpperSeedTailChunk423State] using h423
    simpa only [recordUpperSeedTailPrefix424] using
      recordUpperSeedTailChunk424Step.certifies prior
  have h425 : recordUpperSeedTailChunk425State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix425 := by
    have prior : recordUpperSeedTailChunk425Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix424 := by
      simpa only [
        recordUpperSeedTailChunk425Before,
        recordUpperSeedTailChunk424State] using h424
    simpa only [recordUpperSeedTailPrefix425] using
      recordUpperSeedTailChunk425Step.certifies prior
  have h426 : recordUpperSeedTailChunk426State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix426 := by
    have prior : recordUpperSeedTailChunk426Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix425 := by
      simpa only [
        recordUpperSeedTailChunk426Before,
        recordUpperSeedTailChunk425State] using h425
    simpa only [recordUpperSeedTailPrefix426] using
      recordUpperSeedTailChunk426Step.certifies prior
  have h427 : recordUpperSeedTailChunk427State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix427 := by
    have prior : recordUpperSeedTailChunk427Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix426 := by
      simpa only [
        recordUpperSeedTailChunk427Before,
        recordUpperSeedTailChunk426State] using h426
    simpa only [recordUpperSeedTailPrefix427] using
      recordUpperSeedTailChunk427Step.certifies prior
  have h428 : recordUpperSeedTailChunk428State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix428 := by
    have prior : recordUpperSeedTailChunk428Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix427 := by
      simpa only [
        recordUpperSeedTailChunk428Before,
        recordUpperSeedTailChunk427State] using h427
    simpa only [recordUpperSeedTailPrefix428] using
      recordUpperSeedTailChunk428Step.certifies prior
  have h429 : recordUpperSeedTailChunk429State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix429 := by
    have prior : recordUpperSeedTailChunk429Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix428 := by
      simpa only [
        recordUpperSeedTailChunk429Before,
        recordUpperSeedTailChunk428State] using h428
    simpa only [recordUpperSeedTailPrefix429] using
      recordUpperSeedTailChunk429Step.certifies prior
  have h430 : recordUpperSeedTailChunk430State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix430 := by
    have prior : recordUpperSeedTailChunk430Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix429 := by
      simpa only [
        recordUpperSeedTailChunk430Before,
        recordUpperSeedTailChunk429State] using h429
    simpa only [recordUpperSeedTailPrefix430] using
      recordUpperSeedTailChunk430Step.certifies prior
  have h431 : recordUpperSeedTailChunk431State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix431 := by
    have prior : recordUpperSeedTailChunk431Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix430 := by
      simpa only [
        recordUpperSeedTailChunk431Before,
        recordUpperSeedTailChunk430State] using h430
    simpa only [recordUpperSeedTailPrefix431] using
      recordUpperSeedTailChunk431Step.certifies prior
  have h432 : recordUpperSeedTailChunk432State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix432 := by
    have prior : recordUpperSeedTailChunk432Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix431 := by
      simpa only [
        recordUpperSeedTailChunk432Before,
        recordUpperSeedTailChunk431State] using h431
    simpa only [recordUpperSeedTailPrefix432] using
      recordUpperSeedTailChunk432Step.certifies prior
  have h433 : recordUpperSeedTailChunk433State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix433 := by
    have prior : recordUpperSeedTailChunk433Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix432 := by
      simpa only [
        recordUpperSeedTailChunk433Before,
        recordUpperSeedTailChunk432State] using h432
    simpa only [recordUpperSeedTailPrefix433] using
      recordUpperSeedTailChunk433Step.certifies prior
  have h434 : recordUpperSeedTailChunk434State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix434 := by
    have prior : recordUpperSeedTailChunk434Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix433 := by
      simpa only [
        recordUpperSeedTailChunk434Before,
        recordUpperSeedTailChunk433State] using h433
    simpa only [recordUpperSeedTailPrefix434] using
      recordUpperSeedTailChunk434Step.certifies prior
  have h435 : recordUpperSeedTailChunk435State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix435 := by
    have prior : recordUpperSeedTailChunk435Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix434 := by
      simpa only [
        recordUpperSeedTailChunk435Before,
        recordUpperSeedTailChunk434State] using h434
    simpa only [recordUpperSeedTailPrefix435] using
      recordUpperSeedTailChunk435Step.certifies prior
  have h436 : recordUpperSeedTailChunk436State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix436 := by
    have prior : recordUpperSeedTailChunk436Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix435 := by
      simpa only [
        recordUpperSeedTailChunk436Before,
        recordUpperSeedTailChunk435State] using h435
    simpa only [recordUpperSeedTailPrefix436] using
      recordUpperSeedTailChunk436Step.certifies prior
  have h437 : recordUpperSeedTailChunk437State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix437 := by
    have prior : recordUpperSeedTailChunk437Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix436 := by
      simpa only [
        recordUpperSeedTailChunk437Before,
        recordUpperSeedTailChunk436State] using h436
    simpa only [recordUpperSeedTailPrefix437] using
      recordUpperSeedTailChunk437Step.certifies prior
  have h438 : recordUpperSeedTailChunk438State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix438 := by
    have prior : recordUpperSeedTailChunk438Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix437 := by
      simpa only [
        recordUpperSeedTailChunk438Before,
        recordUpperSeedTailChunk437State] using h437
    simpa only [recordUpperSeedTailPrefix438] using
      recordUpperSeedTailChunk438Step.certifies prior
  have h439 : recordUpperSeedTailChunk439State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix439 := by
    have prior : recordUpperSeedTailChunk439Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix438 := by
      simpa only [
        recordUpperSeedTailChunk439Before,
        recordUpperSeedTailChunk438State] using h438
    simpa only [recordUpperSeedTailPrefix439] using
      recordUpperSeedTailChunk439Step.certifies prior
  have h440 : recordUpperSeedTailChunk440State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix440 := by
    have prior : recordUpperSeedTailChunk440Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix439 := by
      simpa only [
        recordUpperSeedTailChunk440Before,
        recordUpperSeedTailChunk439State] using h439
    simpa only [recordUpperSeedTailPrefix440] using
      recordUpperSeedTailChunk440Step.certifies prior
  exact h440

end PrimeFactorUnimodality
