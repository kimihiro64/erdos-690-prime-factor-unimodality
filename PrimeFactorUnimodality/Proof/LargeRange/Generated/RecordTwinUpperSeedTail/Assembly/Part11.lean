import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Assembly.Part10
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part440

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-upper-seed-base11.json` (semantic SHA-256 `493791f7b41de1500c4b830f254f9f92fd9c5d50d639b62aa2b46ca48591321f`, excluding elapsed time). Semantic tail assembly group 11. -/

namespace PrimeFactorUnimodality

theorem recordUpperSeedTailGroup11_semantic :
    recordUpperSeedTailChunk440State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix440 := by
  have h401 : recordUpperSeedTailChunk401State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix401 := by
    have boundary : recordUpperSeedTailChunk401Before =
        recordUpperSeedTailChunk400State := by rfl
    exact recordUpperSeedTailChunk401Step.certifies
      (boundary.trans recordUpperSeedTailGroup10_semantic)
  have h402 : recordUpperSeedTailChunk402State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix402 := by
    have boundary : recordUpperSeedTailChunk402Before =
        recordUpperSeedTailChunk401State := by rfl
    exact recordUpperSeedTailChunk402Step.certifies
      (boundary.trans h401)
  have h403 : recordUpperSeedTailChunk403State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix403 := by
    have boundary : recordUpperSeedTailChunk403Before =
        recordUpperSeedTailChunk402State := by rfl
    exact recordUpperSeedTailChunk403Step.certifies
      (boundary.trans h402)
  have h404 : recordUpperSeedTailChunk404State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix404 := by
    have boundary : recordUpperSeedTailChunk404Before =
        recordUpperSeedTailChunk403State := by rfl
    exact recordUpperSeedTailChunk404Step.certifies
      (boundary.trans h403)
  have h405 : recordUpperSeedTailChunk405State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix405 := by
    have boundary : recordUpperSeedTailChunk405Before =
        recordUpperSeedTailChunk404State := by rfl
    exact recordUpperSeedTailChunk405Step.certifies
      (boundary.trans h404)
  have h406 : recordUpperSeedTailChunk406State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix406 := by
    have boundary : recordUpperSeedTailChunk406Before =
        recordUpperSeedTailChunk405State := by rfl
    exact recordUpperSeedTailChunk406Step.certifies
      (boundary.trans h405)
  have h407 : recordUpperSeedTailChunk407State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix407 := by
    have boundary : recordUpperSeedTailChunk407Before =
        recordUpperSeedTailChunk406State := by rfl
    exact recordUpperSeedTailChunk407Step.certifies
      (boundary.trans h406)
  have h408 : recordUpperSeedTailChunk408State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix408 := by
    have boundary : recordUpperSeedTailChunk408Before =
        recordUpperSeedTailChunk407State := by rfl
    exact recordUpperSeedTailChunk408Step.certifies
      (boundary.trans h407)
  have h409 : recordUpperSeedTailChunk409State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix409 := by
    have boundary : recordUpperSeedTailChunk409Before =
        recordUpperSeedTailChunk408State := by rfl
    exact recordUpperSeedTailChunk409Step.certifies
      (boundary.trans h408)
  have h410 : recordUpperSeedTailChunk410State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix410 := by
    have boundary : recordUpperSeedTailChunk410Before =
        recordUpperSeedTailChunk409State := by rfl
    exact recordUpperSeedTailChunk410Step.certifies
      (boundary.trans h409)
  have h411 : recordUpperSeedTailChunk411State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix411 := by
    have boundary : recordUpperSeedTailChunk411Before =
        recordUpperSeedTailChunk410State := by rfl
    exact recordUpperSeedTailChunk411Step.certifies
      (boundary.trans h410)
  have h412 : recordUpperSeedTailChunk412State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix412 := by
    have boundary : recordUpperSeedTailChunk412Before =
        recordUpperSeedTailChunk411State := by rfl
    exact recordUpperSeedTailChunk412Step.certifies
      (boundary.trans h411)
  have h413 : recordUpperSeedTailChunk413State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix413 := by
    have boundary : recordUpperSeedTailChunk413Before =
        recordUpperSeedTailChunk412State := by rfl
    exact recordUpperSeedTailChunk413Step.certifies
      (boundary.trans h412)
  have h414 : recordUpperSeedTailChunk414State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix414 := by
    have boundary : recordUpperSeedTailChunk414Before =
        recordUpperSeedTailChunk413State := by rfl
    exact recordUpperSeedTailChunk414Step.certifies
      (boundary.trans h413)
  have h415 : recordUpperSeedTailChunk415State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix415 := by
    have boundary : recordUpperSeedTailChunk415Before =
        recordUpperSeedTailChunk414State := by rfl
    exact recordUpperSeedTailChunk415Step.certifies
      (boundary.trans h414)
  have h416 : recordUpperSeedTailChunk416State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix416 := by
    have boundary : recordUpperSeedTailChunk416Before =
        recordUpperSeedTailChunk415State := by rfl
    exact recordUpperSeedTailChunk416Step.certifies
      (boundary.trans h415)
  have h417 : recordUpperSeedTailChunk417State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix417 := by
    have boundary : recordUpperSeedTailChunk417Before =
        recordUpperSeedTailChunk416State := by rfl
    exact recordUpperSeedTailChunk417Step.certifies
      (boundary.trans h416)
  have h418 : recordUpperSeedTailChunk418State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix418 := by
    have boundary : recordUpperSeedTailChunk418Before =
        recordUpperSeedTailChunk417State := by rfl
    exact recordUpperSeedTailChunk418Step.certifies
      (boundary.trans h417)
  have h419 : recordUpperSeedTailChunk419State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix419 := by
    have boundary : recordUpperSeedTailChunk419Before =
        recordUpperSeedTailChunk418State := by rfl
    exact recordUpperSeedTailChunk419Step.certifies
      (boundary.trans h418)
  have h420 : recordUpperSeedTailChunk420State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix420 := by
    have boundary : recordUpperSeedTailChunk420Before =
        recordUpperSeedTailChunk419State := by rfl
    exact recordUpperSeedTailChunk420Step.certifies
      (boundary.trans h419)
  have h421 : recordUpperSeedTailChunk421State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix421 := by
    have boundary : recordUpperSeedTailChunk421Before =
        recordUpperSeedTailChunk420State := by rfl
    exact recordUpperSeedTailChunk421Step.certifies
      (boundary.trans h420)
  have h422 : recordUpperSeedTailChunk422State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix422 := by
    have boundary : recordUpperSeedTailChunk422Before =
        recordUpperSeedTailChunk421State := by rfl
    exact recordUpperSeedTailChunk422Step.certifies
      (boundary.trans h421)
  have h423 : recordUpperSeedTailChunk423State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix423 := by
    have boundary : recordUpperSeedTailChunk423Before =
        recordUpperSeedTailChunk422State := by rfl
    exact recordUpperSeedTailChunk423Step.certifies
      (boundary.trans h422)
  have h424 : recordUpperSeedTailChunk424State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix424 := by
    have boundary : recordUpperSeedTailChunk424Before =
        recordUpperSeedTailChunk423State := by rfl
    exact recordUpperSeedTailChunk424Step.certifies
      (boundary.trans h423)
  have h425 : recordUpperSeedTailChunk425State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix425 := by
    have boundary : recordUpperSeedTailChunk425Before =
        recordUpperSeedTailChunk424State := by rfl
    exact recordUpperSeedTailChunk425Step.certifies
      (boundary.trans h424)
  have h426 : recordUpperSeedTailChunk426State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix426 := by
    have boundary : recordUpperSeedTailChunk426Before =
        recordUpperSeedTailChunk425State := by rfl
    exact recordUpperSeedTailChunk426Step.certifies
      (boundary.trans h425)
  have h427 : recordUpperSeedTailChunk427State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix427 := by
    have boundary : recordUpperSeedTailChunk427Before =
        recordUpperSeedTailChunk426State := by rfl
    exact recordUpperSeedTailChunk427Step.certifies
      (boundary.trans h426)
  have h428 : recordUpperSeedTailChunk428State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix428 := by
    have boundary : recordUpperSeedTailChunk428Before =
        recordUpperSeedTailChunk427State := by rfl
    exact recordUpperSeedTailChunk428Step.certifies
      (boundary.trans h427)
  have h429 : recordUpperSeedTailChunk429State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix429 := by
    have boundary : recordUpperSeedTailChunk429Before =
        recordUpperSeedTailChunk428State := by rfl
    exact recordUpperSeedTailChunk429Step.certifies
      (boundary.trans h428)
  have h430 : recordUpperSeedTailChunk430State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix430 := by
    have boundary : recordUpperSeedTailChunk430Before =
        recordUpperSeedTailChunk429State := by rfl
    exact recordUpperSeedTailChunk430Step.certifies
      (boundary.trans h429)
  have h431 : recordUpperSeedTailChunk431State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix431 := by
    have boundary : recordUpperSeedTailChunk431Before =
        recordUpperSeedTailChunk430State := by rfl
    exact recordUpperSeedTailChunk431Step.certifies
      (boundary.trans h430)
  have h432 : recordUpperSeedTailChunk432State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix432 := by
    have boundary : recordUpperSeedTailChunk432Before =
        recordUpperSeedTailChunk431State := by rfl
    exact recordUpperSeedTailChunk432Step.certifies
      (boundary.trans h431)
  have h433 : recordUpperSeedTailChunk433State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix433 := by
    have boundary : recordUpperSeedTailChunk433Before =
        recordUpperSeedTailChunk432State := by rfl
    exact recordUpperSeedTailChunk433Step.certifies
      (boundary.trans h432)
  have h434 : recordUpperSeedTailChunk434State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix434 := by
    have boundary : recordUpperSeedTailChunk434Before =
        recordUpperSeedTailChunk433State := by rfl
    exact recordUpperSeedTailChunk434Step.certifies
      (boundary.trans h433)
  have h435 : recordUpperSeedTailChunk435State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix435 := by
    have boundary : recordUpperSeedTailChunk435Before =
        recordUpperSeedTailChunk434State := by rfl
    exact recordUpperSeedTailChunk435Step.certifies
      (boundary.trans h434)
  have h436 : recordUpperSeedTailChunk436State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix436 := by
    have boundary : recordUpperSeedTailChunk436Before =
        recordUpperSeedTailChunk435State := by rfl
    exact recordUpperSeedTailChunk436Step.certifies
      (boundary.trans h435)
  have h437 : recordUpperSeedTailChunk437State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix437 := by
    have boundary : recordUpperSeedTailChunk437Before =
        recordUpperSeedTailChunk436State := by rfl
    exact recordUpperSeedTailChunk437Step.certifies
      (boundary.trans h436)
  have h438 : recordUpperSeedTailChunk438State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix438 := by
    have boundary : recordUpperSeedTailChunk438Before =
        recordUpperSeedTailChunk437State := by rfl
    exact recordUpperSeedTailChunk438Step.certifies
      (boundary.trans h437)
  have h439 : recordUpperSeedTailChunk439State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix439 := by
    have boundary : recordUpperSeedTailChunk439Before =
        recordUpperSeedTailChunk438State := by rfl
    exact recordUpperSeedTailChunk439Step.certifies
      (boundary.trans h438)
  have h440 : recordUpperSeedTailChunk440State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix440 := by
    have boundary : recordUpperSeedTailChunk440Before =
        recordUpperSeedTailChunk439State := by rfl
    exact recordUpperSeedTailChunk440Step.certifies
      (boundary.trans h439)
  exact h440

end PrimeFactorUnimodality
