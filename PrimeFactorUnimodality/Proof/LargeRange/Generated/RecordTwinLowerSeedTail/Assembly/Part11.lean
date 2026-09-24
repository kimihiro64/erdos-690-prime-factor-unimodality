import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Assembly.Part10
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part440

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-lower-seed.json` (semantic SHA-256 `3ce105dad06099400dfd2e30c65d47c6e02828915452a8459553c3bb0eb78b73`, excluding elapsed time). Semantic tail assembly group 11. -/

namespace PrimeFactorUnimodality

theorem recordLowerSeedTailGroup11_semantic :
    recordLowerSeedTailChunk440State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix440 := by
  have h401 : recordLowerSeedTailChunk401State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix401 := by
    have boundary : recordLowerSeedTailChunk401Before =
        recordLowerSeedTailChunk400State := by rfl
    exact recordLowerSeedTailChunk401Step.certifies
      (boundary.trans recordLowerSeedTailGroup10_semantic)
  have h402 : recordLowerSeedTailChunk402State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix402 := by
    have boundary : recordLowerSeedTailChunk402Before =
        recordLowerSeedTailChunk401State := by rfl
    exact recordLowerSeedTailChunk402Step.certifies
      (boundary.trans h401)
  have h403 : recordLowerSeedTailChunk403State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix403 := by
    have boundary : recordLowerSeedTailChunk403Before =
        recordLowerSeedTailChunk402State := by rfl
    exact recordLowerSeedTailChunk403Step.certifies
      (boundary.trans h402)
  have h404 : recordLowerSeedTailChunk404State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix404 := by
    have boundary : recordLowerSeedTailChunk404Before =
        recordLowerSeedTailChunk403State := by rfl
    exact recordLowerSeedTailChunk404Step.certifies
      (boundary.trans h403)
  have h405 : recordLowerSeedTailChunk405State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix405 := by
    have boundary : recordLowerSeedTailChunk405Before =
        recordLowerSeedTailChunk404State := by rfl
    exact recordLowerSeedTailChunk405Step.certifies
      (boundary.trans h404)
  have h406 : recordLowerSeedTailChunk406State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix406 := by
    have boundary : recordLowerSeedTailChunk406Before =
        recordLowerSeedTailChunk405State := by rfl
    exact recordLowerSeedTailChunk406Step.certifies
      (boundary.trans h405)
  have h407 : recordLowerSeedTailChunk407State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix407 := by
    have boundary : recordLowerSeedTailChunk407Before =
        recordLowerSeedTailChunk406State := by rfl
    exact recordLowerSeedTailChunk407Step.certifies
      (boundary.trans h406)
  have h408 : recordLowerSeedTailChunk408State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix408 := by
    have boundary : recordLowerSeedTailChunk408Before =
        recordLowerSeedTailChunk407State := by rfl
    exact recordLowerSeedTailChunk408Step.certifies
      (boundary.trans h407)
  have h409 : recordLowerSeedTailChunk409State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix409 := by
    have boundary : recordLowerSeedTailChunk409Before =
        recordLowerSeedTailChunk408State := by rfl
    exact recordLowerSeedTailChunk409Step.certifies
      (boundary.trans h408)
  have h410 : recordLowerSeedTailChunk410State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix410 := by
    have boundary : recordLowerSeedTailChunk410Before =
        recordLowerSeedTailChunk409State := by rfl
    exact recordLowerSeedTailChunk410Step.certifies
      (boundary.trans h409)
  have h411 : recordLowerSeedTailChunk411State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix411 := by
    have boundary : recordLowerSeedTailChunk411Before =
        recordLowerSeedTailChunk410State := by rfl
    exact recordLowerSeedTailChunk411Step.certifies
      (boundary.trans h410)
  have h412 : recordLowerSeedTailChunk412State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix412 := by
    have boundary : recordLowerSeedTailChunk412Before =
        recordLowerSeedTailChunk411State := by rfl
    exact recordLowerSeedTailChunk412Step.certifies
      (boundary.trans h411)
  have h413 : recordLowerSeedTailChunk413State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix413 := by
    have boundary : recordLowerSeedTailChunk413Before =
        recordLowerSeedTailChunk412State := by rfl
    exact recordLowerSeedTailChunk413Step.certifies
      (boundary.trans h412)
  have h414 : recordLowerSeedTailChunk414State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix414 := by
    have boundary : recordLowerSeedTailChunk414Before =
        recordLowerSeedTailChunk413State := by rfl
    exact recordLowerSeedTailChunk414Step.certifies
      (boundary.trans h413)
  have h415 : recordLowerSeedTailChunk415State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix415 := by
    have boundary : recordLowerSeedTailChunk415Before =
        recordLowerSeedTailChunk414State := by rfl
    exact recordLowerSeedTailChunk415Step.certifies
      (boundary.trans h414)
  have h416 : recordLowerSeedTailChunk416State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix416 := by
    have boundary : recordLowerSeedTailChunk416Before =
        recordLowerSeedTailChunk415State := by rfl
    exact recordLowerSeedTailChunk416Step.certifies
      (boundary.trans h415)
  have h417 : recordLowerSeedTailChunk417State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix417 := by
    have boundary : recordLowerSeedTailChunk417Before =
        recordLowerSeedTailChunk416State := by rfl
    exact recordLowerSeedTailChunk417Step.certifies
      (boundary.trans h416)
  have h418 : recordLowerSeedTailChunk418State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix418 := by
    have boundary : recordLowerSeedTailChunk418Before =
        recordLowerSeedTailChunk417State := by rfl
    exact recordLowerSeedTailChunk418Step.certifies
      (boundary.trans h417)
  have h419 : recordLowerSeedTailChunk419State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix419 := by
    have boundary : recordLowerSeedTailChunk419Before =
        recordLowerSeedTailChunk418State := by rfl
    exact recordLowerSeedTailChunk419Step.certifies
      (boundary.trans h418)
  have h420 : recordLowerSeedTailChunk420State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix420 := by
    have boundary : recordLowerSeedTailChunk420Before =
        recordLowerSeedTailChunk419State := by rfl
    exact recordLowerSeedTailChunk420Step.certifies
      (boundary.trans h419)
  have h421 : recordLowerSeedTailChunk421State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix421 := by
    have boundary : recordLowerSeedTailChunk421Before =
        recordLowerSeedTailChunk420State := by rfl
    exact recordLowerSeedTailChunk421Step.certifies
      (boundary.trans h420)
  have h422 : recordLowerSeedTailChunk422State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix422 := by
    have boundary : recordLowerSeedTailChunk422Before =
        recordLowerSeedTailChunk421State := by rfl
    exact recordLowerSeedTailChunk422Step.certifies
      (boundary.trans h421)
  have h423 : recordLowerSeedTailChunk423State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix423 := by
    have boundary : recordLowerSeedTailChunk423Before =
        recordLowerSeedTailChunk422State := by rfl
    exact recordLowerSeedTailChunk423Step.certifies
      (boundary.trans h422)
  have h424 : recordLowerSeedTailChunk424State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix424 := by
    have boundary : recordLowerSeedTailChunk424Before =
        recordLowerSeedTailChunk423State := by rfl
    exact recordLowerSeedTailChunk424Step.certifies
      (boundary.trans h423)
  have h425 : recordLowerSeedTailChunk425State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix425 := by
    have boundary : recordLowerSeedTailChunk425Before =
        recordLowerSeedTailChunk424State := by rfl
    exact recordLowerSeedTailChunk425Step.certifies
      (boundary.trans h424)
  have h426 : recordLowerSeedTailChunk426State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix426 := by
    have boundary : recordLowerSeedTailChunk426Before =
        recordLowerSeedTailChunk425State := by rfl
    exact recordLowerSeedTailChunk426Step.certifies
      (boundary.trans h425)
  have h427 : recordLowerSeedTailChunk427State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix427 := by
    have boundary : recordLowerSeedTailChunk427Before =
        recordLowerSeedTailChunk426State := by rfl
    exact recordLowerSeedTailChunk427Step.certifies
      (boundary.trans h426)
  have h428 : recordLowerSeedTailChunk428State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix428 := by
    have boundary : recordLowerSeedTailChunk428Before =
        recordLowerSeedTailChunk427State := by rfl
    exact recordLowerSeedTailChunk428Step.certifies
      (boundary.trans h427)
  have h429 : recordLowerSeedTailChunk429State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix429 := by
    have boundary : recordLowerSeedTailChunk429Before =
        recordLowerSeedTailChunk428State := by rfl
    exact recordLowerSeedTailChunk429Step.certifies
      (boundary.trans h428)
  have h430 : recordLowerSeedTailChunk430State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix430 := by
    have boundary : recordLowerSeedTailChunk430Before =
        recordLowerSeedTailChunk429State := by rfl
    exact recordLowerSeedTailChunk430Step.certifies
      (boundary.trans h429)
  have h431 : recordLowerSeedTailChunk431State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix431 := by
    have boundary : recordLowerSeedTailChunk431Before =
        recordLowerSeedTailChunk430State := by rfl
    exact recordLowerSeedTailChunk431Step.certifies
      (boundary.trans h430)
  have h432 : recordLowerSeedTailChunk432State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix432 := by
    have boundary : recordLowerSeedTailChunk432Before =
        recordLowerSeedTailChunk431State := by rfl
    exact recordLowerSeedTailChunk432Step.certifies
      (boundary.trans h431)
  have h433 : recordLowerSeedTailChunk433State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix433 := by
    have boundary : recordLowerSeedTailChunk433Before =
        recordLowerSeedTailChunk432State := by rfl
    exact recordLowerSeedTailChunk433Step.certifies
      (boundary.trans h432)
  have h434 : recordLowerSeedTailChunk434State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix434 := by
    have boundary : recordLowerSeedTailChunk434Before =
        recordLowerSeedTailChunk433State := by rfl
    exact recordLowerSeedTailChunk434Step.certifies
      (boundary.trans h433)
  have h435 : recordLowerSeedTailChunk435State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix435 := by
    have boundary : recordLowerSeedTailChunk435Before =
        recordLowerSeedTailChunk434State := by rfl
    exact recordLowerSeedTailChunk435Step.certifies
      (boundary.trans h434)
  have h436 : recordLowerSeedTailChunk436State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix436 := by
    have boundary : recordLowerSeedTailChunk436Before =
        recordLowerSeedTailChunk435State := by rfl
    exact recordLowerSeedTailChunk436Step.certifies
      (boundary.trans h435)
  have h437 : recordLowerSeedTailChunk437State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix437 := by
    have boundary : recordLowerSeedTailChunk437Before =
        recordLowerSeedTailChunk436State := by rfl
    exact recordLowerSeedTailChunk437Step.certifies
      (boundary.trans h436)
  have h438 : recordLowerSeedTailChunk438State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix438 := by
    have boundary : recordLowerSeedTailChunk438Before =
        recordLowerSeedTailChunk437State := by rfl
    exact recordLowerSeedTailChunk438Step.certifies
      (boundary.trans h437)
  have h439 : recordLowerSeedTailChunk439State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix439 := by
    have boundary : recordLowerSeedTailChunk439Before =
        recordLowerSeedTailChunk438State := by rfl
    exact recordLowerSeedTailChunk439Step.certifies
      (boundary.trans h438)
  have h440 : recordLowerSeedTailChunk440State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix440 := by
    have boundary : recordLowerSeedTailChunk440Before =
        recordLowerSeedTailChunk439State := by rfl
    exact recordLowerSeedTailChunk440Step.certifies
      (boundary.trans h439)
  exact h440

end PrimeFactorUnimodality
