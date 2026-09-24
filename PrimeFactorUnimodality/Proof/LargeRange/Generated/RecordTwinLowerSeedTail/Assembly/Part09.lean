import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Assembly.Part08
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part360

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-lower-seed.json` (semantic SHA-256 `3ce105dad06099400dfd2e30c65d47c6e02828915452a8459553c3bb0eb78b73`, excluding elapsed time). Semantic tail assembly group 9. -/

namespace PrimeFactorUnimodality

theorem recordLowerSeedTailGroup09_semantic :
    recordLowerSeedTailChunk360State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix360 := by
  have h321 : recordLowerSeedTailChunk321State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix321 := by
    have boundary : recordLowerSeedTailChunk321Before =
        recordLowerSeedTailChunk320State := by rfl
    exact recordLowerSeedTailChunk321Step.certifies
      (boundary.trans recordLowerSeedTailGroup08_semantic)
  have h322 : recordLowerSeedTailChunk322State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix322 := by
    have boundary : recordLowerSeedTailChunk322Before =
        recordLowerSeedTailChunk321State := by rfl
    exact recordLowerSeedTailChunk322Step.certifies
      (boundary.trans h321)
  have h323 : recordLowerSeedTailChunk323State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix323 := by
    have boundary : recordLowerSeedTailChunk323Before =
        recordLowerSeedTailChunk322State := by rfl
    exact recordLowerSeedTailChunk323Step.certifies
      (boundary.trans h322)
  have h324 : recordLowerSeedTailChunk324State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix324 := by
    have boundary : recordLowerSeedTailChunk324Before =
        recordLowerSeedTailChunk323State := by rfl
    exact recordLowerSeedTailChunk324Step.certifies
      (boundary.trans h323)
  have h325 : recordLowerSeedTailChunk325State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix325 := by
    have boundary : recordLowerSeedTailChunk325Before =
        recordLowerSeedTailChunk324State := by rfl
    exact recordLowerSeedTailChunk325Step.certifies
      (boundary.trans h324)
  have h326 : recordLowerSeedTailChunk326State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix326 := by
    have boundary : recordLowerSeedTailChunk326Before =
        recordLowerSeedTailChunk325State := by rfl
    exact recordLowerSeedTailChunk326Step.certifies
      (boundary.trans h325)
  have h327 : recordLowerSeedTailChunk327State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix327 := by
    have boundary : recordLowerSeedTailChunk327Before =
        recordLowerSeedTailChunk326State := by rfl
    exact recordLowerSeedTailChunk327Step.certifies
      (boundary.trans h326)
  have h328 : recordLowerSeedTailChunk328State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix328 := by
    have boundary : recordLowerSeedTailChunk328Before =
        recordLowerSeedTailChunk327State := by rfl
    exact recordLowerSeedTailChunk328Step.certifies
      (boundary.trans h327)
  have h329 : recordLowerSeedTailChunk329State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix329 := by
    have boundary : recordLowerSeedTailChunk329Before =
        recordLowerSeedTailChunk328State := by rfl
    exact recordLowerSeedTailChunk329Step.certifies
      (boundary.trans h328)
  have h330 : recordLowerSeedTailChunk330State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix330 := by
    have boundary : recordLowerSeedTailChunk330Before =
        recordLowerSeedTailChunk329State := by rfl
    exact recordLowerSeedTailChunk330Step.certifies
      (boundary.trans h329)
  have h331 : recordLowerSeedTailChunk331State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix331 := by
    have boundary : recordLowerSeedTailChunk331Before =
        recordLowerSeedTailChunk330State := by rfl
    exact recordLowerSeedTailChunk331Step.certifies
      (boundary.trans h330)
  have h332 : recordLowerSeedTailChunk332State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix332 := by
    have boundary : recordLowerSeedTailChunk332Before =
        recordLowerSeedTailChunk331State := by rfl
    exact recordLowerSeedTailChunk332Step.certifies
      (boundary.trans h331)
  have h333 : recordLowerSeedTailChunk333State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix333 := by
    have boundary : recordLowerSeedTailChunk333Before =
        recordLowerSeedTailChunk332State := by rfl
    exact recordLowerSeedTailChunk333Step.certifies
      (boundary.trans h332)
  have h334 : recordLowerSeedTailChunk334State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix334 := by
    have boundary : recordLowerSeedTailChunk334Before =
        recordLowerSeedTailChunk333State := by rfl
    exact recordLowerSeedTailChunk334Step.certifies
      (boundary.trans h333)
  have h335 : recordLowerSeedTailChunk335State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix335 := by
    have boundary : recordLowerSeedTailChunk335Before =
        recordLowerSeedTailChunk334State := by rfl
    exact recordLowerSeedTailChunk335Step.certifies
      (boundary.trans h334)
  have h336 : recordLowerSeedTailChunk336State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix336 := by
    have boundary : recordLowerSeedTailChunk336Before =
        recordLowerSeedTailChunk335State := by rfl
    exact recordLowerSeedTailChunk336Step.certifies
      (boundary.trans h335)
  have h337 : recordLowerSeedTailChunk337State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix337 := by
    have boundary : recordLowerSeedTailChunk337Before =
        recordLowerSeedTailChunk336State := by rfl
    exact recordLowerSeedTailChunk337Step.certifies
      (boundary.trans h336)
  have h338 : recordLowerSeedTailChunk338State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix338 := by
    have boundary : recordLowerSeedTailChunk338Before =
        recordLowerSeedTailChunk337State := by rfl
    exact recordLowerSeedTailChunk338Step.certifies
      (boundary.trans h337)
  have h339 : recordLowerSeedTailChunk339State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix339 := by
    have boundary : recordLowerSeedTailChunk339Before =
        recordLowerSeedTailChunk338State := by rfl
    exact recordLowerSeedTailChunk339Step.certifies
      (boundary.trans h338)
  have h340 : recordLowerSeedTailChunk340State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix340 := by
    have boundary : recordLowerSeedTailChunk340Before =
        recordLowerSeedTailChunk339State := by rfl
    exact recordLowerSeedTailChunk340Step.certifies
      (boundary.trans h339)
  have h341 : recordLowerSeedTailChunk341State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix341 := by
    have boundary : recordLowerSeedTailChunk341Before =
        recordLowerSeedTailChunk340State := by rfl
    exact recordLowerSeedTailChunk341Step.certifies
      (boundary.trans h340)
  have h342 : recordLowerSeedTailChunk342State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix342 := by
    have boundary : recordLowerSeedTailChunk342Before =
        recordLowerSeedTailChunk341State := by rfl
    exact recordLowerSeedTailChunk342Step.certifies
      (boundary.trans h341)
  have h343 : recordLowerSeedTailChunk343State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix343 := by
    have boundary : recordLowerSeedTailChunk343Before =
        recordLowerSeedTailChunk342State := by rfl
    exact recordLowerSeedTailChunk343Step.certifies
      (boundary.trans h342)
  have h344 : recordLowerSeedTailChunk344State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix344 := by
    have boundary : recordLowerSeedTailChunk344Before =
        recordLowerSeedTailChunk343State := by rfl
    exact recordLowerSeedTailChunk344Step.certifies
      (boundary.trans h343)
  have h345 : recordLowerSeedTailChunk345State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix345 := by
    have boundary : recordLowerSeedTailChunk345Before =
        recordLowerSeedTailChunk344State := by rfl
    exact recordLowerSeedTailChunk345Step.certifies
      (boundary.trans h344)
  have h346 : recordLowerSeedTailChunk346State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix346 := by
    have boundary : recordLowerSeedTailChunk346Before =
        recordLowerSeedTailChunk345State := by rfl
    exact recordLowerSeedTailChunk346Step.certifies
      (boundary.trans h345)
  have h347 : recordLowerSeedTailChunk347State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix347 := by
    have boundary : recordLowerSeedTailChunk347Before =
        recordLowerSeedTailChunk346State := by rfl
    exact recordLowerSeedTailChunk347Step.certifies
      (boundary.trans h346)
  have h348 : recordLowerSeedTailChunk348State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix348 := by
    have boundary : recordLowerSeedTailChunk348Before =
        recordLowerSeedTailChunk347State := by rfl
    exact recordLowerSeedTailChunk348Step.certifies
      (boundary.trans h347)
  have h349 : recordLowerSeedTailChunk349State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix349 := by
    have boundary : recordLowerSeedTailChunk349Before =
        recordLowerSeedTailChunk348State := by rfl
    exact recordLowerSeedTailChunk349Step.certifies
      (boundary.trans h348)
  have h350 : recordLowerSeedTailChunk350State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix350 := by
    have boundary : recordLowerSeedTailChunk350Before =
        recordLowerSeedTailChunk349State := by rfl
    exact recordLowerSeedTailChunk350Step.certifies
      (boundary.trans h349)
  have h351 : recordLowerSeedTailChunk351State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix351 := by
    have boundary : recordLowerSeedTailChunk351Before =
        recordLowerSeedTailChunk350State := by rfl
    exact recordLowerSeedTailChunk351Step.certifies
      (boundary.trans h350)
  have h352 : recordLowerSeedTailChunk352State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix352 := by
    have boundary : recordLowerSeedTailChunk352Before =
        recordLowerSeedTailChunk351State := by rfl
    exact recordLowerSeedTailChunk352Step.certifies
      (boundary.trans h351)
  have h353 : recordLowerSeedTailChunk353State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix353 := by
    have boundary : recordLowerSeedTailChunk353Before =
        recordLowerSeedTailChunk352State := by rfl
    exact recordLowerSeedTailChunk353Step.certifies
      (boundary.trans h352)
  have h354 : recordLowerSeedTailChunk354State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix354 := by
    have boundary : recordLowerSeedTailChunk354Before =
        recordLowerSeedTailChunk353State := by rfl
    exact recordLowerSeedTailChunk354Step.certifies
      (boundary.trans h353)
  have h355 : recordLowerSeedTailChunk355State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix355 := by
    have boundary : recordLowerSeedTailChunk355Before =
        recordLowerSeedTailChunk354State := by rfl
    exact recordLowerSeedTailChunk355Step.certifies
      (boundary.trans h354)
  have h356 : recordLowerSeedTailChunk356State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix356 := by
    have boundary : recordLowerSeedTailChunk356Before =
        recordLowerSeedTailChunk355State := by rfl
    exact recordLowerSeedTailChunk356Step.certifies
      (boundary.trans h355)
  have h357 : recordLowerSeedTailChunk357State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix357 := by
    have boundary : recordLowerSeedTailChunk357Before =
        recordLowerSeedTailChunk356State := by rfl
    exact recordLowerSeedTailChunk357Step.certifies
      (boundary.trans h356)
  have h358 : recordLowerSeedTailChunk358State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix358 := by
    have boundary : recordLowerSeedTailChunk358Before =
        recordLowerSeedTailChunk357State := by rfl
    exact recordLowerSeedTailChunk358Step.certifies
      (boundary.trans h357)
  have h359 : recordLowerSeedTailChunk359State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix359 := by
    have boundary : recordLowerSeedTailChunk359Before =
        recordLowerSeedTailChunk358State := by rfl
    exact recordLowerSeedTailChunk359Step.certifies
      (boundary.trans h358)
  have h360 : recordLowerSeedTailChunk360State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix360 := by
    have boundary : recordLowerSeedTailChunk360Before =
        recordLowerSeedTailChunk359State := by rfl
    exact recordLowerSeedTailChunk360Step.certifies
      (boundary.trans h359)
  exact h360

end PrimeFactorUnimodality
