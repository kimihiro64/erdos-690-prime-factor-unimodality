import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Assembly.Part08
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part360

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-upper-seed-base11.json` (semantic SHA-256 `493791f7b41de1500c4b830f254f9f92fd9c5d50d639b62aa2b46ca48591321f`, excluding elapsed time). Semantic tail assembly group 9. -/

namespace PrimeFactorUnimodality

theorem recordUpperSeedTailGroup09_semantic :
    recordUpperSeedTailChunk360State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix360 := by
  have h321 : recordUpperSeedTailChunk321State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix321 := by
    have boundary : recordUpperSeedTailChunk321Before =
        recordUpperSeedTailChunk320State := by rfl
    exact recordUpperSeedTailChunk321Step.certifies
      (boundary.trans recordUpperSeedTailGroup08_semantic)
  have h322 : recordUpperSeedTailChunk322State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix322 := by
    have boundary : recordUpperSeedTailChunk322Before =
        recordUpperSeedTailChunk321State := by rfl
    exact recordUpperSeedTailChunk322Step.certifies
      (boundary.trans h321)
  have h323 : recordUpperSeedTailChunk323State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix323 := by
    have boundary : recordUpperSeedTailChunk323Before =
        recordUpperSeedTailChunk322State := by rfl
    exact recordUpperSeedTailChunk323Step.certifies
      (boundary.trans h322)
  have h324 : recordUpperSeedTailChunk324State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix324 := by
    have boundary : recordUpperSeedTailChunk324Before =
        recordUpperSeedTailChunk323State := by rfl
    exact recordUpperSeedTailChunk324Step.certifies
      (boundary.trans h323)
  have h325 : recordUpperSeedTailChunk325State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix325 := by
    have boundary : recordUpperSeedTailChunk325Before =
        recordUpperSeedTailChunk324State := by rfl
    exact recordUpperSeedTailChunk325Step.certifies
      (boundary.trans h324)
  have h326 : recordUpperSeedTailChunk326State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix326 := by
    have boundary : recordUpperSeedTailChunk326Before =
        recordUpperSeedTailChunk325State := by rfl
    exact recordUpperSeedTailChunk326Step.certifies
      (boundary.trans h325)
  have h327 : recordUpperSeedTailChunk327State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix327 := by
    have boundary : recordUpperSeedTailChunk327Before =
        recordUpperSeedTailChunk326State := by rfl
    exact recordUpperSeedTailChunk327Step.certifies
      (boundary.trans h326)
  have h328 : recordUpperSeedTailChunk328State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix328 := by
    have boundary : recordUpperSeedTailChunk328Before =
        recordUpperSeedTailChunk327State := by rfl
    exact recordUpperSeedTailChunk328Step.certifies
      (boundary.trans h327)
  have h329 : recordUpperSeedTailChunk329State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix329 := by
    have boundary : recordUpperSeedTailChunk329Before =
        recordUpperSeedTailChunk328State := by rfl
    exact recordUpperSeedTailChunk329Step.certifies
      (boundary.trans h328)
  have h330 : recordUpperSeedTailChunk330State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix330 := by
    have boundary : recordUpperSeedTailChunk330Before =
        recordUpperSeedTailChunk329State := by rfl
    exact recordUpperSeedTailChunk330Step.certifies
      (boundary.trans h329)
  have h331 : recordUpperSeedTailChunk331State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix331 := by
    have boundary : recordUpperSeedTailChunk331Before =
        recordUpperSeedTailChunk330State := by rfl
    exact recordUpperSeedTailChunk331Step.certifies
      (boundary.trans h330)
  have h332 : recordUpperSeedTailChunk332State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix332 := by
    have boundary : recordUpperSeedTailChunk332Before =
        recordUpperSeedTailChunk331State := by rfl
    exact recordUpperSeedTailChunk332Step.certifies
      (boundary.trans h331)
  have h333 : recordUpperSeedTailChunk333State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix333 := by
    have boundary : recordUpperSeedTailChunk333Before =
        recordUpperSeedTailChunk332State := by rfl
    exact recordUpperSeedTailChunk333Step.certifies
      (boundary.trans h332)
  have h334 : recordUpperSeedTailChunk334State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix334 := by
    have boundary : recordUpperSeedTailChunk334Before =
        recordUpperSeedTailChunk333State := by rfl
    exact recordUpperSeedTailChunk334Step.certifies
      (boundary.trans h333)
  have h335 : recordUpperSeedTailChunk335State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix335 := by
    have boundary : recordUpperSeedTailChunk335Before =
        recordUpperSeedTailChunk334State := by rfl
    exact recordUpperSeedTailChunk335Step.certifies
      (boundary.trans h334)
  have h336 : recordUpperSeedTailChunk336State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix336 := by
    have boundary : recordUpperSeedTailChunk336Before =
        recordUpperSeedTailChunk335State := by rfl
    exact recordUpperSeedTailChunk336Step.certifies
      (boundary.trans h335)
  have h337 : recordUpperSeedTailChunk337State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix337 := by
    have boundary : recordUpperSeedTailChunk337Before =
        recordUpperSeedTailChunk336State := by rfl
    exact recordUpperSeedTailChunk337Step.certifies
      (boundary.trans h336)
  have h338 : recordUpperSeedTailChunk338State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix338 := by
    have boundary : recordUpperSeedTailChunk338Before =
        recordUpperSeedTailChunk337State := by rfl
    exact recordUpperSeedTailChunk338Step.certifies
      (boundary.trans h337)
  have h339 : recordUpperSeedTailChunk339State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix339 := by
    have boundary : recordUpperSeedTailChunk339Before =
        recordUpperSeedTailChunk338State := by rfl
    exact recordUpperSeedTailChunk339Step.certifies
      (boundary.trans h338)
  have h340 : recordUpperSeedTailChunk340State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix340 := by
    have boundary : recordUpperSeedTailChunk340Before =
        recordUpperSeedTailChunk339State := by rfl
    exact recordUpperSeedTailChunk340Step.certifies
      (boundary.trans h339)
  have h341 : recordUpperSeedTailChunk341State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix341 := by
    have boundary : recordUpperSeedTailChunk341Before =
        recordUpperSeedTailChunk340State := by rfl
    exact recordUpperSeedTailChunk341Step.certifies
      (boundary.trans h340)
  have h342 : recordUpperSeedTailChunk342State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix342 := by
    have boundary : recordUpperSeedTailChunk342Before =
        recordUpperSeedTailChunk341State := by rfl
    exact recordUpperSeedTailChunk342Step.certifies
      (boundary.trans h341)
  have h343 : recordUpperSeedTailChunk343State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix343 := by
    have boundary : recordUpperSeedTailChunk343Before =
        recordUpperSeedTailChunk342State := by rfl
    exact recordUpperSeedTailChunk343Step.certifies
      (boundary.trans h342)
  have h344 : recordUpperSeedTailChunk344State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix344 := by
    have boundary : recordUpperSeedTailChunk344Before =
        recordUpperSeedTailChunk343State := by rfl
    exact recordUpperSeedTailChunk344Step.certifies
      (boundary.trans h343)
  have h345 : recordUpperSeedTailChunk345State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix345 := by
    have boundary : recordUpperSeedTailChunk345Before =
        recordUpperSeedTailChunk344State := by rfl
    exact recordUpperSeedTailChunk345Step.certifies
      (boundary.trans h344)
  have h346 : recordUpperSeedTailChunk346State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix346 := by
    have boundary : recordUpperSeedTailChunk346Before =
        recordUpperSeedTailChunk345State := by rfl
    exact recordUpperSeedTailChunk346Step.certifies
      (boundary.trans h345)
  have h347 : recordUpperSeedTailChunk347State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix347 := by
    have boundary : recordUpperSeedTailChunk347Before =
        recordUpperSeedTailChunk346State := by rfl
    exact recordUpperSeedTailChunk347Step.certifies
      (boundary.trans h346)
  have h348 : recordUpperSeedTailChunk348State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix348 := by
    have boundary : recordUpperSeedTailChunk348Before =
        recordUpperSeedTailChunk347State := by rfl
    exact recordUpperSeedTailChunk348Step.certifies
      (boundary.trans h347)
  have h349 : recordUpperSeedTailChunk349State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix349 := by
    have boundary : recordUpperSeedTailChunk349Before =
        recordUpperSeedTailChunk348State := by rfl
    exact recordUpperSeedTailChunk349Step.certifies
      (boundary.trans h348)
  have h350 : recordUpperSeedTailChunk350State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix350 := by
    have boundary : recordUpperSeedTailChunk350Before =
        recordUpperSeedTailChunk349State := by rfl
    exact recordUpperSeedTailChunk350Step.certifies
      (boundary.trans h349)
  have h351 : recordUpperSeedTailChunk351State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix351 := by
    have boundary : recordUpperSeedTailChunk351Before =
        recordUpperSeedTailChunk350State := by rfl
    exact recordUpperSeedTailChunk351Step.certifies
      (boundary.trans h350)
  have h352 : recordUpperSeedTailChunk352State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix352 := by
    have boundary : recordUpperSeedTailChunk352Before =
        recordUpperSeedTailChunk351State := by rfl
    exact recordUpperSeedTailChunk352Step.certifies
      (boundary.trans h351)
  have h353 : recordUpperSeedTailChunk353State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix353 := by
    have boundary : recordUpperSeedTailChunk353Before =
        recordUpperSeedTailChunk352State := by rfl
    exact recordUpperSeedTailChunk353Step.certifies
      (boundary.trans h352)
  have h354 : recordUpperSeedTailChunk354State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix354 := by
    have boundary : recordUpperSeedTailChunk354Before =
        recordUpperSeedTailChunk353State := by rfl
    exact recordUpperSeedTailChunk354Step.certifies
      (boundary.trans h353)
  have h355 : recordUpperSeedTailChunk355State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix355 := by
    have boundary : recordUpperSeedTailChunk355Before =
        recordUpperSeedTailChunk354State := by rfl
    exact recordUpperSeedTailChunk355Step.certifies
      (boundary.trans h354)
  have h356 : recordUpperSeedTailChunk356State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix356 := by
    have boundary : recordUpperSeedTailChunk356Before =
        recordUpperSeedTailChunk355State := by rfl
    exact recordUpperSeedTailChunk356Step.certifies
      (boundary.trans h355)
  have h357 : recordUpperSeedTailChunk357State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix357 := by
    have boundary : recordUpperSeedTailChunk357Before =
        recordUpperSeedTailChunk356State := by rfl
    exact recordUpperSeedTailChunk357Step.certifies
      (boundary.trans h356)
  have h358 : recordUpperSeedTailChunk358State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix358 := by
    have boundary : recordUpperSeedTailChunk358Before =
        recordUpperSeedTailChunk357State := by rfl
    exact recordUpperSeedTailChunk358Step.certifies
      (boundary.trans h357)
  have h359 : recordUpperSeedTailChunk359State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix359 := by
    have boundary : recordUpperSeedTailChunk359Before =
        recordUpperSeedTailChunk358State := by rfl
    exact recordUpperSeedTailChunk359Step.certifies
      (boundary.trans h358)
  have h360 : recordUpperSeedTailChunk360State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix360 := by
    have boundary : recordUpperSeedTailChunk360Before =
        recordUpperSeedTailChunk359State := by rfl
    exact recordUpperSeedTailChunk360Step.certifies
      (boundary.trans h359)
  exact h360

end PrimeFactorUnimodality
