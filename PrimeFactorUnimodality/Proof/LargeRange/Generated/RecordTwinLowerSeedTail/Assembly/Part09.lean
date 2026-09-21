import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Assembly.Part08
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part360

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-lower-seed.json` (semantic SHA-256 `3ce105dad06099400dfd2e30c65d47c6e02828915452a8459553c3bb0eb78b73`, excluding elapsed time). Semantic tail assembly group 9. -/

namespace PrimeFactorUnimodality

theorem recordLowerSeedTailGroup09_semantic :
    recordLowerSeedTailChunk360State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix360 := by
  have h321 : recordLowerSeedTailChunk321State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix321 := by
    have prior : recordLowerSeedTailChunk321Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix320 := by
      simpa only [
        recordLowerSeedTailChunk321Before,
        recordLowerSeedTailChunk320State] using recordLowerSeedTailGroup08_semantic
    simpa only [recordLowerSeedTailPrefix321] using
      recordLowerSeedTailChunk321Step.certifies prior
  have h322 : recordLowerSeedTailChunk322State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix322 := by
    have prior : recordLowerSeedTailChunk322Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix321 := by
      simpa only [
        recordLowerSeedTailChunk322Before,
        recordLowerSeedTailChunk321State] using h321
    simpa only [recordLowerSeedTailPrefix322] using
      recordLowerSeedTailChunk322Step.certifies prior
  have h323 : recordLowerSeedTailChunk323State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix323 := by
    have prior : recordLowerSeedTailChunk323Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix322 := by
      simpa only [
        recordLowerSeedTailChunk323Before,
        recordLowerSeedTailChunk322State] using h322
    simpa only [recordLowerSeedTailPrefix323] using
      recordLowerSeedTailChunk323Step.certifies prior
  have h324 : recordLowerSeedTailChunk324State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix324 := by
    have prior : recordLowerSeedTailChunk324Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix323 := by
      simpa only [
        recordLowerSeedTailChunk324Before,
        recordLowerSeedTailChunk323State] using h323
    simpa only [recordLowerSeedTailPrefix324] using
      recordLowerSeedTailChunk324Step.certifies prior
  have h325 : recordLowerSeedTailChunk325State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix325 := by
    have prior : recordLowerSeedTailChunk325Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix324 := by
      simpa only [
        recordLowerSeedTailChunk325Before,
        recordLowerSeedTailChunk324State] using h324
    simpa only [recordLowerSeedTailPrefix325] using
      recordLowerSeedTailChunk325Step.certifies prior
  have h326 : recordLowerSeedTailChunk326State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix326 := by
    have prior : recordLowerSeedTailChunk326Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix325 := by
      simpa only [
        recordLowerSeedTailChunk326Before,
        recordLowerSeedTailChunk325State] using h325
    simpa only [recordLowerSeedTailPrefix326] using
      recordLowerSeedTailChunk326Step.certifies prior
  have h327 : recordLowerSeedTailChunk327State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix327 := by
    have prior : recordLowerSeedTailChunk327Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix326 := by
      simpa only [
        recordLowerSeedTailChunk327Before,
        recordLowerSeedTailChunk326State] using h326
    simpa only [recordLowerSeedTailPrefix327] using
      recordLowerSeedTailChunk327Step.certifies prior
  have h328 : recordLowerSeedTailChunk328State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix328 := by
    have prior : recordLowerSeedTailChunk328Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix327 := by
      simpa only [
        recordLowerSeedTailChunk328Before,
        recordLowerSeedTailChunk327State] using h327
    simpa only [recordLowerSeedTailPrefix328] using
      recordLowerSeedTailChunk328Step.certifies prior
  have h329 : recordLowerSeedTailChunk329State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix329 := by
    have prior : recordLowerSeedTailChunk329Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix328 := by
      simpa only [
        recordLowerSeedTailChunk329Before,
        recordLowerSeedTailChunk328State] using h328
    simpa only [recordLowerSeedTailPrefix329] using
      recordLowerSeedTailChunk329Step.certifies prior
  have h330 : recordLowerSeedTailChunk330State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix330 := by
    have prior : recordLowerSeedTailChunk330Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix329 := by
      simpa only [
        recordLowerSeedTailChunk330Before,
        recordLowerSeedTailChunk329State] using h329
    simpa only [recordLowerSeedTailPrefix330] using
      recordLowerSeedTailChunk330Step.certifies prior
  have h331 : recordLowerSeedTailChunk331State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix331 := by
    have prior : recordLowerSeedTailChunk331Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix330 := by
      simpa only [
        recordLowerSeedTailChunk331Before,
        recordLowerSeedTailChunk330State] using h330
    simpa only [recordLowerSeedTailPrefix331] using
      recordLowerSeedTailChunk331Step.certifies prior
  have h332 : recordLowerSeedTailChunk332State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix332 := by
    have prior : recordLowerSeedTailChunk332Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix331 := by
      simpa only [
        recordLowerSeedTailChunk332Before,
        recordLowerSeedTailChunk331State] using h331
    simpa only [recordLowerSeedTailPrefix332] using
      recordLowerSeedTailChunk332Step.certifies prior
  have h333 : recordLowerSeedTailChunk333State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix333 := by
    have prior : recordLowerSeedTailChunk333Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix332 := by
      simpa only [
        recordLowerSeedTailChunk333Before,
        recordLowerSeedTailChunk332State] using h332
    simpa only [recordLowerSeedTailPrefix333] using
      recordLowerSeedTailChunk333Step.certifies prior
  have h334 : recordLowerSeedTailChunk334State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix334 := by
    have prior : recordLowerSeedTailChunk334Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix333 := by
      simpa only [
        recordLowerSeedTailChunk334Before,
        recordLowerSeedTailChunk333State] using h333
    simpa only [recordLowerSeedTailPrefix334] using
      recordLowerSeedTailChunk334Step.certifies prior
  have h335 : recordLowerSeedTailChunk335State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix335 := by
    have prior : recordLowerSeedTailChunk335Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix334 := by
      simpa only [
        recordLowerSeedTailChunk335Before,
        recordLowerSeedTailChunk334State] using h334
    simpa only [recordLowerSeedTailPrefix335] using
      recordLowerSeedTailChunk335Step.certifies prior
  have h336 : recordLowerSeedTailChunk336State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix336 := by
    have prior : recordLowerSeedTailChunk336Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix335 := by
      simpa only [
        recordLowerSeedTailChunk336Before,
        recordLowerSeedTailChunk335State] using h335
    simpa only [recordLowerSeedTailPrefix336] using
      recordLowerSeedTailChunk336Step.certifies prior
  have h337 : recordLowerSeedTailChunk337State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix337 := by
    have prior : recordLowerSeedTailChunk337Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix336 := by
      simpa only [
        recordLowerSeedTailChunk337Before,
        recordLowerSeedTailChunk336State] using h336
    simpa only [recordLowerSeedTailPrefix337] using
      recordLowerSeedTailChunk337Step.certifies prior
  have h338 : recordLowerSeedTailChunk338State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix338 := by
    have prior : recordLowerSeedTailChunk338Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix337 := by
      simpa only [
        recordLowerSeedTailChunk338Before,
        recordLowerSeedTailChunk337State] using h337
    simpa only [recordLowerSeedTailPrefix338] using
      recordLowerSeedTailChunk338Step.certifies prior
  have h339 : recordLowerSeedTailChunk339State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix339 := by
    have prior : recordLowerSeedTailChunk339Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix338 := by
      simpa only [
        recordLowerSeedTailChunk339Before,
        recordLowerSeedTailChunk338State] using h338
    simpa only [recordLowerSeedTailPrefix339] using
      recordLowerSeedTailChunk339Step.certifies prior
  have h340 : recordLowerSeedTailChunk340State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix340 := by
    have prior : recordLowerSeedTailChunk340Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix339 := by
      simpa only [
        recordLowerSeedTailChunk340Before,
        recordLowerSeedTailChunk339State] using h339
    simpa only [recordLowerSeedTailPrefix340] using
      recordLowerSeedTailChunk340Step.certifies prior
  have h341 : recordLowerSeedTailChunk341State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix341 := by
    have prior : recordLowerSeedTailChunk341Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix340 := by
      simpa only [
        recordLowerSeedTailChunk341Before,
        recordLowerSeedTailChunk340State] using h340
    simpa only [recordLowerSeedTailPrefix341] using
      recordLowerSeedTailChunk341Step.certifies prior
  have h342 : recordLowerSeedTailChunk342State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix342 := by
    have prior : recordLowerSeedTailChunk342Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix341 := by
      simpa only [
        recordLowerSeedTailChunk342Before,
        recordLowerSeedTailChunk341State] using h341
    simpa only [recordLowerSeedTailPrefix342] using
      recordLowerSeedTailChunk342Step.certifies prior
  have h343 : recordLowerSeedTailChunk343State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix343 := by
    have prior : recordLowerSeedTailChunk343Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix342 := by
      simpa only [
        recordLowerSeedTailChunk343Before,
        recordLowerSeedTailChunk342State] using h342
    simpa only [recordLowerSeedTailPrefix343] using
      recordLowerSeedTailChunk343Step.certifies prior
  have h344 : recordLowerSeedTailChunk344State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix344 := by
    have prior : recordLowerSeedTailChunk344Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix343 := by
      simpa only [
        recordLowerSeedTailChunk344Before,
        recordLowerSeedTailChunk343State] using h343
    simpa only [recordLowerSeedTailPrefix344] using
      recordLowerSeedTailChunk344Step.certifies prior
  have h345 : recordLowerSeedTailChunk345State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix345 := by
    have prior : recordLowerSeedTailChunk345Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix344 := by
      simpa only [
        recordLowerSeedTailChunk345Before,
        recordLowerSeedTailChunk344State] using h344
    simpa only [recordLowerSeedTailPrefix345] using
      recordLowerSeedTailChunk345Step.certifies prior
  have h346 : recordLowerSeedTailChunk346State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix346 := by
    have prior : recordLowerSeedTailChunk346Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix345 := by
      simpa only [
        recordLowerSeedTailChunk346Before,
        recordLowerSeedTailChunk345State] using h345
    simpa only [recordLowerSeedTailPrefix346] using
      recordLowerSeedTailChunk346Step.certifies prior
  have h347 : recordLowerSeedTailChunk347State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix347 := by
    have prior : recordLowerSeedTailChunk347Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix346 := by
      simpa only [
        recordLowerSeedTailChunk347Before,
        recordLowerSeedTailChunk346State] using h346
    simpa only [recordLowerSeedTailPrefix347] using
      recordLowerSeedTailChunk347Step.certifies prior
  have h348 : recordLowerSeedTailChunk348State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix348 := by
    have prior : recordLowerSeedTailChunk348Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix347 := by
      simpa only [
        recordLowerSeedTailChunk348Before,
        recordLowerSeedTailChunk347State] using h347
    simpa only [recordLowerSeedTailPrefix348] using
      recordLowerSeedTailChunk348Step.certifies prior
  have h349 : recordLowerSeedTailChunk349State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix349 := by
    have prior : recordLowerSeedTailChunk349Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix348 := by
      simpa only [
        recordLowerSeedTailChunk349Before,
        recordLowerSeedTailChunk348State] using h348
    simpa only [recordLowerSeedTailPrefix349] using
      recordLowerSeedTailChunk349Step.certifies prior
  have h350 : recordLowerSeedTailChunk350State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix350 := by
    have prior : recordLowerSeedTailChunk350Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix349 := by
      simpa only [
        recordLowerSeedTailChunk350Before,
        recordLowerSeedTailChunk349State] using h349
    simpa only [recordLowerSeedTailPrefix350] using
      recordLowerSeedTailChunk350Step.certifies prior
  have h351 : recordLowerSeedTailChunk351State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix351 := by
    have prior : recordLowerSeedTailChunk351Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix350 := by
      simpa only [
        recordLowerSeedTailChunk351Before,
        recordLowerSeedTailChunk350State] using h350
    simpa only [recordLowerSeedTailPrefix351] using
      recordLowerSeedTailChunk351Step.certifies prior
  have h352 : recordLowerSeedTailChunk352State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix352 := by
    have prior : recordLowerSeedTailChunk352Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix351 := by
      simpa only [
        recordLowerSeedTailChunk352Before,
        recordLowerSeedTailChunk351State] using h351
    simpa only [recordLowerSeedTailPrefix352] using
      recordLowerSeedTailChunk352Step.certifies prior
  have h353 : recordLowerSeedTailChunk353State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix353 := by
    have prior : recordLowerSeedTailChunk353Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix352 := by
      simpa only [
        recordLowerSeedTailChunk353Before,
        recordLowerSeedTailChunk352State] using h352
    simpa only [recordLowerSeedTailPrefix353] using
      recordLowerSeedTailChunk353Step.certifies prior
  have h354 : recordLowerSeedTailChunk354State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix354 := by
    have prior : recordLowerSeedTailChunk354Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix353 := by
      simpa only [
        recordLowerSeedTailChunk354Before,
        recordLowerSeedTailChunk353State] using h353
    simpa only [recordLowerSeedTailPrefix354] using
      recordLowerSeedTailChunk354Step.certifies prior
  have h355 : recordLowerSeedTailChunk355State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix355 := by
    have prior : recordLowerSeedTailChunk355Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix354 := by
      simpa only [
        recordLowerSeedTailChunk355Before,
        recordLowerSeedTailChunk354State] using h354
    simpa only [recordLowerSeedTailPrefix355] using
      recordLowerSeedTailChunk355Step.certifies prior
  have h356 : recordLowerSeedTailChunk356State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix356 := by
    have prior : recordLowerSeedTailChunk356Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix355 := by
      simpa only [
        recordLowerSeedTailChunk356Before,
        recordLowerSeedTailChunk355State] using h355
    simpa only [recordLowerSeedTailPrefix356] using
      recordLowerSeedTailChunk356Step.certifies prior
  have h357 : recordLowerSeedTailChunk357State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix357 := by
    have prior : recordLowerSeedTailChunk357Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix356 := by
      simpa only [
        recordLowerSeedTailChunk357Before,
        recordLowerSeedTailChunk356State] using h356
    simpa only [recordLowerSeedTailPrefix357] using
      recordLowerSeedTailChunk357Step.certifies prior
  have h358 : recordLowerSeedTailChunk358State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix358 := by
    have prior : recordLowerSeedTailChunk358Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix357 := by
      simpa only [
        recordLowerSeedTailChunk358Before,
        recordLowerSeedTailChunk357State] using h357
    simpa only [recordLowerSeedTailPrefix358] using
      recordLowerSeedTailChunk358Step.certifies prior
  have h359 : recordLowerSeedTailChunk359State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix359 := by
    have prior : recordLowerSeedTailChunk359Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix358 := by
      simpa only [
        recordLowerSeedTailChunk359Before,
        recordLowerSeedTailChunk358State] using h358
    simpa only [recordLowerSeedTailPrefix359] using
      recordLowerSeedTailChunk359Step.certifies prior
  have h360 : recordLowerSeedTailChunk360State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix360 := by
    have prior : recordLowerSeedTailChunk360Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix359 := by
      simpa only [
        recordLowerSeedTailChunk360Before,
        recordLowerSeedTailChunk359State] using h359
    simpa only [recordLowerSeedTailPrefix360] using
      recordLowerSeedTailChunk360Step.certifies prior
  exact h360

end PrimeFactorUnimodality
