import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Assembly.Part08
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part360

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-upper-seed-base11.json` (semantic SHA-256 `493791f7b41de1500c4b830f254f9f92fd9c5d50d639b62aa2b46ca48591321f`, excluding elapsed time). Semantic tail assembly group 9. -/

namespace PrimeFactorUnimodality

theorem recordUpperSeedTailGroup09_semantic :
    recordUpperSeedTailChunk360State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix360 := by
  have h321 : recordUpperSeedTailChunk321State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix321 := by
    have prior : recordUpperSeedTailChunk321Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix320 := by
      simpa only [
        recordUpperSeedTailChunk321Before,
        recordUpperSeedTailChunk320State] using recordUpperSeedTailGroup08_semantic
    simpa only [recordUpperSeedTailPrefix321] using
      recordUpperSeedTailChunk321Step.certifies prior
  have h322 : recordUpperSeedTailChunk322State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix322 := by
    have prior : recordUpperSeedTailChunk322Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix321 := by
      simpa only [
        recordUpperSeedTailChunk322Before,
        recordUpperSeedTailChunk321State] using h321
    simpa only [recordUpperSeedTailPrefix322] using
      recordUpperSeedTailChunk322Step.certifies prior
  have h323 : recordUpperSeedTailChunk323State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix323 := by
    have prior : recordUpperSeedTailChunk323Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix322 := by
      simpa only [
        recordUpperSeedTailChunk323Before,
        recordUpperSeedTailChunk322State] using h322
    simpa only [recordUpperSeedTailPrefix323] using
      recordUpperSeedTailChunk323Step.certifies prior
  have h324 : recordUpperSeedTailChunk324State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix324 := by
    have prior : recordUpperSeedTailChunk324Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix323 := by
      simpa only [
        recordUpperSeedTailChunk324Before,
        recordUpperSeedTailChunk323State] using h323
    simpa only [recordUpperSeedTailPrefix324] using
      recordUpperSeedTailChunk324Step.certifies prior
  have h325 : recordUpperSeedTailChunk325State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix325 := by
    have prior : recordUpperSeedTailChunk325Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix324 := by
      simpa only [
        recordUpperSeedTailChunk325Before,
        recordUpperSeedTailChunk324State] using h324
    simpa only [recordUpperSeedTailPrefix325] using
      recordUpperSeedTailChunk325Step.certifies prior
  have h326 : recordUpperSeedTailChunk326State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix326 := by
    have prior : recordUpperSeedTailChunk326Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix325 := by
      simpa only [
        recordUpperSeedTailChunk326Before,
        recordUpperSeedTailChunk325State] using h325
    simpa only [recordUpperSeedTailPrefix326] using
      recordUpperSeedTailChunk326Step.certifies prior
  have h327 : recordUpperSeedTailChunk327State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix327 := by
    have prior : recordUpperSeedTailChunk327Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix326 := by
      simpa only [
        recordUpperSeedTailChunk327Before,
        recordUpperSeedTailChunk326State] using h326
    simpa only [recordUpperSeedTailPrefix327] using
      recordUpperSeedTailChunk327Step.certifies prior
  have h328 : recordUpperSeedTailChunk328State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix328 := by
    have prior : recordUpperSeedTailChunk328Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix327 := by
      simpa only [
        recordUpperSeedTailChunk328Before,
        recordUpperSeedTailChunk327State] using h327
    simpa only [recordUpperSeedTailPrefix328] using
      recordUpperSeedTailChunk328Step.certifies prior
  have h329 : recordUpperSeedTailChunk329State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix329 := by
    have prior : recordUpperSeedTailChunk329Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix328 := by
      simpa only [
        recordUpperSeedTailChunk329Before,
        recordUpperSeedTailChunk328State] using h328
    simpa only [recordUpperSeedTailPrefix329] using
      recordUpperSeedTailChunk329Step.certifies prior
  have h330 : recordUpperSeedTailChunk330State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix330 := by
    have prior : recordUpperSeedTailChunk330Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix329 := by
      simpa only [
        recordUpperSeedTailChunk330Before,
        recordUpperSeedTailChunk329State] using h329
    simpa only [recordUpperSeedTailPrefix330] using
      recordUpperSeedTailChunk330Step.certifies prior
  have h331 : recordUpperSeedTailChunk331State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix331 := by
    have prior : recordUpperSeedTailChunk331Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix330 := by
      simpa only [
        recordUpperSeedTailChunk331Before,
        recordUpperSeedTailChunk330State] using h330
    simpa only [recordUpperSeedTailPrefix331] using
      recordUpperSeedTailChunk331Step.certifies prior
  have h332 : recordUpperSeedTailChunk332State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix332 := by
    have prior : recordUpperSeedTailChunk332Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix331 := by
      simpa only [
        recordUpperSeedTailChunk332Before,
        recordUpperSeedTailChunk331State] using h331
    simpa only [recordUpperSeedTailPrefix332] using
      recordUpperSeedTailChunk332Step.certifies prior
  have h333 : recordUpperSeedTailChunk333State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix333 := by
    have prior : recordUpperSeedTailChunk333Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix332 := by
      simpa only [
        recordUpperSeedTailChunk333Before,
        recordUpperSeedTailChunk332State] using h332
    simpa only [recordUpperSeedTailPrefix333] using
      recordUpperSeedTailChunk333Step.certifies prior
  have h334 : recordUpperSeedTailChunk334State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix334 := by
    have prior : recordUpperSeedTailChunk334Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix333 := by
      simpa only [
        recordUpperSeedTailChunk334Before,
        recordUpperSeedTailChunk333State] using h333
    simpa only [recordUpperSeedTailPrefix334] using
      recordUpperSeedTailChunk334Step.certifies prior
  have h335 : recordUpperSeedTailChunk335State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix335 := by
    have prior : recordUpperSeedTailChunk335Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix334 := by
      simpa only [
        recordUpperSeedTailChunk335Before,
        recordUpperSeedTailChunk334State] using h334
    simpa only [recordUpperSeedTailPrefix335] using
      recordUpperSeedTailChunk335Step.certifies prior
  have h336 : recordUpperSeedTailChunk336State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix336 := by
    have prior : recordUpperSeedTailChunk336Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix335 := by
      simpa only [
        recordUpperSeedTailChunk336Before,
        recordUpperSeedTailChunk335State] using h335
    simpa only [recordUpperSeedTailPrefix336] using
      recordUpperSeedTailChunk336Step.certifies prior
  have h337 : recordUpperSeedTailChunk337State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix337 := by
    have prior : recordUpperSeedTailChunk337Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix336 := by
      simpa only [
        recordUpperSeedTailChunk337Before,
        recordUpperSeedTailChunk336State] using h336
    simpa only [recordUpperSeedTailPrefix337] using
      recordUpperSeedTailChunk337Step.certifies prior
  have h338 : recordUpperSeedTailChunk338State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix338 := by
    have prior : recordUpperSeedTailChunk338Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix337 := by
      simpa only [
        recordUpperSeedTailChunk338Before,
        recordUpperSeedTailChunk337State] using h337
    simpa only [recordUpperSeedTailPrefix338] using
      recordUpperSeedTailChunk338Step.certifies prior
  have h339 : recordUpperSeedTailChunk339State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix339 := by
    have prior : recordUpperSeedTailChunk339Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix338 := by
      simpa only [
        recordUpperSeedTailChunk339Before,
        recordUpperSeedTailChunk338State] using h338
    simpa only [recordUpperSeedTailPrefix339] using
      recordUpperSeedTailChunk339Step.certifies prior
  have h340 : recordUpperSeedTailChunk340State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix340 := by
    have prior : recordUpperSeedTailChunk340Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix339 := by
      simpa only [
        recordUpperSeedTailChunk340Before,
        recordUpperSeedTailChunk339State] using h339
    simpa only [recordUpperSeedTailPrefix340] using
      recordUpperSeedTailChunk340Step.certifies prior
  have h341 : recordUpperSeedTailChunk341State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix341 := by
    have prior : recordUpperSeedTailChunk341Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix340 := by
      simpa only [
        recordUpperSeedTailChunk341Before,
        recordUpperSeedTailChunk340State] using h340
    simpa only [recordUpperSeedTailPrefix341] using
      recordUpperSeedTailChunk341Step.certifies prior
  have h342 : recordUpperSeedTailChunk342State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix342 := by
    have prior : recordUpperSeedTailChunk342Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix341 := by
      simpa only [
        recordUpperSeedTailChunk342Before,
        recordUpperSeedTailChunk341State] using h341
    simpa only [recordUpperSeedTailPrefix342] using
      recordUpperSeedTailChunk342Step.certifies prior
  have h343 : recordUpperSeedTailChunk343State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix343 := by
    have prior : recordUpperSeedTailChunk343Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix342 := by
      simpa only [
        recordUpperSeedTailChunk343Before,
        recordUpperSeedTailChunk342State] using h342
    simpa only [recordUpperSeedTailPrefix343] using
      recordUpperSeedTailChunk343Step.certifies prior
  have h344 : recordUpperSeedTailChunk344State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix344 := by
    have prior : recordUpperSeedTailChunk344Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix343 := by
      simpa only [
        recordUpperSeedTailChunk344Before,
        recordUpperSeedTailChunk343State] using h343
    simpa only [recordUpperSeedTailPrefix344] using
      recordUpperSeedTailChunk344Step.certifies prior
  have h345 : recordUpperSeedTailChunk345State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix345 := by
    have prior : recordUpperSeedTailChunk345Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix344 := by
      simpa only [
        recordUpperSeedTailChunk345Before,
        recordUpperSeedTailChunk344State] using h344
    simpa only [recordUpperSeedTailPrefix345] using
      recordUpperSeedTailChunk345Step.certifies prior
  have h346 : recordUpperSeedTailChunk346State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix346 := by
    have prior : recordUpperSeedTailChunk346Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix345 := by
      simpa only [
        recordUpperSeedTailChunk346Before,
        recordUpperSeedTailChunk345State] using h345
    simpa only [recordUpperSeedTailPrefix346] using
      recordUpperSeedTailChunk346Step.certifies prior
  have h347 : recordUpperSeedTailChunk347State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix347 := by
    have prior : recordUpperSeedTailChunk347Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix346 := by
      simpa only [
        recordUpperSeedTailChunk347Before,
        recordUpperSeedTailChunk346State] using h346
    simpa only [recordUpperSeedTailPrefix347] using
      recordUpperSeedTailChunk347Step.certifies prior
  have h348 : recordUpperSeedTailChunk348State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix348 := by
    have prior : recordUpperSeedTailChunk348Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix347 := by
      simpa only [
        recordUpperSeedTailChunk348Before,
        recordUpperSeedTailChunk347State] using h347
    simpa only [recordUpperSeedTailPrefix348] using
      recordUpperSeedTailChunk348Step.certifies prior
  have h349 : recordUpperSeedTailChunk349State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix349 := by
    have prior : recordUpperSeedTailChunk349Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix348 := by
      simpa only [
        recordUpperSeedTailChunk349Before,
        recordUpperSeedTailChunk348State] using h348
    simpa only [recordUpperSeedTailPrefix349] using
      recordUpperSeedTailChunk349Step.certifies prior
  have h350 : recordUpperSeedTailChunk350State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix350 := by
    have prior : recordUpperSeedTailChunk350Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix349 := by
      simpa only [
        recordUpperSeedTailChunk350Before,
        recordUpperSeedTailChunk349State] using h349
    simpa only [recordUpperSeedTailPrefix350] using
      recordUpperSeedTailChunk350Step.certifies prior
  have h351 : recordUpperSeedTailChunk351State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix351 := by
    have prior : recordUpperSeedTailChunk351Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix350 := by
      simpa only [
        recordUpperSeedTailChunk351Before,
        recordUpperSeedTailChunk350State] using h350
    simpa only [recordUpperSeedTailPrefix351] using
      recordUpperSeedTailChunk351Step.certifies prior
  have h352 : recordUpperSeedTailChunk352State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix352 := by
    have prior : recordUpperSeedTailChunk352Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix351 := by
      simpa only [
        recordUpperSeedTailChunk352Before,
        recordUpperSeedTailChunk351State] using h351
    simpa only [recordUpperSeedTailPrefix352] using
      recordUpperSeedTailChunk352Step.certifies prior
  have h353 : recordUpperSeedTailChunk353State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix353 := by
    have prior : recordUpperSeedTailChunk353Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix352 := by
      simpa only [
        recordUpperSeedTailChunk353Before,
        recordUpperSeedTailChunk352State] using h352
    simpa only [recordUpperSeedTailPrefix353] using
      recordUpperSeedTailChunk353Step.certifies prior
  have h354 : recordUpperSeedTailChunk354State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix354 := by
    have prior : recordUpperSeedTailChunk354Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix353 := by
      simpa only [
        recordUpperSeedTailChunk354Before,
        recordUpperSeedTailChunk353State] using h353
    simpa only [recordUpperSeedTailPrefix354] using
      recordUpperSeedTailChunk354Step.certifies prior
  have h355 : recordUpperSeedTailChunk355State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix355 := by
    have prior : recordUpperSeedTailChunk355Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix354 := by
      simpa only [
        recordUpperSeedTailChunk355Before,
        recordUpperSeedTailChunk354State] using h354
    simpa only [recordUpperSeedTailPrefix355] using
      recordUpperSeedTailChunk355Step.certifies prior
  have h356 : recordUpperSeedTailChunk356State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix356 := by
    have prior : recordUpperSeedTailChunk356Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix355 := by
      simpa only [
        recordUpperSeedTailChunk356Before,
        recordUpperSeedTailChunk355State] using h355
    simpa only [recordUpperSeedTailPrefix356] using
      recordUpperSeedTailChunk356Step.certifies prior
  have h357 : recordUpperSeedTailChunk357State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix357 := by
    have prior : recordUpperSeedTailChunk357Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix356 := by
      simpa only [
        recordUpperSeedTailChunk357Before,
        recordUpperSeedTailChunk356State] using h356
    simpa only [recordUpperSeedTailPrefix357] using
      recordUpperSeedTailChunk357Step.certifies prior
  have h358 : recordUpperSeedTailChunk358State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix358 := by
    have prior : recordUpperSeedTailChunk358Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix357 := by
      simpa only [
        recordUpperSeedTailChunk358Before,
        recordUpperSeedTailChunk357State] using h357
    simpa only [recordUpperSeedTailPrefix358] using
      recordUpperSeedTailChunk358Step.certifies prior
  have h359 : recordUpperSeedTailChunk359State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix359 := by
    have prior : recordUpperSeedTailChunk359Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix358 := by
      simpa only [
        recordUpperSeedTailChunk359Before,
        recordUpperSeedTailChunk358State] using h358
    simpa only [recordUpperSeedTailPrefix359] using
      recordUpperSeedTailChunk359Step.certifies prior
  have h360 : recordUpperSeedTailChunk360State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix360 := by
    have prior : recordUpperSeedTailChunk360Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix359 := by
      simpa only [
        recordUpperSeedTailChunk360Before,
        recordUpperSeedTailChunk359State] using h359
    simpa only [recordUpperSeedTailPrefix360] using
      recordUpperSeedTailChunk360Step.certifies prior
  exact h360

end PrimeFactorUnimodality
