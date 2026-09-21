import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part040

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-upper-seed-base11.json` (semantic SHA-256 `493791f7b41de1500c4b830f254f9f92fd9c5d50d639b62aa2b46ca48591321f`, excluding elapsed time). Semantic tail assembly group 1. -/

namespace PrimeFactorUnimodality

theorem recordUpperSeedTailGroup01_semantic :
    recordUpperSeedTailChunk040State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix040 := by
  have h000 : (1 : _) =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix000 := by
    simp only [recordUpperSeedTailPrefix000, pow_zero]
  have h001 : recordUpperSeedTailChunk001State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix001 := by
    have prior : recordUpperSeedTailChunk001Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix000 := by
      simpa only [
        recordUpperSeedTailChunk001Before,
        ] using h000
    simpa only [recordUpperSeedTailPrefix001] using
      recordUpperSeedTailChunk001Step.certifies prior
  have h002 : recordUpperSeedTailChunk002State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix002 := by
    have prior : recordUpperSeedTailChunk002Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix001 := by
      simpa only [
        recordUpperSeedTailChunk002Before,
        recordUpperSeedTailChunk001State] using h001
    simpa only [recordUpperSeedTailPrefix002] using
      recordUpperSeedTailChunk002Step.certifies prior
  have h003 : recordUpperSeedTailChunk003State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix003 := by
    have prior : recordUpperSeedTailChunk003Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix002 := by
      simpa only [
        recordUpperSeedTailChunk003Before,
        recordUpperSeedTailChunk002State] using h002
    simpa only [recordUpperSeedTailPrefix003] using
      recordUpperSeedTailChunk003Step.certifies prior
  have h004 : recordUpperSeedTailChunk004State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix004 := by
    have prior : recordUpperSeedTailChunk004Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix003 := by
      simpa only [
        recordUpperSeedTailChunk004Before,
        recordUpperSeedTailChunk003State] using h003
    simpa only [recordUpperSeedTailPrefix004] using
      recordUpperSeedTailChunk004Step.certifies prior
  have h005 : recordUpperSeedTailChunk005State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix005 := by
    have prior : recordUpperSeedTailChunk005Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix004 := by
      simpa only [
        recordUpperSeedTailChunk005Before,
        recordUpperSeedTailChunk004State] using h004
    simpa only [recordUpperSeedTailPrefix005] using
      recordUpperSeedTailChunk005Step.certifies prior
  have h006 : recordUpperSeedTailChunk006State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix006 := by
    have prior : recordUpperSeedTailChunk006Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix005 := by
      simpa only [
        recordUpperSeedTailChunk006Before,
        recordUpperSeedTailChunk005State] using h005
    simpa only [recordUpperSeedTailPrefix006] using
      recordUpperSeedTailChunk006Step.certifies prior
  have h007 : recordUpperSeedTailChunk007State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix007 := by
    have prior : recordUpperSeedTailChunk007Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix006 := by
      simpa only [
        recordUpperSeedTailChunk007Before,
        recordUpperSeedTailChunk006State] using h006
    simpa only [recordUpperSeedTailPrefix007] using
      recordUpperSeedTailChunk007Step.certifies prior
  have h008 : recordUpperSeedTailChunk008State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix008 := by
    have prior : recordUpperSeedTailChunk008Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix007 := by
      simpa only [
        recordUpperSeedTailChunk008Before,
        recordUpperSeedTailChunk007State] using h007
    simpa only [recordUpperSeedTailPrefix008] using
      recordUpperSeedTailChunk008Step.certifies prior
  have h009 : recordUpperSeedTailChunk009State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix009 := by
    have prior : recordUpperSeedTailChunk009Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix008 := by
      simpa only [
        recordUpperSeedTailChunk009Before,
        recordUpperSeedTailChunk008State] using h008
    simpa only [recordUpperSeedTailPrefix009] using
      recordUpperSeedTailChunk009Step.certifies prior
  have h010 : recordUpperSeedTailChunk010State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix010 := by
    have prior : recordUpperSeedTailChunk010Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix009 := by
      simpa only [
        recordUpperSeedTailChunk010Before,
        recordUpperSeedTailChunk009State] using h009
    simpa only [recordUpperSeedTailPrefix010] using
      recordUpperSeedTailChunk010Step.certifies prior
  have h011 : recordUpperSeedTailChunk011State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix011 := by
    have prior : recordUpperSeedTailChunk011Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix010 := by
      simpa only [
        recordUpperSeedTailChunk011Before,
        recordUpperSeedTailChunk010State] using h010
    simpa only [recordUpperSeedTailPrefix011] using
      recordUpperSeedTailChunk011Step.certifies prior
  have h012 : recordUpperSeedTailChunk012State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix012 := by
    have prior : recordUpperSeedTailChunk012Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix011 := by
      simpa only [
        recordUpperSeedTailChunk012Before,
        recordUpperSeedTailChunk011State] using h011
    simpa only [recordUpperSeedTailPrefix012] using
      recordUpperSeedTailChunk012Step.certifies prior
  have h013 : recordUpperSeedTailChunk013State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix013 := by
    have prior : recordUpperSeedTailChunk013Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix012 := by
      simpa only [
        recordUpperSeedTailChunk013Before,
        recordUpperSeedTailChunk012State] using h012
    simpa only [recordUpperSeedTailPrefix013] using
      recordUpperSeedTailChunk013Step.certifies prior
  have h014 : recordUpperSeedTailChunk014State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix014 := by
    have prior : recordUpperSeedTailChunk014Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix013 := by
      simpa only [
        recordUpperSeedTailChunk014Before,
        recordUpperSeedTailChunk013State] using h013
    simpa only [recordUpperSeedTailPrefix014] using
      recordUpperSeedTailChunk014Step.certifies prior
  have h015 : recordUpperSeedTailChunk015State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix015 := by
    have prior : recordUpperSeedTailChunk015Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix014 := by
      simpa only [
        recordUpperSeedTailChunk015Before,
        recordUpperSeedTailChunk014State] using h014
    simpa only [recordUpperSeedTailPrefix015] using
      recordUpperSeedTailChunk015Step.certifies prior
  have h016 : recordUpperSeedTailChunk016State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix016 := by
    have prior : recordUpperSeedTailChunk016Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix015 := by
      simpa only [
        recordUpperSeedTailChunk016Before,
        recordUpperSeedTailChunk015State] using h015
    simpa only [recordUpperSeedTailPrefix016] using
      recordUpperSeedTailChunk016Step.certifies prior
  have h017 : recordUpperSeedTailChunk017State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix017 := by
    have prior : recordUpperSeedTailChunk017Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix016 := by
      simpa only [
        recordUpperSeedTailChunk017Before,
        recordUpperSeedTailChunk016State] using h016
    simpa only [recordUpperSeedTailPrefix017] using
      recordUpperSeedTailChunk017Step.certifies prior
  have h018 : recordUpperSeedTailChunk018State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix018 := by
    have prior : recordUpperSeedTailChunk018Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix017 := by
      simpa only [
        recordUpperSeedTailChunk018Before,
        recordUpperSeedTailChunk017State] using h017
    simpa only [recordUpperSeedTailPrefix018] using
      recordUpperSeedTailChunk018Step.certifies prior
  have h019 : recordUpperSeedTailChunk019State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix019 := by
    have prior : recordUpperSeedTailChunk019Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix018 := by
      simpa only [
        recordUpperSeedTailChunk019Before,
        recordUpperSeedTailChunk018State] using h018
    simpa only [recordUpperSeedTailPrefix019] using
      recordUpperSeedTailChunk019Step.certifies prior
  have h020 : recordUpperSeedTailChunk020State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix020 := by
    have prior : recordUpperSeedTailChunk020Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix019 := by
      simpa only [
        recordUpperSeedTailChunk020Before,
        recordUpperSeedTailChunk019State] using h019
    simpa only [recordUpperSeedTailPrefix020] using
      recordUpperSeedTailChunk020Step.certifies prior
  have h021 : recordUpperSeedTailChunk021State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix021 := by
    have prior : recordUpperSeedTailChunk021Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix020 := by
      simpa only [
        recordUpperSeedTailChunk021Before,
        recordUpperSeedTailChunk020State] using h020
    simpa only [recordUpperSeedTailPrefix021] using
      recordUpperSeedTailChunk021Step.certifies prior
  have h022 : recordUpperSeedTailChunk022State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix022 := by
    have prior : recordUpperSeedTailChunk022Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix021 := by
      simpa only [
        recordUpperSeedTailChunk022Before,
        recordUpperSeedTailChunk021State] using h021
    simpa only [recordUpperSeedTailPrefix022] using
      recordUpperSeedTailChunk022Step.certifies prior
  have h023 : recordUpperSeedTailChunk023State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix023 := by
    have prior : recordUpperSeedTailChunk023Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix022 := by
      simpa only [
        recordUpperSeedTailChunk023Before,
        recordUpperSeedTailChunk022State] using h022
    simpa only [recordUpperSeedTailPrefix023] using
      recordUpperSeedTailChunk023Step.certifies prior
  have h024 : recordUpperSeedTailChunk024State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix024 := by
    have prior : recordUpperSeedTailChunk024Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix023 := by
      simpa only [
        recordUpperSeedTailChunk024Before,
        recordUpperSeedTailChunk023State] using h023
    simpa only [recordUpperSeedTailPrefix024] using
      recordUpperSeedTailChunk024Step.certifies prior
  have h025 : recordUpperSeedTailChunk025State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix025 := by
    have prior : recordUpperSeedTailChunk025Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix024 := by
      simpa only [
        recordUpperSeedTailChunk025Before,
        recordUpperSeedTailChunk024State] using h024
    simpa only [recordUpperSeedTailPrefix025] using
      recordUpperSeedTailChunk025Step.certifies prior
  have h026 : recordUpperSeedTailChunk026State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix026 := by
    have prior : recordUpperSeedTailChunk026Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix025 := by
      simpa only [
        recordUpperSeedTailChunk026Before,
        recordUpperSeedTailChunk025State] using h025
    simpa only [recordUpperSeedTailPrefix026] using
      recordUpperSeedTailChunk026Step.certifies prior
  have h027 : recordUpperSeedTailChunk027State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix027 := by
    have prior : recordUpperSeedTailChunk027Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix026 := by
      simpa only [
        recordUpperSeedTailChunk027Before,
        recordUpperSeedTailChunk026State] using h026
    simpa only [recordUpperSeedTailPrefix027] using
      recordUpperSeedTailChunk027Step.certifies prior
  have h028 : recordUpperSeedTailChunk028State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix028 := by
    have prior : recordUpperSeedTailChunk028Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix027 := by
      simpa only [
        recordUpperSeedTailChunk028Before,
        recordUpperSeedTailChunk027State] using h027
    simpa only [recordUpperSeedTailPrefix028] using
      recordUpperSeedTailChunk028Step.certifies prior
  have h029 : recordUpperSeedTailChunk029State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix029 := by
    have prior : recordUpperSeedTailChunk029Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix028 := by
      simpa only [
        recordUpperSeedTailChunk029Before,
        recordUpperSeedTailChunk028State] using h028
    simpa only [recordUpperSeedTailPrefix029] using
      recordUpperSeedTailChunk029Step.certifies prior
  have h030 : recordUpperSeedTailChunk030State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix030 := by
    have prior : recordUpperSeedTailChunk030Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix029 := by
      simpa only [
        recordUpperSeedTailChunk030Before,
        recordUpperSeedTailChunk029State] using h029
    simpa only [recordUpperSeedTailPrefix030] using
      recordUpperSeedTailChunk030Step.certifies prior
  have h031 : recordUpperSeedTailChunk031State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix031 := by
    have prior : recordUpperSeedTailChunk031Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix030 := by
      simpa only [
        recordUpperSeedTailChunk031Before,
        recordUpperSeedTailChunk030State] using h030
    simpa only [recordUpperSeedTailPrefix031] using
      recordUpperSeedTailChunk031Step.certifies prior
  have h032 : recordUpperSeedTailChunk032State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix032 := by
    have prior : recordUpperSeedTailChunk032Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix031 := by
      simpa only [
        recordUpperSeedTailChunk032Before,
        recordUpperSeedTailChunk031State] using h031
    simpa only [recordUpperSeedTailPrefix032] using
      recordUpperSeedTailChunk032Step.certifies prior
  have h033 : recordUpperSeedTailChunk033State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix033 := by
    have prior : recordUpperSeedTailChunk033Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix032 := by
      simpa only [
        recordUpperSeedTailChunk033Before,
        recordUpperSeedTailChunk032State] using h032
    simpa only [recordUpperSeedTailPrefix033] using
      recordUpperSeedTailChunk033Step.certifies prior
  have h034 : recordUpperSeedTailChunk034State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix034 := by
    have prior : recordUpperSeedTailChunk034Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix033 := by
      simpa only [
        recordUpperSeedTailChunk034Before,
        recordUpperSeedTailChunk033State] using h033
    simpa only [recordUpperSeedTailPrefix034] using
      recordUpperSeedTailChunk034Step.certifies prior
  have h035 : recordUpperSeedTailChunk035State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix035 := by
    have prior : recordUpperSeedTailChunk035Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix034 := by
      simpa only [
        recordUpperSeedTailChunk035Before,
        recordUpperSeedTailChunk034State] using h034
    simpa only [recordUpperSeedTailPrefix035] using
      recordUpperSeedTailChunk035Step.certifies prior
  have h036 : recordUpperSeedTailChunk036State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix036 := by
    have prior : recordUpperSeedTailChunk036Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix035 := by
      simpa only [
        recordUpperSeedTailChunk036Before,
        recordUpperSeedTailChunk035State] using h035
    simpa only [recordUpperSeedTailPrefix036] using
      recordUpperSeedTailChunk036Step.certifies prior
  have h037 : recordUpperSeedTailChunk037State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix037 := by
    have prior : recordUpperSeedTailChunk037Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix036 := by
      simpa only [
        recordUpperSeedTailChunk037Before,
        recordUpperSeedTailChunk036State] using h036
    simpa only [recordUpperSeedTailPrefix037] using
      recordUpperSeedTailChunk037Step.certifies prior
  have h038 : recordUpperSeedTailChunk038State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix038 := by
    have prior : recordUpperSeedTailChunk038Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix037 := by
      simpa only [
        recordUpperSeedTailChunk038Before,
        recordUpperSeedTailChunk037State] using h037
    simpa only [recordUpperSeedTailPrefix038] using
      recordUpperSeedTailChunk038Step.certifies prior
  have h039 : recordUpperSeedTailChunk039State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix039 := by
    have prior : recordUpperSeedTailChunk039Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix038 := by
      simpa only [
        recordUpperSeedTailChunk039Before,
        recordUpperSeedTailChunk038State] using h038
    simpa only [recordUpperSeedTailPrefix039] using
      recordUpperSeedTailChunk039Step.certifies prior
  have h040 : recordUpperSeedTailChunk040State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix040 := by
    have prior : recordUpperSeedTailChunk040Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix039 := by
      simpa only [
        recordUpperSeedTailChunk040Before,
        recordUpperSeedTailChunk039State] using h039
    simpa only [recordUpperSeedTailPrefix040] using
      recordUpperSeedTailChunk040Step.certifies prior
  exact h040

end PrimeFactorUnimodality
