import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part040

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-lower-seed.json` (semantic SHA-256 `3ce105dad06099400dfd2e30c65d47c6e02828915452a8459553c3bb0eb78b73`, excluding elapsed time). Semantic tail assembly group 1. -/

namespace PrimeFactorUnimodality

theorem recordLowerSeedTailGroup01_semantic :
    recordLowerSeedTailChunk040State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix040 := by
  have h000 : (1 : _) =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix000 := by
    simp only [recordLowerSeedTailPrefix000, pow_zero]
  have h001 : recordLowerSeedTailChunk001State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix001 := by
    have prior : recordLowerSeedTailChunk001Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix000 := by
      simpa only [
        recordLowerSeedTailChunk001Before,
        ] using h000
    simpa only [recordLowerSeedTailPrefix001] using
      recordLowerSeedTailChunk001Step.certifies prior
  have h002 : recordLowerSeedTailChunk002State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix002 := by
    have prior : recordLowerSeedTailChunk002Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix001 := by
      simpa only [
        recordLowerSeedTailChunk002Before,
        recordLowerSeedTailChunk001State] using h001
    simpa only [recordLowerSeedTailPrefix002] using
      recordLowerSeedTailChunk002Step.certifies prior
  have h003 : recordLowerSeedTailChunk003State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix003 := by
    have prior : recordLowerSeedTailChunk003Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix002 := by
      simpa only [
        recordLowerSeedTailChunk003Before,
        recordLowerSeedTailChunk002State] using h002
    simpa only [recordLowerSeedTailPrefix003] using
      recordLowerSeedTailChunk003Step.certifies prior
  have h004 : recordLowerSeedTailChunk004State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix004 := by
    have prior : recordLowerSeedTailChunk004Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix003 := by
      simpa only [
        recordLowerSeedTailChunk004Before,
        recordLowerSeedTailChunk003State] using h003
    simpa only [recordLowerSeedTailPrefix004] using
      recordLowerSeedTailChunk004Step.certifies prior
  have h005 : recordLowerSeedTailChunk005State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix005 := by
    have prior : recordLowerSeedTailChunk005Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix004 := by
      simpa only [
        recordLowerSeedTailChunk005Before,
        recordLowerSeedTailChunk004State] using h004
    simpa only [recordLowerSeedTailPrefix005] using
      recordLowerSeedTailChunk005Step.certifies prior
  have h006 : recordLowerSeedTailChunk006State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix006 := by
    have prior : recordLowerSeedTailChunk006Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix005 := by
      simpa only [
        recordLowerSeedTailChunk006Before,
        recordLowerSeedTailChunk005State] using h005
    simpa only [recordLowerSeedTailPrefix006] using
      recordLowerSeedTailChunk006Step.certifies prior
  have h007 : recordLowerSeedTailChunk007State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix007 := by
    have prior : recordLowerSeedTailChunk007Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix006 := by
      simpa only [
        recordLowerSeedTailChunk007Before,
        recordLowerSeedTailChunk006State] using h006
    simpa only [recordLowerSeedTailPrefix007] using
      recordLowerSeedTailChunk007Step.certifies prior
  have h008 : recordLowerSeedTailChunk008State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix008 := by
    have prior : recordLowerSeedTailChunk008Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix007 := by
      simpa only [
        recordLowerSeedTailChunk008Before,
        recordLowerSeedTailChunk007State] using h007
    simpa only [recordLowerSeedTailPrefix008] using
      recordLowerSeedTailChunk008Step.certifies prior
  have h009 : recordLowerSeedTailChunk009State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix009 := by
    have prior : recordLowerSeedTailChunk009Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix008 := by
      simpa only [
        recordLowerSeedTailChunk009Before,
        recordLowerSeedTailChunk008State] using h008
    simpa only [recordLowerSeedTailPrefix009] using
      recordLowerSeedTailChunk009Step.certifies prior
  have h010 : recordLowerSeedTailChunk010State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix010 := by
    have prior : recordLowerSeedTailChunk010Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix009 := by
      simpa only [
        recordLowerSeedTailChunk010Before,
        recordLowerSeedTailChunk009State] using h009
    simpa only [recordLowerSeedTailPrefix010] using
      recordLowerSeedTailChunk010Step.certifies prior
  have h011 : recordLowerSeedTailChunk011State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix011 := by
    have prior : recordLowerSeedTailChunk011Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix010 := by
      simpa only [
        recordLowerSeedTailChunk011Before,
        recordLowerSeedTailChunk010State] using h010
    simpa only [recordLowerSeedTailPrefix011] using
      recordLowerSeedTailChunk011Step.certifies prior
  have h012 : recordLowerSeedTailChunk012State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix012 := by
    have prior : recordLowerSeedTailChunk012Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix011 := by
      simpa only [
        recordLowerSeedTailChunk012Before,
        recordLowerSeedTailChunk011State] using h011
    simpa only [recordLowerSeedTailPrefix012] using
      recordLowerSeedTailChunk012Step.certifies prior
  have h013 : recordLowerSeedTailChunk013State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix013 := by
    have prior : recordLowerSeedTailChunk013Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix012 := by
      simpa only [
        recordLowerSeedTailChunk013Before,
        recordLowerSeedTailChunk012State] using h012
    simpa only [recordLowerSeedTailPrefix013] using
      recordLowerSeedTailChunk013Step.certifies prior
  have h014 : recordLowerSeedTailChunk014State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix014 := by
    have prior : recordLowerSeedTailChunk014Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix013 := by
      simpa only [
        recordLowerSeedTailChunk014Before,
        recordLowerSeedTailChunk013State] using h013
    simpa only [recordLowerSeedTailPrefix014] using
      recordLowerSeedTailChunk014Step.certifies prior
  have h015 : recordLowerSeedTailChunk015State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix015 := by
    have prior : recordLowerSeedTailChunk015Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix014 := by
      simpa only [
        recordLowerSeedTailChunk015Before,
        recordLowerSeedTailChunk014State] using h014
    simpa only [recordLowerSeedTailPrefix015] using
      recordLowerSeedTailChunk015Step.certifies prior
  have h016 : recordLowerSeedTailChunk016State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix016 := by
    have prior : recordLowerSeedTailChunk016Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix015 := by
      simpa only [
        recordLowerSeedTailChunk016Before,
        recordLowerSeedTailChunk015State] using h015
    simpa only [recordLowerSeedTailPrefix016] using
      recordLowerSeedTailChunk016Step.certifies prior
  have h017 : recordLowerSeedTailChunk017State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix017 := by
    have prior : recordLowerSeedTailChunk017Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix016 := by
      simpa only [
        recordLowerSeedTailChunk017Before,
        recordLowerSeedTailChunk016State] using h016
    simpa only [recordLowerSeedTailPrefix017] using
      recordLowerSeedTailChunk017Step.certifies prior
  have h018 : recordLowerSeedTailChunk018State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix018 := by
    have prior : recordLowerSeedTailChunk018Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix017 := by
      simpa only [
        recordLowerSeedTailChunk018Before,
        recordLowerSeedTailChunk017State] using h017
    simpa only [recordLowerSeedTailPrefix018] using
      recordLowerSeedTailChunk018Step.certifies prior
  have h019 : recordLowerSeedTailChunk019State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix019 := by
    have prior : recordLowerSeedTailChunk019Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix018 := by
      simpa only [
        recordLowerSeedTailChunk019Before,
        recordLowerSeedTailChunk018State] using h018
    simpa only [recordLowerSeedTailPrefix019] using
      recordLowerSeedTailChunk019Step.certifies prior
  have h020 : recordLowerSeedTailChunk020State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix020 := by
    have prior : recordLowerSeedTailChunk020Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix019 := by
      simpa only [
        recordLowerSeedTailChunk020Before,
        recordLowerSeedTailChunk019State] using h019
    simpa only [recordLowerSeedTailPrefix020] using
      recordLowerSeedTailChunk020Step.certifies prior
  have h021 : recordLowerSeedTailChunk021State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix021 := by
    have prior : recordLowerSeedTailChunk021Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix020 := by
      simpa only [
        recordLowerSeedTailChunk021Before,
        recordLowerSeedTailChunk020State] using h020
    simpa only [recordLowerSeedTailPrefix021] using
      recordLowerSeedTailChunk021Step.certifies prior
  have h022 : recordLowerSeedTailChunk022State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix022 := by
    have prior : recordLowerSeedTailChunk022Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix021 := by
      simpa only [
        recordLowerSeedTailChunk022Before,
        recordLowerSeedTailChunk021State] using h021
    simpa only [recordLowerSeedTailPrefix022] using
      recordLowerSeedTailChunk022Step.certifies prior
  have h023 : recordLowerSeedTailChunk023State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix023 := by
    have prior : recordLowerSeedTailChunk023Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix022 := by
      simpa only [
        recordLowerSeedTailChunk023Before,
        recordLowerSeedTailChunk022State] using h022
    simpa only [recordLowerSeedTailPrefix023] using
      recordLowerSeedTailChunk023Step.certifies prior
  have h024 : recordLowerSeedTailChunk024State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix024 := by
    have prior : recordLowerSeedTailChunk024Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix023 := by
      simpa only [
        recordLowerSeedTailChunk024Before,
        recordLowerSeedTailChunk023State] using h023
    simpa only [recordLowerSeedTailPrefix024] using
      recordLowerSeedTailChunk024Step.certifies prior
  have h025 : recordLowerSeedTailChunk025State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix025 := by
    have prior : recordLowerSeedTailChunk025Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix024 := by
      simpa only [
        recordLowerSeedTailChunk025Before,
        recordLowerSeedTailChunk024State] using h024
    simpa only [recordLowerSeedTailPrefix025] using
      recordLowerSeedTailChunk025Step.certifies prior
  have h026 : recordLowerSeedTailChunk026State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix026 := by
    have prior : recordLowerSeedTailChunk026Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix025 := by
      simpa only [
        recordLowerSeedTailChunk026Before,
        recordLowerSeedTailChunk025State] using h025
    simpa only [recordLowerSeedTailPrefix026] using
      recordLowerSeedTailChunk026Step.certifies prior
  have h027 : recordLowerSeedTailChunk027State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix027 := by
    have prior : recordLowerSeedTailChunk027Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix026 := by
      simpa only [
        recordLowerSeedTailChunk027Before,
        recordLowerSeedTailChunk026State] using h026
    simpa only [recordLowerSeedTailPrefix027] using
      recordLowerSeedTailChunk027Step.certifies prior
  have h028 : recordLowerSeedTailChunk028State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix028 := by
    have prior : recordLowerSeedTailChunk028Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix027 := by
      simpa only [
        recordLowerSeedTailChunk028Before,
        recordLowerSeedTailChunk027State] using h027
    simpa only [recordLowerSeedTailPrefix028] using
      recordLowerSeedTailChunk028Step.certifies prior
  have h029 : recordLowerSeedTailChunk029State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix029 := by
    have prior : recordLowerSeedTailChunk029Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix028 := by
      simpa only [
        recordLowerSeedTailChunk029Before,
        recordLowerSeedTailChunk028State] using h028
    simpa only [recordLowerSeedTailPrefix029] using
      recordLowerSeedTailChunk029Step.certifies prior
  have h030 : recordLowerSeedTailChunk030State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix030 := by
    have prior : recordLowerSeedTailChunk030Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix029 := by
      simpa only [
        recordLowerSeedTailChunk030Before,
        recordLowerSeedTailChunk029State] using h029
    simpa only [recordLowerSeedTailPrefix030] using
      recordLowerSeedTailChunk030Step.certifies prior
  have h031 : recordLowerSeedTailChunk031State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix031 := by
    have prior : recordLowerSeedTailChunk031Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix030 := by
      simpa only [
        recordLowerSeedTailChunk031Before,
        recordLowerSeedTailChunk030State] using h030
    simpa only [recordLowerSeedTailPrefix031] using
      recordLowerSeedTailChunk031Step.certifies prior
  have h032 : recordLowerSeedTailChunk032State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix032 := by
    have prior : recordLowerSeedTailChunk032Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix031 := by
      simpa only [
        recordLowerSeedTailChunk032Before,
        recordLowerSeedTailChunk031State] using h031
    simpa only [recordLowerSeedTailPrefix032] using
      recordLowerSeedTailChunk032Step.certifies prior
  have h033 : recordLowerSeedTailChunk033State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix033 := by
    have prior : recordLowerSeedTailChunk033Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix032 := by
      simpa only [
        recordLowerSeedTailChunk033Before,
        recordLowerSeedTailChunk032State] using h032
    simpa only [recordLowerSeedTailPrefix033] using
      recordLowerSeedTailChunk033Step.certifies prior
  have h034 : recordLowerSeedTailChunk034State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix034 := by
    have prior : recordLowerSeedTailChunk034Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix033 := by
      simpa only [
        recordLowerSeedTailChunk034Before,
        recordLowerSeedTailChunk033State] using h033
    simpa only [recordLowerSeedTailPrefix034] using
      recordLowerSeedTailChunk034Step.certifies prior
  have h035 : recordLowerSeedTailChunk035State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix035 := by
    have prior : recordLowerSeedTailChunk035Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix034 := by
      simpa only [
        recordLowerSeedTailChunk035Before,
        recordLowerSeedTailChunk034State] using h034
    simpa only [recordLowerSeedTailPrefix035] using
      recordLowerSeedTailChunk035Step.certifies prior
  have h036 : recordLowerSeedTailChunk036State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix036 := by
    have prior : recordLowerSeedTailChunk036Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix035 := by
      simpa only [
        recordLowerSeedTailChunk036Before,
        recordLowerSeedTailChunk035State] using h035
    simpa only [recordLowerSeedTailPrefix036] using
      recordLowerSeedTailChunk036Step.certifies prior
  have h037 : recordLowerSeedTailChunk037State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix037 := by
    have prior : recordLowerSeedTailChunk037Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix036 := by
      simpa only [
        recordLowerSeedTailChunk037Before,
        recordLowerSeedTailChunk036State] using h036
    simpa only [recordLowerSeedTailPrefix037] using
      recordLowerSeedTailChunk037Step.certifies prior
  have h038 : recordLowerSeedTailChunk038State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix038 := by
    have prior : recordLowerSeedTailChunk038Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix037 := by
      simpa only [
        recordLowerSeedTailChunk038Before,
        recordLowerSeedTailChunk037State] using h037
    simpa only [recordLowerSeedTailPrefix038] using
      recordLowerSeedTailChunk038Step.certifies prior
  have h039 : recordLowerSeedTailChunk039State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix039 := by
    have prior : recordLowerSeedTailChunk039Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix038 := by
      simpa only [
        recordLowerSeedTailChunk039Before,
        recordLowerSeedTailChunk038State] using h038
    simpa only [recordLowerSeedTailPrefix039] using
      recordLowerSeedTailChunk039Step.certifies prior
  have h040 : recordLowerSeedTailChunk040State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix040 := by
    have prior : recordLowerSeedTailChunk040Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix039 := by
      simpa only [
        recordLowerSeedTailChunk040Before,
        recordLowerSeedTailChunk039State] using h039
    simpa only [recordLowerSeedTailPrefix040] using
      recordLowerSeedTailChunk040Step.certifies prior
  exact h040

end PrimeFactorUnimodality
