import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part040

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-upper-seed-base11.json` (semantic SHA-256 `493791f7b41de1500c4b830f254f9f92fd9c5d50d639b62aa2b46ca48591321f`, excluding elapsed time). Semantic tail assembly group 1. -/

namespace PrimeFactorUnimodality

theorem recordUpperSeedTailGroup01_semantic :
    recordUpperSeedTailChunk040State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix040 := by
  have h000 : (1 : ZMod recordUpper) =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix000 := by
    simp only [recordUpperSeedTailPrefix000, pow_zero]
  have h001 : recordUpperSeedTailChunk001State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix001 := by
    have boundary : recordUpperSeedTailChunk001Before =
        1 := by rfl
    exact recordUpperSeedTailChunk001Step.certifies
      (boundary.trans h000)
  have h002 : recordUpperSeedTailChunk002State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix002 := by
    have boundary : recordUpperSeedTailChunk002Before =
        recordUpperSeedTailChunk001State := by rfl
    exact recordUpperSeedTailChunk002Step.certifies
      (boundary.trans h001)
  have h003 : recordUpperSeedTailChunk003State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix003 := by
    have boundary : recordUpperSeedTailChunk003Before =
        recordUpperSeedTailChunk002State := by rfl
    exact recordUpperSeedTailChunk003Step.certifies
      (boundary.trans h002)
  have h004 : recordUpperSeedTailChunk004State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix004 := by
    have boundary : recordUpperSeedTailChunk004Before =
        recordUpperSeedTailChunk003State := by rfl
    exact recordUpperSeedTailChunk004Step.certifies
      (boundary.trans h003)
  have h005 : recordUpperSeedTailChunk005State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix005 := by
    have boundary : recordUpperSeedTailChunk005Before =
        recordUpperSeedTailChunk004State := by rfl
    exact recordUpperSeedTailChunk005Step.certifies
      (boundary.trans h004)
  have h006 : recordUpperSeedTailChunk006State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix006 := by
    have boundary : recordUpperSeedTailChunk006Before =
        recordUpperSeedTailChunk005State := by rfl
    exact recordUpperSeedTailChunk006Step.certifies
      (boundary.trans h005)
  have h007 : recordUpperSeedTailChunk007State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix007 := by
    have boundary : recordUpperSeedTailChunk007Before =
        recordUpperSeedTailChunk006State := by rfl
    exact recordUpperSeedTailChunk007Step.certifies
      (boundary.trans h006)
  have h008 : recordUpperSeedTailChunk008State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix008 := by
    have boundary : recordUpperSeedTailChunk008Before =
        recordUpperSeedTailChunk007State := by rfl
    exact recordUpperSeedTailChunk008Step.certifies
      (boundary.trans h007)
  have h009 : recordUpperSeedTailChunk009State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix009 := by
    have boundary : recordUpperSeedTailChunk009Before =
        recordUpperSeedTailChunk008State := by rfl
    exact recordUpperSeedTailChunk009Step.certifies
      (boundary.trans h008)
  have h010 : recordUpperSeedTailChunk010State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix010 := by
    have boundary : recordUpperSeedTailChunk010Before =
        recordUpperSeedTailChunk009State := by rfl
    exact recordUpperSeedTailChunk010Step.certifies
      (boundary.trans h009)
  have h011 : recordUpperSeedTailChunk011State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix011 := by
    have boundary : recordUpperSeedTailChunk011Before =
        recordUpperSeedTailChunk010State := by rfl
    exact recordUpperSeedTailChunk011Step.certifies
      (boundary.trans h010)
  have h012 : recordUpperSeedTailChunk012State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix012 := by
    have boundary : recordUpperSeedTailChunk012Before =
        recordUpperSeedTailChunk011State := by rfl
    exact recordUpperSeedTailChunk012Step.certifies
      (boundary.trans h011)
  have h013 : recordUpperSeedTailChunk013State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix013 := by
    have boundary : recordUpperSeedTailChunk013Before =
        recordUpperSeedTailChunk012State := by rfl
    exact recordUpperSeedTailChunk013Step.certifies
      (boundary.trans h012)
  have h014 : recordUpperSeedTailChunk014State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix014 := by
    have boundary : recordUpperSeedTailChunk014Before =
        recordUpperSeedTailChunk013State := by rfl
    exact recordUpperSeedTailChunk014Step.certifies
      (boundary.trans h013)
  have h015 : recordUpperSeedTailChunk015State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix015 := by
    have boundary : recordUpperSeedTailChunk015Before =
        recordUpperSeedTailChunk014State := by rfl
    exact recordUpperSeedTailChunk015Step.certifies
      (boundary.trans h014)
  have h016 : recordUpperSeedTailChunk016State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix016 := by
    have boundary : recordUpperSeedTailChunk016Before =
        recordUpperSeedTailChunk015State := by rfl
    exact recordUpperSeedTailChunk016Step.certifies
      (boundary.trans h015)
  have h017 : recordUpperSeedTailChunk017State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix017 := by
    have boundary : recordUpperSeedTailChunk017Before =
        recordUpperSeedTailChunk016State := by rfl
    exact recordUpperSeedTailChunk017Step.certifies
      (boundary.trans h016)
  have h018 : recordUpperSeedTailChunk018State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix018 := by
    have boundary : recordUpperSeedTailChunk018Before =
        recordUpperSeedTailChunk017State := by rfl
    exact recordUpperSeedTailChunk018Step.certifies
      (boundary.trans h017)
  have h019 : recordUpperSeedTailChunk019State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix019 := by
    have boundary : recordUpperSeedTailChunk019Before =
        recordUpperSeedTailChunk018State := by rfl
    exact recordUpperSeedTailChunk019Step.certifies
      (boundary.trans h018)
  have h020 : recordUpperSeedTailChunk020State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix020 := by
    have boundary : recordUpperSeedTailChunk020Before =
        recordUpperSeedTailChunk019State := by rfl
    exact recordUpperSeedTailChunk020Step.certifies
      (boundary.trans h019)
  have h021 : recordUpperSeedTailChunk021State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix021 := by
    have boundary : recordUpperSeedTailChunk021Before =
        recordUpperSeedTailChunk020State := by rfl
    exact recordUpperSeedTailChunk021Step.certifies
      (boundary.trans h020)
  have h022 : recordUpperSeedTailChunk022State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix022 := by
    have boundary : recordUpperSeedTailChunk022Before =
        recordUpperSeedTailChunk021State := by rfl
    exact recordUpperSeedTailChunk022Step.certifies
      (boundary.trans h021)
  have h023 : recordUpperSeedTailChunk023State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix023 := by
    have boundary : recordUpperSeedTailChunk023Before =
        recordUpperSeedTailChunk022State := by rfl
    exact recordUpperSeedTailChunk023Step.certifies
      (boundary.trans h022)
  have h024 : recordUpperSeedTailChunk024State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix024 := by
    have boundary : recordUpperSeedTailChunk024Before =
        recordUpperSeedTailChunk023State := by rfl
    exact recordUpperSeedTailChunk024Step.certifies
      (boundary.trans h023)
  have h025 : recordUpperSeedTailChunk025State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix025 := by
    have boundary : recordUpperSeedTailChunk025Before =
        recordUpperSeedTailChunk024State := by rfl
    exact recordUpperSeedTailChunk025Step.certifies
      (boundary.trans h024)
  have h026 : recordUpperSeedTailChunk026State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix026 := by
    have boundary : recordUpperSeedTailChunk026Before =
        recordUpperSeedTailChunk025State := by rfl
    exact recordUpperSeedTailChunk026Step.certifies
      (boundary.trans h025)
  have h027 : recordUpperSeedTailChunk027State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix027 := by
    have boundary : recordUpperSeedTailChunk027Before =
        recordUpperSeedTailChunk026State := by rfl
    exact recordUpperSeedTailChunk027Step.certifies
      (boundary.trans h026)
  have h028 : recordUpperSeedTailChunk028State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix028 := by
    have boundary : recordUpperSeedTailChunk028Before =
        recordUpperSeedTailChunk027State := by rfl
    exact recordUpperSeedTailChunk028Step.certifies
      (boundary.trans h027)
  have h029 : recordUpperSeedTailChunk029State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix029 := by
    have boundary : recordUpperSeedTailChunk029Before =
        recordUpperSeedTailChunk028State := by rfl
    exact recordUpperSeedTailChunk029Step.certifies
      (boundary.trans h028)
  have h030 : recordUpperSeedTailChunk030State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix030 := by
    have boundary : recordUpperSeedTailChunk030Before =
        recordUpperSeedTailChunk029State := by rfl
    exact recordUpperSeedTailChunk030Step.certifies
      (boundary.trans h029)
  have h031 : recordUpperSeedTailChunk031State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix031 := by
    have boundary : recordUpperSeedTailChunk031Before =
        recordUpperSeedTailChunk030State := by rfl
    exact recordUpperSeedTailChunk031Step.certifies
      (boundary.trans h030)
  have h032 : recordUpperSeedTailChunk032State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix032 := by
    have boundary : recordUpperSeedTailChunk032Before =
        recordUpperSeedTailChunk031State := by rfl
    exact recordUpperSeedTailChunk032Step.certifies
      (boundary.trans h031)
  have h033 : recordUpperSeedTailChunk033State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix033 := by
    have boundary : recordUpperSeedTailChunk033Before =
        recordUpperSeedTailChunk032State := by rfl
    exact recordUpperSeedTailChunk033Step.certifies
      (boundary.trans h032)
  have h034 : recordUpperSeedTailChunk034State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix034 := by
    have boundary : recordUpperSeedTailChunk034Before =
        recordUpperSeedTailChunk033State := by rfl
    exact recordUpperSeedTailChunk034Step.certifies
      (boundary.trans h033)
  have h035 : recordUpperSeedTailChunk035State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix035 := by
    have boundary : recordUpperSeedTailChunk035Before =
        recordUpperSeedTailChunk034State := by rfl
    exact recordUpperSeedTailChunk035Step.certifies
      (boundary.trans h034)
  have h036 : recordUpperSeedTailChunk036State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix036 := by
    have boundary : recordUpperSeedTailChunk036Before =
        recordUpperSeedTailChunk035State := by rfl
    exact recordUpperSeedTailChunk036Step.certifies
      (boundary.trans h035)
  have h037 : recordUpperSeedTailChunk037State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix037 := by
    have boundary : recordUpperSeedTailChunk037Before =
        recordUpperSeedTailChunk036State := by rfl
    exact recordUpperSeedTailChunk037Step.certifies
      (boundary.trans h036)
  have h038 : recordUpperSeedTailChunk038State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix038 := by
    have boundary : recordUpperSeedTailChunk038Before =
        recordUpperSeedTailChunk037State := by rfl
    exact recordUpperSeedTailChunk038Step.certifies
      (boundary.trans h037)
  have h039 : recordUpperSeedTailChunk039State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix039 := by
    have boundary : recordUpperSeedTailChunk039Before =
        recordUpperSeedTailChunk038State := by rfl
    exact recordUpperSeedTailChunk039Step.certifies
      (boundary.trans h038)
  have h040 : recordUpperSeedTailChunk040State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix040 := by
    have boundary : recordUpperSeedTailChunk040Before =
        recordUpperSeedTailChunk039State := by rfl
    exact recordUpperSeedTailChunk040Step.certifies
      (boundary.trans h039)
  exact h040

end PrimeFactorUnimodality
