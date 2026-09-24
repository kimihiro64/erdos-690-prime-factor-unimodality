import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part040

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-lower-seed.json` (semantic SHA-256 `3ce105dad06099400dfd2e30c65d47c6e02828915452a8459553c3bb0eb78b73`, excluding elapsed time). Semantic tail assembly group 1. -/

namespace PrimeFactorUnimodality

theorem recordLowerSeedTailGroup01_semantic :
    recordLowerSeedTailChunk040State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix040 := by
  have h000 : (1 : BLSPrimality.X7 recordLower) =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix000 := by
    simp only [recordLowerSeedTailPrefix000, pow_zero]
  have h001 : recordLowerSeedTailChunk001State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix001 := by
    have boundary : recordLowerSeedTailChunk001Before =
        1 := by rfl
    exact recordLowerSeedTailChunk001Step.certifies
      (boundary.trans h000)
  have h002 : recordLowerSeedTailChunk002State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix002 := by
    have boundary : recordLowerSeedTailChunk002Before =
        recordLowerSeedTailChunk001State := by rfl
    exact recordLowerSeedTailChunk002Step.certifies
      (boundary.trans h001)
  have h003 : recordLowerSeedTailChunk003State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix003 := by
    have boundary : recordLowerSeedTailChunk003Before =
        recordLowerSeedTailChunk002State := by rfl
    exact recordLowerSeedTailChunk003Step.certifies
      (boundary.trans h002)
  have h004 : recordLowerSeedTailChunk004State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix004 := by
    have boundary : recordLowerSeedTailChunk004Before =
        recordLowerSeedTailChunk003State := by rfl
    exact recordLowerSeedTailChunk004Step.certifies
      (boundary.trans h003)
  have h005 : recordLowerSeedTailChunk005State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix005 := by
    have boundary : recordLowerSeedTailChunk005Before =
        recordLowerSeedTailChunk004State := by rfl
    exact recordLowerSeedTailChunk005Step.certifies
      (boundary.trans h004)
  have h006 : recordLowerSeedTailChunk006State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix006 := by
    have boundary : recordLowerSeedTailChunk006Before =
        recordLowerSeedTailChunk005State := by rfl
    exact recordLowerSeedTailChunk006Step.certifies
      (boundary.trans h005)
  have h007 : recordLowerSeedTailChunk007State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix007 := by
    have boundary : recordLowerSeedTailChunk007Before =
        recordLowerSeedTailChunk006State := by rfl
    exact recordLowerSeedTailChunk007Step.certifies
      (boundary.trans h006)
  have h008 : recordLowerSeedTailChunk008State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix008 := by
    have boundary : recordLowerSeedTailChunk008Before =
        recordLowerSeedTailChunk007State := by rfl
    exact recordLowerSeedTailChunk008Step.certifies
      (boundary.trans h007)
  have h009 : recordLowerSeedTailChunk009State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix009 := by
    have boundary : recordLowerSeedTailChunk009Before =
        recordLowerSeedTailChunk008State := by rfl
    exact recordLowerSeedTailChunk009Step.certifies
      (boundary.trans h008)
  have h010 : recordLowerSeedTailChunk010State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix010 := by
    have boundary : recordLowerSeedTailChunk010Before =
        recordLowerSeedTailChunk009State := by rfl
    exact recordLowerSeedTailChunk010Step.certifies
      (boundary.trans h009)
  have h011 : recordLowerSeedTailChunk011State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix011 := by
    have boundary : recordLowerSeedTailChunk011Before =
        recordLowerSeedTailChunk010State := by rfl
    exact recordLowerSeedTailChunk011Step.certifies
      (boundary.trans h010)
  have h012 : recordLowerSeedTailChunk012State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix012 := by
    have boundary : recordLowerSeedTailChunk012Before =
        recordLowerSeedTailChunk011State := by rfl
    exact recordLowerSeedTailChunk012Step.certifies
      (boundary.trans h011)
  have h013 : recordLowerSeedTailChunk013State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix013 := by
    have boundary : recordLowerSeedTailChunk013Before =
        recordLowerSeedTailChunk012State := by rfl
    exact recordLowerSeedTailChunk013Step.certifies
      (boundary.trans h012)
  have h014 : recordLowerSeedTailChunk014State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix014 := by
    have boundary : recordLowerSeedTailChunk014Before =
        recordLowerSeedTailChunk013State := by rfl
    exact recordLowerSeedTailChunk014Step.certifies
      (boundary.trans h013)
  have h015 : recordLowerSeedTailChunk015State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix015 := by
    have boundary : recordLowerSeedTailChunk015Before =
        recordLowerSeedTailChunk014State := by rfl
    exact recordLowerSeedTailChunk015Step.certifies
      (boundary.trans h014)
  have h016 : recordLowerSeedTailChunk016State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix016 := by
    have boundary : recordLowerSeedTailChunk016Before =
        recordLowerSeedTailChunk015State := by rfl
    exact recordLowerSeedTailChunk016Step.certifies
      (boundary.trans h015)
  have h017 : recordLowerSeedTailChunk017State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix017 := by
    have boundary : recordLowerSeedTailChunk017Before =
        recordLowerSeedTailChunk016State := by rfl
    exact recordLowerSeedTailChunk017Step.certifies
      (boundary.trans h016)
  have h018 : recordLowerSeedTailChunk018State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix018 := by
    have boundary : recordLowerSeedTailChunk018Before =
        recordLowerSeedTailChunk017State := by rfl
    exact recordLowerSeedTailChunk018Step.certifies
      (boundary.trans h017)
  have h019 : recordLowerSeedTailChunk019State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix019 := by
    have boundary : recordLowerSeedTailChunk019Before =
        recordLowerSeedTailChunk018State := by rfl
    exact recordLowerSeedTailChunk019Step.certifies
      (boundary.trans h018)
  have h020 : recordLowerSeedTailChunk020State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix020 := by
    have boundary : recordLowerSeedTailChunk020Before =
        recordLowerSeedTailChunk019State := by rfl
    exact recordLowerSeedTailChunk020Step.certifies
      (boundary.trans h019)
  have h021 : recordLowerSeedTailChunk021State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix021 := by
    have boundary : recordLowerSeedTailChunk021Before =
        recordLowerSeedTailChunk020State := by rfl
    exact recordLowerSeedTailChunk021Step.certifies
      (boundary.trans h020)
  have h022 : recordLowerSeedTailChunk022State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix022 := by
    have boundary : recordLowerSeedTailChunk022Before =
        recordLowerSeedTailChunk021State := by rfl
    exact recordLowerSeedTailChunk022Step.certifies
      (boundary.trans h021)
  have h023 : recordLowerSeedTailChunk023State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix023 := by
    have boundary : recordLowerSeedTailChunk023Before =
        recordLowerSeedTailChunk022State := by rfl
    exact recordLowerSeedTailChunk023Step.certifies
      (boundary.trans h022)
  have h024 : recordLowerSeedTailChunk024State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix024 := by
    have boundary : recordLowerSeedTailChunk024Before =
        recordLowerSeedTailChunk023State := by rfl
    exact recordLowerSeedTailChunk024Step.certifies
      (boundary.trans h023)
  have h025 : recordLowerSeedTailChunk025State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix025 := by
    have boundary : recordLowerSeedTailChunk025Before =
        recordLowerSeedTailChunk024State := by rfl
    exact recordLowerSeedTailChunk025Step.certifies
      (boundary.trans h024)
  have h026 : recordLowerSeedTailChunk026State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix026 := by
    have boundary : recordLowerSeedTailChunk026Before =
        recordLowerSeedTailChunk025State := by rfl
    exact recordLowerSeedTailChunk026Step.certifies
      (boundary.trans h025)
  have h027 : recordLowerSeedTailChunk027State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix027 := by
    have boundary : recordLowerSeedTailChunk027Before =
        recordLowerSeedTailChunk026State := by rfl
    exact recordLowerSeedTailChunk027Step.certifies
      (boundary.trans h026)
  have h028 : recordLowerSeedTailChunk028State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix028 := by
    have boundary : recordLowerSeedTailChunk028Before =
        recordLowerSeedTailChunk027State := by rfl
    exact recordLowerSeedTailChunk028Step.certifies
      (boundary.trans h027)
  have h029 : recordLowerSeedTailChunk029State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix029 := by
    have boundary : recordLowerSeedTailChunk029Before =
        recordLowerSeedTailChunk028State := by rfl
    exact recordLowerSeedTailChunk029Step.certifies
      (boundary.trans h028)
  have h030 : recordLowerSeedTailChunk030State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix030 := by
    have boundary : recordLowerSeedTailChunk030Before =
        recordLowerSeedTailChunk029State := by rfl
    exact recordLowerSeedTailChunk030Step.certifies
      (boundary.trans h029)
  have h031 : recordLowerSeedTailChunk031State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix031 := by
    have boundary : recordLowerSeedTailChunk031Before =
        recordLowerSeedTailChunk030State := by rfl
    exact recordLowerSeedTailChunk031Step.certifies
      (boundary.trans h030)
  have h032 : recordLowerSeedTailChunk032State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix032 := by
    have boundary : recordLowerSeedTailChunk032Before =
        recordLowerSeedTailChunk031State := by rfl
    exact recordLowerSeedTailChunk032Step.certifies
      (boundary.trans h031)
  have h033 : recordLowerSeedTailChunk033State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix033 := by
    have boundary : recordLowerSeedTailChunk033Before =
        recordLowerSeedTailChunk032State := by rfl
    exact recordLowerSeedTailChunk033Step.certifies
      (boundary.trans h032)
  have h034 : recordLowerSeedTailChunk034State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix034 := by
    have boundary : recordLowerSeedTailChunk034Before =
        recordLowerSeedTailChunk033State := by rfl
    exact recordLowerSeedTailChunk034Step.certifies
      (boundary.trans h033)
  have h035 : recordLowerSeedTailChunk035State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix035 := by
    have boundary : recordLowerSeedTailChunk035Before =
        recordLowerSeedTailChunk034State := by rfl
    exact recordLowerSeedTailChunk035Step.certifies
      (boundary.trans h034)
  have h036 : recordLowerSeedTailChunk036State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix036 := by
    have boundary : recordLowerSeedTailChunk036Before =
        recordLowerSeedTailChunk035State := by rfl
    exact recordLowerSeedTailChunk036Step.certifies
      (boundary.trans h035)
  have h037 : recordLowerSeedTailChunk037State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix037 := by
    have boundary : recordLowerSeedTailChunk037Before =
        recordLowerSeedTailChunk036State := by rfl
    exact recordLowerSeedTailChunk037Step.certifies
      (boundary.trans h036)
  have h038 : recordLowerSeedTailChunk038State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix038 := by
    have boundary : recordLowerSeedTailChunk038Before =
        recordLowerSeedTailChunk037State := by rfl
    exact recordLowerSeedTailChunk038Step.certifies
      (boundary.trans h037)
  have h039 : recordLowerSeedTailChunk039State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix039 := by
    have boundary : recordLowerSeedTailChunk039Before =
        recordLowerSeedTailChunk038State := by rfl
    exact recordLowerSeedTailChunk039Step.certifies
      (boundary.trans h038)
  have h040 : recordLowerSeedTailChunk040State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix040 := by
    have boundary : recordLowerSeedTailChunk040Before =
        recordLowerSeedTailChunk039State := by rfl
    exact recordLowerSeedTailChunk040Step.certifies
      (boundary.trans h039)
  exact h040

end PrimeFactorUnimodality
