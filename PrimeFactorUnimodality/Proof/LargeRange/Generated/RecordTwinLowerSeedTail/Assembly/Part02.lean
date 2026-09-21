import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Assembly.Part01
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part080

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-lower-seed.json` (semantic SHA-256 `3ce105dad06099400dfd2e30c65d47c6e02828915452a8459553c3bb0eb78b73`, excluding elapsed time). Semantic tail assembly group 2. -/

namespace PrimeFactorUnimodality

theorem recordLowerSeedTailGroup02_semantic :
    recordLowerSeedTailChunk080State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix080 := by
  have h041 : recordLowerSeedTailChunk041State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix041 := by
    have prior : recordLowerSeedTailChunk041Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix040 := by
      simpa only [
        recordLowerSeedTailChunk041Before,
        recordLowerSeedTailChunk040State] using recordLowerSeedTailGroup01_semantic
    simpa only [recordLowerSeedTailPrefix041] using
      recordLowerSeedTailChunk041Step.certifies prior
  have h042 : recordLowerSeedTailChunk042State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix042 := by
    have prior : recordLowerSeedTailChunk042Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix041 := by
      simpa only [
        recordLowerSeedTailChunk042Before,
        recordLowerSeedTailChunk041State] using h041
    simpa only [recordLowerSeedTailPrefix042] using
      recordLowerSeedTailChunk042Step.certifies prior
  have h043 : recordLowerSeedTailChunk043State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix043 := by
    have prior : recordLowerSeedTailChunk043Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix042 := by
      simpa only [
        recordLowerSeedTailChunk043Before,
        recordLowerSeedTailChunk042State] using h042
    simpa only [recordLowerSeedTailPrefix043] using
      recordLowerSeedTailChunk043Step.certifies prior
  have h044 : recordLowerSeedTailChunk044State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix044 := by
    have prior : recordLowerSeedTailChunk044Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix043 := by
      simpa only [
        recordLowerSeedTailChunk044Before,
        recordLowerSeedTailChunk043State] using h043
    simpa only [recordLowerSeedTailPrefix044] using
      recordLowerSeedTailChunk044Step.certifies prior
  have h045 : recordLowerSeedTailChunk045State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix045 := by
    have prior : recordLowerSeedTailChunk045Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix044 := by
      simpa only [
        recordLowerSeedTailChunk045Before,
        recordLowerSeedTailChunk044State] using h044
    simpa only [recordLowerSeedTailPrefix045] using
      recordLowerSeedTailChunk045Step.certifies prior
  have h046 : recordLowerSeedTailChunk046State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix046 := by
    have prior : recordLowerSeedTailChunk046Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix045 := by
      simpa only [
        recordLowerSeedTailChunk046Before,
        recordLowerSeedTailChunk045State] using h045
    simpa only [recordLowerSeedTailPrefix046] using
      recordLowerSeedTailChunk046Step.certifies prior
  have h047 : recordLowerSeedTailChunk047State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix047 := by
    have prior : recordLowerSeedTailChunk047Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix046 := by
      simpa only [
        recordLowerSeedTailChunk047Before,
        recordLowerSeedTailChunk046State] using h046
    simpa only [recordLowerSeedTailPrefix047] using
      recordLowerSeedTailChunk047Step.certifies prior
  have h048 : recordLowerSeedTailChunk048State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix048 := by
    have prior : recordLowerSeedTailChunk048Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix047 := by
      simpa only [
        recordLowerSeedTailChunk048Before,
        recordLowerSeedTailChunk047State] using h047
    simpa only [recordLowerSeedTailPrefix048] using
      recordLowerSeedTailChunk048Step.certifies prior
  have h049 : recordLowerSeedTailChunk049State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix049 := by
    have prior : recordLowerSeedTailChunk049Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix048 := by
      simpa only [
        recordLowerSeedTailChunk049Before,
        recordLowerSeedTailChunk048State] using h048
    simpa only [recordLowerSeedTailPrefix049] using
      recordLowerSeedTailChunk049Step.certifies prior
  have h050 : recordLowerSeedTailChunk050State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix050 := by
    have prior : recordLowerSeedTailChunk050Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix049 := by
      simpa only [
        recordLowerSeedTailChunk050Before,
        recordLowerSeedTailChunk049State] using h049
    simpa only [recordLowerSeedTailPrefix050] using
      recordLowerSeedTailChunk050Step.certifies prior
  have h051 : recordLowerSeedTailChunk051State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix051 := by
    have prior : recordLowerSeedTailChunk051Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix050 := by
      simpa only [
        recordLowerSeedTailChunk051Before,
        recordLowerSeedTailChunk050State] using h050
    simpa only [recordLowerSeedTailPrefix051] using
      recordLowerSeedTailChunk051Step.certifies prior
  have h052 : recordLowerSeedTailChunk052State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix052 := by
    have prior : recordLowerSeedTailChunk052Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix051 := by
      simpa only [
        recordLowerSeedTailChunk052Before,
        recordLowerSeedTailChunk051State] using h051
    simpa only [recordLowerSeedTailPrefix052] using
      recordLowerSeedTailChunk052Step.certifies prior
  have h053 : recordLowerSeedTailChunk053State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix053 := by
    have prior : recordLowerSeedTailChunk053Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix052 := by
      simpa only [
        recordLowerSeedTailChunk053Before,
        recordLowerSeedTailChunk052State] using h052
    simpa only [recordLowerSeedTailPrefix053] using
      recordLowerSeedTailChunk053Step.certifies prior
  have h054 : recordLowerSeedTailChunk054State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix054 := by
    have prior : recordLowerSeedTailChunk054Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix053 := by
      simpa only [
        recordLowerSeedTailChunk054Before,
        recordLowerSeedTailChunk053State] using h053
    simpa only [recordLowerSeedTailPrefix054] using
      recordLowerSeedTailChunk054Step.certifies prior
  have h055 : recordLowerSeedTailChunk055State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix055 := by
    have prior : recordLowerSeedTailChunk055Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix054 := by
      simpa only [
        recordLowerSeedTailChunk055Before,
        recordLowerSeedTailChunk054State] using h054
    simpa only [recordLowerSeedTailPrefix055] using
      recordLowerSeedTailChunk055Step.certifies prior
  have h056 : recordLowerSeedTailChunk056State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix056 := by
    have prior : recordLowerSeedTailChunk056Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix055 := by
      simpa only [
        recordLowerSeedTailChunk056Before,
        recordLowerSeedTailChunk055State] using h055
    simpa only [recordLowerSeedTailPrefix056] using
      recordLowerSeedTailChunk056Step.certifies prior
  have h057 : recordLowerSeedTailChunk057State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix057 := by
    have prior : recordLowerSeedTailChunk057Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix056 := by
      simpa only [
        recordLowerSeedTailChunk057Before,
        recordLowerSeedTailChunk056State] using h056
    simpa only [recordLowerSeedTailPrefix057] using
      recordLowerSeedTailChunk057Step.certifies prior
  have h058 : recordLowerSeedTailChunk058State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix058 := by
    have prior : recordLowerSeedTailChunk058Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix057 := by
      simpa only [
        recordLowerSeedTailChunk058Before,
        recordLowerSeedTailChunk057State] using h057
    simpa only [recordLowerSeedTailPrefix058] using
      recordLowerSeedTailChunk058Step.certifies prior
  have h059 : recordLowerSeedTailChunk059State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix059 := by
    have prior : recordLowerSeedTailChunk059Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix058 := by
      simpa only [
        recordLowerSeedTailChunk059Before,
        recordLowerSeedTailChunk058State] using h058
    simpa only [recordLowerSeedTailPrefix059] using
      recordLowerSeedTailChunk059Step.certifies prior
  have h060 : recordLowerSeedTailChunk060State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix060 := by
    have prior : recordLowerSeedTailChunk060Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix059 := by
      simpa only [
        recordLowerSeedTailChunk060Before,
        recordLowerSeedTailChunk059State] using h059
    simpa only [recordLowerSeedTailPrefix060] using
      recordLowerSeedTailChunk060Step.certifies prior
  have h061 : recordLowerSeedTailChunk061State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix061 := by
    have prior : recordLowerSeedTailChunk061Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix060 := by
      simpa only [
        recordLowerSeedTailChunk061Before,
        recordLowerSeedTailChunk060State] using h060
    simpa only [recordLowerSeedTailPrefix061] using
      recordLowerSeedTailChunk061Step.certifies prior
  have h062 : recordLowerSeedTailChunk062State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix062 := by
    have prior : recordLowerSeedTailChunk062Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix061 := by
      simpa only [
        recordLowerSeedTailChunk062Before,
        recordLowerSeedTailChunk061State] using h061
    simpa only [recordLowerSeedTailPrefix062] using
      recordLowerSeedTailChunk062Step.certifies prior
  have h063 : recordLowerSeedTailChunk063State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix063 := by
    have prior : recordLowerSeedTailChunk063Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix062 := by
      simpa only [
        recordLowerSeedTailChunk063Before,
        recordLowerSeedTailChunk062State] using h062
    simpa only [recordLowerSeedTailPrefix063] using
      recordLowerSeedTailChunk063Step.certifies prior
  have h064 : recordLowerSeedTailChunk064State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix064 := by
    have prior : recordLowerSeedTailChunk064Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix063 := by
      simpa only [
        recordLowerSeedTailChunk064Before,
        recordLowerSeedTailChunk063State] using h063
    simpa only [recordLowerSeedTailPrefix064] using
      recordLowerSeedTailChunk064Step.certifies prior
  have h065 : recordLowerSeedTailChunk065State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix065 := by
    have prior : recordLowerSeedTailChunk065Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix064 := by
      simpa only [
        recordLowerSeedTailChunk065Before,
        recordLowerSeedTailChunk064State] using h064
    simpa only [recordLowerSeedTailPrefix065] using
      recordLowerSeedTailChunk065Step.certifies prior
  have h066 : recordLowerSeedTailChunk066State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix066 := by
    have prior : recordLowerSeedTailChunk066Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix065 := by
      simpa only [
        recordLowerSeedTailChunk066Before,
        recordLowerSeedTailChunk065State] using h065
    simpa only [recordLowerSeedTailPrefix066] using
      recordLowerSeedTailChunk066Step.certifies prior
  have h067 : recordLowerSeedTailChunk067State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix067 := by
    have prior : recordLowerSeedTailChunk067Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix066 := by
      simpa only [
        recordLowerSeedTailChunk067Before,
        recordLowerSeedTailChunk066State] using h066
    simpa only [recordLowerSeedTailPrefix067] using
      recordLowerSeedTailChunk067Step.certifies prior
  have h068 : recordLowerSeedTailChunk068State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix068 := by
    have prior : recordLowerSeedTailChunk068Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix067 := by
      simpa only [
        recordLowerSeedTailChunk068Before,
        recordLowerSeedTailChunk067State] using h067
    simpa only [recordLowerSeedTailPrefix068] using
      recordLowerSeedTailChunk068Step.certifies prior
  have h069 : recordLowerSeedTailChunk069State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix069 := by
    have prior : recordLowerSeedTailChunk069Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix068 := by
      simpa only [
        recordLowerSeedTailChunk069Before,
        recordLowerSeedTailChunk068State] using h068
    simpa only [recordLowerSeedTailPrefix069] using
      recordLowerSeedTailChunk069Step.certifies prior
  have h070 : recordLowerSeedTailChunk070State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix070 := by
    have prior : recordLowerSeedTailChunk070Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix069 := by
      simpa only [
        recordLowerSeedTailChunk070Before,
        recordLowerSeedTailChunk069State] using h069
    simpa only [recordLowerSeedTailPrefix070] using
      recordLowerSeedTailChunk070Step.certifies prior
  have h071 : recordLowerSeedTailChunk071State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix071 := by
    have prior : recordLowerSeedTailChunk071Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix070 := by
      simpa only [
        recordLowerSeedTailChunk071Before,
        recordLowerSeedTailChunk070State] using h070
    simpa only [recordLowerSeedTailPrefix071] using
      recordLowerSeedTailChunk071Step.certifies prior
  have h072 : recordLowerSeedTailChunk072State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix072 := by
    have prior : recordLowerSeedTailChunk072Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix071 := by
      simpa only [
        recordLowerSeedTailChunk072Before,
        recordLowerSeedTailChunk071State] using h071
    simpa only [recordLowerSeedTailPrefix072] using
      recordLowerSeedTailChunk072Step.certifies prior
  have h073 : recordLowerSeedTailChunk073State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix073 := by
    have prior : recordLowerSeedTailChunk073Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix072 := by
      simpa only [
        recordLowerSeedTailChunk073Before,
        recordLowerSeedTailChunk072State] using h072
    simpa only [recordLowerSeedTailPrefix073] using
      recordLowerSeedTailChunk073Step.certifies prior
  have h074 : recordLowerSeedTailChunk074State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix074 := by
    have prior : recordLowerSeedTailChunk074Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix073 := by
      simpa only [
        recordLowerSeedTailChunk074Before,
        recordLowerSeedTailChunk073State] using h073
    simpa only [recordLowerSeedTailPrefix074] using
      recordLowerSeedTailChunk074Step.certifies prior
  have h075 : recordLowerSeedTailChunk075State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix075 := by
    have prior : recordLowerSeedTailChunk075Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix074 := by
      simpa only [
        recordLowerSeedTailChunk075Before,
        recordLowerSeedTailChunk074State] using h074
    simpa only [recordLowerSeedTailPrefix075] using
      recordLowerSeedTailChunk075Step.certifies prior
  have h076 : recordLowerSeedTailChunk076State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix076 := by
    have prior : recordLowerSeedTailChunk076Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix075 := by
      simpa only [
        recordLowerSeedTailChunk076Before,
        recordLowerSeedTailChunk075State] using h075
    simpa only [recordLowerSeedTailPrefix076] using
      recordLowerSeedTailChunk076Step.certifies prior
  have h077 : recordLowerSeedTailChunk077State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix077 := by
    have prior : recordLowerSeedTailChunk077Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix076 := by
      simpa only [
        recordLowerSeedTailChunk077Before,
        recordLowerSeedTailChunk076State] using h076
    simpa only [recordLowerSeedTailPrefix077] using
      recordLowerSeedTailChunk077Step.certifies prior
  have h078 : recordLowerSeedTailChunk078State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix078 := by
    have prior : recordLowerSeedTailChunk078Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix077 := by
      simpa only [
        recordLowerSeedTailChunk078Before,
        recordLowerSeedTailChunk077State] using h077
    simpa only [recordLowerSeedTailPrefix078] using
      recordLowerSeedTailChunk078Step.certifies prior
  have h079 : recordLowerSeedTailChunk079State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix079 := by
    have prior : recordLowerSeedTailChunk079Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix078 := by
      simpa only [
        recordLowerSeedTailChunk079Before,
        recordLowerSeedTailChunk078State] using h078
    simpa only [recordLowerSeedTailPrefix079] using
      recordLowerSeedTailChunk079Step.certifies prior
  have h080 : recordLowerSeedTailChunk080State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix080 := by
    have prior : recordLowerSeedTailChunk080Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix079 := by
      simpa only [
        recordLowerSeedTailChunk080Before,
        recordLowerSeedTailChunk079State] using h079
    simpa only [recordLowerSeedTailPrefix080] using
      recordLowerSeedTailChunk080Step.certifies prior
  exact h080

end PrimeFactorUnimodality
