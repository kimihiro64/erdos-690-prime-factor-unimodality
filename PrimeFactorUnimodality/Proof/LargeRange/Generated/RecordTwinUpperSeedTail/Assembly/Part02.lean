import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Assembly.Part01
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part041
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part042
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part043
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part044
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part045
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part046
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part047
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part048
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part049
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part050
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part051
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part052
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part053
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part054
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part055
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part056
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part057
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part058
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part059
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part060
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part061
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part062
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part063
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part064
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part065
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part066
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part067
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part068
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part069
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part070
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part071
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part072
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part073
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part074
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part075
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part076
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part077
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part078
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part079
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part080

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-upper-seed-base11.json` (semantic SHA-256 `493791f7b41de1500c4b830f254f9f92fd9c5d50d639b62aa2b46ca48591321f`, excluding elapsed time). Semantic tail assembly group 2. -/

namespace PrimeFactorUnimodality

theorem recordUpperSeedTailGroup02_semantic :
    recordUpperSeedTailChunk080State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix080 := by
  have h041 : recordUpperSeedTailChunk041State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix041 := by
    have prior : recordUpperSeedTailChunk041Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix040 := by
      simpa only [
        recordUpperSeedTailChunk041Before,
        recordUpperSeedTailChunk040State] using recordUpperSeedTailGroup01_semantic
    simpa only [recordUpperSeedTailPrefix041] using
      recordUpperSeedTailChunk041Step.certifies prior
  have h042 : recordUpperSeedTailChunk042State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix042 := by
    have prior : recordUpperSeedTailChunk042Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix041 := by
      simpa only [
        recordUpperSeedTailChunk042Before,
        recordUpperSeedTailChunk041State] using h041
    simpa only [recordUpperSeedTailPrefix042] using
      recordUpperSeedTailChunk042Step.certifies prior
  have h043 : recordUpperSeedTailChunk043State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix043 := by
    have prior : recordUpperSeedTailChunk043Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix042 := by
      simpa only [
        recordUpperSeedTailChunk043Before,
        recordUpperSeedTailChunk042State] using h042
    simpa only [recordUpperSeedTailPrefix043] using
      recordUpperSeedTailChunk043Step.certifies prior
  have h044 : recordUpperSeedTailChunk044State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix044 := by
    have prior : recordUpperSeedTailChunk044Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix043 := by
      simpa only [
        recordUpperSeedTailChunk044Before,
        recordUpperSeedTailChunk043State] using h043
    simpa only [recordUpperSeedTailPrefix044] using
      recordUpperSeedTailChunk044Step.certifies prior
  have h045 : recordUpperSeedTailChunk045State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix045 := by
    have prior : recordUpperSeedTailChunk045Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix044 := by
      simpa only [
        recordUpperSeedTailChunk045Before,
        recordUpperSeedTailChunk044State] using h044
    simpa only [recordUpperSeedTailPrefix045] using
      recordUpperSeedTailChunk045Step.certifies prior
  have h046 : recordUpperSeedTailChunk046State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix046 := by
    have prior : recordUpperSeedTailChunk046Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix045 := by
      simpa only [
        recordUpperSeedTailChunk046Before,
        recordUpperSeedTailChunk045State] using h045
    simpa only [recordUpperSeedTailPrefix046] using
      recordUpperSeedTailChunk046Step.certifies prior
  have h047 : recordUpperSeedTailChunk047State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix047 := by
    have prior : recordUpperSeedTailChunk047Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix046 := by
      simpa only [
        recordUpperSeedTailChunk047Before,
        recordUpperSeedTailChunk046State] using h046
    simpa only [recordUpperSeedTailPrefix047] using
      recordUpperSeedTailChunk047Step.certifies prior
  have h048 : recordUpperSeedTailChunk048State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix048 := by
    have prior : recordUpperSeedTailChunk048Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix047 := by
      simpa only [
        recordUpperSeedTailChunk048Before,
        recordUpperSeedTailChunk047State] using h047
    simpa only [recordUpperSeedTailPrefix048] using
      recordUpperSeedTailChunk048Step.certifies prior
  have h049 : recordUpperSeedTailChunk049State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix049 := by
    have prior : recordUpperSeedTailChunk049Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix048 := by
      simpa only [
        recordUpperSeedTailChunk049Before,
        recordUpperSeedTailChunk048State] using h048
    simpa only [recordUpperSeedTailPrefix049] using
      recordUpperSeedTailChunk049Step.certifies prior
  have h050 : recordUpperSeedTailChunk050State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix050 := by
    have prior : recordUpperSeedTailChunk050Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix049 := by
      simpa only [
        recordUpperSeedTailChunk050Before,
        recordUpperSeedTailChunk049State] using h049
    simpa only [recordUpperSeedTailPrefix050] using
      recordUpperSeedTailChunk050Step.certifies prior
  have h051 : recordUpperSeedTailChunk051State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix051 := by
    have prior : recordUpperSeedTailChunk051Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix050 := by
      simpa only [
        recordUpperSeedTailChunk051Before,
        recordUpperSeedTailChunk050State] using h050
    simpa only [recordUpperSeedTailPrefix051] using
      recordUpperSeedTailChunk051Step.certifies prior
  have h052 : recordUpperSeedTailChunk052State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix052 := by
    have prior : recordUpperSeedTailChunk052Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix051 := by
      simpa only [
        recordUpperSeedTailChunk052Before,
        recordUpperSeedTailChunk051State] using h051
    simpa only [recordUpperSeedTailPrefix052] using
      recordUpperSeedTailChunk052Step.certifies prior
  have h053 : recordUpperSeedTailChunk053State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix053 := by
    have prior : recordUpperSeedTailChunk053Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix052 := by
      simpa only [
        recordUpperSeedTailChunk053Before,
        recordUpperSeedTailChunk052State] using h052
    simpa only [recordUpperSeedTailPrefix053] using
      recordUpperSeedTailChunk053Step.certifies prior
  have h054 : recordUpperSeedTailChunk054State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix054 := by
    have prior : recordUpperSeedTailChunk054Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix053 := by
      simpa only [
        recordUpperSeedTailChunk054Before,
        recordUpperSeedTailChunk053State] using h053
    simpa only [recordUpperSeedTailPrefix054] using
      recordUpperSeedTailChunk054Step.certifies prior
  have h055 : recordUpperSeedTailChunk055State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix055 := by
    have prior : recordUpperSeedTailChunk055Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix054 := by
      simpa only [
        recordUpperSeedTailChunk055Before,
        recordUpperSeedTailChunk054State] using h054
    simpa only [recordUpperSeedTailPrefix055] using
      recordUpperSeedTailChunk055Step.certifies prior
  have h056 : recordUpperSeedTailChunk056State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix056 := by
    have prior : recordUpperSeedTailChunk056Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix055 := by
      simpa only [
        recordUpperSeedTailChunk056Before,
        recordUpperSeedTailChunk055State] using h055
    simpa only [recordUpperSeedTailPrefix056] using
      recordUpperSeedTailChunk056Step.certifies prior
  have h057 : recordUpperSeedTailChunk057State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix057 := by
    have prior : recordUpperSeedTailChunk057Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix056 := by
      simpa only [
        recordUpperSeedTailChunk057Before,
        recordUpperSeedTailChunk056State] using h056
    simpa only [recordUpperSeedTailPrefix057] using
      recordUpperSeedTailChunk057Step.certifies prior
  have h058 : recordUpperSeedTailChunk058State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix058 := by
    have prior : recordUpperSeedTailChunk058Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix057 := by
      simpa only [
        recordUpperSeedTailChunk058Before,
        recordUpperSeedTailChunk057State] using h057
    simpa only [recordUpperSeedTailPrefix058] using
      recordUpperSeedTailChunk058Step.certifies prior
  have h059 : recordUpperSeedTailChunk059State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix059 := by
    have prior : recordUpperSeedTailChunk059Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix058 := by
      simpa only [
        recordUpperSeedTailChunk059Before,
        recordUpperSeedTailChunk058State] using h058
    simpa only [recordUpperSeedTailPrefix059] using
      recordUpperSeedTailChunk059Step.certifies prior
  have h060 : recordUpperSeedTailChunk060State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix060 := by
    have prior : recordUpperSeedTailChunk060Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix059 := by
      simpa only [
        recordUpperSeedTailChunk060Before,
        recordUpperSeedTailChunk059State] using h059
    simpa only [recordUpperSeedTailPrefix060] using
      recordUpperSeedTailChunk060Step.certifies prior
  have h061 : recordUpperSeedTailChunk061State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix061 := by
    have prior : recordUpperSeedTailChunk061Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix060 := by
      simpa only [
        recordUpperSeedTailChunk061Before,
        recordUpperSeedTailChunk060State] using h060
    simpa only [recordUpperSeedTailPrefix061] using
      recordUpperSeedTailChunk061Step.certifies prior
  have h062 : recordUpperSeedTailChunk062State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix062 := by
    have prior : recordUpperSeedTailChunk062Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix061 := by
      simpa only [
        recordUpperSeedTailChunk062Before,
        recordUpperSeedTailChunk061State] using h061
    simpa only [recordUpperSeedTailPrefix062] using
      recordUpperSeedTailChunk062Step.certifies prior
  have h063 : recordUpperSeedTailChunk063State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix063 := by
    have prior : recordUpperSeedTailChunk063Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix062 := by
      simpa only [
        recordUpperSeedTailChunk063Before,
        recordUpperSeedTailChunk062State] using h062
    simpa only [recordUpperSeedTailPrefix063] using
      recordUpperSeedTailChunk063Step.certifies prior
  have h064 : recordUpperSeedTailChunk064State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix064 := by
    have prior : recordUpperSeedTailChunk064Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix063 := by
      simpa only [
        recordUpperSeedTailChunk064Before,
        recordUpperSeedTailChunk063State] using h063
    simpa only [recordUpperSeedTailPrefix064] using
      recordUpperSeedTailChunk064Step.certifies prior
  have h065 : recordUpperSeedTailChunk065State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix065 := by
    have prior : recordUpperSeedTailChunk065Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix064 := by
      simpa only [
        recordUpperSeedTailChunk065Before,
        recordUpperSeedTailChunk064State] using h064
    simpa only [recordUpperSeedTailPrefix065] using
      recordUpperSeedTailChunk065Step.certifies prior
  have h066 : recordUpperSeedTailChunk066State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix066 := by
    have prior : recordUpperSeedTailChunk066Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix065 := by
      simpa only [
        recordUpperSeedTailChunk066Before,
        recordUpperSeedTailChunk065State] using h065
    simpa only [recordUpperSeedTailPrefix066] using
      recordUpperSeedTailChunk066Step.certifies prior
  have h067 : recordUpperSeedTailChunk067State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix067 := by
    have prior : recordUpperSeedTailChunk067Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix066 := by
      simpa only [
        recordUpperSeedTailChunk067Before,
        recordUpperSeedTailChunk066State] using h066
    simpa only [recordUpperSeedTailPrefix067] using
      recordUpperSeedTailChunk067Step.certifies prior
  have h068 : recordUpperSeedTailChunk068State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix068 := by
    have prior : recordUpperSeedTailChunk068Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix067 := by
      simpa only [
        recordUpperSeedTailChunk068Before,
        recordUpperSeedTailChunk067State] using h067
    simpa only [recordUpperSeedTailPrefix068] using
      recordUpperSeedTailChunk068Step.certifies prior
  have h069 : recordUpperSeedTailChunk069State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix069 := by
    have prior : recordUpperSeedTailChunk069Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix068 := by
      simpa only [
        recordUpperSeedTailChunk069Before,
        recordUpperSeedTailChunk068State] using h068
    simpa only [recordUpperSeedTailPrefix069] using
      recordUpperSeedTailChunk069Step.certifies prior
  have h070 : recordUpperSeedTailChunk070State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix070 := by
    have prior : recordUpperSeedTailChunk070Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix069 := by
      simpa only [
        recordUpperSeedTailChunk070Before,
        recordUpperSeedTailChunk069State] using h069
    simpa only [recordUpperSeedTailPrefix070] using
      recordUpperSeedTailChunk070Step.certifies prior
  have h071 : recordUpperSeedTailChunk071State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix071 := by
    have prior : recordUpperSeedTailChunk071Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix070 := by
      simpa only [
        recordUpperSeedTailChunk071Before,
        recordUpperSeedTailChunk070State] using h070
    simpa only [recordUpperSeedTailPrefix071] using
      recordUpperSeedTailChunk071Step.certifies prior
  have h072 : recordUpperSeedTailChunk072State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix072 := by
    have prior : recordUpperSeedTailChunk072Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix071 := by
      simpa only [
        recordUpperSeedTailChunk072Before,
        recordUpperSeedTailChunk071State] using h071
    simpa only [recordUpperSeedTailPrefix072] using
      recordUpperSeedTailChunk072Step.certifies prior
  have h073 : recordUpperSeedTailChunk073State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix073 := by
    have prior : recordUpperSeedTailChunk073Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix072 := by
      simpa only [
        recordUpperSeedTailChunk073Before,
        recordUpperSeedTailChunk072State] using h072
    simpa only [recordUpperSeedTailPrefix073] using
      recordUpperSeedTailChunk073Step.certifies prior
  have h074 : recordUpperSeedTailChunk074State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix074 := by
    have prior : recordUpperSeedTailChunk074Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix073 := by
      simpa only [
        recordUpperSeedTailChunk074Before,
        recordUpperSeedTailChunk073State] using h073
    simpa only [recordUpperSeedTailPrefix074] using
      recordUpperSeedTailChunk074Step.certifies prior
  have h075 : recordUpperSeedTailChunk075State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix075 := by
    have prior : recordUpperSeedTailChunk075Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix074 := by
      simpa only [
        recordUpperSeedTailChunk075Before,
        recordUpperSeedTailChunk074State] using h074
    simpa only [recordUpperSeedTailPrefix075] using
      recordUpperSeedTailChunk075Step.certifies prior
  have h076 : recordUpperSeedTailChunk076State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix076 := by
    have prior : recordUpperSeedTailChunk076Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix075 := by
      simpa only [
        recordUpperSeedTailChunk076Before,
        recordUpperSeedTailChunk075State] using h075
    simpa only [recordUpperSeedTailPrefix076] using
      recordUpperSeedTailChunk076Step.certifies prior
  have h077 : recordUpperSeedTailChunk077State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix077 := by
    have prior : recordUpperSeedTailChunk077Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix076 := by
      simpa only [
        recordUpperSeedTailChunk077Before,
        recordUpperSeedTailChunk076State] using h076
    simpa only [recordUpperSeedTailPrefix077] using
      recordUpperSeedTailChunk077Step.certifies prior
  have h078 : recordUpperSeedTailChunk078State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix078 := by
    have prior : recordUpperSeedTailChunk078Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix077 := by
      simpa only [
        recordUpperSeedTailChunk078Before,
        recordUpperSeedTailChunk077State] using h077
    simpa only [recordUpperSeedTailPrefix078] using
      recordUpperSeedTailChunk078Step.certifies prior
  have h079 : recordUpperSeedTailChunk079State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix079 := by
    have prior : recordUpperSeedTailChunk079Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix078 := by
      simpa only [
        recordUpperSeedTailChunk079Before,
        recordUpperSeedTailChunk078State] using h078
    simpa only [recordUpperSeedTailPrefix079] using
      recordUpperSeedTailChunk079Step.certifies prior
  have h080 : recordUpperSeedTailChunk080State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix080 := by
    have prior : recordUpperSeedTailChunk080Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix079 := by
      simpa only [
        recordUpperSeedTailChunk080Before,
        recordUpperSeedTailChunk079State] using h079
    simpa only [recordUpperSeedTailPrefix080] using
      recordUpperSeedTailChunk080Step.certifies prior
  exact h080

end PrimeFactorUnimodality
