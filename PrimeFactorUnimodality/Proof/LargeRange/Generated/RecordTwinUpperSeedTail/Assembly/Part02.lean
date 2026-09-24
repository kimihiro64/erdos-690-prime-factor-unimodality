import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Assembly.Part01
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part080

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-upper-seed-base11.json` (semantic SHA-256 `493791f7b41de1500c4b830f254f9f92fd9c5d50d639b62aa2b46ca48591321f`, excluding elapsed time). Semantic tail assembly group 2. -/

namespace PrimeFactorUnimodality

theorem recordUpperSeedTailGroup02_semantic :
    recordUpperSeedTailChunk080State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix080 := by
  have h041 : recordUpperSeedTailChunk041State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix041 := by
    have boundary : recordUpperSeedTailChunk041Before =
        recordUpperSeedTailChunk040State := by rfl
    exact recordUpperSeedTailChunk041Step.certifies
      (boundary.trans recordUpperSeedTailGroup01_semantic)
  have h042 : recordUpperSeedTailChunk042State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix042 := by
    have boundary : recordUpperSeedTailChunk042Before =
        recordUpperSeedTailChunk041State := by rfl
    exact recordUpperSeedTailChunk042Step.certifies
      (boundary.trans h041)
  have h043 : recordUpperSeedTailChunk043State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix043 := by
    have boundary : recordUpperSeedTailChunk043Before =
        recordUpperSeedTailChunk042State := by rfl
    exact recordUpperSeedTailChunk043Step.certifies
      (boundary.trans h042)
  have h044 : recordUpperSeedTailChunk044State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix044 := by
    have boundary : recordUpperSeedTailChunk044Before =
        recordUpperSeedTailChunk043State := by rfl
    exact recordUpperSeedTailChunk044Step.certifies
      (boundary.trans h043)
  have h045 : recordUpperSeedTailChunk045State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix045 := by
    have boundary : recordUpperSeedTailChunk045Before =
        recordUpperSeedTailChunk044State := by rfl
    exact recordUpperSeedTailChunk045Step.certifies
      (boundary.trans h044)
  have h046 : recordUpperSeedTailChunk046State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix046 := by
    have boundary : recordUpperSeedTailChunk046Before =
        recordUpperSeedTailChunk045State := by rfl
    exact recordUpperSeedTailChunk046Step.certifies
      (boundary.trans h045)
  have h047 : recordUpperSeedTailChunk047State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix047 := by
    have boundary : recordUpperSeedTailChunk047Before =
        recordUpperSeedTailChunk046State := by rfl
    exact recordUpperSeedTailChunk047Step.certifies
      (boundary.trans h046)
  have h048 : recordUpperSeedTailChunk048State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix048 := by
    have boundary : recordUpperSeedTailChunk048Before =
        recordUpperSeedTailChunk047State := by rfl
    exact recordUpperSeedTailChunk048Step.certifies
      (boundary.trans h047)
  have h049 : recordUpperSeedTailChunk049State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix049 := by
    have boundary : recordUpperSeedTailChunk049Before =
        recordUpperSeedTailChunk048State := by rfl
    exact recordUpperSeedTailChunk049Step.certifies
      (boundary.trans h048)
  have h050 : recordUpperSeedTailChunk050State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix050 := by
    have boundary : recordUpperSeedTailChunk050Before =
        recordUpperSeedTailChunk049State := by rfl
    exact recordUpperSeedTailChunk050Step.certifies
      (boundary.trans h049)
  have h051 : recordUpperSeedTailChunk051State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix051 := by
    have boundary : recordUpperSeedTailChunk051Before =
        recordUpperSeedTailChunk050State := by rfl
    exact recordUpperSeedTailChunk051Step.certifies
      (boundary.trans h050)
  have h052 : recordUpperSeedTailChunk052State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix052 := by
    have boundary : recordUpperSeedTailChunk052Before =
        recordUpperSeedTailChunk051State := by rfl
    exact recordUpperSeedTailChunk052Step.certifies
      (boundary.trans h051)
  have h053 : recordUpperSeedTailChunk053State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix053 := by
    have boundary : recordUpperSeedTailChunk053Before =
        recordUpperSeedTailChunk052State := by rfl
    exact recordUpperSeedTailChunk053Step.certifies
      (boundary.trans h052)
  have h054 : recordUpperSeedTailChunk054State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix054 := by
    have boundary : recordUpperSeedTailChunk054Before =
        recordUpperSeedTailChunk053State := by rfl
    exact recordUpperSeedTailChunk054Step.certifies
      (boundary.trans h053)
  have h055 : recordUpperSeedTailChunk055State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix055 := by
    have boundary : recordUpperSeedTailChunk055Before =
        recordUpperSeedTailChunk054State := by rfl
    exact recordUpperSeedTailChunk055Step.certifies
      (boundary.trans h054)
  have h056 : recordUpperSeedTailChunk056State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix056 := by
    have boundary : recordUpperSeedTailChunk056Before =
        recordUpperSeedTailChunk055State := by rfl
    exact recordUpperSeedTailChunk056Step.certifies
      (boundary.trans h055)
  have h057 : recordUpperSeedTailChunk057State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix057 := by
    have boundary : recordUpperSeedTailChunk057Before =
        recordUpperSeedTailChunk056State := by rfl
    exact recordUpperSeedTailChunk057Step.certifies
      (boundary.trans h056)
  have h058 : recordUpperSeedTailChunk058State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix058 := by
    have boundary : recordUpperSeedTailChunk058Before =
        recordUpperSeedTailChunk057State := by rfl
    exact recordUpperSeedTailChunk058Step.certifies
      (boundary.trans h057)
  have h059 : recordUpperSeedTailChunk059State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix059 := by
    have boundary : recordUpperSeedTailChunk059Before =
        recordUpperSeedTailChunk058State := by rfl
    exact recordUpperSeedTailChunk059Step.certifies
      (boundary.trans h058)
  have h060 : recordUpperSeedTailChunk060State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix060 := by
    have boundary : recordUpperSeedTailChunk060Before =
        recordUpperSeedTailChunk059State := by rfl
    exact recordUpperSeedTailChunk060Step.certifies
      (boundary.trans h059)
  have h061 : recordUpperSeedTailChunk061State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix061 := by
    have boundary : recordUpperSeedTailChunk061Before =
        recordUpperSeedTailChunk060State := by rfl
    exact recordUpperSeedTailChunk061Step.certifies
      (boundary.trans h060)
  have h062 : recordUpperSeedTailChunk062State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix062 := by
    have boundary : recordUpperSeedTailChunk062Before =
        recordUpperSeedTailChunk061State := by rfl
    exact recordUpperSeedTailChunk062Step.certifies
      (boundary.trans h061)
  have h063 : recordUpperSeedTailChunk063State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix063 := by
    have boundary : recordUpperSeedTailChunk063Before =
        recordUpperSeedTailChunk062State := by rfl
    exact recordUpperSeedTailChunk063Step.certifies
      (boundary.trans h062)
  have h064 : recordUpperSeedTailChunk064State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix064 := by
    have boundary : recordUpperSeedTailChunk064Before =
        recordUpperSeedTailChunk063State := by rfl
    exact recordUpperSeedTailChunk064Step.certifies
      (boundary.trans h063)
  have h065 : recordUpperSeedTailChunk065State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix065 := by
    have boundary : recordUpperSeedTailChunk065Before =
        recordUpperSeedTailChunk064State := by rfl
    exact recordUpperSeedTailChunk065Step.certifies
      (boundary.trans h064)
  have h066 : recordUpperSeedTailChunk066State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix066 := by
    have boundary : recordUpperSeedTailChunk066Before =
        recordUpperSeedTailChunk065State := by rfl
    exact recordUpperSeedTailChunk066Step.certifies
      (boundary.trans h065)
  have h067 : recordUpperSeedTailChunk067State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix067 := by
    have boundary : recordUpperSeedTailChunk067Before =
        recordUpperSeedTailChunk066State := by rfl
    exact recordUpperSeedTailChunk067Step.certifies
      (boundary.trans h066)
  have h068 : recordUpperSeedTailChunk068State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix068 := by
    have boundary : recordUpperSeedTailChunk068Before =
        recordUpperSeedTailChunk067State := by rfl
    exact recordUpperSeedTailChunk068Step.certifies
      (boundary.trans h067)
  have h069 : recordUpperSeedTailChunk069State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix069 := by
    have boundary : recordUpperSeedTailChunk069Before =
        recordUpperSeedTailChunk068State := by rfl
    exact recordUpperSeedTailChunk069Step.certifies
      (boundary.trans h068)
  have h070 : recordUpperSeedTailChunk070State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix070 := by
    have boundary : recordUpperSeedTailChunk070Before =
        recordUpperSeedTailChunk069State := by rfl
    exact recordUpperSeedTailChunk070Step.certifies
      (boundary.trans h069)
  have h071 : recordUpperSeedTailChunk071State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix071 := by
    have boundary : recordUpperSeedTailChunk071Before =
        recordUpperSeedTailChunk070State := by rfl
    exact recordUpperSeedTailChunk071Step.certifies
      (boundary.trans h070)
  have h072 : recordUpperSeedTailChunk072State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix072 := by
    have boundary : recordUpperSeedTailChunk072Before =
        recordUpperSeedTailChunk071State := by rfl
    exact recordUpperSeedTailChunk072Step.certifies
      (boundary.trans h071)
  have h073 : recordUpperSeedTailChunk073State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix073 := by
    have boundary : recordUpperSeedTailChunk073Before =
        recordUpperSeedTailChunk072State := by rfl
    exact recordUpperSeedTailChunk073Step.certifies
      (boundary.trans h072)
  have h074 : recordUpperSeedTailChunk074State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix074 := by
    have boundary : recordUpperSeedTailChunk074Before =
        recordUpperSeedTailChunk073State := by rfl
    exact recordUpperSeedTailChunk074Step.certifies
      (boundary.trans h073)
  have h075 : recordUpperSeedTailChunk075State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix075 := by
    have boundary : recordUpperSeedTailChunk075Before =
        recordUpperSeedTailChunk074State := by rfl
    exact recordUpperSeedTailChunk075Step.certifies
      (boundary.trans h074)
  have h076 : recordUpperSeedTailChunk076State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix076 := by
    have boundary : recordUpperSeedTailChunk076Before =
        recordUpperSeedTailChunk075State := by rfl
    exact recordUpperSeedTailChunk076Step.certifies
      (boundary.trans h075)
  have h077 : recordUpperSeedTailChunk077State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix077 := by
    have boundary : recordUpperSeedTailChunk077Before =
        recordUpperSeedTailChunk076State := by rfl
    exact recordUpperSeedTailChunk077Step.certifies
      (boundary.trans h076)
  have h078 : recordUpperSeedTailChunk078State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix078 := by
    have boundary : recordUpperSeedTailChunk078Before =
        recordUpperSeedTailChunk077State := by rfl
    exact recordUpperSeedTailChunk078Step.certifies
      (boundary.trans h077)
  have h079 : recordUpperSeedTailChunk079State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix079 := by
    have boundary : recordUpperSeedTailChunk079Before =
        recordUpperSeedTailChunk078State := by rfl
    exact recordUpperSeedTailChunk079Step.certifies
      (boundary.trans h078)
  have h080 : recordUpperSeedTailChunk080State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix080 := by
    have boundary : recordUpperSeedTailChunk080Before =
        recordUpperSeedTailChunk079State := by rfl
    exact recordUpperSeedTailChunk080Step.certifies
      (boundary.trans h079)
  exact h080

end PrimeFactorUnimodality
