import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Assembly.Part01
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part080

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-lower-seed.json` (semantic SHA-256 `3ce105dad06099400dfd2e30c65d47c6e02828915452a8459553c3bb0eb78b73`, excluding elapsed time). Semantic tail assembly group 2. -/

namespace PrimeFactorUnimodality

theorem recordLowerSeedTailGroup02_semantic :
    recordLowerSeedTailChunk080State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix080 := by
  have h041 : recordLowerSeedTailChunk041State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix041 := by
    have boundary : recordLowerSeedTailChunk041Before =
        recordLowerSeedTailChunk040State := by rfl
    exact recordLowerSeedTailChunk041Step.certifies
      (boundary.trans recordLowerSeedTailGroup01_semantic)
  have h042 : recordLowerSeedTailChunk042State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix042 := by
    have boundary : recordLowerSeedTailChunk042Before =
        recordLowerSeedTailChunk041State := by rfl
    exact recordLowerSeedTailChunk042Step.certifies
      (boundary.trans h041)
  have h043 : recordLowerSeedTailChunk043State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix043 := by
    have boundary : recordLowerSeedTailChunk043Before =
        recordLowerSeedTailChunk042State := by rfl
    exact recordLowerSeedTailChunk043Step.certifies
      (boundary.trans h042)
  have h044 : recordLowerSeedTailChunk044State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix044 := by
    have boundary : recordLowerSeedTailChunk044Before =
        recordLowerSeedTailChunk043State := by rfl
    exact recordLowerSeedTailChunk044Step.certifies
      (boundary.trans h043)
  have h045 : recordLowerSeedTailChunk045State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix045 := by
    have boundary : recordLowerSeedTailChunk045Before =
        recordLowerSeedTailChunk044State := by rfl
    exact recordLowerSeedTailChunk045Step.certifies
      (boundary.trans h044)
  have h046 : recordLowerSeedTailChunk046State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix046 := by
    have boundary : recordLowerSeedTailChunk046Before =
        recordLowerSeedTailChunk045State := by rfl
    exact recordLowerSeedTailChunk046Step.certifies
      (boundary.trans h045)
  have h047 : recordLowerSeedTailChunk047State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix047 := by
    have boundary : recordLowerSeedTailChunk047Before =
        recordLowerSeedTailChunk046State := by rfl
    exact recordLowerSeedTailChunk047Step.certifies
      (boundary.trans h046)
  have h048 : recordLowerSeedTailChunk048State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix048 := by
    have boundary : recordLowerSeedTailChunk048Before =
        recordLowerSeedTailChunk047State := by rfl
    exact recordLowerSeedTailChunk048Step.certifies
      (boundary.trans h047)
  have h049 : recordLowerSeedTailChunk049State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix049 := by
    have boundary : recordLowerSeedTailChunk049Before =
        recordLowerSeedTailChunk048State := by rfl
    exact recordLowerSeedTailChunk049Step.certifies
      (boundary.trans h048)
  have h050 : recordLowerSeedTailChunk050State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix050 := by
    have boundary : recordLowerSeedTailChunk050Before =
        recordLowerSeedTailChunk049State := by rfl
    exact recordLowerSeedTailChunk050Step.certifies
      (boundary.trans h049)
  have h051 : recordLowerSeedTailChunk051State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix051 := by
    have boundary : recordLowerSeedTailChunk051Before =
        recordLowerSeedTailChunk050State := by rfl
    exact recordLowerSeedTailChunk051Step.certifies
      (boundary.trans h050)
  have h052 : recordLowerSeedTailChunk052State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix052 := by
    have boundary : recordLowerSeedTailChunk052Before =
        recordLowerSeedTailChunk051State := by rfl
    exact recordLowerSeedTailChunk052Step.certifies
      (boundary.trans h051)
  have h053 : recordLowerSeedTailChunk053State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix053 := by
    have boundary : recordLowerSeedTailChunk053Before =
        recordLowerSeedTailChunk052State := by rfl
    exact recordLowerSeedTailChunk053Step.certifies
      (boundary.trans h052)
  have h054 : recordLowerSeedTailChunk054State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix054 := by
    have boundary : recordLowerSeedTailChunk054Before =
        recordLowerSeedTailChunk053State := by rfl
    exact recordLowerSeedTailChunk054Step.certifies
      (boundary.trans h053)
  have h055 : recordLowerSeedTailChunk055State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix055 := by
    have boundary : recordLowerSeedTailChunk055Before =
        recordLowerSeedTailChunk054State := by rfl
    exact recordLowerSeedTailChunk055Step.certifies
      (boundary.trans h054)
  have h056 : recordLowerSeedTailChunk056State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix056 := by
    have boundary : recordLowerSeedTailChunk056Before =
        recordLowerSeedTailChunk055State := by rfl
    exact recordLowerSeedTailChunk056Step.certifies
      (boundary.trans h055)
  have h057 : recordLowerSeedTailChunk057State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix057 := by
    have boundary : recordLowerSeedTailChunk057Before =
        recordLowerSeedTailChunk056State := by rfl
    exact recordLowerSeedTailChunk057Step.certifies
      (boundary.trans h056)
  have h058 : recordLowerSeedTailChunk058State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix058 := by
    have boundary : recordLowerSeedTailChunk058Before =
        recordLowerSeedTailChunk057State := by rfl
    exact recordLowerSeedTailChunk058Step.certifies
      (boundary.trans h057)
  have h059 : recordLowerSeedTailChunk059State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix059 := by
    have boundary : recordLowerSeedTailChunk059Before =
        recordLowerSeedTailChunk058State := by rfl
    exact recordLowerSeedTailChunk059Step.certifies
      (boundary.trans h058)
  have h060 : recordLowerSeedTailChunk060State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix060 := by
    have boundary : recordLowerSeedTailChunk060Before =
        recordLowerSeedTailChunk059State := by rfl
    exact recordLowerSeedTailChunk060Step.certifies
      (boundary.trans h059)
  have h061 : recordLowerSeedTailChunk061State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix061 := by
    have boundary : recordLowerSeedTailChunk061Before =
        recordLowerSeedTailChunk060State := by rfl
    exact recordLowerSeedTailChunk061Step.certifies
      (boundary.trans h060)
  have h062 : recordLowerSeedTailChunk062State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix062 := by
    have boundary : recordLowerSeedTailChunk062Before =
        recordLowerSeedTailChunk061State := by rfl
    exact recordLowerSeedTailChunk062Step.certifies
      (boundary.trans h061)
  have h063 : recordLowerSeedTailChunk063State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix063 := by
    have boundary : recordLowerSeedTailChunk063Before =
        recordLowerSeedTailChunk062State := by rfl
    exact recordLowerSeedTailChunk063Step.certifies
      (boundary.trans h062)
  have h064 : recordLowerSeedTailChunk064State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix064 := by
    have boundary : recordLowerSeedTailChunk064Before =
        recordLowerSeedTailChunk063State := by rfl
    exact recordLowerSeedTailChunk064Step.certifies
      (boundary.trans h063)
  have h065 : recordLowerSeedTailChunk065State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix065 := by
    have boundary : recordLowerSeedTailChunk065Before =
        recordLowerSeedTailChunk064State := by rfl
    exact recordLowerSeedTailChunk065Step.certifies
      (boundary.trans h064)
  have h066 : recordLowerSeedTailChunk066State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix066 := by
    have boundary : recordLowerSeedTailChunk066Before =
        recordLowerSeedTailChunk065State := by rfl
    exact recordLowerSeedTailChunk066Step.certifies
      (boundary.trans h065)
  have h067 : recordLowerSeedTailChunk067State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix067 := by
    have boundary : recordLowerSeedTailChunk067Before =
        recordLowerSeedTailChunk066State := by rfl
    exact recordLowerSeedTailChunk067Step.certifies
      (boundary.trans h066)
  have h068 : recordLowerSeedTailChunk068State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix068 := by
    have boundary : recordLowerSeedTailChunk068Before =
        recordLowerSeedTailChunk067State := by rfl
    exact recordLowerSeedTailChunk068Step.certifies
      (boundary.trans h067)
  have h069 : recordLowerSeedTailChunk069State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix069 := by
    have boundary : recordLowerSeedTailChunk069Before =
        recordLowerSeedTailChunk068State := by rfl
    exact recordLowerSeedTailChunk069Step.certifies
      (boundary.trans h068)
  have h070 : recordLowerSeedTailChunk070State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix070 := by
    have boundary : recordLowerSeedTailChunk070Before =
        recordLowerSeedTailChunk069State := by rfl
    exact recordLowerSeedTailChunk070Step.certifies
      (boundary.trans h069)
  have h071 : recordLowerSeedTailChunk071State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix071 := by
    have boundary : recordLowerSeedTailChunk071Before =
        recordLowerSeedTailChunk070State := by rfl
    exact recordLowerSeedTailChunk071Step.certifies
      (boundary.trans h070)
  have h072 : recordLowerSeedTailChunk072State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix072 := by
    have boundary : recordLowerSeedTailChunk072Before =
        recordLowerSeedTailChunk071State := by rfl
    exact recordLowerSeedTailChunk072Step.certifies
      (boundary.trans h071)
  have h073 : recordLowerSeedTailChunk073State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix073 := by
    have boundary : recordLowerSeedTailChunk073Before =
        recordLowerSeedTailChunk072State := by rfl
    exact recordLowerSeedTailChunk073Step.certifies
      (boundary.trans h072)
  have h074 : recordLowerSeedTailChunk074State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix074 := by
    have boundary : recordLowerSeedTailChunk074Before =
        recordLowerSeedTailChunk073State := by rfl
    exact recordLowerSeedTailChunk074Step.certifies
      (boundary.trans h073)
  have h075 : recordLowerSeedTailChunk075State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix075 := by
    have boundary : recordLowerSeedTailChunk075Before =
        recordLowerSeedTailChunk074State := by rfl
    exact recordLowerSeedTailChunk075Step.certifies
      (boundary.trans h074)
  have h076 : recordLowerSeedTailChunk076State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix076 := by
    have boundary : recordLowerSeedTailChunk076Before =
        recordLowerSeedTailChunk075State := by rfl
    exact recordLowerSeedTailChunk076Step.certifies
      (boundary.trans h075)
  have h077 : recordLowerSeedTailChunk077State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix077 := by
    have boundary : recordLowerSeedTailChunk077Before =
        recordLowerSeedTailChunk076State := by rfl
    exact recordLowerSeedTailChunk077Step.certifies
      (boundary.trans h076)
  have h078 : recordLowerSeedTailChunk078State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix078 := by
    have boundary : recordLowerSeedTailChunk078Before =
        recordLowerSeedTailChunk077State := by rfl
    exact recordLowerSeedTailChunk078Step.certifies
      (boundary.trans h077)
  have h079 : recordLowerSeedTailChunk079State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix079 := by
    have boundary : recordLowerSeedTailChunk079Before =
        recordLowerSeedTailChunk078State := by rfl
    exact recordLowerSeedTailChunk079Step.certifies
      (boundary.trans h078)
  have h080 : recordLowerSeedTailChunk080State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix080 := by
    have boundary : recordLowerSeedTailChunk080Before =
        recordLowerSeedTailChunk079State := by rfl
    exact recordLowerSeedTailChunk080Step.certifies
      (boundary.trans h079)
  exact h080

end PrimeFactorUnimodality
