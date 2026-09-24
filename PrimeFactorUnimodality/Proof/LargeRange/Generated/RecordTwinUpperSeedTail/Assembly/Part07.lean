import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Assembly.Part06
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part280

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-upper-seed-base11.json` (semantic SHA-256 `493791f7b41de1500c4b830f254f9f92fd9c5d50d639b62aa2b46ca48591321f`, excluding elapsed time). Semantic tail assembly group 7. -/

namespace PrimeFactorUnimodality

theorem recordUpperSeedTailGroup07_semantic :
    recordUpperSeedTailChunk280State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix280 := by
  have h241 : recordUpperSeedTailChunk241State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix241 := by
    have boundary : recordUpperSeedTailChunk241Before =
        recordUpperSeedTailChunk240State := by rfl
    exact recordUpperSeedTailChunk241Step.certifies
      (boundary.trans recordUpperSeedTailGroup06_semantic)
  have h242 : recordUpperSeedTailChunk242State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix242 := by
    have boundary : recordUpperSeedTailChunk242Before =
        recordUpperSeedTailChunk241State := by rfl
    exact recordUpperSeedTailChunk242Step.certifies
      (boundary.trans h241)
  have h243 : recordUpperSeedTailChunk243State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix243 := by
    have boundary : recordUpperSeedTailChunk243Before =
        recordUpperSeedTailChunk242State := by rfl
    exact recordUpperSeedTailChunk243Step.certifies
      (boundary.trans h242)
  have h244 : recordUpperSeedTailChunk244State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix244 := by
    have boundary : recordUpperSeedTailChunk244Before =
        recordUpperSeedTailChunk243State := by rfl
    exact recordUpperSeedTailChunk244Step.certifies
      (boundary.trans h243)
  have h245 : recordUpperSeedTailChunk245State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix245 := by
    have boundary : recordUpperSeedTailChunk245Before =
        recordUpperSeedTailChunk244State := by rfl
    exact recordUpperSeedTailChunk245Step.certifies
      (boundary.trans h244)
  have h246 : recordUpperSeedTailChunk246State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix246 := by
    have boundary : recordUpperSeedTailChunk246Before =
        recordUpperSeedTailChunk245State := by rfl
    exact recordUpperSeedTailChunk246Step.certifies
      (boundary.trans h245)
  have h247 : recordUpperSeedTailChunk247State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix247 := by
    have boundary : recordUpperSeedTailChunk247Before =
        recordUpperSeedTailChunk246State := by rfl
    exact recordUpperSeedTailChunk247Step.certifies
      (boundary.trans h246)
  have h248 : recordUpperSeedTailChunk248State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix248 := by
    have boundary : recordUpperSeedTailChunk248Before =
        recordUpperSeedTailChunk247State := by rfl
    exact recordUpperSeedTailChunk248Step.certifies
      (boundary.trans h247)
  have h249 : recordUpperSeedTailChunk249State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix249 := by
    have boundary : recordUpperSeedTailChunk249Before =
        recordUpperSeedTailChunk248State := by rfl
    exact recordUpperSeedTailChunk249Step.certifies
      (boundary.trans h248)
  have h250 : recordUpperSeedTailChunk250State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix250 := by
    have boundary : recordUpperSeedTailChunk250Before =
        recordUpperSeedTailChunk249State := by rfl
    exact recordUpperSeedTailChunk250Step.certifies
      (boundary.trans h249)
  have h251 : recordUpperSeedTailChunk251State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix251 := by
    have boundary : recordUpperSeedTailChunk251Before =
        recordUpperSeedTailChunk250State := by rfl
    exact recordUpperSeedTailChunk251Step.certifies
      (boundary.trans h250)
  have h252 : recordUpperSeedTailChunk252State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix252 := by
    have boundary : recordUpperSeedTailChunk252Before =
        recordUpperSeedTailChunk251State := by rfl
    exact recordUpperSeedTailChunk252Step.certifies
      (boundary.trans h251)
  have h253 : recordUpperSeedTailChunk253State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix253 := by
    have boundary : recordUpperSeedTailChunk253Before =
        recordUpperSeedTailChunk252State := by rfl
    exact recordUpperSeedTailChunk253Step.certifies
      (boundary.trans h252)
  have h254 : recordUpperSeedTailChunk254State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix254 := by
    have boundary : recordUpperSeedTailChunk254Before =
        recordUpperSeedTailChunk253State := by rfl
    exact recordUpperSeedTailChunk254Step.certifies
      (boundary.trans h253)
  have h255 : recordUpperSeedTailChunk255State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix255 := by
    have boundary : recordUpperSeedTailChunk255Before =
        recordUpperSeedTailChunk254State := by rfl
    exact recordUpperSeedTailChunk255Step.certifies
      (boundary.trans h254)
  have h256 : recordUpperSeedTailChunk256State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix256 := by
    have boundary : recordUpperSeedTailChunk256Before =
        recordUpperSeedTailChunk255State := by rfl
    exact recordUpperSeedTailChunk256Step.certifies
      (boundary.trans h255)
  have h257 : recordUpperSeedTailChunk257State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix257 := by
    have boundary : recordUpperSeedTailChunk257Before =
        recordUpperSeedTailChunk256State := by rfl
    exact recordUpperSeedTailChunk257Step.certifies
      (boundary.trans h256)
  have h258 : recordUpperSeedTailChunk258State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix258 := by
    have boundary : recordUpperSeedTailChunk258Before =
        recordUpperSeedTailChunk257State := by rfl
    exact recordUpperSeedTailChunk258Step.certifies
      (boundary.trans h257)
  have h259 : recordUpperSeedTailChunk259State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix259 := by
    have boundary : recordUpperSeedTailChunk259Before =
        recordUpperSeedTailChunk258State := by rfl
    exact recordUpperSeedTailChunk259Step.certifies
      (boundary.trans h258)
  have h260 : recordUpperSeedTailChunk260State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix260 := by
    have boundary : recordUpperSeedTailChunk260Before =
        recordUpperSeedTailChunk259State := by rfl
    exact recordUpperSeedTailChunk260Step.certifies
      (boundary.trans h259)
  have h261 : recordUpperSeedTailChunk261State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix261 := by
    have boundary : recordUpperSeedTailChunk261Before =
        recordUpperSeedTailChunk260State := by rfl
    exact recordUpperSeedTailChunk261Step.certifies
      (boundary.trans h260)
  have h262 : recordUpperSeedTailChunk262State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix262 := by
    have boundary : recordUpperSeedTailChunk262Before =
        recordUpperSeedTailChunk261State := by rfl
    exact recordUpperSeedTailChunk262Step.certifies
      (boundary.trans h261)
  have h263 : recordUpperSeedTailChunk263State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix263 := by
    have boundary : recordUpperSeedTailChunk263Before =
        recordUpperSeedTailChunk262State := by rfl
    exact recordUpperSeedTailChunk263Step.certifies
      (boundary.trans h262)
  have h264 : recordUpperSeedTailChunk264State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix264 := by
    have boundary : recordUpperSeedTailChunk264Before =
        recordUpperSeedTailChunk263State := by rfl
    exact recordUpperSeedTailChunk264Step.certifies
      (boundary.trans h263)
  have h265 : recordUpperSeedTailChunk265State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix265 := by
    have boundary : recordUpperSeedTailChunk265Before =
        recordUpperSeedTailChunk264State := by rfl
    exact recordUpperSeedTailChunk265Step.certifies
      (boundary.trans h264)
  have h266 : recordUpperSeedTailChunk266State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix266 := by
    have boundary : recordUpperSeedTailChunk266Before =
        recordUpperSeedTailChunk265State := by rfl
    exact recordUpperSeedTailChunk266Step.certifies
      (boundary.trans h265)
  have h267 : recordUpperSeedTailChunk267State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix267 := by
    have boundary : recordUpperSeedTailChunk267Before =
        recordUpperSeedTailChunk266State := by rfl
    exact recordUpperSeedTailChunk267Step.certifies
      (boundary.trans h266)
  have h268 : recordUpperSeedTailChunk268State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix268 := by
    have boundary : recordUpperSeedTailChunk268Before =
        recordUpperSeedTailChunk267State := by rfl
    exact recordUpperSeedTailChunk268Step.certifies
      (boundary.trans h267)
  have h269 : recordUpperSeedTailChunk269State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix269 := by
    have boundary : recordUpperSeedTailChunk269Before =
        recordUpperSeedTailChunk268State := by rfl
    exact recordUpperSeedTailChunk269Step.certifies
      (boundary.trans h268)
  have h270 : recordUpperSeedTailChunk270State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix270 := by
    have boundary : recordUpperSeedTailChunk270Before =
        recordUpperSeedTailChunk269State := by rfl
    exact recordUpperSeedTailChunk270Step.certifies
      (boundary.trans h269)
  have h271 : recordUpperSeedTailChunk271State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix271 := by
    have boundary : recordUpperSeedTailChunk271Before =
        recordUpperSeedTailChunk270State := by rfl
    exact recordUpperSeedTailChunk271Step.certifies
      (boundary.trans h270)
  have h272 : recordUpperSeedTailChunk272State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix272 := by
    have boundary : recordUpperSeedTailChunk272Before =
        recordUpperSeedTailChunk271State := by rfl
    exact recordUpperSeedTailChunk272Step.certifies
      (boundary.trans h271)
  have h273 : recordUpperSeedTailChunk273State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix273 := by
    have boundary : recordUpperSeedTailChunk273Before =
        recordUpperSeedTailChunk272State := by rfl
    exact recordUpperSeedTailChunk273Step.certifies
      (boundary.trans h272)
  have h274 : recordUpperSeedTailChunk274State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix274 := by
    have boundary : recordUpperSeedTailChunk274Before =
        recordUpperSeedTailChunk273State := by rfl
    exact recordUpperSeedTailChunk274Step.certifies
      (boundary.trans h273)
  have h275 : recordUpperSeedTailChunk275State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix275 := by
    have boundary : recordUpperSeedTailChunk275Before =
        recordUpperSeedTailChunk274State := by rfl
    exact recordUpperSeedTailChunk275Step.certifies
      (boundary.trans h274)
  have h276 : recordUpperSeedTailChunk276State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix276 := by
    have boundary : recordUpperSeedTailChunk276Before =
        recordUpperSeedTailChunk275State := by rfl
    exact recordUpperSeedTailChunk276Step.certifies
      (boundary.trans h275)
  have h277 : recordUpperSeedTailChunk277State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix277 := by
    have boundary : recordUpperSeedTailChunk277Before =
        recordUpperSeedTailChunk276State := by rfl
    exact recordUpperSeedTailChunk277Step.certifies
      (boundary.trans h276)
  have h278 : recordUpperSeedTailChunk278State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix278 := by
    have boundary : recordUpperSeedTailChunk278Before =
        recordUpperSeedTailChunk277State := by rfl
    exact recordUpperSeedTailChunk278Step.certifies
      (boundary.trans h277)
  have h279 : recordUpperSeedTailChunk279State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix279 := by
    have boundary : recordUpperSeedTailChunk279Before =
        recordUpperSeedTailChunk278State := by rfl
    exact recordUpperSeedTailChunk279Step.certifies
      (boundary.trans h278)
  have h280 : recordUpperSeedTailChunk280State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix280 := by
    have boundary : recordUpperSeedTailChunk280Before =
        recordUpperSeedTailChunk279State := by rfl
    exact recordUpperSeedTailChunk280Step.certifies
      (boundary.trans h279)
  exact h280

end PrimeFactorUnimodality
