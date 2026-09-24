import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Assembly.Part06
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part280

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-lower-seed.json` (semantic SHA-256 `3ce105dad06099400dfd2e30c65d47c6e02828915452a8459553c3bb0eb78b73`, excluding elapsed time). Semantic tail assembly group 7. -/

namespace PrimeFactorUnimodality

theorem recordLowerSeedTailGroup07_semantic :
    recordLowerSeedTailChunk280State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix280 := by
  have h241 : recordLowerSeedTailChunk241State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix241 := by
    have boundary : recordLowerSeedTailChunk241Before =
        recordLowerSeedTailChunk240State := by rfl
    exact recordLowerSeedTailChunk241Step.certifies
      (boundary.trans recordLowerSeedTailGroup06_semantic)
  have h242 : recordLowerSeedTailChunk242State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix242 := by
    have boundary : recordLowerSeedTailChunk242Before =
        recordLowerSeedTailChunk241State := by rfl
    exact recordLowerSeedTailChunk242Step.certifies
      (boundary.trans h241)
  have h243 : recordLowerSeedTailChunk243State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix243 := by
    have boundary : recordLowerSeedTailChunk243Before =
        recordLowerSeedTailChunk242State := by rfl
    exact recordLowerSeedTailChunk243Step.certifies
      (boundary.trans h242)
  have h244 : recordLowerSeedTailChunk244State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix244 := by
    have boundary : recordLowerSeedTailChunk244Before =
        recordLowerSeedTailChunk243State := by rfl
    exact recordLowerSeedTailChunk244Step.certifies
      (boundary.trans h243)
  have h245 : recordLowerSeedTailChunk245State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix245 := by
    have boundary : recordLowerSeedTailChunk245Before =
        recordLowerSeedTailChunk244State := by rfl
    exact recordLowerSeedTailChunk245Step.certifies
      (boundary.trans h244)
  have h246 : recordLowerSeedTailChunk246State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix246 := by
    have boundary : recordLowerSeedTailChunk246Before =
        recordLowerSeedTailChunk245State := by rfl
    exact recordLowerSeedTailChunk246Step.certifies
      (boundary.trans h245)
  have h247 : recordLowerSeedTailChunk247State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix247 := by
    have boundary : recordLowerSeedTailChunk247Before =
        recordLowerSeedTailChunk246State := by rfl
    exact recordLowerSeedTailChunk247Step.certifies
      (boundary.trans h246)
  have h248 : recordLowerSeedTailChunk248State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix248 := by
    have boundary : recordLowerSeedTailChunk248Before =
        recordLowerSeedTailChunk247State := by rfl
    exact recordLowerSeedTailChunk248Step.certifies
      (boundary.trans h247)
  have h249 : recordLowerSeedTailChunk249State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix249 := by
    have boundary : recordLowerSeedTailChunk249Before =
        recordLowerSeedTailChunk248State := by rfl
    exact recordLowerSeedTailChunk249Step.certifies
      (boundary.trans h248)
  have h250 : recordLowerSeedTailChunk250State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix250 := by
    have boundary : recordLowerSeedTailChunk250Before =
        recordLowerSeedTailChunk249State := by rfl
    exact recordLowerSeedTailChunk250Step.certifies
      (boundary.trans h249)
  have h251 : recordLowerSeedTailChunk251State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix251 := by
    have boundary : recordLowerSeedTailChunk251Before =
        recordLowerSeedTailChunk250State := by rfl
    exact recordLowerSeedTailChunk251Step.certifies
      (boundary.trans h250)
  have h252 : recordLowerSeedTailChunk252State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix252 := by
    have boundary : recordLowerSeedTailChunk252Before =
        recordLowerSeedTailChunk251State := by rfl
    exact recordLowerSeedTailChunk252Step.certifies
      (boundary.trans h251)
  have h253 : recordLowerSeedTailChunk253State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix253 := by
    have boundary : recordLowerSeedTailChunk253Before =
        recordLowerSeedTailChunk252State := by rfl
    exact recordLowerSeedTailChunk253Step.certifies
      (boundary.trans h252)
  have h254 : recordLowerSeedTailChunk254State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix254 := by
    have boundary : recordLowerSeedTailChunk254Before =
        recordLowerSeedTailChunk253State := by rfl
    exact recordLowerSeedTailChunk254Step.certifies
      (boundary.trans h253)
  have h255 : recordLowerSeedTailChunk255State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix255 := by
    have boundary : recordLowerSeedTailChunk255Before =
        recordLowerSeedTailChunk254State := by rfl
    exact recordLowerSeedTailChunk255Step.certifies
      (boundary.trans h254)
  have h256 : recordLowerSeedTailChunk256State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix256 := by
    have boundary : recordLowerSeedTailChunk256Before =
        recordLowerSeedTailChunk255State := by rfl
    exact recordLowerSeedTailChunk256Step.certifies
      (boundary.trans h255)
  have h257 : recordLowerSeedTailChunk257State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix257 := by
    have boundary : recordLowerSeedTailChunk257Before =
        recordLowerSeedTailChunk256State := by rfl
    exact recordLowerSeedTailChunk257Step.certifies
      (boundary.trans h256)
  have h258 : recordLowerSeedTailChunk258State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix258 := by
    have boundary : recordLowerSeedTailChunk258Before =
        recordLowerSeedTailChunk257State := by rfl
    exact recordLowerSeedTailChunk258Step.certifies
      (boundary.trans h257)
  have h259 : recordLowerSeedTailChunk259State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix259 := by
    have boundary : recordLowerSeedTailChunk259Before =
        recordLowerSeedTailChunk258State := by rfl
    exact recordLowerSeedTailChunk259Step.certifies
      (boundary.trans h258)
  have h260 : recordLowerSeedTailChunk260State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix260 := by
    have boundary : recordLowerSeedTailChunk260Before =
        recordLowerSeedTailChunk259State := by rfl
    exact recordLowerSeedTailChunk260Step.certifies
      (boundary.trans h259)
  have h261 : recordLowerSeedTailChunk261State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix261 := by
    have boundary : recordLowerSeedTailChunk261Before =
        recordLowerSeedTailChunk260State := by rfl
    exact recordLowerSeedTailChunk261Step.certifies
      (boundary.trans h260)
  have h262 : recordLowerSeedTailChunk262State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix262 := by
    have boundary : recordLowerSeedTailChunk262Before =
        recordLowerSeedTailChunk261State := by rfl
    exact recordLowerSeedTailChunk262Step.certifies
      (boundary.trans h261)
  have h263 : recordLowerSeedTailChunk263State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix263 := by
    have boundary : recordLowerSeedTailChunk263Before =
        recordLowerSeedTailChunk262State := by rfl
    exact recordLowerSeedTailChunk263Step.certifies
      (boundary.trans h262)
  have h264 : recordLowerSeedTailChunk264State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix264 := by
    have boundary : recordLowerSeedTailChunk264Before =
        recordLowerSeedTailChunk263State := by rfl
    exact recordLowerSeedTailChunk264Step.certifies
      (boundary.trans h263)
  have h265 : recordLowerSeedTailChunk265State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix265 := by
    have boundary : recordLowerSeedTailChunk265Before =
        recordLowerSeedTailChunk264State := by rfl
    exact recordLowerSeedTailChunk265Step.certifies
      (boundary.trans h264)
  have h266 : recordLowerSeedTailChunk266State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix266 := by
    have boundary : recordLowerSeedTailChunk266Before =
        recordLowerSeedTailChunk265State := by rfl
    exact recordLowerSeedTailChunk266Step.certifies
      (boundary.trans h265)
  have h267 : recordLowerSeedTailChunk267State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix267 := by
    have boundary : recordLowerSeedTailChunk267Before =
        recordLowerSeedTailChunk266State := by rfl
    exact recordLowerSeedTailChunk267Step.certifies
      (boundary.trans h266)
  have h268 : recordLowerSeedTailChunk268State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix268 := by
    have boundary : recordLowerSeedTailChunk268Before =
        recordLowerSeedTailChunk267State := by rfl
    exact recordLowerSeedTailChunk268Step.certifies
      (boundary.trans h267)
  have h269 : recordLowerSeedTailChunk269State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix269 := by
    have boundary : recordLowerSeedTailChunk269Before =
        recordLowerSeedTailChunk268State := by rfl
    exact recordLowerSeedTailChunk269Step.certifies
      (boundary.trans h268)
  have h270 : recordLowerSeedTailChunk270State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix270 := by
    have boundary : recordLowerSeedTailChunk270Before =
        recordLowerSeedTailChunk269State := by rfl
    exact recordLowerSeedTailChunk270Step.certifies
      (boundary.trans h269)
  have h271 : recordLowerSeedTailChunk271State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix271 := by
    have boundary : recordLowerSeedTailChunk271Before =
        recordLowerSeedTailChunk270State := by rfl
    exact recordLowerSeedTailChunk271Step.certifies
      (boundary.trans h270)
  have h272 : recordLowerSeedTailChunk272State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix272 := by
    have boundary : recordLowerSeedTailChunk272Before =
        recordLowerSeedTailChunk271State := by rfl
    exact recordLowerSeedTailChunk272Step.certifies
      (boundary.trans h271)
  have h273 : recordLowerSeedTailChunk273State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix273 := by
    have boundary : recordLowerSeedTailChunk273Before =
        recordLowerSeedTailChunk272State := by rfl
    exact recordLowerSeedTailChunk273Step.certifies
      (boundary.trans h272)
  have h274 : recordLowerSeedTailChunk274State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix274 := by
    have boundary : recordLowerSeedTailChunk274Before =
        recordLowerSeedTailChunk273State := by rfl
    exact recordLowerSeedTailChunk274Step.certifies
      (boundary.trans h273)
  have h275 : recordLowerSeedTailChunk275State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix275 := by
    have boundary : recordLowerSeedTailChunk275Before =
        recordLowerSeedTailChunk274State := by rfl
    exact recordLowerSeedTailChunk275Step.certifies
      (boundary.trans h274)
  have h276 : recordLowerSeedTailChunk276State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix276 := by
    have boundary : recordLowerSeedTailChunk276Before =
        recordLowerSeedTailChunk275State := by rfl
    exact recordLowerSeedTailChunk276Step.certifies
      (boundary.trans h275)
  have h277 : recordLowerSeedTailChunk277State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix277 := by
    have boundary : recordLowerSeedTailChunk277Before =
        recordLowerSeedTailChunk276State := by rfl
    exact recordLowerSeedTailChunk277Step.certifies
      (boundary.trans h276)
  have h278 : recordLowerSeedTailChunk278State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix278 := by
    have boundary : recordLowerSeedTailChunk278Before =
        recordLowerSeedTailChunk277State := by rfl
    exact recordLowerSeedTailChunk278Step.certifies
      (boundary.trans h277)
  have h279 : recordLowerSeedTailChunk279State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix279 := by
    have boundary : recordLowerSeedTailChunk279Before =
        recordLowerSeedTailChunk278State := by rfl
    exact recordLowerSeedTailChunk279Step.certifies
      (boundary.trans h278)
  have h280 : recordLowerSeedTailChunk280State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix280 := by
    have boundary : recordLowerSeedTailChunk280Before =
        recordLowerSeedTailChunk279State := by rfl
    exact recordLowerSeedTailChunk280Step.certifies
      (boundary.trans h279)
  exact h280

end PrimeFactorUnimodality
