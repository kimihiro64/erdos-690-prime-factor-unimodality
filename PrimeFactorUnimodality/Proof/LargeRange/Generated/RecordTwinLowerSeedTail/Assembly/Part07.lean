import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Assembly.Part06
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part241
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part242
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part243
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part244
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part245
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part246
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part247
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part248
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part249
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part250
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part251
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part252
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part253
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part254
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part255
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part256
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part257
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part258
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part259
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part260
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part261
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part262
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part263
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part264
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part265
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part266
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part267
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part268
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part269
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part270
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part271
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part272
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part273
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part274
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part275
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part276
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part277
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part278
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part279
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part280

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-lower-seed.json` (semantic SHA-256 `3ce105dad06099400dfd2e30c65d47c6e02828915452a8459553c3bb0eb78b73`, excluding elapsed time). Semantic tail assembly group 7. -/

namespace PrimeFactorUnimodality

theorem recordLowerSeedTailGroup07_semantic :
    recordLowerSeedTailChunk280State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix280 := by
  have h241 : recordLowerSeedTailChunk241State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix241 := by
    have prior : recordLowerSeedTailChunk241Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix240 := by
      simpa only [
        recordLowerSeedTailChunk241Before,
        recordLowerSeedTailChunk240State] using recordLowerSeedTailGroup06_semantic
    simpa only [recordLowerSeedTailPrefix241] using
      recordLowerSeedTailChunk241Step.certifies prior
  have h242 : recordLowerSeedTailChunk242State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix242 := by
    have prior : recordLowerSeedTailChunk242Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix241 := by
      simpa only [
        recordLowerSeedTailChunk242Before,
        recordLowerSeedTailChunk241State] using h241
    simpa only [recordLowerSeedTailPrefix242] using
      recordLowerSeedTailChunk242Step.certifies prior
  have h243 : recordLowerSeedTailChunk243State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix243 := by
    have prior : recordLowerSeedTailChunk243Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix242 := by
      simpa only [
        recordLowerSeedTailChunk243Before,
        recordLowerSeedTailChunk242State] using h242
    simpa only [recordLowerSeedTailPrefix243] using
      recordLowerSeedTailChunk243Step.certifies prior
  have h244 : recordLowerSeedTailChunk244State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix244 := by
    have prior : recordLowerSeedTailChunk244Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix243 := by
      simpa only [
        recordLowerSeedTailChunk244Before,
        recordLowerSeedTailChunk243State] using h243
    simpa only [recordLowerSeedTailPrefix244] using
      recordLowerSeedTailChunk244Step.certifies prior
  have h245 : recordLowerSeedTailChunk245State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix245 := by
    have prior : recordLowerSeedTailChunk245Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix244 := by
      simpa only [
        recordLowerSeedTailChunk245Before,
        recordLowerSeedTailChunk244State] using h244
    simpa only [recordLowerSeedTailPrefix245] using
      recordLowerSeedTailChunk245Step.certifies prior
  have h246 : recordLowerSeedTailChunk246State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix246 := by
    have prior : recordLowerSeedTailChunk246Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix245 := by
      simpa only [
        recordLowerSeedTailChunk246Before,
        recordLowerSeedTailChunk245State] using h245
    simpa only [recordLowerSeedTailPrefix246] using
      recordLowerSeedTailChunk246Step.certifies prior
  have h247 : recordLowerSeedTailChunk247State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix247 := by
    have prior : recordLowerSeedTailChunk247Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix246 := by
      simpa only [
        recordLowerSeedTailChunk247Before,
        recordLowerSeedTailChunk246State] using h246
    simpa only [recordLowerSeedTailPrefix247] using
      recordLowerSeedTailChunk247Step.certifies prior
  have h248 : recordLowerSeedTailChunk248State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix248 := by
    have prior : recordLowerSeedTailChunk248Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix247 := by
      simpa only [
        recordLowerSeedTailChunk248Before,
        recordLowerSeedTailChunk247State] using h247
    simpa only [recordLowerSeedTailPrefix248] using
      recordLowerSeedTailChunk248Step.certifies prior
  have h249 : recordLowerSeedTailChunk249State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix249 := by
    have prior : recordLowerSeedTailChunk249Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix248 := by
      simpa only [
        recordLowerSeedTailChunk249Before,
        recordLowerSeedTailChunk248State] using h248
    simpa only [recordLowerSeedTailPrefix249] using
      recordLowerSeedTailChunk249Step.certifies prior
  have h250 : recordLowerSeedTailChunk250State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix250 := by
    have prior : recordLowerSeedTailChunk250Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix249 := by
      simpa only [
        recordLowerSeedTailChunk250Before,
        recordLowerSeedTailChunk249State] using h249
    simpa only [recordLowerSeedTailPrefix250] using
      recordLowerSeedTailChunk250Step.certifies prior
  have h251 : recordLowerSeedTailChunk251State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix251 := by
    have prior : recordLowerSeedTailChunk251Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix250 := by
      simpa only [
        recordLowerSeedTailChunk251Before,
        recordLowerSeedTailChunk250State] using h250
    simpa only [recordLowerSeedTailPrefix251] using
      recordLowerSeedTailChunk251Step.certifies prior
  have h252 : recordLowerSeedTailChunk252State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix252 := by
    have prior : recordLowerSeedTailChunk252Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix251 := by
      simpa only [
        recordLowerSeedTailChunk252Before,
        recordLowerSeedTailChunk251State] using h251
    simpa only [recordLowerSeedTailPrefix252] using
      recordLowerSeedTailChunk252Step.certifies prior
  have h253 : recordLowerSeedTailChunk253State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix253 := by
    have prior : recordLowerSeedTailChunk253Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix252 := by
      simpa only [
        recordLowerSeedTailChunk253Before,
        recordLowerSeedTailChunk252State] using h252
    simpa only [recordLowerSeedTailPrefix253] using
      recordLowerSeedTailChunk253Step.certifies prior
  have h254 : recordLowerSeedTailChunk254State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix254 := by
    have prior : recordLowerSeedTailChunk254Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix253 := by
      simpa only [
        recordLowerSeedTailChunk254Before,
        recordLowerSeedTailChunk253State] using h253
    simpa only [recordLowerSeedTailPrefix254] using
      recordLowerSeedTailChunk254Step.certifies prior
  have h255 : recordLowerSeedTailChunk255State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix255 := by
    have prior : recordLowerSeedTailChunk255Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix254 := by
      simpa only [
        recordLowerSeedTailChunk255Before,
        recordLowerSeedTailChunk254State] using h254
    simpa only [recordLowerSeedTailPrefix255] using
      recordLowerSeedTailChunk255Step.certifies prior
  have h256 : recordLowerSeedTailChunk256State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix256 := by
    have prior : recordLowerSeedTailChunk256Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix255 := by
      simpa only [
        recordLowerSeedTailChunk256Before,
        recordLowerSeedTailChunk255State] using h255
    simpa only [recordLowerSeedTailPrefix256] using
      recordLowerSeedTailChunk256Step.certifies prior
  have h257 : recordLowerSeedTailChunk257State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix257 := by
    have prior : recordLowerSeedTailChunk257Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix256 := by
      simpa only [
        recordLowerSeedTailChunk257Before,
        recordLowerSeedTailChunk256State] using h256
    simpa only [recordLowerSeedTailPrefix257] using
      recordLowerSeedTailChunk257Step.certifies prior
  have h258 : recordLowerSeedTailChunk258State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix258 := by
    have prior : recordLowerSeedTailChunk258Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix257 := by
      simpa only [
        recordLowerSeedTailChunk258Before,
        recordLowerSeedTailChunk257State] using h257
    simpa only [recordLowerSeedTailPrefix258] using
      recordLowerSeedTailChunk258Step.certifies prior
  have h259 : recordLowerSeedTailChunk259State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix259 := by
    have prior : recordLowerSeedTailChunk259Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix258 := by
      simpa only [
        recordLowerSeedTailChunk259Before,
        recordLowerSeedTailChunk258State] using h258
    simpa only [recordLowerSeedTailPrefix259] using
      recordLowerSeedTailChunk259Step.certifies prior
  have h260 : recordLowerSeedTailChunk260State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix260 := by
    have prior : recordLowerSeedTailChunk260Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix259 := by
      simpa only [
        recordLowerSeedTailChunk260Before,
        recordLowerSeedTailChunk259State] using h259
    simpa only [recordLowerSeedTailPrefix260] using
      recordLowerSeedTailChunk260Step.certifies prior
  have h261 : recordLowerSeedTailChunk261State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix261 := by
    have prior : recordLowerSeedTailChunk261Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix260 := by
      simpa only [
        recordLowerSeedTailChunk261Before,
        recordLowerSeedTailChunk260State] using h260
    simpa only [recordLowerSeedTailPrefix261] using
      recordLowerSeedTailChunk261Step.certifies prior
  have h262 : recordLowerSeedTailChunk262State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix262 := by
    have prior : recordLowerSeedTailChunk262Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix261 := by
      simpa only [
        recordLowerSeedTailChunk262Before,
        recordLowerSeedTailChunk261State] using h261
    simpa only [recordLowerSeedTailPrefix262] using
      recordLowerSeedTailChunk262Step.certifies prior
  have h263 : recordLowerSeedTailChunk263State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix263 := by
    have prior : recordLowerSeedTailChunk263Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix262 := by
      simpa only [
        recordLowerSeedTailChunk263Before,
        recordLowerSeedTailChunk262State] using h262
    simpa only [recordLowerSeedTailPrefix263] using
      recordLowerSeedTailChunk263Step.certifies prior
  have h264 : recordLowerSeedTailChunk264State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix264 := by
    have prior : recordLowerSeedTailChunk264Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix263 := by
      simpa only [
        recordLowerSeedTailChunk264Before,
        recordLowerSeedTailChunk263State] using h263
    simpa only [recordLowerSeedTailPrefix264] using
      recordLowerSeedTailChunk264Step.certifies prior
  have h265 : recordLowerSeedTailChunk265State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix265 := by
    have prior : recordLowerSeedTailChunk265Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix264 := by
      simpa only [
        recordLowerSeedTailChunk265Before,
        recordLowerSeedTailChunk264State] using h264
    simpa only [recordLowerSeedTailPrefix265] using
      recordLowerSeedTailChunk265Step.certifies prior
  have h266 : recordLowerSeedTailChunk266State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix266 := by
    have prior : recordLowerSeedTailChunk266Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix265 := by
      simpa only [
        recordLowerSeedTailChunk266Before,
        recordLowerSeedTailChunk265State] using h265
    simpa only [recordLowerSeedTailPrefix266] using
      recordLowerSeedTailChunk266Step.certifies prior
  have h267 : recordLowerSeedTailChunk267State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix267 := by
    have prior : recordLowerSeedTailChunk267Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix266 := by
      simpa only [
        recordLowerSeedTailChunk267Before,
        recordLowerSeedTailChunk266State] using h266
    simpa only [recordLowerSeedTailPrefix267] using
      recordLowerSeedTailChunk267Step.certifies prior
  have h268 : recordLowerSeedTailChunk268State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix268 := by
    have prior : recordLowerSeedTailChunk268Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix267 := by
      simpa only [
        recordLowerSeedTailChunk268Before,
        recordLowerSeedTailChunk267State] using h267
    simpa only [recordLowerSeedTailPrefix268] using
      recordLowerSeedTailChunk268Step.certifies prior
  have h269 : recordLowerSeedTailChunk269State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix269 := by
    have prior : recordLowerSeedTailChunk269Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix268 := by
      simpa only [
        recordLowerSeedTailChunk269Before,
        recordLowerSeedTailChunk268State] using h268
    simpa only [recordLowerSeedTailPrefix269] using
      recordLowerSeedTailChunk269Step.certifies prior
  have h270 : recordLowerSeedTailChunk270State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix270 := by
    have prior : recordLowerSeedTailChunk270Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix269 := by
      simpa only [
        recordLowerSeedTailChunk270Before,
        recordLowerSeedTailChunk269State] using h269
    simpa only [recordLowerSeedTailPrefix270] using
      recordLowerSeedTailChunk270Step.certifies prior
  have h271 : recordLowerSeedTailChunk271State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix271 := by
    have prior : recordLowerSeedTailChunk271Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix270 := by
      simpa only [
        recordLowerSeedTailChunk271Before,
        recordLowerSeedTailChunk270State] using h270
    simpa only [recordLowerSeedTailPrefix271] using
      recordLowerSeedTailChunk271Step.certifies prior
  have h272 : recordLowerSeedTailChunk272State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix272 := by
    have prior : recordLowerSeedTailChunk272Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix271 := by
      simpa only [
        recordLowerSeedTailChunk272Before,
        recordLowerSeedTailChunk271State] using h271
    simpa only [recordLowerSeedTailPrefix272] using
      recordLowerSeedTailChunk272Step.certifies prior
  have h273 : recordLowerSeedTailChunk273State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix273 := by
    have prior : recordLowerSeedTailChunk273Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix272 := by
      simpa only [
        recordLowerSeedTailChunk273Before,
        recordLowerSeedTailChunk272State] using h272
    simpa only [recordLowerSeedTailPrefix273] using
      recordLowerSeedTailChunk273Step.certifies prior
  have h274 : recordLowerSeedTailChunk274State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix274 := by
    have prior : recordLowerSeedTailChunk274Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix273 := by
      simpa only [
        recordLowerSeedTailChunk274Before,
        recordLowerSeedTailChunk273State] using h273
    simpa only [recordLowerSeedTailPrefix274] using
      recordLowerSeedTailChunk274Step.certifies prior
  have h275 : recordLowerSeedTailChunk275State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix275 := by
    have prior : recordLowerSeedTailChunk275Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix274 := by
      simpa only [
        recordLowerSeedTailChunk275Before,
        recordLowerSeedTailChunk274State] using h274
    simpa only [recordLowerSeedTailPrefix275] using
      recordLowerSeedTailChunk275Step.certifies prior
  have h276 : recordLowerSeedTailChunk276State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix276 := by
    have prior : recordLowerSeedTailChunk276Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix275 := by
      simpa only [
        recordLowerSeedTailChunk276Before,
        recordLowerSeedTailChunk275State] using h275
    simpa only [recordLowerSeedTailPrefix276] using
      recordLowerSeedTailChunk276Step.certifies prior
  have h277 : recordLowerSeedTailChunk277State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix277 := by
    have prior : recordLowerSeedTailChunk277Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix276 := by
      simpa only [
        recordLowerSeedTailChunk277Before,
        recordLowerSeedTailChunk276State] using h276
    simpa only [recordLowerSeedTailPrefix277] using
      recordLowerSeedTailChunk277Step.certifies prior
  have h278 : recordLowerSeedTailChunk278State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix278 := by
    have prior : recordLowerSeedTailChunk278Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix277 := by
      simpa only [
        recordLowerSeedTailChunk278Before,
        recordLowerSeedTailChunk277State] using h277
    simpa only [recordLowerSeedTailPrefix278] using
      recordLowerSeedTailChunk278Step.certifies prior
  have h279 : recordLowerSeedTailChunk279State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix279 := by
    have prior : recordLowerSeedTailChunk279Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix278 := by
      simpa only [
        recordLowerSeedTailChunk279Before,
        recordLowerSeedTailChunk278State] using h278
    simpa only [recordLowerSeedTailPrefix279] using
      recordLowerSeedTailChunk279Step.certifies prior
  have h280 : recordLowerSeedTailChunk280State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix280 := by
    have prior : recordLowerSeedTailChunk280Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix279 := by
      simpa only [
        recordLowerSeedTailChunk280Before,
        recordLowerSeedTailChunk279State] using h279
    simpa only [recordLowerSeedTailPrefix280] using
      recordLowerSeedTailChunk280Step.certifies prior
  exact h280

end PrimeFactorUnimodality
