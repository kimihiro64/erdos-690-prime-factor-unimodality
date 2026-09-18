import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Assembly.Part06
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part241
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part242
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part243
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part244
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part245
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part246
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part247
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part248
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part249
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part250
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part251
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part252
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part253
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part254
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part255
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part256
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part257
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part258
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part259
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part260
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part261
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part262
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part263
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part264
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part265
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part266
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part267
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part268
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part269
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part270
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part271
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part272
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part273
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part274
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part275
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part276
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part277
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part278
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part279
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part280

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-upper-seed-base11.json` (semantic SHA-256 `493791f7b41de1500c4b830f254f9f92fd9c5d50d639b62aa2b46ca48591321f`, excluding elapsed time). Semantic tail assembly group 7. -/

namespace PrimeFactorUnimodality

theorem recordUpperSeedTailGroup07_semantic :
    recordUpperSeedTailChunk280State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix280 := by
  have h241 : recordUpperSeedTailChunk241State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix241 := by
    have prior : recordUpperSeedTailChunk241Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix240 := by
      simpa only [
        recordUpperSeedTailChunk241Before,
        recordUpperSeedTailChunk240State] using recordUpperSeedTailGroup06_semantic
    simpa only [recordUpperSeedTailPrefix241] using
      recordUpperSeedTailChunk241Step.certifies prior
  have h242 : recordUpperSeedTailChunk242State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix242 := by
    have prior : recordUpperSeedTailChunk242Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix241 := by
      simpa only [
        recordUpperSeedTailChunk242Before,
        recordUpperSeedTailChunk241State] using h241
    simpa only [recordUpperSeedTailPrefix242] using
      recordUpperSeedTailChunk242Step.certifies prior
  have h243 : recordUpperSeedTailChunk243State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix243 := by
    have prior : recordUpperSeedTailChunk243Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix242 := by
      simpa only [
        recordUpperSeedTailChunk243Before,
        recordUpperSeedTailChunk242State] using h242
    simpa only [recordUpperSeedTailPrefix243] using
      recordUpperSeedTailChunk243Step.certifies prior
  have h244 : recordUpperSeedTailChunk244State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix244 := by
    have prior : recordUpperSeedTailChunk244Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix243 := by
      simpa only [
        recordUpperSeedTailChunk244Before,
        recordUpperSeedTailChunk243State] using h243
    simpa only [recordUpperSeedTailPrefix244] using
      recordUpperSeedTailChunk244Step.certifies prior
  have h245 : recordUpperSeedTailChunk245State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix245 := by
    have prior : recordUpperSeedTailChunk245Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix244 := by
      simpa only [
        recordUpperSeedTailChunk245Before,
        recordUpperSeedTailChunk244State] using h244
    simpa only [recordUpperSeedTailPrefix245] using
      recordUpperSeedTailChunk245Step.certifies prior
  have h246 : recordUpperSeedTailChunk246State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix246 := by
    have prior : recordUpperSeedTailChunk246Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix245 := by
      simpa only [
        recordUpperSeedTailChunk246Before,
        recordUpperSeedTailChunk245State] using h245
    simpa only [recordUpperSeedTailPrefix246] using
      recordUpperSeedTailChunk246Step.certifies prior
  have h247 : recordUpperSeedTailChunk247State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix247 := by
    have prior : recordUpperSeedTailChunk247Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix246 := by
      simpa only [
        recordUpperSeedTailChunk247Before,
        recordUpperSeedTailChunk246State] using h246
    simpa only [recordUpperSeedTailPrefix247] using
      recordUpperSeedTailChunk247Step.certifies prior
  have h248 : recordUpperSeedTailChunk248State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix248 := by
    have prior : recordUpperSeedTailChunk248Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix247 := by
      simpa only [
        recordUpperSeedTailChunk248Before,
        recordUpperSeedTailChunk247State] using h247
    simpa only [recordUpperSeedTailPrefix248] using
      recordUpperSeedTailChunk248Step.certifies prior
  have h249 : recordUpperSeedTailChunk249State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix249 := by
    have prior : recordUpperSeedTailChunk249Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix248 := by
      simpa only [
        recordUpperSeedTailChunk249Before,
        recordUpperSeedTailChunk248State] using h248
    simpa only [recordUpperSeedTailPrefix249] using
      recordUpperSeedTailChunk249Step.certifies prior
  have h250 : recordUpperSeedTailChunk250State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix250 := by
    have prior : recordUpperSeedTailChunk250Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix249 := by
      simpa only [
        recordUpperSeedTailChunk250Before,
        recordUpperSeedTailChunk249State] using h249
    simpa only [recordUpperSeedTailPrefix250] using
      recordUpperSeedTailChunk250Step.certifies prior
  have h251 : recordUpperSeedTailChunk251State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix251 := by
    have prior : recordUpperSeedTailChunk251Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix250 := by
      simpa only [
        recordUpperSeedTailChunk251Before,
        recordUpperSeedTailChunk250State] using h250
    simpa only [recordUpperSeedTailPrefix251] using
      recordUpperSeedTailChunk251Step.certifies prior
  have h252 : recordUpperSeedTailChunk252State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix252 := by
    have prior : recordUpperSeedTailChunk252Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix251 := by
      simpa only [
        recordUpperSeedTailChunk252Before,
        recordUpperSeedTailChunk251State] using h251
    simpa only [recordUpperSeedTailPrefix252] using
      recordUpperSeedTailChunk252Step.certifies prior
  have h253 : recordUpperSeedTailChunk253State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix253 := by
    have prior : recordUpperSeedTailChunk253Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix252 := by
      simpa only [
        recordUpperSeedTailChunk253Before,
        recordUpperSeedTailChunk252State] using h252
    simpa only [recordUpperSeedTailPrefix253] using
      recordUpperSeedTailChunk253Step.certifies prior
  have h254 : recordUpperSeedTailChunk254State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix254 := by
    have prior : recordUpperSeedTailChunk254Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix253 := by
      simpa only [
        recordUpperSeedTailChunk254Before,
        recordUpperSeedTailChunk253State] using h253
    simpa only [recordUpperSeedTailPrefix254] using
      recordUpperSeedTailChunk254Step.certifies prior
  have h255 : recordUpperSeedTailChunk255State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix255 := by
    have prior : recordUpperSeedTailChunk255Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix254 := by
      simpa only [
        recordUpperSeedTailChunk255Before,
        recordUpperSeedTailChunk254State] using h254
    simpa only [recordUpperSeedTailPrefix255] using
      recordUpperSeedTailChunk255Step.certifies prior
  have h256 : recordUpperSeedTailChunk256State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix256 := by
    have prior : recordUpperSeedTailChunk256Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix255 := by
      simpa only [
        recordUpperSeedTailChunk256Before,
        recordUpperSeedTailChunk255State] using h255
    simpa only [recordUpperSeedTailPrefix256] using
      recordUpperSeedTailChunk256Step.certifies prior
  have h257 : recordUpperSeedTailChunk257State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix257 := by
    have prior : recordUpperSeedTailChunk257Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix256 := by
      simpa only [
        recordUpperSeedTailChunk257Before,
        recordUpperSeedTailChunk256State] using h256
    simpa only [recordUpperSeedTailPrefix257] using
      recordUpperSeedTailChunk257Step.certifies prior
  have h258 : recordUpperSeedTailChunk258State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix258 := by
    have prior : recordUpperSeedTailChunk258Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix257 := by
      simpa only [
        recordUpperSeedTailChunk258Before,
        recordUpperSeedTailChunk257State] using h257
    simpa only [recordUpperSeedTailPrefix258] using
      recordUpperSeedTailChunk258Step.certifies prior
  have h259 : recordUpperSeedTailChunk259State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix259 := by
    have prior : recordUpperSeedTailChunk259Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix258 := by
      simpa only [
        recordUpperSeedTailChunk259Before,
        recordUpperSeedTailChunk258State] using h258
    simpa only [recordUpperSeedTailPrefix259] using
      recordUpperSeedTailChunk259Step.certifies prior
  have h260 : recordUpperSeedTailChunk260State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix260 := by
    have prior : recordUpperSeedTailChunk260Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix259 := by
      simpa only [
        recordUpperSeedTailChunk260Before,
        recordUpperSeedTailChunk259State] using h259
    simpa only [recordUpperSeedTailPrefix260] using
      recordUpperSeedTailChunk260Step.certifies prior
  have h261 : recordUpperSeedTailChunk261State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix261 := by
    have prior : recordUpperSeedTailChunk261Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix260 := by
      simpa only [
        recordUpperSeedTailChunk261Before,
        recordUpperSeedTailChunk260State] using h260
    simpa only [recordUpperSeedTailPrefix261] using
      recordUpperSeedTailChunk261Step.certifies prior
  have h262 : recordUpperSeedTailChunk262State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix262 := by
    have prior : recordUpperSeedTailChunk262Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix261 := by
      simpa only [
        recordUpperSeedTailChunk262Before,
        recordUpperSeedTailChunk261State] using h261
    simpa only [recordUpperSeedTailPrefix262] using
      recordUpperSeedTailChunk262Step.certifies prior
  have h263 : recordUpperSeedTailChunk263State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix263 := by
    have prior : recordUpperSeedTailChunk263Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix262 := by
      simpa only [
        recordUpperSeedTailChunk263Before,
        recordUpperSeedTailChunk262State] using h262
    simpa only [recordUpperSeedTailPrefix263] using
      recordUpperSeedTailChunk263Step.certifies prior
  have h264 : recordUpperSeedTailChunk264State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix264 := by
    have prior : recordUpperSeedTailChunk264Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix263 := by
      simpa only [
        recordUpperSeedTailChunk264Before,
        recordUpperSeedTailChunk263State] using h263
    simpa only [recordUpperSeedTailPrefix264] using
      recordUpperSeedTailChunk264Step.certifies prior
  have h265 : recordUpperSeedTailChunk265State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix265 := by
    have prior : recordUpperSeedTailChunk265Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix264 := by
      simpa only [
        recordUpperSeedTailChunk265Before,
        recordUpperSeedTailChunk264State] using h264
    simpa only [recordUpperSeedTailPrefix265] using
      recordUpperSeedTailChunk265Step.certifies prior
  have h266 : recordUpperSeedTailChunk266State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix266 := by
    have prior : recordUpperSeedTailChunk266Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix265 := by
      simpa only [
        recordUpperSeedTailChunk266Before,
        recordUpperSeedTailChunk265State] using h265
    simpa only [recordUpperSeedTailPrefix266] using
      recordUpperSeedTailChunk266Step.certifies prior
  have h267 : recordUpperSeedTailChunk267State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix267 := by
    have prior : recordUpperSeedTailChunk267Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix266 := by
      simpa only [
        recordUpperSeedTailChunk267Before,
        recordUpperSeedTailChunk266State] using h266
    simpa only [recordUpperSeedTailPrefix267] using
      recordUpperSeedTailChunk267Step.certifies prior
  have h268 : recordUpperSeedTailChunk268State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix268 := by
    have prior : recordUpperSeedTailChunk268Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix267 := by
      simpa only [
        recordUpperSeedTailChunk268Before,
        recordUpperSeedTailChunk267State] using h267
    simpa only [recordUpperSeedTailPrefix268] using
      recordUpperSeedTailChunk268Step.certifies prior
  have h269 : recordUpperSeedTailChunk269State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix269 := by
    have prior : recordUpperSeedTailChunk269Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix268 := by
      simpa only [
        recordUpperSeedTailChunk269Before,
        recordUpperSeedTailChunk268State] using h268
    simpa only [recordUpperSeedTailPrefix269] using
      recordUpperSeedTailChunk269Step.certifies prior
  have h270 : recordUpperSeedTailChunk270State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix270 := by
    have prior : recordUpperSeedTailChunk270Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix269 := by
      simpa only [
        recordUpperSeedTailChunk270Before,
        recordUpperSeedTailChunk269State] using h269
    simpa only [recordUpperSeedTailPrefix270] using
      recordUpperSeedTailChunk270Step.certifies prior
  have h271 : recordUpperSeedTailChunk271State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix271 := by
    have prior : recordUpperSeedTailChunk271Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix270 := by
      simpa only [
        recordUpperSeedTailChunk271Before,
        recordUpperSeedTailChunk270State] using h270
    simpa only [recordUpperSeedTailPrefix271] using
      recordUpperSeedTailChunk271Step.certifies prior
  have h272 : recordUpperSeedTailChunk272State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix272 := by
    have prior : recordUpperSeedTailChunk272Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix271 := by
      simpa only [
        recordUpperSeedTailChunk272Before,
        recordUpperSeedTailChunk271State] using h271
    simpa only [recordUpperSeedTailPrefix272] using
      recordUpperSeedTailChunk272Step.certifies prior
  have h273 : recordUpperSeedTailChunk273State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix273 := by
    have prior : recordUpperSeedTailChunk273Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix272 := by
      simpa only [
        recordUpperSeedTailChunk273Before,
        recordUpperSeedTailChunk272State] using h272
    simpa only [recordUpperSeedTailPrefix273] using
      recordUpperSeedTailChunk273Step.certifies prior
  have h274 : recordUpperSeedTailChunk274State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix274 := by
    have prior : recordUpperSeedTailChunk274Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix273 := by
      simpa only [
        recordUpperSeedTailChunk274Before,
        recordUpperSeedTailChunk273State] using h273
    simpa only [recordUpperSeedTailPrefix274] using
      recordUpperSeedTailChunk274Step.certifies prior
  have h275 : recordUpperSeedTailChunk275State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix275 := by
    have prior : recordUpperSeedTailChunk275Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix274 := by
      simpa only [
        recordUpperSeedTailChunk275Before,
        recordUpperSeedTailChunk274State] using h274
    simpa only [recordUpperSeedTailPrefix275] using
      recordUpperSeedTailChunk275Step.certifies prior
  have h276 : recordUpperSeedTailChunk276State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix276 := by
    have prior : recordUpperSeedTailChunk276Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix275 := by
      simpa only [
        recordUpperSeedTailChunk276Before,
        recordUpperSeedTailChunk275State] using h275
    simpa only [recordUpperSeedTailPrefix276] using
      recordUpperSeedTailChunk276Step.certifies prior
  have h277 : recordUpperSeedTailChunk277State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix277 := by
    have prior : recordUpperSeedTailChunk277Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix276 := by
      simpa only [
        recordUpperSeedTailChunk277Before,
        recordUpperSeedTailChunk276State] using h276
    simpa only [recordUpperSeedTailPrefix277] using
      recordUpperSeedTailChunk277Step.certifies prior
  have h278 : recordUpperSeedTailChunk278State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix278 := by
    have prior : recordUpperSeedTailChunk278Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix277 := by
      simpa only [
        recordUpperSeedTailChunk278Before,
        recordUpperSeedTailChunk277State] using h277
    simpa only [recordUpperSeedTailPrefix278] using
      recordUpperSeedTailChunk278Step.certifies prior
  have h279 : recordUpperSeedTailChunk279State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix279 := by
    have prior : recordUpperSeedTailChunk279Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix278 := by
      simpa only [
        recordUpperSeedTailChunk279Before,
        recordUpperSeedTailChunk278State] using h278
    simpa only [recordUpperSeedTailPrefix279] using
      recordUpperSeedTailChunk279Step.certifies prior
  have h280 : recordUpperSeedTailChunk280State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix280 := by
    have prior : recordUpperSeedTailChunk280Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix279 := by
      simpa only [
        recordUpperSeedTailChunk280Before,
        recordUpperSeedTailChunk279State] using h279
    simpa only [recordUpperSeedTailPrefix280] using
      recordUpperSeedTailChunk280Step.certifies prior
  exact h280

end PrimeFactorUnimodality
