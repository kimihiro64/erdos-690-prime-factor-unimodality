import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Assembly.Part05
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part240

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-lower-seed.json` (semantic SHA-256 `3ce105dad06099400dfd2e30c65d47c6e02828915452a8459553c3bb0eb78b73`, excluding elapsed time). Semantic tail assembly group 6. -/

namespace PrimeFactorUnimodality

theorem recordLowerSeedTailGroup06_semantic :
    recordLowerSeedTailChunk240State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix240 := by
  have h201 : recordLowerSeedTailChunk201State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix201 := by
    have prior : recordLowerSeedTailChunk201Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix200 := by
      simpa only [
        recordLowerSeedTailChunk201Before,
        recordLowerSeedTailChunk200State] using recordLowerSeedTailGroup05_semantic
    simpa only [recordLowerSeedTailPrefix201] using
      recordLowerSeedTailChunk201Step.certifies prior
  have h202 : recordLowerSeedTailChunk202State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix202 := by
    have prior : recordLowerSeedTailChunk202Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix201 := by
      simpa only [
        recordLowerSeedTailChunk202Before,
        recordLowerSeedTailChunk201State] using h201
    simpa only [recordLowerSeedTailPrefix202] using
      recordLowerSeedTailChunk202Step.certifies prior
  have h203 : recordLowerSeedTailChunk203State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix203 := by
    have prior : recordLowerSeedTailChunk203Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix202 := by
      simpa only [
        recordLowerSeedTailChunk203Before,
        recordLowerSeedTailChunk202State] using h202
    simpa only [recordLowerSeedTailPrefix203] using
      recordLowerSeedTailChunk203Step.certifies prior
  have h204 : recordLowerSeedTailChunk204State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix204 := by
    have prior : recordLowerSeedTailChunk204Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix203 := by
      simpa only [
        recordLowerSeedTailChunk204Before,
        recordLowerSeedTailChunk203State] using h203
    simpa only [recordLowerSeedTailPrefix204] using
      recordLowerSeedTailChunk204Step.certifies prior
  have h205 : recordLowerSeedTailChunk205State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix205 := by
    have prior : recordLowerSeedTailChunk205Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix204 := by
      simpa only [
        recordLowerSeedTailChunk205Before,
        recordLowerSeedTailChunk204State] using h204
    simpa only [recordLowerSeedTailPrefix205] using
      recordLowerSeedTailChunk205Step.certifies prior
  have h206 : recordLowerSeedTailChunk206State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix206 := by
    have prior : recordLowerSeedTailChunk206Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix205 := by
      simpa only [
        recordLowerSeedTailChunk206Before,
        recordLowerSeedTailChunk205State] using h205
    simpa only [recordLowerSeedTailPrefix206] using
      recordLowerSeedTailChunk206Step.certifies prior
  have h207 : recordLowerSeedTailChunk207State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix207 := by
    have prior : recordLowerSeedTailChunk207Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix206 := by
      simpa only [
        recordLowerSeedTailChunk207Before,
        recordLowerSeedTailChunk206State] using h206
    simpa only [recordLowerSeedTailPrefix207] using
      recordLowerSeedTailChunk207Step.certifies prior
  have h208 : recordLowerSeedTailChunk208State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix208 := by
    have prior : recordLowerSeedTailChunk208Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix207 := by
      simpa only [
        recordLowerSeedTailChunk208Before,
        recordLowerSeedTailChunk207State] using h207
    simpa only [recordLowerSeedTailPrefix208] using
      recordLowerSeedTailChunk208Step.certifies prior
  have h209 : recordLowerSeedTailChunk209State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix209 := by
    have prior : recordLowerSeedTailChunk209Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix208 := by
      simpa only [
        recordLowerSeedTailChunk209Before,
        recordLowerSeedTailChunk208State] using h208
    simpa only [recordLowerSeedTailPrefix209] using
      recordLowerSeedTailChunk209Step.certifies prior
  have h210 : recordLowerSeedTailChunk210State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix210 := by
    have prior : recordLowerSeedTailChunk210Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix209 := by
      simpa only [
        recordLowerSeedTailChunk210Before,
        recordLowerSeedTailChunk209State] using h209
    simpa only [recordLowerSeedTailPrefix210] using
      recordLowerSeedTailChunk210Step.certifies prior
  have h211 : recordLowerSeedTailChunk211State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix211 := by
    have prior : recordLowerSeedTailChunk211Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix210 := by
      simpa only [
        recordLowerSeedTailChunk211Before,
        recordLowerSeedTailChunk210State] using h210
    simpa only [recordLowerSeedTailPrefix211] using
      recordLowerSeedTailChunk211Step.certifies prior
  have h212 : recordLowerSeedTailChunk212State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix212 := by
    have prior : recordLowerSeedTailChunk212Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix211 := by
      simpa only [
        recordLowerSeedTailChunk212Before,
        recordLowerSeedTailChunk211State] using h211
    simpa only [recordLowerSeedTailPrefix212] using
      recordLowerSeedTailChunk212Step.certifies prior
  have h213 : recordLowerSeedTailChunk213State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix213 := by
    have prior : recordLowerSeedTailChunk213Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix212 := by
      simpa only [
        recordLowerSeedTailChunk213Before,
        recordLowerSeedTailChunk212State] using h212
    simpa only [recordLowerSeedTailPrefix213] using
      recordLowerSeedTailChunk213Step.certifies prior
  have h214 : recordLowerSeedTailChunk214State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix214 := by
    have prior : recordLowerSeedTailChunk214Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix213 := by
      simpa only [
        recordLowerSeedTailChunk214Before,
        recordLowerSeedTailChunk213State] using h213
    simpa only [recordLowerSeedTailPrefix214] using
      recordLowerSeedTailChunk214Step.certifies prior
  have h215 : recordLowerSeedTailChunk215State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix215 := by
    have prior : recordLowerSeedTailChunk215Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix214 := by
      simpa only [
        recordLowerSeedTailChunk215Before,
        recordLowerSeedTailChunk214State] using h214
    simpa only [recordLowerSeedTailPrefix215] using
      recordLowerSeedTailChunk215Step.certifies prior
  have h216 : recordLowerSeedTailChunk216State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix216 := by
    have prior : recordLowerSeedTailChunk216Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix215 := by
      simpa only [
        recordLowerSeedTailChunk216Before,
        recordLowerSeedTailChunk215State] using h215
    simpa only [recordLowerSeedTailPrefix216] using
      recordLowerSeedTailChunk216Step.certifies prior
  have h217 : recordLowerSeedTailChunk217State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix217 := by
    have prior : recordLowerSeedTailChunk217Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix216 := by
      simpa only [
        recordLowerSeedTailChunk217Before,
        recordLowerSeedTailChunk216State] using h216
    simpa only [recordLowerSeedTailPrefix217] using
      recordLowerSeedTailChunk217Step.certifies prior
  have h218 : recordLowerSeedTailChunk218State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix218 := by
    have prior : recordLowerSeedTailChunk218Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix217 := by
      simpa only [
        recordLowerSeedTailChunk218Before,
        recordLowerSeedTailChunk217State] using h217
    simpa only [recordLowerSeedTailPrefix218] using
      recordLowerSeedTailChunk218Step.certifies prior
  have h219 : recordLowerSeedTailChunk219State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix219 := by
    have prior : recordLowerSeedTailChunk219Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix218 := by
      simpa only [
        recordLowerSeedTailChunk219Before,
        recordLowerSeedTailChunk218State] using h218
    simpa only [recordLowerSeedTailPrefix219] using
      recordLowerSeedTailChunk219Step.certifies prior
  have h220 : recordLowerSeedTailChunk220State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix220 := by
    have prior : recordLowerSeedTailChunk220Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix219 := by
      simpa only [
        recordLowerSeedTailChunk220Before,
        recordLowerSeedTailChunk219State] using h219
    simpa only [recordLowerSeedTailPrefix220] using
      recordLowerSeedTailChunk220Step.certifies prior
  have h221 : recordLowerSeedTailChunk221State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix221 := by
    have prior : recordLowerSeedTailChunk221Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix220 := by
      simpa only [
        recordLowerSeedTailChunk221Before,
        recordLowerSeedTailChunk220State] using h220
    simpa only [recordLowerSeedTailPrefix221] using
      recordLowerSeedTailChunk221Step.certifies prior
  have h222 : recordLowerSeedTailChunk222State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix222 := by
    have prior : recordLowerSeedTailChunk222Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix221 := by
      simpa only [
        recordLowerSeedTailChunk222Before,
        recordLowerSeedTailChunk221State] using h221
    simpa only [recordLowerSeedTailPrefix222] using
      recordLowerSeedTailChunk222Step.certifies prior
  have h223 : recordLowerSeedTailChunk223State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix223 := by
    have prior : recordLowerSeedTailChunk223Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix222 := by
      simpa only [
        recordLowerSeedTailChunk223Before,
        recordLowerSeedTailChunk222State] using h222
    simpa only [recordLowerSeedTailPrefix223] using
      recordLowerSeedTailChunk223Step.certifies prior
  have h224 : recordLowerSeedTailChunk224State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix224 := by
    have prior : recordLowerSeedTailChunk224Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix223 := by
      simpa only [
        recordLowerSeedTailChunk224Before,
        recordLowerSeedTailChunk223State] using h223
    simpa only [recordLowerSeedTailPrefix224] using
      recordLowerSeedTailChunk224Step.certifies prior
  have h225 : recordLowerSeedTailChunk225State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix225 := by
    have prior : recordLowerSeedTailChunk225Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix224 := by
      simpa only [
        recordLowerSeedTailChunk225Before,
        recordLowerSeedTailChunk224State] using h224
    simpa only [recordLowerSeedTailPrefix225] using
      recordLowerSeedTailChunk225Step.certifies prior
  have h226 : recordLowerSeedTailChunk226State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix226 := by
    have prior : recordLowerSeedTailChunk226Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix225 := by
      simpa only [
        recordLowerSeedTailChunk226Before,
        recordLowerSeedTailChunk225State] using h225
    simpa only [recordLowerSeedTailPrefix226] using
      recordLowerSeedTailChunk226Step.certifies prior
  have h227 : recordLowerSeedTailChunk227State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix227 := by
    have prior : recordLowerSeedTailChunk227Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix226 := by
      simpa only [
        recordLowerSeedTailChunk227Before,
        recordLowerSeedTailChunk226State] using h226
    simpa only [recordLowerSeedTailPrefix227] using
      recordLowerSeedTailChunk227Step.certifies prior
  have h228 : recordLowerSeedTailChunk228State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix228 := by
    have prior : recordLowerSeedTailChunk228Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix227 := by
      simpa only [
        recordLowerSeedTailChunk228Before,
        recordLowerSeedTailChunk227State] using h227
    simpa only [recordLowerSeedTailPrefix228] using
      recordLowerSeedTailChunk228Step.certifies prior
  have h229 : recordLowerSeedTailChunk229State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix229 := by
    have prior : recordLowerSeedTailChunk229Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix228 := by
      simpa only [
        recordLowerSeedTailChunk229Before,
        recordLowerSeedTailChunk228State] using h228
    simpa only [recordLowerSeedTailPrefix229] using
      recordLowerSeedTailChunk229Step.certifies prior
  have h230 : recordLowerSeedTailChunk230State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix230 := by
    have prior : recordLowerSeedTailChunk230Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix229 := by
      simpa only [
        recordLowerSeedTailChunk230Before,
        recordLowerSeedTailChunk229State] using h229
    simpa only [recordLowerSeedTailPrefix230] using
      recordLowerSeedTailChunk230Step.certifies prior
  have h231 : recordLowerSeedTailChunk231State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix231 := by
    have prior : recordLowerSeedTailChunk231Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix230 := by
      simpa only [
        recordLowerSeedTailChunk231Before,
        recordLowerSeedTailChunk230State] using h230
    simpa only [recordLowerSeedTailPrefix231] using
      recordLowerSeedTailChunk231Step.certifies prior
  have h232 : recordLowerSeedTailChunk232State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix232 := by
    have prior : recordLowerSeedTailChunk232Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix231 := by
      simpa only [
        recordLowerSeedTailChunk232Before,
        recordLowerSeedTailChunk231State] using h231
    simpa only [recordLowerSeedTailPrefix232] using
      recordLowerSeedTailChunk232Step.certifies prior
  have h233 : recordLowerSeedTailChunk233State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix233 := by
    have prior : recordLowerSeedTailChunk233Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix232 := by
      simpa only [
        recordLowerSeedTailChunk233Before,
        recordLowerSeedTailChunk232State] using h232
    simpa only [recordLowerSeedTailPrefix233] using
      recordLowerSeedTailChunk233Step.certifies prior
  have h234 : recordLowerSeedTailChunk234State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix234 := by
    have prior : recordLowerSeedTailChunk234Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix233 := by
      simpa only [
        recordLowerSeedTailChunk234Before,
        recordLowerSeedTailChunk233State] using h233
    simpa only [recordLowerSeedTailPrefix234] using
      recordLowerSeedTailChunk234Step.certifies prior
  have h235 : recordLowerSeedTailChunk235State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix235 := by
    have prior : recordLowerSeedTailChunk235Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix234 := by
      simpa only [
        recordLowerSeedTailChunk235Before,
        recordLowerSeedTailChunk234State] using h234
    simpa only [recordLowerSeedTailPrefix235] using
      recordLowerSeedTailChunk235Step.certifies prior
  have h236 : recordLowerSeedTailChunk236State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix236 := by
    have prior : recordLowerSeedTailChunk236Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix235 := by
      simpa only [
        recordLowerSeedTailChunk236Before,
        recordLowerSeedTailChunk235State] using h235
    simpa only [recordLowerSeedTailPrefix236] using
      recordLowerSeedTailChunk236Step.certifies prior
  have h237 : recordLowerSeedTailChunk237State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix237 := by
    have prior : recordLowerSeedTailChunk237Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix236 := by
      simpa only [
        recordLowerSeedTailChunk237Before,
        recordLowerSeedTailChunk236State] using h236
    simpa only [recordLowerSeedTailPrefix237] using
      recordLowerSeedTailChunk237Step.certifies prior
  have h238 : recordLowerSeedTailChunk238State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix238 := by
    have prior : recordLowerSeedTailChunk238Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix237 := by
      simpa only [
        recordLowerSeedTailChunk238Before,
        recordLowerSeedTailChunk237State] using h237
    simpa only [recordLowerSeedTailPrefix238] using
      recordLowerSeedTailChunk238Step.certifies prior
  have h239 : recordLowerSeedTailChunk239State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix239 := by
    have prior : recordLowerSeedTailChunk239Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix238 := by
      simpa only [
        recordLowerSeedTailChunk239Before,
        recordLowerSeedTailChunk238State] using h238
    simpa only [recordLowerSeedTailPrefix239] using
      recordLowerSeedTailChunk239Step.certifies prior
  have h240 : recordLowerSeedTailChunk240State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix240 := by
    have prior : recordLowerSeedTailChunk240Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix239 := by
      simpa only [
        recordLowerSeedTailChunk240Before,
        recordLowerSeedTailChunk239State] using h239
    simpa only [recordLowerSeedTailPrefix240] using
      recordLowerSeedTailChunk240Step.certifies prior
  exact h240

end PrimeFactorUnimodality
