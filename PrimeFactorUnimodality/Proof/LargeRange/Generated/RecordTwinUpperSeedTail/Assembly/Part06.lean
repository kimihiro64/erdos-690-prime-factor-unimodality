import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Assembly.Part05
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part240

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-upper-seed-base11.json` (semantic SHA-256 `493791f7b41de1500c4b830f254f9f92fd9c5d50d639b62aa2b46ca48591321f`, excluding elapsed time). Semantic tail assembly group 6. -/

namespace PrimeFactorUnimodality

theorem recordUpperSeedTailGroup06_semantic :
    recordUpperSeedTailChunk240State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix240 := by
  have h201 : recordUpperSeedTailChunk201State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix201 := by
    have prior : recordUpperSeedTailChunk201Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix200 := by
      simpa only [
        recordUpperSeedTailChunk201Before,
        recordUpperSeedTailChunk200State] using recordUpperSeedTailGroup05_semantic
    simpa only [recordUpperSeedTailPrefix201] using
      recordUpperSeedTailChunk201Step.certifies prior
  have h202 : recordUpperSeedTailChunk202State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix202 := by
    have prior : recordUpperSeedTailChunk202Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix201 := by
      simpa only [
        recordUpperSeedTailChunk202Before,
        recordUpperSeedTailChunk201State] using h201
    simpa only [recordUpperSeedTailPrefix202] using
      recordUpperSeedTailChunk202Step.certifies prior
  have h203 : recordUpperSeedTailChunk203State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix203 := by
    have prior : recordUpperSeedTailChunk203Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix202 := by
      simpa only [
        recordUpperSeedTailChunk203Before,
        recordUpperSeedTailChunk202State] using h202
    simpa only [recordUpperSeedTailPrefix203] using
      recordUpperSeedTailChunk203Step.certifies prior
  have h204 : recordUpperSeedTailChunk204State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix204 := by
    have prior : recordUpperSeedTailChunk204Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix203 := by
      simpa only [
        recordUpperSeedTailChunk204Before,
        recordUpperSeedTailChunk203State] using h203
    simpa only [recordUpperSeedTailPrefix204] using
      recordUpperSeedTailChunk204Step.certifies prior
  have h205 : recordUpperSeedTailChunk205State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix205 := by
    have prior : recordUpperSeedTailChunk205Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix204 := by
      simpa only [
        recordUpperSeedTailChunk205Before,
        recordUpperSeedTailChunk204State] using h204
    simpa only [recordUpperSeedTailPrefix205] using
      recordUpperSeedTailChunk205Step.certifies prior
  have h206 : recordUpperSeedTailChunk206State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix206 := by
    have prior : recordUpperSeedTailChunk206Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix205 := by
      simpa only [
        recordUpperSeedTailChunk206Before,
        recordUpperSeedTailChunk205State] using h205
    simpa only [recordUpperSeedTailPrefix206] using
      recordUpperSeedTailChunk206Step.certifies prior
  have h207 : recordUpperSeedTailChunk207State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix207 := by
    have prior : recordUpperSeedTailChunk207Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix206 := by
      simpa only [
        recordUpperSeedTailChunk207Before,
        recordUpperSeedTailChunk206State] using h206
    simpa only [recordUpperSeedTailPrefix207] using
      recordUpperSeedTailChunk207Step.certifies prior
  have h208 : recordUpperSeedTailChunk208State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix208 := by
    have prior : recordUpperSeedTailChunk208Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix207 := by
      simpa only [
        recordUpperSeedTailChunk208Before,
        recordUpperSeedTailChunk207State] using h207
    simpa only [recordUpperSeedTailPrefix208] using
      recordUpperSeedTailChunk208Step.certifies prior
  have h209 : recordUpperSeedTailChunk209State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix209 := by
    have prior : recordUpperSeedTailChunk209Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix208 := by
      simpa only [
        recordUpperSeedTailChunk209Before,
        recordUpperSeedTailChunk208State] using h208
    simpa only [recordUpperSeedTailPrefix209] using
      recordUpperSeedTailChunk209Step.certifies prior
  have h210 : recordUpperSeedTailChunk210State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix210 := by
    have prior : recordUpperSeedTailChunk210Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix209 := by
      simpa only [
        recordUpperSeedTailChunk210Before,
        recordUpperSeedTailChunk209State] using h209
    simpa only [recordUpperSeedTailPrefix210] using
      recordUpperSeedTailChunk210Step.certifies prior
  have h211 : recordUpperSeedTailChunk211State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix211 := by
    have prior : recordUpperSeedTailChunk211Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix210 := by
      simpa only [
        recordUpperSeedTailChunk211Before,
        recordUpperSeedTailChunk210State] using h210
    simpa only [recordUpperSeedTailPrefix211] using
      recordUpperSeedTailChunk211Step.certifies prior
  have h212 : recordUpperSeedTailChunk212State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix212 := by
    have prior : recordUpperSeedTailChunk212Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix211 := by
      simpa only [
        recordUpperSeedTailChunk212Before,
        recordUpperSeedTailChunk211State] using h211
    simpa only [recordUpperSeedTailPrefix212] using
      recordUpperSeedTailChunk212Step.certifies prior
  have h213 : recordUpperSeedTailChunk213State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix213 := by
    have prior : recordUpperSeedTailChunk213Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix212 := by
      simpa only [
        recordUpperSeedTailChunk213Before,
        recordUpperSeedTailChunk212State] using h212
    simpa only [recordUpperSeedTailPrefix213] using
      recordUpperSeedTailChunk213Step.certifies prior
  have h214 : recordUpperSeedTailChunk214State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix214 := by
    have prior : recordUpperSeedTailChunk214Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix213 := by
      simpa only [
        recordUpperSeedTailChunk214Before,
        recordUpperSeedTailChunk213State] using h213
    simpa only [recordUpperSeedTailPrefix214] using
      recordUpperSeedTailChunk214Step.certifies prior
  have h215 : recordUpperSeedTailChunk215State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix215 := by
    have prior : recordUpperSeedTailChunk215Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix214 := by
      simpa only [
        recordUpperSeedTailChunk215Before,
        recordUpperSeedTailChunk214State] using h214
    simpa only [recordUpperSeedTailPrefix215] using
      recordUpperSeedTailChunk215Step.certifies prior
  have h216 : recordUpperSeedTailChunk216State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix216 := by
    have prior : recordUpperSeedTailChunk216Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix215 := by
      simpa only [
        recordUpperSeedTailChunk216Before,
        recordUpperSeedTailChunk215State] using h215
    simpa only [recordUpperSeedTailPrefix216] using
      recordUpperSeedTailChunk216Step.certifies prior
  have h217 : recordUpperSeedTailChunk217State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix217 := by
    have prior : recordUpperSeedTailChunk217Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix216 := by
      simpa only [
        recordUpperSeedTailChunk217Before,
        recordUpperSeedTailChunk216State] using h216
    simpa only [recordUpperSeedTailPrefix217] using
      recordUpperSeedTailChunk217Step.certifies prior
  have h218 : recordUpperSeedTailChunk218State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix218 := by
    have prior : recordUpperSeedTailChunk218Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix217 := by
      simpa only [
        recordUpperSeedTailChunk218Before,
        recordUpperSeedTailChunk217State] using h217
    simpa only [recordUpperSeedTailPrefix218] using
      recordUpperSeedTailChunk218Step.certifies prior
  have h219 : recordUpperSeedTailChunk219State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix219 := by
    have prior : recordUpperSeedTailChunk219Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix218 := by
      simpa only [
        recordUpperSeedTailChunk219Before,
        recordUpperSeedTailChunk218State] using h218
    simpa only [recordUpperSeedTailPrefix219] using
      recordUpperSeedTailChunk219Step.certifies prior
  have h220 : recordUpperSeedTailChunk220State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix220 := by
    have prior : recordUpperSeedTailChunk220Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix219 := by
      simpa only [
        recordUpperSeedTailChunk220Before,
        recordUpperSeedTailChunk219State] using h219
    simpa only [recordUpperSeedTailPrefix220] using
      recordUpperSeedTailChunk220Step.certifies prior
  have h221 : recordUpperSeedTailChunk221State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix221 := by
    have prior : recordUpperSeedTailChunk221Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix220 := by
      simpa only [
        recordUpperSeedTailChunk221Before,
        recordUpperSeedTailChunk220State] using h220
    simpa only [recordUpperSeedTailPrefix221] using
      recordUpperSeedTailChunk221Step.certifies prior
  have h222 : recordUpperSeedTailChunk222State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix222 := by
    have prior : recordUpperSeedTailChunk222Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix221 := by
      simpa only [
        recordUpperSeedTailChunk222Before,
        recordUpperSeedTailChunk221State] using h221
    simpa only [recordUpperSeedTailPrefix222] using
      recordUpperSeedTailChunk222Step.certifies prior
  have h223 : recordUpperSeedTailChunk223State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix223 := by
    have prior : recordUpperSeedTailChunk223Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix222 := by
      simpa only [
        recordUpperSeedTailChunk223Before,
        recordUpperSeedTailChunk222State] using h222
    simpa only [recordUpperSeedTailPrefix223] using
      recordUpperSeedTailChunk223Step.certifies prior
  have h224 : recordUpperSeedTailChunk224State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix224 := by
    have prior : recordUpperSeedTailChunk224Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix223 := by
      simpa only [
        recordUpperSeedTailChunk224Before,
        recordUpperSeedTailChunk223State] using h223
    simpa only [recordUpperSeedTailPrefix224] using
      recordUpperSeedTailChunk224Step.certifies prior
  have h225 : recordUpperSeedTailChunk225State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix225 := by
    have prior : recordUpperSeedTailChunk225Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix224 := by
      simpa only [
        recordUpperSeedTailChunk225Before,
        recordUpperSeedTailChunk224State] using h224
    simpa only [recordUpperSeedTailPrefix225] using
      recordUpperSeedTailChunk225Step.certifies prior
  have h226 : recordUpperSeedTailChunk226State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix226 := by
    have prior : recordUpperSeedTailChunk226Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix225 := by
      simpa only [
        recordUpperSeedTailChunk226Before,
        recordUpperSeedTailChunk225State] using h225
    simpa only [recordUpperSeedTailPrefix226] using
      recordUpperSeedTailChunk226Step.certifies prior
  have h227 : recordUpperSeedTailChunk227State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix227 := by
    have prior : recordUpperSeedTailChunk227Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix226 := by
      simpa only [
        recordUpperSeedTailChunk227Before,
        recordUpperSeedTailChunk226State] using h226
    simpa only [recordUpperSeedTailPrefix227] using
      recordUpperSeedTailChunk227Step.certifies prior
  have h228 : recordUpperSeedTailChunk228State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix228 := by
    have prior : recordUpperSeedTailChunk228Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix227 := by
      simpa only [
        recordUpperSeedTailChunk228Before,
        recordUpperSeedTailChunk227State] using h227
    simpa only [recordUpperSeedTailPrefix228] using
      recordUpperSeedTailChunk228Step.certifies prior
  have h229 : recordUpperSeedTailChunk229State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix229 := by
    have prior : recordUpperSeedTailChunk229Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix228 := by
      simpa only [
        recordUpperSeedTailChunk229Before,
        recordUpperSeedTailChunk228State] using h228
    simpa only [recordUpperSeedTailPrefix229] using
      recordUpperSeedTailChunk229Step.certifies prior
  have h230 : recordUpperSeedTailChunk230State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix230 := by
    have prior : recordUpperSeedTailChunk230Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix229 := by
      simpa only [
        recordUpperSeedTailChunk230Before,
        recordUpperSeedTailChunk229State] using h229
    simpa only [recordUpperSeedTailPrefix230] using
      recordUpperSeedTailChunk230Step.certifies prior
  have h231 : recordUpperSeedTailChunk231State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix231 := by
    have prior : recordUpperSeedTailChunk231Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix230 := by
      simpa only [
        recordUpperSeedTailChunk231Before,
        recordUpperSeedTailChunk230State] using h230
    simpa only [recordUpperSeedTailPrefix231] using
      recordUpperSeedTailChunk231Step.certifies prior
  have h232 : recordUpperSeedTailChunk232State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix232 := by
    have prior : recordUpperSeedTailChunk232Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix231 := by
      simpa only [
        recordUpperSeedTailChunk232Before,
        recordUpperSeedTailChunk231State] using h231
    simpa only [recordUpperSeedTailPrefix232] using
      recordUpperSeedTailChunk232Step.certifies prior
  have h233 : recordUpperSeedTailChunk233State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix233 := by
    have prior : recordUpperSeedTailChunk233Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix232 := by
      simpa only [
        recordUpperSeedTailChunk233Before,
        recordUpperSeedTailChunk232State] using h232
    simpa only [recordUpperSeedTailPrefix233] using
      recordUpperSeedTailChunk233Step.certifies prior
  have h234 : recordUpperSeedTailChunk234State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix234 := by
    have prior : recordUpperSeedTailChunk234Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix233 := by
      simpa only [
        recordUpperSeedTailChunk234Before,
        recordUpperSeedTailChunk233State] using h233
    simpa only [recordUpperSeedTailPrefix234] using
      recordUpperSeedTailChunk234Step.certifies prior
  have h235 : recordUpperSeedTailChunk235State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix235 := by
    have prior : recordUpperSeedTailChunk235Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix234 := by
      simpa only [
        recordUpperSeedTailChunk235Before,
        recordUpperSeedTailChunk234State] using h234
    simpa only [recordUpperSeedTailPrefix235] using
      recordUpperSeedTailChunk235Step.certifies prior
  have h236 : recordUpperSeedTailChunk236State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix236 := by
    have prior : recordUpperSeedTailChunk236Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix235 := by
      simpa only [
        recordUpperSeedTailChunk236Before,
        recordUpperSeedTailChunk235State] using h235
    simpa only [recordUpperSeedTailPrefix236] using
      recordUpperSeedTailChunk236Step.certifies prior
  have h237 : recordUpperSeedTailChunk237State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix237 := by
    have prior : recordUpperSeedTailChunk237Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix236 := by
      simpa only [
        recordUpperSeedTailChunk237Before,
        recordUpperSeedTailChunk236State] using h236
    simpa only [recordUpperSeedTailPrefix237] using
      recordUpperSeedTailChunk237Step.certifies prior
  have h238 : recordUpperSeedTailChunk238State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix238 := by
    have prior : recordUpperSeedTailChunk238Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix237 := by
      simpa only [
        recordUpperSeedTailChunk238Before,
        recordUpperSeedTailChunk237State] using h237
    simpa only [recordUpperSeedTailPrefix238] using
      recordUpperSeedTailChunk238Step.certifies prior
  have h239 : recordUpperSeedTailChunk239State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix239 := by
    have prior : recordUpperSeedTailChunk239Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix238 := by
      simpa only [
        recordUpperSeedTailChunk239Before,
        recordUpperSeedTailChunk238State] using h238
    simpa only [recordUpperSeedTailPrefix239] using
      recordUpperSeedTailChunk239Step.certifies prior
  have h240 : recordUpperSeedTailChunk240State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix240 := by
    have prior : recordUpperSeedTailChunk240Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix239 := by
      simpa only [
        recordUpperSeedTailChunk240Before,
        recordUpperSeedTailChunk239State] using h239
    simpa only [recordUpperSeedTailPrefix240] using
      recordUpperSeedTailChunk240Step.certifies prior
  exact h240

end PrimeFactorUnimodality
