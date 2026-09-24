import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Assembly.Part05
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part240

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-upper-seed-base11.json` (semantic SHA-256 `493791f7b41de1500c4b830f254f9f92fd9c5d50d639b62aa2b46ca48591321f`, excluding elapsed time). Semantic tail assembly group 6. -/

namespace PrimeFactorUnimodality

theorem recordUpperSeedTailGroup06_semantic :
    recordUpperSeedTailChunk240State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix240 := by
  have h201 : recordUpperSeedTailChunk201State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix201 := by
    have boundary : recordUpperSeedTailChunk201Before =
        recordUpperSeedTailChunk200State := by rfl
    exact recordUpperSeedTailChunk201Step.certifies
      (boundary.trans recordUpperSeedTailGroup05_semantic)
  have h202 : recordUpperSeedTailChunk202State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix202 := by
    have boundary : recordUpperSeedTailChunk202Before =
        recordUpperSeedTailChunk201State := by rfl
    exact recordUpperSeedTailChunk202Step.certifies
      (boundary.trans h201)
  have h203 : recordUpperSeedTailChunk203State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix203 := by
    have boundary : recordUpperSeedTailChunk203Before =
        recordUpperSeedTailChunk202State := by rfl
    exact recordUpperSeedTailChunk203Step.certifies
      (boundary.trans h202)
  have h204 : recordUpperSeedTailChunk204State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix204 := by
    have boundary : recordUpperSeedTailChunk204Before =
        recordUpperSeedTailChunk203State := by rfl
    exact recordUpperSeedTailChunk204Step.certifies
      (boundary.trans h203)
  have h205 : recordUpperSeedTailChunk205State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix205 := by
    have boundary : recordUpperSeedTailChunk205Before =
        recordUpperSeedTailChunk204State := by rfl
    exact recordUpperSeedTailChunk205Step.certifies
      (boundary.trans h204)
  have h206 : recordUpperSeedTailChunk206State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix206 := by
    have boundary : recordUpperSeedTailChunk206Before =
        recordUpperSeedTailChunk205State := by rfl
    exact recordUpperSeedTailChunk206Step.certifies
      (boundary.trans h205)
  have h207 : recordUpperSeedTailChunk207State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix207 := by
    have boundary : recordUpperSeedTailChunk207Before =
        recordUpperSeedTailChunk206State := by rfl
    exact recordUpperSeedTailChunk207Step.certifies
      (boundary.trans h206)
  have h208 : recordUpperSeedTailChunk208State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix208 := by
    have boundary : recordUpperSeedTailChunk208Before =
        recordUpperSeedTailChunk207State := by rfl
    exact recordUpperSeedTailChunk208Step.certifies
      (boundary.trans h207)
  have h209 : recordUpperSeedTailChunk209State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix209 := by
    have boundary : recordUpperSeedTailChunk209Before =
        recordUpperSeedTailChunk208State := by rfl
    exact recordUpperSeedTailChunk209Step.certifies
      (boundary.trans h208)
  have h210 : recordUpperSeedTailChunk210State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix210 := by
    have boundary : recordUpperSeedTailChunk210Before =
        recordUpperSeedTailChunk209State := by rfl
    exact recordUpperSeedTailChunk210Step.certifies
      (boundary.trans h209)
  have h211 : recordUpperSeedTailChunk211State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix211 := by
    have boundary : recordUpperSeedTailChunk211Before =
        recordUpperSeedTailChunk210State := by rfl
    exact recordUpperSeedTailChunk211Step.certifies
      (boundary.trans h210)
  have h212 : recordUpperSeedTailChunk212State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix212 := by
    have boundary : recordUpperSeedTailChunk212Before =
        recordUpperSeedTailChunk211State := by rfl
    exact recordUpperSeedTailChunk212Step.certifies
      (boundary.trans h211)
  have h213 : recordUpperSeedTailChunk213State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix213 := by
    have boundary : recordUpperSeedTailChunk213Before =
        recordUpperSeedTailChunk212State := by rfl
    exact recordUpperSeedTailChunk213Step.certifies
      (boundary.trans h212)
  have h214 : recordUpperSeedTailChunk214State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix214 := by
    have boundary : recordUpperSeedTailChunk214Before =
        recordUpperSeedTailChunk213State := by rfl
    exact recordUpperSeedTailChunk214Step.certifies
      (boundary.trans h213)
  have h215 : recordUpperSeedTailChunk215State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix215 := by
    have boundary : recordUpperSeedTailChunk215Before =
        recordUpperSeedTailChunk214State := by rfl
    exact recordUpperSeedTailChunk215Step.certifies
      (boundary.trans h214)
  have h216 : recordUpperSeedTailChunk216State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix216 := by
    have boundary : recordUpperSeedTailChunk216Before =
        recordUpperSeedTailChunk215State := by rfl
    exact recordUpperSeedTailChunk216Step.certifies
      (boundary.trans h215)
  have h217 : recordUpperSeedTailChunk217State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix217 := by
    have boundary : recordUpperSeedTailChunk217Before =
        recordUpperSeedTailChunk216State := by rfl
    exact recordUpperSeedTailChunk217Step.certifies
      (boundary.trans h216)
  have h218 : recordUpperSeedTailChunk218State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix218 := by
    have boundary : recordUpperSeedTailChunk218Before =
        recordUpperSeedTailChunk217State := by rfl
    exact recordUpperSeedTailChunk218Step.certifies
      (boundary.trans h217)
  have h219 : recordUpperSeedTailChunk219State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix219 := by
    have boundary : recordUpperSeedTailChunk219Before =
        recordUpperSeedTailChunk218State := by rfl
    exact recordUpperSeedTailChunk219Step.certifies
      (boundary.trans h218)
  have h220 : recordUpperSeedTailChunk220State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix220 := by
    have boundary : recordUpperSeedTailChunk220Before =
        recordUpperSeedTailChunk219State := by rfl
    exact recordUpperSeedTailChunk220Step.certifies
      (boundary.trans h219)
  have h221 : recordUpperSeedTailChunk221State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix221 := by
    have boundary : recordUpperSeedTailChunk221Before =
        recordUpperSeedTailChunk220State := by rfl
    exact recordUpperSeedTailChunk221Step.certifies
      (boundary.trans h220)
  have h222 : recordUpperSeedTailChunk222State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix222 := by
    have boundary : recordUpperSeedTailChunk222Before =
        recordUpperSeedTailChunk221State := by rfl
    exact recordUpperSeedTailChunk222Step.certifies
      (boundary.trans h221)
  have h223 : recordUpperSeedTailChunk223State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix223 := by
    have boundary : recordUpperSeedTailChunk223Before =
        recordUpperSeedTailChunk222State := by rfl
    exact recordUpperSeedTailChunk223Step.certifies
      (boundary.trans h222)
  have h224 : recordUpperSeedTailChunk224State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix224 := by
    have boundary : recordUpperSeedTailChunk224Before =
        recordUpperSeedTailChunk223State := by rfl
    exact recordUpperSeedTailChunk224Step.certifies
      (boundary.trans h223)
  have h225 : recordUpperSeedTailChunk225State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix225 := by
    have boundary : recordUpperSeedTailChunk225Before =
        recordUpperSeedTailChunk224State := by rfl
    exact recordUpperSeedTailChunk225Step.certifies
      (boundary.trans h224)
  have h226 : recordUpperSeedTailChunk226State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix226 := by
    have boundary : recordUpperSeedTailChunk226Before =
        recordUpperSeedTailChunk225State := by rfl
    exact recordUpperSeedTailChunk226Step.certifies
      (boundary.trans h225)
  have h227 : recordUpperSeedTailChunk227State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix227 := by
    have boundary : recordUpperSeedTailChunk227Before =
        recordUpperSeedTailChunk226State := by rfl
    exact recordUpperSeedTailChunk227Step.certifies
      (boundary.trans h226)
  have h228 : recordUpperSeedTailChunk228State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix228 := by
    have boundary : recordUpperSeedTailChunk228Before =
        recordUpperSeedTailChunk227State := by rfl
    exact recordUpperSeedTailChunk228Step.certifies
      (boundary.trans h227)
  have h229 : recordUpperSeedTailChunk229State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix229 := by
    have boundary : recordUpperSeedTailChunk229Before =
        recordUpperSeedTailChunk228State := by rfl
    exact recordUpperSeedTailChunk229Step.certifies
      (boundary.trans h228)
  have h230 : recordUpperSeedTailChunk230State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix230 := by
    have boundary : recordUpperSeedTailChunk230Before =
        recordUpperSeedTailChunk229State := by rfl
    exact recordUpperSeedTailChunk230Step.certifies
      (boundary.trans h229)
  have h231 : recordUpperSeedTailChunk231State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix231 := by
    have boundary : recordUpperSeedTailChunk231Before =
        recordUpperSeedTailChunk230State := by rfl
    exact recordUpperSeedTailChunk231Step.certifies
      (boundary.trans h230)
  have h232 : recordUpperSeedTailChunk232State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix232 := by
    have boundary : recordUpperSeedTailChunk232Before =
        recordUpperSeedTailChunk231State := by rfl
    exact recordUpperSeedTailChunk232Step.certifies
      (boundary.trans h231)
  have h233 : recordUpperSeedTailChunk233State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix233 := by
    have boundary : recordUpperSeedTailChunk233Before =
        recordUpperSeedTailChunk232State := by rfl
    exact recordUpperSeedTailChunk233Step.certifies
      (boundary.trans h232)
  have h234 : recordUpperSeedTailChunk234State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix234 := by
    have boundary : recordUpperSeedTailChunk234Before =
        recordUpperSeedTailChunk233State := by rfl
    exact recordUpperSeedTailChunk234Step.certifies
      (boundary.trans h233)
  have h235 : recordUpperSeedTailChunk235State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix235 := by
    have boundary : recordUpperSeedTailChunk235Before =
        recordUpperSeedTailChunk234State := by rfl
    exact recordUpperSeedTailChunk235Step.certifies
      (boundary.trans h234)
  have h236 : recordUpperSeedTailChunk236State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix236 := by
    have boundary : recordUpperSeedTailChunk236Before =
        recordUpperSeedTailChunk235State := by rfl
    exact recordUpperSeedTailChunk236Step.certifies
      (boundary.trans h235)
  have h237 : recordUpperSeedTailChunk237State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix237 := by
    have boundary : recordUpperSeedTailChunk237Before =
        recordUpperSeedTailChunk236State := by rfl
    exact recordUpperSeedTailChunk237Step.certifies
      (boundary.trans h236)
  have h238 : recordUpperSeedTailChunk238State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix238 := by
    have boundary : recordUpperSeedTailChunk238Before =
        recordUpperSeedTailChunk237State := by rfl
    exact recordUpperSeedTailChunk238Step.certifies
      (boundary.trans h237)
  have h239 : recordUpperSeedTailChunk239State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix239 := by
    have boundary : recordUpperSeedTailChunk239Before =
        recordUpperSeedTailChunk238State := by rfl
    exact recordUpperSeedTailChunk239Step.certifies
      (boundary.trans h238)
  have h240 : recordUpperSeedTailChunk240State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix240 := by
    have boundary : recordUpperSeedTailChunk240Before =
        recordUpperSeedTailChunk239State := by rfl
    exact recordUpperSeedTailChunk240Step.certifies
      (boundary.trans h239)
  exact h240

end PrimeFactorUnimodality
