import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Assembly.Part05
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part240

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-lower-seed.json` (semantic SHA-256 `3ce105dad06099400dfd2e30c65d47c6e02828915452a8459553c3bb0eb78b73`, excluding elapsed time). Semantic tail assembly group 6. -/

namespace PrimeFactorUnimodality

theorem recordLowerSeedTailGroup06_semantic :
    recordLowerSeedTailChunk240State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix240 := by
  have h201 : recordLowerSeedTailChunk201State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix201 := by
    have boundary : recordLowerSeedTailChunk201Before =
        recordLowerSeedTailChunk200State := by rfl
    exact recordLowerSeedTailChunk201Step.certifies
      (boundary.trans recordLowerSeedTailGroup05_semantic)
  have h202 : recordLowerSeedTailChunk202State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix202 := by
    have boundary : recordLowerSeedTailChunk202Before =
        recordLowerSeedTailChunk201State := by rfl
    exact recordLowerSeedTailChunk202Step.certifies
      (boundary.trans h201)
  have h203 : recordLowerSeedTailChunk203State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix203 := by
    have boundary : recordLowerSeedTailChunk203Before =
        recordLowerSeedTailChunk202State := by rfl
    exact recordLowerSeedTailChunk203Step.certifies
      (boundary.trans h202)
  have h204 : recordLowerSeedTailChunk204State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix204 := by
    have boundary : recordLowerSeedTailChunk204Before =
        recordLowerSeedTailChunk203State := by rfl
    exact recordLowerSeedTailChunk204Step.certifies
      (boundary.trans h203)
  have h205 : recordLowerSeedTailChunk205State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix205 := by
    have boundary : recordLowerSeedTailChunk205Before =
        recordLowerSeedTailChunk204State := by rfl
    exact recordLowerSeedTailChunk205Step.certifies
      (boundary.trans h204)
  have h206 : recordLowerSeedTailChunk206State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix206 := by
    have boundary : recordLowerSeedTailChunk206Before =
        recordLowerSeedTailChunk205State := by rfl
    exact recordLowerSeedTailChunk206Step.certifies
      (boundary.trans h205)
  have h207 : recordLowerSeedTailChunk207State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix207 := by
    have boundary : recordLowerSeedTailChunk207Before =
        recordLowerSeedTailChunk206State := by rfl
    exact recordLowerSeedTailChunk207Step.certifies
      (boundary.trans h206)
  have h208 : recordLowerSeedTailChunk208State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix208 := by
    have boundary : recordLowerSeedTailChunk208Before =
        recordLowerSeedTailChunk207State := by rfl
    exact recordLowerSeedTailChunk208Step.certifies
      (boundary.trans h207)
  have h209 : recordLowerSeedTailChunk209State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix209 := by
    have boundary : recordLowerSeedTailChunk209Before =
        recordLowerSeedTailChunk208State := by rfl
    exact recordLowerSeedTailChunk209Step.certifies
      (boundary.trans h208)
  have h210 : recordLowerSeedTailChunk210State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix210 := by
    have boundary : recordLowerSeedTailChunk210Before =
        recordLowerSeedTailChunk209State := by rfl
    exact recordLowerSeedTailChunk210Step.certifies
      (boundary.trans h209)
  have h211 : recordLowerSeedTailChunk211State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix211 := by
    have boundary : recordLowerSeedTailChunk211Before =
        recordLowerSeedTailChunk210State := by rfl
    exact recordLowerSeedTailChunk211Step.certifies
      (boundary.trans h210)
  have h212 : recordLowerSeedTailChunk212State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix212 := by
    have boundary : recordLowerSeedTailChunk212Before =
        recordLowerSeedTailChunk211State := by rfl
    exact recordLowerSeedTailChunk212Step.certifies
      (boundary.trans h211)
  have h213 : recordLowerSeedTailChunk213State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix213 := by
    have boundary : recordLowerSeedTailChunk213Before =
        recordLowerSeedTailChunk212State := by rfl
    exact recordLowerSeedTailChunk213Step.certifies
      (boundary.trans h212)
  have h214 : recordLowerSeedTailChunk214State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix214 := by
    have boundary : recordLowerSeedTailChunk214Before =
        recordLowerSeedTailChunk213State := by rfl
    exact recordLowerSeedTailChunk214Step.certifies
      (boundary.trans h213)
  have h215 : recordLowerSeedTailChunk215State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix215 := by
    have boundary : recordLowerSeedTailChunk215Before =
        recordLowerSeedTailChunk214State := by rfl
    exact recordLowerSeedTailChunk215Step.certifies
      (boundary.trans h214)
  have h216 : recordLowerSeedTailChunk216State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix216 := by
    have boundary : recordLowerSeedTailChunk216Before =
        recordLowerSeedTailChunk215State := by rfl
    exact recordLowerSeedTailChunk216Step.certifies
      (boundary.trans h215)
  have h217 : recordLowerSeedTailChunk217State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix217 := by
    have boundary : recordLowerSeedTailChunk217Before =
        recordLowerSeedTailChunk216State := by rfl
    exact recordLowerSeedTailChunk217Step.certifies
      (boundary.trans h216)
  have h218 : recordLowerSeedTailChunk218State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix218 := by
    have boundary : recordLowerSeedTailChunk218Before =
        recordLowerSeedTailChunk217State := by rfl
    exact recordLowerSeedTailChunk218Step.certifies
      (boundary.trans h217)
  have h219 : recordLowerSeedTailChunk219State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix219 := by
    have boundary : recordLowerSeedTailChunk219Before =
        recordLowerSeedTailChunk218State := by rfl
    exact recordLowerSeedTailChunk219Step.certifies
      (boundary.trans h218)
  have h220 : recordLowerSeedTailChunk220State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix220 := by
    have boundary : recordLowerSeedTailChunk220Before =
        recordLowerSeedTailChunk219State := by rfl
    exact recordLowerSeedTailChunk220Step.certifies
      (boundary.trans h219)
  have h221 : recordLowerSeedTailChunk221State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix221 := by
    have boundary : recordLowerSeedTailChunk221Before =
        recordLowerSeedTailChunk220State := by rfl
    exact recordLowerSeedTailChunk221Step.certifies
      (boundary.trans h220)
  have h222 : recordLowerSeedTailChunk222State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix222 := by
    have boundary : recordLowerSeedTailChunk222Before =
        recordLowerSeedTailChunk221State := by rfl
    exact recordLowerSeedTailChunk222Step.certifies
      (boundary.trans h221)
  have h223 : recordLowerSeedTailChunk223State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix223 := by
    have boundary : recordLowerSeedTailChunk223Before =
        recordLowerSeedTailChunk222State := by rfl
    exact recordLowerSeedTailChunk223Step.certifies
      (boundary.trans h222)
  have h224 : recordLowerSeedTailChunk224State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix224 := by
    have boundary : recordLowerSeedTailChunk224Before =
        recordLowerSeedTailChunk223State := by rfl
    exact recordLowerSeedTailChunk224Step.certifies
      (boundary.trans h223)
  have h225 : recordLowerSeedTailChunk225State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix225 := by
    have boundary : recordLowerSeedTailChunk225Before =
        recordLowerSeedTailChunk224State := by rfl
    exact recordLowerSeedTailChunk225Step.certifies
      (boundary.trans h224)
  have h226 : recordLowerSeedTailChunk226State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix226 := by
    have boundary : recordLowerSeedTailChunk226Before =
        recordLowerSeedTailChunk225State := by rfl
    exact recordLowerSeedTailChunk226Step.certifies
      (boundary.trans h225)
  have h227 : recordLowerSeedTailChunk227State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix227 := by
    have boundary : recordLowerSeedTailChunk227Before =
        recordLowerSeedTailChunk226State := by rfl
    exact recordLowerSeedTailChunk227Step.certifies
      (boundary.trans h226)
  have h228 : recordLowerSeedTailChunk228State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix228 := by
    have boundary : recordLowerSeedTailChunk228Before =
        recordLowerSeedTailChunk227State := by rfl
    exact recordLowerSeedTailChunk228Step.certifies
      (boundary.trans h227)
  have h229 : recordLowerSeedTailChunk229State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix229 := by
    have boundary : recordLowerSeedTailChunk229Before =
        recordLowerSeedTailChunk228State := by rfl
    exact recordLowerSeedTailChunk229Step.certifies
      (boundary.trans h228)
  have h230 : recordLowerSeedTailChunk230State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix230 := by
    have boundary : recordLowerSeedTailChunk230Before =
        recordLowerSeedTailChunk229State := by rfl
    exact recordLowerSeedTailChunk230Step.certifies
      (boundary.trans h229)
  have h231 : recordLowerSeedTailChunk231State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix231 := by
    have boundary : recordLowerSeedTailChunk231Before =
        recordLowerSeedTailChunk230State := by rfl
    exact recordLowerSeedTailChunk231Step.certifies
      (boundary.trans h230)
  have h232 : recordLowerSeedTailChunk232State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix232 := by
    have boundary : recordLowerSeedTailChunk232Before =
        recordLowerSeedTailChunk231State := by rfl
    exact recordLowerSeedTailChunk232Step.certifies
      (boundary.trans h231)
  have h233 : recordLowerSeedTailChunk233State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix233 := by
    have boundary : recordLowerSeedTailChunk233Before =
        recordLowerSeedTailChunk232State := by rfl
    exact recordLowerSeedTailChunk233Step.certifies
      (boundary.trans h232)
  have h234 : recordLowerSeedTailChunk234State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix234 := by
    have boundary : recordLowerSeedTailChunk234Before =
        recordLowerSeedTailChunk233State := by rfl
    exact recordLowerSeedTailChunk234Step.certifies
      (boundary.trans h233)
  have h235 : recordLowerSeedTailChunk235State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix235 := by
    have boundary : recordLowerSeedTailChunk235Before =
        recordLowerSeedTailChunk234State := by rfl
    exact recordLowerSeedTailChunk235Step.certifies
      (boundary.trans h234)
  have h236 : recordLowerSeedTailChunk236State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix236 := by
    have boundary : recordLowerSeedTailChunk236Before =
        recordLowerSeedTailChunk235State := by rfl
    exact recordLowerSeedTailChunk236Step.certifies
      (boundary.trans h235)
  have h237 : recordLowerSeedTailChunk237State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix237 := by
    have boundary : recordLowerSeedTailChunk237Before =
        recordLowerSeedTailChunk236State := by rfl
    exact recordLowerSeedTailChunk237Step.certifies
      (boundary.trans h236)
  have h238 : recordLowerSeedTailChunk238State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix238 := by
    have boundary : recordLowerSeedTailChunk238Before =
        recordLowerSeedTailChunk237State := by rfl
    exact recordLowerSeedTailChunk238Step.certifies
      (boundary.trans h237)
  have h239 : recordLowerSeedTailChunk239State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix239 := by
    have boundary : recordLowerSeedTailChunk239Before =
        recordLowerSeedTailChunk238State := by rfl
    exact recordLowerSeedTailChunk239Step.certifies
      (boundary.trans h238)
  have h240 : recordLowerSeedTailChunk240State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix240 := by
    have boundary : recordLowerSeedTailChunk240Before =
        recordLowerSeedTailChunk239State := by rfl
    exact recordLowerSeedTailChunk240Step.certifies
      (boundary.trans h239)
  exact h240

end PrimeFactorUnimodality
