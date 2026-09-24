import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Assembly.Part02
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part120

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-lower-seed.json` (semantic SHA-256 `3ce105dad06099400dfd2e30c65d47c6e02828915452a8459553c3bb0eb78b73`, excluding elapsed time). Semantic tail assembly group 3. -/

namespace PrimeFactorUnimodality

theorem recordLowerSeedTailGroup03_semantic :
    recordLowerSeedTailChunk120State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix120 := by
  have h081 : recordLowerSeedTailChunk081State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix081 := by
    have boundary : recordLowerSeedTailChunk081Before =
        recordLowerSeedTailChunk080State := by rfl
    exact recordLowerSeedTailChunk081Step.certifies
      (boundary.trans recordLowerSeedTailGroup02_semantic)
  have h082 : recordLowerSeedTailChunk082State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix082 := by
    have boundary : recordLowerSeedTailChunk082Before =
        recordLowerSeedTailChunk081State := by rfl
    exact recordLowerSeedTailChunk082Step.certifies
      (boundary.trans h081)
  have h083 : recordLowerSeedTailChunk083State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix083 := by
    have boundary : recordLowerSeedTailChunk083Before =
        recordLowerSeedTailChunk082State := by rfl
    exact recordLowerSeedTailChunk083Step.certifies
      (boundary.trans h082)
  have h084 : recordLowerSeedTailChunk084State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix084 := by
    have boundary : recordLowerSeedTailChunk084Before =
        recordLowerSeedTailChunk083State := by rfl
    exact recordLowerSeedTailChunk084Step.certifies
      (boundary.trans h083)
  have h085 : recordLowerSeedTailChunk085State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix085 := by
    have boundary : recordLowerSeedTailChunk085Before =
        recordLowerSeedTailChunk084State := by rfl
    exact recordLowerSeedTailChunk085Step.certifies
      (boundary.trans h084)
  have h086 : recordLowerSeedTailChunk086State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix086 := by
    have boundary : recordLowerSeedTailChunk086Before =
        recordLowerSeedTailChunk085State := by rfl
    exact recordLowerSeedTailChunk086Step.certifies
      (boundary.trans h085)
  have h087 : recordLowerSeedTailChunk087State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix087 := by
    have boundary : recordLowerSeedTailChunk087Before =
        recordLowerSeedTailChunk086State := by rfl
    exact recordLowerSeedTailChunk087Step.certifies
      (boundary.trans h086)
  have h088 : recordLowerSeedTailChunk088State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix088 := by
    have boundary : recordLowerSeedTailChunk088Before =
        recordLowerSeedTailChunk087State := by rfl
    exact recordLowerSeedTailChunk088Step.certifies
      (boundary.trans h087)
  have h089 : recordLowerSeedTailChunk089State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix089 := by
    have boundary : recordLowerSeedTailChunk089Before =
        recordLowerSeedTailChunk088State := by rfl
    exact recordLowerSeedTailChunk089Step.certifies
      (boundary.trans h088)
  have h090 : recordLowerSeedTailChunk090State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix090 := by
    have boundary : recordLowerSeedTailChunk090Before =
        recordLowerSeedTailChunk089State := by rfl
    exact recordLowerSeedTailChunk090Step.certifies
      (boundary.trans h089)
  have h091 : recordLowerSeedTailChunk091State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix091 := by
    have boundary : recordLowerSeedTailChunk091Before =
        recordLowerSeedTailChunk090State := by rfl
    exact recordLowerSeedTailChunk091Step.certifies
      (boundary.trans h090)
  have h092 : recordLowerSeedTailChunk092State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix092 := by
    have boundary : recordLowerSeedTailChunk092Before =
        recordLowerSeedTailChunk091State := by rfl
    exact recordLowerSeedTailChunk092Step.certifies
      (boundary.trans h091)
  have h093 : recordLowerSeedTailChunk093State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix093 := by
    have boundary : recordLowerSeedTailChunk093Before =
        recordLowerSeedTailChunk092State := by rfl
    exact recordLowerSeedTailChunk093Step.certifies
      (boundary.trans h092)
  have h094 : recordLowerSeedTailChunk094State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix094 := by
    have boundary : recordLowerSeedTailChunk094Before =
        recordLowerSeedTailChunk093State := by rfl
    exact recordLowerSeedTailChunk094Step.certifies
      (boundary.trans h093)
  have h095 : recordLowerSeedTailChunk095State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix095 := by
    have boundary : recordLowerSeedTailChunk095Before =
        recordLowerSeedTailChunk094State := by rfl
    exact recordLowerSeedTailChunk095Step.certifies
      (boundary.trans h094)
  have h096 : recordLowerSeedTailChunk096State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix096 := by
    have boundary : recordLowerSeedTailChunk096Before =
        recordLowerSeedTailChunk095State := by rfl
    exact recordLowerSeedTailChunk096Step.certifies
      (boundary.trans h095)
  have h097 : recordLowerSeedTailChunk097State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix097 := by
    have boundary : recordLowerSeedTailChunk097Before =
        recordLowerSeedTailChunk096State := by rfl
    exact recordLowerSeedTailChunk097Step.certifies
      (boundary.trans h096)
  have h098 : recordLowerSeedTailChunk098State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix098 := by
    have boundary : recordLowerSeedTailChunk098Before =
        recordLowerSeedTailChunk097State := by rfl
    exact recordLowerSeedTailChunk098Step.certifies
      (boundary.trans h097)
  have h099 : recordLowerSeedTailChunk099State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix099 := by
    have boundary : recordLowerSeedTailChunk099Before =
        recordLowerSeedTailChunk098State := by rfl
    exact recordLowerSeedTailChunk099Step.certifies
      (boundary.trans h098)
  have h100 : recordLowerSeedTailChunk100State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix100 := by
    have boundary : recordLowerSeedTailChunk100Before =
        recordLowerSeedTailChunk099State := by rfl
    exact recordLowerSeedTailChunk100Step.certifies
      (boundary.trans h099)
  have h101 : recordLowerSeedTailChunk101State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix101 := by
    have boundary : recordLowerSeedTailChunk101Before =
        recordLowerSeedTailChunk100State := by rfl
    exact recordLowerSeedTailChunk101Step.certifies
      (boundary.trans h100)
  have h102 : recordLowerSeedTailChunk102State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix102 := by
    have boundary : recordLowerSeedTailChunk102Before =
        recordLowerSeedTailChunk101State := by rfl
    exact recordLowerSeedTailChunk102Step.certifies
      (boundary.trans h101)
  have h103 : recordLowerSeedTailChunk103State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix103 := by
    have boundary : recordLowerSeedTailChunk103Before =
        recordLowerSeedTailChunk102State := by rfl
    exact recordLowerSeedTailChunk103Step.certifies
      (boundary.trans h102)
  have h104 : recordLowerSeedTailChunk104State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix104 := by
    have boundary : recordLowerSeedTailChunk104Before =
        recordLowerSeedTailChunk103State := by rfl
    exact recordLowerSeedTailChunk104Step.certifies
      (boundary.trans h103)
  have h105 : recordLowerSeedTailChunk105State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix105 := by
    have boundary : recordLowerSeedTailChunk105Before =
        recordLowerSeedTailChunk104State := by rfl
    exact recordLowerSeedTailChunk105Step.certifies
      (boundary.trans h104)
  have h106 : recordLowerSeedTailChunk106State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix106 := by
    have boundary : recordLowerSeedTailChunk106Before =
        recordLowerSeedTailChunk105State := by rfl
    exact recordLowerSeedTailChunk106Step.certifies
      (boundary.trans h105)
  have h107 : recordLowerSeedTailChunk107State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix107 := by
    have boundary : recordLowerSeedTailChunk107Before =
        recordLowerSeedTailChunk106State := by rfl
    exact recordLowerSeedTailChunk107Step.certifies
      (boundary.trans h106)
  have h108 : recordLowerSeedTailChunk108State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix108 := by
    have boundary : recordLowerSeedTailChunk108Before =
        recordLowerSeedTailChunk107State := by rfl
    exact recordLowerSeedTailChunk108Step.certifies
      (boundary.trans h107)
  have h109 : recordLowerSeedTailChunk109State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix109 := by
    have boundary : recordLowerSeedTailChunk109Before =
        recordLowerSeedTailChunk108State := by rfl
    exact recordLowerSeedTailChunk109Step.certifies
      (boundary.trans h108)
  have h110 : recordLowerSeedTailChunk110State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix110 := by
    have boundary : recordLowerSeedTailChunk110Before =
        recordLowerSeedTailChunk109State := by rfl
    exact recordLowerSeedTailChunk110Step.certifies
      (boundary.trans h109)
  have h111 : recordLowerSeedTailChunk111State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix111 := by
    have boundary : recordLowerSeedTailChunk111Before =
        recordLowerSeedTailChunk110State := by rfl
    exact recordLowerSeedTailChunk111Step.certifies
      (boundary.trans h110)
  have h112 : recordLowerSeedTailChunk112State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix112 := by
    have boundary : recordLowerSeedTailChunk112Before =
        recordLowerSeedTailChunk111State := by rfl
    exact recordLowerSeedTailChunk112Step.certifies
      (boundary.trans h111)
  have h113 : recordLowerSeedTailChunk113State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix113 := by
    have boundary : recordLowerSeedTailChunk113Before =
        recordLowerSeedTailChunk112State := by rfl
    exact recordLowerSeedTailChunk113Step.certifies
      (boundary.trans h112)
  have h114 : recordLowerSeedTailChunk114State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix114 := by
    have boundary : recordLowerSeedTailChunk114Before =
        recordLowerSeedTailChunk113State := by rfl
    exact recordLowerSeedTailChunk114Step.certifies
      (boundary.trans h113)
  have h115 : recordLowerSeedTailChunk115State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix115 := by
    have boundary : recordLowerSeedTailChunk115Before =
        recordLowerSeedTailChunk114State := by rfl
    exact recordLowerSeedTailChunk115Step.certifies
      (boundary.trans h114)
  have h116 : recordLowerSeedTailChunk116State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix116 := by
    have boundary : recordLowerSeedTailChunk116Before =
        recordLowerSeedTailChunk115State := by rfl
    exact recordLowerSeedTailChunk116Step.certifies
      (boundary.trans h115)
  have h117 : recordLowerSeedTailChunk117State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix117 := by
    have boundary : recordLowerSeedTailChunk117Before =
        recordLowerSeedTailChunk116State := by rfl
    exact recordLowerSeedTailChunk117Step.certifies
      (boundary.trans h116)
  have h118 : recordLowerSeedTailChunk118State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix118 := by
    have boundary : recordLowerSeedTailChunk118Before =
        recordLowerSeedTailChunk117State := by rfl
    exact recordLowerSeedTailChunk118Step.certifies
      (boundary.trans h117)
  have h119 : recordLowerSeedTailChunk119State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix119 := by
    have boundary : recordLowerSeedTailChunk119Before =
        recordLowerSeedTailChunk118State := by rfl
    exact recordLowerSeedTailChunk119Step.certifies
      (boundary.trans h118)
  have h120 : recordLowerSeedTailChunk120State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix120 := by
    have boundary : recordLowerSeedTailChunk120Before =
        recordLowerSeedTailChunk119State := by rfl
    exact recordLowerSeedTailChunk120Step.certifies
      (boundary.trans h119)
  exact h120

end PrimeFactorUnimodality
