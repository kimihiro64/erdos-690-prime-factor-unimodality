import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Assembly.Part02
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part120

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-upper-seed-base11.json` (semantic SHA-256 `493791f7b41de1500c4b830f254f9f92fd9c5d50d639b62aa2b46ca48591321f`, excluding elapsed time). Semantic tail assembly group 3. -/

namespace PrimeFactorUnimodality

theorem recordUpperSeedTailGroup03_semantic :
    recordUpperSeedTailChunk120State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix120 := by
  have h081 : recordUpperSeedTailChunk081State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix081 := by
    have boundary : recordUpperSeedTailChunk081Before =
        recordUpperSeedTailChunk080State := by rfl
    exact recordUpperSeedTailChunk081Step.certifies
      (boundary.trans recordUpperSeedTailGroup02_semantic)
  have h082 : recordUpperSeedTailChunk082State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix082 := by
    have boundary : recordUpperSeedTailChunk082Before =
        recordUpperSeedTailChunk081State := by rfl
    exact recordUpperSeedTailChunk082Step.certifies
      (boundary.trans h081)
  have h083 : recordUpperSeedTailChunk083State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix083 := by
    have boundary : recordUpperSeedTailChunk083Before =
        recordUpperSeedTailChunk082State := by rfl
    exact recordUpperSeedTailChunk083Step.certifies
      (boundary.trans h082)
  have h084 : recordUpperSeedTailChunk084State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix084 := by
    have boundary : recordUpperSeedTailChunk084Before =
        recordUpperSeedTailChunk083State := by rfl
    exact recordUpperSeedTailChunk084Step.certifies
      (boundary.trans h083)
  have h085 : recordUpperSeedTailChunk085State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix085 := by
    have boundary : recordUpperSeedTailChunk085Before =
        recordUpperSeedTailChunk084State := by rfl
    exact recordUpperSeedTailChunk085Step.certifies
      (boundary.trans h084)
  have h086 : recordUpperSeedTailChunk086State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix086 := by
    have boundary : recordUpperSeedTailChunk086Before =
        recordUpperSeedTailChunk085State := by rfl
    exact recordUpperSeedTailChunk086Step.certifies
      (boundary.trans h085)
  have h087 : recordUpperSeedTailChunk087State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix087 := by
    have boundary : recordUpperSeedTailChunk087Before =
        recordUpperSeedTailChunk086State := by rfl
    exact recordUpperSeedTailChunk087Step.certifies
      (boundary.trans h086)
  have h088 : recordUpperSeedTailChunk088State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix088 := by
    have boundary : recordUpperSeedTailChunk088Before =
        recordUpperSeedTailChunk087State := by rfl
    exact recordUpperSeedTailChunk088Step.certifies
      (boundary.trans h087)
  have h089 : recordUpperSeedTailChunk089State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix089 := by
    have boundary : recordUpperSeedTailChunk089Before =
        recordUpperSeedTailChunk088State := by rfl
    exact recordUpperSeedTailChunk089Step.certifies
      (boundary.trans h088)
  have h090 : recordUpperSeedTailChunk090State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix090 := by
    have boundary : recordUpperSeedTailChunk090Before =
        recordUpperSeedTailChunk089State := by rfl
    exact recordUpperSeedTailChunk090Step.certifies
      (boundary.trans h089)
  have h091 : recordUpperSeedTailChunk091State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix091 := by
    have boundary : recordUpperSeedTailChunk091Before =
        recordUpperSeedTailChunk090State := by rfl
    exact recordUpperSeedTailChunk091Step.certifies
      (boundary.trans h090)
  have h092 : recordUpperSeedTailChunk092State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix092 := by
    have boundary : recordUpperSeedTailChunk092Before =
        recordUpperSeedTailChunk091State := by rfl
    exact recordUpperSeedTailChunk092Step.certifies
      (boundary.trans h091)
  have h093 : recordUpperSeedTailChunk093State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix093 := by
    have boundary : recordUpperSeedTailChunk093Before =
        recordUpperSeedTailChunk092State := by rfl
    exact recordUpperSeedTailChunk093Step.certifies
      (boundary.trans h092)
  have h094 : recordUpperSeedTailChunk094State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix094 := by
    have boundary : recordUpperSeedTailChunk094Before =
        recordUpperSeedTailChunk093State := by rfl
    exact recordUpperSeedTailChunk094Step.certifies
      (boundary.trans h093)
  have h095 : recordUpperSeedTailChunk095State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix095 := by
    have boundary : recordUpperSeedTailChunk095Before =
        recordUpperSeedTailChunk094State := by rfl
    exact recordUpperSeedTailChunk095Step.certifies
      (boundary.trans h094)
  have h096 : recordUpperSeedTailChunk096State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix096 := by
    have boundary : recordUpperSeedTailChunk096Before =
        recordUpperSeedTailChunk095State := by rfl
    exact recordUpperSeedTailChunk096Step.certifies
      (boundary.trans h095)
  have h097 : recordUpperSeedTailChunk097State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix097 := by
    have boundary : recordUpperSeedTailChunk097Before =
        recordUpperSeedTailChunk096State := by rfl
    exact recordUpperSeedTailChunk097Step.certifies
      (boundary.trans h096)
  have h098 : recordUpperSeedTailChunk098State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix098 := by
    have boundary : recordUpperSeedTailChunk098Before =
        recordUpperSeedTailChunk097State := by rfl
    exact recordUpperSeedTailChunk098Step.certifies
      (boundary.trans h097)
  have h099 : recordUpperSeedTailChunk099State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix099 := by
    have boundary : recordUpperSeedTailChunk099Before =
        recordUpperSeedTailChunk098State := by rfl
    exact recordUpperSeedTailChunk099Step.certifies
      (boundary.trans h098)
  have h100 : recordUpperSeedTailChunk100State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix100 := by
    have boundary : recordUpperSeedTailChunk100Before =
        recordUpperSeedTailChunk099State := by rfl
    exact recordUpperSeedTailChunk100Step.certifies
      (boundary.trans h099)
  have h101 : recordUpperSeedTailChunk101State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix101 := by
    have boundary : recordUpperSeedTailChunk101Before =
        recordUpperSeedTailChunk100State := by rfl
    exact recordUpperSeedTailChunk101Step.certifies
      (boundary.trans h100)
  have h102 : recordUpperSeedTailChunk102State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix102 := by
    have boundary : recordUpperSeedTailChunk102Before =
        recordUpperSeedTailChunk101State := by rfl
    exact recordUpperSeedTailChunk102Step.certifies
      (boundary.trans h101)
  have h103 : recordUpperSeedTailChunk103State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix103 := by
    have boundary : recordUpperSeedTailChunk103Before =
        recordUpperSeedTailChunk102State := by rfl
    exact recordUpperSeedTailChunk103Step.certifies
      (boundary.trans h102)
  have h104 : recordUpperSeedTailChunk104State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix104 := by
    have boundary : recordUpperSeedTailChunk104Before =
        recordUpperSeedTailChunk103State := by rfl
    exact recordUpperSeedTailChunk104Step.certifies
      (boundary.trans h103)
  have h105 : recordUpperSeedTailChunk105State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix105 := by
    have boundary : recordUpperSeedTailChunk105Before =
        recordUpperSeedTailChunk104State := by rfl
    exact recordUpperSeedTailChunk105Step.certifies
      (boundary.trans h104)
  have h106 : recordUpperSeedTailChunk106State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix106 := by
    have boundary : recordUpperSeedTailChunk106Before =
        recordUpperSeedTailChunk105State := by rfl
    exact recordUpperSeedTailChunk106Step.certifies
      (boundary.trans h105)
  have h107 : recordUpperSeedTailChunk107State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix107 := by
    have boundary : recordUpperSeedTailChunk107Before =
        recordUpperSeedTailChunk106State := by rfl
    exact recordUpperSeedTailChunk107Step.certifies
      (boundary.trans h106)
  have h108 : recordUpperSeedTailChunk108State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix108 := by
    have boundary : recordUpperSeedTailChunk108Before =
        recordUpperSeedTailChunk107State := by rfl
    exact recordUpperSeedTailChunk108Step.certifies
      (boundary.trans h107)
  have h109 : recordUpperSeedTailChunk109State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix109 := by
    have boundary : recordUpperSeedTailChunk109Before =
        recordUpperSeedTailChunk108State := by rfl
    exact recordUpperSeedTailChunk109Step.certifies
      (boundary.trans h108)
  have h110 : recordUpperSeedTailChunk110State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix110 := by
    have boundary : recordUpperSeedTailChunk110Before =
        recordUpperSeedTailChunk109State := by rfl
    exact recordUpperSeedTailChunk110Step.certifies
      (boundary.trans h109)
  have h111 : recordUpperSeedTailChunk111State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix111 := by
    have boundary : recordUpperSeedTailChunk111Before =
        recordUpperSeedTailChunk110State := by rfl
    exact recordUpperSeedTailChunk111Step.certifies
      (boundary.trans h110)
  have h112 : recordUpperSeedTailChunk112State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix112 := by
    have boundary : recordUpperSeedTailChunk112Before =
        recordUpperSeedTailChunk111State := by rfl
    exact recordUpperSeedTailChunk112Step.certifies
      (boundary.trans h111)
  have h113 : recordUpperSeedTailChunk113State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix113 := by
    have boundary : recordUpperSeedTailChunk113Before =
        recordUpperSeedTailChunk112State := by rfl
    exact recordUpperSeedTailChunk113Step.certifies
      (boundary.trans h112)
  have h114 : recordUpperSeedTailChunk114State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix114 := by
    have boundary : recordUpperSeedTailChunk114Before =
        recordUpperSeedTailChunk113State := by rfl
    exact recordUpperSeedTailChunk114Step.certifies
      (boundary.trans h113)
  have h115 : recordUpperSeedTailChunk115State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix115 := by
    have boundary : recordUpperSeedTailChunk115Before =
        recordUpperSeedTailChunk114State := by rfl
    exact recordUpperSeedTailChunk115Step.certifies
      (boundary.trans h114)
  have h116 : recordUpperSeedTailChunk116State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix116 := by
    have boundary : recordUpperSeedTailChunk116Before =
        recordUpperSeedTailChunk115State := by rfl
    exact recordUpperSeedTailChunk116Step.certifies
      (boundary.trans h115)
  have h117 : recordUpperSeedTailChunk117State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix117 := by
    have boundary : recordUpperSeedTailChunk117Before =
        recordUpperSeedTailChunk116State := by rfl
    exact recordUpperSeedTailChunk117Step.certifies
      (boundary.trans h116)
  have h118 : recordUpperSeedTailChunk118State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix118 := by
    have boundary : recordUpperSeedTailChunk118Before =
        recordUpperSeedTailChunk117State := by rfl
    exact recordUpperSeedTailChunk118Step.certifies
      (boundary.trans h117)
  have h119 : recordUpperSeedTailChunk119State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix119 := by
    have boundary : recordUpperSeedTailChunk119Before =
        recordUpperSeedTailChunk118State := by rfl
    exact recordUpperSeedTailChunk119Step.certifies
      (boundary.trans h118)
  have h120 : recordUpperSeedTailChunk120State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix120 := by
    have boundary : recordUpperSeedTailChunk120Before =
        recordUpperSeedTailChunk119State := by rfl
    exact recordUpperSeedTailChunk120Step.certifies
      (boundary.trans h119)
  exact h120

end PrimeFactorUnimodality
