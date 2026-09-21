import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Assembly.Part02
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part120

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-upper-seed-base11.json` (semantic SHA-256 `493791f7b41de1500c4b830f254f9f92fd9c5d50d639b62aa2b46ca48591321f`, excluding elapsed time). Semantic tail assembly group 3. -/

namespace PrimeFactorUnimodality

theorem recordUpperSeedTailGroup03_semantic :
    recordUpperSeedTailChunk120State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix120 := by
  have h081 : recordUpperSeedTailChunk081State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix081 := by
    have prior : recordUpperSeedTailChunk081Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix080 := by
      simpa only [
        recordUpperSeedTailChunk081Before,
        recordUpperSeedTailChunk080State] using recordUpperSeedTailGroup02_semantic
    simpa only [recordUpperSeedTailPrefix081] using
      recordUpperSeedTailChunk081Step.certifies prior
  have h082 : recordUpperSeedTailChunk082State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix082 := by
    have prior : recordUpperSeedTailChunk082Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix081 := by
      simpa only [
        recordUpperSeedTailChunk082Before,
        recordUpperSeedTailChunk081State] using h081
    simpa only [recordUpperSeedTailPrefix082] using
      recordUpperSeedTailChunk082Step.certifies prior
  have h083 : recordUpperSeedTailChunk083State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix083 := by
    have prior : recordUpperSeedTailChunk083Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix082 := by
      simpa only [
        recordUpperSeedTailChunk083Before,
        recordUpperSeedTailChunk082State] using h082
    simpa only [recordUpperSeedTailPrefix083] using
      recordUpperSeedTailChunk083Step.certifies prior
  have h084 : recordUpperSeedTailChunk084State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix084 := by
    have prior : recordUpperSeedTailChunk084Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix083 := by
      simpa only [
        recordUpperSeedTailChunk084Before,
        recordUpperSeedTailChunk083State] using h083
    simpa only [recordUpperSeedTailPrefix084] using
      recordUpperSeedTailChunk084Step.certifies prior
  have h085 : recordUpperSeedTailChunk085State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix085 := by
    have prior : recordUpperSeedTailChunk085Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix084 := by
      simpa only [
        recordUpperSeedTailChunk085Before,
        recordUpperSeedTailChunk084State] using h084
    simpa only [recordUpperSeedTailPrefix085] using
      recordUpperSeedTailChunk085Step.certifies prior
  have h086 : recordUpperSeedTailChunk086State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix086 := by
    have prior : recordUpperSeedTailChunk086Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix085 := by
      simpa only [
        recordUpperSeedTailChunk086Before,
        recordUpperSeedTailChunk085State] using h085
    simpa only [recordUpperSeedTailPrefix086] using
      recordUpperSeedTailChunk086Step.certifies prior
  have h087 : recordUpperSeedTailChunk087State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix087 := by
    have prior : recordUpperSeedTailChunk087Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix086 := by
      simpa only [
        recordUpperSeedTailChunk087Before,
        recordUpperSeedTailChunk086State] using h086
    simpa only [recordUpperSeedTailPrefix087] using
      recordUpperSeedTailChunk087Step.certifies prior
  have h088 : recordUpperSeedTailChunk088State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix088 := by
    have prior : recordUpperSeedTailChunk088Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix087 := by
      simpa only [
        recordUpperSeedTailChunk088Before,
        recordUpperSeedTailChunk087State] using h087
    simpa only [recordUpperSeedTailPrefix088] using
      recordUpperSeedTailChunk088Step.certifies prior
  have h089 : recordUpperSeedTailChunk089State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix089 := by
    have prior : recordUpperSeedTailChunk089Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix088 := by
      simpa only [
        recordUpperSeedTailChunk089Before,
        recordUpperSeedTailChunk088State] using h088
    simpa only [recordUpperSeedTailPrefix089] using
      recordUpperSeedTailChunk089Step.certifies prior
  have h090 : recordUpperSeedTailChunk090State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix090 := by
    have prior : recordUpperSeedTailChunk090Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix089 := by
      simpa only [
        recordUpperSeedTailChunk090Before,
        recordUpperSeedTailChunk089State] using h089
    simpa only [recordUpperSeedTailPrefix090] using
      recordUpperSeedTailChunk090Step.certifies prior
  have h091 : recordUpperSeedTailChunk091State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix091 := by
    have prior : recordUpperSeedTailChunk091Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix090 := by
      simpa only [
        recordUpperSeedTailChunk091Before,
        recordUpperSeedTailChunk090State] using h090
    simpa only [recordUpperSeedTailPrefix091] using
      recordUpperSeedTailChunk091Step.certifies prior
  have h092 : recordUpperSeedTailChunk092State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix092 := by
    have prior : recordUpperSeedTailChunk092Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix091 := by
      simpa only [
        recordUpperSeedTailChunk092Before,
        recordUpperSeedTailChunk091State] using h091
    simpa only [recordUpperSeedTailPrefix092] using
      recordUpperSeedTailChunk092Step.certifies prior
  have h093 : recordUpperSeedTailChunk093State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix093 := by
    have prior : recordUpperSeedTailChunk093Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix092 := by
      simpa only [
        recordUpperSeedTailChunk093Before,
        recordUpperSeedTailChunk092State] using h092
    simpa only [recordUpperSeedTailPrefix093] using
      recordUpperSeedTailChunk093Step.certifies prior
  have h094 : recordUpperSeedTailChunk094State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix094 := by
    have prior : recordUpperSeedTailChunk094Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix093 := by
      simpa only [
        recordUpperSeedTailChunk094Before,
        recordUpperSeedTailChunk093State] using h093
    simpa only [recordUpperSeedTailPrefix094] using
      recordUpperSeedTailChunk094Step.certifies prior
  have h095 : recordUpperSeedTailChunk095State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix095 := by
    have prior : recordUpperSeedTailChunk095Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix094 := by
      simpa only [
        recordUpperSeedTailChunk095Before,
        recordUpperSeedTailChunk094State] using h094
    simpa only [recordUpperSeedTailPrefix095] using
      recordUpperSeedTailChunk095Step.certifies prior
  have h096 : recordUpperSeedTailChunk096State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix096 := by
    have prior : recordUpperSeedTailChunk096Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix095 := by
      simpa only [
        recordUpperSeedTailChunk096Before,
        recordUpperSeedTailChunk095State] using h095
    simpa only [recordUpperSeedTailPrefix096] using
      recordUpperSeedTailChunk096Step.certifies prior
  have h097 : recordUpperSeedTailChunk097State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix097 := by
    have prior : recordUpperSeedTailChunk097Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix096 := by
      simpa only [
        recordUpperSeedTailChunk097Before,
        recordUpperSeedTailChunk096State] using h096
    simpa only [recordUpperSeedTailPrefix097] using
      recordUpperSeedTailChunk097Step.certifies prior
  have h098 : recordUpperSeedTailChunk098State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix098 := by
    have prior : recordUpperSeedTailChunk098Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix097 := by
      simpa only [
        recordUpperSeedTailChunk098Before,
        recordUpperSeedTailChunk097State] using h097
    simpa only [recordUpperSeedTailPrefix098] using
      recordUpperSeedTailChunk098Step.certifies prior
  have h099 : recordUpperSeedTailChunk099State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix099 := by
    have prior : recordUpperSeedTailChunk099Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix098 := by
      simpa only [
        recordUpperSeedTailChunk099Before,
        recordUpperSeedTailChunk098State] using h098
    simpa only [recordUpperSeedTailPrefix099] using
      recordUpperSeedTailChunk099Step.certifies prior
  have h100 : recordUpperSeedTailChunk100State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix100 := by
    have prior : recordUpperSeedTailChunk100Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix099 := by
      simpa only [
        recordUpperSeedTailChunk100Before,
        recordUpperSeedTailChunk099State] using h099
    simpa only [recordUpperSeedTailPrefix100] using
      recordUpperSeedTailChunk100Step.certifies prior
  have h101 : recordUpperSeedTailChunk101State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix101 := by
    have prior : recordUpperSeedTailChunk101Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix100 := by
      simpa only [
        recordUpperSeedTailChunk101Before,
        recordUpperSeedTailChunk100State] using h100
    simpa only [recordUpperSeedTailPrefix101] using
      recordUpperSeedTailChunk101Step.certifies prior
  have h102 : recordUpperSeedTailChunk102State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix102 := by
    have prior : recordUpperSeedTailChunk102Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix101 := by
      simpa only [
        recordUpperSeedTailChunk102Before,
        recordUpperSeedTailChunk101State] using h101
    simpa only [recordUpperSeedTailPrefix102] using
      recordUpperSeedTailChunk102Step.certifies prior
  have h103 : recordUpperSeedTailChunk103State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix103 := by
    have prior : recordUpperSeedTailChunk103Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix102 := by
      simpa only [
        recordUpperSeedTailChunk103Before,
        recordUpperSeedTailChunk102State] using h102
    simpa only [recordUpperSeedTailPrefix103] using
      recordUpperSeedTailChunk103Step.certifies prior
  have h104 : recordUpperSeedTailChunk104State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix104 := by
    have prior : recordUpperSeedTailChunk104Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix103 := by
      simpa only [
        recordUpperSeedTailChunk104Before,
        recordUpperSeedTailChunk103State] using h103
    simpa only [recordUpperSeedTailPrefix104] using
      recordUpperSeedTailChunk104Step.certifies prior
  have h105 : recordUpperSeedTailChunk105State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix105 := by
    have prior : recordUpperSeedTailChunk105Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix104 := by
      simpa only [
        recordUpperSeedTailChunk105Before,
        recordUpperSeedTailChunk104State] using h104
    simpa only [recordUpperSeedTailPrefix105] using
      recordUpperSeedTailChunk105Step.certifies prior
  have h106 : recordUpperSeedTailChunk106State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix106 := by
    have prior : recordUpperSeedTailChunk106Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix105 := by
      simpa only [
        recordUpperSeedTailChunk106Before,
        recordUpperSeedTailChunk105State] using h105
    simpa only [recordUpperSeedTailPrefix106] using
      recordUpperSeedTailChunk106Step.certifies prior
  have h107 : recordUpperSeedTailChunk107State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix107 := by
    have prior : recordUpperSeedTailChunk107Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix106 := by
      simpa only [
        recordUpperSeedTailChunk107Before,
        recordUpperSeedTailChunk106State] using h106
    simpa only [recordUpperSeedTailPrefix107] using
      recordUpperSeedTailChunk107Step.certifies prior
  have h108 : recordUpperSeedTailChunk108State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix108 := by
    have prior : recordUpperSeedTailChunk108Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix107 := by
      simpa only [
        recordUpperSeedTailChunk108Before,
        recordUpperSeedTailChunk107State] using h107
    simpa only [recordUpperSeedTailPrefix108] using
      recordUpperSeedTailChunk108Step.certifies prior
  have h109 : recordUpperSeedTailChunk109State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix109 := by
    have prior : recordUpperSeedTailChunk109Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix108 := by
      simpa only [
        recordUpperSeedTailChunk109Before,
        recordUpperSeedTailChunk108State] using h108
    simpa only [recordUpperSeedTailPrefix109] using
      recordUpperSeedTailChunk109Step.certifies prior
  have h110 : recordUpperSeedTailChunk110State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix110 := by
    have prior : recordUpperSeedTailChunk110Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix109 := by
      simpa only [
        recordUpperSeedTailChunk110Before,
        recordUpperSeedTailChunk109State] using h109
    simpa only [recordUpperSeedTailPrefix110] using
      recordUpperSeedTailChunk110Step.certifies prior
  have h111 : recordUpperSeedTailChunk111State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix111 := by
    have prior : recordUpperSeedTailChunk111Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix110 := by
      simpa only [
        recordUpperSeedTailChunk111Before,
        recordUpperSeedTailChunk110State] using h110
    simpa only [recordUpperSeedTailPrefix111] using
      recordUpperSeedTailChunk111Step.certifies prior
  have h112 : recordUpperSeedTailChunk112State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix112 := by
    have prior : recordUpperSeedTailChunk112Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix111 := by
      simpa only [
        recordUpperSeedTailChunk112Before,
        recordUpperSeedTailChunk111State] using h111
    simpa only [recordUpperSeedTailPrefix112] using
      recordUpperSeedTailChunk112Step.certifies prior
  have h113 : recordUpperSeedTailChunk113State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix113 := by
    have prior : recordUpperSeedTailChunk113Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix112 := by
      simpa only [
        recordUpperSeedTailChunk113Before,
        recordUpperSeedTailChunk112State] using h112
    simpa only [recordUpperSeedTailPrefix113] using
      recordUpperSeedTailChunk113Step.certifies prior
  have h114 : recordUpperSeedTailChunk114State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix114 := by
    have prior : recordUpperSeedTailChunk114Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix113 := by
      simpa only [
        recordUpperSeedTailChunk114Before,
        recordUpperSeedTailChunk113State] using h113
    simpa only [recordUpperSeedTailPrefix114] using
      recordUpperSeedTailChunk114Step.certifies prior
  have h115 : recordUpperSeedTailChunk115State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix115 := by
    have prior : recordUpperSeedTailChunk115Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix114 := by
      simpa only [
        recordUpperSeedTailChunk115Before,
        recordUpperSeedTailChunk114State] using h114
    simpa only [recordUpperSeedTailPrefix115] using
      recordUpperSeedTailChunk115Step.certifies prior
  have h116 : recordUpperSeedTailChunk116State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix116 := by
    have prior : recordUpperSeedTailChunk116Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix115 := by
      simpa only [
        recordUpperSeedTailChunk116Before,
        recordUpperSeedTailChunk115State] using h115
    simpa only [recordUpperSeedTailPrefix116] using
      recordUpperSeedTailChunk116Step.certifies prior
  have h117 : recordUpperSeedTailChunk117State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix117 := by
    have prior : recordUpperSeedTailChunk117Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix116 := by
      simpa only [
        recordUpperSeedTailChunk117Before,
        recordUpperSeedTailChunk116State] using h116
    simpa only [recordUpperSeedTailPrefix117] using
      recordUpperSeedTailChunk117Step.certifies prior
  have h118 : recordUpperSeedTailChunk118State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix118 := by
    have prior : recordUpperSeedTailChunk118Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix117 := by
      simpa only [
        recordUpperSeedTailChunk118Before,
        recordUpperSeedTailChunk117State] using h117
    simpa only [recordUpperSeedTailPrefix118] using
      recordUpperSeedTailChunk118Step.certifies prior
  have h119 : recordUpperSeedTailChunk119State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix119 := by
    have prior : recordUpperSeedTailChunk119Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix118 := by
      simpa only [
        recordUpperSeedTailChunk119Before,
        recordUpperSeedTailChunk118State] using h118
    simpa only [recordUpperSeedTailPrefix119] using
      recordUpperSeedTailChunk119Step.certifies prior
  have h120 : recordUpperSeedTailChunk120State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix120 := by
    have prior : recordUpperSeedTailChunk120Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix119 := by
      simpa only [
        recordUpperSeedTailChunk120Before,
        recordUpperSeedTailChunk119State] using h119
    simpa only [recordUpperSeedTailPrefix120] using
      recordUpperSeedTailChunk120Step.certifies prior
  exact h120

end PrimeFactorUnimodality
