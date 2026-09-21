import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Assembly.Part02
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part120

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-lower-seed.json` (semantic SHA-256 `3ce105dad06099400dfd2e30c65d47c6e02828915452a8459553c3bb0eb78b73`, excluding elapsed time). Semantic tail assembly group 3. -/

namespace PrimeFactorUnimodality

theorem recordLowerSeedTailGroup03_semantic :
    recordLowerSeedTailChunk120State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix120 := by
  have h081 : recordLowerSeedTailChunk081State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix081 := by
    have prior : recordLowerSeedTailChunk081Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix080 := by
      simpa only [
        recordLowerSeedTailChunk081Before,
        recordLowerSeedTailChunk080State] using recordLowerSeedTailGroup02_semantic
    simpa only [recordLowerSeedTailPrefix081] using
      recordLowerSeedTailChunk081Step.certifies prior
  have h082 : recordLowerSeedTailChunk082State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix082 := by
    have prior : recordLowerSeedTailChunk082Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix081 := by
      simpa only [
        recordLowerSeedTailChunk082Before,
        recordLowerSeedTailChunk081State] using h081
    simpa only [recordLowerSeedTailPrefix082] using
      recordLowerSeedTailChunk082Step.certifies prior
  have h083 : recordLowerSeedTailChunk083State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix083 := by
    have prior : recordLowerSeedTailChunk083Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix082 := by
      simpa only [
        recordLowerSeedTailChunk083Before,
        recordLowerSeedTailChunk082State] using h082
    simpa only [recordLowerSeedTailPrefix083] using
      recordLowerSeedTailChunk083Step.certifies prior
  have h084 : recordLowerSeedTailChunk084State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix084 := by
    have prior : recordLowerSeedTailChunk084Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix083 := by
      simpa only [
        recordLowerSeedTailChunk084Before,
        recordLowerSeedTailChunk083State] using h083
    simpa only [recordLowerSeedTailPrefix084] using
      recordLowerSeedTailChunk084Step.certifies prior
  have h085 : recordLowerSeedTailChunk085State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix085 := by
    have prior : recordLowerSeedTailChunk085Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix084 := by
      simpa only [
        recordLowerSeedTailChunk085Before,
        recordLowerSeedTailChunk084State] using h084
    simpa only [recordLowerSeedTailPrefix085] using
      recordLowerSeedTailChunk085Step.certifies prior
  have h086 : recordLowerSeedTailChunk086State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix086 := by
    have prior : recordLowerSeedTailChunk086Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix085 := by
      simpa only [
        recordLowerSeedTailChunk086Before,
        recordLowerSeedTailChunk085State] using h085
    simpa only [recordLowerSeedTailPrefix086] using
      recordLowerSeedTailChunk086Step.certifies prior
  have h087 : recordLowerSeedTailChunk087State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix087 := by
    have prior : recordLowerSeedTailChunk087Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix086 := by
      simpa only [
        recordLowerSeedTailChunk087Before,
        recordLowerSeedTailChunk086State] using h086
    simpa only [recordLowerSeedTailPrefix087] using
      recordLowerSeedTailChunk087Step.certifies prior
  have h088 : recordLowerSeedTailChunk088State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix088 := by
    have prior : recordLowerSeedTailChunk088Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix087 := by
      simpa only [
        recordLowerSeedTailChunk088Before,
        recordLowerSeedTailChunk087State] using h087
    simpa only [recordLowerSeedTailPrefix088] using
      recordLowerSeedTailChunk088Step.certifies prior
  have h089 : recordLowerSeedTailChunk089State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix089 := by
    have prior : recordLowerSeedTailChunk089Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix088 := by
      simpa only [
        recordLowerSeedTailChunk089Before,
        recordLowerSeedTailChunk088State] using h088
    simpa only [recordLowerSeedTailPrefix089] using
      recordLowerSeedTailChunk089Step.certifies prior
  have h090 : recordLowerSeedTailChunk090State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix090 := by
    have prior : recordLowerSeedTailChunk090Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix089 := by
      simpa only [
        recordLowerSeedTailChunk090Before,
        recordLowerSeedTailChunk089State] using h089
    simpa only [recordLowerSeedTailPrefix090] using
      recordLowerSeedTailChunk090Step.certifies prior
  have h091 : recordLowerSeedTailChunk091State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix091 := by
    have prior : recordLowerSeedTailChunk091Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix090 := by
      simpa only [
        recordLowerSeedTailChunk091Before,
        recordLowerSeedTailChunk090State] using h090
    simpa only [recordLowerSeedTailPrefix091] using
      recordLowerSeedTailChunk091Step.certifies prior
  have h092 : recordLowerSeedTailChunk092State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix092 := by
    have prior : recordLowerSeedTailChunk092Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix091 := by
      simpa only [
        recordLowerSeedTailChunk092Before,
        recordLowerSeedTailChunk091State] using h091
    simpa only [recordLowerSeedTailPrefix092] using
      recordLowerSeedTailChunk092Step.certifies prior
  have h093 : recordLowerSeedTailChunk093State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix093 := by
    have prior : recordLowerSeedTailChunk093Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix092 := by
      simpa only [
        recordLowerSeedTailChunk093Before,
        recordLowerSeedTailChunk092State] using h092
    simpa only [recordLowerSeedTailPrefix093] using
      recordLowerSeedTailChunk093Step.certifies prior
  have h094 : recordLowerSeedTailChunk094State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix094 := by
    have prior : recordLowerSeedTailChunk094Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix093 := by
      simpa only [
        recordLowerSeedTailChunk094Before,
        recordLowerSeedTailChunk093State] using h093
    simpa only [recordLowerSeedTailPrefix094] using
      recordLowerSeedTailChunk094Step.certifies prior
  have h095 : recordLowerSeedTailChunk095State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix095 := by
    have prior : recordLowerSeedTailChunk095Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix094 := by
      simpa only [
        recordLowerSeedTailChunk095Before,
        recordLowerSeedTailChunk094State] using h094
    simpa only [recordLowerSeedTailPrefix095] using
      recordLowerSeedTailChunk095Step.certifies prior
  have h096 : recordLowerSeedTailChunk096State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix096 := by
    have prior : recordLowerSeedTailChunk096Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix095 := by
      simpa only [
        recordLowerSeedTailChunk096Before,
        recordLowerSeedTailChunk095State] using h095
    simpa only [recordLowerSeedTailPrefix096] using
      recordLowerSeedTailChunk096Step.certifies prior
  have h097 : recordLowerSeedTailChunk097State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix097 := by
    have prior : recordLowerSeedTailChunk097Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix096 := by
      simpa only [
        recordLowerSeedTailChunk097Before,
        recordLowerSeedTailChunk096State] using h096
    simpa only [recordLowerSeedTailPrefix097] using
      recordLowerSeedTailChunk097Step.certifies prior
  have h098 : recordLowerSeedTailChunk098State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix098 := by
    have prior : recordLowerSeedTailChunk098Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix097 := by
      simpa only [
        recordLowerSeedTailChunk098Before,
        recordLowerSeedTailChunk097State] using h097
    simpa only [recordLowerSeedTailPrefix098] using
      recordLowerSeedTailChunk098Step.certifies prior
  have h099 : recordLowerSeedTailChunk099State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix099 := by
    have prior : recordLowerSeedTailChunk099Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix098 := by
      simpa only [
        recordLowerSeedTailChunk099Before,
        recordLowerSeedTailChunk098State] using h098
    simpa only [recordLowerSeedTailPrefix099] using
      recordLowerSeedTailChunk099Step.certifies prior
  have h100 : recordLowerSeedTailChunk100State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix100 := by
    have prior : recordLowerSeedTailChunk100Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix099 := by
      simpa only [
        recordLowerSeedTailChunk100Before,
        recordLowerSeedTailChunk099State] using h099
    simpa only [recordLowerSeedTailPrefix100] using
      recordLowerSeedTailChunk100Step.certifies prior
  have h101 : recordLowerSeedTailChunk101State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix101 := by
    have prior : recordLowerSeedTailChunk101Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix100 := by
      simpa only [
        recordLowerSeedTailChunk101Before,
        recordLowerSeedTailChunk100State] using h100
    simpa only [recordLowerSeedTailPrefix101] using
      recordLowerSeedTailChunk101Step.certifies prior
  have h102 : recordLowerSeedTailChunk102State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix102 := by
    have prior : recordLowerSeedTailChunk102Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix101 := by
      simpa only [
        recordLowerSeedTailChunk102Before,
        recordLowerSeedTailChunk101State] using h101
    simpa only [recordLowerSeedTailPrefix102] using
      recordLowerSeedTailChunk102Step.certifies prior
  have h103 : recordLowerSeedTailChunk103State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix103 := by
    have prior : recordLowerSeedTailChunk103Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix102 := by
      simpa only [
        recordLowerSeedTailChunk103Before,
        recordLowerSeedTailChunk102State] using h102
    simpa only [recordLowerSeedTailPrefix103] using
      recordLowerSeedTailChunk103Step.certifies prior
  have h104 : recordLowerSeedTailChunk104State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix104 := by
    have prior : recordLowerSeedTailChunk104Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix103 := by
      simpa only [
        recordLowerSeedTailChunk104Before,
        recordLowerSeedTailChunk103State] using h103
    simpa only [recordLowerSeedTailPrefix104] using
      recordLowerSeedTailChunk104Step.certifies prior
  have h105 : recordLowerSeedTailChunk105State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix105 := by
    have prior : recordLowerSeedTailChunk105Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix104 := by
      simpa only [
        recordLowerSeedTailChunk105Before,
        recordLowerSeedTailChunk104State] using h104
    simpa only [recordLowerSeedTailPrefix105] using
      recordLowerSeedTailChunk105Step.certifies prior
  have h106 : recordLowerSeedTailChunk106State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix106 := by
    have prior : recordLowerSeedTailChunk106Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix105 := by
      simpa only [
        recordLowerSeedTailChunk106Before,
        recordLowerSeedTailChunk105State] using h105
    simpa only [recordLowerSeedTailPrefix106] using
      recordLowerSeedTailChunk106Step.certifies prior
  have h107 : recordLowerSeedTailChunk107State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix107 := by
    have prior : recordLowerSeedTailChunk107Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix106 := by
      simpa only [
        recordLowerSeedTailChunk107Before,
        recordLowerSeedTailChunk106State] using h106
    simpa only [recordLowerSeedTailPrefix107] using
      recordLowerSeedTailChunk107Step.certifies prior
  have h108 : recordLowerSeedTailChunk108State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix108 := by
    have prior : recordLowerSeedTailChunk108Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix107 := by
      simpa only [
        recordLowerSeedTailChunk108Before,
        recordLowerSeedTailChunk107State] using h107
    simpa only [recordLowerSeedTailPrefix108] using
      recordLowerSeedTailChunk108Step.certifies prior
  have h109 : recordLowerSeedTailChunk109State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix109 := by
    have prior : recordLowerSeedTailChunk109Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix108 := by
      simpa only [
        recordLowerSeedTailChunk109Before,
        recordLowerSeedTailChunk108State] using h108
    simpa only [recordLowerSeedTailPrefix109] using
      recordLowerSeedTailChunk109Step.certifies prior
  have h110 : recordLowerSeedTailChunk110State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix110 := by
    have prior : recordLowerSeedTailChunk110Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix109 := by
      simpa only [
        recordLowerSeedTailChunk110Before,
        recordLowerSeedTailChunk109State] using h109
    simpa only [recordLowerSeedTailPrefix110] using
      recordLowerSeedTailChunk110Step.certifies prior
  have h111 : recordLowerSeedTailChunk111State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix111 := by
    have prior : recordLowerSeedTailChunk111Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix110 := by
      simpa only [
        recordLowerSeedTailChunk111Before,
        recordLowerSeedTailChunk110State] using h110
    simpa only [recordLowerSeedTailPrefix111] using
      recordLowerSeedTailChunk111Step.certifies prior
  have h112 : recordLowerSeedTailChunk112State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix112 := by
    have prior : recordLowerSeedTailChunk112Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix111 := by
      simpa only [
        recordLowerSeedTailChunk112Before,
        recordLowerSeedTailChunk111State] using h111
    simpa only [recordLowerSeedTailPrefix112] using
      recordLowerSeedTailChunk112Step.certifies prior
  have h113 : recordLowerSeedTailChunk113State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix113 := by
    have prior : recordLowerSeedTailChunk113Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix112 := by
      simpa only [
        recordLowerSeedTailChunk113Before,
        recordLowerSeedTailChunk112State] using h112
    simpa only [recordLowerSeedTailPrefix113] using
      recordLowerSeedTailChunk113Step.certifies prior
  have h114 : recordLowerSeedTailChunk114State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix114 := by
    have prior : recordLowerSeedTailChunk114Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix113 := by
      simpa only [
        recordLowerSeedTailChunk114Before,
        recordLowerSeedTailChunk113State] using h113
    simpa only [recordLowerSeedTailPrefix114] using
      recordLowerSeedTailChunk114Step.certifies prior
  have h115 : recordLowerSeedTailChunk115State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix115 := by
    have prior : recordLowerSeedTailChunk115Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix114 := by
      simpa only [
        recordLowerSeedTailChunk115Before,
        recordLowerSeedTailChunk114State] using h114
    simpa only [recordLowerSeedTailPrefix115] using
      recordLowerSeedTailChunk115Step.certifies prior
  have h116 : recordLowerSeedTailChunk116State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix116 := by
    have prior : recordLowerSeedTailChunk116Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix115 := by
      simpa only [
        recordLowerSeedTailChunk116Before,
        recordLowerSeedTailChunk115State] using h115
    simpa only [recordLowerSeedTailPrefix116] using
      recordLowerSeedTailChunk116Step.certifies prior
  have h117 : recordLowerSeedTailChunk117State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix117 := by
    have prior : recordLowerSeedTailChunk117Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix116 := by
      simpa only [
        recordLowerSeedTailChunk117Before,
        recordLowerSeedTailChunk116State] using h116
    simpa only [recordLowerSeedTailPrefix117] using
      recordLowerSeedTailChunk117Step.certifies prior
  have h118 : recordLowerSeedTailChunk118State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix118 := by
    have prior : recordLowerSeedTailChunk118Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix117 := by
      simpa only [
        recordLowerSeedTailChunk118Before,
        recordLowerSeedTailChunk117State] using h117
    simpa only [recordLowerSeedTailPrefix118] using
      recordLowerSeedTailChunk118Step.certifies prior
  have h119 : recordLowerSeedTailChunk119State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix119 := by
    have prior : recordLowerSeedTailChunk119Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix118 := by
      simpa only [
        recordLowerSeedTailChunk119Before,
        recordLowerSeedTailChunk118State] using h118
    simpa only [recordLowerSeedTailPrefix119] using
      recordLowerSeedTailChunk119Step.certifies prior
  have h120 : recordLowerSeedTailChunk120State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix120 := by
    have prior : recordLowerSeedTailChunk120Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix119 := by
      simpa only [
        recordLowerSeedTailChunk120Before,
        recordLowerSeedTailChunk119State] using h119
    simpa only [recordLowerSeedTailPrefix120] using
      recordLowerSeedTailChunk120Step.certifies prior
  exact h120

end PrimeFactorUnimodality
