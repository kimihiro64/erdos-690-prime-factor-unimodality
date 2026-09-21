import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Assembly.Part03
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part160

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-lower-seed.json` (semantic SHA-256 `3ce105dad06099400dfd2e30c65d47c6e02828915452a8459553c3bb0eb78b73`, excluding elapsed time). Semantic tail assembly group 4. -/

namespace PrimeFactorUnimodality

theorem recordLowerSeedTailGroup04_semantic :
    recordLowerSeedTailChunk160State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix160 := by
  have h121 : recordLowerSeedTailChunk121State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix121 := by
    have prior : recordLowerSeedTailChunk121Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix120 := by
      simpa only [
        recordLowerSeedTailChunk121Before,
        recordLowerSeedTailChunk120State] using recordLowerSeedTailGroup03_semantic
    simpa only [recordLowerSeedTailPrefix121] using
      recordLowerSeedTailChunk121Step.certifies prior
  have h122 : recordLowerSeedTailChunk122State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix122 := by
    have prior : recordLowerSeedTailChunk122Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix121 := by
      simpa only [
        recordLowerSeedTailChunk122Before,
        recordLowerSeedTailChunk121State] using h121
    simpa only [recordLowerSeedTailPrefix122] using
      recordLowerSeedTailChunk122Step.certifies prior
  have h123 : recordLowerSeedTailChunk123State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix123 := by
    have prior : recordLowerSeedTailChunk123Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix122 := by
      simpa only [
        recordLowerSeedTailChunk123Before,
        recordLowerSeedTailChunk122State] using h122
    simpa only [recordLowerSeedTailPrefix123] using
      recordLowerSeedTailChunk123Step.certifies prior
  have h124 : recordLowerSeedTailChunk124State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix124 := by
    have prior : recordLowerSeedTailChunk124Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix123 := by
      simpa only [
        recordLowerSeedTailChunk124Before,
        recordLowerSeedTailChunk123State] using h123
    simpa only [recordLowerSeedTailPrefix124] using
      recordLowerSeedTailChunk124Step.certifies prior
  have h125 : recordLowerSeedTailChunk125State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix125 := by
    have prior : recordLowerSeedTailChunk125Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix124 := by
      simpa only [
        recordLowerSeedTailChunk125Before,
        recordLowerSeedTailChunk124State] using h124
    simpa only [recordLowerSeedTailPrefix125] using
      recordLowerSeedTailChunk125Step.certifies prior
  have h126 : recordLowerSeedTailChunk126State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix126 := by
    have prior : recordLowerSeedTailChunk126Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix125 := by
      simpa only [
        recordLowerSeedTailChunk126Before,
        recordLowerSeedTailChunk125State] using h125
    simpa only [recordLowerSeedTailPrefix126] using
      recordLowerSeedTailChunk126Step.certifies prior
  have h127 : recordLowerSeedTailChunk127State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix127 := by
    have prior : recordLowerSeedTailChunk127Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix126 := by
      simpa only [
        recordLowerSeedTailChunk127Before,
        recordLowerSeedTailChunk126State] using h126
    simpa only [recordLowerSeedTailPrefix127] using
      recordLowerSeedTailChunk127Step.certifies prior
  have h128 : recordLowerSeedTailChunk128State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix128 := by
    have prior : recordLowerSeedTailChunk128Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix127 := by
      simpa only [
        recordLowerSeedTailChunk128Before,
        recordLowerSeedTailChunk127State] using h127
    simpa only [recordLowerSeedTailPrefix128] using
      recordLowerSeedTailChunk128Step.certifies prior
  have h129 : recordLowerSeedTailChunk129State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix129 := by
    have prior : recordLowerSeedTailChunk129Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix128 := by
      simpa only [
        recordLowerSeedTailChunk129Before,
        recordLowerSeedTailChunk128State] using h128
    simpa only [recordLowerSeedTailPrefix129] using
      recordLowerSeedTailChunk129Step.certifies prior
  have h130 : recordLowerSeedTailChunk130State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix130 := by
    have prior : recordLowerSeedTailChunk130Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix129 := by
      simpa only [
        recordLowerSeedTailChunk130Before,
        recordLowerSeedTailChunk129State] using h129
    simpa only [recordLowerSeedTailPrefix130] using
      recordLowerSeedTailChunk130Step.certifies prior
  have h131 : recordLowerSeedTailChunk131State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix131 := by
    have prior : recordLowerSeedTailChunk131Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix130 := by
      simpa only [
        recordLowerSeedTailChunk131Before,
        recordLowerSeedTailChunk130State] using h130
    simpa only [recordLowerSeedTailPrefix131] using
      recordLowerSeedTailChunk131Step.certifies prior
  have h132 : recordLowerSeedTailChunk132State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix132 := by
    have prior : recordLowerSeedTailChunk132Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix131 := by
      simpa only [
        recordLowerSeedTailChunk132Before,
        recordLowerSeedTailChunk131State] using h131
    simpa only [recordLowerSeedTailPrefix132] using
      recordLowerSeedTailChunk132Step.certifies prior
  have h133 : recordLowerSeedTailChunk133State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix133 := by
    have prior : recordLowerSeedTailChunk133Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix132 := by
      simpa only [
        recordLowerSeedTailChunk133Before,
        recordLowerSeedTailChunk132State] using h132
    simpa only [recordLowerSeedTailPrefix133] using
      recordLowerSeedTailChunk133Step.certifies prior
  have h134 : recordLowerSeedTailChunk134State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix134 := by
    have prior : recordLowerSeedTailChunk134Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix133 := by
      simpa only [
        recordLowerSeedTailChunk134Before,
        recordLowerSeedTailChunk133State] using h133
    simpa only [recordLowerSeedTailPrefix134] using
      recordLowerSeedTailChunk134Step.certifies prior
  have h135 : recordLowerSeedTailChunk135State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix135 := by
    have prior : recordLowerSeedTailChunk135Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix134 := by
      simpa only [
        recordLowerSeedTailChunk135Before,
        recordLowerSeedTailChunk134State] using h134
    simpa only [recordLowerSeedTailPrefix135] using
      recordLowerSeedTailChunk135Step.certifies prior
  have h136 : recordLowerSeedTailChunk136State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix136 := by
    have prior : recordLowerSeedTailChunk136Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix135 := by
      simpa only [
        recordLowerSeedTailChunk136Before,
        recordLowerSeedTailChunk135State] using h135
    simpa only [recordLowerSeedTailPrefix136] using
      recordLowerSeedTailChunk136Step.certifies prior
  have h137 : recordLowerSeedTailChunk137State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix137 := by
    have prior : recordLowerSeedTailChunk137Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix136 := by
      simpa only [
        recordLowerSeedTailChunk137Before,
        recordLowerSeedTailChunk136State] using h136
    simpa only [recordLowerSeedTailPrefix137] using
      recordLowerSeedTailChunk137Step.certifies prior
  have h138 : recordLowerSeedTailChunk138State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix138 := by
    have prior : recordLowerSeedTailChunk138Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix137 := by
      simpa only [
        recordLowerSeedTailChunk138Before,
        recordLowerSeedTailChunk137State] using h137
    simpa only [recordLowerSeedTailPrefix138] using
      recordLowerSeedTailChunk138Step.certifies prior
  have h139 : recordLowerSeedTailChunk139State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix139 := by
    have prior : recordLowerSeedTailChunk139Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix138 := by
      simpa only [
        recordLowerSeedTailChunk139Before,
        recordLowerSeedTailChunk138State] using h138
    simpa only [recordLowerSeedTailPrefix139] using
      recordLowerSeedTailChunk139Step.certifies prior
  have h140 : recordLowerSeedTailChunk140State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix140 := by
    have prior : recordLowerSeedTailChunk140Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix139 := by
      simpa only [
        recordLowerSeedTailChunk140Before,
        recordLowerSeedTailChunk139State] using h139
    simpa only [recordLowerSeedTailPrefix140] using
      recordLowerSeedTailChunk140Step.certifies prior
  have h141 : recordLowerSeedTailChunk141State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix141 := by
    have prior : recordLowerSeedTailChunk141Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix140 := by
      simpa only [
        recordLowerSeedTailChunk141Before,
        recordLowerSeedTailChunk140State] using h140
    simpa only [recordLowerSeedTailPrefix141] using
      recordLowerSeedTailChunk141Step.certifies prior
  have h142 : recordLowerSeedTailChunk142State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix142 := by
    have prior : recordLowerSeedTailChunk142Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix141 := by
      simpa only [
        recordLowerSeedTailChunk142Before,
        recordLowerSeedTailChunk141State] using h141
    simpa only [recordLowerSeedTailPrefix142] using
      recordLowerSeedTailChunk142Step.certifies prior
  have h143 : recordLowerSeedTailChunk143State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix143 := by
    have prior : recordLowerSeedTailChunk143Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix142 := by
      simpa only [
        recordLowerSeedTailChunk143Before,
        recordLowerSeedTailChunk142State] using h142
    simpa only [recordLowerSeedTailPrefix143] using
      recordLowerSeedTailChunk143Step.certifies prior
  have h144 : recordLowerSeedTailChunk144State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix144 := by
    have prior : recordLowerSeedTailChunk144Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix143 := by
      simpa only [
        recordLowerSeedTailChunk144Before,
        recordLowerSeedTailChunk143State] using h143
    simpa only [recordLowerSeedTailPrefix144] using
      recordLowerSeedTailChunk144Step.certifies prior
  have h145 : recordLowerSeedTailChunk145State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix145 := by
    have prior : recordLowerSeedTailChunk145Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix144 := by
      simpa only [
        recordLowerSeedTailChunk145Before,
        recordLowerSeedTailChunk144State] using h144
    simpa only [recordLowerSeedTailPrefix145] using
      recordLowerSeedTailChunk145Step.certifies prior
  have h146 : recordLowerSeedTailChunk146State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix146 := by
    have prior : recordLowerSeedTailChunk146Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix145 := by
      simpa only [
        recordLowerSeedTailChunk146Before,
        recordLowerSeedTailChunk145State] using h145
    simpa only [recordLowerSeedTailPrefix146] using
      recordLowerSeedTailChunk146Step.certifies prior
  have h147 : recordLowerSeedTailChunk147State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix147 := by
    have prior : recordLowerSeedTailChunk147Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix146 := by
      simpa only [
        recordLowerSeedTailChunk147Before,
        recordLowerSeedTailChunk146State] using h146
    simpa only [recordLowerSeedTailPrefix147] using
      recordLowerSeedTailChunk147Step.certifies prior
  have h148 : recordLowerSeedTailChunk148State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix148 := by
    have prior : recordLowerSeedTailChunk148Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix147 := by
      simpa only [
        recordLowerSeedTailChunk148Before,
        recordLowerSeedTailChunk147State] using h147
    simpa only [recordLowerSeedTailPrefix148] using
      recordLowerSeedTailChunk148Step.certifies prior
  have h149 : recordLowerSeedTailChunk149State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix149 := by
    have prior : recordLowerSeedTailChunk149Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix148 := by
      simpa only [
        recordLowerSeedTailChunk149Before,
        recordLowerSeedTailChunk148State] using h148
    simpa only [recordLowerSeedTailPrefix149] using
      recordLowerSeedTailChunk149Step.certifies prior
  have h150 : recordLowerSeedTailChunk150State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix150 := by
    have prior : recordLowerSeedTailChunk150Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix149 := by
      simpa only [
        recordLowerSeedTailChunk150Before,
        recordLowerSeedTailChunk149State] using h149
    simpa only [recordLowerSeedTailPrefix150] using
      recordLowerSeedTailChunk150Step.certifies prior
  have h151 : recordLowerSeedTailChunk151State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix151 := by
    have prior : recordLowerSeedTailChunk151Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix150 := by
      simpa only [
        recordLowerSeedTailChunk151Before,
        recordLowerSeedTailChunk150State] using h150
    simpa only [recordLowerSeedTailPrefix151] using
      recordLowerSeedTailChunk151Step.certifies prior
  have h152 : recordLowerSeedTailChunk152State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix152 := by
    have prior : recordLowerSeedTailChunk152Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix151 := by
      simpa only [
        recordLowerSeedTailChunk152Before,
        recordLowerSeedTailChunk151State] using h151
    simpa only [recordLowerSeedTailPrefix152] using
      recordLowerSeedTailChunk152Step.certifies prior
  have h153 : recordLowerSeedTailChunk153State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix153 := by
    have prior : recordLowerSeedTailChunk153Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix152 := by
      simpa only [
        recordLowerSeedTailChunk153Before,
        recordLowerSeedTailChunk152State] using h152
    simpa only [recordLowerSeedTailPrefix153] using
      recordLowerSeedTailChunk153Step.certifies prior
  have h154 : recordLowerSeedTailChunk154State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix154 := by
    have prior : recordLowerSeedTailChunk154Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix153 := by
      simpa only [
        recordLowerSeedTailChunk154Before,
        recordLowerSeedTailChunk153State] using h153
    simpa only [recordLowerSeedTailPrefix154] using
      recordLowerSeedTailChunk154Step.certifies prior
  have h155 : recordLowerSeedTailChunk155State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix155 := by
    have prior : recordLowerSeedTailChunk155Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix154 := by
      simpa only [
        recordLowerSeedTailChunk155Before,
        recordLowerSeedTailChunk154State] using h154
    simpa only [recordLowerSeedTailPrefix155] using
      recordLowerSeedTailChunk155Step.certifies prior
  have h156 : recordLowerSeedTailChunk156State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix156 := by
    have prior : recordLowerSeedTailChunk156Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix155 := by
      simpa only [
        recordLowerSeedTailChunk156Before,
        recordLowerSeedTailChunk155State] using h155
    simpa only [recordLowerSeedTailPrefix156] using
      recordLowerSeedTailChunk156Step.certifies prior
  have h157 : recordLowerSeedTailChunk157State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix157 := by
    have prior : recordLowerSeedTailChunk157Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix156 := by
      simpa only [
        recordLowerSeedTailChunk157Before,
        recordLowerSeedTailChunk156State] using h156
    simpa only [recordLowerSeedTailPrefix157] using
      recordLowerSeedTailChunk157Step.certifies prior
  have h158 : recordLowerSeedTailChunk158State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix158 := by
    have prior : recordLowerSeedTailChunk158Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix157 := by
      simpa only [
        recordLowerSeedTailChunk158Before,
        recordLowerSeedTailChunk157State] using h157
    simpa only [recordLowerSeedTailPrefix158] using
      recordLowerSeedTailChunk158Step.certifies prior
  have h159 : recordLowerSeedTailChunk159State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix159 := by
    have prior : recordLowerSeedTailChunk159Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix158 := by
      simpa only [
        recordLowerSeedTailChunk159Before,
        recordLowerSeedTailChunk158State] using h158
    simpa only [recordLowerSeedTailPrefix159] using
      recordLowerSeedTailChunk159Step.certifies prior
  have h160 : recordLowerSeedTailChunk160State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix160 := by
    have prior : recordLowerSeedTailChunk160Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix159 := by
      simpa only [
        recordLowerSeedTailChunk160Before,
        recordLowerSeedTailChunk159State] using h159
    simpa only [recordLowerSeedTailPrefix160] using
      recordLowerSeedTailChunk160Step.certifies prior
  exact h160

end PrimeFactorUnimodality
