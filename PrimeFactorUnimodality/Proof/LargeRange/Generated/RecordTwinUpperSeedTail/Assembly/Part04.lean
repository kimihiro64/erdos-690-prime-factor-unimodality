import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Assembly.Part03
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part121
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part122
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part123
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part124
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part125
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part126
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part127
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part128
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part129
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part130
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part131
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part132
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part133
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part134
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part135
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part136
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part137
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part138
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part139
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part140
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part141
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part142
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part143
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part144
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part145
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part146
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part147
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part148
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part149
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part150
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part151
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part152
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part153
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part154
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part155
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part156
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part157
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part158
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part159
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part160

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-upper-seed-base11.json` (semantic SHA-256 `493791f7b41de1500c4b830f254f9f92fd9c5d50d639b62aa2b46ca48591321f`, excluding elapsed time). Semantic tail assembly group 4. -/

namespace PrimeFactorUnimodality

theorem recordUpperSeedTailGroup04_semantic :
    recordUpperSeedTailChunk160State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix160 := by
  have h121 : recordUpperSeedTailChunk121State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix121 := by
    have prior : recordUpperSeedTailChunk121Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix120 := by
      simpa only [
        recordUpperSeedTailChunk121Before,
        recordUpperSeedTailChunk120State] using recordUpperSeedTailGroup03_semantic
    simpa only [recordUpperSeedTailPrefix121] using
      recordUpperSeedTailChunk121Step.certifies prior
  have h122 : recordUpperSeedTailChunk122State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix122 := by
    have prior : recordUpperSeedTailChunk122Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix121 := by
      simpa only [
        recordUpperSeedTailChunk122Before,
        recordUpperSeedTailChunk121State] using h121
    simpa only [recordUpperSeedTailPrefix122] using
      recordUpperSeedTailChunk122Step.certifies prior
  have h123 : recordUpperSeedTailChunk123State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix123 := by
    have prior : recordUpperSeedTailChunk123Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix122 := by
      simpa only [
        recordUpperSeedTailChunk123Before,
        recordUpperSeedTailChunk122State] using h122
    simpa only [recordUpperSeedTailPrefix123] using
      recordUpperSeedTailChunk123Step.certifies prior
  have h124 : recordUpperSeedTailChunk124State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix124 := by
    have prior : recordUpperSeedTailChunk124Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix123 := by
      simpa only [
        recordUpperSeedTailChunk124Before,
        recordUpperSeedTailChunk123State] using h123
    simpa only [recordUpperSeedTailPrefix124] using
      recordUpperSeedTailChunk124Step.certifies prior
  have h125 : recordUpperSeedTailChunk125State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix125 := by
    have prior : recordUpperSeedTailChunk125Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix124 := by
      simpa only [
        recordUpperSeedTailChunk125Before,
        recordUpperSeedTailChunk124State] using h124
    simpa only [recordUpperSeedTailPrefix125] using
      recordUpperSeedTailChunk125Step.certifies prior
  have h126 : recordUpperSeedTailChunk126State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix126 := by
    have prior : recordUpperSeedTailChunk126Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix125 := by
      simpa only [
        recordUpperSeedTailChunk126Before,
        recordUpperSeedTailChunk125State] using h125
    simpa only [recordUpperSeedTailPrefix126] using
      recordUpperSeedTailChunk126Step.certifies prior
  have h127 : recordUpperSeedTailChunk127State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix127 := by
    have prior : recordUpperSeedTailChunk127Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix126 := by
      simpa only [
        recordUpperSeedTailChunk127Before,
        recordUpperSeedTailChunk126State] using h126
    simpa only [recordUpperSeedTailPrefix127] using
      recordUpperSeedTailChunk127Step.certifies prior
  have h128 : recordUpperSeedTailChunk128State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix128 := by
    have prior : recordUpperSeedTailChunk128Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix127 := by
      simpa only [
        recordUpperSeedTailChunk128Before,
        recordUpperSeedTailChunk127State] using h127
    simpa only [recordUpperSeedTailPrefix128] using
      recordUpperSeedTailChunk128Step.certifies prior
  have h129 : recordUpperSeedTailChunk129State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix129 := by
    have prior : recordUpperSeedTailChunk129Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix128 := by
      simpa only [
        recordUpperSeedTailChunk129Before,
        recordUpperSeedTailChunk128State] using h128
    simpa only [recordUpperSeedTailPrefix129] using
      recordUpperSeedTailChunk129Step.certifies prior
  have h130 : recordUpperSeedTailChunk130State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix130 := by
    have prior : recordUpperSeedTailChunk130Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix129 := by
      simpa only [
        recordUpperSeedTailChunk130Before,
        recordUpperSeedTailChunk129State] using h129
    simpa only [recordUpperSeedTailPrefix130] using
      recordUpperSeedTailChunk130Step.certifies prior
  have h131 : recordUpperSeedTailChunk131State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix131 := by
    have prior : recordUpperSeedTailChunk131Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix130 := by
      simpa only [
        recordUpperSeedTailChunk131Before,
        recordUpperSeedTailChunk130State] using h130
    simpa only [recordUpperSeedTailPrefix131] using
      recordUpperSeedTailChunk131Step.certifies prior
  have h132 : recordUpperSeedTailChunk132State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix132 := by
    have prior : recordUpperSeedTailChunk132Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix131 := by
      simpa only [
        recordUpperSeedTailChunk132Before,
        recordUpperSeedTailChunk131State] using h131
    simpa only [recordUpperSeedTailPrefix132] using
      recordUpperSeedTailChunk132Step.certifies prior
  have h133 : recordUpperSeedTailChunk133State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix133 := by
    have prior : recordUpperSeedTailChunk133Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix132 := by
      simpa only [
        recordUpperSeedTailChunk133Before,
        recordUpperSeedTailChunk132State] using h132
    simpa only [recordUpperSeedTailPrefix133] using
      recordUpperSeedTailChunk133Step.certifies prior
  have h134 : recordUpperSeedTailChunk134State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix134 := by
    have prior : recordUpperSeedTailChunk134Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix133 := by
      simpa only [
        recordUpperSeedTailChunk134Before,
        recordUpperSeedTailChunk133State] using h133
    simpa only [recordUpperSeedTailPrefix134] using
      recordUpperSeedTailChunk134Step.certifies prior
  have h135 : recordUpperSeedTailChunk135State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix135 := by
    have prior : recordUpperSeedTailChunk135Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix134 := by
      simpa only [
        recordUpperSeedTailChunk135Before,
        recordUpperSeedTailChunk134State] using h134
    simpa only [recordUpperSeedTailPrefix135] using
      recordUpperSeedTailChunk135Step.certifies prior
  have h136 : recordUpperSeedTailChunk136State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix136 := by
    have prior : recordUpperSeedTailChunk136Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix135 := by
      simpa only [
        recordUpperSeedTailChunk136Before,
        recordUpperSeedTailChunk135State] using h135
    simpa only [recordUpperSeedTailPrefix136] using
      recordUpperSeedTailChunk136Step.certifies prior
  have h137 : recordUpperSeedTailChunk137State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix137 := by
    have prior : recordUpperSeedTailChunk137Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix136 := by
      simpa only [
        recordUpperSeedTailChunk137Before,
        recordUpperSeedTailChunk136State] using h136
    simpa only [recordUpperSeedTailPrefix137] using
      recordUpperSeedTailChunk137Step.certifies prior
  have h138 : recordUpperSeedTailChunk138State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix138 := by
    have prior : recordUpperSeedTailChunk138Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix137 := by
      simpa only [
        recordUpperSeedTailChunk138Before,
        recordUpperSeedTailChunk137State] using h137
    simpa only [recordUpperSeedTailPrefix138] using
      recordUpperSeedTailChunk138Step.certifies prior
  have h139 : recordUpperSeedTailChunk139State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix139 := by
    have prior : recordUpperSeedTailChunk139Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix138 := by
      simpa only [
        recordUpperSeedTailChunk139Before,
        recordUpperSeedTailChunk138State] using h138
    simpa only [recordUpperSeedTailPrefix139] using
      recordUpperSeedTailChunk139Step.certifies prior
  have h140 : recordUpperSeedTailChunk140State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix140 := by
    have prior : recordUpperSeedTailChunk140Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix139 := by
      simpa only [
        recordUpperSeedTailChunk140Before,
        recordUpperSeedTailChunk139State] using h139
    simpa only [recordUpperSeedTailPrefix140] using
      recordUpperSeedTailChunk140Step.certifies prior
  have h141 : recordUpperSeedTailChunk141State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix141 := by
    have prior : recordUpperSeedTailChunk141Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix140 := by
      simpa only [
        recordUpperSeedTailChunk141Before,
        recordUpperSeedTailChunk140State] using h140
    simpa only [recordUpperSeedTailPrefix141] using
      recordUpperSeedTailChunk141Step.certifies prior
  have h142 : recordUpperSeedTailChunk142State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix142 := by
    have prior : recordUpperSeedTailChunk142Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix141 := by
      simpa only [
        recordUpperSeedTailChunk142Before,
        recordUpperSeedTailChunk141State] using h141
    simpa only [recordUpperSeedTailPrefix142] using
      recordUpperSeedTailChunk142Step.certifies prior
  have h143 : recordUpperSeedTailChunk143State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix143 := by
    have prior : recordUpperSeedTailChunk143Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix142 := by
      simpa only [
        recordUpperSeedTailChunk143Before,
        recordUpperSeedTailChunk142State] using h142
    simpa only [recordUpperSeedTailPrefix143] using
      recordUpperSeedTailChunk143Step.certifies prior
  have h144 : recordUpperSeedTailChunk144State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix144 := by
    have prior : recordUpperSeedTailChunk144Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix143 := by
      simpa only [
        recordUpperSeedTailChunk144Before,
        recordUpperSeedTailChunk143State] using h143
    simpa only [recordUpperSeedTailPrefix144] using
      recordUpperSeedTailChunk144Step.certifies prior
  have h145 : recordUpperSeedTailChunk145State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix145 := by
    have prior : recordUpperSeedTailChunk145Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix144 := by
      simpa only [
        recordUpperSeedTailChunk145Before,
        recordUpperSeedTailChunk144State] using h144
    simpa only [recordUpperSeedTailPrefix145] using
      recordUpperSeedTailChunk145Step.certifies prior
  have h146 : recordUpperSeedTailChunk146State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix146 := by
    have prior : recordUpperSeedTailChunk146Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix145 := by
      simpa only [
        recordUpperSeedTailChunk146Before,
        recordUpperSeedTailChunk145State] using h145
    simpa only [recordUpperSeedTailPrefix146] using
      recordUpperSeedTailChunk146Step.certifies prior
  have h147 : recordUpperSeedTailChunk147State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix147 := by
    have prior : recordUpperSeedTailChunk147Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix146 := by
      simpa only [
        recordUpperSeedTailChunk147Before,
        recordUpperSeedTailChunk146State] using h146
    simpa only [recordUpperSeedTailPrefix147] using
      recordUpperSeedTailChunk147Step.certifies prior
  have h148 : recordUpperSeedTailChunk148State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix148 := by
    have prior : recordUpperSeedTailChunk148Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix147 := by
      simpa only [
        recordUpperSeedTailChunk148Before,
        recordUpperSeedTailChunk147State] using h147
    simpa only [recordUpperSeedTailPrefix148] using
      recordUpperSeedTailChunk148Step.certifies prior
  have h149 : recordUpperSeedTailChunk149State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix149 := by
    have prior : recordUpperSeedTailChunk149Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix148 := by
      simpa only [
        recordUpperSeedTailChunk149Before,
        recordUpperSeedTailChunk148State] using h148
    simpa only [recordUpperSeedTailPrefix149] using
      recordUpperSeedTailChunk149Step.certifies prior
  have h150 : recordUpperSeedTailChunk150State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix150 := by
    have prior : recordUpperSeedTailChunk150Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix149 := by
      simpa only [
        recordUpperSeedTailChunk150Before,
        recordUpperSeedTailChunk149State] using h149
    simpa only [recordUpperSeedTailPrefix150] using
      recordUpperSeedTailChunk150Step.certifies prior
  have h151 : recordUpperSeedTailChunk151State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix151 := by
    have prior : recordUpperSeedTailChunk151Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix150 := by
      simpa only [
        recordUpperSeedTailChunk151Before,
        recordUpperSeedTailChunk150State] using h150
    simpa only [recordUpperSeedTailPrefix151] using
      recordUpperSeedTailChunk151Step.certifies prior
  have h152 : recordUpperSeedTailChunk152State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix152 := by
    have prior : recordUpperSeedTailChunk152Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix151 := by
      simpa only [
        recordUpperSeedTailChunk152Before,
        recordUpperSeedTailChunk151State] using h151
    simpa only [recordUpperSeedTailPrefix152] using
      recordUpperSeedTailChunk152Step.certifies prior
  have h153 : recordUpperSeedTailChunk153State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix153 := by
    have prior : recordUpperSeedTailChunk153Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix152 := by
      simpa only [
        recordUpperSeedTailChunk153Before,
        recordUpperSeedTailChunk152State] using h152
    simpa only [recordUpperSeedTailPrefix153] using
      recordUpperSeedTailChunk153Step.certifies prior
  have h154 : recordUpperSeedTailChunk154State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix154 := by
    have prior : recordUpperSeedTailChunk154Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix153 := by
      simpa only [
        recordUpperSeedTailChunk154Before,
        recordUpperSeedTailChunk153State] using h153
    simpa only [recordUpperSeedTailPrefix154] using
      recordUpperSeedTailChunk154Step.certifies prior
  have h155 : recordUpperSeedTailChunk155State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix155 := by
    have prior : recordUpperSeedTailChunk155Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix154 := by
      simpa only [
        recordUpperSeedTailChunk155Before,
        recordUpperSeedTailChunk154State] using h154
    simpa only [recordUpperSeedTailPrefix155] using
      recordUpperSeedTailChunk155Step.certifies prior
  have h156 : recordUpperSeedTailChunk156State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix156 := by
    have prior : recordUpperSeedTailChunk156Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix155 := by
      simpa only [
        recordUpperSeedTailChunk156Before,
        recordUpperSeedTailChunk155State] using h155
    simpa only [recordUpperSeedTailPrefix156] using
      recordUpperSeedTailChunk156Step.certifies prior
  have h157 : recordUpperSeedTailChunk157State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix157 := by
    have prior : recordUpperSeedTailChunk157Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix156 := by
      simpa only [
        recordUpperSeedTailChunk157Before,
        recordUpperSeedTailChunk156State] using h156
    simpa only [recordUpperSeedTailPrefix157] using
      recordUpperSeedTailChunk157Step.certifies prior
  have h158 : recordUpperSeedTailChunk158State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix158 := by
    have prior : recordUpperSeedTailChunk158Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix157 := by
      simpa only [
        recordUpperSeedTailChunk158Before,
        recordUpperSeedTailChunk157State] using h157
    simpa only [recordUpperSeedTailPrefix158] using
      recordUpperSeedTailChunk158Step.certifies prior
  have h159 : recordUpperSeedTailChunk159State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix159 := by
    have prior : recordUpperSeedTailChunk159Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix158 := by
      simpa only [
        recordUpperSeedTailChunk159Before,
        recordUpperSeedTailChunk158State] using h158
    simpa only [recordUpperSeedTailPrefix159] using
      recordUpperSeedTailChunk159Step.certifies prior
  have h160 : recordUpperSeedTailChunk160State =
      (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix160 := by
    have prior : recordUpperSeedTailChunk160Before =
        (recordUpperWitnessBase) ^ recordUpperSeedTailPrefix159 := by
      simpa only [
        recordUpperSeedTailChunk160Before,
        recordUpperSeedTailChunk159State] using h159
    simpa only [recordUpperSeedTailPrefix160] using
      recordUpperSeedTailChunk160Step.certifies prior
  exact h160

end PrimeFactorUnimodality
