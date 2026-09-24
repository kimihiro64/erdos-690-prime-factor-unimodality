import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Assembly.Part03
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part160

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-upper-seed-base11.json` (semantic SHA-256 `493791f7b41de1500c4b830f254f9f92fd9c5d50d639b62aa2b46ca48591321f`, excluding elapsed time). Semantic tail assembly group 4. -/

namespace PrimeFactorUnimodality

theorem recordUpperSeedTailGroup04_semantic :
    recordUpperSeedTailChunk160State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix160 := by
  have h121 : recordUpperSeedTailChunk121State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix121 := by
    have boundary : recordUpperSeedTailChunk121Before =
        recordUpperSeedTailChunk120State := by rfl
    exact recordUpperSeedTailChunk121Step.certifies
      (boundary.trans recordUpperSeedTailGroup03_semantic)
  have h122 : recordUpperSeedTailChunk122State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix122 := by
    have boundary : recordUpperSeedTailChunk122Before =
        recordUpperSeedTailChunk121State := by rfl
    exact recordUpperSeedTailChunk122Step.certifies
      (boundary.trans h121)
  have h123 : recordUpperSeedTailChunk123State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix123 := by
    have boundary : recordUpperSeedTailChunk123Before =
        recordUpperSeedTailChunk122State := by rfl
    exact recordUpperSeedTailChunk123Step.certifies
      (boundary.trans h122)
  have h124 : recordUpperSeedTailChunk124State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix124 := by
    have boundary : recordUpperSeedTailChunk124Before =
        recordUpperSeedTailChunk123State := by rfl
    exact recordUpperSeedTailChunk124Step.certifies
      (boundary.trans h123)
  have h125 : recordUpperSeedTailChunk125State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix125 := by
    have boundary : recordUpperSeedTailChunk125Before =
        recordUpperSeedTailChunk124State := by rfl
    exact recordUpperSeedTailChunk125Step.certifies
      (boundary.trans h124)
  have h126 : recordUpperSeedTailChunk126State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix126 := by
    have boundary : recordUpperSeedTailChunk126Before =
        recordUpperSeedTailChunk125State := by rfl
    exact recordUpperSeedTailChunk126Step.certifies
      (boundary.trans h125)
  have h127 : recordUpperSeedTailChunk127State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix127 := by
    have boundary : recordUpperSeedTailChunk127Before =
        recordUpperSeedTailChunk126State := by rfl
    exact recordUpperSeedTailChunk127Step.certifies
      (boundary.trans h126)
  have h128 : recordUpperSeedTailChunk128State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix128 := by
    have boundary : recordUpperSeedTailChunk128Before =
        recordUpperSeedTailChunk127State := by rfl
    exact recordUpperSeedTailChunk128Step.certifies
      (boundary.trans h127)
  have h129 : recordUpperSeedTailChunk129State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix129 := by
    have boundary : recordUpperSeedTailChunk129Before =
        recordUpperSeedTailChunk128State := by rfl
    exact recordUpperSeedTailChunk129Step.certifies
      (boundary.trans h128)
  have h130 : recordUpperSeedTailChunk130State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix130 := by
    have boundary : recordUpperSeedTailChunk130Before =
        recordUpperSeedTailChunk129State := by rfl
    exact recordUpperSeedTailChunk130Step.certifies
      (boundary.trans h129)
  have h131 : recordUpperSeedTailChunk131State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix131 := by
    have boundary : recordUpperSeedTailChunk131Before =
        recordUpperSeedTailChunk130State := by rfl
    exact recordUpperSeedTailChunk131Step.certifies
      (boundary.trans h130)
  have h132 : recordUpperSeedTailChunk132State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix132 := by
    have boundary : recordUpperSeedTailChunk132Before =
        recordUpperSeedTailChunk131State := by rfl
    exact recordUpperSeedTailChunk132Step.certifies
      (boundary.trans h131)
  have h133 : recordUpperSeedTailChunk133State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix133 := by
    have boundary : recordUpperSeedTailChunk133Before =
        recordUpperSeedTailChunk132State := by rfl
    exact recordUpperSeedTailChunk133Step.certifies
      (boundary.trans h132)
  have h134 : recordUpperSeedTailChunk134State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix134 := by
    have boundary : recordUpperSeedTailChunk134Before =
        recordUpperSeedTailChunk133State := by rfl
    exact recordUpperSeedTailChunk134Step.certifies
      (boundary.trans h133)
  have h135 : recordUpperSeedTailChunk135State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix135 := by
    have boundary : recordUpperSeedTailChunk135Before =
        recordUpperSeedTailChunk134State := by rfl
    exact recordUpperSeedTailChunk135Step.certifies
      (boundary.trans h134)
  have h136 : recordUpperSeedTailChunk136State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix136 := by
    have boundary : recordUpperSeedTailChunk136Before =
        recordUpperSeedTailChunk135State := by rfl
    exact recordUpperSeedTailChunk136Step.certifies
      (boundary.trans h135)
  have h137 : recordUpperSeedTailChunk137State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix137 := by
    have boundary : recordUpperSeedTailChunk137Before =
        recordUpperSeedTailChunk136State := by rfl
    exact recordUpperSeedTailChunk137Step.certifies
      (boundary.trans h136)
  have h138 : recordUpperSeedTailChunk138State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix138 := by
    have boundary : recordUpperSeedTailChunk138Before =
        recordUpperSeedTailChunk137State := by rfl
    exact recordUpperSeedTailChunk138Step.certifies
      (boundary.trans h137)
  have h139 : recordUpperSeedTailChunk139State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix139 := by
    have boundary : recordUpperSeedTailChunk139Before =
        recordUpperSeedTailChunk138State := by rfl
    exact recordUpperSeedTailChunk139Step.certifies
      (boundary.trans h138)
  have h140 : recordUpperSeedTailChunk140State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix140 := by
    have boundary : recordUpperSeedTailChunk140Before =
        recordUpperSeedTailChunk139State := by rfl
    exact recordUpperSeedTailChunk140Step.certifies
      (boundary.trans h139)
  have h141 : recordUpperSeedTailChunk141State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix141 := by
    have boundary : recordUpperSeedTailChunk141Before =
        recordUpperSeedTailChunk140State := by rfl
    exact recordUpperSeedTailChunk141Step.certifies
      (boundary.trans h140)
  have h142 : recordUpperSeedTailChunk142State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix142 := by
    have boundary : recordUpperSeedTailChunk142Before =
        recordUpperSeedTailChunk141State := by rfl
    exact recordUpperSeedTailChunk142Step.certifies
      (boundary.trans h141)
  have h143 : recordUpperSeedTailChunk143State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix143 := by
    have boundary : recordUpperSeedTailChunk143Before =
        recordUpperSeedTailChunk142State := by rfl
    exact recordUpperSeedTailChunk143Step.certifies
      (boundary.trans h142)
  have h144 : recordUpperSeedTailChunk144State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix144 := by
    have boundary : recordUpperSeedTailChunk144Before =
        recordUpperSeedTailChunk143State := by rfl
    exact recordUpperSeedTailChunk144Step.certifies
      (boundary.trans h143)
  have h145 : recordUpperSeedTailChunk145State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix145 := by
    have boundary : recordUpperSeedTailChunk145Before =
        recordUpperSeedTailChunk144State := by rfl
    exact recordUpperSeedTailChunk145Step.certifies
      (boundary.trans h144)
  have h146 : recordUpperSeedTailChunk146State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix146 := by
    have boundary : recordUpperSeedTailChunk146Before =
        recordUpperSeedTailChunk145State := by rfl
    exact recordUpperSeedTailChunk146Step.certifies
      (boundary.trans h145)
  have h147 : recordUpperSeedTailChunk147State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix147 := by
    have boundary : recordUpperSeedTailChunk147Before =
        recordUpperSeedTailChunk146State := by rfl
    exact recordUpperSeedTailChunk147Step.certifies
      (boundary.trans h146)
  have h148 : recordUpperSeedTailChunk148State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix148 := by
    have boundary : recordUpperSeedTailChunk148Before =
        recordUpperSeedTailChunk147State := by rfl
    exact recordUpperSeedTailChunk148Step.certifies
      (boundary.trans h147)
  have h149 : recordUpperSeedTailChunk149State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix149 := by
    have boundary : recordUpperSeedTailChunk149Before =
        recordUpperSeedTailChunk148State := by rfl
    exact recordUpperSeedTailChunk149Step.certifies
      (boundary.trans h148)
  have h150 : recordUpperSeedTailChunk150State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix150 := by
    have boundary : recordUpperSeedTailChunk150Before =
        recordUpperSeedTailChunk149State := by rfl
    exact recordUpperSeedTailChunk150Step.certifies
      (boundary.trans h149)
  have h151 : recordUpperSeedTailChunk151State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix151 := by
    have boundary : recordUpperSeedTailChunk151Before =
        recordUpperSeedTailChunk150State := by rfl
    exact recordUpperSeedTailChunk151Step.certifies
      (boundary.trans h150)
  have h152 : recordUpperSeedTailChunk152State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix152 := by
    have boundary : recordUpperSeedTailChunk152Before =
        recordUpperSeedTailChunk151State := by rfl
    exact recordUpperSeedTailChunk152Step.certifies
      (boundary.trans h151)
  have h153 : recordUpperSeedTailChunk153State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix153 := by
    have boundary : recordUpperSeedTailChunk153Before =
        recordUpperSeedTailChunk152State := by rfl
    exact recordUpperSeedTailChunk153Step.certifies
      (boundary.trans h152)
  have h154 : recordUpperSeedTailChunk154State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix154 := by
    have boundary : recordUpperSeedTailChunk154Before =
        recordUpperSeedTailChunk153State := by rfl
    exact recordUpperSeedTailChunk154Step.certifies
      (boundary.trans h153)
  have h155 : recordUpperSeedTailChunk155State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix155 := by
    have boundary : recordUpperSeedTailChunk155Before =
        recordUpperSeedTailChunk154State := by rfl
    exact recordUpperSeedTailChunk155Step.certifies
      (boundary.trans h154)
  have h156 : recordUpperSeedTailChunk156State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix156 := by
    have boundary : recordUpperSeedTailChunk156Before =
        recordUpperSeedTailChunk155State := by rfl
    exact recordUpperSeedTailChunk156Step.certifies
      (boundary.trans h155)
  have h157 : recordUpperSeedTailChunk157State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix157 := by
    have boundary : recordUpperSeedTailChunk157Before =
        recordUpperSeedTailChunk156State := by rfl
    exact recordUpperSeedTailChunk157Step.certifies
      (boundary.trans h156)
  have h158 : recordUpperSeedTailChunk158State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix158 := by
    have boundary : recordUpperSeedTailChunk158Before =
        recordUpperSeedTailChunk157State := by rfl
    exact recordUpperSeedTailChunk158Step.certifies
      (boundary.trans h157)
  have h159 : recordUpperSeedTailChunk159State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix159 := by
    have boundary : recordUpperSeedTailChunk159Before =
        recordUpperSeedTailChunk158State := by rfl
    exact recordUpperSeedTailChunk159Step.certifies
      (boundary.trans h158)
  have h160 : recordUpperSeedTailChunk160State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix160 := by
    have boundary : recordUpperSeedTailChunk160Before =
        recordUpperSeedTailChunk159State := by rfl
    exact recordUpperSeedTailChunk160Step.certifies
      (boundary.trans h159)
  exact h160

end PrimeFactorUnimodality
