import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Assembly.Part03
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part160

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-lower-seed.json` (semantic SHA-256 `3ce105dad06099400dfd2e30c65d47c6e02828915452a8459553c3bb0eb78b73`, excluding elapsed time). Semantic tail assembly group 4. -/

namespace PrimeFactorUnimodality

theorem recordLowerSeedTailGroup04_semantic :
    recordLowerSeedTailChunk160State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix160 := by
  have h121 : recordLowerSeedTailChunk121State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix121 := by
    have boundary : recordLowerSeedTailChunk121Before =
        recordLowerSeedTailChunk120State := by rfl
    exact recordLowerSeedTailChunk121Step.certifies
      (boundary.trans recordLowerSeedTailGroup03_semantic)
  have h122 : recordLowerSeedTailChunk122State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix122 := by
    have boundary : recordLowerSeedTailChunk122Before =
        recordLowerSeedTailChunk121State := by rfl
    exact recordLowerSeedTailChunk122Step.certifies
      (boundary.trans h121)
  have h123 : recordLowerSeedTailChunk123State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix123 := by
    have boundary : recordLowerSeedTailChunk123Before =
        recordLowerSeedTailChunk122State := by rfl
    exact recordLowerSeedTailChunk123Step.certifies
      (boundary.trans h122)
  have h124 : recordLowerSeedTailChunk124State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix124 := by
    have boundary : recordLowerSeedTailChunk124Before =
        recordLowerSeedTailChunk123State := by rfl
    exact recordLowerSeedTailChunk124Step.certifies
      (boundary.trans h123)
  have h125 : recordLowerSeedTailChunk125State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix125 := by
    have boundary : recordLowerSeedTailChunk125Before =
        recordLowerSeedTailChunk124State := by rfl
    exact recordLowerSeedTailChunk125Step.certifies
      (boundary.trans h124)
  have h126 : recordLowerSeedTailChunk126State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix126 := by
    have boundary : recordLowerSeedTailChunk126Before =
        recordLowerSeedTailChunk125State := by rfl
    exact recordLowerSeedTailChunk126Step.certifies
      (boundary.trans h125)
  have h127 : recordLowerSeedTailChunk127State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix127 := by
    have boundary : recordLowerSeedTailChunk127Before =
        recordLowerSeedTailChunk126State := by rfl
    exact recordLowerSeedTailChunk127Step.certifies
      (boundary.trans h126)
  have h128 : recordLowerSeedTailChunk128State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix128 := by
    have boundary : recordLowerSeedTailChunk128Before =
        recordLowerSeedTailChunk127State := by rfl
    exact recordLowerSeedTailChunk128Step.certifies
      (boundary.trans h127)
  have h129 : recordLowerSeedTailChunk129State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix129 := by
    have boundary : recordLowerSeedTailChunk129Before =
        recordLowerSeedTailChunk128State := by rfl
    exact recordLowerSeedTailChunk129Step.certifies
      (boundary.trans h128)
  have h130 : recordLowerSeedTailChunk130State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix130 := by
    have boundary : recordLowerSeedTailChunk130Before =
        recordLowerSeedTailChunk129State := by rfl
    exact recordLowerSeedTailChunk130Step.certifies
      (boundary.trans h129)
  have h131 : recordLowerSeedTailChunk131State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix131 := by
    have boundary : recordLowerSeedTailChunk131Before =
        recordLowerSeedTailChunk130State := by rfl
    exact recordLowerSeedTailChunk131Step.certifies
      (boundary.trans h130)
  have h132 : recordLowerSeedTailChunk132State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix132 := by
    have boundary : recordLowerSeedTailChunk132Before =
        recordLowerSeedTailChunk131State := by rfl
    exact recordLowerSeedTailChunk132Step.certifies
      (boundary.trans h131)
  have h133 : recordLowerSeedTailChunk133State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix133 := by
    have boundary : recordLowerSeedTailChunk133Before =
        recordLowerSeedTailChunk132State := by rfl
    exact recordLowerSeedTailChunk133Step.certifies
      (boundary.trans h132)
  have h134 : recordLowerSeedTailChunk134State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix134 := by
    have boundary : recordLowerSeedTailChunk134Before =
        recordLowerSeedTailChunk133State := by rfl
    exact recordLowerSeedTailChunk134Step.certifies
      (boundary.trans h133)
  have h135 : recordLowerSeedTailChunk135State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix135 := by
    have boundary : recordLowerSeedTailChunk135Before =
        recordLowerSeedTailChunk134State := by rfl
    exact recordLowerSeedTailChunk135Step.certifies
      (boundary.trans h134)
  have h136 : recordLowerSeedTailChunk136State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix136 := by
    have boundary : recordLowerSeedTailChunk136Before =
        recordLowerSeedTailChunk135State := by rfl
    exact recordLowerSeedTailChunk136Step.certifies
      (boundary.trans h135)
  have h137 : recordLowerSeedTailChunk137State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix137 := by
    have boundary : recordLowerSeedTailChunk137Before =
        recordLowerSeedTailChunk136State := by rfl
    exact recordLowerSeedTailChunk137Step.certifies
      (boundary.trans h136)
  have h138 : recordLowerSeedTailChunk138State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix138 := by
    have boundary : recordLowerSeedTailChunk138Before =
        recordLowerSeedTailChunk137State := by rfl
    exact recordLowerSeedTailChunk138Step.certifies
      (boundary.trans h137)
  have h139 : recordLowerSeedTailChunk139State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix139 := by
    have boundary : recordLowerSeedTailChunk139Before =
        recordLowerSeedTailChunk138State := by rfl
    exact recordLowerSeedTailChunk139Step.certifies
      (boundary.trans h138)
  have h140 : recordLowerSeedTailChunk140State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix140 := by
    have boundary : recordLowerSeedTailChunk140Before =
        recordLowerSeedTailChunk139State := by rfl
    exact recordLowerSeedTailChunk140Step.certifies
      (boundary.trans h139)
  have h141 : recordLowerSeedTailChunk141State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix141 := by
    have boundary : recordLowerSeedTailChunk141Before =
        recordLowerSeedTailChunk140State := by rfl
    exact recordLowerSeedTailChunk141Step.certifies
      (boundary.trans h140)
  have h142 : recordLowerSeedTailChunk142State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix142 := by
    have boundary : recordLowerSeedTailChunk142Before =
        recordLowerSeedTailChunk141State := by rfl
    exact recordLowerSeedTailChunk142Step.certifies
      (boundary.trans h141)
  have h143 : recordLowerSeedTailChunk143State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix143 := by
    have boundary : recordLowerSeedTailChunk143Before =
        recordLowerSeedTailChunk142State := by rfl
    exact recordLowerSeedTailChunk143Step.certifies
      (boundary.trans h142)
  have h144 : recordLowerSeedTailChunk144State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix144 := by
    have boundary : recordLowerSeedTailChunk144Before =
        recordLowerSeedTailChunk143State := by rfl
    exact recordLowerSeedTailChunk144Step.certifies
      (boundary.trans h143)
  have h145 : recordLowerSeedTailChunk145State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix145 := by
    have boundary : recordLowerSeedTailChunk145Before =
        recordLowerSeedTailChunk144State := by rfl
    exact recordLowerSeedTailChunk145Step.certifies
      (boundary.trans h144)
  have h146 : recordLowerSeedTailChunk146State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix146 := by
    have boundary : recordLowerSeedTailChunk146Before =
        recordLowerSeedTailChunk145State := by rfl
    exact recordLowerSeedTailChunk146Step.certifies
      (boundary.trans h145)
  have h147 : recordLowerSeedTailChunk147State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix147 := by
    have boundary : recordLowerSeedTailChunk147Before =
        recordLowerSeedTailChunk146State := by rfl
    exact recordLowerSeedTailChunk147Step.certifies
      (boundary.trans h146)
  have h148 : recordLowerSeedTailChunk148State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix148 := by
    have boundary : recordLowerSeedTailChunk148Before =
        recordLowerSeedTailChunk147State := by rfl
    exact recordLowerSeedTailChunk148Step.certifies
      (boundary.trans h147)
  have h149 : recordLowerSeedTailChunk149State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix149 := by
    have boundary : recordLowerSeedTailChunk149Before =
        recordLowerSeedTailChunk148State := by rfl
    exact recordLowerSeedTailChunk149Step.certifies
      (boundary.trans h148)
  have h150 : recordLowerSeedTailChunk150State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix150 := by
    have boundary : recordLowerSeedTailChunk150Before =
        recordLowerSeedTailChunk149State := by rfl
    exact recordLowerSeedTailChunk150Step.certifies
      (boundary.trans h149)
  have h151 : recordLowerSeedTailChunk151State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix151 := by
    have boundary : recordLowerSeedTailChunk151Before =
        recordLowerSeedTailChunk150State := by rfl
    exact recordLowerSeedTailChunk151Step.certifies
      (boundary.trans h150)
  have h152 : recordLowerSeedTailChunk152State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix152 := by
    have boundary : recordLowerSeedTailChunk152Before =
        recordLowerSeedTailChunk151State := by rfl
    exact recordLowerSeedTailChunk152Step.certifies
      (boundary.trans h151)
  have h153 : recordLowerSeedTailChunk153State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix153 := by
    have boundary : recordLowerSeedTailChunk153Before =
        recordLowerSeedTailChunk152State := by rfl
    exact recordLowerSeedTailChunk153Step.certifies
      (boundary.trans h152)
  have h154 : recordLowerSeedTailChunk154State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix154 := by
    have boundary : recordLowerSeedTailChunk154Before =
        recordLowerSeedTailChunk153State := by rfl
    exact recordLowerSeedTailChunk154Step.certifies
      (boundary.trans h153)
  have h155 : recordLowerSeedTailChunk155State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix155 := by
    have boundary : recordLowerSeedTailChunk155Before =
        recordLowerSeedTailChunk154State := by rfl
    exact recordLowerSeedTailChunk155Step.certifies
      (boundary.trans h154)
  have h156 : recordLowerSeedTailChunk156State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix156 := by
    have boundary : recordLowerSeedTailChunk156Before =
        recordLowerSeedTailChunk155State := by rfl
    exact recordLowerSeedTailChunk156Step.certifies
      (boundary.trans h155)
  have h157 : recordLowerSeedTailChunk157State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix157 := by
    have boundary : recordLowerSeedTailChunk157Before =
        recordLowerSeedTailChunk156State := by rfl
    exact recordLowerSeedTailChunk157Step.certifies
      (boundary.trans h156)
  have h158 : recordLowerSeedTailChunk158State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix158 := by
    have boundary : recordLowerSeedTailChunk158Before =
        recordLowerSeedTailChunk157State := by rfl
    exact recordLowerSeedTailChunk158Step.certifies
      (boundary.trans h157)
  have h159 : recordLowerSeedTailChunk159State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix159 := by
    have boundary : recordLowerSeedTailChunk159Before =
        recordLowerSeedTailChunk158State := by rfl
    exact recordLowerSeedTailChunk159Step.certifies
      (boundary.trans h158)
  have h160 : recordLowerSeedTailChunk160State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix160 := by
    have boundary : recordLowerSeedTailChunk160Before =
        recordLowerSeedTailChunk159State := by rfl
    exact recordLowerSeedTailChunk160Step.certifies
      (boundary.trans h159)
  exact h160

end PrimeFactorUnimodality
