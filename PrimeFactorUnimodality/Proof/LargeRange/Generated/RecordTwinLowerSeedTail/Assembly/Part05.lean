import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Assembly.Part04
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part200

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-lower-seed.json` (semantic SHA-256 `3ce105dad06099400dfd2e30c65d47c6e02828915452a8459553c3bb0eb78b73`, excluding elapsed time). Semantic tail assembly group 5. -/

namespace PrimeFactorUnimodality

theorem recordLowerSeedTailGroup05_semantic :
    recordLowerSeedTailChunk200State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix200 := by
  have h161 : recordLowerSeedTailChunk161State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix161 := by
    have boundary : recordLowerSeedTailChunk161Before =
        recordLowerSeedTailChunk160State := by rfl
    exact recordLowerSeedTailChunk161Step.certifies
      (boundary.trans recordLowerSeedTailGroup04_semantic)
  have h162 : recordLowerSeedTailChunk162State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix162 := by
    have boundary : recordLowerSeedTailChunk162Before =
        recordLowerSeedTailChunk161State := by rfl
    exact recordLowerSeedTailChunk162Step.certifies
      (boundary.trans h161)
  have h163 : recordLowerSeedTailChunk163State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix163 := by
    have boundary : recordLowerSeedTailChunk163Before =
        recordLowerSeedTailChunk162State := by rfl
    exact recordLowerSeedTailChunk163Step.certifies
      (boundary.trans h162)
  have h164 : recordLowerSeedTailChunk164State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix164 := by
    have boundary : recordLowerSeedTailChunk164Before =
        recordLowerSeedTailChunk163State := by rfl
    exact recordLowerSeedTailChunk164Step.certifies
      (boundary.trans h163)
  have h165 : recordLowerSeedTailChunk165State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix165 := by
    have boundary : recordLowerSeedTailChunk165Before =
        recordLowerSeedTailChunk164State := by rfl
    exact recordLowerSeedTailChunk165Step.certifies
      (boundary.trans h164)
  have h166 : recordLowerSeedTailChunk166State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix166 := by
    have boundary : recordLowerSeedTailChunk166Before =
        recordLowerSeedTailChunk165State := by rfl
    exact recordLowerSeedTailChunk166Step.certifies
      (boundary.trans h165)
  have h167 : recordLowerSeedTailChunk167State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix167 := by
    have boundary : recordLowerSeedTailChunk167Before =
        recordLowerSeedTailChunk166State := by rfl
    exact recordLowerSeedTailChunk167Step.certifies
      (boundary.trans h166)
  have h168 : recordLowerSeedTailChunk168State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix168 := by
    have boundary : recordLowerSeedTailChunk168Before =
        recordLowerSeedTailChunk167State := by rfl
    exact recordLowerSeedTailChunk168Step.certifies
      (boundary.trans h167)
  have h169 : recordLowerSeedTailChunk169State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix169 := by
    have boundary : recordLowerSeedTailChunk169Before =
        recordLowerSeedTailChunk168State := by rfl
    exact recordLowerSeedTailChunk169Step.certifies
      (boundary.trans h168)
  have h170 : recordLowerSeedTailChunk170State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix170 := by
    have boundary : recordLowerSeedTailChunk170Before =
        recordLowerSeedTailChunk169State := by rfl
    exact recordLowerSeedTailChunk170Step.certifies
      (boundary.trans h169)
  have h171 : recordLowerSeedTailChunk171State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix171 := by
    have boundary : recordLowerSeedTailChunk171Before =
        recordLowerSeedTailChunk170State := by rfl
    exact recordLowerSeedTailChunk171Step.certifies
      (boundary.trans h170)
  have h172 : recordLowerSeedTailChunk172State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix172 := by
    have boundary : recordLowerSeedTailChunk172Before =
        recordLowerSeedTailChunk171State := by rfl
    exact recordLowerSeedTailChunk172Step.certifies
      (boundary.trans h171)
  have h173 : recordLowerSeedTailChunk173State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix173 := by
    have boundary : recordLowerSeedTailChunk173Before =
        recordLowerSeedTailChunk172State := by rfl
    exact recordLowerSeedTailChunk173Step.certifies
      (boundary.trans h172)
  have h174 : recordLowerSeedTailChunk174State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix174 := by
    have boundary : recordLowerSeedTailChunk174Before =
        recordLowerSeedTailChunk173State := by rfl
    exact recordLowerSeedTailChunk174Step.certifies
      (boundary.trans h173)
  have h175 : recordLowerSeedTailChunk175State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix175 := by
    have boundary : recordLowerSeedTailChunk175Before =
        recordLowerSeedTailChunk174State := by rfl
    exact recordLowerSeedTailChunk175Step.certifies
      (boundary.trans h174)
  have h176 : recordLowerSeedTailChunk176State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix176 := by
    have boundary : recordLowerSeedTailChunk176Before =
        recordLowerSeedTailChunk175State := by rfl
    exact recordLowerSeedTailChunk176Step.certifies
      (boundary.trans h175)
  have h177 : recordLowerSeedTailChunk177State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix177 := by
    have boundary : recordLowerSeedTailChunk177Before =
        recordLowerSeedTailChunk176State := by rfl
    exact recordLowerSeedTailChunk177Step.certifies
      (boundary.trans h176)
  have h178 : recordLowerSeedTailChunk178State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix178 := by
    have boundary : recordLowerSeedTailChunk178Before =
        recordLowerSeedTailChunk177State := by rfl
    exact recordLowerSeedTailChunk178Step.certifies
      (boundary.trans h177)
  have h179 : recordLowerSeedTailChunk179State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix179 := by
    have boundary : recordLowerSeedTailChunk179Before =
        recordLowerSeedTailChunk178State := by rfl
    exact recordLowerSeedTailChunk179Step.certifies
      (boundary.trans h178)
  have h180 : recordLowerSeedTailChunk180State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix180 := by
    have boundary : recordLowerSeedTailChunk180Before =
        recordLowerSeedTailChunk179State := by rfl
    exact recordLowerSeedTailChunk180Step.certifies
      (boundary.trans h179)
  have h181 : recordLowerSeedTailChunk181State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix181 := by
    have boundary : recordLowerSeedTailChunk181Before =
        recordLowerSeedTailChunk180State := by rfl
    exact recordLowerSeedTailChunk181Step.certifies
      (boundary.trans h180)
  have h182 : recordLowerSeedTailChunk182State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix182 := by
    have boundary : recordLowerSeedTailChunk182Before =
        recordLowerSeedTailChunk181State := by rfl
    exact recordLowerSeedTailChunk182Step.certifies
      (boundary.trans h181)
  have h183 : recordLowerSeedTailChunk183State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix183 := by
    have boundary : recordLowerSeedTailChunk183Before =
        recordLowerSeedTailChunk182State := by rfl
    exact recordLowerSeedTailChunk183Step.certifies
      (boundary.trans h182)
  have h184 : recordLowerSeedTailChunk184State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix184 := by
    have boundary : recordLowerSeedTailChunk184Before =
        recordLowerSeedTailChunk183State := by rfl
    exact recordLowerSeedTailChunk184Step.certifies
      (boundary.trans h183)
  have h185 : recordLowerSeedTailChunk185State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix185 := by
    have boundary : recordLowerSeedTailChunk185Before =
        recordLowerSeedTailChunk184State := by rfl
    exact recordLowerSeedTailChunk185Step.certifies
      (boundary.trans h184)
  have h186 : recordLowerSeedTailChunk186State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix186 := by
    have boundary : recordLowerSeedTailChunk186Before =
        recordLowerSeedTailChunk185State := by rfl
    exact recordLowerSeedTailChunk186Step.certifies
      (boundary.trans h185)
  have h187 : recordLowerSeedTailChunk187State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix187 := by
    have boundary : recordLowerSeedTailChunk187Before =
        recordLowerSeedTailChunk186State := by rfl
    exact recordLowerSeedTailChunk187Step.certifies
      (boundary.trans h186)
  have h188 : recordLowerSeedTailChunk188State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix188 := by
    have boundary : recordLowerSeedTailChunk188Before =
        recordLowerSeedTailChunk187State := by rfl
    exact recordLowerSeedTailChunk188Step.certifies
      (boundary.trans h187)
  have h189 : recordLowerSeedTailChunk189State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix189 := by
    have boundary : recordLowerSeedTailChunk189Before =
        recordLowerSeedTailChunk188State := by rfl
    exact recordLowerSeedTailChunk189Step.certifies
      (boundary.trans h188)
  have h190 : recordLowerSeedTailChunk190State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix190 := by
    have boundary : recordLowerSeedTailChunk190Before =
        recordLowerSeedTailChunk189State := by rfl
    exact recordLowerSeedTailChunk190Step.certifies
      (boundary.trans h189)
  have h191 : recordLowerSeedTailChunk191State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix191 := by
    have boundary : recordLowerSeedTailChunk191Before =
        recordLowerSeedTailChunk190State := by rfl
    exact recordLowerSeedTailChunk191Step.certifies
      (boundary.trans h190)
  have h192 : recordLowerSeedTailChunk192State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix192 := by
    have boundary : recordLowerSeedTailChunk192Before =
        recordLowerSeedTailChunk191State := by rfl
    exact recordLowerSeedTailChunk192Step.certifies
      (boundary.trans h191)
  have h193 : recordLowerSeedTailChunk193State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix193 := by
    have boundary : recordLowerSeedTailChunk193Before =
        recordLowerSeedTailChunk192State := by rfl
    exact recordLowerSeedTailChunk193Step.certifies
      (boundary.trans h192)
  have h194 : recordLowerSeedTailChunk194State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix194 := by
    have boundary : recordLowerSeedTailChunk194Before =
        recordLowerSeedTailChunk193State := by rfl
    exact recordLowerSeedTailChunk194Step.certifies
      (boundary.trans h193)
  have h195 : recordLowerSeedTailChunk195State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix195 := by
    have boundary : recordLowerSeedTailChunk195Before =
        recordLowerSeedTailChunk194State := by rfl
    exact recordLowerSeedTailChunk195Step.certifies
      (boundary.trans h194)
  have h196 : recordLowerSeedTailChunk196State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix196 := by
    have boundary : recordLowerSeedTailChunk196Before =
        recordLowerSeedTailChunk195State := by rfl
    exact recordLowerSeedTailChunk196Step.certifies
      (boundary.trans h195)
  have h197 : recordLowerSeedTailChunk197State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix197 := by
    have boundary : recordLowerSeedTailChunk197Before =
        recordLowerSeedTailChunk196State := by rfl
    exact recordLowerSeedTailChunk197Step.certifies
      (boundary.trans h196)
  have h198 : recordLowerSeedTailChunk198State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix198 := by
    have boundary : recordLowerSeedTailChunk198Before =
        recordLowerSeedTailChunk197State := by rfl
    exact recordLowerSeedTailChunk198Step.certifies
      (boundary.trans h197)
  have h199 : recordLowerSeedTailChunk199State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix199 := by
    have boundary : recordLowerSeedTailChunk199Before =
        recordLowerSeedTailChunk198State := by rfl
    exact recordLowerSeedTailChunk199Step.certifies
      (boundary.trans h198)
  have h200 : recordLowerSeedTailChunk200State =
      (BLSPrimality.alpha recordLower : BLSPrimality.X7 recordLower) ^ recordLowerSeedTailPrefix200 := by
    have boundary : recordLowerSeedTailChunk200Before =
        recordLowerSeedTailChunk199State := by rfl
    exact recordLowerSeedTailChunk200Step.certifies
      (boundary.trans h199)
  exact h200

end PrimeFactorUnimodality
