import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Assembly.Part04
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinUpperSeedTail.Part200

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-upper-seed-base11.json` (semantic SHA-256 `493791f7b41de1500c4b830f254f9f92fd9c5d50d639b62aa2b46ca48591321f`, excluding elapsed time). Semantic tail assembly group 5. -/

namespace PrimeFactorUnimodality

theorem recordUpperSeedTailGroup05_semantic :
    recordUpperSeedTailChunk200State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix200 := by
  have h161 : recordUpperSeedTailChunk161State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix161 := by
    have boundary : recordUpperSeedTailChunk161Before =
        recordUpperSeedTailChunk160State := by rfl
    exact recordUpperSeedTailChunk161Step.certifies
      (boundary.trans recordUpperSeedTailGroup04_semantic)
  have h162 : recordUpperSeedTailChunk162State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix162 := by
    have boundary : recordUpperSeedTailChunk162Before =
        recordUpperSeedTailChunk161State := by rfl
    exact recordUpperSeedTailChunk162Step.certifies
      (boundary.trans h161)
  have h163 : recordUpperSeedTailChunk163State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix163 := by
    have boundary : recordUpperSeedTailChunk163Before =
        recordUpperSeedTailChunk162State := by rfl
    exact recordUpperSeedTailChunk163Step.certifies
      (boundary.trans h162)
  have h164 : recordUpperSeedTailChunk164State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix164 := by
    have boundary : recordUpperSeedTailChunk164Before =
        recordUpperSeedTailChunk163State := by rfl
    exact recordUpperSeedTailChunk164Step.certifies
      (boundary.trans h163)
  have h165 : recordUpperSeedTailChunk165State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix165 := by
    have boundary : recordUpperSeedTailChunk165Before =
        recordUpperSeedTailChunk164State := by rfl
    exact recordUpperSeedTailChunk165Step.certifies
      (boundary.trans h164)
  have h166 : recordUpperSeedTailChunk166State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix166 := by
    have boundary : recordUpperSeedTailChunk166Before =
        recordUpperSeedTailChunk165State := by rfl
    exact recordUpperSeedTailChunk166Step.certifies
      (boundary.trans h165)
  have h167 : recordUpperSeedTailChunk167State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix167 := by
    have boundary : recordUpperSeedTailChunk167Before =
        recordUpperSeedTailChunk166State := by rfl
    exact recordUpperSeedTailChunk167Step.certifies
      (boundary.trans h166)
  have h168 : recordUpperSeedTailChunk168State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix168 := by
    have boundary : recordUpperSeedTailChunk168Before =
        recordUpperSeedTailChunk167State := by rfl
    exact recordUpperSeedTailChunk168Step.certifies
      (boundary.trans h167)
  have h169 : recordUpperSeedTailChunk169State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix169 := by
    have boundary : recordUpperSeedTailChunk169Before =
        recordUpperSeedTailChunk168State := by rfl
    exact recordUpperSeedTailChunk169Step.certifies
      (boundary.trans h168)
  have h170 : recordUpperSeedTailChunk170State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix170 := by
    have boundary : recordUpperSeedTailChunk170Before =
        recordUpperSeedTailChunk169State := by rfl
    exact recordUpperSeedTailChunk170Step.certifies
      (boundary.trans h169)
  have h171 : recordUpperSeedTailChunk171State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix171 := by
    have boundary : recordUpperSeedTailChunk171Before =
        recordUpperSeedTailChunk170State := by rfl
    exact recordUpperSeedTailChunk171Step.certifies
      (boundary.trans h170)
  have h172 : recordUpperSeedTailChunk172State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix172 := by
    have boundary : recordUpperSeedTailChunk172Before =
        recordUpperSeedTailChunk171State := by rfl
    exact recordUpperSeedTailChunk172Step.certifies
      (boundary.trans h171)
  have h173 : recordUpperSeedTailChunk173State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix173 := by
    have boundary : recordUpperSeedTailChunk173Before =
        recordUpperSeedTailChunk172State := by rfl
    exact recordUpperSeedTailChunk173Step.certifies
      (boundary.trans h172)
  have h174 : recordUpperSeedTailChunk174State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix174 := by
    have boundary : recordUpperSeedTailChunk174Before =
        recordUpperSeedTailChunk173State := by rfl
    exact recordUpperSeedTailChunk174Step.certifies
      (boundary.trans h173)
  have h175 : recordUpperSeedTailChunk175State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix175 := by
    have boundary : recordUpperSeedTailChunk175Before =
        recordUpperSeedTailChunk174State := by rfl
    exact recordUpperSeedTailChunk175Step.certifies
      (boundary.trans h174)
  have h176 : recordUpperSeedTailChunk176State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix176 := by
    have boundary : recordUpperSeedTailChunk176Before =
        recordUpperSeedTailChunk175State := by rfl
    exact recordUpperSeedTailChunk176Step.certifies
      (boundary.trans h175)
  have h177 : recordUpperSeedTailChunk177State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix177 := by
    have boundary : recordUpperSeedTailChunk177Before =
        recordUpperSeedTailChunk176State := by rfl
    exact recordUpperSeedTailChunk177Step.certifies
      (boundary.trans h176)
  have h178 : recordUpperSeedTailChunk178State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix178 := by
    have boundary : recordUpperSeedTailChunk178Before =
        recordUpperSeedTailChunk177State := by rfl
    exact recordUpperSeedTailChunk178Step.certifies
      (boundary.trans h177)
  have h179 : recordUpperSeedTailChunk179State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix179 := by
    have boundary : recordUpperSeedTailChunk179Before =
        recordUpperSeedTailChunk178State := by rfl
    exact recordUpperSeedTailChunk179Step.certifies
      (boundary.trans h178)
  have h180 : recordUpperSeedTailChunk180State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix180 := by
    have boundary : recordUpperSeedTailChunk180Before =
        recordUpperSeedTailChunk179State := by rfl
    exact recordUpperSeedTailChunk180Step.certifies
      (boundary.trans h179)
  have h181 : recordUpperSeedTailChunk181State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix181 := by
    have boundary : recordUpperSeedTailChunk181Before =
        recordUpperSeedTailChunk180State := by rfl
    exact recordUpperSeedTailChunk181Step.certifies
      (boundary.trans h180)
  have h182 : recordUpperSeedTailChunk182State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix182 := by
    have boundary : recordUpperSeedTailChunk182Before =
        recordUpperSeedTailChunk181State := by rfl
    exact recordUpperSeedTailChunk182Step.certifies
      (boundary.trans h181)
  have h183 : recordUpperSeedTailChunk183State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix183 := by
    have boundary : recordUpperSeedTailChunk183Before =
        recordUpperSeedTailChunk182State := by rfl
    exact recordUpperSeedTailChunk183Step.certifies
      (boundary.trans h182)
  have h184 : recordUpperSeedTailChunk184State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix184 := by
    have boundary : recordUpperSeedTailChunk184Before =
        recordUpperSeedTailChunk183State := by rfl
    exact recordUpperSeedTailChunk184Step.certifies
      (boundary.trans h183)
  have h185 : recordUpperSeedTailChunk185State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix185 := by
    have boundary : recordUpperSeedTailChunk185Before =
        recordUpperSeedTailChunk184State := by rfl
    exact recordUpperSeedTailChunk185Step.certifies
      (boundary.trans h184)
  have h186 : recordUpperSeedTailChunk186State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix186 := by
    have boundary : recordUpperSeedTailChunk186Before =
        recordUpperSeedTailChunk185State := by rfl
    exact recordUpperSeedTailChunk186Step.certifies
      (boundary.trans h185)
  have h187 : recordUpperSeedTailChunk187State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix187 := by
    have boundary : recordUpperSeedTailChunk187Before =
        recordUpperSeedTailChunk186State := by rfl
    exact recordUpperSeedTailChunk187Step.certifies
      (boundary.trans h186)
  have h188 : recordUpperSeedTailChunk188State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix188 := by
    have boundary : recordUpperSeedTailChunk188Before =
        recordUpperSeedTailChunk187State := by rfl
    exact recordUpperSeedTailChunk188Step.certifies
      (boundary.trans h187)
  have h189 : recordUpperSeedTailChunk189State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix189 := by
    have boundary : recordUpperSeedTailChunk189Before =
        recordUpperSeedTailChunk188State := by rfl
    exact recordUpperSeedTailChunk189Step.certifies
      (boundary.trans h188)
  have h190 : recordUpperSeedTailChunk190State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix190 := by
    have boundary : recordUpperSeedTailChunk190Before =
        recordUpperSeedTailChunk189State := by rfl
    exact recordUpperSeedTailChunk190Step.certifies
      (boundary.trans h189)
  have h191 : recordUpperSeedTailChunk191State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix191 := by
    have boundary : recordUpperSeedTailChunk191Before =
        recordUpperSeedTailChunk190State := by rfl
    exact recordUpperSeedTailChunk191Step.certifies
      (boundary.trans h190)
  have h192 : recordUpperSeedTailChunk192State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix192 := by
    have boundary : recordUpperSeedTailChunk192Before =
        recordUpperSeedTailChunk191State := by rfl
    exact recordUpperSeedTailChunk192Step.certifies
      (boundary.trans h191)
  have h193 : recordUpperSeedTailChunk193State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix193 := by
    have boundary : recordUpperSeedTailChunk193Before =
        recordUpperSeedTailChunk192State := by rfl
    exact recordUpperSeedTailChunk193Step.certifies
      (boundary.trans h192)
  have h194 : recordUpperSeedTailChunk194State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix194 := by
    have boundary : recordUpperSeedTailChunk194Before =
        recordUpperSeedTailChunk193State := by rfl
    exact recordUpperSeedTailChunk194Step.certifies
      (boundary.trans h193)
  have h195 : recordUpperSeedTailChunk195State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix195 := by
    have boundary : recordUpperSeedTailChunk195Before =
        recordUpperSeedTailChunk194State := by rfl
    exact recordUpperSeedTailChunk195Step.certifies
      (boundary.trans h194)
  have h196 : recordUpperSeedTailChunk196State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix196 := by
    have boundary : recordUpperSeedTailChunk196Before =
        recordUpperSeedTailChunk195State := by rfl
    exact recordUpperSeedTailChunk196Step.certifies
      (boundary.trans h195)
  have h197 : recordUpperSeedTailChunk197State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix197 := by
    have boundary : recordUpperSeedTailChunk197Before =
        recordUpperSeedTailChunk196State := by rfl
    exact recordUpperSeedTailChunk197Step.certifies
      (boundary.trans h196)
  have h198 : recordUpperSeedTailChunk198State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix198 := by
    have boundary : recordUpperSeedTailChunk198Before =
        recordUpperSeedTailChunk197State := by rfl
    exact recordUpperSeedTailChunk198Step.certifies
      (boundary.trans h197)
  have h199 : recordUpperSeedTailChunk199State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix199 := by
    have boundary : recordUpperSeedTailChunk199Before =
        recordUpperSeedTailChunk198State := by rfl
    exact recordUpperSeedTailChunk199Step.certifies
      (boundary.trans h198)
  have h200 : recordUpperSeedTailChunk200State =
      (recordUpperWitnessBase : ZMod recordUpper) ^ recordUpperSeedTailPrefix200 := by
    have boundary : recordUpperSeedTailChunk200Before =
        recordUpperSeedTailChunk199State := by rfl
    exact recordUpperSeedTailChunk200Step.certifies
      (boundary.trans h199)
  exact h200

end PrimeFactorUnimodality
