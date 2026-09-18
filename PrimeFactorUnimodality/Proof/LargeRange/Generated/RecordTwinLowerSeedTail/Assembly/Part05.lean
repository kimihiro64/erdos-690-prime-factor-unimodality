import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Assembly.Part04
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part161
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part162
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part163
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part164
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part165
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part166
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part167
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part168
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part169
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part170
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part171
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part172
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part173
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part174
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part175
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part176
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part177
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part178
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part179
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part180
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part181
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part182
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part183
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part184
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part185
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part186
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part187
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part188
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part189
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part190
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part191
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part192
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part193
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part194
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part195
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part196
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part197
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part198
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part199
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordTwinLowerSeedTail.Part200

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! Generated from `.research/generated/record-twin-lower-seed.json` (semantic SHA-256 `3ce105dad06099400dfd2e30c65d47c6e02828915452a8459553c3bb0eb78b73`, excluding elapsed time). Semantic tail assembly group 5. -/

namespace PrimeFactorUnimodality

theorem recordLowerSeedTailGroup05_semantic :
    recordLowerSeedTailChunk200State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix200 := by
  have h161 : recordLowerSeedTailChunk161State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix161 := by
    have prior : recordLowerSeedTailChunk161Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix160 := by
      simpa only [
        recordLowerSeedTailChunk161Before,
        recordLowerSeedTailChunk160State] using recordLowerSeedTailGroup04_semantic
    simpa only [recordLowerSeedTailPrefix161] using
      recordLowerSeedTailChunk161Step.certifies prior
  have h162 : recordLowerSeedTailChunk162State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix162 := by
    have prior : recordLowerSeedTailChunk162Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix161 := by
      simpa only [
        recordLowerSeedTailChunk162Before,
        recordLowerSeedTailChunk161State] using h161
    simpa only [recordLowerSeedTailPrefix162] using
      recordLowerSeedTailChunk162Step.certifies prior
  have h163 : recordLowerSeedTailChunk163State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix163 := by
    have prior : recordLowerSeedTailChunk163Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix162 := by
      simpa only [
        recordLowerSeedTailChunk163Before,
        recordLowerSeedTailChunk162State] using h162
    simpa only [recordLowerSeedTailPrefix163] using
      recordLowerSeedTailChunk163Step.certifies prior
  have h164 : recordLowerSeedTailChunk164State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix164 := by
    have prior : recordLowerSeedTailChunk164Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix163 := by
      simpa only [
        recordLowerSeedTailChunk164Before,
        recordLowerSeedTailChunk163State] using h163
    simpa only [recordLowerSeedTailPrefix164] using
      recordLowerSeedTailChunk164Step.certifies prior
  have h165 : recordLowerSeedTailChunk165State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix165 := by
    have prior : recordLowerSeedTailChunk165Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix164 := by
      simpa only [
        recordLowerSeedTailChunk165Before,
        recordLowerSeedTailChunk164State] using h164
    simpa only [recordLowerSeedTailPrefix165] using
      recordLowerSeedTailChunk165Step.certifies prior
  have h166 : recordLowerSeedTailChunk166State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix166 := by
    have prior : recordLowerSeedTailChunk166Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix165 := by
      simpa only [
        recordLowerSeedTailChunk166Before,
        recordLowerSeedTailChunk165State] using h165
    simpa only [recordLowerSeedTailPrefix166] using
      recordLowerSeedTailChunk166Step.certifies prior
  have h167 : recordLowerSeedTailChunk167State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix167 := by
    have prior : recordLowerSeedTailChunk167Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix166 := by
      simpa only [
        recordLowerSeedTailChunk167Before,
        recordLowerSeedTailChunk166State] using h166
    simpa only [recordLowerSeedTailPrefix167] using
      recordLowerSeedTailChunk167Step.certifies prior
  have h168 : recordLowerSeedTailChunk168State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix168 := by
    have prior : recordLowerSeedTailChunk168Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix167 := by
      simpa only [
        recordLowerSeedTailChunk168Before,
        recordLowerSeedTailChunk167State] using h167
    simpa only [recordLowerSeedTailPrefix168] using
      recordLowerSeedTailChunk168Step.certifies prior
  have h169 : recordLowerSeedTailChunk169State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix169 := by
    have prior : recordLowerSeedTailChunk169Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix168 := by
      simpa only [
        recordLowerSeedTailChunk169Before,
        recordLowerSeedTailChunk168State] using h168
    simpa only [recordLowerSeedTailPrefix169] using
      recordLowerSeedTailChunk169Step.certifies prior
  have h170 : recordLowerSeedTailChunk170State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix170 := by
    have prior : recordLowerSeedTailChunk170Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix169 := by
      simpa only [
        recordLowerSeedTailChunk170Before,
        recordLowerSeedTailChunk169State] using h169
    simpa only [recordLowerSeedTailPrefix170] using
      recordLowerSeedTailChunk170Step.certifies prior
  have h171 : recordLowerSeedTailChunk171State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix171 := by
    have prior : recordLowerSeedTailChunk171Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix170 := by
      simpa only [
        recordLowerSeedTailChunk171Before,
        recordLowerSeedTailChunk170State] using h170
    simpa only [recordLowerSeedTailPrefix171] using
      recordLowerSeedTailChunk171Step.certifies prior
  have h172 : recordLowerSeedTailChunk172State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix172 := by
    have prior : recordLowerSeedTailChunk172Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix171 := by
      simpa only [
        recordLowerSeedTailChunk172Before,
        recordLowerSeedTailChunk171State] using h171
    simpa only [recordLowerSeedTailPrefix172] using
      recordLowerSeedTailChunk172Step.certifies prior
  have h173 : recordLowerSeedTailChunk173State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix173 := by
    have prior : recordLowerSeedTailChunk173Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix172 := by
      simpa only [
        recordLowerSeedTailChunk173Before,
        recordLowerSeedTailChunk172State] using h172
    simpa only [recordLowerSeedTailPrefix173] using
      recordLowerSeedTailChunk173Step.certifies prior
  have h174 : recordLowerSeedTailChunk174State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix174 := by
    have prior : recordLowerSeedTailChunk174Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix173 := by
      simpa only [
        recordLowerSeedTailChunk174Before,
        recordLowerSeedTailChunk173State] using h173
    simpa only [recordLowerSeedTailPrefix174] using
      recordLowerSeedTailChunk174Step.certifies prior
  have h175 : recordLowerSeedTailChunk175State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix175 := by
    have prior : recordLowerSeedTailChunk175Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix174 := by
      simpa only [
        recordLowerSeedTailChunk175Before,
        recordLowerSeedTailChunk174State] using h174
    simpa only [recordLowerSeedTailPrefix175] using
      recordLowerSeedTailChunk175Step.certifies prior
  have h176 : recordLowerSeedTailChunk176State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix176 := by
    have prior : recordLowerSeedTailChunk176Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix175 := by
      simpa only [
        recordLowerSeedTailChunk176Before,
        recordLowerSeedTailChunk175State] using h175
    simpa only [recordLowerSeedTailPrefix176] using
      recordLowerSeedTailChunk176Step.certifies prior
  have h177 : recordLowerSeedTailChunk177State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix177 := by
    have prior : recordLowerSeedTailChunk177Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix176 := by
      simpa only [
        recordLowerSeedTailChunk177Before,
        recordLowerSeedTailChunk176State] using h176
    simpa only [recordLowerSeedTailPrefix177] using
      recordLowerSeedTailChunk177Step.certifies prior
  have h178 : recordLowerSeedTailChunk178State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix178 := by
    have prior : recordLowerSeedTailChunk178Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix177 := by
      simpa only [
        recordLowerSeedTailChunk178Before,
        recordLowerSeedTailChunk177State] using h177
    simpa only [recordLowerSeedTailPrefix178] using
      recordLowerSeedTailChunk178Step.certifies prior
  have h179 : recordLowerSeedTailChunk179State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix179 := by
    have prior : recordLowerSeedTailChunk179Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix178 := by
      simpa only [
        recordLowerSeedTailChunk179Before,
        recordLowerSeedTailChunk178State] using h178
    simpa only [recordLowerSeedTailPrefix179] using
      recordLowerSeedTailChunk179Step.certifies prior
  have h180 : recordLowerSeedTailChunk180State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix180 := by
    have prior : recordLowerSeedTailChunk180Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix179 := by
      simpa only [
        recordLowerSeedTailChunk180Before,
        recordLowerSeedTailChunk179State] using h179
    simpa only [recordLowerSeedTailPrefix180] using
      recordLowerSeedTailChunk180Step.certifies prior
  have h181 : recordLowerSeedTailChunk181State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix181 := by
    have prior : recordLowerSeedTailChunk181Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix180 := by
      simpa only [
        recordLowerSeedTailChunk181Before,
        recordLowerSeedTailChunk180State] using h180
    simpa only [recordLowerSeedTailPrefix181] using
      recordLowerSeedTailChunk181Step.certifies prior
  have h182 : recordLowerSeedTailChunk182State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix182 := by
    have prior : recordLowerSeedTailChunk182Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix181 := by
      simpa only [
        recordLowerSeedTailChunk182Before,
        recordLowerSeedTailChunk181State] using h181
    simpa only [recordLowerSeedTailPrefix182] using
      recordLowerSeedTailChunk182Step.certifies prior
  have h183 : recordLowerSeedTailChunk183State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix183 := by
    have prior : recordLowerSeedTailChunk183Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix182 := by
      simpa only [
        recordLowerSeedTailChunk183Before,
        recordLowerSeedTailChunk182State] using h182
    simpa only [recordLowerSeedTailPrefix183] using
      recordLowerSeedTailChunk183Step.certifies prior
  have h184 : recordLowerSeedTailChunk184State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix184 := by
    have prior : recordLowerSeedTailChunk184Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix183 := by
      simpa only [
        recordLowerSeedTailChunk184Before,
        recordLowerSeedTailChunk183State] using h183
    simpa only [recordLowerSeedTailPrefix184] using
      recordLowerSeedTailChunk184Step.certifies prior
  have h185 : recordLowerSeedTailChunk185State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix185 := by
    have prior : recordLowerSeedTailChunk185Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix184 := by
      simpa only [
        recordLowerSeedTailChunk185Before,
        recordLowerSeedTailChunk184State] using h184
    simpa only [recordLowerSeedTailPrefix185] using
      recordLowerSeedTailChunk185Step.certifies prior
  have h186 : recordLowerSeedTailChunk186State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix186 := by
    have prior : recordLowerSeedTailChunk186Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix185 := by
      simpa only [
        recordLowerSeedTailChunk186Before,
        recordLowerSeedTailChunk185State] using h185
    simpa only [recordLowerSeedTailPrefix186] using
      recordLowerSeedTailChunk186Step.certifies prior
  have h187 : recordLowerSeedTailChunk187State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix187 := by
    have prior : recordLowerSeedTailChunk187Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix186 := by
      simpa only [
        recordLowerSeedTailChunk187Before,
        recordLowerSeedTailChunk186State] using h186
    simpa only [recordLowerSeedTailPrefix187] using
      recordLowerSeedTailChunk187Step.certifies prior
  have h188 : recordLowerSeedTailChunk188State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix188 := by
    have prior : recordLowerSeedTailChunk188Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix187 := by
      simpa only [
        recordLowerSeedTailChunk188Before,
        recordLowerSeedTailChunk187State] using h187
    simpa only [recordLowerSeedTailPrefix188] using
      recordLowerSeedTailChunk188Step.certifies prior
  have h189 : recordLowerSeedTailChunk189State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix189 := by
    have prior : recordLowerSeedTailChunk189Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix188 := by
      simpa only [
        recordLowerSeedTailChunk189Before,
        recordLowerSeedTailChunk188State] using h188
    simpa only [recordLowerSeedTailPrefix189] using
      recordLowerSeedTailChunk189Step.certifies prior
  have h190 : recordLowerSeedTailChunk190State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix190 := by
    have prior : recordLowerSeedTailChunk190Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix189 := by
      simpa only [
        recordLowerSeedTailChunk190Before,
        recordLowerSeedTailChunk189State] using h189
    simpa only [recordLowerSeedTailPrefix190] using
      recordLowerSeedTailChunk190Step.certifies prior
  have h191 : recordLowerSeedTailChunk191State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix191 := by
    have prior : recordLowerSeedTailChunk191Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix190 := by
      simpa only [
        recordLowerSeedTailChunk191Before,
        recordLowerSeedTailChunk190State] using h190
    simpa only [recordLowerSeedTailPrefix191] using
      recordLowerSeedTailChunk191Step.certifies prior
  have h192 : recordLowerSeedTailChunk192State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix192 := by
    have prior : recordLowerSeedTailChunk192Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix191 := by
      simpa only [
        recordLowerSeedTailChunk192Before,
        recordLowerSeedTailChunk191State] using h191
    simpa only [recordLowerSeedTailPrefix192] using
      recordLowerSeedTailChunk192Step.certifies prior
  have h193 : recordLowerSeedTailChunk193State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix193 := by
    have prior : recordLowerSeedTailChunk193Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix192 := by
      simpa only [
        recordLowerSeedTailChunk193Before,
        recordLowerSeedTailChunk192State] using h192
    simpa only [recordLowerSeedTailPrefix193] using
      recordLowerSeedTailChunk193Step.certifies prior
  have h194 : recordLowerSeedTailChunk194State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix194 := by
    have prior : recordLowerSeedTailChunk194Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix193 := by
      simpa only [
        recordLowerSeedTailChunk194Before,
        recordLowerSeedTailChunk193State] using h193
    simpa only [recordLowerSeedTailPrefix194] using
      recordLowerSeedTailChunk194Step.certifies prior
  have h195 : recordLowerSeedTailChunk195State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix195 := by
    have prior : recordLowerSeedTailChunk195Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix194 := by
      simpa only [
        recordLowerSeedTailChunk195Before,
        recordLowerSeedTailChunk194State] using h194
    simpa only [recordLowerSeedTailPrefix195] using
      recordLowerSeedTailChunk195Step.certifies prior
  have h196 : recordLowerSeedTailChunk196State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix196 := by
    have prior : recordLowerSeedTailChunk196Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix195 := by
      simpa only [
        recordLowerSeedTailChunk196Before,
        recordLowerSeedTailChunk195State] using h195
    simpa only [recordLowerSeedTailPrefix196] using
      recordLowerSeedTailChunk196Step.certifies prior
  have h197 : recordLowerSeedTailChunk197State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix197 := by
    have prior : recordLowerSeedTailChunk197Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix196 := by
      simpa only [
        recordLowerSeedTailChunk197Before,
        recordLowerSeedTailChunk196State] using h196
    simpa only [recordLowerSeedTailPrefix197] using
      recordLowerSeedTailChunk197Step.certifies prior
  have h198 : recordLowerSeedTailChunk198State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix198 := by
    have prior : recordLowerSeedTailChunk198Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix197 := by
      simpa only [
        recordLowerSeedTailChunk198Before,
        recordLowerSeedTailChunk197State] using h197
    simpa only [recordLowerSeedTailPrefix198] using
      recordLowerSeedTailChunk198Step.certifies prior
  have h199 : recordLowerSeedTailChunk199State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix199 := by
    have prior : recordLowerSeedTailChunk199Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix198 := by
      simpa only [
        recordLowerSeedTailChunk199Before,
        recordLowerSeedTailChunk198State] using h198
    simpa only [recordLowerSeedTailPrefix199] using
      recordLowerSeedTailChunk199Step.certifies prior
  have h200 : recordLowerSeedTailChunk200State =
      (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix200 := by
    have prior : recordLowerSeedTailChunk200Before =
        (BLSPrimality.alpha recordLower) ^ recordLowerSeedTailPrefix199 := by
      simpa only [
        recordLowerSeedTailChunk200Before,
        recordLowerSeedTailChunk199State] using h199
    simpa only [recordLowerSeedTailPrefix200] using
      recordLowerSeedTailChunk200Step.certifies prior
  exact h200

end PrimeFactorUnimodality
