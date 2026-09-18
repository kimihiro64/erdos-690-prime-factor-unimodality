import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00058_values : List Nat :=
  [fullRecordGapCenterValue - 39204,
    fullRecordGapCenterValue - 38808,
    fullRecordGapCenterValue - 38400,
    fullRecordGapCenterValue - 37422,
    fullRecordGapCenterValue - 37044,
    fullRecordGapCenterValue - 35574,
    fullRecordGapCenterValue - 34992,
    fullRecordGapCenterValue - 34848,
    fullRecordGapCenterValue - 34650,
    fullRecordGapCenterValue - 33792,
    fullRecordGapCenterValue - 33600,
    fullRecordGapCenterValue - 33264,
    fullRecordGapCenterValue - 33000,
    fullRecordGapCenterValue - 32928,
    fullRecordGapCenterValue - 32400,
    fullRecordGapCenterValue - 31944,
    fullRecordGapCenterValue - 31752,
    fullRecordGapCenterValue - 31104,
    fullRecordGapCenterValue - 30492,
    fullRecordGapCenterValue - 30184,
    fullRecordGapCenterValue - 29700,
    fullRecordGapCenterValue - 29568,
    fullRecordGapCenterValue - 29400,
    fullRecordGapCenterValue - 29040,
    fullRecordGapCenterValue - 28812,
    fullRecordGapCenterValue - 28672,
    fullRecordGapCenterValue - 27720,
    fullRecordGapCenterValue - 26880,
    fullRecordGapCenterValue - 26730,
    fullRecordGapCenterValue - 26460,
    fullRecordGapCenterValue - 24640,
    fullRecordGapCenterValue - 24192,
    fullRecordGapCenterValue - 24010,
    fullRecordGapCenterValue - 24000,
    fullRecordGapCenterValue - 23958,
    fullRecordGapCenterValue - 23814,
    fullRecordGapCenterValue - 23520,
    fullRecordGapCenterValue - 21870,
    fullRecordGapCenterValue - 21600,
    fullRecordGapCenterValue - 21504,
    fullRecordGapCenterValue - 21384,
    fullRecordGapCenterValue - 21000,
    fullRecordGapCenterValue - 20412,
    fullRecordGapCenterValue - 20160,
    fullRecordGapCenterValue - 19600,
    fullRecordGapCenterValue - 18900,
    fullRecordGapCenterValue - 17280,
    fullRecordGapCenterValue - 16632,
    fullRecordGapCenterValue - 16200,
    fullRecordGapCenterValue - 16170,
    fullRecordGapCenterValue - 15120,
    fullRecordGapCenterValue - 14520,
    fullRecordGapCenterValue - 13824,
    fullRecordGapCenterValue - 13750,
    fullRecordGapCenterValue - 13720,
    fullRecordGapCenterValue - 13500,
    fullRecordGapCenterValue - 13440,
    fullRecordGapCenterValue - 13068,
    fullRecordGapCenterValue - 12960,
    fullRecordGapCenterValue - 12672,
    fullRecordGapCenterValue - 12150,
    fullRecordGapCenterValue - 12100,
    fullRecordGapCenterValue - 11760,
    fullRecordGapCenterValue - 11340]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00058_fermat : ∀ n ∈ fullRecordGapRow00058_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03649_not_prime : ¬(recordGapCenter - 39204).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 39204]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03650_not_prime : ¬(recordGapCenter - 38808).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 38808]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03651_not_prime : ¬(recordGapCenter - 38400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 38400]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03652_not_prime : ¬(recordGapCenter - 37422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 37422]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03653_not_prime : ¬(recordGapCenter - 37044).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 37044]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03654_not_prime : ¬(recordGapCenter - 35574).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 35574]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03655_not_prime : ¬(recordGapCenter - 34992).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 34992]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03656_not_prime : ¬(recordGapCenter - 34848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 34848]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03657_not_prime : ¬(recordGapCenter - 34650).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 34650]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03658_not_prime : ¬(recordGapCenter - 33792).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 33792]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03659_not_prime : ¬(recordGapCenter - 33600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 33600]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03660_not_prime : ¬(recordGapCenter - 33264).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 33264]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03661_not_prime : ¬(recordGapCenter - 33000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 33000]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03662_not_prime : ¬(recordGapCenter - 32928).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 32928]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03663_not_prime : ¬(recordGapCenter - 32400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 32400]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03664_not_prime : ¬(recordGapCenter - 31944).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 31944]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03665_not_prime : ¬(recordGapCenter - 31752).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 31752]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03666_not_prime : ¬(recordGapCenter - 31104).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 31104]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03667_not_prime : ¬(recordGapCenter - 30492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 30492]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03668_not_prime : ¬(recordGapCenter - 30184).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 30184]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03669_not_prime : ¬(recordGapCenter - 29700).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 29700]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03670_not_prime : ¬(recordGapCenter - 29568).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 29568]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03671_not_prime : ¬(recordGapCenter - 29400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 29400]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03672_not_prime : ¬(recordGapCenter - 29040).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 29040]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03673_not_prime : ¬(recordGapCenter - 28812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 28812]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03674_not_prime : ¬(recordGapCenter - 28672).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 28672]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03675_not_prime : ¬(recordGapCenter - 27720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 27720]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03676_not_prime : ¬(recordGapCenter - 26880).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 26880]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03677_not_prime : ¬(recordGapCenter - 26730).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 26730]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03678_not_prime : ¬(recordGapCenter - 26460).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 26460]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03679_not_prime : ¬(recordGapCenter - 24640).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 24640]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03680_not_prime : ¬(recordGapCenter - 24192).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 24192]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03681_not_prime : ¬(recordGapCenter - 24010).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 24010]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03682_not_prime : ¬(recordGapCenter - 24000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 24000]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03683_not_prime : ¬(recordGapCenter - 23958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 23958]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03684_not_prime : ¬(recordGapCenter - 23814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 23814]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03685_not_prime : ¬(recordGapCenter - 23520).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 23520]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03686_not_prime : ¬(recordGapCenter - 21870).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 21870]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03687_not_prime : ¬(recordGapCenter - 21600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 21600]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03688_not_prime : ¬(recordGapCenter - 21504).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 21504]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03689_not_prime : ¬(recordGapCenter - 21384).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 21384]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03690_not_prime : ¬(recordGapCenter - 21000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 21000]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03691_not_prime : ¬(recordGapCenter - 20412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 20412]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03692_not_prime : ¬(recordGapCenter - 20160).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 20160]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03693_not_prime : ¬(recordGapCenter - 19600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 19600]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03694_not_prime : ¬(recordGapCenter - 18900).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 18900]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03695_not_prime : ¬(recordGapCenter - 17280).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 17280]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03696_not_prime : ¬(recordGapCenter - 16632).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 16632]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03697_not_prime : ¬(recordGapCenter - 16200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 16200]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03698_not_prime : ¬(recordGapCenter - 16170).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 16170]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03699_not_prime : ¬(recordGapCenter - 15120).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 15120]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03700_not_prime : ¬(recordGapCenter - 14520).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 14520]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03701_not_prime : ¬(recordGapCenter - 13824).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 13824]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03702_not_prime : ¬(recordGapCenter - 13750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 13750]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03703_not_prime : ¬(recordGapCenter - 13720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 13720]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03704_not_prime : ¬(recordGapCenter - 13500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 13500]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03705_not_prime : ¬(recordGapCenter - 13440).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 13440]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03706_not_prime : ¬(recordGapCenter - 13068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 13068]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03707_not_prime : ¬(recordGapCenter - 12960).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 12960]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03708_not_prime : ¬(recordGapCenter - 12672).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 12672]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03709_not_prime : ¬(recordGapCenter - 12150).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 12150]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03710_not_prime : ¬(recordGapCenter - 12100).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 12100]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03711_not_prime : ¬(recordGapCenter - 11760).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 11760]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

theorem fullRecordGapTerm03712_not_prime : ¬(recordGapCenter - 11340).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 11340]
  · apply fullRecordGapRow00058_fermat
    simp [fullRecordGapRow00058_values]

end PrimeFactorUnimodality
