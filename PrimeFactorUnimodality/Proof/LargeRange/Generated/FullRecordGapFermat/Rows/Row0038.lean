import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00038_values : List Nat :=
  [fullRecordGapCenterValue + 568572,
    fullRecordGapCenterValue + 568892,
    fullRecordGapCenterValue + 568970,
    fullRecordGapCenterValue + 569018,
    fullRecordGapCenterValue + 569046,
    fullRecordGapCenterValue + 569090,
    fullRecordGapCenterValue + 569172,
    fullRecordGapCenterValue + 569186,
    fullRecordGapCenterValue + 569210,
    fullRecordGapCenterValue + 569276,
    fullRecordGapCenterValue + 569318,
    fullRecordGapCenterValue + 569336,
    fullRecordGapCenterValue + 569508,
    fullRecordGapCenterValue + 569528,
    fullRecordGapCenterValue + 569570,
    fullRecordGapCenterValue + 569612,
    fullRecordGapCenterValue + 569630,
    fullRecordGapCenterValue + 569678,
    fullRecordGapCenterValue + 569706,
    fullRecordGapCenterValue + 569732,
    fullRecordGapCenterValue + 569762,
    fullRecordGapCenterValue + 569958,
    fullRecordGapCenterValue + 569978,
    fullRecordGapCenterValue + 569990,
    fullRecordGapCenterValue + 570012,
    fullRecordGapCenterValue + 570098,
    fullRecordGapCenterValue + 570242,
    fullRecordGapCenterValue + 570252,
    fullRecordGapCenterValue + 570278,
    fullRecordGapCenterValue + 570356,
    fullRecordGapCenterValue + 570428,
    fullRecordGapCenterValue + 570470,
    fullRecordGapCenterValue + 570476,
    fullRecordGapCenterValue + 570498,
    fullRecordGapCenterValue + 570516,
    fullRecordGapCenterValue + 570558,
    fullRecordGapCenterValue + 570666,
    fullRecordGapCenterValue + 570692,
    fullRecordGapCenterValue + 570756,
    fullRecordGapCenterValue + 570770,
    fullRecordGapCenterValue + 570858,
    fullRecordGapCenterValue + 570890,
    fullRecordGapCenterValue + 571070,
    fullRecordGapCenterValue + 571092,
    fullRecordGapCenterValue + 571112,
    fullRecordGapCenterValue + 571146,
    fullRecordGapCenterValue + 571148,
    fullRecordGapCenterValue + 571190,
    fullRecordGapCenterValue + 571196,
    fullRecordGapCenterValue + 571218,
    fullRecordGapCenterValue + 571278,
    fullRecordGapCenterValue + 571308,
    fullRecordGapCenterValue + 571322,
    fullRecordGapCenterValue + 571386,
    fullRecordGapCenterValue + 571398,
    fullRecordGapCenterValue + 571476,
    fullRecordGapCenterValue + 571496,
    fullRecordGapCenterValue + 571646,
    fullRecordGapCenterValue + 571730,
    fullRecordGapCenterValue + 571832,
    fullRecordGapCenterValue + 571866,
    fullRecordGapCenterValue + 571902,
    fullRecordGapCenterValue + 571916,
    fullRecordGapCenterValue + 571958,
    fullRecordGapCenterValue + 572126,
    fullRecordGapCenterValue + 572210,
    fullRecordGapCenterValue + 572342,
    fullRecordGapCenterValue + 572412,
    fullRecordGapCenterValue + 572478,
    fullRecordGapCenterValue + 572498,
    fullRecordGapCenterValue + 572510,
    fullRecordGapCenterValue + 572532,
    fullRecordGapCenterValue + 572552,
    fullRecordGapCenterValue + 572556,
    fullRecordGapCenterValue + 572646,
    fullRecordGapCenterValue + 572658,
    fullRecordGapCenterValue + 572708,
    fullRecordGapCenterValue + 572786,
    fullRecordGapCenterValue + 572826,
    fullRecordGapCenterValue + 572870,
    fullRecordGapCenterValue + 572996,
    fullRecordGapCenterValue + 573176,
    fullRecordGapCenterValue + 573290,
    fullRecordGapCenterValue + 573332,
    fullRecordGapCenterValue + 573422,
    fullRecordGapCenterValue + 573440,
    fullRecordGapCenterValue + 573486,
    fullRecordGapCenterValue + 573548,
    fullRecordGapCenterValue + 573618,
    fullRecordGapCenterValue + 573626,
    fullRecordGapCenterValue + 573662,
    fullRecordGapCenterValue + 573702,
    fullRecordGapCenterValue + 573708,
    fullRecordGapCenterValue + 573746,
    fullRecordGapCenterValue + 573828,
    fullRecordGapCenterValue + 573890,
    fullRecordGapCenterValue + 573962,
    fullRecordGapCenterValue + 574268,
    fullRecordGapCenterValue + 574278,
    fullRecordGapCenterValue + 574358,
    fullRecordGapCenterValue + 574382,
    fullRecordGapCenterValue + 574386,
    fullRecordGapCenterValue + 574428,
    fullRecordGapCenterValue + 574466,
    fullRecordGapCenterValue + 574502,
    fullRecordGapCenterValue + 574562,
    fullRecordGapCenterValue + 574568,
    fullRecordGapCenterValue + 574572,
    fullRecordGapCenterValue + 574676,
    fullRecordGapCenterValue + 574796,
    fullRecordGapCenterValue + 574806,
    fullRecordGapCenterValue + 574836,
    fullRecordGapCenterValue + 574898,
    fullRecordGapCenterValue + 575048,
    fullRecordGapCenterValue + 575096,
    fullRecordGapCenterValue + 575258,
    fullRecordGapCenterValue + 575268,
    fullRecordGapCenterValue + 575286,
    fullRecordGapCenterValue + 575342,
    fullRecordGapCenterValue + 575466,
    fullRecordGapCenterValue + 575502,
    fullRecordGapCenterValue + 575556,
    fullRecordGapCenterValue + 575576,
    fullRecordGapCenterValue + 575628,
    fullRecordGapCenterValue + 575636,
    fullRecordGapCenterValue + 575642,
    fullRecordGapCenterValue + 575682,
    fullRecordGapCenterValue + 575702,
    fullRecordGapCenterValue + 575726,
    fullRecordGapCenterValue + 575768,
    fullRecordGapCenterValue + 575870,
    fullRecordGapCenterValue + 575922,
    fullRecordGapCenterValue + 575930,
    fullRecordGapCenterValue + 576102,
    fullRecordGapCenterValue + 576276,
    fullRecordGapCenterValue + 576318,
    fullRecordGapCenterValue + 576348,
    fullRecordGapCenterValue + 576362,
    fullRecordGapCenterValue + 576398,
    fullRecordGapCenterValue + 576482,
    fullRecordGapCenterValue + 576698,
    fullRecordGapCenterValue + 576866,
    fullRecordGapCenterValue + 576872,
    fullRecordGapCenterValue + 576942,
    fullRecordGapCenterValue + 576962,
    fullRecordGapCenterValue + 577196,
    fullRecordGapCenterValue + 577292,
    fullRecordGapCenterValue + 577358,
    fullRecordGapCenterValue + 577370,
    fullRecordGapCenterValue + 577398,
    fullRecordGapCenterValue + 577466,
    fullRecordGapCenterValue + 577572,
    fullRecordGapCenterValue + 577578,
    fullRecordGapCenterValue + 577706,
    fullRecordGapCenterValue + 577916,
    fullRecordGapCenterValue + 577938,
    fullRecordGapCenterValue + 577946,
    fullRecordGapCenterValue + 577988,
    fullRecordGapCenterValue + 578030,
    fullRecordGapCenterValue + 578126,
    fullRecordGapCenterValue + 578148,
    fullRecordGapCenterValue + 578316,
    fullRecordGapCenterValue + 578342,
    fullRecordGapCenterValue + 578372,
    fullRecordGapCenterValue + 578390,
    fullRecordGapCenterValue + 578498,
    fullRecordGapCenterValue + 578546,
    fullRecordGapCenterValue + 578742,
    fullRecordGapCenterValue + 578762,
    fullRecordGapCenterValue + 578810,
    fullRecordGapCenterValue + 578846,
    fullRecordGapCenterValue + 578868,
    fullRecordGapCenterValue + 579108,
    fullRecordGapCenterValue + 579162,
    fullRecordGapCenterValue + 579170,
    fullRecordGapCenterValue + 579206,
    fullRecordGapCenterValue + 579356,
    fullRecordGapCenterValue + 579482,
    fullRecordGapCenterValue + 579518,
    fullRecordGapCenterValue + 579596,
    fullRecordGapCenterValue + 579686,
    fullRecordGapCenterValue + 579756,
    fullRecordGapCenterValue + 579848,
    fullRecordGapCenterValue + 579902,
    fullRecordGapCenterValue + 579966,
    fullRecordGapCenterValue + 580002,
    fullRecordGapCenterValue + 580022,
    fullRecordGapCenterValue + 580046,
    fullRecordGapCenterValue + 580226,
    fullRecordGapCenterValue + 580238,
    fullRecordGapCenterValue + 580310,
    fullRecordGapCenterValue + 580386,
    fullRecordGapCenterValue + 580430,
    fullRecordGapCenterValue + 580472,
    fullRecordGapCenterValue + 580578,
    fullRecordGapCenterValue + 580616,
    fullRecordGapCenterValue + 580722,
    fullRecordGapCenterValue + 580772,
    fullRecordGapCenterValue + 580886,
    fullRecordGapCenterValue + 580946,
    fullRecordGapCenterValue + 581018,
    fullRecordGapCenterValue + 581042,
    fullRecordGapCenterValue + 581246,
    fullRecordGapCenterValue + 581388,
    fullRecordGapCenterValue + 581432,
    fullRecordGapCenterValue + 581442,
    fullRecordGapCenterValue + 581466,
    fullRecordGapCenterValue + 581606,
    fullRecordGapCenterValue + 581732,
    fullRecordGapCenterValue + 581738,
    fullRecordGapCenterValue + 581772,
    fullRecordGapCenterValue + 581892,
    fullRecordGapCenterValue + 581942,
    fullRecordGapCenterValue + 581948,
    fullRecordGapCenterValue + 581982,
    fullRecordGapCenterValue + 582068,
    fullRecordGapCenterValue + 582086,
    fullRecordGapCenterValue + 582110,
    fullRecordGapCenterValue + 582120,
    fullRecordGapCenterValue + 582206,
    fullRecordGapCenterValue + 582356,
    fullRecordGapCenterValue + 582396,
    fullRecordGapCenterValue + 582398,
    fullRecordGapCenterValue + 582486,
    fullRecordGapCenterValue + 582548,
    fullRecordGapCenterValue + 582662,
    fullRecordGapCenterValue + 582702,
    fullRecordGapCenterValue + 582746,
    fullRecordGapCenterValue + 582836,
    fullRecordGapCenterValue + 582872,
    fullRecordGapCenterValue + 582878,
    fullRecordGapCenterValue + 582906,
    fullRecordGapCenterValue + 582962,
    fullRecordGapCenterValue + 583068,
    fullRecordGapCenterValue + 583112,
    fullRecordGapCenterValue + 583200,
    fullRecordGapCenterValue + 583278,
    fullRecordGapCenterValue + 583292,
    fullRecordGapCenterValue + 583322,
    fullRecordGapCenterValue + 583332,
    fullRecordGapCenterValue + 583382,
    fullRecordGapCenterValue + 583592,
    fullRecordGapCenterValue + 583706,
    fullRecordGapCenterValue + 583910,
    fullRecordGapCenterValue + 584138,
    fullRecordGapCenterValue + 584186,
    fullRecordGapCenterValue + 584202,
    fullRecordGapCenterValue + 584238,
    fullRecordGapCenterValue + 584252,
    fullRecordGapCenterValue + 584270,
    fullRecordGapCenterValue + 584286,
    fullRecordGapCenterValue + 584312,
    fullRecordGapCenterValue + 584322,
    fullRecordGapCenterValue + 584390,
    fullRecordGapCenterValue + 584462,
    fullRecordGapCenterValue + 584468]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00038_fermat : ∀ n ∈ fullRecordGapRow00038_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09473_not_prime : ¬(recordGapCenter + 568572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 568572]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09474_not_prime : ¬(recordGapCenter + 568892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 568892]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09475_not_prime : ¬(recordGapCenter + 568970).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 568970]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09476_not_prime : ¬(recordGapCenter + 569018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569018]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09477_not_prime : ¬(recordGapCenter + 569046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569046]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09478_not_prime : ¬(recordGapCenter + 569090).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569090]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09479_not_prime : ¬(recordGapCenter + 569172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569172]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09480_not_prime : ¬(recordGapCenter + 569186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569186]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09481_not_prime : ¬(recordGapCenter + 569210).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569210]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09482_not_prime : ¬(recordGapCenter + 569276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569276]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09483_not_prime : ¬(recordGapCenter + 569318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569318]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09484_not_prime : ¬(recordGapCenter + 569336).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569336]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09485_not_prime : ¬(recordGapCenter + 569508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569508]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09486_not_prime : ¬(recordGapCenter + 569528).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569528]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09487_not_prime : ¬(recordGapCenter + 569570).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569570]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09488_not_prime : ¬(recordGapCenter + 569612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569612]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09489_not_prime : ¬(recordGapCenter + 569630).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569630]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09490_not_prime : ¬(recordGapCenter + 569678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569678]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09491_not_prime : ¬(recordGapCenter + 569706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569706]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09492_not_prime : ¬(recordGapCenter + 569732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569732]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09493_not_prime : ¬(recordGapCenter + 569762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569762]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09494_not_prime : ¬(recordGapCenter + 569958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569958]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09495_not_prime : ¬(recordGapCenter + 569978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569978]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09496_not_prime : ¬(recordGapCenter + 569990).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569990]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09497_not_prime : ¬(recordGapCenter + 570012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570012]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09498_not_prime : ¬(recordGapCenter + 570098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570098]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09499_not_prime : ¬(recordGapCenter + 570242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570242]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09500_not_prime : ¬(recordGapCenter + 570252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570252]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09501_not_prime : ¬(recordGapCenter + 570278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570278]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09502_not_prime : ¬(recordGapCenter + 570356).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570356]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09503_not_prime : ¬(recordGapCenter + 570428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570428]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09504_not_prime : ¬(recordGapCenter + 570470).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570470]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09505_not_prime : ¬(recordGapCenter + 570476).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570476]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09506_not_prime : ¬(recordGapCenter + 570498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570498]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09507_not_prime : ¬(recordGapCenter + 570516).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570516]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09508_not_prime : ¬(recordGapCenter + 570558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570558]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09509_not_prime : ¬(recordGapCenter + 570666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570666]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09510_not_prime : ¬(recordGapCenter + 570692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570692]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09511_not_prime : ¬(recordGapCenter + 570756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570756]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09512_not_prime : ¬(recordGapCenter + 570770).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570770]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09513_not_prime : ¬(recordGapCenter + 570858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570858]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09514_not_prime : ¬(recordGapCenter + 570890).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570890]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09515_not_prime : ¬(recordGapCenter + 571070).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571070]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09516_not_prime : ¬(recordGapCenter + 571092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571092]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09517_not_prime : ¬(recordGapCenter + 571112).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571112]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09518_not_prime : ¬(recordGapCenter + 571146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571146]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09519_not_prime : ¬(recordGapCenter + 571148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571148]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09520_not_prime : ¬(recordGapCenter + 571190).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571190]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09521_not_prime : ¬(recordGapCenter + 571196).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571196]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09522_not_prime : ¬(recordGapCenter + 571218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571218]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09523_not_prime : ¬(recordGapCenter + 571278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571278]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09524_not_prime : ¬(recordGapCenter + 571308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571308]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09525_not_prime : ¬(recordGapCenter + 571322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571322]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09526_not_prime : ¬(recordGapCenter + 571386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571386]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09527_not_prime : ¬(recordGapCenter + 571398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571398]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09528_not_prime : ¬(recordGapCenter + 571476).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571476]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09529_not_prime : ¬(recordGapCenter + 571496).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571496]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09530_not_prime : ¬(recordGapCenter + 571646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571646]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09531_not_prime : ¬(recordGapCenter + 571730).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571730]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09532_not_prime : ¬(recordGapCenter + 571832).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571832]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09533_not_prime : ¬(recordGapCenter + 571866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571866]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09534_not_prime : ¬(recordGapCenter + 571902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571902]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09535_not_prime : ¬(recordGapCenter + 571916).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571916]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09536_not_prime : ¬(recordGapCenter + 571958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571958]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09537_not_prime : ¬(recordGapCenter + 572126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572126]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09538_not_prime : ¬(recordGapCenter + 572210).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572210]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09539_not_prime : ¬(recordGapCenter + 572342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572342]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09540_not_prime : ¬(recordGapCenter + 572412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572412]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09541_not_prime : ¬(recordGapCenter + 572478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572478]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09542_not_prime : ¬(recordGapCenter + 572498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572498]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09543_not_prime : ¬(recordGapCenter + 572510).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572510]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09544_not_prime : ¬(recordGapCenter + 572532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572532]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09545_not_prime : ¬(recordGapCenter + 572552).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572552]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09546_not_prime : ¬(recordGapCenter + 572556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572556]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09547_not_prime : ¬(recordGapCenter + 572646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572646]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09548_not_prime : ¬(recordGapCenter + 572658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572658]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09549_not_prime : ¬(recordGapCenter + 572708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572708]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09550_not_prime : ¬(recordGapCenter + 572786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572786]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09551_not_prime : ¬(recordGapCenter + 572826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572826]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09552_not_prime : ¬(recordGapCenter + 572870).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572870]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09553_not_prime : ¬(recordGapCenter + 572996).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572996]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09554_not_prime : ¬(recordGapCenter + 573176).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573176]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09555_not_prime : ¬(recordGapCenter + 573290).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573290]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09556_not_prime : ¬(recordGapCenter + 573332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573332]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09557_not_prime : ¬(recordGapCenter + 573422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573422]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09558_not_prime : ¬(recordGapCenter + 573440).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573440]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09559_not_prime : ¬(recordGapCenter + 573486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573486]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09560_not_prime : ¬(recordGapCenter + 573548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573548]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09561_not_prime : ¬(recordGapCenter + 573618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573618]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09562_not_prime : ¬(recordGapCenter + 573626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573626]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09563_not_prime : ¬(recordGapCenter + 573662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573662]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09564_not_prime : ¬(recordGapCenter + 573702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573702]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09565_not_prime : ¬(recordGapCenter + 573708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573708]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09566_not_prime : ¬(recordGapCenter + 573746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573746]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09567_not_prime : ¬(recordGapCenter + 573828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573828]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09568_not_prime : ¬(recordGapCenter + 573890).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573890]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09569_not_prime : ¬(recordGapCenter + 573962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573962]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09570_not_prime : ¬(recordGapCenter + 574268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574268]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09571_not_prime : ¬(recordGapCenter + 574278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574278]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09572_not_prime : ¬(recordGapCenter + 574358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574358]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09573_not_prime : ¬(recordGapCenter + 574382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574382]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09574_not_prime : ¬(recordGapCenter + 574386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574386]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09575_not_prime : ¬(recordGapCenter + 574428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574428]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09576_not_prime : ¬(recordGapCenter + 574466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574466]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09577_not_prime : ¬(recordGapCenter + 574502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574502]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09578_not_prime : ¬(recordGapCenter + 574562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574562]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09579_not_prime : ¬(recordGapCenter + 574568).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574568]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09580_not_prime : ¬(recordGapCenter + 574572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574572]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09581_not_prime : ¬(recordGapCenter + 574676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574676]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09582_not_prime : ¬(recordGapCenter + 574796).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574796]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09583_not_prime : ¬(recordGapCenter + 574806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574806]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09584_not_prime : ¬(recordGapCenter + 574836).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574836]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09585_not_prime : ¬(recordGapCenter + 574898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574898]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09586_not_prime : ¬(recordGapCenter + 575048).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575048]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09587_not_prime : ¬(recordGapCenter + 575096).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575096]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09588_not_prime : ¬(recordGapCenter + 575258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575258]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09589_not_prime : ¬(recordGapCenter + 575268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575268]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09590_not_prime : ¬(recordGapCenter + 575286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575286]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09591_not_prime : ¬(recordGapCenter + 575342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575342]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09592_not_prime : ¬(recordGapCenter + 575466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575466]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09593_not_prime : ¬(recordGapCenter + 575502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575502]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09594_not_prime : ¬(recordGapCenter + 575556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575556]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09595_not_prime : ¬(recordGapCenter + 575576).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575576]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09596_not_prime : ¬(recordGapCenter + 575628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575628]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09597_not_prime : ¬(recordGapCenter + 575636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575636]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09598_not_prime : ¬(recordGapCenter + 575642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575642]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09599_not_prime : ¬(recordGapCenter + 575682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575682]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09600_not_prime : ¬(recordGapCenter + 575702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575702]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09601_not_prime : ¬(recordGapCenter + 575726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575726]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09602_not_prime : ¬(recordGapCenter + 575768).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575768]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09603_not_prime : ¬(recordGapCenter + 575870).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575870]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09604_not_prime : ¬(recordGapCenter + 575922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575922]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09605_not_prime : ¬(recordGapCenter + 575930).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575930]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09606_not_prime : ¬(recordGapCenter + 576102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 576102]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09607_not_prime : ¬(recordGapCenter + 576276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 576276]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09608_not_prime : ¬(recordGapCenter + 576318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 576318]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09609_not_prime : ¬(recordGapCenter + 576348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 576348]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09610_not_prime : ¬(recordGapCenter + 576362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 576362]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09611_not_prime : ¬(recordGapCenter + 576398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 576398]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09612_not_prime : ¬(recordGapCenter + 576482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 576482]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09613_not_prime : ¬(recordGapCenter + 576698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 576698]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09614_not_prime : ¬(recordGapCenter + 576866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 576866]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09615_not_prime : ¬(recordGapCenter + 576872).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 576872]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09616_not_prime : ¬(recordGapCenter + 576942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 576942]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09617_not_prime : ¬(recordGapCenter + 576962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 576962]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09618_not_prime : ¬(recordGapCenter + 577196).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 577196]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09619_not_prime : ¬(recordGapCenter + 577292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 577292]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09620_not_prime : ¬(recordGapCenter + 577358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 577358]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09621_not_prime : ¬(recordGapCenter + 577370).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 577370]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09622_not_prime : ¬(recordGapCenter + 577398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 577398]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09623_not_prime : ¬(recordGapCenter + 577466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 577466]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09624_not_prime : ¬(recordGapCenter + 577572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 577572]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09625_not_prime : ¬(recordGapCenter + 577578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 577578]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09626_not_prime : ¬(recordGapCenter + 577706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 577706]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09627_not_prime : ¬(recordGapCenter + 577916).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 577916]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09628_not_prime : ¬(recordGapCenter + 577938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 577938]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09629_not_prime : ¬(recordGapCenter + 577946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 577946]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09630_not_prime : ¬(recordGapCenter + 577988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 577988]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09631_not_prime : ¬(recordGapCenter + 578030).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578030]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09632_not_prime : ¬(recordGapCenter + 578126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578126]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09633_not_prime : ¬(recordGapCenter + 578148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578148]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09634_not_prime : ¬(recordGapCenter + 578316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578316]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09635_not_prime : ¬(recordGapCenter + 578342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578342]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09636_not_prime : ¬(recordGapCenter + 578372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578372]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09637_not_prime : ¬(recordGapCenter + 578390).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578390]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09638_not_prime : ¬(recordGapCenter + 578498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578498]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09639_not_prime : ¬(recordGapCenter + 578546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578546]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09640_not_prime : ¬(recordGapCenter + 578742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578742]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09641_not_prime : ¬(recordGapCenter + 578762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578762]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09642_not_prime : ¬(recordGapCenter + 578810).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578810]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09643_not_prime : ¬(recordGapCenter + 578846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578846]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09644_not_prime : ¬(recordGapCenter + 578868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578868]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09645_not_prime : ¬(recordGapCenter + 579108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 579108]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09646_not_prime : ¬(recordGapCenter + 579162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 579162]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09647_not_prime : ¬(recordGapCenter + 579170).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 579170]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09648_not_prime : ¬(recordGapCenter + 579206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 579206]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09649_not_prime : ¬(recordGapCenter + 579356).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 579356]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09650_not_prime : ¬(recordGapCenter + 579482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 579482]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09651_not_prime : ¬(recordGapCenter + 579518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 579518]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09652_not_prime : ¬(recordGapCenter + 579596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 579596]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09653_not_prime : ¬(recordGapCenter + 579686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 579686]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09654_not_prime : ¬(recordGapCenter + 579756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 579756]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09655_not_prime : ¬(recordGapCenter + 579848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 579848]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09656_not_prime : ¬(recordGapCenter + 579902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 579902]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09657_not_prime : ¬(recordGapCenter + 579966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 579966]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09658_not_prime : ¬(recordGapCenter + 580002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580002]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09659_not_prime : ¬(recordGapCenter + 580022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580022]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09660_not_prime : ¬(recordGapCenter + 580046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580046]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09661_not_prime : ¬(recordGapCenter + 580226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580226]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09662_not_prime : ¬(recordGapCenter + 580238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580238]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09663_not_prime : ¬(recordGapCenter + 580310).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580310]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09664_not_prime : ¬(recordGapCenter + 580386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580386]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09665_not_prime : ¬(recordGapCenter + 580430).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580430]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09666_not_prime : ¬(recordGapCenter + 580472).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580472]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09667_not_prime : ¬(recordGapCenter + 580578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580578]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09668_not_prime : ¬(recordGapCenter + 580616).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580616]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09669_not_prime : ¬(recordGapCenter + 580722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580722]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09670_not_prime : ¬(recordGapCenter + 580772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580772]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09671_not_prime : ¬(recordGapCenter + 580886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580886]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09672_not_prime : ¬(recordGapCenter + 580946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580946]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09673_not_prime : ¬(recordGapCenter + 581018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581018]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09674_not_prime : ¬(recordGapCenter + 581042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581042]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09675_not_prime : ¬(recordGapCenter + 581246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581246]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09676_not_prime : ¬(recordGapCenter + 581388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581388]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09677_not_prime : ¬(recordGapCenter + 581432).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581432]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09678_not_prime : ¬(recordGapCenter + 581442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581442]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09679_not_prime : ¬(recordGapCenter + 581466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581466]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09680_not_prime : ¬(recordGapCenter + 581606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581606]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09681_not_prime : ¬(recordGapCenter + 581732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581732]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09682_not_prime : ¬(recordGapCenter + 581738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581738]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09683_not_prime : ¬(recordGapCenter + 581772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581772]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09684_not_prime : ¬(recordGapCenter + 581892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581892]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09685_not_prime : ¬(recordGapCenter + 581942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581942]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09686_not_prime : ¬(recordGapCenter + 581948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581948]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09687_not_prime : ¬(recordGapCenter + 581982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581982]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09688_not_prime : ¬(recordGapCenter + 582068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582068]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09689_not_prime : ¬(recordGapCenter + 582086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582086]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09690_not_prime : ¬(recordGapCenter + 582110).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582110]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09691_not_prime : ¬(recordGapCenter + 582120).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582120]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09692_not_prime : ¬(recordGapCenter + 582206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582206]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09693_not_prime : ¬(recordGapCenter + 582356).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582356]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09694_not_prime : ¬(recordGapCenter + 582396).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582396]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09695_not_prime : ¬(recordGapCenter + 582398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582398]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09696_not_prime : ¬(recordGapCenter + 582486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582486]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09697_not_prime : ¬(recordGapCenter + 582548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582548]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09698_not_prime : ¬(recordGapCenter + 582662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582662]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09699_not_prime : ¬(recordGapCenter + 582702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582702]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09700_not_prime : ¬(recordGapCenter + 582746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582746]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09701_not_prime : ¬(recordGapCenter + 582836).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582836]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09702_not_prime : ¬(recordGapCenter + 582872).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582872]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09703_not_prime : ¬(recordGapCenter + 582878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582878]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09704_not_prime : ¬(recordGapCenter + 582906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582906]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09705_not_prime : ¬(recordGapCenter + 582962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582962]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09706_not_prime : ¬(recordGapCenter + 583068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 583068]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09707_not_prime : ¬(recordGapCenter + 583112).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 583112]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09708_not_prime : ¬(recordGapCenter + 583200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 583200]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09709_not_prime : ¬(recordGapCenter + 583278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 583278]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09710_not_prime : ¬(recordGapCenter + 583292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 583292]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09711_not_prime : ¬(recordGapCenter + 583322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 583322]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09712_not_prime : ¬(recordGapCenter + 583332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 583332]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09713_not_prime : ¬(recordGapCenter + 583382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 583382]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09714_not_prime : ¬(recordGapCenter + 583592).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 583592]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09715_not_prime : ¬(recordGapCenter + 583706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 583706]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09716_not_prime : ¬(recordGapCenter + 583910).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 583910]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09717_not_prime : ¬(recordGapCenter + 584138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584138]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09718_not_prime : ¬(recordGapCenter + 584186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584186]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09719_not_prime : ¬(recordGapCenter + 584202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584202]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09720_not_prime : ¬(recordGapCenter + 584238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584238]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09721_not_prime : ¬(recordGapCenter + 584252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584252]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09722_not_prime : ¬(recordGapCenter + 584270).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584270]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09723_not_prime : ¬(recordGapCenter + 584286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584286]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09724_not_prime : ¬(recordGapCenter + 584312).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584312]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09725_not_prime : ¬(recordGapCenter + 584322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584322]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09726_not_prime : ¬(recordGapCenter + 584390).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584390]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09727_not_prime : ¬(recordGapCenter + 584462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584462]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm09728_not_prime : ¬(recordGapCenter + 584468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584468]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

end PrimeFactorUnimodality
