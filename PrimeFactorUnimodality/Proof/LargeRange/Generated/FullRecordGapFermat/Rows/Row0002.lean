import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00002_values : List Nat :=
  [fullRecordGapCenterValue - 435600,
    fullRecordGapCenterValue - 435354,
    fullRecordGapCenterValue - 435322,
    fullRecordGapCenterValue - 435304,
    fullRecordGapCenterValue - 435154,
    fullRecordGapCenterValue - 435118,
    fullRecordGapCenterValue - 434998,
    fullRecordGapCenterValue - 434982,
    fullRecordGapCenterValue - 434958,
    fullRecordGapCenterValue - 434914,
    fullRecordGapCenterValue - 434802,
    fullRecordGapCenterValue - 434734,
    fullRecordGapCenterValue - 434572,
    fullRecordGapCenterValue - 434524,
    fullRecordGapCenterValue - 434458,
    fullRecordGapCenterValue - 434410,
    fullRecordGapCenterValue - 434338,
    fullRecordGapCenterValue - 434314,
    fullRecordGapCenterValue - 434298,
    fullRecordGapCenterValue - 434242,
    fullRecordGapCenterValue - 434202,
    fullRecordGapCenterValue - 434164,
    fullRecordGapCenterValue - 434002,
    fullRecordGapCenterValue - 433990,
    fullRecordGapCenterValue - 433894,
    fullRecordGapCenterValue - 433878,
    fullRecordGapCenterValue - 433702,
    fullRecordGapCenterValue - 433684,
    fullRecordGapCenterValue - 433614,
    fullRecordGapCenterValue - 433372,
    fullRecordGapCenterValue - 433282,
    fullRecordGapCenterValue - 433138,
    fullRecordGapCenterValue - 433018,
    fullRecordGapCenterValue - 433002,
    fullRecordGapCenterValue - 432988,
    fullRecordGapCenterValue - 432910,
    fullRecordGapCenterValue - 432868,
    fullRecordGapCenterValue - 432862,
    fullRecordGapCenterValue - 432844,
    fullRecordGapCenterValue - 432802,
    fullRecordGapCenterValue - 432742,
    fullRecordGapCenterValue - 432472,
    fullRecordGapCenterValue - 432462,
    fullRecordGapCenterValue - 432358,
    fullRecordGapCenterValue - 432318,
    fullRecordGapCenterValue - 432070,
    fullRecordGapCenterValue - 432010,
    fullRecordGapCenterValue - 432000,
    fullRecordGapCenterValue - 431962,
    fullRecordGapCenterValue - 431944,
    fullRecordGapCenterValue - 431898,
    fullRecordGapCenterValue - 431890,
    fullRecordGapCenterValue - 431778,
    fullRecordGapCenterValue - 431764,
    fullRecordGapCenterValue - 431682,
    fullRecordGapCenterValue - 431608,
    fullRecordGapCenterValue - 431590,
    fullRecordGapCenterValue - 431394,
    fullRecordGapCenterValue - 431308,
    fullRecordGapCenterValue - 431092,
    fullRecordGapCenterValue - 431058,
    fullRecordGapCenterValue - 431014,
    fullRecordGapCenterValue - 430888,
    fullRecordGapCenterValue - 430854,
    fullRecordGapCenterValue - 430842,
    fullRecordGapCenterValue - 430834,
    fullRecordGapCenterValue - 430792,
    fullRecordGapCenterValue - 430762,
    fullRecordGapCenterValue - 430734,
    fullRecordGapCenterValue - 430684,
    fullRecordGapCenterValue - 430594,
    fullRecordGapCenterValue - 430558,
    fullRecordGapCenterValue - 430552,
    fullRecordGapCenterValue - 430264,
    fullRecordGapCenterValue - 430174,
    fullRecordGapCenterValue - 430072,
    fullRecordGapCenterValue - 429798,
    fullRecordGapCenterValue - 429622,
    fullRecordGapCenterValue - 429544,
    fullRecordGapCenterValue - 429508,
    fullRecordGapCenterValue - 429414,
    fullRecordGapCenterValue - 429222,
    fullRecordGapCenterValue - 429064,
    fullRecordGapCenterValue - 428998,
    fullRecordGapCenterValue - 428878,
    fullRecordGapCenterValue - 428788,
    fullRecordGapCenterValue - 428782,
    fullRecordGapCenterValue - 428728,
    fullRecordGapCenterValue - 428658,
    fullRecordGapCenterValue - 428622,
    fullRecordGapCenterValue - 428334,
    fullRecordGapCenterValue - 427998,
    fullRecordGapCenterValue - 427972,
    fullRecordGapCenterValue - 427962,
    fullRecordGapCenterValue - 427902,
    fullRecordGapCenterValue - 427894,
    fullRecordGapCenterValue - 427858,
    fullRecordGapCenterValue - 427852,
    fullRecordGapCenterValue - 427828,
    fullRecordGapCenterValue - 427762,
    fullRecordGapCenterValue - 427528,
    fullRecordGapCenterValue - 427474,
    fullRecordGapCenterValue - 427468,
    fullRecordGapCenterValue - 427444,
    fullRecordGapCenterValue - 427282,
    fullRecordGapCenterValue - 427254,
    fullRecordGapCenterValue - 427012,
    fullRecordGapCenterValue - 426982,
    fullRecordGapCenterValue - 426934,
    fullRecordGapCenterValue - 426898,
    fullRecordGapCenterValue - 426888,
    fullRecordGapCenterValue - 426772,
    fullRecordGapCenterValue - 426724,
    fullRecordGapCenterValue - 426534,
    fullRecordGapCenterValue - 426508,
    fullRecordGapCenterValue - 426484,
    fullRecordGapCenterValue - 426418,
    fullRecordGapCenterValue - 426414,
    fullRecordGapCenterValue - 426354,
    fullRecordGapCenterValue - 426138,
    fullRecordGapCenterValue - 426124,
    fullRecordGapCenterValue - 426004,
    fullRecordGapCenterValue - 425994,
    fullRecordGapCenterValue - 425974,
    fullRecordGapCenterValue - 425962,
    fullRecordGapCenterValue - 425848,
    fullRecordGapCenterValue - 425694,
    fullRecordGapCenterValue - 425512,
    fullRecordGapCenterValue - 425428,
    fullRecordGapCenterValue - 425338,
    fullRecordGapCenterValue - 425254,
    fullRecordGapCenterValue - 425250,
    fullRecordGapCenterValue - 425212,
    fullRecordGapCenterValue - 425164,
    fullRecordGapCenterValue - 425122,
    fullRecordGapCenterValue - 425094,
    fullRecordGapCenterValue - 425058,
    fullRecordGapCenterValue - 424828,
    fullRecordGapCenterValue - 424744,
    fullRecordGapCenterValue - 424738,
    fullRecordGapCenterValue - 424552,
    fullRecordGapCenterValue - 424492,
    fullRecordGapCenterValue - 424374,
    fullRecordGapCenterValue - 424282,
    fullRecordGapCenterValue - 424254,
    fullRecordGapCenterValue - 424234,
    fullRecordGapCenterValue - 424132,
    fullRecordGapCenterValue - 424114,
    fullRecordGapCenterValue - 423868,
    fullRecordGapCenterValue - 423784,
    fullRecordGapCenterValue - 423762,
    fullRecordGapCenterValue - 423622,
    fullRecordGapCenterValue - 423562,
    fullRecordGapCenterValue - 423532,
    fullRecordGapCenterValue - 423498,
    fullRecordGapCenterValue - 423454,
    fullRecordGapCenterValue - 423360,
    fullRecordGapCenterValue - 423352,
    fullRecordGapCenterValue - 423268,
    fullRecordGapCenterValue - 423222,
    fullRecordGapCenterValue - 423142,
    fullRecordGapCenterValue - 422854,
    fullRecordGapCenterValue - 422742,
    fullRecordGapCenterValue - 422574,
    fullRecordGapCenterValue - 422538,
    fullRecordGapCenterValue - 422482,
    fullRecordGapCenterValue - 422428,
    fullRecordGapCenterValue - 422398,
    fullRecordGapCenterValue - 422274,
    fullRecordGapCenterValue - 422194,
    fullRecordGapCenterValue - 422152,
    fullRecordGapCenterValue - 422068,
    fullRecordGapCenterValue - 422014,
    fullRecordGapCenterValue - 421878,
    fullRecordGapCenterValue - 421864,
    fullRecordGapCenterValue - 421738,
    fullRecordGapCenterValue - 421734,
    fullRecordGapCenterValue - 421714,
    fullRecordGapCenterValue - 421588,
    fullRecordGapCenterValue - 421522,
    fullRecordGapCenterValue - 421438,
    fullRecordGapCenterValue - 421242,
    fullRecordGapCenterValue - 421108,
    fullRecordGapCenterValue - 421054,
    fullRecordGapCenterValue - 421048,
    fullRecordGapCenterValue - 420982,
    fullRecordGapCenterValue - 420922,
    fullRecordGapCenterValue - 420874,
    fullRecordGapCenterValue - 420814,
    fullRecordGapCenterValue - 420802,
    fullRecordGapCenterValue - 420718,
    fullRecordGapCenterValue - 420664,
    fullRecordGapCenterValue - 420474,
    fullRecordGapCenterValue - 420388,
    fullRecordGapCenterValue - 420382,
    fullRecordGapCenterValue - 420262,
    fullRecordGapCenterValue - 420234,
    fullRecordGapCenterValue - 420088,
    fullRecordGapCenterValue - 420054,
    fullRecordGapCenterValue - 420018,
    fullRecordGapCenterValue - 420000,
    fullRecordGapCenterValue - 419982,
    fullRecordGapCenterValue - 419788,
    fullRecordGapCenterValue - 419674,
    fullRecordGapCenterValue - 419578,
    fullRecordGapCenterValue - 419464,
    fullRecordGapCenterValue - 419262,
    fullRecordGapCenterValue - 419194,
    fullRecordGapCenterValue - 419158,
    fullRecordGapCenterValue - 419142,
    fullRecordGapCenterValue - 419134,
    fullRecordGapCenterValue - 419092,
    fullRecordGapCenterValue - 419032,
    fullRecordGapCenterValue - 418974,
    fullRecordGapCenterValue - 418962,
    fullRecordGapCenterValue - 418942,
    fullRecordGapCenterValue - 418918,
    fullRecordGapCenterValue - 418732,
    fullRecordGapCenterValue - 418714,
    fullRecordGapCenterValue - 418504,
    fullRecordGapCenterValue - 418408,
    fullRecordGapCenterValue - 418402,
    fullRecordGapCenterValue - 418372,
    fullRecordGapCenterValue - 418108,
    fullRecordGapCenterValue - 418024,
    fullRecordGapCenterValue - 417892,
    fullRecordGapCenterValue - 417778,
    fullRecordGapCenterValue - 417598,
    fullRecordGapCenterValue - 417532,
    fullRecordGapCenterValue - 417442,
    fullRecordGapCenterValue - 417244,
    fullRecordGapCenterValue - 417022,
    fullRecordGapCenterValue - 416994,
    fullRecordGapCenterValue - 416824,
    fullRecordGapCenterValue - 416818,
    fullRecordGapCenterValue - 416758,
    fullRecordGapCenterValue - 416742,
    fullRecordGapCenterValue - 416562,
    fullRecordGapCenterValue - 416554,
    fullRecordGapCenterValue - 416434,
    fullRecordGapCenterValue - 416418,
    fullRecordGapCenterValue - 416334,
    fullRecordGapCenterValue - 416212,
    fullRecordGapCenterValue - 416022,
    fullRecordGapCenterValue - 415942,
    fullRecordGapCenterValue - 415924,
    fullRecordGapCenterValue - 415894,
    fullRecordGapCenterValue - 415800,
    fullRecordGapCenterValue - 415768,
    fullRecordGapCenterValue - 415594,
    fullRecordGapCenterValue - 415468,
    fullRecordGapCenterValue - 415434,
    fullRecordGapCenterValue - 415432,
    fullRecordGapCenterValue - 415258,
    fullRecordGapCenterValue - 415204,
    fullRecordGapCenterValue - 414978]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00002_fermat : ∀ n ∈ fullRecordGapRow00002_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00257_not_prime : ¬(recordGapCenter - 435600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 435600]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00258_not_prime : ¬(recordGapCenter - 435354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 435354]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00259_not_prime : ¬(recordGapCenter - 435322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 435322]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00260_not_prime : ¬(recordGapCenter - 435304).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 435304]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00261_not_prime : ¬(recordGapCenter - 435154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 435154]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00262_not_prime : ¬(recordGapCenter - 435118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 435118]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00263_not_prime : ¬(recordGapCenter - 434998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434998]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00264_not_prime : ¬(recordGapCenter - 434982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434982]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00265_not_prime : ¬(recordGapCenter - 434958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434958]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00266_not_prime : ¬(recordGapCenter - 434914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434914]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00267_not_prime : ¬(recordGapCenter - 434802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434802]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00268_not_prime : ¬(recordGapCenter - 434734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434734]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00269_not_prime : ¬(recordGapCenter - 434572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434572]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00270_not_prime : ¬(recordGapCenter - 434524).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434524]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00271_not_prime : ¬(recordGapCenter - 434458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434458]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00272_not_prime : ¬(recordGapCenter - 434410).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434410]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00273_not_prime : ¬(recordGapCenter - 434338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434338]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00274_not_prime : ¬(recordGapCenter - 434314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434314]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00275_not_prime : ¬(recordGapCenter - 434298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434298]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00276_not_prime : ¬(recordGapCenter - 434242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434242]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00277_not_prime : ¬(recordGapCenter - 434202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434202]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00278_not_prime : ¬(recordGapCenter - 434164).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434164]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00279_not_prime : ¬(recordGapCenter - 434002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434002]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00280_not_prime : ¬(recordGapCenter - 433990).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 433990]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00281_not_prime : ¬(recordGapCenter - 433894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 433894]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00282_not_prime : ¬(recordGapCenter - 433878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 433878]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00283_not_prime : ¬(recordGapCenter - 433702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 433702]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00284_not_prime : ¬(recordGapCenter - 433684).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 433684]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00285_not_prime : ¬(recordGapCenter - 433614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 433614]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00286_not_prime : ¬(recordGapCenter - 433372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 433372]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00287_not_prime : ¬(recordGapCenter - 433282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 433282]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00288_not_prime : ¬(recordGapCenter - 433138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 433138]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00289_not_prime : ¬(recordGapCenter - 433018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 433018]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00290_not_prime : ¬(recordGapCenter - 433002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 433002]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00291_not_prime : ¬(recordGapCenter - 432988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432988]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00292_not_prime : ¬(recordGapCenter - 432910).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432910]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00293_not_prime : ¬(recordGapCenter - 432868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432868]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00294_not_prime : ¬(recordGapCenter - 432862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432862]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00295_not_prime : ¬(recordGapCenter - 432844).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432844]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00296_not_prime : ¬(recordGapCenter - 432802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432802]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00297_not_prime : ¬(recordGapCenter - 432742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432742]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00298_not_prime : ¬(recordGapCenter - 432472).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432472]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00299_not_prime : ¬(recordGapCenter - 432462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432462]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00300_not_prime : ¬(recordGapCenter - 432358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432358]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00301_not_prime : ¬(recordGapCenter - 432318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432318]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00302_not_prime : ¬(recordGapCenter - 432070).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432070]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00303_not_prime : ¬(recordGapCenter - 432010).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432010]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00304_not_prime : ¬(recordGapCenter - 432000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432000]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00305_not_prime : ¬(recordGapCenter - 431962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431962]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00306_not_prime : ¬(recordGapCenter - 431944).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431944]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00307_not_prime : ¬(recordGapCenter - 431898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431898]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00308_not_prime : ¬(recordGapCenter - 431890).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431890]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00309_not_prime : ¬(recordGapCenter - 431778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431778]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00310_not_prime : ¬(recordGapCenter - 431764).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431764]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00311_not_prime : ¬(recordGapCenter - 431682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431682]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00312_not_prime : ¬(recordGapCenter - 431608).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431608]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00313_not_prime : ¬(recordGapCenter - 431590).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431590]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00314_not_prime : ¬(recordGapCenter - 431394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431394]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00315_not_prime : ¬(recordGapCenter - 431308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431308]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00316_not_prime : ¬(recordGapCenter - 431092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431092]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00317_not_prime : ¬(recordGapCenter - 431058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431058]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00318_not_prime : ¬(recordGapCenter - 431014).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431014]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00319_not_prime : ¬(recordGapCenter - 430888).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430888]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00320_not_prime : ¬(recordGapCenter - 430854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430854]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00321_not_prime : ¬(recordGapCenter - 430842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430842]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00322_not_prime : ¬(recordGapCenter - 430834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430834]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00323_not_prime : ¬(recordGapCenter - 430792).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430792]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00324_not_prime : ¬(recordGapCenter - 430762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430762]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00325_not_prime : ¬(recordGapCenter - 430734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430734]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00326_not_prime : ¬(recordGapCenter - 430684).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430684]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00327_not_prime : ¬(recordGapCenter - 430594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430594]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00328_not_prime : ¬(recordGapCenter - 430558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430558]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00329_not_prime : ¬(recordGapCenter - 430552).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430552]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00330_not_prime : ¬(recordGapCenter - 430264).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430264]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00331_not_prime : ¬(recordGapCenter - 430174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430174]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00332_not_prime : ¬(recordGapCenter - 430072).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430072]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00333_not_prime : ¬(recordGapCenter - 429798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 429798]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00334_not_prime : ¬(recordGapCenter - 429622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 429622]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00335_not_prime : ¬(recordGapCenter - 429544).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 429544]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00336_not_prime : ¬(recordGapCenter - 429508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 429508]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00337_not_prime : ¬(recordGapCenter - 429414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 429414]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00338_not_prime : ¬(recordGapCenter - 429222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 429222]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00339_not_prime : ¬(recordGapCenter - 429064).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 429064]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00340_not_prime : ¬(recordGapCenter - 428998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 428998]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00341_not_prime : ¬(recordGapCenter - 428878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 428878]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00342_not_prime : ¬(recordGapCenter - 428788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 428788]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00343_not_prime : ¬(recordGapCenter - 428782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 428782]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00344_not_prime : ¬(recordGapCenter - 428728).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 428728]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00345_not_prime : ¬(recordGapCenter - 428658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 428658]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00346_not_prime : ¬(recordGapCenter - 428622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 428622]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00347_not_prime : ¬(recordGapCenter - 428334).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 428334]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00348_not_prime : ¬(recordGapCenter - 427998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427998]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00349_not_prime : ¬(recordGapCenter - 427972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427972]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00350_not_prime : ¬(recordGapCenter - 427962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427962]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00351_not_prime : ¬(recordGapCenter - 427902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427902]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00352_not_prime : ¬(recordGapCenter - 427894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427894]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00353_not_prime : ¬(recordGapCenter - 427858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427858]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00354_not_prime : ¬(recordGapCenter - 427852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427852]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00355_not_prime : ¬(recordGapCenter - 427828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427828]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00356_not_prime : ¬(recordGapCenter - 427762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427762]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00357_not_prime : ¬(recordGapCenter - 427528).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427528]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00358_not_prime : ¬(recordGapCenter - 427474).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427474]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00359_not_prime : ¬(recordGapCenter - 427468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427468]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00360_not_prime : ¬(recordGapCenter - 427444).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427444]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00361_not_prime : ¬(recordGapCenter - 427282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427282]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00362_not_prime : ¬(recordGapCenter - 427254).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427254]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00363_not_prime : ¬(recordGapCenter - 427012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427012]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00364_not_prime : ¬(recordGapCenter - 426982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426982]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00365_not_prime : ¬(recordGapCenter - 426934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426934]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00366_not_prime : ¬(recordGapCenter - 426898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426898]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00367_not_prime : ¬(recordGapCenter - 426888).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426888]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00368_not_prime : ¬(recordGapCenter - 426772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426772]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00369_not_prime : ¬(recordGapCenter - 426724).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426724]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00370_not_prime : ¬(recordGapCenter - 426534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426534]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00371_not_prime : ¬(recordGapCenter - 426508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426508]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00372_not_prime : ¬(recordGapCenter - 426484).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426484]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00373_not_prime : ¬(recordGapCenter - 426418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426418]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00374_not_prime : ¬(recordGapCenter - 426414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426414]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00375_not_prime : ¬(recordGapCenter - 426354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426354]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00376_not_prime : ¬(recordGapCenter - 426138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426138]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00377_not_prime : ¬(recordGapCenter - 426124).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426124]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00378_not_prime : ¬(recordGapCenter - 426004).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426004]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00379_not_prime : ¬(recordGapCenter - 425994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425994]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00380_not_prime : ¬(recordGapCenter - 425974).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425974]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00381_not_prime : ¬(recordGapCenter - 425962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425962]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00382_not_prime : ¬(recordGapCenter - 425848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425848]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00383_not_prime : ¬(recordGapCenter - 425694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425694]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00384_not_prime : ¬(recordGapCenter - 425512).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425512]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00385_not_prime : ¬(recordGapCenter - 425428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425428]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00386_not_prime : ¬(recordGapCenter - 425338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425338]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00387_not_prime : ¬(recordGapCenter - 425254).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425254]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00388_not_prime : ¬(recordGapCenter - 425250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425250]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00389_not_prime : ¬(recordGapCenter - 425212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425212]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00390_not_prime : ¬(recordGapCenter - 425164).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425164]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00391_not_prime : ¬(recordGapCenter - 425122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425122]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00392_not_prime : ¬(recordGapCenter - 425094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425094]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00393_not_prime : ¬(recordGapCenter - 425058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425058]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00394_not_prime : ¬(recordGapCenter - 424828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 424828]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00395_not_prime : ¬(recordGapCenter - 424744).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 424744]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00396_not_prime : ¬(recordGapCenter - 424738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 424738]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00397_not_prime : ¬(recordGapCenter - 424552).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 424552]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00398_not_prime : ¬(recordGapCenter - 424492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 424492]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00399_not_prime : ¬(recordGapCenter - 424374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 424374]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00400_not_prime : ¬(recordGapCenter - 424282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 424282]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00401_not_prime : ¬(recordGapCenter - 424254).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 424254]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00402_not_prime : ¬(recordGapCenter - 424234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 424234]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00403_not_prime : ¬(recordGapCenter - 424132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 424132]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00404_not_prime : ¬(recordGapCenter - 424114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 424114]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00405_not_prime : ¬(recordGapCenter - 423868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 423868]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00406_not_prime : ¬(recordGapCenter - 423784).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 423784]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00407_not_prime : ¬(recordGapCenter - 423762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 423762]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00408_not_prime : ¬(recordGapCenter - 423622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 423622]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00409_not_prime : ¬(recordGapCenter - 423562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 423562]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00410_not_prime : ¬(recordGapCenter - 423532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 423532]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00411_not_prime : ¬(recordGapCenter - 423498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 423498]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00412_not_prime : ¬(recordGapCenter - 423454).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 423454]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00413_not_prime : ¬(recordGapCenter - 423360).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 423360]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00414_not_prime : ¬(recordGapCenter - 423352).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 423352]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00415_not_prime : ¬(recordGapCenter - 423268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 423268]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00416_not_prime : ¬(recordGapCenter - 423222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 423222]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00417_not_prime : ¬(recordGapCenter - 423142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 423142]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00418_not_prime : ¬(recordGapCenter - 422854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 422854]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00419_not_prime : ¬(recordGapCenter - 422742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 422742]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00420_not_prime : ¬(recordGapCenter - 422574).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 422574]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00421_not_prime : ¬(recordGapCenter - 422538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 422538]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00422_not_prime : ¬(recordGapCenter - 422482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 422482]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00423_not_prime : ¬(recordGapCenter - 422428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 422428]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00424_not_prime : ¬(recordGapCenter - 422398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 422398]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00425_not_prime : ¬(recordGapCenter - 422274).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 422274]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00426_not_prime : ¬(recordGapCenter - 422194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 422194]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00427_not_prime : ¬(recordGapCenter - 422152).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 422152]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00428_not_prime : ¬(recordGapCenter - 422068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 422068]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00429_not_prime : ¬(recordGapCenter - 422014).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 422014]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00430_not_prime : ¬(recordGapCenter - 421878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 421878]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00431_not_prime : ¬(recordGapCenter - 421864).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 421864]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00432_not_prime : ¬(recordGapCenter - 421738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 421738]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00433_not_prime : ¬(recordGapCenter - 421734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 421734]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00434_not_prime : ¬(recordGapCenter - 421714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 421714]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00435_not_prime : ¬(recordGapCenter - 421588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 421588]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00436_not_prime : ¬(recordGapCenter - 421522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 421522]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00437_not_prime : ¬(recordGapCenter - 421438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 421438]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00438_not_prime : ¬(recordGapCenter - 421242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 421242]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00439_not_prime : ¬(recordGapCenter - 421108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 421108]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00440_not_prime : ¬(recordGapCenter - 421054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 421054]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00441_not_prime : ¬(recordGapCenter - 421048).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 421048]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00442_not_prime : ¬(recordGapCenter - 420982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420982]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00443_not_prime : ¬(recordGapCenter - 420922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420922]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00444_not_prime : ¬(recordGapCenter - 420874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420874]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00445_not_prime : ¬(recordGapCenter - 420814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420814]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00446_not_prime : ¬(recordGapCenter - 420802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420802]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00447_not_prime : ¬(recordGapCenter - 420718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420718]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00448_not_prime : ¬(recordGapCenter - 420664).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420664]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00449_not_prime : ¬(recordGapCenter - 420474).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420474]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00450_not_prime : ¬(recordGapCenter - 420388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420388]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00451_not_prime : ¬(recordGapCenter - 420382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420382]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00452_not_prime : ¬(recordGapCenter - 420262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420262]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00453_not_prime : ¬(recordGapCenter - 420234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420234]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00454_not_prime : ¬(recordGapCenter - 420088).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420088]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00455_not_prime : ¬(recordGapCenter - 420054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420054]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00456_not_prime : ¬(recordGapCenter - 420018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420018]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00457_not_prime : ¬(recordGapCenter - 420000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420000]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00458_not_prime : ¬(recordGapCenter - 419982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 419982]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00459_not_prime : ¬(recordGapCenter - 419788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 419788]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00460_not_prime : ¬(recordGapCenter - 419674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 419674]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00461_not_prime : ¬(recordGapCenter - 419578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 419578]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00462_not_prime : ¬(recordGapCenter - 419464).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 419464]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00463_not_prime : ¬(recordGapCenter - 419262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 419262]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00464_not_prime : ¬(recordGapCenter - 419194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 419194]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00465_not_prime : ¬(recordGapCenter - 419158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 419158]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00466_not_prime : ¬(recordGapCenter - 419142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 419142]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00467_not_prime : ¬(recordGapCenter - 419134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 419134]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00468_not_prime : ¬(recordGapCenter - 419092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 419092]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00469_not_prime : ¬(recordGapCenter - 419032).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 419032]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00470_not_prime : ¬(recordGapCenter - 418974).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 418974]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00471_not_prime : ¬(recordGapCenter - 418962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 418962]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00472_not_prime : ¬(recordGapCenter - 418942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 418942]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00473_not_prime : ¬(recordGapCenter - 418918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 418918]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00474_not_prime : ¬(recordGapCenter - 418732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 418732]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00475_not_prime : ¬(recordGapCenter - 418714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 418714]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00476_not_prime : ¬(recordGapCenter - 418504).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 418504]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00477_not_prime : ¬(recordGapCenter - 418408).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 418408]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00478_not_prime : ¬(recordGapCenter - 418402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 418402]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00479_not_prime : ¬(recordGapCenter - 418372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 418372]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00480_not_prime : ¬(recordGapCenter - 418108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 418108]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00481_not_prime : ¬(recordGapCenter - 418024).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 418024]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00482_not_prime : ¬(recordGapCenter - 417892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 417892]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00483_not_prime : ¬(recordGapCenter - 417778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 417778]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00484_not_prime : ¬(recordGapCenter - 417598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 417598]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00485_not_prime : ¬(recordGapCenter - 417532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 417532]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00486_not_prime : ¬(recordGapCenter - 417442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 417442]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00487_not_prime : ¬(recordGapCenter - 417244).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 417244]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00488_not_prime : ¬(recordGapCenter - 417022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 417022]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00489_not_prime : ¬(recordGapCenter - 416994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 416994]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00490_not_prime : ¬(recordGapCenter - 416824).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 416824]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00491_not_prime : ¬(recordGapCenter - 416818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 416818]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00492_not_prime : ¬(recordGapCenter - 416758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 416758]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00493_not_prime : ¬(recordGapCenter - 416742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 416742]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00494_not_prime : ¬(recordGapCenter - 416562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 416562]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00495_not_prime : ¬(recordGapCenter - 416554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 416554]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00496_not_prime : ¬(recordGapCenter - 416434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 416434]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00497_not_prime : ¬(recordGapCenter - 416418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 416418]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00498_not_prime : ¬(recordGapCenter - 416334).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 416334]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00499_not_prime : ¬(recordGapCenter - 416212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 416212]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00500_not_prime : ¬(recordGapCenter - 416022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 416022]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00501_not_prime : ¬(recordGapCenter - 415942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 415942]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00502_not_prime : ¬(recordGapCenter - 415924).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 415924]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00503_not_prime : ¬(recordGapCenter - 415894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 415894]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00504_not_prime : ¬(recordGapCenter - 415800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 415800]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00505_not_prime : ¬(recordGapCenter - 415768).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 415768]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00506_not_prime : ¬(recordGapCenter - 415594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 415594]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00507_not_prime : ¬(recordGapCenter - 415468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 415468]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00508_not_prime : ¬(recordGapCenter - 415434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 415434]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00509_not_prime : ¬(recordGapCenter - 415432).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 415432]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00510_not_prime : ¬(recordGapCenter - 415258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 415258]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00511_not_prime : ¬(recordGapCenter - 415204).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 415204]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00512_not_prime : ¬(recordGapCenter - 414978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414978]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

end PrimeFactorUnimodality
