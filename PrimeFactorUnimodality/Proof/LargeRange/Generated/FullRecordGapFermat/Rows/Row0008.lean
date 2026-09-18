import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00008_values : List Nat :=
  [fullRecordGapCenterValue - 310782,
    fullRecordGapCenterValue - 310762,
    fullRecordGapCenterValue - 310438,
    fullRecordGapCenterValue - 310348,
    fullRecordGapCenterValue - 310342,
    fullRecordGapCenterValue - 310228,
    fullRecordGapCenterValue - 310162,
    fullRecordGapCenterValue - 310098,
    fullRecordGapCenterValue - 310084,
    fullRecordGapCenterValue - 310074,
    fullRecordGapCenterValue - 310018,
    fullRecordGapCenterValue - 309882,
    fullRecordGapCenterValue - 309822,
    fullRecordGapCenterValue - 309760,
    fullRecordGapCenterValue - 309682,
    fullRecordGapCenterValue - 309678,
    fullRecordGapCenterValue - 309598,
    fullRecordGapCenterValue - 309574,
    fullRecordGapCenterValue - 309538,
    fullRecordGapCenterValue - 309382,
    fullRecordGapCenterValue - 309378,
    fullRecordGapCenterValue - 309292,
    fullRecordGapCenterValue - 308878,
    fullRecordGapCenterValue - 308874,
    fullRecordGapCenterValue - 308838,
    fullRecordGapCenterValue - 308700,
    fullRecordGapCenterValue - 308668,
    fullRecordGapCenterValue - 308622,
    fullRecordGapCenterValue - 308478,
    fullRecordGapCenterValue - 308314,
    fullRecordGapCenterValue - 308188,
    fullRecordGapCenterValue - 308164,
    fullRecordGapCenterValue - 308122,
    fullRecordGapCenterValue - 308094,
    fullRecordGapCenterValue - 308082,
    fullRecordGapCenterValue - 308068,
    fullRecordGapCenterValue - 308058,
    fullRecordGapCenterValue - 308002,
    fullRecordGapCenterValue - 307852,
    fullRecordGapCenterValue - 307774,
    fullRecordGapCenterValue - 307698,
    fullRecordGapCenterValue - 307578,
    fullRecordGapCenterValue - 307402,
    fullRecordGapCenterValue - 307348,
    fullRecordGapCenterValue - 307282,
    fullRecordGapCenterValue - 307158,
    fullRecordGapCenterValue - 307114,
    fullRecordGapCenterValue - 307018,
    fullRecordGapCenterValue - 306942,
    fullRecordGapCenterValue - 306814,
    fullRecordGapCenterValue - 306798,
    fullRecordGapCenterValue - 306742,
    fullRecordGapCenterValue - 306654,
    fullRecordGapCenterValue - 306604,
    fullRecordGapCenterValue - 306562,
    fullRecordGapCenterValue - 306388,
    fullRecordGapCenterValue - 306274,
    fullRecordGapCenterValue - 306214,
    fullRecordGapCenterValue - 306154,
    fullRecordGapCenterValue - 306142,
    fullRecordGapCenterValue - 306028,
    fullRecordGapCenterValue - 305962,
    fullRecordGapCenterValue - 305934,
    fullRecordGapCenterValue - 305884,
    fullRecordGapCenterValue - 305878,
    fullRecordGapCenterValue - 305818,
    fullRecordGapCenterValue - 305814,
    fullRecordGapCenterValue - 305692,
    fullRecordGapCenterValue - 305638,
    fullRecordGapCenterValue - 305454,
    fullRecordGapCenterValue - 305212,
    fullRecordGapCenterValue - 305202,
    fullRecordGapCenterValue - 305142,
    fullRecordGapCenterValue - 305134,
    fullRecordGapCenterValue - 305062,
    fullRecordGapCenterValue - 305044,
    fullRecordGapCenterValue - 304918,
    fullRecordGapCenterValue - 304834,
    fullRecordGapCenterValue - 304762,
    fullRecordGapCenterValue - 304534,
    fullRecordGapCenterValue - 304518,
    fullRecordGapCenterValue - 304498,
    fullRecordGapCenterValue - 304338,
    fullRecordGapCenterValue - 304324,
    fullRecordGapCenterValue - 304294,
    fullRecordGapCenterValue - 304098,
    fullRecordGapCenterValue - 304078,
    fullRecordGapCenterValue - 303988,
    fullRecordGapCenterValue - 303694,
    fullRecordGapCenterValue - 303652,
    fullRecordGapCenterValue - 303532,
    fullRecordGapCenterValue - 303522,
    fullRecordGapCenterValue - 303412,
    fullRecordGapCenterValue - 303172,
    fullRecordGapCenterValue - 303018,
    fullRecordGapCenterValue - 302754,
    fullRecordGapCenterValue - 302308,
    fullRecordGapCenterValue - 302298,
    fullRecordGapCenterValue - 302154,
    fullRecordGapCenterValue - 301762,
    fullRecordGapCenterValue - 301612,
    fullRecordGapCenterValue - 301564,
    fullRecordGapCenterValue - 301468,
    fullRecordGapCenterValue - 301348,
    fullRecordGapCenterValue - 301234,
    fullRecordGapCenterValue - 301174,
    fullRecordGapCenterValue - 300954,
    fullRecordGapCenterValue - 300862,
    fullRecordGapCenterValue - 300774,
    fullRecordGapCenterValue - 300772,
    fullRecordGapCenterValue - 300754,
    fullRecordGapCenterValue - 300738,
    fullRecordGapCenterValue - 300522,
    fullRecordGapCenterValue - 300442,
    fullRecordGapCenterValue - 300418,
    fullRecordGapCenterValue - 300394,
    fullRecordGapCenterValue - 300178,
    fullRecordGapCenterValue - 300052,
    fullRecordGapCenterValue - 300022,
    fullRecordGapCenterValue - 299938,
    fullRecordGapCenterValue - 299878,
    fullRecordGapCenterValue - 299674,
    fullRecordGapCenterValue - 299658,
    fullRecordGapCenterValue - 299634,
    fullRecordGapCenterValue - 299542,
    fullRecordGapCenterValue - 299518,
    fullRecordGapCenterValue - 299514,
    fullRecordGapCenterValue - 299458,
    fullRecordGapCenterValue - 299434,
    fullRecordGapCenterValue - 299428,
    fullRecordGapCenterValue - 299308,
    fullRecordGapCenterValue - 299058,
    fullRecordGapCenterValue - 298882,
    fullRecordGapCenterValue - 298834,
    fullRecordGapCenterValue - 298798,
    fullRecordGapCenterValue - 298762,
    fullRecordGapCenterValue - 298734,
    fullRecordGapCenterValue - 298618,
    fullRecordGapCenterValue - 298542,
    fullRecordGapCenterValue - 298492,
    fullRecordGapCenterValue - 298482,
    fullRecordGapCenterValue - 298318,
    fullRecordGapCenterValue - 298198,
    fullRecordGapCenterValue - 298084,
    fullRecordGapCenterValue - 297978,
    fullRecordGapCenterValue - 297922,
    fullRecordGapCenterValue - 297834,
    fullRecordGapCenterValue - 297658,
    fullRecordGapCenterValue - 297652,
    fullRecordGapCenterValue - 297618,
    fullRecordGapCenterValue - 297582,
    fullRecordGapCenterValue - 297442,
    fullRecordGapCenterValue - 297412,
    fullRecordGapCenterValue - 297294,
    fullRecordGapCenterValue - 297292,
    fullRecordGapCenterValue - 297282,
    fullRecordGapCenterValue - 297148,
    fullRecordGapCenterValue - 297138,
    fullRecordGapCenterValue - 297034,
    fullRecordGapCenterValue - 296778,
    fullRecordGapCenterValue - 296602,
    fullRecordGapCenterValue - 296524,
    fullRecordGapCenterValue - 296284,
    fullRecordGapCenterValue - 296214,
    fullRecordGapCenterValue - 296202,
    fullRecordGapCenterValue - 296158,
    fullRecordGapCenterValue - 295998,
    fullRecordGapCenterValue - 295680,
    fullRecordGapCenterValue - 295654,
    fullRecordGapCenterValue - 295588,
    fullRecordGapCenterValue - 295558,
    fullRecordGapCenterValue - 295468,
    fullRecordGapCenterValue - 295294,
    fullRecordGapCenterValue - 295258,
    fullRecordGapCenterValue - 295242,
    fullRecordGapCenterValue - 295234,
    fullRecordGapCenterValue - 295194,
    fullRecordGapCenterValue - 295132,
    fullRecordGapCenterValue - 295084,
    fullRecordGapCenterValue - 294912,
    fullRecordGapCenterValue - 294772,
    fullRecordGapCenterValue - 294754,
    fullRecordGapCenterValue - 294702,
    fullRecordGapCenterValue - 294682,
    fullRecordGapCenterValue - 294618,
    fullRecordGapCenterValue - 294394,
    fullRecordGapCenterValue - 294222,
    fullRecordGapCenterValue - 294214,
    fullRecordGapCenterValue - 294114,
    fullRecordGapCenterValue - 294058,
    fullRecordGapCenterValue - 294000,
    fullRecordGapCenterValue - 293932,
    fullRecordGapCenterValue - 293842,
    fullRecordGapCenterValue - 293838,
    fullRecordGapCenterValue - 293718,
    fullRecordGapCenterValue - 293668,
    fullRecordGapCenterValue - 293614,
    fullRecordGapCenterValue - 293452,
    fullRecordGapCenterValue - 293334,
    fullRecordGapCenterValue - 293298,
    fullRecordGapCenterValue - 293278,
    fullRecordGapCenterValue - 293218,
    fullRecordGapCenterValue - 293214,
    fullRecordGapCenterValue - 292542,
    fullRecordGapCenterValue - 292282,
    fullRecordGapCenterValue - 292074,
    fullRecordGapCenterValue - 292018,
    fullRecordGapCenterValue - 291748,
    fullRecordGapCenterValue - 291738,
    fullRecordGapCenterValue - 291598,
    fullRecordGapCenterValue - 291358,
    fullRecordGapCenterValue - 291322,
    fullRecordGapCenterValue - 291274,
    fullRecordGapCenterValue - 291268,
    fullRecordGapCenterValue - 291234,
    fullRecordGapCenterValue - 291202,
    fullRecordGapCenterValue - 291198,
    fullRecordGapCenterValue - 291178,
    fullRecordGapCenterValue - 291154,
    fullRecordGapCenterValue - 291052,
    fullRecordGapCenterValue - 291022,
    fullRecordGapCenterValue - 290922,
    fullRecordGapCenterValue - 290908,
    fullRecordGapCenterValue - 290694,
    fullRecordGapCenterValue - 290622,
    fullRecordGapCenterValue - 290614,
    fullRecordGapCenterValue - 290572,
    fullRecordGapCenterValue - 290518,
    fullRecordGapCenterValue - 290478,
    fullRecordGapCenterValue - 290454,
    fullRecordGapCenterValue - 290442,
    fullRecordGapCenterValue - 290400,
    fullRecordGapCenterValue - 290304,
    fullRecordGapCenterValue - 290218,
    fullRecordGapCenterValue - 290182,
    fullRecordGapCenterValue - 290062,
    fullRecordGapCenterValue - 289972,
    fullRecordGapCenterValue - 289834,
    fullRecordGapCenterValue - 289798,
    fullRecordGapCenterValue - 289684,
    fullRecordGapCenterValue - 289582,
    fullRecordGapCenterValue - 289558,
    fullRecordGapCenterValue - 289554,
    fullRecordGapCenterValue - 289482,
    fullRecordGapCenterValue - 289468,
    fullRecordGapCenterValue - 289462,
    fullRecordGapCenterValue - 289438,
    fullRecordGapCenterValue - 289434,
    fullRecordGapCenterValue - 289342,
    fullRecordGapCenterValue - 289252,
    fullRecordGapCenterValue - 289228,
    fullRecordGapCenterValue - 289222,
    fullRecordGapCenterValue - 289182,
    fullRecordGapCenterValue - 289158,
    fullRecordGapCenterValue - 289074,
    fullRecordGapCenterValue - 289012]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00008_fermat : ∀ n ∈ fullRecordGapRow00008_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01793_not_prime : ¬(recordGapCenter - 310782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 310782]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01794_not_prime : ¬(recordGapCenter - 310762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 310762]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01795_not_prime : ¬(recordGapCenter - 310438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 310438]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01796_not_prime : ¬(recordGapCenter - 310348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 310348]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01797_not_prime : ¬(recordGapCenter - 310342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 310342]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01798_not_prime : ¬(recordGapCenter - 310228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 310228]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01799_not_prime : ¬(recordGapCenter - 310162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 310162]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01800_not_prime : ¬(recordGapCenter - 310098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 310098]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01801_not_prime : ¬(recordGapCenter - 310084).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 310084]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01802_not_prime : ¬(recordGapCenter - 310074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 310074]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01803_not_prime : ¬(recordGapCenter - 310018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 310018]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01804_not_prime : ¬(recordGapCenter - 309882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 309882]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01805_not_prime : ¬(recordGapCenter - 309822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 309822]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01806_not_prime : ¬(recordGapCenter - 309760).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 309760]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01807_not_prime : ¬(recordGapCenter - 309682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 309682]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01808_not_prime : ¬(recordGapCenter - 309678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 309678]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01809_not_prime : ¬(recordGapCenter - 309598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 309598]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01810_not_prime : ¬(recordGapCenter - 309574).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 309574]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01811_not_prime : ¬(recordGapCenter - 309538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 309538]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01812_not_prime : ¬(recordGapCenter - 309382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 309382]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01813_not_prime : ¬(recordGapCenter - 309378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 309378]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01814_not_prime : ¬(recordGapCenter - 309292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 309292]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01815_not_prime : ¬(recordGapCenter - 308878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308878]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01816_not_prime : ¬(recordGapCenter - 308874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308874]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01817_not_prime : ¬(recordGapCenter - 308838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308838]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01818_not_prime : ¬(recordGapCenter - 308700).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308700]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01819_not_prime : ¬(recordGapCenter - 308668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308668]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01820_not_prime : ¬(recordGapCenter - 308622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308622]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01821_not_prime : ¬(recordGapCenter - 308478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308478]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01822_not_prime : ¬(recordGapCenter - 308314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308314]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01823_not_prime : ¬(recordGapCenter - 308188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308188]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01824_not_prime : ¬(recordGapCenter - 308164).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308164]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01825_not_prime : ¬(recordGapCenter - 308122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308122]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01826_not_prime : ¬(recordGapCenter - 308094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308094]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01827_not_prime : ¬(recordGapCenter - 308082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308082]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01828_not_prime : ¬(recordGapCenter - 308068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308068]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01829_not_prime : ¬(recordGapCenter - 308058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308058]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01830_not_prime : ¬(recordGapCenter - 308002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 308002]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01831_not_prime : ¬(recordGapCenter - 307852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 307852]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01832_not_prime : ¬(recordGapCenter - 307774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 307774]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01833_not_prime : ¬(recordGapCenter - 307698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 307698]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01834_not_prime : ¬(recordGapCenter - 307578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 307578]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01835_not_prime : ¬(recordGapCenter - 307402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 307402]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01836_not_prime : ¬(recordGapCenter - 307348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 307348]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01837_not_prime : ¬(recordGapCenter - 307282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 307282]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01838_not_prime : ¬(recordGapCenter - 307158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 307158]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01839_not_prime : ¬(recordGapCenter - 307114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 307114]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01840_not_prime : ¬(recordGapCenter - 307018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 307018]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01841_not_prime : ¬(recordGapCenter - 306942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 306942]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01842_not_prime : ¬(recordGapCenter - 306814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 306814]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01843_not_prime : ¬(recordGapCenter - 306798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 306798]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01844_not_prime : ¬(recordGapCenter - 306742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 306742]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01845_not_prime : ¬(recordGapCenter - 306654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 306654]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01846_not_prime : ¬(recordGapCenter - 306604).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 306604]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01847_not_prime : ¬(recordGapCenter - 306562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 306562]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01848_not_prime : ¬(recordGapCenter - 306388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 306388]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01849_not_prime : ¬(recordGapCenter - 306274).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 306274]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01850_not_prime : ¬(recordGapCenter - 306214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 306214]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01851_not_prime : ¬(recordGapCenter - 306154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 306154]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01852_not_prime : ¬(recordGapCenter - 306142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 306142]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01853_not_prime : ¬(recordGapCenter - 306028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 306028]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01854_not_prime : ¬(recordGapCenter - 305962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305962]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01855_not_prime : ¬(recordGapCenter - 305934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305934]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01856_not_prime : ¬(recordGapCenter - 305884).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305884]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01857_not_prime : ¬(recordGapCenter - 305878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305878]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01858_not_prime : ¬(recordGapCenter - 305818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305818]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01859_not_prime : ¬(recordGapCenter - 305814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305814]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01860_not_prime : ¬(recordGapCenter - 305692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305692]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01861_not_prime : ¬(recordGapCenter - 305638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305638]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01862_not_prime : ¬(recordGapCenter - 305454).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305454]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01863_not_prime : ¬(recordGapCenter - 305212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305212]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01864_not_prime : ¬(recordGapCenter - 305202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305202]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01865_not_prime : ¬(recordGapCenter - 305142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305142]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01866_not_prime : ¬(recordGapCenter - 305134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305134]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01867_not_prime : ¬(recordGapCenter - 305062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305062]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01868_not_prime : ¬(recordGapCenter - 305044).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305044]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01869_not_prime : ¬(recordGapCenter - 304918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 304918]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01870_not_prime : ¬(recordGapCenter - 304834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 304834]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01871_not_prime : ¬(recordGapCenter - 304762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 304762]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01872_not_prime : ¬(recordGapCenter - 304534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 304534]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01873_not_prime : ¬(recordGapCenter - 304518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 304518]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01874_not_prime : ¬(recordGapCenter - 304498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 304498]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01875_not_prime : ¬(recordGapCenter - 304338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 304338]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01876_not_prime : ¬(recordGapCenter - 304324).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 304324]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01877_not_prime : ¬(recordGapCenter - 304294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 304294]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01878_not_prime : ¬(recordGapCenter - 304098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 304098]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01879_not_prime : ¬(recordGapCenter - 304078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 304078]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01880_not_prime : ¬(recordGapCenter - 303988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 303988]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01881_not_prime : ¬(recordGapCenter - 303694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 303694]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01882_not_prime : ¬(recordGapCenter - 303652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 303652]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01883_not_prime : ¬(recordGapCenter - 303532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 303532]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01884_not_prime : ¬(recordGapCenter - 303522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 303522]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01885_not_prime : ¬(recordGapCenter - 303412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 303412]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01886_not_prime : ¬(recordGapCenter - 303172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 303172]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01887_not_prime : ¬(recordGapCenter - 303018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 303018]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01888_not_prime : ¬(recordGapCenter - 302754).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 302754]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01889_not_prime : ¬(recordGapCenter - 302308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 302308]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01890_not_prime : ¬(recordGapCenter - 302298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 302298]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01891_not_prime : ¬(recordGapCenter - 302154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 302154]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01892_not_prime : ¬(recordGapCenter - 301762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 301762]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01893_not_prime : ¬(recordGapCenter - 301612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 301612]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01894_not_prime : ¬(recordGapCenter - 301564).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 301564]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01895_not_prime : ¬(recordGapCenter - 301468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 301468]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01896_not_prime : ¬(recordGapCenter - 301348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 301348]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01897_not_prime : ¬(recordGapCenter - 301234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 301234]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01898_not_prime : ¬(recordGapCenter - 301174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 301174]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01899_not_prime : ¬(recordGapCenter - 300954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 300954]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01900_not_prime : ¬(recordGapCenter - 300862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 300862]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01901_not_prime : ¬(recordGapCenter - 300774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 300774]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01902_not_prime : ¬(recordGapCenter - 300772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 300772]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01903_not_prime : ¬(recordGapCenter - 300754).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 300754]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01904_not_prime : ¬(recordGapCenter - 300738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 300738]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01905_not_prime : ¬(recordGapCenter - 300522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 300522]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01906_not_prime : ¬(recordGapCenter - 300442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 300442]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01907_not_prime : ¬(recordGapCenter - 300418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 300418]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01908_not_prime : ¬(recordGapCenter - 300394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 300394]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01909_not_prime : ¬(recordGapCenter - 300178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 300178]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01910_not_prime : ¬(recordGapCenter - 300052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 300052]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01911_not_prime : ¬(recordGapCenter - 300022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 300022]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01912_not_prime : ¬(recordGapCenter - 299938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 299938]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01913_not_prime : ¬(recordGapCenter - 299878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 299878]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01914_not_prime : ¬(recordGapCenter - 299674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 299674]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01915_not_prime : ¬(recordGapCenter - 299658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 299658]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01916_not_prime : ¬(recordGapCenter - 299634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 299634]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01917_not_prime : ¬(recordGapCenter - 299542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 299542]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01918_not_prime : ¬(recordGapCenter - 299518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 299518]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01919_not_prime : ¬(recordGapCenter - 299514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 299514]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01920_not_prime : ¬(recordGapCenter - 299458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 299458]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01921_not_prime : ¬(recordGapCenter - 299434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 299434]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01922_not_prime : ¬(recordGapCenter - 299428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 299428]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01923_not_prime : ¬(recordGapCenter - 299308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 299308]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01924_not_prime : ¬(recordGapCenter - 299058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 299058]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01925_not_prime : ¬(recordGapCenter - 298882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 298882]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01926_not_prime : ¬(recordGapCenter - 298834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 298834]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01927_not_prime : ¬(recordGapCenter - 298798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 298798]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01928_not_prime : ¬(recordGapCenter - 298762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 298762]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01929_not_prime : ¬(recordGapCenter - 298734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 298734]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01930_not_prime : ¬(recordGapCenter - 298618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 298618]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01931_not_prime : ¬(recordGapCenter - 298542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 298542]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01932_not_prime : ¬(recordGapCenter - 298492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 298492]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01933_not_prime : ¬(recordGapCenter - 298482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 298482]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01934_not_prime : ¬(recordGapCenter - 298318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 298318]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01935_not_prime : ¬(recordGapCenter - 298198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 298198]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01936_not_prime : ¬(recordGapCenter - 298084).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 298084]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01937_not_prime : ¬(recordGapCenter - 297978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297978]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01938_not_prime : ¬(recordGapCenter - 297922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297922]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01939_not_prime : ¬(recordGapCenter - 297834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297834]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01940_not_prime : ¬(recordGapCenter - 297658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297658]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01941_not_prime : ¬(recordGapCenter - 297652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297652]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01942_not_prime : ¬(recordGapCenter - 297618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297618]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01943_not_prime : ¬(recordGapCenter - 297582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297582]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01944_not_prime : ¬(recordGapCenter - 297442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297442]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01945_not_prime : ¬(recordGapCenter - 297412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297412]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01946_not_prime : ¬(recordGapCenter - 297294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297294]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01947_not_prime : ¬(recordGapCenter - 297292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297292]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01948_not_prime : ¬(recordGapCenter - 297282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297282]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01949_not_prime : ¬(recordGapCenter - 297148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297148]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01950_not_prime : ¬(recordGapCenter - 297138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297138]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01951_not_prime : ¬(recordGapCenter - 297034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297034]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01952_not_prime : ¬(recordGapCenter - 296778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 296778]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01953_not_prime : ¬(recordGapCenter - 296602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 296602]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01954_not_prime : ¬(recordGapCenter - 296524).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 296524]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01955_not_prime : ¬(recordGapCenter - 296284).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 296284]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01956_not_prime : ¬(recordGapCenter - 296214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 296214]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01957_not_prime : ¬(recordGapCenter - 296202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 296202]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01958_not_prime : ¬(recordGapCenter - 296158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 296158]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01959_not_prime : ¬(recordGapCenter - 295998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 295998]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01960_not_prime : ¬(recordGapCenter - 295680).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 295680]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01961_not_prime : ¬(recordGapCenter - 295654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 295654]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01962_not_prime : ¬(recordGapCenter - 295588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 295588]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01963_not_prime : ¬(recordGapCenter - 295558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 295558]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01964_not_prime : ¬(recordGapCenter - 295468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 295468]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01965_not_prime : ¬(recordGapCenter - 295294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 295294]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01966_not_prime : ¬(recordGapCenter - 295258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 295258]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01967_not_prime : ¬(recordGapCenter - 295242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 295242]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01968_not_prime : ¬(recordGapCenter - 295234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 295234]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01969_not_prime : ¬(recordGapCenter - 295194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 295194]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01970_not_prime : ¬(recordGapCenter - 295132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 295132]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01971_not_prime : ¬(recordGapCenter - 295084).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 295084]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01972_not_prime : ¬(recordGapCenter - 294912).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 294912]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01973_not_prime : ¬(recordGapCenter - 294772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 294772]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01974_not_prime : ¬(recordGapCenter - 294754).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 294754]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01975_not_prime : ¬(recordGapCenter - 294702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 294702]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01976_not_prime : ¬(recordGapCenter - 294682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 294682]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01977_not_prime : ¬(recordGapCenter - 294618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 294618]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01978_not_prime : ¬(recordGapCenter - 294394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 294394]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01979_not_prime : ¬(recordGapCenter - 294222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 294222]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01980_not_prime : ¬(recordGapCenter - 294214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 294214]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01981_not_prime : ¬(recordGapCenter - 294114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 294114]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01982_not_prime : ¬(recordGapCenter - 294058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 294058]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01983_not_prime : ¬(recordGapCenter - 294000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 294000]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01984_not_prime : ¬(recordGapCenter - 293932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 293932]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01985_not_prime : ¬(recordGapCenter - 293842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 293842]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01986_not_prime : ¬(recordGapCenter - 293838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 293838]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01987_not_prime : ¬(recordGapCenter - 293718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 293718]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01988_not_prime : ¬(recordGapCenter - 293668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 293668]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01989_not_prime : ¬(recordGapCenter - 293614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 293614]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01990_not_prime : ¬(recordGapCenter - 293452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 293452]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01991_not_prime : ¬(recordGapCenter - 293334).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 293334]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01992_not_prime : ¬(recordGapCenter - 293298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 293298]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01993_not_prime : ¬(recordGapCenter - 293278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 293278]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01994_not_prime : ¬(recordGapCenter - 293218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 293218]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01995_not_prime : ¬(recordGapCenter - 293214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 293214]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01996_not_prime : ¬(recordGapCenter - 292542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 292542]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01997_not_prime : ¬(recordGapCenter - 292282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 292282]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01998_not_prime : ¬(recordGapCenter - 292074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 292074]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm01999_not_prime : ¬(recordGapCenter - 292018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 292018]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02000_not_prime : ¬(recordGapCenter - 291748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291748]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02001_not_prime : ¬(recordGapCenter - 291738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291738]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02002_not_prime : ¬(recordGapCenter - 291598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291598]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02003_not_prime : ¬(recordGapCenter - 291358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291358]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02004_not_prime : ¬(recordGapCenter - 291322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291322]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02005_not_prime : ¬(recordGapCenter - 291274).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291274]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02006_not_prime : ¬(recordGapCenter - 291268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291268]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02007_not_prime : ¬(recordGapCenter - 291234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291234]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02008_not_prime : ¬(recordGapCenter - 291202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291202]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02009_not_prime : ¬(recordGapCenter - 291198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291198]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02010_not_prime : ¬(recordGapCenter - 291178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291178]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02011_not_prime : ¬(recordGapCenter - 291154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291154]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02012_not_prime : ¬(recordGapCenter - 291052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291052]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02013_not_prime : ¬(recordGapCenter - 291022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291022]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02014_not_prime : ¬(recordGapCenter - 290922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290922]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02015_not_prime : ¬(recordGapCenter - 290908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290908]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02016_not_prime : ¬(recordGapCenter - 290694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290694]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02017_not_prime : ¬(recordGapCenter - 290622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290622]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02018_not_prime : ¬(recordGapCenter - 290614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290614]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02019_not_prime : ¬(recordGapCenter - 290572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290572]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02020_not_prime : ¬(recordGapCenter - 290518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290518]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02021_not_prime : ¬(recordGapCenter - 290478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290478]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02022_not_prime : ¬(recordGapCenter - 290454).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290454]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02023_not_prime : ¬(recordGapCenter - 290442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290442]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02024_not_prime : ¬(recordGapCenter - 290400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290400]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02025_not_prime : ¬(recordGapCenter - 290304).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290304]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02026_not_prime : ¬(recordGapCenter - 290218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290218]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02027_not_prime : ¬(recordGapCenter - 290182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290182]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02028_not_prime : ¬(recordGapCenter - 290062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290062]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02029_not_prime : ¬(recordGapCenter - 289972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289972]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02030_not_prime : ¬(recordGapCenter - 289834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289834]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02031_not_prime : ¬(recordGapCenter - 289798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289798]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02032_not_prime : ¬(recordGapCenter - 289684).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289684]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02033_not_prime : ¬(recordGapCenter - 289582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289582]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02034_not_prime : ¬(recordGapCenter - 289558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289558]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02035_not_prime : ¬(recordGapCenter - 289554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289554]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02036_not_prime : ¬(recordGapCenter - 289482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289482]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02037_not_prime : ¬(recordGapCenter - 289468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289468]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02038_not_prime : ¬(recordGapCenter - 289462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289462]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02039_not_prime : ¬(recordGapCenter - 289438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289438]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02040_not_prime : ¬(recordGapCenter - 289434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289434]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02041_not_prime : ¬(recordGapCenter - 289342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289342]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02042_not_prime : ¬(recordGapCenter - 289252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289252]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02043_not_prime : ¬(recordGapCenter - 289228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289228]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02044_not_prime : ¬(recordGapCenter - 289222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289222]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02045_not_prime : ¬(recordGapCenter - 289182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289182]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02046_not_prime : ¬(recordGapCenter - 289158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289158]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02047_not_prime : ¬(recordGapCenter - 289074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289074]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm02048_not_prime : ¬(recordGapCenter - 289012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289012]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

end PrimeFactorUnimodality
