import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00123_values : List Nat :=
  [fullRecordGapCenterValue + 455690,
    fullRecordGapCenterValue + 455732,
    fullRecordGapCenterValue + 455738,
    fullRecordGapCenterValue + 455828,
    fullRecordGapCenterValue + 455870,
    fullRecordGapCenterValue + 455876,
    fullRecordGapCenterValue + 455912,
    fullRecordGapCenterValue + 456018,
    fullRecordGapCenterValue + 456026,
    fullRecordGapCenterValue + 456186,
    fullRecordGapCenterValue + 456192,
    fullRecordGapCenterValue + 456206,
    fullRecordGapCenterValue + 456278,
    fullRecordGapCenterValue + 456332,
    fullRecordGapCenterValue + 456398,
    fullRecordGapCenterValue + 456486,
    fullRecordGapCenterValue + 456668,
    fullRecordGapCenterValue + 456776,
    fullRecordGapCenterValue + 456788,
    fullRecordGapCenterValue + 456942,
    fullRecordGapCenterValue + 457076,
    fullRecordGapCenterValue + 457196,
    fullRecordGapCenterValue + 457202,
    fullRecordGapCenterValue + 457238,
    fullRecordGapCenterValue + 457380,
    fullRecordGapCenterValue + 457502,
    fullRecordGapCenterValue + 457658,
    fullRecordGapCenterValue + 457698,
    fullRecordGapCenterValue + 457790,
    fullRecordGapCenterValue + 457868,
    fullRecordGapCenterValue + 458162,
    fullRecordGapCenterValue + 458202,
    fullRecordGapCenterValue + 458246,
    fullRecordGapCenterValue + 458270,
    fullRecordGapCenterValue + 458330,
    fullRecordGapCenterValue + 458468,
    fullRecordGapCenterValue + 458538,
    fullRecordGapCenterValue + 458642,
    fullRecordGapCenterValue + 458648,
    fullRecordGapCenterValue + 458690,
    fullRecordGapCenterValue + 458930,
    fullRecordGapCenterValue + 458936,
    fullRecordGapCenterValue + 459182,
    fullRecordGapCenterValue + 459278,
    fullRecordGapCenterValue + 459308,
    fullRecordGapCenterValue + 459366,
    fullRecordGapCenterValue + 459506,
    fullRecordGapCenterValue + 459518,
    fullRecordGapCenterValue + 459530,
    fullRecordGapCenterValue + 459618,
    fullRecordGapCenterValue + 459698,
    fullRecordGapCenterValue + 459896,
    fullRecordGapCenterValue + 460002,
    fullRecordGapCenterValue + 460178,
    fullRecordGapCenterValue + 460202,
    fullRecordGapCenterValue + 460268,
    fullRecordGapCenterValue + 460398,
    fullRecordGapCenterValue + 460406,
    fullRecordGapCenterValue + 460442,
    fullRecordGapCenterValue + 460472,
    fullRecordGapCenterValue + 460562,
    fullRecordGapCenterValue + 460652,
    fullRecordGapCenterValue + 460682,
    fullRecordGapCenterValue + 460706]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00123_fermat : ∀ n ∈ fullRecordGapRow00123_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07809_not_prime : ¬(recordGapCenter + 455690).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 455690]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07810_not_prime : ¬(recordGapCenter + 455732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 455732]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07811_not_prime : ¬(recordGapCenter + 455738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 455738]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07812_not_prime : ¬(recordGapCenter + 455828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 455828]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07813_not_prime : ¬(recordGapCenter + 455870).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 455870]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07814_not_prime : ¬(recordGapCenter + 455876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 455876]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07815_not_prime : ¬(recordGapCenter + 455912).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 455912]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07816_not_prime : ¬(recordGapCenter + 456018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 456018]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07817_not_prime : ¬(recordGapCenter + 456026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 456026]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07818_not_prime : ¬(recordGapCenter + 456186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 456186]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07819_not_prime : ¬(recordGapCenter + 456192).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 456192]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07820_not_prime : ¬(recordGapCenter + 456206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 456206]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07821_not_prime : ¬(recordGapCenter + 456278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 456278]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07822_not_prime : ¬(recordGapCenter + 456332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 456332]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07823_not_prime : ¬(recordGapCenter + 456398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 456398]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07824_not_prime : ¬(recordGapCenter + 456486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 456486]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07825_not_prime : ¬(recordGapCenter + 456668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 456668]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07826_not_prime : ¬(recordGapCenter + 456776).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 456776]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07827_not_prime : ¬(recordGapCenter + 456788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 456788]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07828_not_prime : ¬(recordGapCenter + 456942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 456942]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07829_not_prime : ¬(recordGapCenter + 457076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 457076]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07830_not_prime : ¬(recordGapCenter + 457196).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 457196]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07831_not_prime : ¬(recordGapCenter + 457202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 457202]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07832_not_prime : ¬(recordGapCenter + 457238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 457238]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07833_not_prime : ¬(recordGapCenter + 457380).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 457380]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07834_not_prime : ¬(recordGapCenter + 457502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 457502]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07835_not_prime : ¬(recordGapCenter + 457658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 457658]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07836_not_prime : ¬(recordGapCenter + 457698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 457698]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07837_not_prime : ¬(recordGapCenter + 457790).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 457790]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07838_not_prime : ¬(recordGapCenter + 457868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 457868]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07839_not_prime : ¬(recordGapCenter + 458162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 458162]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07840_not_prime : ¬(recordGapCenter + 458202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 458202]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07841_not_prime : ¬(recordGapCenter + 458246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 458246]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07842_not_prime : ¬(recordGapCenter + 458270).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 458270]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07843_not_prime : ¬(recordGapCenter + 458330).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 458330]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07844_not_prime : ¬(recordGapCenter + 458468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 458468]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07845_not_prime : ¬(recordGapCenter + 458538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 458538]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07846_not_prime : ¬(recordGapCenter + 458642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 458642]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07847_not_prime : ¬(recordGapCenter + 458648).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 458648]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07848_not_prime : ¬(recordGapCenter + 458690).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 458690]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07849_not_prime : ¬(recordGapCenter + 458930).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 458930]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07850_not_prime : ¬(recordGapCenter + 458936).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 458936]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07851_not_prime : ¬(recordGapCenter + 459182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 459182]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07852_not_prime : ¬(recordGapCenter + 459278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 459278]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07853_not_prime : ¬(recordGapCenter + 459308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 459308]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07854_not_prime : ¬(recordGapCenter + 459366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 459366]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07855_not_prime : ¬(recordGapCenter + 459506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 459506]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07856_not_prime : ¬(recordGapCenter + 459518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 459518]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07857_not_prime : ¬(recordGapCenter + 459530).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 459530]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07858_not_prime : ¬(recordGapCenter + 459618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 459618]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07859_not_prime : ¬(recordGapCenter + 459698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 459698]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07860_not_prime : ¬(recordGapCenter + 459896).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 459896]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07861_not_prime : ¬(recordGapCenter + 460002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 460002]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07862_not_prime : ¬(recordGapCenter + 460178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 460178]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07863_not_prime : ¬(recordGapCenter + 460202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 460202]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07864_not_prime : ¬(recordGapCenter + 460268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 460268]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07865_not_prime : ¬(recordGapCenter + 460398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 460398]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07866_not_prime : ¬(recordGapCenter + 460406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 460406]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07867_not_prime : ¬(recordGapCenter + 460442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 460442]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07868_not_prime : ¬(recordGapCenter + 460472).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 460472]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07869_not_prime : ¬(recordGapCenter + 460562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 460562]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07870_not_prime : ¬(recordGapCenter + 460652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 460652]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07871_not_prime : ¬(recordGapCenter + 460682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 460682]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

theorem fullRecordGapTerm07872_not_prime : ¬(recordGapCenter + 460706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 460706]
  · apply fullRecordGapRow00123_fermat
    simp [fullRecordGapRow00123_values]

end PrimeFactorUnimodality
