import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00030_values : List Nat :=
  [fullRecordGapCenterValue - 305878,
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
    fullRecordGapCenterValue - 299458]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00030_fermat : ∀ n ∈ fullRecordGapRow00030_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01857_not_prime : ¬(recordGapCenter - 305878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305878]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01858_not_prime : ¬(recordGapCenter - 305818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305818]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01859_not_prime : ¬(recordGapCenter - 305814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305814]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01860_not_prime : ¬(recordGapCenter - 305692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305692]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01861_not_prime : ¬(recordGapCenter - 305638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305638]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01862_not_prime : ¬(recordGapCenter - 305454).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305454]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01863_not_prime : ¬(recordGapCenter - 305212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305212]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01864_not_prime : ¬(recordGapCenter - 305202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305202]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01865_not_prime : ¬(recordGapCenter - 305142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305142]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01866_not_prime : ¬(recordGapCenter - 305134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305134]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01867_not_prime : ¬(recordGapCenter - 305062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305062]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01868_not_prime : ¬(recordGapCenter - 305044).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 305044]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01869_not_prime : ¬(recordGapCenter - 304918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 304918]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01870_not_prime : ¬(recordGapCenter - 304834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 304834]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01871_not_prime : ¬(recordGapCenter - 304762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 304762]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01872_not_prime : ¬(recordGapCenter - 304534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 304534]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01873_not_prime : ¬(recordGapCenter - 304518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 304518]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01874_not_prime : ¬(recordGapCenter - 304498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 304498]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01875_not_prime : ¬(recordGapCenter - 304338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 304338]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01876_not_prime : ¬(recordGapCenter - 304324).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 304324]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01877_not_prime : ¬(recordGapCenter - 304294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 304294]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01878_not_prime : ¬(recordGapCenter - 304098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 304098]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01879_not_prime : ¬(recordGapCenter - 304078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 304078]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01880_not_prime : ¬(recordGapCenter - 303988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 303988]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01881_not_prime : ¬(recordGapCenter - 303694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 303694]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01882_not_prime : ¬(recordGapCenter - 303652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 303652]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01883_not_prime : ¬(recordGapCenter - 303532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 303532]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01884_not_prime : ¬(recordGapCenter - 303522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 303522]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01885_not_prime : ¬(recordGapCenter - 303412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 303412]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01886_not_prime : ¬(recordGapCenter - 303172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 303172]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01887_not_prime : ¬(recordGapCenter - 303018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 303018]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01888_not_prime : ¬(recordGapCenter - 302754).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 302754]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01889_not_prime : ¬(recordGapCenter - 302308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 302308]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01890_not_prime : ¬(recordGapCenter - 302298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 302298]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01891_not_prime : ¬(recordGapCenter - 302154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 302154]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01892_not_prime : ¬(recordGapCenter - 301762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 301762]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01893_not_prime : ¬(recordGapCenter - 301612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 301612]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01894_not_prime : ¬(recordGapCenter - 301564).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 301564]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01895_not_prime : ¬(recordGapCenter - 301468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 301468]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01896_not_prime : ¬(recordGapCenter - 301348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 301348]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01897_not_prime : ¬(recordGapCenter - 301234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 301234]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01898_not_prime : ¬(recordGapCenter - 301174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 301174]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01899_not_prime : ¬(recordGapCenter - 300954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 300954]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01900_not_prime : ¬(recordGapCenter - 300862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 300862]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01901_not_prime : ¬(recordGapCenter - 300774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 300774]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01902_not_prime : ¬(recordGapCenter - 300772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 300772]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01903_not_prime : ¬(recordGapCenter - 300754).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 300754]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01904_not_prime : ¬(recordGapCenter - 300738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 300738]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01905_not_prime : ¬(recordGapCenter - 300522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 300522]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01906_not_prime : ¬(recordGapCenter - 300442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 300442]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01907_not_prime : ¬(recordGapCenter - 300418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 300418]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01908_not_prime : ¬(recordGapCenter - 300394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 300394]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01909_not_prime : ¬(recordGapCenter - 300178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 300178]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01910_not_prime : ¬(recordGapCenter - 300052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 300052]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01911_not_prime : ¬(recordGapCenter - 300022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 300022]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01912_not_prime : ¬(recordGapCenter - 299938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 299938]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01913_not_prime : ¬(recordGapCenter - 299878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 299878]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01914_not_prime : ¬(recordGapCenter - 299674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 299674]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01915_not_prime : ¬(recordGapCenter - 299658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 299658]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01916_not_prime : ¬(recordGapCenter - 299634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 299634]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01917_not_prime : ¬(recordGapCenter - 299542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 299542]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01918_not_prime : ¬(recordGapCenter - 299518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 299518]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01919_not_prime : ¬(recordGapCenter - 299514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 299514]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

theorem fullRecordGapTerm01920_not_prime : ¬(recordGapCenter - 299458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 299458]
  · apply fullRecordGapRow00030_fermat
    simp [fullRecordGapRow00030_values]

end PrimeFactorUnimodality
