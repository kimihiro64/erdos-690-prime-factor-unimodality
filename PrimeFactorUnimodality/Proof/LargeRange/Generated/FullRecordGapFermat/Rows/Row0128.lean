import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00128_values : List Nat :=
  [fullRecordGapCenterValue + 478766,
    fullRecordGapCenterValue + 478796,
    fullRecordGapCenterValue + 478866,
    fullRecordGapCenterValue + 478938,
    fullRecordGapCenterValue + 479036,
    fullRecordGapCenterValue + 479078,
    fullRecordGapCenterValue + 479096,
    fullRecordGapCenterValue + 479238,
    fullRecordGapCenterValue + 479390,
    fullRecordGapCenterValue + 479418,
    fullRecordGapCenterValue + 479558,
    fullRecordGapCenterValue + 479768,
    fullRecordGapCenterValue + 479802,
    fullRecordGapCenterValue + 479810,
    fullRecordGapCenterValue + 480000,
    fullRecordGapCenterValue + 480068,
    fullRecordGapCenterValue + 480188,
    fullRecordGapCenterValue + 480218,
    fullRecordGapCenterValue + 480230,
    fullRecordGapCenterValue + 480296,
    fullRecordGapCenterValue + 480302,
    fullRecordGapCenterValue + 480306,
    fullRecordGapCenterValue + 480566,
    fullRecordGapCenterValue + 480642,
    fullRecordGapCenterValue + 480698,
    fullRecordGapCenterValue + 480728,
    fullRecordGapCenterValue + 480758,
    fullRecordGapCenterValue + 480846,
    fullRecordGapCenterValue + 480918,
    fullRecordGapCenterValue + 480932,
    fullRecordGapCenterValue + 481112,
    fullRecordGapCenterValue + 481142,
    fullRecordGapCenterValue + 481178,
    fullRecordGapCenterValue + 481196,
    fullRecordGapCenterValue + 481250,
    fullRecordGapCenterValue + 481310,
    fullRecordGapCenterValue + 481398,
    fullRecordGapCenterValue + 481478,
    fullRecordGapCenterValue + 481652,
    fullRecordGapCenterValue + 481706,
    fullRecordGapCenterValue + 481722,
    fullRecordGapCenterValue + 481736,
    fullRecordGapCenterValue + 481766,
    fullRecordGapCenterValue + 481790,
    fullRecordGapCenterValue + 482046,
    fullRecordGapCenterValue + 482168,
    fullRecordGapCenterValue + 482228,
    fullRecordGapCenterValue + 482252,
    fullRecordGapCenterValue + 482276,
    fullRecordGapCenterValue + 482322,
    fullRecordGapCenterValue + 482442,
    fullRecordGapCenterValue + 482606,
    fullRecordGapCenterValue + 482696,
    fullRecordGapCenterValue + 482756,
    fullRecordGapCenterValue + 482826,
    fullRecordGapCenterValue + 482858,
    fullRecordGapCenterValue + 482882,
    fullRecordGapCenterValue + 482906,
    fullRecordGapCenterValue + 482946,
    fullRecordGapCenterValue + 482948,
    fullRecordGapCenterValue + 482990,
    fullRecordGapCenterValue + 483068,
    fullRecordGapCenterValue + 483078,
    fullRecordGapCenterValue + 483122]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00128_fermat : ∀ n ∈ fullRecordGapRow00128_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08129_not_prime : ¬(recordGapCenter + 478766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 478766]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08130_not_prime : ¬(recordGapCenter + 478796).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 478796]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08131_not_prime : ¬(recordGapCenter + 478866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 478866]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08132_not_prime : ¬(recordGapCenter + 478938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 478938]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08133_not_prime : ¬(recordGapCenter + 479036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 479036]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08134_not_prime : ¬(recordGapCenter + 479078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 479078]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08135_not_prime : ¬(recordGapCenter + 479096).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 479096]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08136_not_prime : ¬(recordGapCenter + 479238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 479238]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08137_not_prime : ¬(recordGapCenter + 479390).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 479390]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08138_not_prime : ¬(recordGapCenter + 479418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 479418]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08139_not_prime : ¬(recordGapCenter + 479558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 479558]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08140_not_prime : ¬(recordGapCenter + 479768).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 479768]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08141_not_prime : ¬(recordGapCenter + 479802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 479802]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08142_not_prime : ¬(recordGapCenter + 479810).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 479810]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08143_not_prime : ¬(recordGapCenter + 480000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480000]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08144_not_prime : ¬(recordGapCenter + 480068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480068]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08145_not_prime : ¬(recordGapCenter + 480188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480188]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08146_not_prime : ¬(recordGapCenter + 480218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480218]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08147_not_prime : ¬(recordGapCenter + 480230).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480230]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08148_not_prime : ¬(recordGapCenter + 480296).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480296]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08149_not_prime : ¬(recordGapCenter + 480302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480302]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08150_not_prime : ¬(recordGapCenter + 480306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480306]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08151_not_prime : ¬(recordGapCenter + 480566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480566]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08152_not_prime : ¬(recordGapCenter + 480642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480642]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08153_not_prime : ¬(recordGapCenter + 480698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480698]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08154_not_prime : ¬(recordGapCenter + 480728).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480728]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08155_not_prime : ¬(recordGapCenter + 480758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480758]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08156_not_prime : ¬(recordGapCenter + 480846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480846]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08157_not_prime : ¬(recordGapCenter + 480918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480918]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08158_not_prime : ¬(recordGapCenter + 480932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480932]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08159_not_prime : ¬(recordGapCenter + 481112).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481112]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08160_not_prime : ¬(recordGapCenter + 481142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481142]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08161_not_prime : ¬(recordGapCenter + 481178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481178]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08162_not_prime : ¬(recordGapCenter + 481196).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481196]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08163_not_prime : ¬(recordGapCenter + 481250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481250]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08164_not_prime : ¬(recordGapCenter + 481310).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481310]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08165_not_prime : ¬(recordGapCenter + 481398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481398]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08166_not_prime : ¬(recordGapCenter + 481478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481478]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08167_not_prime : ¬(recordGapCenter + 481652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481652]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08168_not_prime : ¬(recordGapCenter + 481706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481706]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08169_not_prime : ¬(recordGapCenter + 481722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481722]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08170_not_prime : ¬(recordGapCenter + 481736).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481736]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08171_not_prime : ¬(recordGapCenter + 481766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481766]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08172_not_prime : ¬(recordGapCenter + 481790).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481790]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08173_not_prime : ¬(recordGapCenter + 482046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482046]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08174_not_prime : ¬(recordGapCenter + 482168).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482168]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08175_not_prime : ¬(recordGapCenter + 482228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482228]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08176_not_prime : ¬(recordGapCenter + 482252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482252]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08177_not_prime : ¬(recordGapCenter + 482276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482276]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08178_not_prime : ¬(recordGapCenter + 482322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482322]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08179_not_prime : ¬(recordGapCenter + 482442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482442]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08180_not_prime : ¬(recordGapCenter + 482606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482606]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08181_not_prime : ¬(recordGapCenter + 482696).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482696]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08182_not_prime : ¬(recordGapCenter + 482756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482756]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08183_not_prime : ¬(recordGapCenter + 482826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482826]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08184_not_prime : ¬(recordGapCenter + 482858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482858]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08185_not_prime : ¬(recordGapCenter + 482882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482882]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08186_not_prime : ¬(recordGapCenter + 482906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482906]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08187_not_prime : ¬(recordGapCenter + 482946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482946]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08188_not_prime : ¬(recordGapCenter + 482948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482948]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08189_not_prime : ¬(recordGapCenter + 482990).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482990]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08190_not_prime : ¬(recordGapCenter + 483068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483068]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08191_not_prime : ¬(recordGapCenter + 483078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483078]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

theorem fullRecordGapTerm08192_not_prime : ¬(recordGapCenter + 483122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483122]
  · apply fullRecordGapRow00128_fermat
    simp [fullRecordGapRow00128_values]

end PrimeFactorUnimodality
