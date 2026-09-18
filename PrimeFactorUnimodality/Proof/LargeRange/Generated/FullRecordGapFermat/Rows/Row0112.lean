import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00112_values : List Nat :=
  [fullRecordGapCenterValue + 401942,
    fullRecordGapCenterValue + 401966,
    fullRecordGapCenterValue + 401972,
    fullRecordGapCenterValue + 402092,
    fullRecordGapCenterValue + 402098,
    fullRecordGapCenterValue + 402126,
    fullRecordGapCenterValue + 402188,
    fullRecordGapCenterValue + 402386,
    fullRecordGapCenterValue + 402452,
    fullRecordGapCenterValue + 402692,
    fullRecordGapCenterValue + 402806,
    fullRecordGapCenterValue + 402812,
    fullRecordGapCenterValue + 402902,
    fullRecordGapCenterValue + 402932,
    fullRecordGapCenterValue + 403016,
    fullRecordGapCenterValue + 403076,
    fullRecordGapCenterValue + 403148,
    fullRecordGapCenterValue + 403266,
    fullRecordGapCenterValue + 403292,
    fullRecordGapCenterValue + 403302,
    fullRecordGapCenterValue + 403386,
    fullRecordGapCenterValue + 403412,
    fullRecordGapCenterValue + 403418,
    fullRecordGapCenterValue + 403538,
    fullRecordGapCenterValue + 403562,
    fullRecordGapCenterValue + 403566,
    fullRecordGapCenterValue + 403638,
    fullRecordGapCenterValue + 403778,
    fullRecordGapCenterValue + 403838,
    fullRecordGapCenterValue + 403946,
    fullRecordGapCenterValue + 404126,
    fullRecordGapCenterValue + 404252,
    fullRecordGapCenterValue + 404258,
    fullRecordGapCenterValue + 404346,
    fullRecordGapCenterValue + 404366,
    fullRecordGapCenterValue + 404402,
    fullRecordGapCenterValue + 404526,
    fullRecordGapCenterValue + 404762,
    fullRecordGapCenterValue + 404792,
    fullRecordGapCenterValue + 404958,
    fullRecordGapCenterValue + 405000,
    fullRecordGapCenterValue + 405116,
    fullRecordGapCenterValue + 405176,
    fullRecordGapCenterValue + 405282,
    fullRecordGapCenterValue + 405332,
    fullRecordGapCenterValue + 405386,
    fullRecordGapCenterValue + 405402,
    fullRecordGapCenterValue + 405452,
    fullRecordGapCenterValue + 405458,
    fullRecordGapCenterValue + 405506,
    fullRecordGapCenterValue + 405906,
    fullRecordGapCenterValue + 405932,
    fullRecordGapCenterValue + 405998,
    fullRecordGapCenterValue + 406052,
    fullRecordGapCenterValue + 406338,
    fullRecordGapCenterValue + 406418,
    fullRecordGapCenterValue + 406442,
    fullRecordGapCenterValue + 406506,
    fullRecordGapCenterValue + 406560,
    fullRecordGapCenterValue + 406646,
    fullRecordGapCenterValue + 406682,
    fullRecordGapCenterValue + 406698,
    fullRecordGapCenterValue + 406712,
    fullRecordGapCenterValue + 406856]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00112_fermat : ∀ n ∈ fullRecordGapRow00112_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07105_not_prime : ¬(recordGapCenter + 401942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401942]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07106_not_prime : ¬(recordGapCenter + 401966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401966]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07107_not_prime : ¬(recordGapCenter + 401972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401972]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07108_not_prime : ¬(recordGapCenter + 402092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 402092]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07109_not_prime : ¬(recordGapCenter + 402098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 402098]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07110_not_prime : ¬(recordGapCenter + 402126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 402126]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07111_not_prime : ¬(recordGapCenter + 402188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 402188]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07112_not_prime : ¬(recordGapCenter + 402386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 402386]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07113_not_prime : ¬(recordGapCenter + 402452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 402452]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07114_not_prime : ¬(recordGapCenter + 402692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 402692]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07115_not_prime : ¬(recordGapCenter + 402806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 402806]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07116_not_prime : ¬(recordGapCenter + 402812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 402812]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07117_not_prime : ¬(recordGapCenter + 402902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 402902]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07118_not_prime : ¬(recordGapCenter + 402932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 402932]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07119_not_prime : ¬(recordGapCenter + 403016).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403016]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07120_not_prime : ¬(recordGapCenter + 403076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403076]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07121_not_prime : ¬(recordGapCenter + 403148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403148]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07122_not_prime : ¬(recordGapCenter + 403266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403266]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07123_not_prime : ¬(recordGapCenter + 403292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403292]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07124_not_prime : ¬(recordGapCenter + 403302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403302]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07125_not_prime : ¬(recordGapCenter + 403386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403386]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07126_not_prime : ¬(recordGapCenter + 403412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403412]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07127_not_prime : ¬(recordGapCenter + 403418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403418]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07128_not_prime : ¬(recordGapCenter + 403538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403538]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07129_not_prime : ¬(recordGapCenter + 403562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403562]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07130_not_prime : ¬(recordGapCenter + 403566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403566]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07131_not_prime : ¬(recordGapCenter + 403638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403638]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07132_not_prime : ¬(recordGapCenter + 403778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403778]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07133_not_prime : ¬(recordGapCenter + 403838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403838]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07134_not_prime : ¬(recordGapCenter + 403946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403946]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07135_not_prime : ¬(recordGapCenter + 404126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 404126]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07136_not_prime : ¬(recordGapCenter + 404252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 404252]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07137_not_prime : ¬(recordGapCenter + 404258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 404258]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07138_not_prime : ¬(recordGapCenter + 404346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 404346]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07139_not_prime : ¬(recordGapCenter + 404366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 404366]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07140_not_prime : ¬(recordGapCenter + 404402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 404402]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07141_not_prime : ¬(recordGapCenter + 404526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 404526]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07142_not_prime : ¬(recordGapCenter + 404762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 404762]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07143_not_prime : ¬(recordGapCenter + 404792).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 404792]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07144_not_prime : ¬(recordGapCenter + 404958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 404958]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07145_not_prime : ¬(recordGapCenter + 405000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 405000]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07146_not_prime : ¬(recordGapCenter + 405116).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 405116]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07147_not_prime : ¬(recordGapCenter + 405176).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 405176]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07148_not_prime : ¬(recordGapCenter + 405282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 405282]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07149_not_prime : ¬(recordGapCenter + 405332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 405332]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07150_not_prime : ¬(recordGapCenter + 405386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 405386]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07151_not_prime : ¬(recordGapCenter + 405402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 405402]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07152_not_prime : ¬(recordGapCenter + 405452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 405452]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07153_not_prime : ¬(recordGapCenter + 405458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 405458]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07154_not_prime : ¬(recordGapCenter + 405506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 405506]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07155_not_prime : ¬(recordGapCenter + 405906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 405906]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07156_not_prime : ¬(recordGapCenter + 405932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 405932]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07157_not_prime : ¬(recordGapCenter + 405998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 405998]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07158_not_prime : ¬(recordGapCenter + 406052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 406052]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07159_not_prime : ¬(recordGapCenter + 406338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 406338]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07160_not_prime : ¬(recordGapCenter + 406418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 406418]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07161_not_prime : ¬(recordGapCenter + 406442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 406442]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07162_not_prime : ¬(recordGapCenter + 406506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 406506]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07163_not_prime : ¬(recordGapCenter + 406560).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 406560]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07164_not_prime : ¬(recordGapCenter + 406646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 406646]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07165_not_prime : ¬(recordGapCenter + 406682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 406682]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07166_not_prime : ¬(recordGapCenter + 406698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 406698]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07167_not_prime : ¬(recordGapCenter + 406712).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 406712]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

theorem fullRecordGapTerm07168_not_prime : ¬(recordGapCenter + 406856).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 406856]
  · apply fullRecordGapRow00112_fermat
    simp [fullRecordGapRow00112_values]

end PrimeFactorUnimodality
