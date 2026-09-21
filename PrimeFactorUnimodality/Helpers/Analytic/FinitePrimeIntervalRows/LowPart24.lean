import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 24 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
def lowPocklingtonData24 : List PocklingtonData := [
    { n := 17939, F := 17938, R := 1, a := 2, factors := [2, 8969], residues := [(2, 8969), (8969, 5980)] },
    { n := 17957, F := 17956, R := 1, a := 2, factors := [2, 2, 67, 67], residues := [(2, 8978), (67, 4269)] },
    { n := 17959, F := 17958, R := 1, a := 6, factors := [2, 3, 41, 73], residues := [(2, 8979), (3, 14943), (41, 6642), (73, 4268)] },
    { n := 17971, F := 17970, R := 1, a := 3, factors := [2, 3, 5, 599], residues := [(2, 8985), (3, 912), (5, 13702), (599, 1122)] },
    { n := 17977, F := 17976, R := 1, a := 5, factors := [2, 2, 2, 3, 7, 107], residues := [(2, 8988), (3, 13590), (7, 3962), (107, 6547)] },
    { n := 17981, F := 17980, R := 1, a := 2, factors := [2, 2, 5, 29, 31], residues := [(2, 8990), (5, 3990), (29, 11846), (31, 6443)] },
    { n := 17987, F := 17986, R := 1, a := 5, factors := [2, 17, 23, 23], residues := [(2, 8993), (17, 16746), (23, 8008)] },
    { n := 17989, F := 17988, R := 1, a := 2, factors := [2, 2, 3, 1499], residues := [(2, 8994), (3, 15892), (1499, 7692)] },
    { n := 18013, F := 18012, R := 1, a := 2, factors := [2, 2, 3, 19, 79], residues := [(2, 9006), (3, 6780), (19, 8913), (79, 6066)] },
    { n := 18041, F := 18040, R := 1, a := 3, factors := [2, 2, 2, 5, 11, 41], residues := [(2, 9020), (5, 6345), (11, 8339), (41, 8337)] }
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPocklingtonData24_valid : PocklingtonRow.Valid lowPocklingtonData24 := by
  apply PocklingtonRow.valid_of_decide_all
  decide

theorem lowPocklingtonPrime24 (i : Fin lowPocklingtonData24.length) :
    Nat.Prime (lowPocklingtonData24.get i).n := by
  exact PocklingtonRow.prime_of_mem lowPocklingtonData24_valid (List.get_mem _ _)
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17929) (q := 17939) (by
      have hp := lowPocklingtonPrime24 ⟨0, by simp [lowPocklingtonData24]⟩
      simpa [lowPocklingtonData24] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17939) (q := 17957) (by
      have hp := lowPocklingtonPrime24 ⟨1, by simp [lowPocklingtonData24]⟩
      simpa [lowPocklingtonData24] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17957) (q := 17959) (by
      have hp := lowPocklingtonPrime24 ⟨2, by simp [lowPocklingtonData24]⟩
      simpa [lowPocklingtonData24] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17959) (q := 17971) (by
      have hp := lowPocklingtonPrime24 ⟨3, by simp [lowPocklingtonData24]⟩
      simpa [lowPocklingtonData24] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17971) (q := 17977) (by
      have hp := lowPocklingtonPrime24 ⟨4, by simp [lowPocklingtonData24]⟩
      simpa [lowPocklingtonData24] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17977) (q := 17981) (by
      have hp := lowPocklingtonPrime24 ⟨5, by simp [lowPocklingtonData24]⟩
      simpa [lowPocklingtonData24] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17981) (q := 17987) (by
      have hp := lowPocklingtonPrime24 ⟨6, by simp [lowPocklingtonData24]⟩
      simpa [lowPocklingtonData24] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17987) (q := 17989) (by
      have hp := lowPocklingtonPrime24 ⟨7, by simp [lowPocklingtonData24]⟩
      simpa [lowPocklingtonData24] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part11_chain :
    DusartPrimeRowsChain 17929 17988 dusartPrimeRows_17159_18040_part11 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17989) (q := 18013) (by
      have hp := lowPocklingtonPrime24 ⟨8, by simp [lowPocklingtonData24]⟩
      simpa [lowPocklingtonData24] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 18013) (q := 18041) (by
      have hp := lowPocklingtonPrime24 ⟨9, by simp [lowPocklingtonData24]⟩
      simpa [lowPocklingtonData24] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part12_chain :
    DusartPrimeRowsChain 17989 18040 dusartPrimeRows_17159_18040_part12 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.empty
      norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]
