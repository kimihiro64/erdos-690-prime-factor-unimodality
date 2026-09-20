import PrimeFactorUnimodality.Helpers.Analytic.DusartLemma33MidrangeRows

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-! # Coverage of Dusart's Lemma 3.3 midrange rows

This module proves that the midrange rows cover the complete bounded interval. -/

namespace PrimeFactorUnimodality

noncomputable section

theorem dusartLemma33MidrangeRowsCover :
    DusartLemma33FiniteRowsCover dusartLemma33MidrangeRows 10000000 := by
  intro x hx hX
  let n : Nat := ⌊x⌋₊
  have hnlow : (2402 : Nat) ≤ n := by
    dsimp [n]
    exact Nat.le_floor (by linarith)
  have hnreal : (n : Real) ≤ x := by
    dsimp [n]
    exact Nat.floor_le hx.le
  have hnupper : x < (n : Real) + 1 := by
    simpa only [n] using Nat.lt_floor_add_one x
  have hnmax : n ≤ 10000000 := by
    have hnr : (n : Real) ≤ 10000000 := hnreal.trans hX
    exact_mod_cast hnr

  by_cases h0 : n ≤ 2808
  · refine ⟨dusartLemma33MidrangeRow_2402_2808, by simp, ?_, ?_⟩
    · have hnat : 2402 ≤ n := by omega
      have hreal : (2402 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 2808 := by exact_mod_cast h0
      linarith
  by_cases h1 : n ≤ 3124
  · refine ⟨dusartLemma33MidrangeRow_2809_3124, by simp, ?_, ?_⟩
    · have hnat : 2809 ≤ n := by omega
      have hreal : (2809 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 3124 := by exact_mod_cast h1
      linarith
  by_cases h2 : n ≤ 3480
  · refine ⟨dusartLemma33MidrangeRow_3125_3480, by simp, ?_, ?_⟩
    · have hnat : 3125 ≤ n := by omega
      have hreal : (3125 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 3480 := by exact_mod_cast h2
      linarith
  by_cases h3 : n ≤ 3720
  · refine ⟨dusartLemma33MidrangeRow_3481_3720, by simp, ?_, ?_⟩
    · have hnat : 3481 ≤ n := by omega
      have hreal : (3481 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 3720 := by exact_mod_cast h3
      linarith
  by_cases h4 : n ≤ 4488
  · refine ⟨dusartLemma33MidrangeRow_3721_4488, by simp, ?_, ?_⟩
    · have hnat : 3721 ≤ n := by omega
      have hreal : (3721 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 4488 := by exact_mod_cast h4
      linarith
  by_cases h5 : n ≤ 5040
  · refine ⟨dusartLemma33MidrangeRow_4489_5040, by simp, ?_, ?_⟩
    · have hnat : 4489 ≤ n := by omega
      have hreal : (4489 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 5040 := by exact_mod_cast h5
      linarith
  by_cases h6 : n ≤ 5328
  · refine ⟨dusartLemma33MidrangeRow_5041_5328, by simp, ?_, ?_⟩
    · have hnat : 5041 ≤ n := by omega
      have hreal : (5041 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 5328 := by exact_mod_cast h6
      linarith
  by_cases h7 : n ≤ 6240
  · refine ⟨dusartLemma33MidrangeRow_5329_6240, by simp, ?_, ?_⟩
    · have hnat : 5329 ≤ n := by omega
      have hreal : (5329 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 6240 := by exact_mod_cast h7
      linarith
  by_cases h8 : n ≤ 6858
  · refine ⟨dusartLemma33MidrangeRow_6241_6858, by simp, ?_, ?_⟩
    · have hnat : 6241 ≤ n := by omega
      have hreal : (6241 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 6858 := by exact_mod_cast h8
      linarith
  by_cases h9 : n ≤ 6888
  · refine ⟨dusartLemma33MidrangeRow_6859_6888, by simp, ?_, ?_⟩
    · have hnat : 6859 ≤ n := by omega
      have hreal : (6859 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 6888 := by exact_mod_cast h9
      linarith
  by_cases h10 : n ≤ 7920
  · refine ⟨dusartLemma33MidrangeRow_6889_7920, by simp, ?_, ?_⟩
    · have hnat : 6889 ≤ n := by omega
      have hreal : (6889 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 7920 := by exact_mod_cast h10
      linarith
  by_cases h11 : n ≤ 9408
  · refine ⟨dusartLemma33MidrangeRow_7921_9408, by simp, ?_, ?_⟩
    · have hnat : 7921 ≤ n := by omega
      have hreal : (7921 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 9408 := by exact_mod_cast h11
      linarith
  by_cases h12 : n ≤ 10200
  · refine ⟨dusartLemma33MidrangeRow_9409_10200, by simp, ?_, ?_⟩
    · have hnat : 9409 ≤ n := by omega
      have hreal : (9409 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 10200 := by exact_mod_cast h12
      linarith
  by_cases h13 : n ≤ 11448
  · refine ⟨dusartLemma33MidrangeRow_10201_11448, by simp, ?_, ?_⟩
    · have hnat : 10201 ≤ n := by omega
      have hreal : (10201 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 11448 := by exact_mod_cast h13
      linarith
  by_cases h14 : n ≤ 12166
  · refine ⟨dusartLemma33MidrangeRow_11449_12166, by simp, ?_, ?_⟩
    · have hnat : 11449 ≤ n := by omega
      have hreal : (11449 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 12166 := by exact_mod_cast h14
      linarith
  by_cases h15 : n ≤ 12768
  · refine ⟨dusartLemma33MidrangeRow_12167_12768, by simp, ?_, ?_⟩
    · have hnat : 12167 ≤ n := by omega
      have hreal : (12167 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 12768 := by exact_mod_cast h15
      linarith
  by_cases h16 : n ≤ 16128
  · refine ⟨dusartLemma33MidrangeRow_12769_16128, by simp, ?_, ?_⟩
    · have hnat : 12769 ≤ n := by omega
      have hreal : (12769 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 16128 := by exact_mod_cast h16
      linarith
  by_cases h17 : n ≤ 17160
  · refine ⟨dusartLemma33MidrangeRow_16129_17160, by simp, ?_, ?_⟩
    · have hnat : 16129 ≤ n := by omega
      have hreal : (16129 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 17160 := by exact_mod_cast h17
      linarith
  by_cases h18 : n ≤ 18768
  · refine ⟨dusartLemma33MidrangeRow_17161_18768, by simp, ?_, ?_⟩
    · have hnat : 17161 ≤ n := by omega
      have hreal : (17161 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 18768 := by exact_mod_cast h18
      linarith
  by_cases h19 : n ≤ 19320
  · refine ⟨dusartLemma33MidrangeRow_18769_19320, by simp, ?_, ?_⟩
    · have hnat : 18769 ≤ n := by omega
      have hreal : (18769 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 19320 := by exact_mod_cast h19
      linarith
  by_cases h20 : n ≤ 22200
  · refine ⟨dusartLemma33MidrangeRow_19321_22200, by simp, ?_, ?_⟩
    · have hnat : 19321 ≤ n := by omega
      have hreal : (19321 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 22200 := by exact_mod_cast h20
      linarith
  by_cases h21 : n ≤ 24388
  · refine ⟨dusartLemma33MidrangeRow_22201_24388, by simp, ?_, ?_⟩
    · have hnat : 22201 ≤ n := by omega
      have hreal : (22201 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 24388 := by exact_mod_cast h21
      linarith
  by_cases h22 : n ≤ 24648
  · refine ⟨dusartLemma33MidrangeRow_24389_24648, by simp, ?_, ?_⟩
    · have hnat : 24389 ≤ n := by omega
      have hreal : (24389 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 24648 := by exact_mod_cast h22
      linarith
  by_cases h23 : n ≤ 26568
  · refine ⟨dusartLemma33MidrangeRow_24649_26568, by simp, ?_, ?_⟩
    · have hnat : 24649 ≤ n := by omega
      have hreal : (24649 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 26568 := by exact_mod_cast h23
      linarith
  by_cases h24 : n ≤ 28560
  · refine ⟨dusartLemma33MidrangeRow_26569_28560, by simp, ?_, ?_⟩
    · have hnat : 26569 ≤ n := by omega
      have hreal : (26569 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 28560 := by exact_mod_cast h24
      linarith
  by_cases h25 : n ≤ 29928
  · refine ⟨dusartLemma33MidrangeRow_28561_29928, by simp, ?_, ?_⟩
    · have hnat : 28561 ≤ n := by omega
      have hreal : (28561 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 29928 := by exact_mod_cast h25
      linarith
  by_cases h26 : n ≤ 32040
  · refine ⟨dusartLemma33MidrangeRow_29929_32040, by simp, ?_, ?_⟩
    · have hnat : 29929 ≤ n := by omega
      have hreal : (29929 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 32040 := by exact_mod_cast h26
      linarith
  by_cases h27 : n ≤ 32760
  · refine ⟨dusartLemma33MidrangeRow_32041_32760, by simp, ?_, ?_⟩
    · have hnat : 32041 ≤ n := by omega
      have hreal : (32041 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 32760 := by exact_mod_cast h27
      linarith
  by_cases h28 : n ≤ 36480
  · refine ⟨dusartLemma33MidrangeRow_32761_36480, by simp, ?_, ?_⟩
    · have hnat : 32761 ≤ n := by omega
      have hreal : (32761 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 36480 := by exact_mod_cast h28
      linarith
  by_cases h29 : n ≤ 37248
  · refine ⟨dusartLemma33MidrangeRow_36481_37248, by simp, ?_, ?_⟩
    · have hnat : 36481 ≤ n := by omega
      have hreal : (36481 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 37248 := by exact_mod_cast h29
      linarith
  by_cases h30 : n ≤ 38808
  · refine ⟨dusartLemma33MidrangeRow_37249_38808, by simp, ?_, ?_⟩
    · have hnat : 37249 ≤ n := by omega
      have hreal : (37249 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 38808 := by exact_mod_cast h30
      linarith
  by_cases h31 : n ≤ 44520
  · refine ⟨dusartLemma33MidrangeRow_38809_44520, by simp, ?_, ?_⟩
    · have hnat : 38809 ≤ n := by omega
      have hreal : (38809 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 44520 := by exact_mod_cast h31
      linarith
  by_cases h32 : n ≤ 50652
  · refine ⟨dusartLemma33MidrangeRow_44521_50652, by simp, ?_, ?_⟩
    · have hnat : 44521 ≤ n := by omega
      have hreal : (44521 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 50652 := by exact_mod_cast h32
      linarith
  by_cases h33 : n ≤ 52440
  · refine ⟨dusartLemma33MidrangeRow_50653_52440, by simp, ?_, ?_⟩
    · have hnat : 50653 ≤ n := by omega
      have hreal : (50653 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 52440 := by exact_mod_cast h33
      linarith
  by_cases h34 : n ≤ 57120
  · refine ⟨dusartLemma33MidrangeRow_52441_57120, by simp, ?_, ?_⟩
    · have hnat : 52441 ≤ n := by omega
      have hreal : (52441 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 57120 := by exact_mod_cast h34
      linarith
  by_cases h35 : n ≤ 63000
  · refine ⟨dusartLemma33MidrangeRow_57121_63000, by simp, ?_, ?_⟩
    · have hnat : 57121 ≤ n := by omega
      have hreal : (57121 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 63000 := by exact_mod_cast h35
      linarith
  by_cases h36 : n ≤ 69168
  · refine ⟨dusartLemma33MidrangeRow_63001_69168, by simp, ?_, ?_⟩
    · have hnat : 63001 ≤ n := by omega
      have hreal : (63001 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 69168 := by exact_mod_cast h36
      linarith
  by_cases h37 : n ≤ 73440
  · refine ⟨dusartLemma33MidrangeRow_69169_73440, by simp, ?_, ?_⟩
    · have hnat : 69169 ≤ n := by omega
      have hreal : (69169 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 73440 := by exact_mod_cast h37
      linarith
  by_cases h38 : n ≤ 78960
  · refine ⟨dusartLemma33MidrangeRow_73441_78960, by simp, ?_, ?_⟩
    · have hnat : 73441 ≤ n := by omega
      have hreal : (73441 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 78960 := by exact_mod_cast h38
      linarith
  by_cases h39 : n ≤ 83520
  · refine ⟨dusartLemma33MidrangeRow_78961_83520, by simp, ?_, ?_⟩
    · have hnat : 78961 ≤ n := by omega
      have hreal : (78961 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 83520 := by exact_mod_cast h39
      linarith
  by_cases h40 : n ≤ 94248
  · refine ⟨dusartLemma33MidrangeRow_83521_94248, by simp, ?_, ?_⟩
    · have hnat : 83521 ≤ n := by omega
      have hreal : (83521 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 94248 := by exact_mod_cast h40
      linarith
  by_cases h41 : n ≤ 97968
  · refine ⟨dusartLemma33MidrangeRow_94249_97968, by simp, ?_, ?_⟩
    · have hnat : 94249 ≤ n := by omega
      have hreal : (94249 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 97968 := by exact_mod_cast h41
      linarith
  by_cases h42 : n ≤ 109560
  · refine ⟨dusartLemma33MidrangeRow_97969_109560, by simp, ?_, ?_⟩
    · have hnat : 97969 ≤ n := by omega
      have hreal : (97969 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 109560 := by exact_mod_cast h42
      linarith
  by_cases h43 : n ≤ 120408
  · refine ⟨dusartLemma33MidrangeRow_109561_120408, by simp, ?_, ?_⟩
    · have hnat : 109561 ≤ n := by omega
      have hreal : (109561 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 120408 := by exact_mod_cast h43
      linarith
  by_cases h44 : n ≤ 124608
  · refine ⟨dusartLemma33MidrangeRow_120409_124608, by simp, ?_, ?_⟩
    · have hnat : 120409 ≤ n := by omega
      have hreal : (120409 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 124608 := by exact_mod_cast h44
      linarith
  by_cases h45 : n ≤ 134688
  · refine ⟨dusartLemma33MidrangeRow_124609_134688, by simp, ?_, ?_⟩
    · have hnat : 124609 ≤ n := by omega
      have hreal : (124609 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 134688 := by exact_mod_cast h45
      linarith
  by_cases h46 : n ≤ 143640
  · refine ⟨dusartLemma33MidrangeRow_134689_143640, by simp, ?_, ?_⟩
    · have hnat : 134689 ≤ n := by omega
      have hreal : (134689 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 143640 := by exact_mod_cast h46
      linarith
  by_cases h47 : n ≤ 151320
  · refine ⟨dusartLemma33MidrangeRow_143641_151320, by simp, ?_, ?_⟩
    · have hnat : 143641 ≤ n := by omega
      have hreal : (143641 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 151320 := by exact_mod_cast h47
      linarith
  by_cases h48 : n ≤ 160800
  · refine ⟨dusartLemma33MidrangeRow_151321_160800, by simp, ?_, ?_⟩
    · have hnat : 151321 ≤ n := by omega
      have hreal : (151321 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 160800 := by exact_mod_cast h48
      linarith
  by_cases h49 : n ≤ 175560
  · refine ⟨dusartLemma33MidrangeRow_160801_175560, by simp, ?_, ?_⟩
    · have hnat : 160801 ≤ n := by omega
      have hreal : (160801 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 175560 := by exact_mod_cast h49
      linarith
  by_cases h50 : n ≤ 185760
  · refine ⟨dusartLemma33MidrangeRow_175561_185760, by simp, ?_, ?_⟩
    · have hnat : 175561 ≤ n := by omega
      have hreal : (175561 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 185760 := by exact_mod_cast h50
      linarith
  by_cases h51 : n ≤ 196248
  · refine ⟨dusartLemma33MidrangeRow_185761_196248, by simp, ?_, ?_⟩
    · have hnat : 185761 ≤ n := by omega
      have hreal : (185761 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 196248 := by exact_mod_cast h51
      linarith
  by_cases h52 : n ≤ 208848
  · refine ⟨dusartLemma33MidrangeRow_196249_208848, by simp, ?_, ?_⟩
    · have hnat : 196249 ≤ n := by omega
      have hreal : (196249 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 208848 := by exact_mod_cast h52
      linarith
  by_cases h53 : n ≤ 218088
  · refine ⟨dusartLemma33MidrangeRow_208849_218088, by simp, ?_, ?_⟩
    · have hnat : 208849 ≤ n := by omega
      have hreal : (208849 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 218088 := by exact_mod_cast h53
      linarith
  by_cases h54 : n ≤ 237168
  · refine ⟨dusartLemma33MidrangeRow_218089_237168, by simp, ?_, ?_⟩
    · have hnat : 218089 ≤ n := by omega
      have hreal : (218089 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 237168 := by exact_mod_cast h54
      linarith
  by_cases h55 : n ≤ 253008
  · refine ⟨dusartLemma33MidrangeRow_237169_253008, by simp, ?_, ?_⟩
    · have hnat : 237169 ≤ n := by omega
      have hreal : (237169 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 253008 := by exact_mod_cast h55
      linarith
  by_cases h56 : n ≤ 273528
  · refine ⟨dusartLemma33MidrangeRow_253009_273528, by simp, ?_, ?_⟩
    · have hnat : 253009 ≤ n := by omega
      have hreal : (253009 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 273528 := by exact_mod_cast h56
      linarith
  by_cases h57 : n ≤ 300762
  · refine ⟨dusartLemma33MidrangeRow_273529_300762, by simp, ?_, ?_⟩
    · have hnat : 273529 ≤ n := by omega
      have hreal : (273529 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 300762 := by exact_mod_cast h57
      linarith
  by_cases h58 : n ≤ 323760
  · refine ⟨dusartLemma33MidrangeRow_300763_323760, by simp, ?_, ?_⟩
    · have hnat : 300763 ≤ n := by omega
      have hreal : (300763 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 323760 := by exact_mod_cast h58
      linarith
  by_cases h59 : n ≤ 344568
  · refine ⟨dusartLemma33MidrangeRow_323761_344568, by simp, ?_, ?_⟩
    · have hnat : 323761 ≤ n := by omega
      have hreal : (323761 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 344568 := by exact_mod_cast h59
      linarith
  by_cases h60 : n ≤ 361200
  · refine ⟨dusartLemma33MidrangeRow_344569_361200, by simp, ?_, ?_⟩
    · have hnat : 344569 ≤ n := by omega
      have hreal : (344569 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 361200 := by exact_mod_cast h60
      linarith
  by_cases h61 : n ≤ 380688
  · refine ⟨dusartLemma33MidrangeRow_361201_380688, by simp, ?_, ?_⟩
    · have hnat : 361201 ≤ n := by omega
      have hreal : (361201 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 380688 := by exact_mod_cast h61
      linarith
  by_cases h62 : n ≤ 398160
  · refine ⟨dusartLemma33MidrangeRow_380689_398160, by simp, ?_, ?_⟩
    · have hnat : 380689 ≤ n := by omega
      have hreal : (380689 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 398160 := by exact_mod_cast h62
      linarith
  by_cases h63 : n ≤ 418608
  · refine ⟨dusartLemma33MidrangeRow_398161_418608, by simp, ?_, ?_⟩
    · have hnat : 398161 ≤ n := by omega
      have hreal : (398161 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 418608 := by exact_mod_cast h63
      linarith
  by_cases h64 : n ≤ 436920
  · refine ⟨dusartLemma33MidrangeRow_418609_436920, by simp, ?_, ?_⟩
    · have hnat : 418609 ≤ n := by omega
      have hreal : (418609 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 436920 := by exact_mod_cast h64
      linarith
  by_cases h65 : n ≤ 466488
  · refine ⟨dusartLemma33MidrangeRow_436921_466488, by simp, ?_, ?_⟩
    · have hnat : 436921 ≤ n := by omega
      have hreal : (436921 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 466488 := by exact_mod_cast h65
      linarith
  by_cases h66 : n ≤ 502680
  · refine ⟨dusartLemma33MidrangeRow_466489_502680, by simp, ?_, ?_⟩
    · have hnat : 466489 ≤ n := by omega
      have hreal : (466489 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 502680 := by exact_mod_cast h66
      linarith
  by_cases h67 : n ≤ 537288
  · refine ⟨dusartLemma33MidrangeRow_502681_537288, by simp, ?_, ?_⟩
    · have hnat : 502681 ≤ n := by omega
      have hreal : (502681 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 537288 := by exact_mod_cast h67
      linarith
  by_cases h68 : n ≤ 571786
  · refine ⟨dusartLemma33MidrangeRow_537289_571786, by simp, ?_, ?_⟩
    · have hnat : 537289 ≤ n := by omega
      have hreal : (537289 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 571786 := by exact_mod_cast h68
      linarith
  by_cases h69 : n ≤ 591360
  · refine ⟨dusartLemma33MidrangeRow_571787_591360, by simp, ?_, ?_⟩
    · have hnat : 571787 ≤ n := by omega
      have hreal : (571787 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 591360 := by exact_mod_cast h69
      linarith
  by_cases h70 : n ≤ 654480
  · refine ⟨dusartLemma33MidrangeRow_591361_654480, by simp, ?_, ?_⟩
    · have hnat : 591361 ≤ n := by omega
      have hreal : (591361 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 654480 := by exact_mod_cast h70
      linarith
  by_cases h71 : n ≤ 683928
  · refine ⟨dusartLemma33MidrangeRow_654481_683928, by simp, ?_, ?_⟩
    · have hnat : 654481 ≤ n := by omega
      have hreal : (654481 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 683928 := by exact_mod_cast h71
      linarith
  by_cases h72 : n ≤ 734448
  · refine ⟨dusartLemma33MidrangeRow_683929_734448, by simp, ?_, ?_⟩
    · have hnat : 683929 ≤ n := by omega
      have hreal : (683929 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 734448 := by exact_mod_cast h72
      linarith
  by_cases h73 : n ≤ 776160
  · refine ⟨dusartLemma33MidrangeRow_734449_776160, by simp, ?_, ?_⟩
    · have hnat : 734449 ≤ n := by omega
      have hreal : (734449 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 776160 := by exact_mod_cast h73
      linarith
  by_cases h74 : n ≤ 829920
  · refine ⟨dusartLemma33MidrangeRow_776161_829920, by simp, ?_, ?_⟩
    · have hnat : 776161 ≤ n := by omega
      have hreal : (776161 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 829920 := by exact_mod_cast h74
      linarith
  by_cases h75 : n ≤ 896808
  · refine ⟨dusartLemma33MidrangeRow_829921_896808, by simp, ?_, ?_⟩
    · have hnat : 829921 ≤ n := by omega
      have hreal : (829921 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 896808 := by exact_mod_cast h75
      linarith
  by_cases h76 : n ≤ 954528
  · refine ⟨dusartLemma33MidrangeRow_896809_954528, by simp, ?_, ?_⟩
    · have hnat : 896809 ≤ n := by omega
      have hreal : (896809 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 954528 := by exact_mod_cast h76
      linarith
  by_cases h77 : n ≤ 1026168
  · refine ⟨dusartLemma33MidrangeRow_954529_1026168, by simp, ?_, ?_⟩
    · have hnat : 954529 ≤ n := by omega
      have hreal : (954529 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 1026168 := by exact_mod_cast h77
      linarith
  by_cases h78 : n ≤ 1079520
  · refine ⟨dusartLemma33MidrangeRow_1026169_1079520, by simp, ?_, ?_⟩
    · have hnat : 1026169 ≤ n := by omega
      have hreal : (1026169 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 1079520 := by exact_mod_cast h78
      linarith
  by_cases h79 : n ≤ 1129968
  · refine ⟨dusartLemma33MidrangeRow_1079521_1129968, by simp, ?_, ?_⟩
    · have hnat : 1079521 ≤ n := by omega
      have hreal : (1079521 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 1129968 := by exact_mod_cast h79
      linarith
  by_cases h80 : n ≤ 1203408
  · refine ⟨dusartLemma33MidrangeRow_1129969_1203408, by simp, ?_, ?_⟩
    · have hnat : 1129969 ≤ n := by omega
      have hreal : (1129969 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 1203408 := by exact_mod_cast h80
      linarith
  by_cases h81 : n ≤ 1274640
  · refine ⟨dusartLemma33MidrangeRow_1203409_1274640, by simp, ?_, ?_⟩
    · have hnat : 1203409 ≤ n := by omega
      have hreal : (1203409 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 1274640 := by exact_mod_cast h81
      linarith
  by_cases h82 : n ≤ 1371240
  · refine ⟨dusartLemma33MidrangeRow_1274641_1371240, by simp, ?_, ?_⟩
    · have hnat : 1274641 ≤ n := by omega
      have hreal : (1274641 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 1371240 := by exact_mod_cast h82
      linarith
  by_cases h83 : n ≤ 1442896
  · refine ⟨dusartLemma33MidrangeRow_1371241_1442896, by simp, ?_, ?_⟩
    · have hnat : 1371241 ≤ n := by omega
      have hreal : (1371241 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 1442896 := by exact_mod_cast h83
      linarith
  by_cases h84 : n ≤ 1510440
  · refine ⟨dusartLemma33MidrangeRow_1442897_1510440, by simp, ?_, ?_⟩
    · have hnat : 1442897 ≤ n := by omega
      have hreal : (1442897 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 1510440 := by exact_mod_cast h84
      linarith
  by_cases h85 : n ≤ 1630728
  · refine ⟨dusartLemma33MidrangeRow_1510441_1630728, by simp, ?_, ?_⟩
    · have hnat : 1510441 ≤ n := by omega
      have hreal : (1510441 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 1630728 := by exact_mod_cast h85
      linarith
  by_cases h86 : n ≤ 1682208
  · refine ⟨dusartLemma33MidrangeRow_1630729_1682208, by simp, ?_, ?_⟩
    · have hnat : 1630729 ≤ n := by omega
      have hreal : (1630729 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 1682208 := by exact_mod_cast h86
      linarith
  by_cases h87 : n ≤ 1760928
  · refine ⟨dusartLemma33MidrangeRow_1682209_1760928, by simp, ?_, ?_⟩
    · have hnat : 1682209 ≤ n := by omega
      have hreal : (1682209 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 1760928 := by exact_mod_cast h87
      linarith
  by_cases h88 : n ≤ 1957200
  · refine ⟨dusartLemma33MidrangeRow_1760929_1957200, by simp, ?_, ?_⟩
    · have hnat : 1760929 ≤ n := by omega
      have hreal : (1760929 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 1957200 := by exact_mod_cast h88
      linarith
  by_cases h89 : n ≤ 2053488
  · refine ⟨dusartLemma33MidrangeRow_1957201_2053488, by simp, ?_, ?_⟩
    · have hnat : 1957201 ≤ n := by omega
      have hreal : (1957201 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 2053488 := by exact_mod_cast h89
      linarith
  by_cases h90 : n ≤ 2163840
  · refine ⟨dusartLemma33MidrangeRow_2053489_2163840, by simp, ?_, ?_⟩
    · have hnat : 2053489 ≤ n := by omega
      have hreal : (2053489 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 2163840 := by exact_mod_cast h90
      linarith
  by_cases h91 : n ≤ 2247000
  · refine ⟨dusartLemma33MidrangeRow_2163841_2247000, by simp, ?_, ?_⟩
    · have hnat : 2163841 ≤ n := by omega
      have hreal : (2163841 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 2247000 := by exact_mod_cast h91
      linarith
  by_cases h92 : n ≤ 2411808
  · refine ⟨dusartLemma33MidrangeRow_2247001_2411808, by simp, ?_, ?_⟩
    · have hnat : 2247001 ≤ n := by omega
      have hreal : (2247001 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 2411808 := by exact_mod_cast h92
      linarith
  by_cases h93 : n ≤ 2550408
  · refine ⟨dusartLemma33MidrangeRow_2411809_2550408, by simp, ?_, ?_⟩
    · have hnat : 2411809 ≤ n := by omega
      have hreal : (2411809 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 2550408 := by exact_mod_cast h93
      linarith
  by_cases h94 : n ≤ 2627640
  · refine ⟨dusartLemma33MidrangeRow_2550409_2627640, by simp, ?_, ?_⟩
    · have hnat : 2550409 ≤ n := by omega
      have hreal : (2550409 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 2627640 := by exact_mod_cast h94
      linarith
  by_cases h95 : n ≤ 2785560
  · refine ⟨dusartLemma33MidrangeRow_2627641_2785560, by simp, ?_, ?_⟩
    · have hnat : 2627641 ≤ n := by omega
      have hreal : (2627641 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 2785560 := by exact_mod_cast h95
      linarith
  by_cases h96 : n ≤ 2968728
  · refine ⟨dusartLemma33MidrangeRow_2785561_2968728, by simp, ?_, ?_⟩
    · have hnat : 2785561 ≤ n := by omega
      have hreal : (2785561 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 2968728 := by exact_mod_cast h96
      linarith
  by_cases h97 : n ≤ 3179088
  · refine ⟨dusartLemma33MidrangeRow_2968729_3179088, by simp, ?_, ?_⟩
    · have hnat : 2968729 ≤ n := by omega
      have hreal : (2968729 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 3179088 := by exact_mod_cast h97
      linarith
  by_cases h98 : n ≤ 3411408
  · refine ⟨dusartLemma33MidrangeRow_3179089_3411408, by simp, ?_, ?_⟩
    · have hnat : 3179089 ≤ n := by omega
      have hreal : (3179089 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 3411408 := by exact_mod_cast h98
      linarith
  by_cases h99 : n ≤ 3530640
  · refine ⟨dusartLemma33MidrangeRow_3411409_3530640, by simp, ?_, ?_⟩
    · have hnat : 3411409 ≤ n := by omega
      have hreal : (3411409 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 3530640 := by exact_mod_cast h99
      linarith
  by_cases h100 : n ≤ 3798600
  · refine ⟨dusartLemma33MidrangeRow_3530641_3798600, by simp, ?_, ?_⟩
    · have hnat : 3530641 ≤ n := by omega
      have hreal : (3530641 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 3798600 := by exact_mod_cast h100
      linarith
  by_cases h101 : n ≤ 3996000
  · refine ⟨dusartLemma33MidrangeRow_3798601_3996000, by simp, ?_, ?_⟩
    · have hnat : 3798601 ≤ n := by omega
      have hreal : (3798601 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 3996000 := by exact_mod_cast h101
      linarith
  by_cases h102 : n ≤ 4255968
  · refine ⟨dusartLemma33MidrangeRow_3996001_4255968, by simp, ?_, ?_⟩
    · have hnat : 3996001 ≤ n := by omega
      have hreal : (3996001 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 4255968 := by exact_mod_cast h102
      linarith
  by_cases h103 : n ≤ 4464768
  · refine ⟨dusartLemma33MidrangeRow_4255969_4464768, by simp, ?_, ?_⟩
    · have hnat : 4255969 ≤ n := by omega
      have hreal : (4255969 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 4464768 := by exact_mod_cast h103
      linarith
  by_cases h104 : n ≤ 4748040
  · refine ⟨dusartLemma33MidrangeRow_4464769_4748040, by simp, ?_, ?_⟩
    · have hnat : 4464769 ≤ n := by omega
      have hreal : (4464769 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 4748040 := by exact_mod_cast h104
      linarith
  by_cases h105 : n ≤ 5031048
  · refine ⟨dusartLemma33MidrangeRow_4748041_5031048, by simp, ?_, ?_⟩
    · have hnat : 4748041 ≤ n := by omega
      have hreal : (4748041 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 5031048 := by exact_mod_cast h105
      linarith
  by_cases h106 : n ≤ 5257848
  · refine ⟨dusartLemma33MidrangeRow_5031049_5257848, by simp, ?_, ?_⟩
    · have hnat : 5031049 ≤ n := by omega
      have hreal : (5031049 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 5257848 := by exact_mod_cast h106
      linarith
  by_cases h107 : n ≤ 5527200
  · refine ⟨dusartLemma33MidrangeRow_5257849_5527200, by simp, ?_, ?_⟩
    · have hnat : 5257849 ≤ n := by omega
      have hreal : (5257849 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 5527200 := by exact_mod_cast h107
      linarith
  by_cases h108 : n ≤ 5755200
  · refine ⟨dusartLemma33MidrangeRow_5527201_5755200, by simp, ?_, ?_⟩
    · have hnat : 5527201 ≤ n := by omega
      have hreal : (5527201 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 5755200 := by exact_mod_cast h108
      linarith
  by_cases h109 : n ≤ 6086088
  · refine ⟨dusartLemma33MidrangeRow_5755201_6086088, by simp, ?_, ?_⟩
    · have hnat : 5755201 ≤ n := by omega
      have hreal : (5755201 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 6086088 := by exact_mod_cast h109
      linarith
  by_cases h110 : n ≤ 6497400
  · refine ⟨dusartLemma33MidrangeRow_6086089_6497400, by simp, ?_, ?_⟩
    · have hnat : 6086089 ≤ n := by omega
      have hreal : (6086089 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 6497400 := by exact_mod_cast h110
      linarith
  by_cases h111 : n ≤ 6932688
  · refine ⟨dusartLemma33MidrangeRow_6497401_6932688, by simp, ?_, ?_⟩
    · have hnat : 6497401 ≤ n := by omega
      have hreal : (6497401 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 6932688 := by exact_mod_cast h111
      linarith
  by_cases h112 : n ≤ 7219968
  · refine ⟨dusartLemma33MidrangeRow_6932689_7219968, by simp, ?_, ?_⟩
    · have hnat : 6932689 ≤ n := by omega
      have hreal : (6932689 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 7219968 := by exact_mod_cast h112
      linarith
  by_cases h113 : n ≤ 7458360
  · refine ⟨dusartLemma33MidrangeRow_7219969_7458360, by simp, ?_, ?_⟩
    · have hnat : 7219969 ≤ n := by omega
      have hreal : (7219969 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 7458360 := by exact_mod_cast h113
      linarith
  by_cases h114 : n ≤ 7845600
  · refine ⟨dusartLemma33MidrangeRow_7458361_7845600, by simp, ?_, ?_⟩
    · have hnat : 7458361 ≤ n := by omega
      have hreal : (7458361 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 7845600 := by exact_mod_cast h114
      linarith
  by_cases h115 : n ≤ 8185320
  · refine ⟨dusartLemma33MidrangeRow_7845601_8185320, by simp, ?_, ?_⟩
    · have hnat : 7845601 ≤ n := by omega
      have hreal : (7845601 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 8185320 := by exact_mod_cast h115
      linarith
  by_cases h116 : n ≤ 8720208
  · refine ⟨dusartLemma33MidrangeRow_8185321_8720208, by simp, ?_, ?_⟩
    · have hnat : 8185321 ≤ n := by omega
      have hreal : (8185321 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 8720208 := by exact_mod_cast h116
      linarith
  by_cases h117 : n ≤ 9223368
  · refine ⟨dusartLemma33MidrangeRow_8720209_9223368, by simp, ?_, ?_⟩
    · have hnat : 8720209 ≤ n := by omega
      have hreal : (8720209 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 9223368 := by exact_mod_cast h117
      linarith
  by_cases h118 : n ≤ 9740640
  · refine ⟨dusartLemma33MidrangeRow_9223369_9740640, by simp, ?_, ?_⟩
    · have hnat : 9223369 ≤ n := by omega
      have hreal : (9223369 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 9740640 := by exact_mod_cast h118
      linarith
  by_cases h119 : n ≤ 10000000
  · refine ⟨dusartLemma33MidrangeRow_9740641_10000000, by simp, ?_, ?_⟩
    · have hnat : 9740641 ≤ n := by omega
      have hreal : (9740641 : Real) ≤ n := by exact_mod_cast hnat
      exact hreal.trans hnreal
    · have hreal : (n : Real) ≤ 10000000 := by exact_mod_cast h119
      linarith
  · exfalso
    omega

end

end PrimeFactorUnimodality
