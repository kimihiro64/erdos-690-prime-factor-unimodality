import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.MediumLogBand01
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.MediumLogBand02
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.MediumLogBand03
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.MediumLogBand04
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.MediumLogBand05
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.MediumLogBand06
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.MediumLogBand07

set_option autoImplicit false

/-! # Generated medium logarithmic rows

This facade assembles the independent medium log-cubed row bands. -/

namespace PrimeFactorUnimodality

noncomputable section

def mediumLogRowsPrefix01 : List FinitePrimeGapLogRow :=
  [mediumLogSeedRow] ++ mediumLogRows01

def mediumLogRowsPrefix02 : List FinitePrimeGapLogRow :=
  mediumLogRowsPrefix01 ++ mediumLogRows02

def mediumLogRowsPrefix03 : List FinitePrimeGapLogRow :=
  mediumLogRowsPrefix02 ++ mediumLogRows03

def mediumLogRowsPrefix04 : List FinitePrimeGapLogRow :=
  mediumLogRowsPrefix03 ++ mediumLogRows04

def mediumLogRowsPrefix05 : List FinitePrimeGapLogRow :=
  mediumLogRowsPrefix04 ++ mediumLogRows05

def mediumLogRowsPrefix06 : List FinitePrimeGapLogRow :=
  mediumLogRowsPrefix05 ++ mediumLogRows06

def mediumLogRowsPrefix07 : List FinitePrimeGapLogRow :=
  mediumLogRowsPrefix06 ++ mediumLogRows07

theorem mediumLogRowsPrefix01_chain :
    FinitePrimeGapLogRowsChain 89693 100002 mediumLogRowsPrefix01 := by
  exact finitePrimeGapLogRowsChain_append mediumLogSeedChain mediumLogRows01_chain

theorem mediumLogRowsPrefix02_chain :
    FinitePrimeGapLogRowsChain 100003 110016 mediumLogRowsPrefix02 := by
  exact finitePrimeGapLogRowsChain_append mediumLogRowsPrefix01_chain mediumLogRows02_chain

theorem mediumLogRowsPrefix03_chain :
    FinitePrimeGapLogRowsChain 110017 150000 mediumLogRowsPrefix03 := by
  exact finitePrimeGapLogRowsChain_append mediumLogRowsPrefix02_chain mediumLogRows03_chain

theorem mediumLogRowsPrefix04_chain :
    FinitePrimeGapLogRowsChain 150001 160000 mediumLogRowsPrefix04 := by
  exact finitePrimeGapLogRowsChain_append mediumLogRowsPrefix03_chain mediumLogRows04_chain

theorem mediumLogRowsPrefix05_chain :
    FinitePrimeGapLogRowsChain 160001 220008 mediumLogRowsPrefix05 := by
  exact finitePrimeGapLogRowsChain_append mediumLogRowsPrefix04_chain mediumLogRows05_chain

theorem mediumLogRowsPrefix06_chain :
    FinitePrimeGapLogRowsChain 220009 300006 mediumLogRowsPrefix06 := by
  exact finitePrimeGapLogRowsChain_append mediumLogRowsPrefix05_chain mediumLogRows06_chain

theorem mediumLogRowsPrefix07_chain :
    FinitePrimeGapLogRowsChain 300007 360748 mediumLogRowsPrefix07 := by
  exact finitePrimeGapLogRowsChain_append mediumLogRowsPrefix06_chain mediumLogRows07_chain

theorem mediumLogRows_89693_360653_chain :
    FinitePrimeGapLogRowsChain 89693 360748 mediumLogRowsPrefix07 := by
  exact mediumLogRowsPrefix07_chain

theorem mediumLogRows_89693_360653_cover :
    FinitePrimeGapLogRowsCoverUpTo mediumLogRowsPrefix07 (360653 : Real) := by
  exact finitePrimeGapLogRowsCoverUpTo_of_chain
    mediumLogRows_89693_360653_chain (by norm_num)

theorem hasLogCubedShortIntervalPrimeBelow_360653 :
    HasLogCubedShortIntervalPrimeBelow (360653 : Real) := by
  exact hasLogCubedShortIntervalPrimeBelow_of_finite_gap_log_rows
    mediumLogRows_89693_360653_cover

end

end PrimeFactorUnimodality
