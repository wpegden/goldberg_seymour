import Tablet.ColoredVertexSetElementary
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MissingColorIncidenceEndpoint
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.TashTreeBadPair
import Tablet.TashTreeControlledInterchange
import Tablet.TashTreeFourUnusedColors
import Tablet.TashTreeMinimumBadPair
import Tablet.TashTreeMinimumBadPathIndex
import Tablet.TashTreePathIndex
import Tablet.TashTreeLastIndexDeletion
import Tablet.TashTreeLastIndexFirstNormalForm
import Tablet.TashTreeLastIndexSecondNormalForm
import Tablet.TashTreeLastIndexThirdNormalForm
import Tablet.TashTreeProperPrefixElementary
import Tablet.TashTreeRankLess
import Tablet.TashTreeSuffixPath
import Tablet.TashkinovTree
import Tablet.TreeFreeColors
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TreeUsedColors
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorComponentSwapProper

-- [TABLET NODE: TashTreeCasePathIndexLast]
theorem TashTreeCasePathIndexLast {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hlast : TashTreePathIndex G T = T.length) : False := by
-- BODY
  obtain ⟨phi₁, beta₁, j₁, hmin₁, hj₁, hbeta₁j, hbeta₁last,
    hbeta₁unused⟩ :=
    TashTreeLastIndexFirstNormalForm G k e0 phi T hmin hq hlast
  obtain ⟨phi₂, gamma, r, p, hr, hp, hmin₂, hrgamma, hpgamma⟩ :=
    TashTreeLastIndexSecondNormalForm G k e0 phi₁ T hmin₁ hq hlast
      beta₁ j₁ hj₁ hbeta₁j hbeta₁last hbeta₁unused
  obtain ⟨phi₃, beta₃, j₃, hmin₃, hrgamma₃, hpgamma₃, hj₃,
    hbeta₃j, hbeta₃last⟩ :=
    TashTreeLastIndexThirdNormalForm G k e0 phi₂ T hmin₂ hq hlast
      gamma r p hr hp hrgamma hpgamma
  obtain ⟨P, S, s, hPlength, hPT, hSlength, hPS, hs, hsedge,
    hsvertex, hbadS, hrankS⟩ :=
    TashTreeLastIndexDeletion G k e0 phi₃ T hmin₃ hq hlast
      gamma beta₃ r p j₃ hr hp hj₃ hrgamma₃ hpgamma₃
      hbeta₃j hbeta₃last
  exact (hmin₃.2 hbadS) hrankS
