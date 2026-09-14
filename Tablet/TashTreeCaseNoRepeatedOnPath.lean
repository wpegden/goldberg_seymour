import Tablet.TashTreeCaseRepeatedOnPath
import Tablet.TashTreeControlledInterchange
import Tablet.TashTreeFourUnusedColors
import Tablet.TashTreeProperPrefixElementary
import Tablet.TwoColorComponentSwapProper

-- [TABLET NODE: TashTreeCaseNoRepeatedOnPath]
theorem TashTreeCaseNoRepeatedOnPath {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hbefore : TashTreePathIndex G T < T.length)
    (hnone : ¬ ∃ alpha : Fin k, ∃ i : Fin (T.length + 1),
      TashTreePathIndex G T ≤ i.val ∧ i.val < T.length ∧
      alpha ∈ MissingColors G phi (T.vertex i) ∧
      alpha ∈ MissingColors G phi (T.vertex (Fin.last T.length))) : False := by
-- BODY
  sorry
