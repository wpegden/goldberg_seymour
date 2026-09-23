import Tablet.MissingColorIncidenceEndpoint
import Tablet.KTriple
import Tablet.TashTreeBadPair
import Tablet.TashTreeCaseRepeatedOnPath
import Tablet.TashTreeControlledInterchange
import Tablet.TashTreeMinimumBadPair
import Tablet.TreeColorUnusedThrough
import Tablet.TreeSequence
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwapMissingBehavior

-- [TABLET NODE: TashTreeControlledRepeatedSuffixContradiction]
theorem TashTreeControlledRepeatedSuffixContradiction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hbefore : TashTreePathIndex G T < T.length)
    (i j : Fin (T.length + 1)) (hij : i.val < j.val)
    (hj : j.val < T.length) (hpath : TashTreePathIndex G T ≤ j.val)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (ha : alpha ∈ MissingColors G phi (T.vertex i))
    (hb : beta ∈ MissingColors G phi (T.vertex j))
    (hau : TreeColorUnusedThrough phi T alpha j)
    (hbu : TreeColorUnusedThrough phi T beta j)
    (hlast : alpha ∈
      MissingColors G phi (T.vertex (Fin.last T.length))) : False := by
-- BODY
  sorry
