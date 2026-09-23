import Tablet.ColoredVertexSetElementary
import Tablet.KTriple
import Tablet.TashTreeMinimumBadPair
import Tablet.TashTreeBadPair
import Tablet.TashTreePathIndex
import Tablet.TashTreeRankLess
import Tablet.TashTreeSuffixPath
import Tablet.TashkinovTree
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequencePreservesTashkinovTree
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentTashkinovSplice

-- [TABLET NODE: TashTreeNoRepeatedIntersectionShortening]
theorem TashTreeNoRepeatedIntersectionShortening {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hbefore : TashTreePathIndex G T < T.length)
    (beta epsilon : Fin k) (hne : epsilon ≠ beta)
    (i m : Fin (T.length + 1))
    (hi : i.val + 2 ≤ TashTreePathIndex G T)
    (hm : m.val + 2 ≤ TashTreePathIndex G T)
    (hbeta : beta ∈ MissingColors G phi (T.vertex i))
    (hlast : beta ∈
      MissingColors G phi (T.vertex (Fin.last T.length)))
    (hepsilon : epsilon ∈ MissingColors G phi (T.vertex m))
    (hmeets : ∃ s : Fin (T.length + 1),
      s.val + 1 ≤ TashTreePathIndex G T ∧
      Sum.inl (T.vertex s) ∈
        TwoColorComponent G phi epsilon beta
          (Sum.inl (T.vertex (Fin.last T.length)))) : False := by
-- BODY
  sorry
