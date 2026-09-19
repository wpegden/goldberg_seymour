import Tablet.ColoredVertexSetElementary
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.TashTreeBadPair
import Tablet.TashTreeMinimumBadPair
import Tablet.TashTreePathIndex
import Tablet.TashTreeRankLess
import Tablet.TashTreeSuffixPath
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequencePreservesTashkinovTree
import Tablet.TashkinovTree
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentTashkinovSplice

-- [TABLET NODE: TashTreeLastIndexIntersectionShortening]
theorem TashTreeLastIndexIntersectionShortening {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T S : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hlast : TashTreePathIndex G T = T.length)
    (hST : TreeSequenceInitialSegment S T)
    (hlen : S.length + 2 = T.length)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (halpha : alpha ∈ TreeMissingColors phi S)
    (hbeta : beta ∈ TreeMissingColors phi S)
    (hlastbeta : beta ∈
      MissingColors G phi (T.vertex (Fin.last T.length)))
    (hlastOutside : T.vertex (Fin.last T.length) ∉ TreeSequenceVertexSet S)
    (hmeets : ∃ u ∈ TreeSequenceVertexSet S,
      Sum.inl u ∈ TwoColorComponent G phi alpha beta
        (Sum.inl (T.vertex (Fin.last T.length)))) : False := by
-- BODY
  sorry
