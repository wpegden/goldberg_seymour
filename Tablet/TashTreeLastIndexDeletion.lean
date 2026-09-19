import Tablet.ColoredVertexSetElementary
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.TashTreeBadPair
import Tablet.TashTreeMinimumBadPair
import Tablet.TashTreePathIndex
import Tablet.TashTreeRankLess
import Tablet.TashTreeSuffixPath
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: TashTreeLastIndexDeletion]
theorem TashTreeLastIndexDeletion {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hlast : TashTreePathIndex G T = T.length)
    (gamma beta : Fin k) (r : Fin T.length) (p j : Fin (T.length + 1))
    (hr : r.val + 1 = T.length) (hp : p.val + 1 = T.length)
    (hj : j.val + 2 ≤ T.length)
    (hrgamma : phi (T.edge r) = some gamma)
    (hpgamma : gamma ∈ PresentColors G phi (T.vertex p))
    (hbj : beta ∈ MissingColors G phi (T.vertex j))
    (hblast : beta ∈ MissingColors G phi (T.vertex (Fin.last T.length))) :
    ∃ (P S : TreeSequence G e0) (s : Fin S.length),
      P.length + 2 = T.length ∧
        TreeSequenceInitialSegment P T ∧
        S.length = P.length + 1 ∧
        TreeSequenceInitialSegment P S ∧
        s.val + 1 = S.length ∧
        S.edge s = T.edge r ∧
        S.vertex (Fin.last S.length) = T.vertex (Fin.last T.length) ∧
        TashTreeBadPair G k e0 phi S ∧
        TashTreeRankLess G S T := by
-- BODY
  sorry
