import Tablet.MissingColors
import Tablet.TashTreeMinimumBadPair
import Tablet.TashTreePathIndex
import Tablet.TashTreeRhoOneAdvance
import Tablet.TreeSequence

-- [TABLET NODE: TashTreeRhoOneIterate]
theorem TashTreeRhoOneIterate {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : TashTreePathIndex G T = 1) (beta : Fin k)
    (i : Fin T.length)
    (hi : beta ∈ MissingColors G phi (T.vertex i.castSucc))
    (hlast : beta ∈ MissingColors G phi
      (T.vertex (Fin.last T.length))) :
    ∃ (psi : PartialEdgeColoring E k) (p : Fin T.length),
      p.val + 1 = T.length ∧
      TashTreeMinimumBadPair G k e0 psi T ∧
      beta ∈ MissingColors G psi (T.vertex p.castSucc) ∧
      beta ∈ MissingColors G psi
        (T.vertex (Fin.last T.length)) := by
-- BODY
  sorry
