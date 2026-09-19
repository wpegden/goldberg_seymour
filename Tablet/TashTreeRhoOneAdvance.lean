import Tablet.TashTreeSuffixAdvance

-- [TABLET NODE: TashTreeRhoOneAdvance]
theorem TashTreeRhoOneAdvance {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : TashTreePathIndex G T = 1) (beta : Fin k)
    (i : Fin T.length) (hiNext : i.val + 1 < T.length)
    (hi : beta ∈ MissingColors G phi (T.vertex i.castSucc))
    (hlast : beta ∈ MissingColors G phi
      (T.vertex (Fin.last T.length))) :
    ∃ phi' : PartialEdgeColoring E k,
      TashTreeMinimumBadPair G k e0 phi' T ∧
      beta ∈ MissingColors G phi' (T.vertex i.succ) ∧
      beta ∈ MissingColors G phi'
        (T.vertex (Fin.last T.length)) := by
-- BODY
  apply TashTreeSuffixAdvance G k e0 phi T hmin beta i
  · by_cases hiZero : i.val = 0
    · exact Or.inl hiZero
    · exact Or.inr (by omega)
  · exact hiNext
  · exact hi
  · exact hlast
