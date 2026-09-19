import Tablet.IsOneEdgeUncolored
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.TashTreeBadPair
import Tablet.TashTreeMinimumBadPair
import Tablet.TashkinovTree
import Tablet.TreeColorUnusedThrough
import Tablet.TreeSequence
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TwoColorComponentSwapProper

-- [TABLET NODE: TashTreeDisjointComponentNormalization]
theorem TashTreeDisjointComponentNormalization {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (p a b : Fin (T.length + 1)) (hp : p.val < T.length)
    (hap : a.val ≤ p.val) (hbp : b.val ≤ p.val)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (ha : alpha ∈ MissingColors G phi (T.vertex a))
    (hb : beta ∈ MissingColors G phi (T.vertex b))
    (hlast : beta ∈ MissingColors G phi (T.vertex (Fin.last T.length)))
    (hau : TreeColorUnusedThrough phi T alpha p)
    (hbu : TreeColorUnusedThrough phi T beta p)
    (hvertices : ∀ q : Fin (T.length + 1), q.val ≤ p.val →
      Sum.inl (T.vertex q) ∉
        TwoColorComponent G phi alpha beta
          (Sum.inl (T.vertex (Fin.last T.length))))
    (hedges : ∀ r : Fin T.length, r.val < p.val →
      Sum.inr (T.edge r) ∉
        TwoColorComponent G phi alpha beta
          (Sum.inl (T.vertex (Fin.last T.length)))) :
    let phi' := TwoColorComponentSwap G phi alpha beta
      (Sum.inl (T.vertex (Fin.last T.length)))
    TashTreeMinimumBadPair G k e0 phi' T ∧
      (∀ r : Fin T.length, r.val < p.val →
        phi' (T.edge r) = phi (T.edge r)) ∧
      alpha ∈ MissingColors G phi' (T.vertex a) ∧
      alpha ∈ MissingColors G phi' (T.vertex (Fin.last T.length)) := by
-- BODY
  sorry
