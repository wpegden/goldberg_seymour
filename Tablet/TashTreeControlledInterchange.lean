import Tablet.ColoredVertexSetElementary
import Tablet.IsOneEdgeUncolored
import Tablet.KTriple
import Tablet.MissingColorIncidenceEndpoint
import Tablet.TashTreeBadPair
import Tablet.TashTreeMinimumBadPair
import Tablet.TashTreePathIndex
import Tablet.TashTreeProperPrefixElementary
import Tablet.TashTreeRankLess
import Tablet.TashTreeSuffixPath
import Tablet.TashkinovTree
import Tablet.TreeColorUnusedThrough
import Tablet.TreeSequence
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent

-- [TABLET NODE: TashTreeControlledInterchange]
theorem TashTreeControlledInterchange {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (i j : Fin (T.length + 1)) (hij : i.val < j.val)
    (hj : j.val < T.length) (alpha beta : Fin k) (hne : alpha ≠ beta)
    (ha : alpha ∈ MissingColors G phi (T.vertex i))
    (hb : beta ∈ MissingColors G phi (T.vertex j))
    (hau : TreeColorUnusedThrough phi T alpha j)
    (hbu : TreeColorUnusedThrough phi T beta j) :
    let phi' := TwoColorComponentSwap G phi alpha beta (Sum.inl (T.vertex j))
    TwoColorPathComponent G phi alpha beta (Sum.inl (T.vertex j)) ∧
      Sum.inl (T.vertex i) ∈
        TwoColorComponent G phi alpha beta (Sum.inl (T.vertex j)) ∧
      Set.Subsingleton
        ((TwoColorIncidenceGraph G phi alpha beta).neighborSet
          (Sum.inl (T.vertex i))) ∧
      Set.Subsingleton
        ((TwoColorIncidenceGraph G phi alpha beta).neighborSet
          (Sum.inl (T.vertex j))) ∧
      beta ∈ MissingColors G phi' (T.vertex i) ∧
      alpha ∈ MissingColors G phi' (T.vertex j) ∧
      (∀ r : Fin T.length, 1 ≤ r.val → r.val < j.val →
        phi' (T.edge r) = phi (T.edge r)) ∧
      (∀ r : Fin T.length, j.val ≤ r.val →
        ∀ w : Fin (r.val + 1), ∀ c : Fin k,
          phi (T.edge r) = some c →
          c ∈ MissingColors G phi
            (T.vertex (Fin.castLT w
              (Nat.lt_trans w.isLt (Nat.succ_lt_succ r.isLt)))) →
          ∃ w' : Fin (r.val + 1), ∃ c' : Fin k,
            phi' (T.edge r) = some c' ∧
            c' ∈ MissingColors G phi'
              (T.vertex (Fin.castLT w'
                (Nat.lt_trans w'.isLt (Nat.succ_lt_succ r.isLt))))) ∧
      TashTreeMinimumBadPair G k e0 phi' T := by
-- BODY
  sorry
