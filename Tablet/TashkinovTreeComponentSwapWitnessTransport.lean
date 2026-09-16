import Tablet.IsProperEdgeColoring
import Tablet.MissingColorIncidenceEndpoint
import Tablet.MissingColors
import Tablet.TashkinovTree
import Tablet.TreeColorUnusedThrough
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: TashkinovTreeComponentSwapWitnessTransport]
theorem TashkinovTreeComponentSwapWitnessTransport {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hproper : IsProperEdgeColoring G phi)
    (hTash : TashkinovTree G e0 phi T)
    (i j : Fin (T.length + 1)) (hij : i.val < j.val)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (ha : alpha ∈ MissingColors G phi (T.vertex i))
    (hb : beta ∈ MissingColors G phi (T.vertex j))
    (hau : TreeColorUnusedThrough phi T alpha j)
    (hbu : TreeColorUnusedThrough phi T beta j) :
    let C := TwoColorComponent G phi alpha beta (Sum.inl (T.vertex j))
    let phi' := TwoColorComponentSwap G phi alpha beta (Sum.inl (T.vertex j))
    (∀ r : Fin T.length, 1 ≤ r.val → r.val < j.val →
      phi' (T.edge r) = phi (T.edge r)) ∧
      (∀ S : TreeSequence G e0, TreeSequenceInitialSegment S T →
        S.length = j.val → TashkinovTree G e0 phi' S) ∧
      (Sum.inl (T.vertex i) ∈ C →
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
          TashkinovTree G e0 phi' T) := by
-- BODY
  sorry
