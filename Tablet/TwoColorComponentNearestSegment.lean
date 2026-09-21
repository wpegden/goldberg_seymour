import Tablet.Incident
import Tablet.IsProperEdgeColoring
import Tablet.LooplessMultigraph
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorIncidenceGraph

open scoped Sym2

-- [TABLET NODE: TwoColorComponentNearestSegment]
theorem TwoColorComponentNearestSegment
    {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) {k : Nat} {e0 : E}
    (phi : PartialEdgeColoring E k) (S : TreeSequence G e0)
    (alpha beta : Fin k) (y : V)
    (hproper : IsProperEdgeColoring G phi)
    (hne : alpha ≠ beta)
    (hy : y ∉ TreeSequenceVertexSet S)
    (hmeets : ∃ u ∈ TreeSequenceVertexSet S,
      Sum.inl u ∈ TwoColorComponent G phi alpha beta (Sum.inl y)) :
    ∃ (m : Nat) (_ : 1 ≤ m)
      (pathVertex : Fin (m + 1) → V) (pathEdge : Fin m → E),
      Function.Injective pathVertex ∧
        Function.Injective pathEdge ∧
        pathVertex 0 ∈ TreeSequenceVertexSet S ∧
        pathVertex (Fin.last m) = y ∧
        (∀ i : Fin m,
          pathVertex i.succ ∉ TreeSequenceVertexSet S) ∧
        (∀ i : Fin (m + 1),
          Sum.inl (pathVertex i) ∈
            TwoColorComponent G phi alpha beta (Sum.inl y)) ∧
        (∀ i : Fin m,
          Sum.inr (pathEdge i) ∈
            TwoColorComponent G phi alpha beta (Sum.inl y)) ∧
        (∀ i : Fin m,
          phi (pathEdge i) = some alpha ∨
            phi (pathEdge i) = some beta) ∧
        (∀ i : Fin m,
          G.ends (pathEdge i) =
            s(pathVertex i.castSucc, pathVertex i.succ)) ∧
        ∀ i : Fin m, ∀ j : Fin S.length,
          pathEdge i ≠ S.edge j := by
-- BODY
  sorry
