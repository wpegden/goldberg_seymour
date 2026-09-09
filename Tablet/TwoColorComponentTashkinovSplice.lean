import Tablet.Incident
import Tablet.IsProperEdgeColoring
import Tablet.LooplessMultigraph
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorIncidenceGraph

open scoped Sym2

-- [TABLET NODE: TwoColorComponentTashkinovSplice]
theorem TwoColorComponentTashkinovSplice
    {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) {k : Nat} {e0 : E}
    (phi : PartialEdgeColoring E k) (S : TreeSequence G e0)
    (alpha beta : Fin k) (y : V)
    (hproper : IsProperEdgeColoring G phi)
    (hne : alpha ≠ beta)
    (halpha : alpha ∈ TreeMissingColors phi S)
    (hbeta : beta ∈ TreeMissingColors phi S)
    (hy : y ∉ TreeSequenceVertexSet S)
    (hmeets : ∃ u ∈ TreeSequenceVertexSet S,
      Sum.inl u ∈ TwoColorComponent G phi alpha beta (Sum.inl y)) :
    ∃ (u : V) (S' : TreeSequence G e0),
      u ∈ TreeSequenceVertexSet S /\
        TreeSequenceInitialSegment S S' /\
        S.length < S'.length /\
        TashkinovAugmentationSequence phi S S' /\
        S'.vertex (Fin.last S'.length) = y /\
        ∀ r : Fin S'.length, S.length ≤ r.val →
          S'.vertex r.succ ∉ TreeSequenceVertexSet S /\
            Sum.inr (S'.edge r) ∈
              TwoColorComponent G phi alpha beta (Sum.inl y) /\
            Sum.inl (S'.vertex r.succ) ∈
              TwoColorComponent G phi alpha beta (Sum.inl y) /\
            (phi (S'.edge r) = some alpha ∨
              phi (S'.edge r) = some beta) /\
            G.ends (S'.edge r) =
              if r.val = S.length then
                s(u, S'.vertex r.succ)
              else
                s(S'.vertex r.castSucc, S'.vertex r.succ) := by
-- BODY
  sorry
