import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent

open scoped Sym2

-- [TABLET NODE: TashkinovAlternatingSegmentAppend]
theorem TashkinovAlternatingSegmentAppend
    {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) {k : Nat} {e0 : E}
    (phi : PartialEdgeColoring E k) (S : TreeSequence G e0)
    (alpha beta : Fin k) (y : V)
    (m : Nat) (hm : 1 ≤ m)
    (pathVertex : Fin (m + 1) → V) (pathEdge : Fin m → E)
    (hvertexInjective : Function.Injective pathVertex)
    (hedgeInjective : Function.Injective pathEdge)
    (hstart : pathVertex 0 ∈ TreeSequenceVertexSet S)
    (houtside : ∀ i : Fin m,
      pathVertex i.succ ∉ TreeSequenceVertexSet S)
    (hvertexComponent : ∀ i : Fin (m + 1),
      Sum.inl (pathVertex i) ∈
        TwoColorComponent G phi alpha beta (Sum.inl y))
    (hedgeComponent : ∀ i : Fin m,
      Sum.inr (pathEdge i) ∈
        TwoColorComponent G phi alpha beta (Sum.inl y))
    (hcolors : ∀ i : Fin m,
      phi (pathEdge i) = some alpha ∨
        phi (pathEdge i) = some beta)
    (hends : ∀ i : Fin m,
      G.ends (pathEdge i) =
        s(pathVertex i.castSucc, pathVertex i.succ))
    (hedgeFresh : ∀ i : Fin m, ∀ j : Fin S.length,
      pathEdge i ≠ S.edge j)
    (halpha : alpha ∈ TreeMissingColors phi S)
    (hbeta : beta ∈ TreeMissingColors phi S) :
    ∃ S' : TreeSequence G e0,
      TreeSequenceInitialSegment S S' ∧
        S'.length = S.length + m ∧
        (∀ i : Fin m, ∃ r : Fin S'.length,
          r.val = S.length + i.val ∧
            S'.edge r = pathEdge i ∧
            S'.vertex r.succ = pathVertex i.succ) ∧
        S.length < S'.length ∧
        TashkinovAugmentationSequence phi S S' ∧
        S'.vertex (Fin.last S'.length) = pathVertex (Fin.last m) ∧
        ∀ r : Fin S'.length, S.length ≤ r.val →
          S'.vertex r.succ ∉ TreeSequenceVertexSet S ∧
            Sum.inr (S'.edge r) ∈
              TwoColorComponent G phi alpha beta (Sum.inl y) ∧
            Sum.inl (S'.vertex r.succ) ∈
              TwoColorComponent G phi alpha beta (Sum.inl y) ∧
            (phi (S'.edge r) = some alpha ∨
              phi (S'.edge r) = some beta) ∧
            G.ends (S'.edge r) =
              if r.val = S.length then
                s(pathVertex 0, S'.vertex r.succ)
              else
                s(S'.vertex r.castSucc, S'.vertex r.succ) := by
-- BODY
  sorry
