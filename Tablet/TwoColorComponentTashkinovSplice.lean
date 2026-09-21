import Tablet.IsProperEdgeColoring
import Tablet.TashkinovAlternatingSegmentAppend
import Tablet.TwoColorComponentNearestSegment

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
        Sum.inl u ∈
          TwoColorComponent G phi alpha beta (Sum.inl y) /\
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
  obtain ⟨m, hm, pathVertex, pathEdge, hvertexInjective,
      hedgeInjective, hstart, hlast, houtside, hvertexComponent,
      hedgeComponent, hcolors, hends, hedgeFresh⟩ :=
    TwoColorComponentNearestSegment G phi S alpha beta y hproper hne hy hmeets
  obtain ⟨S', hSS', _hlengthEq, hlength, haugment, hlastVertex, hnew⟩ :=
    TashkinovAlternatingSegmentAppend G phi S alpha beta y m hm
      pathVertex pathEdge hvertexInjective hedgeInjective hstart houtside
      hvertexComponent hedgeComponent hcolors hends hedgeFresh halpha hbeta
  refine ⟨pathVertex 0, S', hstart, hvertexComponent 0, hSS', hlength,
    haugment, ?_, hnew⟩
  rw [hlastVertex, hlast]
