import Tablet.BoundaryEdges
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideEnlargedVertexSet
import Tablet.ScheideReplacementData
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideLastExitPath]
structure ScheideLastExitPath {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d)
    (alpha : Fin k) where
-- BODY
  terminal : V
  lastInside : V
  firstOutside : V
  crossing : E
  path : (TwoColorIncidenceGraph G phi D.alpha0 alpha).Walk
    (Sum.inl (C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩))
    (Sum.inl terminal)
  lastIndex : Fin (path.length + 1)
  pathSimple : path.IsPath
  pathSpans : {z | z ∈ path.support} =
    TwoColorComponent G phi D.alpha0 alpha
      (Sum.inl (C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩))
  terminalOutside : terminal ∉ ScheideEnlargedVertexSet R
  lastInsideAt : path.getVert lastIndex.val = Sum.inl lastInside
  lastInsideMem : lastInside ∈ ScheideEnlargedVertexSet R
  followingVertex : lastIndex.val + 2 ≤ path.length
  crossingAt : path.getVert (lastIndex.val + 1) = Sum.inr crossing
  firstOutsideAt : path.getVert (lastIndex.val + 2) = Sum.inl firstOutside
  firstOutsideNotMem : firstOutside ∉ ScheideEnlargedVertexSet R
  afterLastOutside : ∀ (j : Fin (path.length + 1)),
    lastIndex.val < j.val → ∀ x : V, path.getVert j.val = Sum.inl x →
      x ∉ ScheideEnlargedVertexSet R
  crossingBoundary : crossing ∈ BoundaryEdges G (ScheideEnlargedVertexSet R)
  crossingColor : phi crossing = some alpha
  crossingComponent : Sum.inr crossing ∈
    TwoColorComponent G phi D.alpha0 alpha
      (Sum.inl (C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩))
