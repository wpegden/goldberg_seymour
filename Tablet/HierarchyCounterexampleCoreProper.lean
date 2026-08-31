import Tablet.HierarchyCounterexample

-- [TABLET NODE: HierarchyCounterexampleCoreProper]
theorem HierarchyCounterexampleCoreProper {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T generating}
    {base : HierarchyBase ett generating}
    (C : HierarchyCounterexample base)
    (hcore : ColoredVertexSetElementary G generating
      (TreeSequenceVertexSet base.core)) :
    T ≠ base.core := by
-- BODY
  intro h
  have hnot := C.notElementary
  rw [h] at hnot
  exact hnot hcore
