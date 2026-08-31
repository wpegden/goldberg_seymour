import Tablet.HierarchyCounterexample
import Tablet.HierarchyPathNumber

-- [TABLET NODE: HierarchyCounterexampleMeasure]
noncomputable def HierarchyCounterexampleMeasure {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T generating}
    {base : HierarchyBase ett generating} (C : HierarchyCounterexample base) :
    ℕ × ℕ :=
-- BODY
  (HierarchyPathNumber C.hierarchy,
    T.length - (C.hierarchy.stage
      ⟨C.hierarchy.dividerCount, by omega⟩).length)
