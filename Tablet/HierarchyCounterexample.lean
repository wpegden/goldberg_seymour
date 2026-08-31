import Tablet.ColoredVertexSetElementary
import Tablet.GoodHierarchy
import Tablet.MaximumProperty

-- [TABLET NODE: HierarchyCounterexample]
structure HierarchyCounterexample {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T generating}
    (base : HierarchyBase ett generating) where
-- BODY
  positive : 0 < ett.rounds
  hierarchy : TashkinovHierarchy ett base
  good : GoodHierarchy hierarchy
  maximum : MaximumProperty ett
  notElementary :
    ¬ ColoredVertexSetElementary G generating (TreeSequenceVertexSet T)
