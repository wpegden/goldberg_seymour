import Tablet.BoundaryColorEdges
import Tablet.ColoredVertexSetClosed
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TreeColorSetClosed
import Tablet.TreeMissingColors
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: TashkinovClosureOfRouteAndAllMissingClosed]
theorem TashkinovClosureOfRouteAndAllMissingClosed
    {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (phi : PartialEdgeColoring E k) (S T : TreeSequence G e0)
    (hroute : TashkinovAugmentationSequence phi S T)
    (hclosed : TreeColorSetClosed G phi T (TreeMissingColors phi T)) :
    TashkinovClosure phi S T := by
-- BODY
  refine ⟨hroute, ?_⟩
  intro f c v hf hv hfc hmissing
  have hc : c ∈ TreeMissingColors phi T := by
    unfold TreeMissingColors
    exact Finset.mem_biUnion.mpr ⟨v, hv, hmissing⟩
  have hempty := hclosed c hc
  have hboundaryColor :
      f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) c := by
    unfold BoundaryColorEdges
    exact Finset.mem_filter.mpr ⟨hf, hfc⟩
  rw [hempty] at hboundaryColor
  simpa using hboundaryColor
