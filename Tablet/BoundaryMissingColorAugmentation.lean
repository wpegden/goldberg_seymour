import Tablet.BoundaryColorEdges
import Tablet.TashkinovAugmentation
import Tablet.TreeMissingColors
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceBoundaryEdgeAppendExists
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceInitialSegmentVertexSetStrict
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: BoundaryMissingColorAugmentation]
theorem BoundaryMissingColorAugmentation {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (X : TreeSequence G e0)
    (c : Fin k) (f : E)
    (hf : f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet X) c)
    (hc : c ∈ TreeMissingColors phi X) :
    ∃ Xplus : TreeSequence G e0,
      TreeSequenceAdjoinEdge X f Xplus ∧
      TashkinovAugmentation phi X Xplus ∧
      TreeSequenceVertexSet X ⊂ TreeSequenceVertexSet Xplus := by
-- BODY
  change f ∈ (BoundaryEdges G (TreeSequenceVertexSet X)).filter
    (fun g => phi g = some c) at hf
  rw [Finset.mem_filter] at hf
  obtain ⟨Xplus, hAdjoin⟩ :=
    TreeSequenceBoundaryEdgeAppendExists X f hf.1
  obtain ⟨hLength, hInitial, hLastEdge⟩ := hAdjoin
  refine ⟨Xplus, ⟨hLength, hInitial, hLastEdge⟩, ?_, ?_⟩
  · refine ⟨hLength, hInitial, c, ?_, hc⟩
    rw [hLastEdge]
    exact hf.2
  · apply TreeSequenceInitialSegmentVertexSetStrict hInitial
    omega
