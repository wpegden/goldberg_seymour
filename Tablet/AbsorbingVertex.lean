import Tablet.GlobalMaximumTriple
import Tablet.MissingColors
import Tablet.TreeFreeColors
import Tablet.TwoColorComponent

-- [TABLET NODE: AbsorbingVertex]
def AbsorbingVertex {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k) (v : V) : Prop :=
-- BODY
  v ∉ TreeSequenceVertexSet T ∧
    ∀ delta ∈ MissingColors G phi v,
      ∀ gamma ∈ TreeFreeColors phi T, gamma ≠ delta →
        ∃ u : V,
          u ∈ TreeSequenceVertexSet T ∧
            gamma ∈ MissingColors G phi u ∧
            Sum.inl u ∈ TwoColorComponent G phi gamma delta (Sum.inl v) ∧
            ∀ w ∈ TreeSequenceVertexSet T,
              gamma ∈ MissingColors G phi w → w = u
