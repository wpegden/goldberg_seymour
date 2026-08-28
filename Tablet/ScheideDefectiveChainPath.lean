import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent

-- [TABLET NODE: ScheideDefectiveChainPath]
def ScheideDefectiveChainPath {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (alpha gamma : Fin k) (u z : V)
    (p : (TwoColorIncidenceGraph G phi alpha gamma).Walk
      (Sum.inl u) (Sum.inl z)) : Prop :=
-- BODY
  u ∈ TreeSequenceVertexSet T ∧ p.IsPath ∧
    z ∉ TreeSequenceVertexSet T ∧
    {x | x ∈ p.support} =
      TwoColorComponent G phi alpha gamma (Sum.inl u)
