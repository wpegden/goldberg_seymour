import Tablet.BoundaryEdges
import Tablet.TashkinovSeriesData
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorCycle

open scoped Sym2

-- [TABLET NODE: RevisitingExtensionCertificate]
structure RevisitingExtensionCertificate {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    (data : TashkinovSeriesData G k rounds e0)
    (i : Fin (rounds + 1)) where
-- BODY
  earlier : Fin (rounds + 1)
  earlierPositive : 0 < earlier.val
  earlierAtMost : earlier.val ≤ i.val
  earlierPE : data.kind earlier = some TashkinovExtensionKind.PE
  interveningRevisiting : ∀ j : Fin (rounds + 1),
    0 < j.val → earlier.val < j.val → j.val ≤ i.val →
      data.kind j = some TashkinovExtensionKind.RE
  gamma : Fin k
  delta : Fin k
  earlierGamma : data.gamma earlier = some gamma
  earlierDelta : data.delta earlier = some delta
  cycle : TwoColorCycle G (data.coloring i) gamma delta
  meetsEarlier : ∃ v ∈ TreeSequenceVertexSet (data.tree earlier.castSucc),
    Sum.inl v ∈ cycle.walk.support
  leavesCurrent : ∃ u ∉ TreeSequenceVertexSet (data.tree i.succ),
    Sum.inl u ∈ cycle.walk.support
  edge : E
  edgeOnCycle : Sum.inr edge ∈ cycle.walk.support
  edgeBoundary : edge ∈ BoundaryEdges G (TreeSequenceVertexSet (data.tree i.succ))
  insideEndpoint : V
  outsideEndpoint : V
  insideInCurrent : insideEndpoint ∈ TreeSequenceVertexSet (data.tree i.succ)
  outsideNotCurrent : outsideEndpoint ∉ TreeSequenceVertexSet (data.tree i.succ)
  edgeEnds : G.ends edge = s(insideEndpoint, outsideEndpoint)
  returnVertex : V
  returnInEarlier : returnVertex ∈ TreeSequenceVertexSet (data.tree earlier.castSucc)
  returnPath : (TwoColorIncidenceGraph G (data.coloring i) gamma delta).Walk
    (Sum.inr edge) (Sum.inl returnVertex)
  returnPathIsPath : returnPath.IsPath
  returnPathOnCycle : ∀ z ∈ returnPath.support, z ∈ cycle.walk.support
  returnPathInternal : ∀ v, Sum.inl v ∈ returnPath.support →
    v ∈ TreeSequenceVertexSet (data.tree i.succ)
