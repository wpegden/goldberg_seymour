import Tablet.BoundaryColorEdges
import Tablet.Incident
import Tablet.RutgersClosedPresentation
import Tablet.TreeExitPath
import Tablet.TreeMissingColors
import Tablet.TreeVertexOrder

-- [TABLET NODE: RutgersCounterexample]
structure RutgersCounterexample
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (original : ExtendedTashkinovTree G k e0 input T generating)
    (presentation : RutgersClosedPresentation G k e0 original) where
-- BODY
  alpha : Fin k
  beta : Fin k
  colorsDistinct : alpha ≠ beta
  alphaMissing : alpha ∈ TreeMissingColors presentation.sigma presentation.U
  betaPresent : beta ∉ TreeMissingColors presentation.sigma presentation.U
  a1 : V
  b1 : V
  a2 : V
  b2 : V
  a3 : V
  b3 : V
  Q1 : (TwoColorIncidenceGraph G presentation.sigma alpha beta).Walk
    (Sum.inl a1) (Sum.inl b1)
  Q2 : (TwoColorIncidenceGraph G presentation.sigma alpha beta).Walk
    (Sum.inl a2) (Sum.inl b2)
  Q3 : (TwoColorIncidenceGraph G presentation.sigma alpha beta).Walk
    (Sum.inl a3) (Sum.inl b3)
  f1 : E
  f2 : E
  f3 : E
  exit1 : TreeExitPath presentation.U presentation.sigma alpha beta a1 b1 Q1
  exit2 : TreeExitPath presentation.U presentation.sigma alpha beta a2 b2 Q2
  exit3 : TreeExitPath presentation.U presentation.sigma alpha beta a3 b3 Q3
  supportDisjoint12 : forall x, x ∈ Q1.support -> x ∉ Q2.support
  supportDisjoint13 : forall x, x ∈ Q1.support -> x ∉ Q3.support
  supportDisjoint23 : forall x, x ∈ Q2.support -> x ∉ Q3.support
  outsideDistinct12 : a1 ≠ a2
  outsideDistinct13 : a1 ≠ a3
  outsideDistinct23 : a2 ≠ a3
  insideDistinct12 : b1 ≠ b2
  insideDistinct13 : b1 ≠ b3
  insideDistinct23 : b2 ≠ b3
  insideOrder12 : TreeVertexOrder presentation.U b1 b2
  insideOrder23 : TreeVertexOrder presentation.U b2 b3
  boundary1 : f1 ∈ BoundaryColorEdges G presentation.sigma
    (TreeSequenceVertexSet presentation.U) beta
  boundary2 : f2 ∈ BoundaryColorEdges G presentation.sigma
    (TreeSequenceVertexSet presentation.U) beta
  boundary3 : f3 ∈ BoundaryColorEdges G presentation.sigma
    (TreeSequenceVertexSet presentation.U) beta
  incident1 : Incident G b1 f1
  incident2 : Incident G b2 f2
  incident3 : Incident G b3 f3
  edgeOnWalk1 : Sum.inr f1 ∈ Q1.support
  edgeOnWalk2 : Sum.inr f2 ∈ Q2.support
  edgeOnWalk3 : Sum.inr f3 ∈ Q3.support
