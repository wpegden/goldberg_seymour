import Tablet.BoundaryColorEdges
import Tablet.ColoredVertexSetClosed
import Tablet.Incident
import Tablet.KTriple
import Tablet.TashkinovTree
import Tablet.TreeExitPath
import Tablet.TreeMissingColors

-- [TABLET NODE: TchangeCounterexample]
structure TchangeCounterexample {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E) where
-- BODY
  phi : PartialEdgeColoring E k
  T : TreeSequence G e0
  a : Fin k
  b : Fin k
  colorsDistinct : a ≠ b
  triple : KTriple G k e0 phi
  tree : TashkinovTree G e0 phi T
  closed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T)
  aMissing : a ∈ TreeMissingColors phi T
  bNotMissing : b ∉ TreeMissingColors phi T
  a1 : V
  b1 : V
  a2 : V
  b2 : V
  a3 : V
  b3 : V
  P1 : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl a1) (Sum.inl b1)
  P2 : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl a2) (Sum.inl b2)
  P3 : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl a3) (Sum.inl b3)
  exit1 : TreeExitPath T phi a b a1 b1 P1
  exit2 : TreeExitPath T phi a b a2 b2 P2
  exit3 : TreeExitPath T phi a b a3 b3 P3
  disjoint12 : ∀ x, x ∈ P1.support → x ∉ P2.support
  disjoint13 : ∀ x, x ∈ P1.support → x ∉ P3.support
  disjoint23 : ∀ x, x ∈ P2.support → x ∉ P3.support
  remote12 : a1 ≠ a2
  remote13 : a1 ≠ a3
  remote23 : a2 ≠ a3
  tree12 : b1 ≠ b2
  tree13 : b1 ≠ b3
  tree23 : b2 ≠ b3
  f1 : E
  f2 : E
  f3 : E
  boundary1 : f1 ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) b
  boundary2 : f2 ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) b
  boundary3 : f3 ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) b
  incident1 : Incident G b1 f1
  incident2 : Incident G b2 f2
  incident3 : Incident G b3 f3
  support1 : Sum.inr f1 ∈ P1.support
  support2 : Sum.inr f2 ∈ P2.support
  support3 : Sum.inr f3 ∈ P3.support
