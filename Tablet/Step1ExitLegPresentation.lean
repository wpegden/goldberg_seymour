import Tablet.BoundaryColorEdges
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyBase
import Tablet.HierarchyTerminalStoredColors
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumProperty
import Tablet.TreeColorSetClosed
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeExitPath
import Tablet.TreeMissingColors
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: Step1ExitLegPresentation]
structure Step1ExitLegPresentation {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (n q : ℕ) where
-- BODY
  input : PartialEdgeColoring E k
  T : TreeSequence G e0
  phi : PartialEdgeColoring E k
  ett : ExtendedTashkinovTree G k e0 input T phi
  base : HierarchyBase ett phi
  hierarchy : TashkinovHierarchy ett base
  good : GoodHierarchy hierarchy
  rounds_eq : ett.rounds = n
  maximum : MaximumProperty ett
  divider_lt : hierarchy.dividerCount < q
  proper : IsProperEdgeColoring G phi
  oneUncolored : IsOneEdgeUncolored phi e0
  large : 2 * ett.rounds + 11 ≤
    (TreeMissingColors phi
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card
  terminalMinusClosed : TreeColorSetMinusClosed G phi T
    ((HierarchyTerminalStoredColors hierarchy).biUnion
      (good.gamma (Fin.last hierarchy.dividerCount)))
  a : Fin k
  b : Fin k
  a_ne_b : a ≠ b
  aMissing : a ∈ TreeMissingColors phi T
  aClosed : TreeColorSetClosed G phi T {a}
  a1 : V
  b1 : V
  a2 : V
  b2 : V
  P1 : (TwoColorIncidenceGraph G phi a b).Walk
    (Sum.inl a1) (Sum.inl b1)
  P2 : (TwoColorIncidenceGraph G phi a b).Walk
    (Sum.inl a2) (Sum.inl b2)
  exit1 : TreeExitPath T phi a b a1 b1 P1
  exit2 : TreeExitPath T phi a b a2 b2 P2
  disjoint12 : ∀ x, x ∈ P1.support → x ∉ P2.support
  outsideDistinct : a1 ≠ a2
  treeDistinct : b1 ≠ b2
  treeOrder : TreeVertexOrder T b1 b2
  f1 : E
  f2 : E
  boundary1 : f1 ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) b
  boundary2 : f2 ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) b
  incident1 : Incident G b1 f1
  incident2 : Incident G b2 f2
  support1 : Sum.inr f1 ∈ P1.support
  support2 : Sum.inr f2 ∈ P2.support
