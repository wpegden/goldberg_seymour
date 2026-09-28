import Tablet.ColoredVertexSetElementary
import Tablet.Incident
import Tablet.TashkinovAugmentation
import Tablet.TashkinovClosure
import Tablet.TchangeCounterexample
import Tablet.TreeSequenceInitialSegment
import Tablet.TwoColorComponentSwap

-- [TABLET NODE: TchangeKempeClosureData]
structure TchangeKempeClosureData {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (C : TchangeCounterexample G k e0) where
-- BODY
  sigma : PartialEdgeColoring E k
  baseTree : TreeSequence G e0
  oneTree : TreeSequence G e0
  twoTree : TreeSequence G e0
  closedTree : TreeSequence G e0
  sigmaEq : sigma = TwoColorComponentSwap G C.phi C.a C.b (Sum.inl C.b3)
  baseInitial : TreeSequenceInitialSegment baseTree C.T
  baseLast : baseTree.vertex (Fin.last baseTree.length) = C.b3
  b1InBase : C.b1 ∈ TreeSequenceVertexSet baseTree
  b2InBase : C.b2 ∈ TreeSequenceVertexSet baseTree
  baseIsTree : TashkinovTree G e0 sigma baseTree
  firstAugmentation : TashkinovAugmentation sigma baseTree oneTree
  secondAugmentation : TashkinovAugmentation sigma oneTree twoTree
  closureRoute : TashkinovClosure sigma twoTree closedTree
  triple : KTriple G k e0 sigma
  closureTree : TashkinovTree G e0 sigma closedTree
  closureClosed : ColoredVertexSetClosed G sigma (TreeSequenceVertexSet closedTree)
  closureElementary : ColoredVertexSetElementary G sigma
    (TreeSequenceVertexSet closedTree)
  betaMissing : C.b ∈ MissingColors G sigma C.b3
  b1InClosure : C.b1 ∈ TreeSequenceVertexSet closedTree
  b2InClosure : C.b2 ∈ TreeSequenceVertexSet closedTree
  b3InClosure : C.b3 ∈ TreeSequenceVertexSet closedTree
  a1Outside : C.a1 ∉ TreeSequenceVertexSet closedTree
  a2Outside : C.a2 ∉ TreeSequenceVertexSet closedTree
  a3Outside : C.a3 ∉ TreeSequenceVertexSet closedTree
  f1EndsInside : ∀ v, Incident G v C.f1 → v ∈ TreeSequenceVertexSet closedTree
  Q1 : (TwoColorIncidenceGraph G sigma C.a C.b).Walk
    (Sum.inl C.a1) (Sum.inl C.b1)
  Q2 : (TwoColorIncidenceGraph G sigma C.a C.b).Walk
    (Sum.inl C.a2) (Sum.inl C.b2)
  Q3 : (TwoColorIncidenceGraph G sigma C.a C.b).Walk
    (Sum.inl C.a3) (Sum.inl C.b3)
  exit1 : TreeExitPath C.T sigma C.a C.b C.a1 C.b1 Q1
  exit2 : TreeExitPath C.T sigma C.a C.b C.a2 C.b2 Q2
  exit3 : TreeExitPath C.T sigma C.a C.b C.a3 C.b3 Q3
  support1 : Q1.support = C.P1.support
  support2 : Q2.support = C.P2.support
  support3 : Q3.support = C.P3.support
  length1 : Q1.length = C.P1.length
  length2 : Q2.length = C.P2.length
  length3 : Q3.length = C.P3.length
