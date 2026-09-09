import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyPathNumber
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MissingColors
import Tablet.TashkinovAugmentationSequence
import Tablet.TreeColoringInvariant
import Tablet.TreeMissingColors
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponentSwap

set_option maxHeartbeats 800000

-- [TABLET NODE: HierarchySituationThreeDisjointData]
structure HierarchySituationThreeDisjointData {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx)
    (alpha beta : Fin k) where
-- BODY
  switched : HierarchyReplacementPresentation
    G k e0 input T phi ett base C ctx
  switchedColoring : switched.coloring =
    TwoColorComponentSwap G P.coloring alpha beta
      (Sum.inl (T.vertex (Fin.last T.length)))
  proper : IsProperEdgeColoring G switched.coloring
  oneEdgeUncolored : IsOneEdgeUncolored switched.coloring e0
  invariantOnSplit :
    let j := HierarchyPathNumber C.hierarchy
    let X := HierarchyFullTailPrefix C (j - 1)
    TreeColoringInvariant X P.coloring switched.coloring
  affectedMissingOnSplit :
    let j := HierarchyPathNumber C.hierarchy
    let X := HierarchyFullTailPrefix C (j - 1)
    alpha ∈ TreeMissingColors switched.coloring X ∧
      beta ∈ TreeMissingColors switched.coloring X
  transportedSuffix :
    let j := HierarchyPathNumber C.hierarchy
    let X := HierarchyFullTailPrefix C (j - 1)
    TashkinovAugmentationSequence switched.coloring X T
  betaMissingTerminal :
    beta ∈ MissingColors G switched.coloring
      (T.vertex (Fin.last T.length))
  betaMissingTwoBefore :
    let j := HierarchyPathNumber C.hierarchy
    let B := HierarchyFullTailPrefix C (j - 2)
    beta ∈ TreeMissingColors switched.coloring B
  betaOutsideGamma :
    let H := switched.counterexample.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let D := HierarchyStoredColorsAt H q
    let Gamma := D.biUnion (switched.counterexample.good.gamma q)
    beta ∉ Gamma
  conditionNine :
    let H := switched.counterexample.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let A := HierarchyStarredStage H q
    let j := HierarchyPathNumber C.hierarchy
    let B := HierarchyFullTailPrefix C (j - 2)
    let n : Fin (switched.corresponding.replacementETT.rounds + 1) :=
      Fin.last switched.corresponding.replacementETT.rounds
    let Tn := switched.corresponding.replacementETT.series.data.tree n.castSucc
    let D := HierarchyStoredColorsAt H q
    let Gamma := D.biUnion (switched.counterexample.good.gamma q)
    let baseExtraMissing :=
      ((TreeSequenceVertexSet switched.replacementBase.core \
          TreeSequenceVertexSet Tn).biUnion
        fun v => MissingColors G switched.coloring v)
    let tailUsedThroughJ :=
      (Finset.univ : Finset (Fin k)).filter fun c =>
        ∃ r : Fin T.length,
          A.length ≤ r.val ∧ r.val < A.length + j ∧
            switched.coloring (T.edge r) = some c
    (beta ∉ baseExtraMissing ∧ beta ∉ tailUsedThroughJ ∧
        beta ∉ Gamma ∧ beta ∉ D) ∨
      (beta ∈ D ∧ beta ∈ TreeMissingColors switched.coloring B ∧
        Disjoint (switched.counterexample.good.gamma q beta ∪ {beta})
          tailUsedThroughJ)
  theta : Fin k
  thetaMissingAtJ :
    let j := HierarchyPathNumber C.hierarchy
    let Y := HierarchyFullTailPrefix C j
    theta ∈ MissingColors G switched.coloring
      (Y.vertex (Fin.last Y.length))
  thetaOutsideGamma :
    let H := switched.counterexample.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let D := HierarchyStoredColorsAt H q
    let Gamma := D.biUnion (switched.counterexample.good.gamma q)
    theta ∉ Gamma
