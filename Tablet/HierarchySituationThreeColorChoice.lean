import Tablet.GoodHierarchy
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.NineN
import Tablet.SameGoodHierarchy
import Tablet.SameHierarchyStages
import Tablet.TashkinovHierarchy
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix

-- [TABLET NODE: HierarchySituationThreeColorChoice]
theorem HierarchySituationThreeColorChoice
    {V E : Type*}
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
    (alpha : Fin k)
    (hpathLower : 2 <= HierarchyPathNumber C.hierarchy)
    (hpathUpper :
      HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C)
    (halpha :
      let H := P.counterexample.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
        Fin.last P.corresponding.replacementETT.rounds
      let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
      let j := HierarchyPathNumber C.hierarchy
      let B := HierarchyFullTailPrefix C (j - 2)
      let D := HierarchyStoredColorsAt H q
      let Gamma := D.biUnion (P.counterexample.good.gamma q)
      let baseExtraMissing :=
        ((TreeSequenceVertexSet P.replacementBase.core \
            TreeSequenceVertexSet Tn).biUnion
          fun v => MissingColors G P.coloring v)
      alpha ∈ MissingColors G P.coloring
          (T.vertex (Fin.last T.length)) /\
        alpha ∈ TreeMissingColors P.coloring B /\
        (alpha ∉ Gamma ∪ baseExtraMissing ∨
          exists eta : Fin k, eta ∈ D /\
            alpha ∈ P.counterexample.good.gamma q eta /\
            (HierarchyFirstMissingPosition P.coloring T eta).val <=
              B.length)) :
    let H := P.counterexample.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let j := HierarchyPathNumber C.hierarchy
    let A := HierarchyStarredStage H q
    let B := HierarchyFullTailPrefix C (j - 2)
    let D := HierarchyStoredColorsAt H q
    let Gamma := D.biUnion (P.counterexample.good.gamma q)
    let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
      Fin.last P.corresponding.replacementETT.rounds
    let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
    let baseExtraMissing :=
      ((TreeSequenceVertexSet P.replacementBase.core \
          TreeSequenceVertexSet Tn).biUnion
        fun v => MissingColors G P.coloring v)
    let tailUsedThroughJ :=
      (Finset.univ : Finset (Fin k)).filter fun c =>
        exists r : Fin T.length,
          A.length <= r.val /\ r.val < A.length + j /\
            P.coloring (T.edge r) = some c
    exists beta : Fin k,
      beta ≠ alpha /\
        beta ∈ TreeMissingColors P.coloring B /\
        beta ∉ Gamma /\ beta ∉ tailUsedThroughJ /\
        (beta ∉ baseExtraMissing ∪ D ∨
          beta ∈ D /\
            Disjoint (P.counterexample.good.gamma q beta ∪ {beta})
              tailUsedThroughJ) := by
-- BODY
  sorry
