import Tablet.P2880_T1_SplitSwapData
import Tablet.GoodHierarchyTerminalPrefixRepackage
import Tablet.HierarchyLEMStable
import Tablet.HierarchySplitter
import Tablet.Td
import Tablet.MaximumPropertyTransport
import Tablet.HierarchyFirstMissingPositionPrefixCutoff
import Tablet.P2752_T2_TerminalStoredColors
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TashkinovAugmentationSequenceInitialSegment

-- [TABLET NODE: P2880_T1_OutsidePrefixBranch]
theorem P2880_T1_OutsidePrefixBranch
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
    (alpha beta : Fin k) (sigma : PartialEdgeColoring E k)
    (S : P2880_T1_SplitSwapData G k e0 input T phi ett base C ctx P
      alpha beta sigma)
    (hneither : ¬ (
      let H := P.counterexample.hierarchy
      let q := Fin.last H.dividerCount
      let m := P.corresponding.replacementETT
      let n := Fin.last m.rounds
      let A := HierarchyStarredStage H q
      let Tnq := H.stage ⟨H.dividerCount, by omega⟩
      let Tn := m.series.data.tree n.castSucc
      let Dn := TashkinovStoredColors m.series.data n
      let qualifies := fun (a b : Fin k) =>
        (0 < H.dividerCount ∧ a ∈ TreeMissingColors P.coloring Tnq) ∨
        (H.dividerCount = 0 ∧
          (a ∈ TreeMissingColors P.coloring Tn ∨
            (a ∈ TreeMissingColors P.coloring A ∧ a ∉ Dn ∧ b ∉ Dn)))
      qualifies alpha beta ∨ qualifies beta alpha)) :
    ∃ corr : CorrespondingExtendedTashkinovTree G k e0
        P.corresponding.replacementETT sigma T,
      MaximumProperty corr.replacementETT ∧
      ∃ newBase : HierarchyBase corr.replacementETT sigma,
        ∃ K : TashkinovHierarchy corr.replacementETT newBase,
          ∃ good : GoodHierarchy K,
            SameGoodHierarchy P.counterexample.good good := by
-- BODY
  sorry

