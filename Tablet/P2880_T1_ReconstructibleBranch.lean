import Tablet.P2880_T1_SplitSwapData
import Tablet.P2880_T1_KempeOrientation
import Tablet.StableChangeCasesOneTwoSplitTail

-- [TABLET NODE: P2880_T1_ReconstructibleBranch]
theorem P2880_T1_ReconstructibleBranch
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
    (hcase :
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
      qualifies alpha beta ∨ qualifies beta alpha) :
    ∃ corr : CorrespondingExtendedTashkinovTree G k e0
        P.corresponding.replacementETT sigma T,
      MaximumProperty corr.replacementETT ∧
      ∃ newBase : HierarchyBase corr.replacementETT sigma,
        ∃ K : TashkinovHierarchy corr.replacementETT newBase,
          ∃ good : GoodHierarchy K,
            SameGoodHierarchy P.counterexample.good good := by
-- BODY
  classical
  let X := HierarchyFullTailPrefix C (HierarchyPathNumber C.hierarchy - 1)
  have fixed : ∀ t : Fin T.length,
      (HierarchyStarredStage P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount)).length ≤ t.val →
      t.val < X.length → sigma (T.edge t) = P.coloring (T.edge t) := by
    intro t _ ht
    exact S.fixedOnSplit t ht
  rcases hcase with hcase | hcase
  · have changed := StableChangeCasesOneTwoSplitTail G k e0
      P.corresponding.replacementInput T P.coloring
      P.corresponding.replacementETT P.replacementBase P.counterexample
      P.minimumContext alpha beta S.distinct S.oldMissingOnPenultimate
      (Sum.inl (T.vertex (Fin.last T.length))) S.path sigma S.swapped hcase
      S.separatedAlpha X S.splitAboveStar.1 S.splitAboveStar.2
      S.splitInPenultimate fixed S.prefixRoute S.oldSuffix S.missingOnSplit
      S.penultimateMissing S.storedFirst S.gammaCutoff
    exact changed.2.2
  · obtain ⟨hgraph, hcomponents, hswaps, hpaths⟩ :=
      P2880_T1_KempeOrientation G P.coloring alpha beta S.distinct
    have hsigma : sigma = TwoColorComponentSwap G P.coloring beta alpha
        (Sum.inl (T.vertex (Fin.last T.length))) :=
      S.swapped.trans (hswaps _)
    have hpath : TwoColorPathComponent G P.coloring beta alpha
        (Sum.inl (T.vertex (Fin.last T.length))) := (hpaths _).mp S.path
    have hsep : Disjoint
        (TwoColorComponent G P.coloring beta alpha
          (Sum.inl (T.vertex (Fin.last T.length))))
        (TwoColorComponent G P.coloring beta alpha
          (Sum.inl (T.vertex (HierarchyFirstMissingPosition P.coloring T beta)))) := by
      simpa only [← hcomponents] using S.separatedBeta
    have hcut :
        let H := P.counterexample.hierarchy
        let q := Fin.last H.dividerCount
        ∀ eta ∈ HierarchyStoredColorsAt H q,
          (beta ∈ P.counterexample.good.gamma q eta ∨
            alpha ∈ P.counterexample.good.gamma q eta) →
          (HierarchyFirstMissingPosition P.coloring T eta).val ≤ X.length := by
      dsimp only
      intro eta heta hc
      exact S.gammaCutoff eta heta hc.symm
    have changed := StableChangeCasesOneTwoSplitTail G k e0
      P.corresponding.replacementInput T P.coloring
      P.corresponding.replacementETT P.replacementBase P.counterexample
      P.minimumContext beta alpha (Ne.symm S.distinct)
      S.oldMissingOnPenultimate.symm
      (Sum.inl (T.vertex (Fin.last T.length))) hpath sigma hsigma hcase
      hsep X S.splitAboveStar.1 S.splitAboveStar.2
      S.splitInPenultimate fixed S.prefixRoute S.oldSuffix S.missingOnSplit.symm
      S.penultimateMissing S.storedFirst hcut
    exact changed.2.2
