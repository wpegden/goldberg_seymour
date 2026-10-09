import Tablet.P2752_T2_HierarchyMeasures
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.SameGoodHierarchy

-- [TABLET NODE: P2752_T2_MinimumContextTransport]
theorem P2752_T2_MinimumContextTransport {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T)
    (newBase : HierarchyBase corr.replacementETT sigma)
    (Cnew : HierarchyCounterexample newBase)
    (hsame : SameGoodHierarchy C.good Cnew.good) :
    Nonempty (HierarchyMinimumCounterexampleContext G k e0
      corr.replacementInput T sigma corr.replacementETT newBase Cnew) := by
-- BODY
  classical
  obtain ⟨hstar, hpath, hstage⟩ :=
    P2752_T2_HierarchyMeasures C.hierarchy Cnew.hierarchy hsame.1
  have hmeasure : HierarchyCounterexampleMeasure Cnew =
      HierarchyCounterexampleMeasure C := by
    unfold HierarchyCounterexampleMeasure
    rw [← hpath, ← hstage]
  have hcount : C.hierarchy.dividerCount = Cnew.hierarchy.dividerCount := hsame.2.choose
  rcases corr with ⟨replacementInput, replacementSeries, replacementETT,
    rungAgreement, seriesPresentation, finalGeneratingColoring,
    ladderTreesAgree, storedColorsAgree, connectingEdgesAgree,
    extensionKindsAgree, replacementProper, replacementOneUncolored,
    replacementStable⟩
  cases replacementETT with
  | mk rounds roundsPositive series above strict below generating =>
    cases rungAgreement
    have hseries : series = replacementSeries := eq_of_heq seriesPresentation
    cases hseries
    let i : Fin ett.rounds := ⟨ett.rounds - 1, by have hp := ett.roundsPositive; omega⟩
    have hi : i.succ = Fin.last ett.rounds := by
      apply Fin.ext
      change ett.rounds - 1 + 1 = ett.rounds
      exact Nat.sub_add_cancel ett.roundsPositive
    have htree : replacementSeries.data.tree (Fin.last ett.rounds).castSucc =
        ett.series.data.tree (Fin.last ett.rounds).castSucc := by
      simpa [hi] using ladderTreesAgree i
    have hmissing : TreeMissingColors sigma
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) =
        TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by
      have hs := replacementStable i
      rw [hi, ← ett.generatingColoring, ← finalGeneratingColoring] at hs
      unfold TreeMissingColors
      apply Finset.biUnion_congr rfl
      intro v hv
      exact hs.2 v hv
    refine ⟨{
      proper := finalGeneratingColoring ▸ replacementProper (Fin.last ett.rounds)
      oneEdgeUncolored := finalGeneratingColoring ▸
        replacementOneUncolored (Fin.last ett.rounds)
      lowerRung := ?_
      fewerDividers := ?_
      lexicographicMinimality := ?_
      largeMissingSet := ?_ }⟩
    · intro input' T' generating' lower hp hlt hm
      exact ctx.lowerRung lower hp hlt hm
    · intro input' T' generating' other hr hm base' K good hdiv
      exact ctx.fewerDividers other hr hm base' K good (by simpa [hcount] using hdiv)
    · intro input' T' generating' other base' C' hr hc
      rw [hmeasure]
      exact ctx.lexicographicMinimality C' hr (hc.trans hcount.symm)
    · change 2 * ett.rounds + 11 ≤
        (TreeMissingColors sigma (replacementSeries.data.tree (Fin.last ett.rounds).castSucc)).card
      rw [htree, hmissing]
      exact ctx.largeMissingSet
