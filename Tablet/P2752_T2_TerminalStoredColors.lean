import Tablet.CorrespondingExtendedTashkinovTree

-- [TABLET NODE: P2752_T2_TerminalStoredColors]
theorem P2752_T2_TerminalStoredColors {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input phi sigma : PartialEdgeColoring E k} {T U : TreeSequence G e0}
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma U) :
    TashkinovStoredColors corr.replacementETT.series.data
        (Fin.last corr.replacementETT.rounds) =
      TashkinovStoredColors ett.series.data (Fin.last ett.rounds) := by
-- BODY
  classical
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
    have hs := replacementStable i
    rw [hi] at hs
    have hmissing : TreeMissingColors
        (replacementSeries.data.coloring (Fin.last ett.rounds))
        (replacementSeries.data.tree (Fin.last ett.rounds).castSucc) =
        TreeMissingColors (ett.series.data.coloring (Fin.last ett.rounds))
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by
      rw [htree]
      unfold TreeMissingColors
      exact Finset.biUnion_congr rfl hs.2
    change TashkinovStoredColors replacementSeries.data (Fin.last ett.rounds) = _
    unfold TashkinovStoredColors
    simp only [storedColorsAgree, hmissing]
