import Tablet.ExtendedTashkinovTree
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeSequenceInitialSegment

-- [TABLET NODE: TashkinovSeriesFinalETTExists]
theorem TashkinovSeriesFinalETTExists
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k rounds : Nat) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input)
    (hrounds : 0 < rounds) :
    exists ett : ExtendedTashkinovTree G k e0 input
        (series.data.tree (Fin.last (rounds + 1)))
        (series.data.coloring (Fin.last rounds)),
      ett.rounds = rounds ∧ HEq ett.series series := by
-- BODY
  have stepFacts : ∀ r : Fin rounds,
      TreeSequenceInitialSegment
          (series.data.tree r.succ.castSucc) (series.data.tree r.succ.succ) ∧
        (series.data.tree r.succ.castSucc).length <
          (series.data.tree r.succ.succ).length := by
    intro r
    have fact := series.certified r.succ
    generalize hi : r.succ = z at fact ⊢
    cases fact with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
      simp_all
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      have hsame : i = r := by
        apply Fin.ext
        simpa using (congrArg Fin.val hi).symm
      subst i
      simpa [hi] using ⟨orderedExtension, strictExtension⟩
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma closedExtension orderedExtension
        strictExtension =>
      have hsame : i = r := by
        apply Fin.ext
        simpa using (congrArg Fin.val hi).symm
      subst i
      simpa [hi] using ⟨orderedExtension, strictExtension⟩
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      have hsame : i = r := by
        apply Fin.ext
        simpa using (congrArg Fin.val hi).symm
      subst i
      simpa [hi] using ⟨orderedExtension, strictExtension⟩
  let r : Fin rounds := ⟨rounds - 1, by omega⟩
  have hpen : r.succ.castSucc = (⟨rounds, by omega⟩ : Fin (rounds + 2)) := by
    apply Fin.ext
    simp [r]
    omega
  have hfinal : r.succ.succ = Fin.last (rounds + 1) := by
    apply Fin.ext
    simp [r]
    omega
  have terminalOrdered : TreeSequenceInitialSegment
      (series.data.tree ⟨rounds, by omega⟩)
      (series.data.tree (Fin.last (rounds + 1))) := by
    rw [← hpen, ← hfinal]
    exact (stepFacts r).1
  have terminalStrict :
      (series.data.tree ⟨rounds, by omega⟩).length <
        (series.data.tree (Fin.last (rounds + 1))).length := by
    rw [← hpen, ← hfinal]
    exact (stepFacts r).2
  let ett : ExtendedTashkinovTree G k e0 input
      (series.data.tree (Fin.last (rounds + 1)))
      (series.data.coloring (Fin.last rounds)) := {
    rounds := rounds
    roundsPositive := hrounds
    series := series
    abovePenultimate := terminalOrdered
    strictAbovePenultimate := terminalStrict
    belowFinal := ⟨le_rfl, (fun _ => rfl), (fun _ => rfl)⟩
    generatingColoring := rfl }
  exact ⟨ett, rfl, HEq.rfl⟩
