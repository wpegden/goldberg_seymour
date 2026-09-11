import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesData
import Tablet.TashkinovSeriesStep
import Tablet.TreeSequence

-- [TABLET NODE: CertifiedSeriesRoundsBound]
lemma CertifiedSeriesRoundsBound
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k rounds : Nat) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input) :
    rounds + 2 <= Fintype.card V := by
-- BODY
  have stepStrict : forall r : Fin rounds,
      (series.data.tree r.succ.castSucc).length <
        (series.data.tree r.succ.succ).length := by
    intro r
    have fact := series.certified r.succ
    generalize hi : r.succ = z at fact
    cases fact with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
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
      simpa [hi] using strictExtension
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
      simpa [hi] using strictExtension
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      have hsame : i = r := by
        apply Fin.ext
        simpa using (congrArg Fin.val hi).symm
      subst i
      simpa [hi] using strictExtension
  have chain : forall j : Nat, forall hj : j <= rounds,
      (series.data.tree (1 : Fin (rounds + 2))).length + j <=
        (series.data.tree (Fin.castLE (by omega : j + 2 <= rounds + 2)
          (Fin.last (j + 1)))).length := by
    intro j
    induction j with
    | zero =>
      intro hj
      have hindex :
          Fin.castLE (by omega : 0 + 2 <= rounds + 2) (Fin.last (0 + 1)) =
            (1 : Fin (rounds + 2)) := by
        apply Fin.ext
        simp
      rw [hindex]
      simp
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      let r : Fin rounds := ⟨j, by omega⟩
      have hstep := stepStrict r
      have oldIndex : r.succ.castSucc =
          Fin.castLE (by omega : j + 2 <= rounds + 2) (Fin.last (j + 1)) := by
        apply Fin.ext
        simp [r]
      have newIndex : r.succ.succ =
          Fin.castLE (by omega : j + 3 <= rounds + 2) (Fin.last (j + 2)) := by
        apply Fin.ext
        simp [r]
      rw [oldIndex, newIndex] at hstep
      have targetIndex :
          Fin.castLE (by omega : Nat.succ j + 2 <= rounds + 2)
              (Fin.last (Nat.succ j + 1)) =
            Fin.castLE (by omega : j + 3 <= rounds + 2)
              (Fin.last (j + 2)) := by
        apply Fin.ext
        simp
      rw [targetIndex]
      omega
  have hchain := chain rounds (le_rfl)
  have finalIndex :
      Fin.castLE (by omega : rounds + 2 <= rounds + 2) (Fin.last (rounds + 1)) =
        Fin.last (rounds + 1) := by
    apply Fin.ext
    simp
  rw [finalIndex] at hchain
  have hpositive := (series.data.tree (1 : Fin (rounds + 2))).positive
  have hcard :
      (series.data.tree (Fin.last (rounds + 1))).length + 1 <=
        Fintype.card V := by
    simpa using Fintype.card_le_of_injective
      (series.data.tree (Fin.last (rounds + 1))).vertex
      (series.data.tree (Fin.last (rounds + 1))).vertex_injective
  omega
