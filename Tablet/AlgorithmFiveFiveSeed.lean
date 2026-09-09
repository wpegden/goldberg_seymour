import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.HierarchyBase
import Tablet.KTriple
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumProperty
import Tablet.OrderedTreeUnion
import Tablet.StableColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment

-- [TABLET NODE: AlgorithmFiveFiveSeed]
theorem AlgorithmFiveFiveSeed {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett) (base : HierarchyBase ett phi)
    (hcoreStrict :
      ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE →
        (ett.series.data.tree (Fin.last ett.rounds).castSucc).length <
          base.core.length)
    (hcoreClosure :
      ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE →
        TashkinovClosure phi base.core
          (ett.series.data.tree (Fin.last (ett.rounds + 1)))) :
    ∃ (J : TreeSequence G e0)
        (corrJ : CorrespondingExtendedTashkinovTree G k e0 ett phi J),
      MaximumProperty corrJ.replacementETT ∧
      TreeSequenceInitialSegment J
        (ett.series.data.tree (Fin.last (ett.rounds + 1))) ∧
      ∃ baseJ : HierarchyBase corrJ.replacementETT phi,
        baseJ.core = base.core ∧
        baseJ.closure = base.closure ∧
        baseJ.supportPosition.val = base.supportPosition.val ∧
        ∃ KJ : TashkinovHierarchy corrJ.replacementETT baseJ,
          KJ.dividerCount = 0 ∧
          KJ.stage 0 =
            ett.series.data.tree (Fin.last ett.rounds).castSucc ∧
          KJ.stage (Fin.last (KJ.dividerCount + 1)) = J ∧
          ((ett.series.data.kind (Fin.last ett.rounds) =
                some TashkinovExtensionKind.PE ∧
              J = base.core) ∨
            ((ett.series.data.kind (Fin.last ett.rounds) =
                  some TashkinovExtensionKind.SE ∨
                ett.series.data.kind (Fin.last ett.rounds) =
                  some TashkinovExtensionKind.RE) ∧
              ∃ f : E,
                ett.series.data.connectingEdges (Fin.last ett.rounds) = {f} ∧
                TreeSequenceAdjoinEdge
                  (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                  f J ∧
                TashkinovAugmentationSequence phi J
                  (ett.series.data.tree (Fin.last (ett.rounds + 1))))) := by
-- BODY
  let terminalIndex : Fin (ett.rounds + 1) := Fin.last ett.rounds
  have terminal := ett.series.certified terminalIndex
  generalize terminalEquality : terminalIndex = chosenIndex at terminal
  have initialTrans : ∀ (A B C : TreeSequence G e0),
      TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B C →
        TreeSequenceInitialSegment A C := by
    intro A B C hab hbc
    rcases hab with ⟨hab, hva, hea⟩
    rcases hbc with ⟨hbc, hvb, heb⟩
    refine ⟨Nat.le_trans hab hbc, ?_, ?_⟩
    · intro i
      calc
        C.vertex (Fin.castLE (Nat.succ_le_succ (Nat.le_trans hab hbc)) i) =
            C.vertex (Fin.castLE (Nat.succ_le_succ hbc)
              (Fin.castLE (Nat.succ_le_succ hab) i)) := by congr 1
        _ = B.vertex (Fin.castLE (Nat.succ_le_succ hab) i) := hvb _
        _ = A.vertex i := hva _
    · intro i
      calc
        C.edge (Fin.castLE (Nat.le_trans hab hbc) i) =
            C.edge (Fin.castLE hbc (Fin.castLE hab i)) := by congr 1
        _ = B.edge (Fin.castLE hab i) := heb _
        _ = A.edge i := hea _
  have initialFromSequence : ∀ (A B : TreeSequence G e0),
      TashkinovAugmentationSequence phi A B →
        TreeSequenceInitialSegment A B := by
    intro A B hseq
    unfold TashkinovAugmentationSequence at hseq
    induction hseq using Relation.ReflTransGen.head_induction_on with
    | refl =>
        refine ⟨le_rfl, ?_, ?_⟩
        · intro i; rfl
        · intro i; rfl
    | head hstep htail ih =>
        rcases hstep with ⟨hlen, hseg, color, hcolor, hmiss⟩
        exact initialTrans _ _ _ hseg ih
  have seriesProper : ∀ j : Fin (ett.rounds + 1),
      IsProperEdgeColoring G (ett.series.data.coloring j) := by
    intro j
    have certificate := ett.series.certified j
    cases certificate with
    | initial triple seedLength initialColoring initialStored initialEdges initialKind
        initialVertex initialOutside initialDelta initialGamma initialClosure =>
        simpa [initialColoring] using triple.2.2.2.1
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
        rw [currentColoring]
        exact choice.selectedProper
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma closedExtension orderedExtension
        strictExtension =>
        exact currentProper
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored currentEdges
        currentKind currentVertex currentOutside currentDelta currentGamma adjoined
        adjoinedExactly closedExtension orderedExtension strictExtension =>
        rw [currentColoring]
        exact previousProper
  have seriesOneUncolored : ∀ j : Fin (ett.rounds + 1),
      IsOneEdgeUncolored (ett.series.data.coloring j) e0 := by
    intro j
    have certificate := ett.series.certified j
    cases certificate with
    | initial triple seedLength initialColoring initialStored initialEdges initialKind
        initialVertex initialOutside initialDelta initialGamma initialClosure =>
        simpa [initialColoring] using triple.2.2.2.2
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
        rw [currentColoring]
        exact choice.selectedOneUncolored
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma closedExtension orderedExtension
        strictExtension =>
        exact currentOneUncolored
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored currentEdges
        currentKind currentVertex currentOutside currentDelta currentGamma adjoined
        adjoinedExactly closedExtension orderedExtension strictExtension =>
        rw [currentColoring]
        exact previousOneUncolored
  have selfStable : ∀ (X : TreeSequence G e0) (C : Finset (Fin k))
      (q : PartialEdgeColoring E k), StableColoring X C q q := by
    intro X C q
    exact ⟨fun f hf h => rfl, fun v hv => rfl⟩
  let buildCorresponding : ∀ (J : TreeSequence G e0),
      TreeSequenceInitialSegment
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) J →
      (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < J.length →
      TreeSequenceInitialSegment J
        (ett.series.data.tree (Fin.last (ett.rounds + 1))) →
        CorrespondingExtendedTashkinovTree G k e0 ett phi J := by
    intro J hpen hstrict hJ
    let replacementETT : ExtendedTashkinovTree G k e0 input J phi :=
      { rounds := ett.rounds
        roundsPositive := ett.roundsPositive
        series := ett.series
        abovePenultimate := hpen
        strictAbovePenultimate := hstrict
        belowFinal := hJ
        generatingColoring := ett.generatingColoring }
    refine
      { replacementInput := input
        replacementSeries := ett.series
        replacementETT := replacementETT
        rungAgreement := rfl
        seriesPresentation := by dsimp [replacementETT]; rfl
        finalGeneratingColoring := ett.generatingColoring
        ladderTreesAgree := fun j => rfl
        storedColorsAgree := fun j => rfl
        connectingEdgesAgree := fun j => rfl
        extensionKindsAgree := fun j => rfl
        replacementProper := fun j => seriesProper j
        replacementOneUncolored := fun j => seriesOneUncolored j
        replacementStable := fun j => selfStable _ _ _ }
  let buildHierarchy := fun (J : TreeSequence G e0)
      (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi J)
      (baseJ : HierarchyBase corr.replacementETT phi)
      (hpen : TreeSequenceInitialSegment
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) J)
      (hstrict : (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < J.length)
      (hcore : TreeSequenceInitialSegment baseJ.core J)
      (hbaseStage : ett.series.data.tree (Fin.last ett.rounds).castSucc =
        corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc) =>
    ({ dividerCount := 0
       stage := fun q => if q.val = 0 then
         ett.series.data.tree (Fin.last ett.rounds).castSucc else J
       baseStage := by simpa [hbaseStage]
       terminalStage := by simp
       nested := by
         intro j
         have hj : j = 0 := Fin.eq_zero j
         subst j
         simpa using hpen
       strict := by
         intro j
         have hj : j = 0 := Fin.eq_zero j
         subst j
         simpa using hstrict
       dividerPosition := fun q => Fin.elim0 q
       dividerPositive := fun q => Fin.elim0 q
       dividerIncreasing := fun q r h => Fin.elim0 q
       dividerStage := fun q => Fin.elim0 q
       coreInsideFirst := hcore } : TashkinovHierarchy corr.replacementETT baseJ)
  cases terminal with
  | initial triple seedLength initialColoring initialStored initialEdges initialKind
      initialVertex initialOutside initialDelta initialGamma initialClosure =>
      have impossible : (0 : ℕ) < ett.rounds := ett.roundsPositive
      dsimp [terminalIndex] at terminalEquality
      have valueEquality := congrArg Fin.val terminalEquality
      dsimp [terminalIndex] at valueEquality
      omega
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
      have indexEquality : i.succ = Fin.last ett.rounds := by
        apply Fin.ext
        dsimp [terminalIndex] at terminalEquality
        omega
      have hkind : ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.SE := by simpa [indexEquality] using currentKind
      have hseq : TashkinovAugmentationSequence phi adjoined
          (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
        simpa [ett.generatingColoring, indexEquality] using closedExtension.1
      have hJ : TreeSequenceInitialSegment adjoined
          (ett.series.data.tree (Fin.last (ett.rounds + 1))) :=
        initialFromSequence _ _ hseq
      have hpen : TreeSequenceInitialSegment
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) adjoined := by
        simpa [indexEquality] using adjoinedExactly.2.1
      have hstrict : (ett.series.data.tree (Fin.last ett.rounds).castSucc).length <
          adjoined.length := by
        have hlen := adjoinedExactly.1
        have hlen' : adjoined.length =
            (ett.series.data.tree (Fin.last ett.rounds).castSucc).length + 1 := by
          simpa [indexEquality] using hlen
        omega
      let corr := buildCorresponding adjoined hpen hstrict hJ
      refine ⟨adjoined, corr, ?_, hJ, ?_⟩
      · simpa only [MaximumProperty] using hMP
      · let baseJ : HierarchyBase corr.replacementETT phi := by
          dsimp [corr]
          exact {
            core := base.core
            closure := base.closure
            supportPosition := base.supportPosition
            supportPositive := base.supportPositive
            terminalMissingColors := base.terminalMissingColors
            parallel := base.parallel
            nonparallel := base.nonparallel }
        refine ⟨baseJ, rfl, rfl, ?_, ?_⟩
        · simp [baseJ]
        · have hbase : base.core =
              ett.series.data.tree (Fin.last ett.rounds).castSucc :=
            base.nonparallel (by simpa [hkind])
          have hb : baseJ.core =
              ett.series.data.tree (Fin.last ett.rounds).castSucc := by
            dsimp [baseJ]
            exact hbase
          have hc : TreeSequenceInitialSegment baseJ.core adjoined := by
            rw [hb]
            exact hpen
          let KJ := buildHierarchy adjoined corr baseJ hpen hstrict hc (by rfl)
          exact ⟨KJ, rfl, rfl, rfl,
            Or.inr ⟨Or.inl hkind,
              ⟨choice.edge, by simpa [indexEquality] using currentEdges,
                (by simpa [indexEquality] using adjoinedExactly), hseq⟩⟩⟩
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
      have indexEquality : i.succ = Fin.last ett.rounds := by
        apply Fin.ext
        dsimp [terminalIndex] at terminalEquality
        omega
      have hkind : ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE := by simpa [indexEquality] using currentKind
      have hseq := hcoreClosure hkind
      have hJ : TreeSequenceInitialSegment base.core
          (ett.series.data.tree (Fin.last (ett.rounds + 1))) :=
        initialFromSequence _ _ hseq.1
      rcases base.parallel hkind with ⟨chosen, hclosed, hunion⟩
      rcases hunion with ⟨union⟩
      have hpen : TreeSequenceInitialSegment
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) base.core :=
        union.leftSegment
      have hstrict : (ett.series.data.tree (Fin.last ett.rounds).castSucc).length <
          base.core.length := hcoreStrict hkind
      let corr := buildCorresponding base.core hpen hstrict hJ
      refine ⟨base.core, corr, ?_, hJ, ?_⟩
      · simpa only [MaximumProperty] using hMP
      · let baseJ : HierarchyBase corr.replacementETT phi := by
          dsimp [corr]
          exact {
            core := base.core
            closure := base.closure
            supportPosition := base.supportPosition
            supportPositive := base.supportPositive
            terminalMissingColors := base.terminalMissingColors
            parallel := base.parallel
            nonparallel := base.nonparallel }
        refine ⟨baseJ, rfl, rfl, ?_, ?_⟩
        · simp [baseJ]
        · let KJ := buildHierarchy base.core corr baseJ hpen hstrict (by
            simpa [baseJ] using (show TreeSequenceInitialSegment base.core base.core from
              ⟨le_rfl, (fun i => rfl), (fun i => rfl)⟩)) (by rfl)
          exact ⟨KJ, rfl, rfl, rfl, Or.inl ⟨hkind, rfl⟩⟩
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma adjoined
      adjoinedExactly closedExtension orderedExtension strictExtension =>
      have indexEquality : i.succ = Fin.last ett.rounds := by
        apply Fin.ext
        dsimp [terminalIndex] at terminalEquality
        omega
      have hkind : ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.RE := by simpa [indexEquality] using currentKind
      have hseq : TashkinovAugmentationSequence phi adjoined
          (ett.series.data.tree (Fin.last (ett.rounds + 1))) := by
        simpa [ett.generatingColoring, indexEquality] using closedExtension.1
      have hJ : TreeSequenceInitialSegment adjoined
          (ett.series.data.tree (Fin.last (ett.rounds + 1))) :=
        initialFromSequence _ _ hseq
      have hpen : TreeSequenceInitialSegment
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) adjoined := by
        simpa [indexEquality] using adjoinedExactly.2.1
      have hstrict : (ett.series.data.tree (Fin.last ett.rounds).castSucc).length <
          adjoined.length := by
        have hlen := adjoinedExactly.1
        have hlen' : adjoined.length =
            (ett.series.data.tree (Fin.last ett.rounds).castSucc).length + 1 := by
          simpa [indexEquality] using hlen
        omega
      let corr := buildCorresponding adjoined hpen hstrict hJ
      refine ⟨adjoined, corr, ?_, hJ, ?_⟩
      · simpa only [MaximumProperty] using hMP
      · let baseJ : HierarchyBase corr.replacementETT phi := by
          dsimp [corr]
          exact {
            core := base.core
            closure := base.closure
            supportPosition := base.supportPosition
            supportPositive := base.supportPositive
            terminalMissingColors := base.terminalMissingColors
            parallel := base.parallel
            nonparallel := base.nonparallel }
        refine ⟨baseJ, rfl, rfl, ?_, ?_⟩
        · simp [baseJ]
        · have hbase : base.core =
              ett.series.data.tree (Fin.last ett.rounds).castSucc :=
            base.nonparallel (by simpa [hkind])
          have hb : baseJ.core =
              ett.series.data.tree (Fin.last ett.rounds).castSucc := by
            dsimp [baseJ]
            exact hbase
          have hc : TreeSequenceInitialSegment baseJ.core adjoined := by
            rw [hb]
            exact hpen
          let KJ := buildHierarchy adjoined corr baseJ hpen hstrict hc (by rfl)
          exact ⟨KJ, rfl, rfl, rfl,
            Or.inr ⟨Or.inr hkind,
              ⟨available.edge, by simpa [indexEquality] using currentEdges,
                (by simpa [indexEquality] using adjoinedExactly), hseq⟩⟩⟩
