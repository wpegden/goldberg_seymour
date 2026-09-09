import Tablet.CorrespondingExtendedTashkinovTreeTrans
import Tablet.HierarchyReplacementPresentation

-- [TABLET NODE: HierarchyReplacementPresentationTrans]
lemma HierarchyReplacementPresentationTrans
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
    (tau : PartialEdgeColoring E k)
    (second : CorrespondingExtendedTashkinovTree G k e0
      P.corresponding.replacementETT tau T)
    (baseSecond : HierarchyBase second.replacementETT tau)
    (CSecond : HierarchyCounterexample baseSecond)
    (sameGoodSecond : SameGoodHierarchy
      P.counterexample.good CSecond.good) :
    Exists fun PSecond : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx =>
        PSecond.coloring = tau := by
-- BODY
  obtain ⟨composite, hinput, hseries, hett⟩ :=
    CorrespondingExtendedTashkinovTreeTrans G k e0 input T phi
      P.coloring tau ett P.corresponding second
  rcases composite with ⟨compositeInput, compositeSeries, compositeETT,
    compositeRung, compositePresentation, compositeFinal,
    compositeLadder, compositeStored, compositeEdges, compositeKinds,
    compositeProper, compositeOne, compositeStable⟩
  rcases second with ⟨secondInput, secondSeries, secondETT,
    secondRung, secondPresentation, secondFinal,
    secondLadder, secondStored, secondEdges, secondKinds,
    secondProper, secondOne, secondStable⟩
  cases hinput
  have ettEq : compositeETT = secondETT := by
    exact eq_of_heq hett
  revert baseSecond CSecond sameGoodSecond
  cases ettEq
  intro baseSecond CSecond sameGoodSecond
  let second : CorrespondingExtendedTashkinovTree
      G k e0 P.corresponding.replacementETT tau T := {
    replacementInput := compositeInput
    replacementSeries := secondSeries
    replacementETT := compositeETT
    rungAgreement := secondRung
    seriesPresentation := secondPresentation
    finalGeneratingColoring := secondFinal
    ladderTreesAgree := secondLadder
    storedColorsAgree := secondStored
    connectingEdgesAgree := secondEdges
    extensionKindsAgree := secondKinds
    replacementProper := secondProper
    replacementOneUncolored := secondOne
    replacementStable := secondStable }
  let composite : CorrespondingExtendedTashkinovTree G k e0 ett tau T := {
    replacementInput := compositeInput
    replacementSeries := compositeSeries
    replacementETT := compositeETT
    rungAgreement := compositeRung
    seriesPresentation := compositePresentation
    finalGeneratingColoring := compositeFinal
    ladderTreesAgree := compositeLadder
    storedColorsAgree := compositeStored
    connectingEdgesAgree := compositeEdges
    extensionKindsAgree := compositeKinds
    replacementProper := compositeProper
    replacementOneUncolored := compositeOne
    replacementStable := compositeStable }
  let alignedETT : ExtendedTashkinovTree G k e0 compositeInput T tau :=
    compositeETT
  let baseAligned : HierarchyBase alignedETT tau := baseSecond
  let Cfinal : HierarchyCounterexample baseAligned := CSecond
  have h12 : SameGoodHierarchy P.counterexample.good Cfinal.good := by
    simpa [Cfinal] using sameGoodSecond
  have sameComposed : SameGoodHierarchy C.good Cfinal.good := by
    have firstData := P.sameGood
    unfold SameGoodHierarchy at firstData h12 ⊢
    rcases firstData with ⟨firstStages, firstCount, firstStored⟩
    rcases h12 with ⟨secondStages, secondCount, secondStored⟩
    rcases firstStages with ⟨coreFirst, countFirst, stageFirst,
      positionFirst, kindFirst, closureFirst⟩
    rcases secondStages with ⟨coreSecond, countSecond, stageSecond,
      positionSecond, kindSecond, closureSecond⟩
    refine ⟨?_, ?_⟩
    · refine ⟨coreFirst.trans coreSecond, firstCount.trans secondCount,
        HEq.trans stageFirst stageSecond, HEq.trans positionFirst positionSecond,
        ?_, ?_⟩
      · constructor
        · intro h
          exact kindSecond.mp (kindFirst.mp h)
        · intro h
          exact kindFirst.mpr (kindSecond.mpr h)
      · intro h
        exact closureFirst h |>.trans (closureSecond (kindFirst.mp h))
    · refine ⟨firstCount.trans secondCount, ?_⟩
      have castChain : ∀ (j : Fin (C.hierarchy.dividerCount + 1)),
          Fin.cast (congrArg (fun q => q + 1) secondCount)
              (Fin.cast (congrArg (fun q => q + 1) firstCount) j) =
            Fin.cast (congrArg (fun q => q + 1) (firstCount.trans secondCount)) j := by
        intro j
        exact Fin.cast_cast _ _
      intro j
      have firstAt := firstStored j
      have secondAt := secondStored
        (Fin.cast (congrArg (fun q => q + 1) firstCount) j)
      rw [← castChain j]
      refine ⟨firstAt.1.trans secondAt.1, ?_⟩
      intro eta heta
      have hmid : eta ∈ HierarchyStoredColorsAt P.counterexample.hierarchy
          (Fin.cast (congrArg (fun q => q + 1) firstCount) j) := by
        exact firstAt.1 ▸ heta
      have gammaLink := (firstAt.2 eta heta).trans (secondAt.2 eta hmid)
      exact gammaLink
  exact ⟨by
    refine {
      coloring := tau
      corresponding := composite
      maximum := by
        have maxAligned : MaximumProperty alignedETT := by
          exact CSecond.maximum
        simpa [composite] using maxAligned
      replacementBase := by
        exact baseAligned
      counterexample := by
        exact Cfinal
      sameGood := ?_
      minimumContext := ?_ }
    · exact sameComposed
    · refine {
        proper := ?_
        oneEdgeUncolored := ?_
        lowerRung := ?_
        fewerDividers := ?_
        lexicographicMinimality := ?_
        largeMissingSet := ?_ }
      · rw [composite.finalGeneratingColoring]
        exact composite.replacementProper (Fin.last ett.rounds)
      · rw [composite.finalGeneratingColoring]
        exact composite.replacementOneUncolored (Fin.last ett.rounds)
      · intro input' T' generating' lower hpos hlt hmax
        apply ctx.lowerRung lower hpos
        · simpa [composite.rungAgreement] using hlt
        · exact hmax
      · intro input' T' generating' other hround otherMax base' K goodK hdiv
        have countLink : C.hierarchy.dividerCount = Cfinal.hierarchy.dividerCount :=
          sameComposed.2.choose
        apply ctx.fewerDividers other
          (composite.rungAgreement ▸ hround) otherMax base' K goodK
        exact countLink.symm ▸ hdiv
      · intro input' T' generating' other base' C' hr hc
        have countLink : C.hierarchy.dividerCount = Cfinal.hierarchy.dividerCount :=
          sameComposed.2.choose
        have oldMinimal := ctx.lexicographicMinimality C'
          (composite.rungAgreement ▸ hr) (hc.trans countLink.symm)
        have hmeasure :
            HierarchyCounterexampleMeasure C =
              HierarchyCounterexampleMeasure Cfinal := by
          have stageData := sameComposed.1
          unfold SameHierarchyStages at stageData
          rcases stageData with ⟨coreEq, countEq, stagesEq, positionsEq,
            kindEq, closureEq⟩
          have starHelper : ∀ (n m : Nat)
              (coreLeft coreRight : TreeSequence G e0)
              (stageLeft : Fin (n + 2) → TreeSequence G e0)
              (stageRight : Fin (m + 2) → TreeSequence G e0),
              n = m → coreLeft = coreRight → HEq stageLeft stageRight →
              (let leftStar := Fin.cases (motive := fun _ => TreeSequence G e0) coreLeft
                  (fun i : Fin n => stageLeft i.succ.castSucc) (Fin.last n)
               let rightStar := Fin.cases (motive := fun _ => TreeSequence G e0) coreRight
                  (fun i : Fin m => stageRight i.succ.castSucc) (Fin.last m)
               leftStar = rightStar) := by
            intro n m coreLeft coreRight stageLeft stageRight hnm hcore hstage
            subst m
            have hstage' : stageLeft = stageRight := eq_of_heq hstage
            simp [hcore, hstage']
          have starredEq :
              HierarchyStarredStage C.hierarchy
                  (Fin.last C.hierarchy.dividerCount) =
                HierarchyStarredStage Cfinal.hierarchy
                  (Fin.last Cfinal.hierarchy.dividerCount) := by
            exact starHelper _ _ base.core baseAligned.core
              C.hierarchy.stage Cfinal.hierarchy.stage countEq coreEq stagesEq
          unfold HierarchyCounterexampleMeasure
          have terminalEq :=
            (Fin.heq_fun_iff (congrArg (fun q => q + 2) countEq)).mp stagesEq
            (⟨C.hierarchy.dividerCount, by omega⟩ :
              Fin (C.hierarchy.dividerCount + 2))
          simp [HierarchyPathNumber, starredEq]
          have indexEq :
              Fin.cast (congrArg (fun q => q + 2) countEq)
                  (⟨C.hierarchy.dividerCount, by omega⟩ :
                    Fin (C.hierarchy.dividerCount + 2)) =
                (⟨Cfinal.hierarchy.dividerCount, by omega⟩ :
                  Fin (Cfinal.hierarchy.dividerCount + 2)) := by
            apply Fin.ext
            exact countEq
          have terminalEq' := terminalEq.trans
            (congrArg Cfinal.hierarchy.stage indexEq)
          exact congrArg (fun q => T.length - q.length) terminalEq'
        rw [← hmeasure]
        exact oldMinimal
      · dsimp
        classical
        let terminalIndex : Fin ett.rounds :=
          ⟨ett.rounds - 1, by have hp := C.positive; omega⟩
        have terminalSucc : terminalIndex.succ = Fin.last ett.rounds := by
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_last]
          have hp := C.positive
          have hi : terminalIndex.val = ett.rounds - 1 := rfl
          rw [hi]
          omega
        have terminalTree :
            terminalIndex.castSucc.succ =
              (Fin.last ett.rounds).castSucc := by
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_last, Fin.val_castSucc]
          have hp := C.positive
          have hi : terminalIndex.val = ett.rounds - 1 := rfl
          rw [hi]
          omega
        have stableTerminal := composite.replacementStable terminalIndex
        dsimp [composite] at stableTerminal
        rw [terminalTree] at stableTerminal
        rw [terminalSucc] at stableTerminal
        have colorEq :
            compositeSeries.data.coloring (Fin.last ett.rounds) = tau :=
          composite.finalGeneratingColoring.symm
        have phiEq :
            ett.series.data.coloring (Fin.last ett.rounds) = phi :=
          ett.generatingColoring.symm
        have treeEq :
            compositeETT.series.data.tree
                (Fin.last compositeETT.rounds).castSucc =
              ett.series.data.tree (Fin.last ett.rounds).castSucc := by
          have presentation : compositeETT.series =
              compositeRung.symm ▸ compositeSeries := by
            have typeLink :
                TashkinovSeries G k ett.rounds e0 compositeInput =
                  TashkinovSeries G k compositeETT.rounds e0 compositeInput :=
              congrArg (fun r => TashkinovSeries G k r e0 compositeInput)
                compositeRung.symm
            have castProof : HEq compositeSeries
                (compositeRung.symm ▸ compositeSeries) := by
              simpa using (cast_heq typeLink compositeSeries).symm
            exact eq_of_heq (HEq.trans composite.seriesPresentation castProof)
          have castTree {a b : Nat} (h : a = b)
              (s : TashkinovSeries G k a e0 compositeInput)
              (i : Fin (b + 2)) :
              (cast (congrArg (fun r => TashkinovSeries G k r e0 compositeInput) h) s).data.tree i =
                s.data.tree (Fin.cast (congrArg (fun r => r + 2) h.symm) i) := by
            cases h
            rfl
          rw [presentation]
          calc
            (compositeRung.symm ▸ compositeSeries).data.tree
                (Fin.last compositeETT.rounds).castSucc =
              compositeSeries.data.tree
                (Fin.cast (congrArg (fun r => r + 2) compositeRung)
                  (Fin.last compositeETT.rounds).castSucc) := by
                have transportEq :
                    compositeRung.symm ▸ compositeSeries =
                      cast (congrArg
                        (fun r => TashkinovSeries G k r e0 compositeInput)
                        compositeRung.symm) compositeSeries := by
                  symm
                  apply cast_eq_iff_heq.mpr
                  simpa using (cast_heq
                    (congrArg
                      (fun r => TashkinovSeries G k r e0 compositeInput)
                      compositeRung.symm) compositeSeries).symm
                rw [transportEq]
                simpa using castTree compositeRung.symm compositeSeries
                  (Fin.last compositeETT.rounds).castSucc
            _ = ett.series.data.tree (Fin.last ett.rounds).castSucc := by
              simpa [terminalTree, terminalSucc, composite] using
                composite.ladderTreesAgree terminalIndex
        have missingEq :
            TreeMissingColors tau
                (compositeETT.series.data.tree
                  (Fin.last compositeETT.rounds).castSucc) =
              TreeMissingColors phi
                (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by
          rw [treeEq]
          ext c
          simp only [TreeMissingColors, Finset.mem_biUnion]
          constructor
          · rintro ⟨v, hv, hc⟩
            refine ⟨v, hv, ?_⟩
            have hv' := stableTerminal.2 v hv
            rw [colorEq, phiEq] at hv'
            exact hv'.symm ▸ hc
          · rintro ⟨v, hv, hc⟩
            refine ⟨v, hv, ?_⟩
            have hv' := stableTerminal.2 v hv
            rw [colorEq, phiEq] at hv'
            exact hv' ▸ hc
        have bound := ctx.largeMissingSet
        dsimp at bound
        rw [← missingEq] at bound
        simpa [composite, compositeRung] using bound
  , rfl⟩
