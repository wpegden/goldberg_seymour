import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDefectiveChoice
import Tablet.sc2
import Tablet.StableColoring
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeMissingColors

-- [TABLET NODE: CorrespondingExtendedTashkinovTreeTransTrees]
lemma CorrespondingExtendedTashkinovTreeTransTrees
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k)
    (T0 T1 T2 : TreeSequence G e0)
    (phi sigma tau : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T0 phi)
    (first : CorrespondingExtendedTashkinovTree G k e0 ett sigma T1)
    (second : CorrespondingExtendedTashkinovTree
      G k e0 first.replacementETT tau T2) :
    exists composite : CorrespondingExtendedTashkinovTree G k e0 ett tau T2,
      composite.replacementInput = second.replacementInput /\
        HEq composite.replacementSeries second.replacementSeries /\
        HEq composite.replacementETT second.replacementETT := by
-- BODY
  have roundLink : second.replacementETT.rounds = ett.rounds :=
    second.rungAgreement.trans first.rungAgreement
  let transported : TashkinovSeries G k ett.rounds e0 second.replacementInput :=
    first.rungAgreement ▸ second.replacementSeries
  have seriesTransport : HEq transported second.replacementSeries := by
    have typeLink :
        TashkinovSeries G k first.replacementETT.rounds e0 second.replacementInput =
          TashkinovSeries G k ett.rounds e0 second.replacementInput :=
      congrArg (fun r => TashkinovSeries G k r e0 second.replacementInput)
        first.rungAgreement
    simpa [transported] using (cast_heq typeLink second.replacementSeries)
  have projectLast : ∀ {r s : Nat}
      {inputColoring : PartialEdgeColoring E k}
      (h : r = s) (x : TashkinovSeries G k r e0 inputColoring),
      HEq ((h ▸ x).data.coloring (Fin.last s))
        (x.data.coloring (Fin.last r)) := by
    intro r s inputColoring h x
    cases h
    rfl
  have projectTree : ∀ {r s : Nat} (h : r = s)
      {inputColoring : PartialEdgeColoring E k}
      (x : TashkinovSeries G k r e0 inputColoring)
      (i : Fin r),
      HEq ((h ▸ x).data.tree ((h ▸ i).succ.castSucc))
        (x.data.tree i.succ.castSucc) := by
    intro r s h inputColoring x i
    cases h
    rfl
  have castBack : ∀ {r s : Nat} (h : r = s) (i : Fin s),
      h ▸ (h.symm ▸ i) = i := by
    intro r s h i
    cases h
    rfl
  have castBackPlus : ∀ {r s : Nat} (h : r = s) (i : Fin (s + 1)),
      h ▸ (h.symm ▸ i) = i := by
    intro r s h i
    cases h
    rfl
  have castValue : ∀ {r s : Nat} (h : r = s) (i : Fin r),
      ((h ▸ i : Fin s) : Nat) = (i : Nat) := by
    intro r s h i
    cases h
    rfl
  have castValuePlus : ∀ {r s : Nat} (h : r = s) (i : Fin (r + 1)),
      ((h ▸ i : Fin (s + 1)) : Nat) = (i : Nat) := by
    intro r s h i
    cases h
    rfl
  have succCast : ∀ {r s : Nat} (h : r = s) (i : Fin r),
      (h ▸ i).succ = h ▸ i.succ := by
    intro r s h i
    cases h
    rfl
  have projectColoring : ∀ {r s : Nat} (h : r = s)
      {inputColoring : PartialEdgeColoring E k}
      (x : TashkinovSeries G k r e0 inputColoring) (i : Fin (r + 1)),
      HEq ((h ▸ x).data.coloring (h ▸ i)) (x.data.coloring i) := by
    intro r s h inputColoring x i
    cases h
    rfl
  have projectStored : ∀ {r s : Nat} (h : r = s)
      {inputColoring : PartialEdgeColoring E k}
      (x : TashkinovSeries G k r e0 inputColoring) (i : Fin (r + 1)),
      HEq ((h ▸ x).data.stored (h ▸ i)) (x.data.stored i) := by
    intro r s h inputColoring x i
    cases h
    rfl
  have projectEdges : ∀ {r s : Nat} (h : r = s)
      {inputColoring : PartialEdgeColoring E k}
      (x : TashkinovSeries G k r e0 inputColoring) (i : Fin (r + 1)),
      HEq ((h ▸ x).data.connectingEdges (h ▸ i)) (x.data.connectingEdges i) := by
    intro r s h inputColoring x i
    cases h
    rfl
  have projectKind : ∀ {r s : Nat} (h : r = s)
      {inputColoring : PartialEdgeColoring E k}
      (x : TashkinovSeries G k r e0 inputColoring) (i : Fin (r + 1)),
      HEq ((h ▸ x).data.kind (h ▸ i)) (x.data.kind i) := by
    intro r s h inputColoring x i
    cases h
    rfl
  have firstSeriesEq : first.replacementETT.series =
      first.rungAgreement.symm ▸ first.replacementSeries := by
    have typeLink :
        TashkinovSeries G k ett.rounds e0 first.replacementInput =
          TashkinovSeries G k first.replacementETT.rounds e0 first.replacementInput :=
      congrArg (fun r => TashkinovSeries G k r e0 first.replacementInput)
        first.rungAgreement.symm
    have castProof : HEq
        first.replacementSeries
        (first.rungAgreement.symm ▸ first.replacementSeries) := by
      simpa using (cast_heq typeLink first.replacementSeries).symm
    exact eq_of_heq (HEq.trans first.seriesPresentation castProof)
  have secondSeriesEq : second.replacementETT.series =
      second.rungAgreement.symm ▸ second.replacementSeries := by
    have typeLink :
        TashkinovSeries G k first.replacementETT.rounds e0 second.replacementInput =
          TashkinovSeries G k second.replacementETT.rounds e0 second.replacementInput :=
      congrArg (fun r => TashkinovSeries G k r e0 second.replacementInput)
        second.rungAgreement.symm
    have castProof : HEq
        second.replacementSeries
        (second.rungAgreement.symm ▸ second.replacementSeries) := by
      simpa using (cast_heq typeLink second.replacementSeries).symm
    exact eq_of_heq (HEq.trans second.seriesPresentation castProof)
  let composite : CorrespondingExtendedTashkinovTree G k e0 ett tau T2 := {
    replacementInput := second.replacementInput
    replacementSeries := transported
    replacementETT := second.replacementETT
    rungAgreement := roundLink
    seriesPresentation := by
      exact HEq.trans second.seriesPresentation seriesTransport.symm
    finalGeneratingColoring := by
      have finalTransport := projectLast first.rungAgreement second.replacementSeries
      exact second.finalGeneratingColoring.trans (eq_of_heq finalTransport).symm
    ladderTreesAgree := by
      intro i
      let middleIndex := first.rungAgreement.symm ▸ i
      have secondStep := second.ladderTreesAgree middleIndex
      have firstStep := first.ladderTreesAgree i
      rw [firstSeriesEq] at secondStep
      have transportedCast := projectTree first.rungAgreement
        second.replacementSeries middleIndex
      have firstCast := projectTree first.rungAgreement.symm
        first.replacementSeries i
      have firstStepCast :
          (first.rungAgreement.symm ▸ first.replacementSeries).data.tree
              middleIndex.succ.castSucc =
            ett.series.data.tree i.succ.castSucc := by
        exact (eq_of_heq firstCast).trans firstStep
      have secondStepCast :
          second.replacementSeries.data.tree middleIndex.succ.castSucc =
            (first.rungAgreement.symm ▸ first.replacementSeries).data.tree
              middleIndex.succ.castSucc := by
        exact secondStep
      have transportedCastEq :
          transported.data.tree i.succ.castSucc =
            second.replacementSeries.data.tree middleIndex.succ.castSucc := by
        have indexBack : first.rungAgreement ▸ middleIndex = i := by
          exact castBack first.rungAgreement i
        convert (eq_of_heq transportedCast) using 1
        · simp [transported, indexBack]
      exact transportedCastEq.trans (secondStepCast.trans firstStepCast)
    storedColorsAgree := by
      intro i
      let middleIndex := first.rungAgreement.symm ▸ i
      have a := second.storedColorsAgree middleIndex
      rw [firstSeriesEq] at a
      have b := first.storedColorsAgree i
      have c := projectStored first.rungAgreement.symm first.replacementSeries i
      have d := projectStored first.rungAgreement second.replacementSeries middleIndex
      have hi : i = first.rungAgreement ▸ middleIndex := by
        exact (castBackPlus first.rungAgreement i).symm
      have dEq : transported.data.stored i =
          second.replacementSeries.data.stored middleIndex := by
        convert (eq_of_heq d) using 1
        simpa [transported, middleIndex, Fin.cast_eq_self] using congrArg
          (fun q => transported.data.stored q)
          hi
        all_goals omega
      exact dEq.trans (a.trans ((eq_of_heq c).trans b))
    connectingEdgesAgree := by
      intro i
      let middleIndex := first.rungAgreement.symm ▸ i
      have a := second.connectingEdgesAgree middleIndex
      rw [firstSeriesEq] at a
      have b := first.connectingEdgesAgree i
      have c := projectEdges first.rungAgreement.symm first.replacementSeries i
      have d := projectEdges first.rungAgreement second.replacementSeries middleIndex
      have hi : i = first.rungAgreement ▸ middleIndex := by
        exact (castBackPlus first.rungAgreement i).symm
      have dEq : transported.data.connectingEdges i =
          second.replacementSeries.data.connectingEdges middleIndex := by
        convert (eq_of_heq d) using 1
        simpa [transported, middleIndex, Fin.cast_eq_self] using congrArg
          (fun q => transported.data.connectingEdges q)
          hi
        all_goals omega
      exact dEq.trans (a.trans ((eq_of_heq c).trans b))
    extensionKindsAgree := by
      intro i
      let middleIndex := first.rungAgreement.symm ▸ i
      have a := second.extensionKindsAgree middleIndex
      rw [firstSeriesEq] at a
      have b := first.extensionKindsAgree i
      have c := projectKind first.rungAgreement.symm first.replacementSeries i
      have d := projectKind first.rungAgreement second.replacementSeries middleIndex
      have hi : i = first.rungAgreement ▸ middleIndex := by
        exact (castBackPlus first.rungAgreement i).symm
      have dEq : transported.data.kind i =
          second.replacementSeries.data.kind middleIndex := by
        convert (eq_of_heq d) using 1
        simpa [transported, middleIndex, Fin.cast_eq_self] using congrArg
          (fun q => transported.data.kind q)
          hi
        all_goals omega
      exact dEq.trans (a.trans ((eq_of_heq c).trans b))
    replacementProper := by
      intro i
      let middleIndex := first.rungAgreement.symm ▸ i
      have hc := projectColoring first.rungAgreement second.replacementSeries middleIndex
      have hi : i = first.rungAgreement ▸ middleIndex := by
        exact (castBackPlus first.rungAgreement i).symm
      have hcEq : transported.data.coloring i =
          second.replacementSeries.data.coloring middleIndex := by
        convert (eq_of_heq hc) using 1
        simpa [transported, middleIndex, Fin.cast_eq_self] using congrArg
          (fun q => transported.data.coloring q)
          hi
        all_goals omega
      rw [hcEq]
      exact second.replacementProper middleIndex
    replacementOneUncolored := by
      intro i
      let middleIndex := first.rungAgreement.symm ▸ i
      have hc := projectColoring first.rungAgreement second.replacementSeries middleIndex
      have hi : i = first.rungAgreement ▸ middleIndex := by
        exact (castBackPlus first.rungAgreement i).symm
      have hcEq : transported.data.coloring i =
          second.replacementSeries.data.coloring middleIndex := by
        convert (eq_of_heq hc) using 1
        simpa [transported, middleIndex, Fin.cast_eq_self] using congrArg
          (fun q => transported.data.coloring q)
          hi
        all_goals omega
      rw [hcEq]
      exact second.replacementOneUncolored middleIndex
    replacementStable := by
      intro i
      let middleIndex := first.rungAgreement.symm ▸ i
      have treeBridge :
          first.replacementETT.series.data.tree middleIndex.succ.castSucc =
            ett.series.data.tree i.succ.castSucc := by
        rw [firstSeriesEq]
        exact (eq_of_heq (projectTree first.rungAgreement.symm
          first.replacementSeries i)).trans (first.ladderTreesAgree i)
      have storedBridge :
          first.replacementETT.series.data.stored middleIndex.succ =
            ett.series.data.stored i.succ := by
        have middleSucc : middleIndex.succ = first.rungAgreement.symm ▸ i.succ := by
          exact succCast first.rungAgreement.symm i
        rw [middleSucc]
        rw [firstSeriesEq]
        exact (eq_of_heq (projectStored first.rungAgreement.symm
          first.replacementSeries i.succ)).trans
          (first.storedColorsAgree i.succ)
      have middleColorBridge :
          first.replacementETT.series.data.coloring middleIndex.succ =
            first.replacementSeries.data.coloring i.succ := by
        have middleSucc : middleIndex.succ = first.rungAgreement.symm ▸ i.succ := by
          exact succCast first.rungAgreement.symm i
        rw [middleSucc]
        rw [firstSeriesEq]
        exact eq_of_heq (projectColoring first.rungAgreement.symm
          first.replacementSeries i.succ)
      have storedColorBridge :
          TashkinovStoredColors first.replacementETT.series.data middleIndex.succ =
            TashkinovStoredColors ett.series.data i.succ := by
        have raw : ∀ j : Fin (first.replacementETT.rounds + 1),
            first.replacementETT.series.data.stored j =
              ett.series.data.stored (first.rungAgreement ▸ j) := by
          intro j
          rw [firstSeriesEq]
          have p := projectStored first.rungAgreement.symm
            first.replacementSeries (first.rungAgreement ▸ j)
          have pj := eq_of_heq p
          rw [castBackPlus first.rungAgreement.symm j] at pj
          exact pj.trans (first.storedColorsAgree (first.rungAgreement ▸ j))
        have missing :
            TreeMissingColors
                (first.replacementETT.series.data.coloring middleIndex.succ)
                (first.replacementETT.series.data.tree middleIndex.succ.castSucc) =
              TreeMissingColors (ett.series.data.coloring i.succ)
                (ett.series.data.tree i.succ.castSucc) := by
          rw [middleColorBridge, treeBridge]
          ext c
          simp only [TreeMissingColors, Finset.mem_biUnion]
          constructor
          · rintro ⟨v, hv, hc⟩
            exact ⟨v, hv, by
              rw [← (first.replacementStable i).2 v hv]
              exact hc⟩
          · rintro ⟨v, hv, hc⟩
            exact ⟨v, hv, by
              rw [(first.replacementStable i).2 v hv]
              exact hc⟩
        unfold TashkinovStoredColors
        simp [Fin.succ, Nat.succ_ne_zero]
        ext c
        simp only [Finset.mem_sdiff, Finset.mem_biUnion]
        constructor
        · rintro ⟨⟨j, hj, hc⟩, hn⟩
          refine ⟨⟨first.rungAgreement ▸ j, by simp, ?_⟩, ?_⟩
          · rw [← raw j]
            have castJ := castValuePlus first.rungAgreement j
            have castI := castValue first.rungAgreement.symm i
            simpa [middleIndex, castJ, castI] using hc
          · have hn' : c ∉ TreeMissingColors
                (ett.series.data.coloring i.succ)
                (ett.series.data.tree i.succ.castSucc) := by
              rw [← missing]
              exact hn
            simpa [Fin.succ] using hn'
        · rintro ⟨⟨j, hj, hc⟩, hn⟩
          refine ⟨⟨first.rungAgreement.symm ▸ j, by simp, ?_⟩, ?_⟩
          · have rr := raw (first.rungAgreement.symm ▸ j)
            rw [rr]
            have castJ := castValuePlus first.rungAgreement.symm j
            have castI := castValue first.rungAgreement.symm i
            rw [castBackPlus first.rungAgreement j]
            simpa [middleIndex, castJ, castI] using hc
          · have hn' : c ∉ TreeMissingColors
                (first.replacementETT.series.data.coloring middleIndex.succ)
                (first.replacementETT.series.data.tree middleIndex.succ.castSucc) := by
              rw [missing]
              exact hn
            simpa [Fin.succ] using hn'
      have secondStable : StableColoring
          (ett.series.data.tree i.succ.castSucc)
          (TashkinovStoredColors ett.series.data i.succ)
          (first.replacementSeries.data.coloring i.succ)
          (second.replacementSeries.data.coloring middleIndex.succ) := by
        have h := second.replacementStable middleIndex
        rw [treeBridge, storedColorBridge, middleColorBridge] at h
        exact h
      have originalGood : IsProperEdgeColoring G (ett.series.data.coloring i.succ) ∧
          IsOneEdgeUncolored (ett.series.data.coloring i.succ) e0 := by
        have step := ett.series.certified i.succ
        generalize stepIndex : i.succ = z at step
        cases step <;> simp_all [stepIndex] <;> aesop
          <;> first
            | exact MaximumDefectiveChoice.selectedProper (by assumption)
            | exact MaximumDefectiveChoice.selectedOneUncolored (by assumption)
            | omega
      have middleGood : IsProperEdgeColoring G
          (first.replacementSeries.data.coloring i.succ) ∧
          IsOneEdgeUncolored (first.replacementSeries.data.coloring i.succ) e0 :=
        ⟨first.replacementProper i.succ, first.replacementOneUncolored i.succ⟩
      have finalGood : IsProperEdgeColoring G
          (second.replacementSeries.data.coloring middleIndex.succ) ∧
          IsOneEdgeUncolored (second.replacementSeries.data.coloring middleIndex.succ) e0 :=
        ⟨second.replacementProper middleIndex.succ,
          second.replacementOneUncolored middleIndex.succ⟩
      have finalColor : transported.data.coloring i.succ =
          second.replacementSeries.data.coloring middleIndex.succ := by
        have hc := projectColoring first.rungAgreement
          second.replacementSeries middleIndex.succ
        have hi : i.succ = first.rungAgreement ▸ middleIndex.succ := by
          calc
            i.succ = first.rungAgreement ▸
                (first.rungAgreement.symm ▸ i.succ) :=
              (castBackPlus first.rungAgreement i.succ).symm
            _ = first.rungAgreement ▸ middleIndex.succ := by
              rw [succCast]
        convert (eq_of_heq hc) using 1
        simpa [transported, middleIndex] using congrArg
          (fun q => transported.data.coloring q) hi
      rw [finalColor]
      exact (sc2 G e0 (ett.series.data.tree i.succ.castSucc)
        (TashkinovStoredColors ett.series.data i.succ)).trans
        (x := ⟨ett.series.data.coloring i.succ, originalGood⟩)
        (y := ⟨first.replacementSeries.data.coloring i.succ, middleGood⟩)
        (z := ⟨second.replacementSeries.data.coloring middleIndex.succ, finalGood⟩)
        (first.replacementStable i) secondStable }
  exact ⟨composite, rfl, seriesTransport, by rfl⟩
