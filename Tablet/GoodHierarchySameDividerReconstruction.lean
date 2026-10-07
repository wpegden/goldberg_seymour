import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.TashkinovHierarchy
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix

-- [TABLET NODE: GoodHierarchySameDividerReconstruction]
theorem GoodHierarchySameDividerReconstruction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (J U : TreeSequence G e0)
    (corrJ : CorrespondingExtendedTashkinovTree G k e0 ett sigma J)
    (baseJ : HierarchyBase corrJ.replacementETT sigma)
    (KJ : TashkinovHierarchy corrJ.replacementETT baseJ)
    (corrU : CorrespondingExtendedTashkinovTree G k e0 ett sigma U)
    (baseU : HierarchyBase corrU.replacementETT sigma)
    (hcore : baseU.core = baseJ.core)
    (hJU : TashkinovAugmentationSequence sigma J U) :
    ∃ KU : TashkinovHierarchy corrU.replacementETT baseU,
      ∃ hcount : KU.dividerCount = KJ.dividerCount,
        (∀ j : Fin (KU.dividerCount + 1),
          let jo : Fin (KJ.dividerCount + 1) :=
            Fin.cast (congrArg (fun n : ℕ => n + 1) hcount) j
          KU.stage j.castSucc = KJ.stage jo.castSucc ∧
            HierarchyStarredStage KU j = HierarchyStarredStage KJ jo ∧
            HierarchyStoredColorsAt KU j =
              HierarchyStoredColorsAt KJ jo ∧
            HierarchyStageMissingColors KU j =
              HierarchyStageMissingColors KJ jo) ∧
        (∀ i : Fin KU.dividerCount,
          (KU.dividerPosition i).val =
            (KJ.dividerPosition (Fin.cast hcount i)).val) := by
-- BODY
  classical
  rcases corrJ with ⟨replacementInputJ, replacementSeriesJ, replacementETTJ,
    rungAgreementJ, seriesPresentationJ, finalGeneratingColoringJ,
    ladderTreesAgreeJ, storedColorsAgreeJ, connectingEdgesAgreeJ,
    extensionKindsAgreeJ, replacementProperJ, replacementOneUncoloredJ,
    replacementStableJ⟩
  cases replacementETTJ with
  | mk roundsJ roundsPositiveJ replacementDataJ aboveJ strictJ belowJ generatingJ =>
    cases rungAgreementJ
    have seriesSameJ : replacementDataJ = replacementSeriesJ :=
      eq_of_heq seriesPresentationJ
    cases seriesSameJ
    rcases corrU with ⟨replacementInputU, replacementSeriesU, replacementETTU,
      rungAgreementU, seriesPresentationU, finalGeneratingColoringU,
      ladderTreesAgreeU, storedColorsAgreeU, connectingEdgesAgreeU,
      extensionKindsAgreeU, replacementProperU, replacementOneUncoloredU,
      replacementStableU⟩
    cases replacementETTU with
    | mk roundsU roundsPositiveU replacementDataU aboveU strictU belowU generatingU =>
      cases rungAgreementU
      have seriesSameU : replacementDataU = replacementSeriesU :=
        eq_of_heq seriesPresentationU
      cases seriesSameU
      have segmentJU : TreeSequenceInitialSegment J U :=
        TashkinovAugmentationSequenceInitialSegment sigma J U hJU
      have segmentTrans {A B C : TreeSequence G e0}
          (hAB : TreeSequenceInitialSegment A B)
          (hBC : TreeSequenceInitialSegment B C) :
          TreeSequenceInitialSegment A C := by
        rcases hAB with ⟨hab, hvab, heab⟩
        rcases hBC with ⟨hbc, hvbc, hebc⟩
        refine ⟨Nat.le_trans hab hbc, ?_, ?_⟩
        · intro i
          have hmid := hvbc (Fin.castLE (Nat.succ_le_succ hab) i)
          simpa using hmid.trans (hvab i)
        · intro i
          have hmid := hebc (Fin.castLE hab i)
          simpa using hmid.trans (heab i)
      let terminalIndex : Fin ett.rounds :=
        ⟨ett.rounds - 1,
          Nat.sub_lt (Nat.zero_lt_of_lt ett.roundsPositive) (by omega)⟩
      have terminalIndexEq : terminalIndex.succ.castSucc =
          (Fin.last ett.rounds).castSucc := by
        apply Fin.ext
        simp [terminalIndex, Nat.sub_add_cancel ett.roundsPositive]
      have finalTreeEq : replacementSeriesU.data.tree
            (Fin.last ett.rounds).castSucc =
          replacementSeriesJ.data.tree (Fin.last ett.rounds).castSucc := by
        rw [← terminalIndexEq]
        exact (ladderTreesAgreeU terminalIndex).trans
          (ladderTreesAgreeJ terminalIndex).symm
      have storedEntryEq (i : Fin (ett.rounds + 1)) :
          replacementSeriesU.data.stored i = replacementSeriesJ.data.stored i :=
        (storedColorsAgreeU i).trans (storedColorsAgreeJ i).symm
      have finalMissingEq : TreeMissingColors
            (replacementSeriesU.data.coloring (Fin.last ett.rounds))
            (replacementSeriesU.data.tree (Fin.last ett.rounds).castSucc) =
          TreeMissingColors
            (replacementSeriesJ.data.coloring (Fin.last ett.rounds))
            (replacementSeriesJ.data.tree (Fin.last ett.rounds).castSucc) := by
        rw [← finalGeneratingColoringU, ← finalGeneratingColoringJ, finalTreeEq]
      have terminalStoredEq : TashkinovStoredColors replacementSeriesU.data
            (Fin.last ett.rounds) =
          TashkinovStoredColors replacementSeriesJ.data
            (Fin.last ett.rounds) := by
        unfold TashkinovStoredColors
        have hnonzero : (Fin.last ett.rounds).val ≠ 0 := by
          simpa using Nat.ne_of_gt (Nat.zero_lt_of_lt ett.roundsPositive)
        simp only [if_neg hnonzero]
        ext c
        simp only [Finset.mem_sdiff, Finset.mem_biUnion]
        constructor
        · rintro ⟨⟨i, hi, hc⟩, hn⟩
          refine ⟨⟨i, hi, ?_⟩, ?_⟩
          · by_cases hle : i.val ≤ (Fin.last ett.rounds).val
            · simp only [if_pos hle] at hc ⊢
              simpa [storedEntryEq i] using hc
            · simp only [if_neg hle] at hc ⊢
              exact hc
          · rwa [finalMissingEq] at hn
        · rintro ⟨⟨i, hi, hc⟩, hn⟩
          refine ⟨⟨i, hi, ?_⟩, ?_⟩
          · by_cases hle : i.val ≤ (Fin.last ett.rounds).val
            · simp only [if_pos hle] at hc ⊢
              simpa [storedEntryEq i] using hc
            · simp only [if_neg hle] at hc ⊢
              exact hc
          · rwa [finalMissingEq]
      let kuStage : Fin (KJ.dividerCount + 2) → TreeSequence G e0 :=
        fun j => if j.val = KJ.dividerCount + 1 then U
          else KJ.stage ⟨j.val, by omega⟩
      have kuStageOld (j : Fin (KJ.dividerCount + 1)) :
          kuStage j.castSucc = KJ.stage j.castSucc := by
        have hj : j.castSucc.val ≠ KJ.dividerCount + 1 :=
          Nat.ne_of_lt j.isLt
        simp only [kuStage, if_neg hj]
      have kuStageLast :
          kuStage (Fin.last (KJ.dividerCount + 1)) = U := by
        simp [kuStage]
      have kuStageAt (j : Fin (KJ.dividerCount + 2))
          (hj : j.val ≤ KJ.dividerCount) :
          kuStage j = KJ.stage ⟨j.val, by omega⟩ := by
        simp only [kuStage]
        split <;> rename_i hs
        · omega
        · rfl
      have kuNested : ∀ j : Fin (KJ.dividerCount + 1),
          TreeSequenceInitialSegment (kuStage j.castSucc) (kuStage j.succ) := by
        intro j
        by_cases hj : j.val = KJ.dividerCount
        · have hlast : j = Fin.last KJ.dividerCount := Fin.ext (by simpa using hj)
          rw [hlast, kuStageOld]
          have hsucc : (Fin.last KJ.dividerCount).succ =
              Fin.last (KJ.dividerCount + 1) := rfl
          rw [hsucc, kuStageLast]
          have oldLast := KJ.nested (Fin.last KJ.dividerCount)
          rw [hsucc, KJ.terminalStage] at oldLast
          exact segmentTrans oldLast segmentJU
        · have hjlt : j.val < KJ.dividerCount := by omega
          have hcast : j.castSucc.val ≤ KJ.dividerCount := by
            simpa using Nat.le_of_lt_succ j.isLt
          have hsuccle : j.succ.val ≤ KJ.dividerCount := by
            change j.val + 1 ≤ KJ.dividerCount
            omega
          rw [kuStageAt j.castSucc hcast, kuStageAt j.succ hsuccle]
          have hold := KJ.nested ⟨j.val, by omega⟩
          convert hold using 1 <;> apply congrArg KJ.stage <;>
            apply Fin.ext <;> rfl
      have kuStrict : ∀ j : Fin (KJ.dividerCount + 1),
          (kuStage j.castSucc).length < (kuStage j.succ).length := by
        intro j
        by_cases hj : j.val = KJ.dividerCount
        · have hlast : j = Fin.last KJ.dividerCount := Fin.ext (by simpa using hj)
          rw [hlast, kuStageOld]
          have hsucc : (Fin.last KJ.dividerCount).succ =
              Fin.last (KJ.dividerCount + 1) := rfl
          rw [hsucc, kuStageLast]
          have hold := KJ.strict (Fin.last KJ.dividerCount)
          rw [hsucc, KJ.terminalStage] at hold
          exact lt_of_lt_of_le hold segmentJU.1
        · have hjlt : j.val < KJ.dividerCount := by omega
          have hcast : j.castSucc.val ≤ KJ.dividerCount := by
            simpa using Nat.le_of_lt_succ j.isLt
          have hsuccle : j.succ.val ≤ KJ.dividerCount := by
            change j.val + 1 ≤ KJ.dividerCount
            omega
          rw [kuStageAt j.castSucc hcast, kuStageAt j.succ hsuccle]
          have hold := KJ.strict ⟨j.val, by omega⟩
          convert hold using 1 <;> apply congrArg TreeSequence.length <;>
            apply congrArg KJ.stage <;> apply Fin.ext <;> rfl
      let kuDividerPosition (i : Fin KJ.dividerCount) : Fin (U.length + 1) :=
        ⟨(KJ.dividerPosition i).val,
          lt_of_lt_of_le (KJ.dividerPosition i).isLt
            (Nat.succ_le_succ segmentJU.1)⟩
      let KU : TashkinovHierarchy
          { rounds := ett.rounds
            roundsPositive := roundsPositiveU
            series := replacementSeriesU
            abovePenultimate := aboveU
            strictAbovePenultimate := strictU
            belowFinal := belowU
            generatingColoring := generatingU }
          baseU :=
        { dividerCount := KJ.dividerCount
          stage := kuStage
          baseStage := by
            calc
              kuStage 0 = KJ.stage 0 := by
                simpa using kuStageOld (0 : Fin (KJ.dividerCount + 1))
              _ = replacementSeriesJ.data.tree
                    (Fin.last ett.rounds).castSucc := KJ.baseStage
              _ = replacementSeriesU.data.tree
                    (Fin.last ett.rounds).castSucc := finalTreeEq.symm
          terminalStage := kuStageLast
          nested := kuNested
          strict := kuStrict
          dividerPosition := kuDividerPosition
          dividerPositive := by intro i; exact KJ.dividerPositive i
          dividerIncreasing := by
            intro i j hij
            exact KJ.dividerIncreasing i j hij
          dividerStage := by
            intro i
            have hstageIndex : (i.val + 1) ≤ KJ.dividerCount :=
              Nat.succ_le_of_lt i.isLt
            have hstage : kuStage ⟨i.val + 1, by omega⟩ =
                KJ.stage ⟨i.val + 1, by omega⟩ :=
              kuStageAt ⟨i.val + 1, by omega⟩ hstageIndex
            have hposJ : (KJ.dividerPosition i).val ≤ J.length :=
              Nat.le_of_lt_succ (KJ.dividerPosition i).isLt
            have hposU : (KJ.dividerPosition i).val ≤ U.length :=
              le_trans hposJ segmentJU.1
            have prefixEq : TreeSequencePrefix U (KJ.dividerPosition i).val
                  (KJ.dividerPositive i) hposU =
                TreeSequencePrefix J (KJ.dividerPosition i).val
                  (KJ.dividerPositive i) hposJ := by
              rw [TreeSequencePrefix, TreeSequencePrefix]
              congr
              · funext x
                have hv := segmentJU.2.1
                  (Fin.castLE (Nat.succ_le_succ hposJ) x)
                simpa using hv
              · funext x
                have he := segmentJU.2.2 (Fin.castLE hposJ x)
                simpa using he
            rw [prefixEq]
            rw [hstage]
            simpa [kuDividerPosition] using KJ.dividerStage i
          coreInsideFirst := by
            by_cases hd : KJ.dividerCount = 0
            · have hstage : kuStage ⟨1, by omega⟩ = U := by
                simp [kuStage, hd]
              rw [hstage]
              have hold := KJ.coreInsideFirst
              have holdStage : KJ.stage ⟨1, by omega⟩ = J := by
                convert KJ.terminalStage using 1 <;> apply congrArg KJ.stage <;>
                  apply Fin.ext <;> simp [hd]
              rw [holdStage] at hold
              rw [hcore]
              exact segmentTrans hold segmentJU
            · have hstage : kuStage ⟨1, by omega⟩ = KJ.stage ⟨1, by omega⟩ :=
                kuStageAt ⟨1, by omega⟩ (Nat.one_le_iff_ne_zero.mpr hd)
              rw [hstage, hcore]
              exact KJ.coreInsideFirst }
      have stageEq (j : Fin (KJ.dividerCount + 1)) :
          KU.stage j.castSucc = KJ.stage j.castSucc := kuStageOld j
      have starredEq (j : Fin (KJ.dividerCount + 1)) :
          HierarchyStarredStage KU j = HierarchyStarredStage KJ j := by
        refine Fin.cases ?_ (fun i => ?_) j
        · simpa [HierarchyStarredStage, KU] using hcore
        · change KU.stage i.succ.castSucc = KJ.stage i.succ.castSucc
          exact stageEq i.succ
      have storedEq (j : Fin (KJ.dividerCount + 1)) :
          HierarchyStoredColorsAt KU j = HierarchyStoredColorsAt KJ j := by
        unfold HierarchyStoredColorsAt
        change TashkinovStoredColors replacementSeriesU.data
              (Fin.last ett.rounds) \
            TreeMissingColors sigma (HierarchyStarredStage KU j) =
          TashkinovStoredColors replacementSeriesJ.data
              (Fin.last ett.rounds) \
            TreeMissingColors sigma (HierarchyStarredStage KJ j)
        rw [terminalStoredEq, starredEq]
      have missingEq (j : Fin (KJ.dividerCount + 1)) :
          HierarchyStageMissingColors KU j =
            HierarchyStageMissingColors KJ j := by
        unfold HierarchyStageMissingColors
        refine Fin.cases ?_ (fun i => ?_) j
        · change TreeMissingColors sigma
              (replacementSeriesU.data.tree (Fin.last ett.rounds).castSucc) =
            TreeMissingColors sigma
              (replacementSeriesJ.data.tree (Fin.last ett.rounds).castSucc)
          rw [finalTreeEq]
        · change TreeMissingColors sigma (KU.stage i.succ.castSucc) =
            TreeMissingColors sigma (KJ.stage i.succ.castSucc)
          exact congrArg (TreeMissingColors sigma) (stageEq i.succ)
      refine ⟨KU, rfl, ?_, ?_⟩
      · intro j
        exact ⟨stageEq j, starredEq j, storedEq j, missingEq j⟩
      · intro i
        rfl
