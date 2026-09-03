import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyBase
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchySegmentColors
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.MaximumProperty
import Tablet.MissingColors
import Tablet.OrderedTreeUnion
import Tablet.TashkinovHierarchy
import Tablet.TreeSequenceInitialSegment

-- [TABLET NODE: GoodHierarchyTerminalPrefixRepackage]
theorem GoodHierarchyTerminalPrefixRepackage {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base)
    (good : GoodHierarchy H)
    (B : TreeSequence G e0)
    (hAB : TreeSequenceInitialSegment
      (HierarchyStarredStage H (Fin.last H.dividerCount)) B)
    (hABstrict :
      (HierarchyStarredStage H (Fin.last H.dividerCount)).length < B.length)
    (hBT : TreeSequenceInitialSegment B T) :
    ∃ ettB : ExtendedTashkinovTree G k e0 input B generating,
      MaximumProperty ettB ∧
      ettB.rounds = ett.rounds ∧ HEq ettB.series ett.series ∧
      ∃ baseB : HierarchyBase ettB phi,
        baseB.core = base.core ∧
        baseB.closure = base.closure ∧
        baseB.supportPosition.val = base.supportPosition.val ∧
        ∃ HB : TashkinovHierarchy ettB baseB,
          ∃ hcount : HB.dividerCount = H.dividerCount,
            (∀ j : Fin (HB.dividerCount + 1),
              let jo : Fin (H.dividerCount + 1) :=
                Fin.cast (congrArg (fun n : ℕ => n + 1) hcount) j
              HB.stage j.castSucc = H.stage jo.castSucc ∧
                HierarchyStarredStage HB j = HierarchyStarredStage H jo) ∧
            (∀ i : Fin HB.dividerCount,
              (HB.dividerPosition i).val =
                (H.dividerPosition (Fin.cast hcount i)).val) ∧
            ∃ goodB : GoodHierarchy HB,
              ∀ j : Fin (HB.dividerCount + 1),
                let jo : Fin (H.dividerCount + 1) :=
                  Fin.cast (congrArg (fun n : ℕ => n + 1) hcount) j
                HierarchyStoredColorsAt HB j = HierarchyStoredColorsAt H jo ∧
                  HierarchyStageMissingColors HB j =
                    HierarchyStageMissingColors H jo ∧
                  ∀ eta : Fin k,
                    goodB.gamma j eta = good.gamma jo eta ∧
                      HierarchySegmentColors HB j eta ⊆
                        HierarchySegmentColors H jo eta := by
-- BODY
  classical
  have segmentRefl (A : TreeSequence G e0) :
      TreeSequenceInitialSegment A A :=
    ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
  have segmentTrans {A B C : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B)
      (hBC : TreeSequenceInitialSegment B C) :
      TreeSequenceInitialSegment A C := by
    rcases hAB with ⟨hab, hvab, heab⟩
    rcases hBC with ⟨hbc, hvbc, hebc⟩
    refine ⟨le_trans hab hbc, ?_, ?_⟩
    · intro i
      have hmid := hvbc (Fin.castLE (Nat.succ_le_succ hab) i)
      simpa using hmid.trans (hvab i)
    · intro i
      have hmid := hebc (Fin.castLE hab i)
      simpa using hmid.trans (heab i)
  have stageSegment : ∀ (a d : ℕ)
      (hbound : a + d ≤ H.dividerCount + 1),
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
        (H.stage ⟨a + d, by omega⟩) := by
    intro a d
    induction d with
    | zero => intro h; simpa using segmentRefl (H.stage ⟨a, by omega⟩)
    | succ d ih =>
      intro h
      have hp := ih (by omega)
      have hn := H.nested ⟨a + d, by omega⟩
      have hn' : TreeSequenceInitialSegment
          (H.stage ⟨a+d, by omega⟩) (H.stage ⟨a+(d+1), by omega⟩) := by
        simpa [Nat.add_assoc] using hn
      exact segmentTrans hp hn'
  let lastStage : TreeSequence G e0 :=
    HierarchyStarredStage H (Fin.last H.dividerCount)
  have lastZero : H.dividerCount = 0 →
      lastStage = base.core := by
    intro h
    simpa [lastStage, HierarchyStarredStage, h, Fin.last] 
  have lastPositive : H.dividerCount ≠ 0 →
      lastStage = H.stage ⟨H.dividerCount, by omega⟩ := by
    intro h
    unfold lastStage HierarchyStarredStage
    obtain hzero | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ (Fin.last H.dividerCount)
    · have hz : H.dividerCount = 0 := by
        simpa using congrArg Fin.val hzero
      exact False.elim (h hz)
    · rw [hi]
      simp only [Fin.cases_succ]
      congr 1
      apply Fin.ext
      simpa using (congrArg Fin.val hi).symm
  have stageLastPositive : H.dividerCount ≠ 0 →
      H.stage (Fin.last H.dividerCount).castSucc = lastStage := by
    intro hp
    rw [lastPositive hp]
    apply congrArg H.stage
    apply Fin.ext
    simp
  have stageToLast : TreeSequenceInitialSegment
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) lastStage := by
    by_cases hq : H.dividerCount = 0
    · by_cases hk : ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE
      · obtain ⟨_, _, ⟨u⟩⟩ := base.parallel hk
        rw [lastZero hq]
        exact u.leftSegment
      · have hc : base.core = ett.series.data.tree (Fin.last ett.rounds).castSucc :=
          base.nonparallel hk
        rw [lastZero hq, hc]
        exact segmentRefl _
    · have hs := stageSegment 0 H.dividerCount (by omega)
      rw [lastPositive hq]
      rw [← H.baseStage]
      convert hs using 1 <;> apply congrArg H.stage <;> apply Fin.ext <;> simp <;> omega
  have lastToB : TreeSequenceInitialSegment lastStage B := hAB
  have firstToB := segmentTrans stageToLast lastToB
  have strictFirst :
      (ett.series.data.tree (Fin.last ett.rounds).castSucc).length < B.length := by
    have hlt : (ett.series.data.tree (Fin.last ett.rounds).castSucc).length ≤
        lastStage.length := stageToLast.1
    exact lt_of_le_of_lt hlt (by exact hABstrict)
  let ettB : ExtendedTashkinovTree G k e0 input B generating :=
    { rounds := ett.rounds
      roundsPositive := ett.roundsPositive
      series := ett.series
      abovePenultimate := firstToB
      strictAbovePenultimate := strictFirst
      belowFinal := segmentTrans hBT ett.belowFinal
      generatingColoring := ett.generatingColoring }
  have mpB : MaximumProperty ettB := by
    simpa [MaximumProperty, ettB] using hMP
  let baseB : HierarchyBase ettB phi :=
    { core := base.core
      closure := base.closure
      supportPosition := base.supportPosition
      supportPositive := base.supportPositive
      terminalMissingColors := by simpa [ettB] using base.terminalMissingColors
      parallel := by simpa [ettB] using base.parallel
      nonparallel := by simpa [ettB] using base.nonparallel }
  let hbStage : Fin (H.dividerCount + 2) → TreeSequence G e0 :=
    fun j => if j.val = H.dividerCount + 1 then B
      else H.stage ⟨j.val, by omega⟩
  have hbStageOld (j : Fin (H.dividerCount + 1)) :
      hbStage j.castSucc = H.stage j.castSucc := by
    by_cases hh : j.castSucc.val = H.dividerCount + 1
    · have hj : j.val = H.dividerCount + 1 := by simpa using hh
      omega
    · simp only [hbStage, if_neg hh]
  have hbStageLast : hbStage (Fin.last (H.dividerCount + 1)) = B := by
    have he : (Fin.last (H.dividerCount + 1)).val = H.dividerCount + 1 := by simp
    simp only [hbStage, if_pos he]
  have hbStageAt (j : Fin (H.dividerCount + 2)) (hj : j.val ≤ H.dividerCount) :
      hbStage j = H.stage ⟨j.val, by omega⟩ := by
    simp only [hbStage]
    split <;> rename_i hs
    · omega
    · rfl
  have hbNested : ∀ j : Fin (H.dividerCount + 1),
      TreeSequenceInitialSegment (hbStage j.castSucc) (hbStage j.succ) := by
    intro j
    by_cases hj : j.val = H.dividerCount
    · have hlast : j = Fin.last H.dividerCount := by
        apply Fin.ext
        simpa using hj
      rw [hlast]
      rw [hbStageOld (Fin.last H.dividerCount)]
      have hjs : (Fin.last H.dividerCount).succ = Fin.last (H.dividerCount + 1) := by rfl
      rw [hjs, hbStageLast]
      by_cases hc : H.dividerCount = 0
      · have hs0 : TreeSequenceInitialSegment (H.stage 0) lastStage := by
          simpa [H.baseStage] using stageToLast
        have hab : TreeSequenceInitialSegment lastStage B := by
          change TreeSequenceInitialSegment lastStage B at hAB
          exact hAB
        have hidx : H.stage (Fin.last H.dividerCount).castSucc = H.stage 0 := by
          congr 1
          apply Fin.ext
          simp [hc]
        rw [hidx]
        exact segmentTrans hs0 hab
      · rw [stageLastPositive hc]
        exact hAB
    · have hjlt : j.val < H.dividerCount := by omega
      have hsucc : j.val + 1 ≤ H.dividerCount := Nat.succ_le_of_lt hjlt
      rw [hbStageAt j.castSucc (Nat.le_of_lt_succ j.isLt),
        hbStageAt j.succ hsucc]
      have hn := H.nested ⟨j.val, by omega⟩
      convert hn using 1 <;> apply congrArg H.stage <;> apply Fin.ext <;> rfl
  have hbStrict : ∀ j : Fin (H.dividerCount + 1),
      (hbStage j.castSucc).length < (hbStage j.succ).length := by
    intro j
    by_cases hj : j.val = H.dividerCount
    · have hlast : j = Fin.last H.dividerCount := by
        apply Fin.ext
        simpa using hj
      rw [hlast]
      rw [hbStageOld (Fin.last H.dividerCount)]
      have hjs : (Fin.last H.dividerCount).succ = Fin.last (H.dividerCount + 1) := by rfl
      rw [hjs, hbStageLast]
      by_cases hc : H.dividerCount = 0
      · have hs0 : TreeSequenceInitialSegment (H.stage 0) lastStage := by
          simpa [H.baseStage] using stageToLast
        have hlen : lastStage.length < B.length := hABstrict
        have hidx : H.stage (Fin.last H.dividerCount).castSucc = H.stage 0 := by
          congr 1
          apply Fin.ext
          simp [hc]
        rw [hidx]
        exact lt_of_le_of_lt hs0.1 hlen
      · rw [stageLastPositive hc]
        exact hABstrict
    · have hjlt : j.val < H.dividerCount := by omega
      have hsucc : j.val + 1 ≤ H.dividerCount := Nat.succ_le_of_lt hjlt
      rw [hbStageAt j.castSucc (Nat.le_of_lt_succ j.isLt),
        hbStageAt j.succ hsucc]
      have hn := H.strict ⟨j.val, by omega⟩
      convert hn using 1 <;> apply congrArg TreeSequence.length <;>
        apply congrArg H.stage <;> apply Fin.ext <;> rfl
  let HB : TashkinovHierarchy ettB baseB :=
    { dividerCount := H.dividerCount
      stage := hbStage
      baseStage := by
        rw [show hbStage 0 = H.stage 0 by simp [hbStage]]
        simpa [ettB] using H.baseStage
      terminalStage := by simpa [hbStage, ettB] using hbStageLast.trans H.terminalStage
      nested := hbNested
      strict := hbStrict
      dividerPosition := fun i => ⟨(H.dividerPosition i).val, by
        have hd := H.dividerStage i
        have hi : i.val + 1 ≤ H.dividerCount := Nat.succ_le_of_lt i.isLt
        have hlastB : TreeSequenceInitialSegment
            (H.stage ⟨H.dividerCount, by omega⟩) B := by
          rw [← lastPositive (by omega)]
          exact lastToB
        have hseg := stageSegment (i.val + 1)
          (H.dividerCount - (i.val + 1)) (by omega)
        have heq : i.val + 1 + (H.dividerCount - (i.val + 1)) = H.dividerCount :=
          Nat.add_sub_of_le hi
        have hseg' : TreeSequenceInitialSegment
            (H.stage ⟨i.val + 1, by omega⟩)
            (H.stage ⟨H.dividerCount, by omega⟩) := by
          convert hseg using 1
          · congr 1
            apply Fin.ext
            exact heq.symm
        have hp := (segmentTrans hseg' hlastB).1
        have he := congrArg TreeSequence.length hd
        have he' : (H.stage ⟨i.val + 1, by omega⟩).length =
            (H.dividerPosition i).val := by
          rw [TreeSequencePrefix] at he
          simpa using he
        exact Nat.lt_succ_of_le (by
          rw [← he']
          exact hp)⟩
      dividerPositive := by intro i; exact H.dividerPositive i
      dividerIncreasing := by intro i j hij; exact H.dividerIncreasing i j hij
      dividerStage := by
        intro i
        have hi : i.val + 1 ≤ H.dividerCount := Nat.succ_le_of_lt i.isLt
        have he : hbStage ⟨i.val + 1, by omega⟩ =
            H.stage ⟨i.val + 1, by omega⟩ := by
          exact hbStageAt ⟨i.val + 1, by omega⟩ hi
        rw [he]
        have hpos : (H.dividerPosition i).val ≤ B.length := by
          have hs := stageSegment (i.val + 1)
            (H.dividerCount - (i.val + 1)) (by omega)
          have hs' : TreeSequenceInitialSegment
              (H.stage ⟨i.val + 1, by omega⟩)
              (H.stage ⟨H.dividerCount, by omega⟩) := by
            convert hs using 1
            apply congrArg H.stage
            apply Fin.ext
            exact (Nat.add_sub_of_le hi).symm
          have hab : TreeSequenceInitialSegment
              (H.stage ⟨H.dividerCount, by omega⟩) B := by
            rw [← lastPositive (by omega)]
            exact hAB
          have hsB := (segmentTrans hs' hab).1
          have hlen := congrArg TreeSequence.length (H.dividerStage i)
          rw [TreeSequencePrefix] at hlen
          have hval : (H.stage ⟨i.val + 1, by omega⟩).length =
              (H.dividerPosition i).val := by simpa using hlen
          omega
        have hpref : TreeSequencePrefix B (H.dividerPosition i).val
            (H.dividerPositive i) hpos =
            TreeSequencePrefix T (H.dividerPosition i).val
              (H.dividerPositive i) (by omega) := by
          rw [TreeSequencePrefix, TreeSequencePrefix]
          congr
          · funext x
            have hv := hBT.2.1 (Fin.castLE (Nat.succ_le_succ hpos) x)
            simpa using hv.symm
          · funext x
            have heq := hBT.2.2 (Fin.castLE hpos x)
            simpa using heq.symm
        rw [hpref]
        simpa [ettB] using H.dividerStage i
      coreInsideFirst := by
        by_cases hc : H.dividerCount = 0
        · have he : hbStage ⟨1, by omega⟩ = B := by simp [hbStage, hc]
          rw [he]
          have hab : TreeSequenceInitialSegment base.core B := by
            have hh := hAB
            have hs : HierarchyStarredStage H (Fin.last H.dividerCount) = base.core := by
              simpa [lastStage] using lastZero hc
            rw [hs] at hh
            exact hh
          simpa [baseB] using hab
        · have he : hbStage ⟨1, by omega⟩ = H.stage ⟨1, by omega⟩ :=
          hbStageAt ⟨1, by omega⟩ (Nat.one_le_iff_ne_zero.mpr hc)
          rw [he]
          simpa [baseB] using H.coreInsideFirst }
  have stageOrd (i : Fin H.dividerCount) :
      HB.stage i.castSucc.succ = H.stage i.castSucc.succ := by
    change hbStage i.castSucc.succ = H.stage i.castSucc.succ
    exact hbStageAt i.castSucc.succ (Nat.succ_le_of_lt i.isLt)
  have stageOrdNext (i : Fin H.dividerCount) :
      HB.stage i.succ.castSucc = H.stage i.succ.castSucc := by
    have hindex : i.succ.castSucc = i.castSucc.succ := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact stageOrd i
  have stageEq (j : Fin (H.dividerCount + 2)) :
      HB.stage j = if j.val = H.dividerCount + 1 then B
        else H.stage ⟨j.val, by omega⟩ := rfl
  have starredEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStarredStage HB j = HierarchyStarredStage H j := by
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [HierarchyStarredStage, baseB]
    · change HB.stage i.succ.castSucc = H.stage i.succ.castSucc
      exact stageOrd i
  have storedEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStoredColorsAt HB j = HierarchyStoredColorsAt H j := by
    unfold HierarchyStoredColorsAt
    rw [starredEq]
  have beforeFirstMissing {A B : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B) (eta : Fin k)
      (i : Fin (A.length + 1)) (hiEnd : i.val < A.length)
      (hi : i.val < (HierarchyFirstMissingPosition phi A eta).val) :
      let iB : Fin (B.length + 1) :=
        Fin.castLE (Nat.succ_le_succ hAB.1) i
      iB.val < (HierarchyFirstMissingPosition phi B eta).val := by
    let candidatesA : Finset (Fin (A.length + 1)) :=
      Finset.univ.filter fun x => eta ∈ MissingColors G phi (A.vertex x)
    let candidatesB : Finset (Fin (B.length + 1)) :=
      Finset.univ.filter fun x => eta ∈ MissingColors G phi (B.vertex x)
    change i.val < (if h : candidatesA.Nonempty then candidatesA.min' h
      else Fin.last A.length).val at hi
    change (Fin.castLE (Nat.succ_le_succ hAB.1) i).val <
      (if h : candidatesB.Nonempty then candidatesB.min' h
      else Fin.last B.length).val
    by_cases hB : candidatesB.Nonempty
    · rw [dif_pos hB]
      by_contra hnot
      have hle : (candidatesB.min' hB).val ≤ i.val := by simpa using hnot
      let ia : Fin (A.length + 1) := ⟨(candidatesB.min' hB).val, by omega⟩
      have hmemB := Finset.min'_mem candidatesB hB
      have hmissingB := (Finset.mem_filter.mp hmemB).2
      have hcast : Fin.castLE (Nat.succ_le_succ hAB.1) ia =
          candidatesB.min' hB := Fin.ext rfl
      have hmissingA : eta ∈ MissingColors G phi (A.vertex ia) := by
        rw [← hAB.2.1 ia, hcast]
        exact hmissingB
      have hmemA : ia ∈ candidatesA :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmissingA⟩
      by_cases hA : candidatesA.Nonempty
      · rw [dif_pos hA] at hi
        have hminA := Finset.min'_le candidatesA ia hmemA
        change (candidatesA.min' hA).val ≤ ia.val at hminA
        dsimp [ia] at hminA
        omega
      · exact hA ⟨ia, hmemA⟩
    · rw [dif_neg hB]
      simpa using lt_of_lt_of_le hiEnd hAB.1
  have missingEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStageMissingColors HB j = HierarchyStageMissingColors H j := by
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [HierarchyStageMissingColors, ettB]
    · change TreeMissingColors phi (HB.stage i.succ.castSucc) =
        TreeMissingColors phi (H.stage i.succ.castSucc)
      rw [stageOrdNext i]
  have segmentSubset (j : Fin (H.dividerCount + 1)) (eta : Fin k) :
      HierarchySegmentColors HB j eta ⊆ HierarchySegmentColors H j eta := by
    intro c hc
    unfold HierarchySegmentColors at hc ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    rcases hc with ⟨x, hafter, hbefore, hcolor⟩
    have hnext : TreeSequenceInitialSegment
        (HB.stage j.succ) (H.stage j.succ) := by
      by_cases hj : j.val = H.dividerCount
      · have hlast : j = Fin.last H.dividerCount := by
          apply Fin.ext
          simpa using hj
        rw [hlast]
        have hjs : (Fin.last H.dividerCount).succ =
            Fin.last (H.dividerCount + 1) := by rfl
        rw [hjs, HB.terminalStage, H.terminalStage]
        exact hBT
      · have hjlt : j.val < H.dividerCount := by omega
        change TreeSequenceInitialSegment (hbStage j.succ) (H.stage j.succ)
        rw [hbStageAt j.succ (Nat.succ_le_of_lt hjlt)]
        exact segmentRefl _
    have hstageB : TreeSequenceInitialSegment (HB.stage j.succ) B := by
      by_cases hj : j.val = H.dividerCount
      · have hlast : j = Fin.last H.dividerCount := by
          apply Fin.ext
          simpa using hj
        rw [hlast]
        have hjs : (Fin.last H.dividerCount).succ =
            Fin.last (H.dividerCount + 1) := by rfl
        rw [hjs, HB.terminalStage]
        exact segmentRefl _
      · have hjlt : j.val < H.dividerCount := by omega
        change TreeSequenceInitialSegment (hbStage j.succ) B
        rw [hbStageAt j.succ (Nat.succ_le_of_lt hjlt)]
        have hs := stageSegment (j.val + 1)
          (H.dividerCount - (j.val + 1)) (by omega)
        rw [show (⟨j.val + 1 + (H.dividerCount - (j.val + 1)), by omega⟩ :
          Fin (H.dividerCount + 2)) = ⟨H.dividerCount, by omega⟩ by
            apply Fin.ext
            simpa using Nat.add_sub_of_le (Nat.succ_le_of_lt hjlt)] at hs
        have hs' : TreeSequenceInitialSegment
            (H.stage ⟨j.val + 1, by omega⟩)
            (H.stage ⟨H.dividerCount, by omega⟩) := by
          exact hs
        have hab : TreeSequenceInitialSegment
            (H.stage ⟨H.dividerCount, by omega⟩) B := by
          rw [← lastPositive (by omega)]
          exact hAB
        exact segmentTrans hs' hab
    let xold : Fin (H.stage j.succ).length :=
      Fin.castLE hnext.1 x
    let xB : Fin (B.length + 1) := Fin.castLE
      (Nat.succ_le_succ hstageB.1) ⟨x.val, by omega⟩
    refine ⟨xold, ?_, ?_, ?_⟩
    · rw [← starredEq j]
      simpa [xold] using hafter
    · apply lt_min
      · have hm := beforeFirstMissing hBT eta xB (by dsimp [xB]; omega)
          (by simpa [xB] using (lt_min_iff.mp hbefore).1)
        simpa [xold, xB] using hm
      · exact lt_of_lt_of_le (lt_min_iff.mp hbefore).2 hnext.1
    · change phi ((H.stage j.succ).edge (Fin.castLE hnext.1 x)) = some c
      rw [hnext.2.2 x]
      exact hcolor
  let goodB : GoodHierarchy HB :=
    { gamma := good.gamma
      twoColors := by
        intro j eta hmem
        apply good.twoColors j eta
        rw [← storedEq j]
        exact hmem
      avoidance := by
        intro j eta hmem c hc
        have ho := good.avoidance j eta (by rw [← storedEq j]; exact hmem) hc
        exact Finset.mem_sdiff.mpr ⟨by rw [missingEq j]; exact (Finset.mem_sdiff.mp ho).1,
          fun hn => (Finset.mem_sdiff.mp ho).2 (segmentSubset j eta hn)⟩
      disjointPairs := by
        intro j eta theta h₁ h₂ hne
        apply good.disjointPairs j eta theta
        · rw [← storedEq j]; exact h₁
        · rw [← storedEq j]; exact h₂
        · exact hne
      uniqueRefresh := by
        intro i
        rw [stageOrdNext i]
        simpa [storedEq, starredEq] using good.uniqueRefresh i
      parallelBase := by
        simpa [ettB, baseB, HierarchyStoredColorsAt, HierarchyStarredStage] using good.parallelBase
      minusClosed := by
        intro i
        rw [stageOrdNext i]
        simpa [storedEq] using good.minusClosed i }
  refine ⟨ettB, mpB, rfl, HEq.rfl, baseB, rfl, rfl, rfl, HB, rfl, ?_, ?_, goodB, ?_⟩
  · intro j
    exact ⟨by simpa using hbStageOld j, starredEq j⟩
  · intro i
    rfl
  · intro j
    exact ⟨storedEq j, missingEq j, fun eta => ⟨rfl, segmentSubset j eta⟩⟩
