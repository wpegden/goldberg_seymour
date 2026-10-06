import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyFirstMissingPositionPrefixCutoff
import Tablet.HierarchySegmentColors
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.TashkinovHierarchy

-- [TABLET NODE: GoodHierarchySameDividerTransport]
theorem GoodHierarchySameDividerTransport {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (J U : TreeSequence G e0)
    (corrJ : CorrespondingExtendedTashkinovTree G k e0 ett sigma J)
    (baseJ : HierarchyBase corrJ.replacementETT sigma)
    (KJ : TashkinovHierarchy corrJ.replacementETT baseJ)
    (goodJ : GoodHierarchy KJ)
    (corrU : CorrespondingExtendedTashkinovTree G k e0 ett sigma U)
    (baseU : HierarchyBase corrU.replacementETT sigma)
    (hcore : baseU.core = baseJ.core)
    (hclosure : baseU.closure = baseJ.closure)
    (KU : TashkinovHierarchy corrU.replacementETT baseU)
    (hcount : KU.dividerCount = KJ.dividerCount)
    (hstages : ∀ j : Fin (KU.dividerCount + 1),
      let jo : Fin (KJ.dividerCount + 1) :=
        Fin.cast (congrArg (fun n : ℕ => n + 1) hcount) j
      KU.stage j.castSucc = KJ.stage jo.castSucc ∧
        HierarchyStarredStage KU j = HierarchyStarredStage KJ jo ∧
        HierarchyStoredColorsAt KU j = HierarchyStoredColorsAt KJ jo ∧
        HierarchyStageMissingColors KU j = HierarchyStageMissingColors KJ jo)
    (hJU : TashkinovAugmentationSequence sigma J U) :
    let lastJ : Fin (KJ.dividerCount + 1) := Fin.last KJ.dividerCount
    let A : TreeSequence G e0 := HierarchyStarredStage KJ lastJ
    let restrictedColors : TreeSequence G e0 → Fin k → Finset (Fin k) :=
      fun W eta => Finset.univ.filter fun c =>
        ∃ r : Fin W.length, A.length ≤ r.val ∧
          r.val < min (HierarchyFirstMissingPosition sigma W eta).val W.length ∧
          sigma (W.edge r) = some c
    (∀ eta : Fin k, eta ∈ HierarchyStoredColorsAt KJ lastJ →
      Disjoint (goodJ.gamma lastJ eta) (restrictedColors U eta)) →
    ∃ goodU : GoodHierarchy KU,
      ∀ j : Fin (KU.dividerCount + 1),
        let jo : Fin (KJ.dividerCount + 1) :=
          Fin.cast (congrArg (fun n : ℕ => n + 1) hcount) j
        ∀ eta : Fin k, goodU.gamma j eta = goodJ.gamma jo eta := by
-- BODY
  classical
  dsimp
  intro havoid
  let index (j : Fin (KU.dividerCount + 1)) : Fin (KJ.dividerCount + 1) :=
    Fin.cast (congrArg (fun n : ℕ => n + 1) hcount) j
  let gammaU : Fin (KU.dividerCount + 1) → Fin k → Finset (Fin k) :=
    fun j eta => goodJ.gamma (index j) eta
  have stageEq (j : Fin (KU.dividerCount + 1)) :
      KU.stage j.castSucc = KJ.stage (index j).castSucc :=
    (hstages j).1
  have starredEq (j : Fin (KU.dividerCount + 1)) :
      HierarchyStarredStage KU j = HierarchyStarredStage KJ (index j) :=
    (hstages j).2.1
  have storedEq (j : Fin (KU.dividerCount + 1)) :
      HierarchyStoredColorsAt KU j = HierarchyStoredColorsAt KJ (index j) :=
    (hstages j).2.2.1
  have missingEq (j : Fin (KU.dividerCount + 1)) :
      HierarchyStageMissingColors KU j = HierarchyStageMissingColors KJ (index j) :=
    (hstages j).2.2.2
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
      (hbound : a + d ≤ KJ.dividerCount + 1),
      TreeSequenceInitialSegment (KJ.stage ⟨a, by omega⟩)
        (KJ.stage ⟨a + d, by omega⟩) := by
    intro a d
    induction d with
    | zero =>
        intro hbound
        simpa using (show TreeSequenceInitialSegment
          (KJ.stage ⟨a, by omega⟩) (KJ.stage ⟨a, by omega⟩) from
          ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩)
    | succ d ih =>
        intro hbound
        have hprev := ih (by omega)
        have hnext := KJ.nested ⟨a + d, by omega⟩
        have hnext' : TreeSequenceInitialSegment
            (KJ.stage ⟨a + d, by omega⟩)
            (KJ.stage ⟨a + (d + 1), by omega⟩) := by
          simpa [Nat.add_assoc] using hnext
        exact segmentTrans hprev hnext'
  have prefixJU : TreeSequenceInitialSegment J U :=
    TashkinovAugmentationSequenceInitialSegment sigma J U hJU
  have nextSegment (j : Fin KU.dividerCount) :
      TreeSequenceInitialSegment (KJ.stage (index j.succ).castSucc) J := by
    have hj : (index j.succ).val ≤ KJ.dividerCount := by
      have := (index j.succ).isLt
      omega
    have hs := stageSegment (index j.succ).val
      (KJ.dividerCount + 1 - (index j.succ).val) (by omega)
    have hlast : (KJ.stage ⟨(index j.succ).val +
        (KJ.dividerCount + 1 - (index j.succ).val), by omega⟩) = J := by
      have hi : (⟨(index j.succ).val +
          (KJ.dividerCount + 1 - (index j.succ).val), by omega⟩ :
          Fin (KJ.dividerCount + 2)) = Fin.last (KJ.dividerCount + 1) := by
        apply Fin.ext
        have hval : (index j.succ).val ≤ KJ.dividerCount := by omega
        simpa using Nat.add_sub_of_le (Nat.le_succ_of_le hval)
      rw [hi, KJ.terminalStage]
    rw [hlast] at hs
    convert hs using 1
    apply congrArg KJ.stage
    apply Fin.ext
    rfl
  have segmentEqInternal (j : Fin KU.dividerCount) (eta : Fin k) :
      HierarchySegmentColors KU j.castSucc eta =
        HierarchySegmentColors KJ (index j.castSucc) eta := by
    have hseg := nextSegment j
    have hcut := HierarchyFirstMissingPositionPrefixCutoff sigma J U
      prefixJU eta (KJ.stage (index j.succ).castSucc).length
      (Nat.le_of_lt_succ (Nat.lt_succ_of_le hseg.1))
    unfold HierarchySegmentColors
    dsimp
    have hidx : j.castSucc.succ = j.succ.castSucc := by
      apply Fin.ext
      rfl
    have hindex : (index j.castSucc).succ = (index j.succ).castSucc := by
      apply Fin.ext
      rfl
    rw [hidx, stageEq j.succ, hindex, starredEq j.castSucc]
    apply Finset.ext
    intro c
    constructor
    · intro hc
      rcases Finset.mem_filter.mp hc with ⟨_, r, hlo, hhi, hcol⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, r, hlo, ?_, hcol⟩
      simpa [hcut] using hhi
    · intro hc
      rcases Finset.mem_filter.mp hc with ⟨_, r, hlo, hhi, hcol⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, r, hlo, ?_, hcol⟩
      simpa [hcut] using hhi
  have terminalSegmentEq (eta : Fin k) :
      HierarchySegmentColors KU (Fin.last KU.dividerCount) eta =
        Finset.univ.filter (fun c => ∃ r : Fin U.length,
          (HierarchyStarredStage KJ (Fin.last KJ.dividerCount)).length ≤ r.val ∧
          r.val < min (HierarchyFirstMissingPosition sigma U eta).val U.length ∧
          sigma (U.edge r) = some c) := by
    unfold HierarchySegmentColors
    dsimp
    rw [KU.terminalStage]
    have hlastIndex : index (Fin.last KU.dividerCount) =
        Fin.last KJ.dividerCount := by
      apply Fin.ext
      simp [index]
    rw [← hlastIndex]
    rw [starredEq (Fin.last KU.dividerCount)]
  have terminalData (W : TreeSequence G e0)
      (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma W) :
      corr.replacementETT.series.data.tree
          (Fin.last corr.replacementETT.rounds).castSucc =
          ett.series.data.tree (Fin.last ett.rounds).castSucc ∧
      corr.replacementETT.series.data.kind (Fin.last corr.replacementETT.rounds) =
          ett.series.data.kind (Fin.last ett.rounds) := by
    rcases corr with ⟨replacementInput, replacementSeries, replacementETT,
      rungAgreement, seriesPresentation, finalGeneratingColoring,
      ladderTreesAgree, storedColorsAgree, connectingEdgesAgree,
      extensionKindsAgree, replacementProper, replacementOneUncolored,
      replacementStable⟩
    cases replacementETT with
    | mk rounds roundsPositive replacementData above strict below generating =>
      cases rungAgreement
      have seriesSame : replacementData = replacementSeries :=
        eq_of_heq seriesPresentation
      cases seriesSame
      let q : Fin ett.rounds :=
        ⟨ett.rounds - 1,
          Nat.sub_lt (Nat.zero_lt_of_lt ett.roundsPositive) (by omega)⟩
      have hq : q.succ = Fin.last ett.rounds := by
        apply Fin.ext
        exact Nat.sub_add_cancel ett.roundsPositive
      refine ⟨?_, ?_⟩
      · rw [← hq]
        exact (ladderTreesAgree q).trans rfl
      · exact extensionKindsAgree (Fin.last ett.rounds)
  let goodU : GoodHierarchy KU :=
    { gamma := gammaU
      twoColors := by
        intro j eta hmem
        apply goodJ.twoColors (index j) eta
        rw [← storedEq j]
        exact hmem
      avoidance := by
        intro j eta hmem c hc
        have hmemOld : eta ∈ HierarchyStoredColorsAt KJ (index j) := by
          rw [← storedEq j]
          exact hmem
        have hmissing := (Finset.mem_sdiff.mp
          (goodJ.avoidance (index j) eta hmemOld hc)).1
        have hnewMissing : c ∈ HierarchyStageMissingColors KU j := by
          rw [missingEq j]
          exact hmissing
        refine Finset.mem_sdiff.mpr ⟨hnewMissing, ?_⟩
        intro hseg
        by_cases hj : j.val < KU.dividerCount
        · let ji : Fin KU.dividerCount := ⟨j.val, hj⟩
          have heq := segmentEqInternal ji eta
          have hindex : index ji.castSucc = index j := by
            apply Fin.ext
            rfl
          have hsegOld : c ∈ HierarchySegmentColors KJ (index j) eta := by
            rw [← hindex, ← heq]
            simpa [ji] using hseg
          exact (Finset.mem_sdiff.mp
            (goodJ.avoidance (index j) eta hmemOld hc)).2 hsegOld
        · have hjlast : j = Fin.last KU.dividerCount := by
            apply Fin.ext
            simp only [Fin.val_last]
            omega
          subst j
          have hrestrict : c ∈ Finset.univ.filter (fun c => ∃ r : Fin U.length,
              (HierarchyStarredStage KJ (Fin.last KJ.dividerCount)).length ≤ r.val ∧
              r.val < min (HierarchyFirstMissingPosition sigma U eta).val U.length ∧
              sigma (U.edge r) = some c) := by
            rw [← terminalSegmentEq eta]
            exact hseg
          have hlastIndex : index (Fin.last KU.dividerCount) =
              Fin.last KJ.dividerCount := by
            apply Fin.ext
            simp [index, hcount]
          rw [hlastIndex] at hmemOld
          have hcOld : c ∈ goodJ.gamma (Fin.last KJ.dividerCount) eta := by
            simpa [gammaU, hlastIndex] using hc
          exact (Finset.disjoint_left.mp (havoid eta hmemOld)) hcOld hrestrict
      disjointPairs := by
        intro j eta theta h₁ h₂ hne
        apply goodJ.disjointPairs (index j) eta theta
        · rw [← storedEq j]; exact h₁
        · rw [← storedEq j]; exact h₂
        · exact hne
      uniqueRefresh := by
        intro i
        let oldInternal : Fin KJ.dividerCount := ⟨i.val, by
          simpa [hcount] using i.isLt⟩
        have hold := goodJ.uniqueRefresh oldInternal
        rcases hold with ⟨chosen, hchosen, hunique⟩
        have hnext : oldInternal.succ = index i.succ := by
          apply Fin.ext
          rfl
        have hprev : oldInternal.castSucc = index i.castSucc := by
          apply Fin.ext
          rfl
        refine ⟨chosen, ?_, ?_⟩
        · rcases hchosen with ⟨hchosen, hlocal, hrest⟩
          refine ⟨?_, ?_, ?_⟩
          · rw [storedEq i.succ]
            exact hchosen
          · rw [stageEq i.succ, starredEq i.castSucc]
            simpa [gammaU, oldInternal, hnext, hprev] using hlocal
          · intro theta htheta hne
            have hthetaOld : theta ∈ HierarchyStoredColorsAt KJ oldInternal.succ := by
              rw [hnext]
              exact (storedEq i.succ).symm ▸ htheta
            have hh := hrest theta hthetaOld hne
            simpa [gammaU, oldInternal, hnext, hprev] using hh
        · intro eta heta
          have hetaOld : eta ∈ HierarchyStoredColorsAt KJ oldInternal.succ := by
            rw [hnext]
            exact (storedEq i.succ).symm ▸ heta.1
          apply hunique eta
          refine ⟨hetaOld, ?_, ?_⟩
          · have hnewlocal := heta.2.1
            rw [stageEq i.succ, starredEq i.castSucc] at hnewlocal
            simpa [gammaU, oldInternal, hnext, hprev] using hnewlocal
          · intro theta htheta hne
            have hthetaNew : theta ∈ HierarchyStoredColorsAt KU i.succ := by
              rw [storedEq i.succ]
              rw [hnext] at htheta
              exact htheta
            simpa [gammaU, oldInternal, hnext, hprev] using
              heta.2.2 theta hthetaNew hne
      parallelBase := by
        have dataJ := terminalData J corrJ
        have dataU := terminalData U corrU
        have hkind : corrU.replacementETT.series.data.kind
            (Fin.last corrU.replacementETT.rounds) =
            corrJ.replacementETT.series.data.kind
              (Fin.last corrJ.replacementETT.rounds) :=
          dataU.2.trans dataJ.2.symm
        have hzero : (HierarchyStoredColorsAt KU 0).biUnion (gammaU 0) =
            (HierarchyStoredColorsAt KJ 0).biUnion (goodJ.gamma 0) := by
          rw [storedEq 0]
          have hi0 : index 0 = (0 : Fin (KJ.dividerCount + 1)) := by
            apply Fin.ext
            rfl
          simp [gammaU, hi0]
        dsimp
        intro hpe
        have hpeJ : corrJ.replacementETT.series.data.kind
            (Fin.last corrJ.replacementETT.rounds) =
            some TashkinovExtensionKind.PE := by
          rw [← hkind]
          exact hpe
        have hold := goodJ.parallelBase hpeJ
        rw [hcore, hclosure, hzero]
        rw [dataU.1, ← dataJ.1]
        exact hold
      minusClosed := by
        intro i
        let oldInternal : Fin KJ.dividerCount := ⟨i.val, by
          simpa [hcount] using i.isLt⟩
        have hold := goodJ.minusClosed oldInternal
        have hnext : oldInternal.succ = index i.succ := by
          apply Fin.ext
          rfl
        have hprev : oldInternal.castSucc = index i.castSucc := by
          apply Fin.ext
          rfl
        rw [hnext, hprev] at hold
        rw [stageEq i.succ, storedEq i.succ]
        simpa [gammaU] using hold }
  refine ⟨goodU, ?_⟩
  intro j eta
  rfl
