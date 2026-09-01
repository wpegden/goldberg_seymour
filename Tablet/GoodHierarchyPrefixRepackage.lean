import Tablet.GoodHierarchy
import Tablet.MaximumProperty
import Tablet.TreeSequencePrefix

-- [TABLET NODE: GoodHierarchyPrefixRepackage]
theorem GoodHierarchyPrefixRepackage {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base)
    (good : GoodHierarchy H)
    (r : Fin (H.dividerCount + 1)) (hr : 1 ≤ r.val) :
    ∃ ettPrefix : ExtendedTashkinovTree G k e0 input
        (H.stage r.castSucc) generating,
      MaximumProperty ettPrefix ∧
      ettPrefix.rounds = ett.rounds ∧ HEq ettPrefix.series ett.series ∧
      ∃ basePrefix : HierarchyBase ettPrefix phi,
        basePrefix.core = base.core ∧
        basePrefix.closure = base.closure ∧
        basePrefix.supportPosition.val = base.supportPosition.val ∧
        ∃ HP : TashkinovHierarchy ettPrefix basePrefix,
          ∃ hcount : HP.dividerCount = r.val - 1,
            (∀ j : Fin (r.val + 1),
              HP.stage (Fin.cast (by omega) j) =
                H.stage ⟨j.val, by omega⟩) ∧
            (∀ i : Fin (r.val - 1),
              (HP.dividerPosition (Fin.cast (by omega) i)).val =
                (H.dividerPosition ⟨i.val, by omega⟩).val) ∧
            ∃ goodPrefix : GoodHierarchy HP,
              (∀ j : Fin r.val,
                HierarchyStoredColorsAt HP (Fin.cast (by omega) j) =
                    HierarchyStoredColorsAt H ⟨j.val, by omega⟩ ∧
                  ∀ eta : Fin k,
                    goodPrefix.gamma (Fin.cast (by omega) j) eta =
                      good.gamma ⟨j.val, by omega⟩ eta) ∧
              TreeColorSetMinusClosed G phi (H.stage r.castSucc)
                ((HierarchyStoredColorsAt H r).biUnion
                  (good.gamma ⟨r.val - 1, by omega⟩)) := by
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
    | zero =>
        intro hbound
        simpa using segmentRefl (H.stage ⟨a, by omega⟩)
    | succ d ih =>
        intro hbound
        have hprev := ih (by omega)
        have hnext := H.nested ⟨a + d, by omega⟩
        have hnext' : TreeSequenceInitialSegment
            (H.stage ⟨a + d, by omega⟩)
            (H.stage ⟨a + (d + 1), by omega⟩) := by
          simpa [Nat.add_assoc] using hnext
        exact segmentTrans hprev hnext'
  have prefixEqOfSegment {A B : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B) :
      A = TreeSequencePrefix B A.length A.positive hAB.1 := by
    cases A with
    | mk la pa va ea via eia fea aa =>
      cases B with
      | mk lb pb vb eb vib eib feb ab =>
        rw [TreeSequence.mk.injEq]
        refine ⟨rfl, ?_, ?_⟩
        · apply heq_of_eq
          funext i
          simpa [TreeSequencePrefix] using (hAB.2.1 i).symm
        · apply heq_of_eq
          funext i
          simpa [TreeSequencePrefix] using (hAB.2.2 i).symm
  let Tp := H.stage r.castSucc
  have firstToPrefix : TreeSequenceInitialSegment
      (ett.series.data.tree ⟨ett.rounds, by omega⟩) Tp := by
    change TreeSequenceInitialSegment
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) Tp
    rw [← H.baseStage]
    have hs := stageSegment 0 r.val (by omega)
    convert hs using 1 <;> apply congrArg H.stage <;> apply Fin.ext <;> simp
  have prefixToTerminal : TreeSequenceInitialSegment Tp T := by
    have hs := stageSegment r.val (H.dividerCount + 1 - r.val) (by omega)
    have hind : r.val + (H.dividerCount + 1 - r.val) =
        H.dividerCount + 1 := by omega
    have hidx : (⟨r.val + (H.dividerCount + 1 - r.val), by omega⟩ :
        Fin (H.dividerCount + 2)) = Fin.last (H.dividerCount + 1) :=
      Fin.ext hind
    rw [hidx, H.terminalStage] at hs
    convert hs using 1
    apply congrArg H.stage
    apply Fin.ext
    rfl
  let ettPrefix : ExtendedTashkinovTree G k e0 input Tp generating :=
    { rounds := ett.rounds
      roundsPositive := ett.roundsPositive
      series := ett.series
      abovePenultimate := firstToPrefix
      strictAbovePenultimate := by
        change (ett.series.data.tree
          (Fin.last ett.rounds).castSucc).length < Tp.length
        rw [← H.baseStage]
        have hfirst := H.strict (0 : Fin (H.dividerCount + 1))
        have hrest := (stageSegment 1 (r.val - 1) (by omega)).1
        have hidx : H.stage ⟨1 + (r.val - 1), by omega⟩ = Tp := by
          dsimp [Tp]
          apply congrArg H.stage
          apply Fin.ext
          simp
          omega
        rw [hidx] at hrest
        apply lt_of_lt_of_le hfirst
        exact hrest
      belowFinal := segmentTrans prefixToTerminal ett.belowFinal
      generatingColoring := ett.generatingColoring }
  have mpPrefix : MaximumProperty ettPrefix := by
    simpa [MaximumProperty, ettPrefix] using hMP
  let basePrefix : HierarchyBase ettPrefix phi :=
    { core := base.core
      closure := base.closure
      supportPosition := base.supportPosition
      supportPositive := base.supportPositive
      terminalMissingColors := by simpa [ettPrefix] using base.terminalMissingColors
      parallel := by simpa [ettPrefix] using base.parallel
      nonparallel := by simpa [ettPrefix] using base.nonparallel }
  have oldDividerValue (i : Fin H.dividerCount) :
      (H.dividerPosition i).val =
        (H.stage ⟨i.val + 1, by omega⟩).length := by
    have h := congrArg TreeSequence.length (H.dividerStage i)
    simpa [TreeSequencePrefix] using h.symm
  let dividerPositionPrefix (i : Fin (r.val - 1)) : Fin (Tp.length + 1) :=
    ⟨(H.stage ⟨i.val + 1, by omega⟩).length,
      by
        have hs := stageSegment (i.val + 1)
          (r.val - (i.val + 1)) (by omega)
        have hind : i.val + 1 + (r.val - (i.val + 1)) = r.val := by omega
        have hidx : (⟨i.val + 1 + (r.val - (i.val + 1)), by omega⟩ :
            Fin (H.dividerCount + 2)) = r.castSucc := Fin.ext hind
        rw [hidx] at hs
        exact Nat.lt_succ_of_le (by simpa [Tp] using hs.1)⟩
  let HP : TashkinovHierarchy ettPrefix basePrefix :=
    { dividerCount := r.val - 1
      stage := fun j => H.stage ⟨j.val, by omega⟩
      baseStage := by simpa [ettPrefix] using H.baseStage
      terminalStage := by
        dsimp [Tp]
        apply congrArg H.stage
        apply Fin.ext
        simp
        omega
      nested := by
        intro j
        have hn := H.nested ⟨j.val, by omega⟩
        convert hn using 1 <;> apply congrArg H.stage <;> apply Fin.ext <;> rfl
      strict := by
        intro j
        have hs := H.strict ⟨j.val, by omega⟩
        convert hs using 1 <;> apply congrArg TreeSequence.length <;>
          apply congrArg H.stage <;> apply Fin.ext <;> rfl
      dividerPosition := dividerPositionPrefix
      dividerPositive := by
        intro i
        exact (H.stage ⟨i.val + 1, by omega⟩).positive
      dividerIncreasing := by
        intro i j hij
        have oldInc := H.dividerIncreasing
          (⟨i.val, by omega⟩ : Fin H.dividerCount)
          (⟨j.val, by omega⟩ : Fin H.dividerCount) hij
        simpa [dividerPositionPrefix, oldDividerValue] using oldInc
      dividerStage := by
        intro i
        have hs := stageSegment (i.val + 1)
          (r.val - (i.val + 1)) (by omega)
        have hind : i.val + 1 + (r.val - (i.val + 1)) = r.val := by omega
        have hidx : (⟨i.val + 1 + (r.val - (i.val + 1)), by omega⟩ :
            Fin (H.dividerCount + 2)) = r.castSucc := Fin.ext hind
        rw [hidx] at hs
        simpa [dividerPositionPrefix, Tp] using prefixEqOfSegment hs
      coreInsideFirst := by simpa [basePrefix] using H.coreInsideFirst }
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
      let ia : Fin (A.length + 1) :=
        ⟨(candidatesB.min' hB).val, by omega⟩
      have hmemB := Finset.min'_mem candidatesB hB
      have hmissingB : eta ∈ MissingColors G phi
          (B.vertex (candidatesB.min' hB)) :=
        (Finset.mem_filter.mp hmemB).2
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
  have stageEqRaw (j : Fin (HP.dividerCount + 2)) :
      HP.stage j = H.stage ⟨j.val, by
        have hj := j.isLt
        change j.val < r.val - 1 + 2 at hj
        omega⟩ := by
    rfl
  have starredEqRaw (j : Fin (HP.dividerCount + 1)) :
      HierarchyStarredStage HP j =
        HierarchyStarredStage H ⟨j.val, by
          have hj := j.isLt
          change j.val < r.val - 1 + 1 at hj
          omega⟩ := by
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [HierarchyStarredStage, basePrefix]
    · change HP.stage i.succ.castSucc =
        H.stage ⟨i.val + 1, by
          have hi := i.isLt
          change i.val < r.val - 1 at hi
          omega⟩
      exact stageEqRaw i.succ.castSucc
  have storedEqRaw (j : Fin (HP.dividerCount + 1)) :
      HierarchyStoredColorsAt HP j =
        HierarchyStoredColorsAt H ⟨j.val, by
          have hj := j.isLt
          change j.val < r.val - 1 + 1 at hj
          omega⟩ := by
    unfold HierarchyStoredColorsAt
    dsimp [ettPrefix]
    rw [starredEqRaw]
  have stageMissingEqRaw (j : Fin (HP.dividerCount + 1)) :
      HierarchyStageMissingColors HP j =
        HierarchyStageMissingColors H ⟨j.val, by
          have hj := j.isLt
          change j.val < r.val - 1 + 1 at hj
          omega⟩ := by
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [HierarchyStageMissingColors, ettPrefix]
    · change TreeMissingColors phi (HP.stage i.succ.castSucc) =
        TreeMissingColors phi (H.stage ⟨i.val + 1, by
          have hi := i.isLt
          change i.val < r.val - 1 at hi
          omega⟩)
      rw [stageEqRaw i.succ.castSucc]
      congr 2
  have segmentSubsetRaw (j : Fin (HP.dividerCount + 1)) (eta : Fin k) :
      HierarchySegmentColors HP j eta ⊆
        HierarchySegmentColors H ⟨j.val, by
          have hj := j.isLt
          change j.val < r.val - 1 + 1 at hj
          omega⟩ eta := by
    intro c hc
    unfold HierarchySegmentColors at hc ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    rcases hc with ⟨x, hafter, hbefore, hcolor⟩
    let jo : Fin (H.dividerCount + 1) := ⟨j.val, by
      have hj := j.isLt
      change j.val < r.val - 1 + 1 at hj
      omega⟩
    have hstage : HP.stage j.succ = H.stage jo.succ := by
      rw [stageEqRaw j.succ]
      apply congrArg H.stage
      apply Fin.ext
      rfl
    let xo : Fin (H.stage jo.succ).length :=
      Fin.cast (congrArg TreeSequence.length hstage) x
    have hsOld := stageSegment (j.val + 1)
      (r.val - (j.val + 1)) (by
        have hj := j.isLt
        change j.val < r.val - 1 + 1 at hj
        omega)
    have hind : j.val + 1 + (r.val - (j.val + 1)) = r.val := by
      have hj := j.isLt
      change j.val < r.val - 1 + 1 at hj
      omega
    have hidx : (⟨j.val + 1 + (r.val - (j.val + 1)), by omega⟩ :
        Fin (H.dividerCount + 2)) = r.castSucc := Fin.ext hind
    rw [hidx] at hsOld
    have hsNew : TreeSequenceInitialSegment (HP.stage j.succ) Tp := by
      rw [hstage]
      exact hsOld
    have hxStage : x.val < (HP.stage j.succ).length :=
      lt_of_lt_of_le hbefore (Nat.min_le_right _ _)
    have hxFirst : x.val <
        (HierarchyFirstMissingPosition phi Tp eta).val :=
      lt_of_lt_of_le hbefore (Nat.min_le_left _ _)
    let ix : Fin (Tp.length + 1) := ⟨x.val, by omega⟩
    have hxOldFirst := beforeFirstMissing prefixToTerminal eta ix
      (by dsimp [ix]; omega) (by simpa [ix] using hxFirst)
    refine ⟨xo, ?_, ?_, ?_⟩
    · rw [← starredEqRaw j]
      simpa [xo] using hafter
    · apply lt_min
      · simpa [xo, ix] using hxOldFirst
      · simpa [xo, hstage] using hxStage
    · cases hstage
      exact hcolor
  let oldGammaIndex (j : Fin (HP.dividerCount + 1)) :
      Fin (H.dividerCount + 1) := ⟨j.val, by
        have hj := j.isLt
        change j.val < r.val - 1 + 1 at hj
        omega⟩
  let gammaPrefix : Fin (HP.dividerCount + 1) → Fin k → Finset (Fin k) :=
    fun j eta => good.gamma (oldGammaIndex j) eta
  let goodPrefix : GoodHierarchy HP :=
    { gamma := gammaPrefix
      twoColors := by
        intro j eta heta
        apply good.twoColors (oldGammaIndex j) eta
        rw [← storedEqRaw j]
        exact heta
      avoidance := by
        intro j eta heta c hc
        have hetaOld : eta ∈ HierarchyStoredColorsAt H (oldGammaIndex j) := by
          rw [← storedEqRaw j]
          exact heta
        have hold := good.avoidance (oldGammaIndex j) eta hetaOld hc
        apply Finset.mem_sdiff.mpr
        constructor
        · rw [stageMissingEqRaw j]
          exact (Finset.mem_sdiff.mp hold).1
        · intro hnew
          exact (Finset.mem_sdiff.mp hold).2 (segmentSubsetRaw j eta hnew)
      disjointPairs := by
        intro j eta theta heta htheta hne
        apply good.disjointPairs (oldGammaIndex j) eta theta
        · rw [← storedEqRaw j]
          exact heta
        · rw [← storedEqRaw j]
          exact htheta
        · exact hne
      uniqueRefresh := by
        intro i
        let io : Fin H.dividerCount := ⟨i.val, by
          have hi := i.isLt
          change i.val < r.val - 1 at hi
          omega⟩
        have hold := good.uniqueRefresh io
        rw [storedEqRaw i.succ, stageEqRaw i.succ.castSucc,
          starredEqRaw i.castSucc]
        simpa [gammaPrefix, oldGammaIndex, io] using hold
      parallelBase := by
        simpa [ettPrefix, basePrefix, gammaPrefix, oldGammaIndex, HP,
          HierarchyStoredColorsAt, HierarchyStarredStage] using
            good.parallelBase
      minusClosed := by
        intro i
        let io : Fin H.dividerCount := ⟨i.val, by
          have hi := i.isLt
          change i.val < r.val - 1 at hi
          omega⟩
        have hold := good.minusClosed io
        rw [stageEqRaw i.succ.castSucc, storedEqRaw i.succ]
        simpa [gammaPrefix, oldGammaIndex, io] using hold }
  let lastInternal : Fin H.dividerCount := ⟨r.val - 1, by omega⟩
  have terminalClosed :
      TreeColorSetMinusClosed G phi (H.stage r.castSucc)
        ((HierarchyStoredColorsAt H r).biUnion
          (good.gamma ⟨r.val - 1, by omega⟩)) := by
    have hold := good.minusClosed lastInternal
    have hs : lastInternal.succ = r := by
      apply Fin.ext
      dsimp [lastInternal]
      omega
    rw [hs] at hold
    simpa [lastInternal] using hold
  refine ⟨ettPrefix, mpPrefix, rfl, HEq.rfl, basePrefix, rfl, rfl, rfl,
    HP, rfl, ?_, ?_, goodPrefix, ?_, terminalClosed⟩
  · intro j
    rfl
  · intro i
    change (H.stage ⟨i.val + 1, by omega⟩).length =
      (H.dividerPosition ⟨i.val, by omega⟩).val
    exact (oldDividerValue ⟨i.val, by omega⟩).symm
  · intro j
    constructor
    · let jp : Fin (HP.dividerCount + 1) :=
        Fin.cast (by dsimp [HP]; omega) j
      have hs := storedEqRaw jp
      convert hs using 1 <;> congr 2
    · intro eta
      rfl
