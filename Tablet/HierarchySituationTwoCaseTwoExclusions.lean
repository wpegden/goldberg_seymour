import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchySituationTwoCaseTwoData
import Tablet.HierarchyStarredStage
import Tablet.HierarchyTailMissingColorExclusion
import Tablet.TashkinovStoredColors
import Tablet.TreeMissingColors

-- [TABLET NODE: HierarchySituationTwoCaseTwoExclusions]
theorem HierarchySituationTwoCaseTwoExclusions {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseTwoData
      G k e0 input T phi ett base C ctx) :
    let H := C.hierarchy
    let A := HierarchyStarredStage H (Fin.last H.dividerCount)
    let ell := HierarchyFullTailLength C
    let B := HierarchyFullTailPrefix C (ell - 2)
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    D.alpha ∉ TreeMissingColors phi B ∧
      D.alpha ∉ TashkinovStoredColors ett.series.data n ∧
      ∀ t : Fin T.length, A.length ≤ t.val →
        phi (T.edge t) ≠ some D.alpha := by
-- BODY
  dsimp
  let H := C.hierarchy
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  let ell := HierarchyFullTailLength C
  let B := HierarchyFullTailPrefix C (ell - 2)
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  have segmentTrans {X Y Z : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y)
      (hYZ : TreeSequenceInitialSegment Y Z) :
      TreeSequenceInitialSegment X Z := by
    rcases hXY with ⟨hxy, vxy, exy⟩
    rcases hYZ with ⟨hyz, vyz, eyz⟩
    refine ⟨le_trans hxy hyz, ?_, ?_⟩
    · intro i
      have hm := vyz (Fin.castLE (Nat.succ_le_succ hxy) i)
      simpa using hm.trans (vxy i)
    · intro i
      have hm := eyz (Fin.castLE hxy i)
      simpa using hm.trans (exy i)
  have stageSegment : ∀ (a d : ℕ), (hbound : a + d ≤ H.dividerCount + 1) →
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
        (H.stage ⟨a + d, by omega⟩) := by
    intro a d hbound
    induction d with
    | zero => exact ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
    | succ d ih =>
      apply segmentTrans (ih (by omega))
      have hn := H.nested ⟨a + d, by omega⟩
      simpa [Nat.add_assoc] using hn
  have hAstage : ∀ hq : 0 < H.dividerCount,
      A = H.stage ⟨H.dividerCount, by omega⟩ := by
    intro hq
    have hlast : (Fin.last H.dividerCount : Fin (H.dividerCount + 1)) =
        (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ := by
      apply Fin.ext
      simp
      omega
    dsimp [A, HierarchyStarredStage]
    rw [hlast]
    simp only [Fin.cases]
    apply congrArg H.stage
    apply Fin.ext
    simp
    omega
  have hAT : TreeSequenceInitialSegment A T := by
    by_cases hq : H.dividerCount = 0
    · have hc := H.coreInsideFirst
      have ht : H.stage ⟨1, by omega⟩ = T := by
        have hi : (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) =
            Fin.last (H.dividerCount + 1) := by
          apply Fin.ext
          simp [hq]
        rw [hi]
        exact H.terminalStage
      have hc' : TreeSequenceInitialSegment base.core T := by
        convert hc using 1
        exact ht.symm
      simpa [A, H, HierarchyStarredStage, Fin.last, hq] using hc'
    · have hs := stageSegment H.dividerCount 1 (by omega)
      have ha : A = H.stage ⟨H.dividerCount, by omega⟩ := hAstage (Nat.pos_of_ne_zero hq)
      rw [ha]
      have ht : H.stage ⟨H.dividerCount + 1, by omega⟩ = T := by
        convert H.terminalStage using 1
        apply congrArg H.stage
        apply Fin.ext
        rfl
      simpa [ht] using hs
  have helem : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet (HierarchyFullTailPrefix C (ell - 1))) := by
    change ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet
        (TreeSequencePrefix T
          (min (A.length + (ell - 1)) T.length)
          (by have hA := A.positive; have hT := T.positive; omega)
          (Nat.min_le_right _ _)))
    exact HierarchyCounterexamplePenultimateElementary G k e0 input T phi ett base C
      (hproper := ctx.proper) (hone := ctx.oneEdgeUncolored)
      (hlower := ctx.lowerRung) (hfewer := ctx.fewerDividers)
      (hminimal := ctx.lexicographicMinimality)
      (hlarge := ctx.largeMissingSet)
  have hlen : A.length ≤ T.length := hAT.1
  have htail : 2 ≤ ell := D.tailAtLeastTwo
  have hEll : ell = T.length - A.length := by
    change ell = T.length - A.length
    rfl
  have hBlen : (HierarchyFullTailPrefix C (ell - 2)).length = T.length - 2 := by
    change min (A.length + (ell - 2)) T.length = T.length - 2
    rw [hEll]
    omega
  have hlast : (HierarchyFullTailPrefix C (ell - 1)).length = T.length - 1 := by
    change min (A.length + (ell - 1)) T.length = T.length - 1
    rw [hEll]
    omega
  have hBseg : TreeSequenceInitialSegment
      (HierarchyFullTailPrefix C (ell - 2))
      (HierarchyFullTailPrefix C (ell - 1)) := by
    unfold HierarchyFullTailPrefix
    refine ⟨?_, ?_, ?_⟩
    · simp
      change min (A.length + (ell - 2)) T.length ≤
        min (A.length + (ell - 1)) T.length
      rw [hEll]
      omega
    · intro i
      rfl
    · intro i
      rfl
  have halphaB : D.alpha ∉ TreeMissingColors phi B := by
    dsimp [B]
    intro hab
    have hab' : D.alpha ∈
        (TreeSequenceVertexSet B).biUnion (fun v => MissingColors G phi v) := by
      simpa [TreeMissingColors] using hab
    obtain ⟨z, hz, haz⟩ := Finset.mem_biUnion.mp hab'
    dsimp [B] at hz
    have hz' : ∃ j, j ∈ Finset.univ ∧
        (HierarchyFullTailPrefix C (ell - 2)).vertex j = z := by
      simpa only [TreeSequenceVertexSet, Finset.mem_image] using hz
    obtain ⟨j, _, hjz⟩ := hz'
    have hj : j.val < T.length - 1 := by
      have hj0 := j.isLt
      have hstep : j.val < T.length - 2 + 1 := by
        calc
          j.val < (HierarchyFullTailPrefix C (ell - 2)).length + 1 := hj0
          _ = T.length - 2 + 1 := by rw [hBlen]
      omega
    have hzplus : z ∈
        TreeSequenceVertexSet (HierarchyFullTailPrefix C (ell - 1)) := by
      have hvmap := hBseg.2.1 j
      simpa only [TreeSequenceVertexSet] using
        ((@Finset.mem_image _ _ (Classical.decEq V)).mpr
          ⟨Fin.castLE (Nat.succ_le_succ hBseg.1) j, Finset.mem_univ _,
            hvmap.trans hjz⟩)
    have hyplus : T.vertex D.penultimateVertexIndex ∈
        TreeSequenceVertexSet (HierarchyFullTailPrefix C (ell - 1)) := by
      simpa only [TreeSequenceVertexSet] using
        ((@Finset.mem_image _ _ (Classical.decEq V)).mpr
          ⟨Fin.last (HierarchyFullTailPrefix C (ell - 1)).length,
            Finset.mem_univ _, by
            change T.vertex _ = _
            apply congrArg T.vertex
            apply Fin.ext
            change (HierarchyFullTailPrefix C (ell - 1)).length =
              D.penultimateVertexIndex.val
            rw [hlast]
            have hp := D.penultimateVertexPosition
            omega⟩)
    have hne : z ≠ T.vertex D.penultimateVertexIndex := by
      intro heq
      have hzmap := hBseg.2.1 j
      have hyval : (Fin.last (HierarchyFullTailPrefix C (ell - 1)).length).val =
          D.penultimateVertexIndex.val := by
        rw [hlast]
        simp only [Fin.val_last]
        have hp := D.penultimateVertexPosition
        omega
      have heq' :
          (HierarchyFullTailPrefix C (ell - 1)).vertex
              (Fin.castLE (Nat.succ_le_succ hBseg.1) j) =
            (HierarchyFullTailPrefix C (ell - 1)).vertex
              (Fin.last (HierarchyFullTailPrefix C (ell - 1)).length) := by
        calc
          _ = z := Eq.trans hzmap hjz
          _ = T.vertex D.penultimateVertexIndex := heq
          _ = _ := by
            change T.vertex _ = _
            apply congrArg T.vertex
            apply Fin.ext
            symm
            change (Fin.castLE _ (Fin.last (HierarchyFullTailPrefix C (ell - 1)).length)).val =
              D.penultimateVertexIndex.val
            change (Fin.last (HierarchyFullTailPrefix C (ell - 1)).length).val =
              D.penultimateVertexIndex.val
            simp only [Fin.val_last]
            rw [hlast]
            have hp := D.penultimateVertexPosition
            omega
      have hi := (HierarchyFullTailPrefix C (ell - 1)).vertex_injective heq'
      have hv := congrArg Fin.val hi
      change j.val = (Fin.last (HierarchyFullTailPrefix C (ell - 1)).length).val at hv
      rw [hlast] at hv
      simp only [Fin.val_last] at hv
      omega
    have hd := helem hzplus hyplus hne
    exact (Finset.disjoint_left.1 hd) haz D.alphaMissingPenultimate
  have halphaStored : D.alpha ∉ TashkinovStoredColors ett.series.data n := by
    intro ha
    have haA : D.alpha ∉ TreeMissingColors phi A := by
      dsimp [A] at *
      intro haA'
      have haA'' : D.alpha ∈
          (TreeSequenceVertexSet A).biUnion (fun v => MissingColors G phi v) := by
        simpa [TreeMissingColors] using haA'
      obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp haA''
      have hvB : v ∈ TreeSequenceVertexSet B := by
        dsimp [B]
        have hv' : ∃ i, i ∈ Finset.univ ∧ A.vertex i = v := by
          simpa only [TreeSequenceVertexSet, Finset.mem_image] using hv
        obtain ⟨i, _, hiv⟩ := hv'
        have hidx := hAT.2.1 i
        have hi' : A.length ≤ B.length := by
          change A.length ≤ (HierarchyFullTailPrefix C (ell - 2)).length
          rw [hBlen]
          have hsum : A.length + ell = T.length := by
            calc
              A.length + ell = A.length + (T.length - A.length) := by rw [hEll]
              _ = T.length := Nat.add_sub_of_le hlen
          omega
        let ib : Fin (B.length + 1) := ⟨i.val, by omega⟩
        have hmem : v ∈ TreeSequenceVertexSet
            (HierarchyFullTailPrefix C (ell - 2)) := by
          simpa only [TreeSequenceVertexSet] using
            ((@Finset.mem_image _ _ (Classical.decEq V)).mpr (⟨ib, Finset.mem_univ _, by
              have hmap :
                  (HierarchyFullTailPrefix C (ell - 2)).vertex ib = A.vertex i := by
                change T.vertex _ = A.vertex i
                rw [← hidx]
                apply congrArg T.vertex
                apply Fin.ext
                rfl
              exact hmap.trans hiv⟩))
        exact hmem
      exact halphaB (by
        simpa [TreeMissingColors] using
          (Finset.mem_biUnion.mpr ⟨v, hvB, hav⟩))
    have hstored : D.alpha ∈
        HierarchyStoredColorsAt H (Fin.last H.dividerCount) := by
      unfold HierarchyStoredColorsAt
      rw [Finset.mem_sdiff]
      exact ⟨ha, haA⟩
    exact D.alphaOutsideStored hstored
  refine ⟨halphaB, halphaStored, ?_⟩
  intro t ht
  by_cases hlastIndex : t.val + 1 = T.length
  · have hi : t = D.lastEdgeIndex := by
      apply Fin.ext
      have hp := D.lastEdgePosition
      omega
    intro he
    have hedge : T.edge t = T.edge D.lastEdgeIndex := by rw [hi]
    have he' : phi (T.edge D.lastEdgeIndex) = some D.alpha := by
      rw [← hedge]
      exact he
    have htheta : phi (T.edge D.lastEdgeIndex) = some D.theta := D.thetaOnLastEdge
    have hta : D.theta = D.alpha := Option.some.inj (htheta.symm.trans he')
    have hmissTheta : D.theta ∉ MissingColors G phi
        (T.vertex D.penultimateVertexIndex) := D.thetaPresentPenultimate
    have := hmissTheta
    exact this (hta.symm ▸ D.alphaMissingPenultimate)
  · have htlt : t.val < T.length - 1 := by omega
    let i : Fin (HierarchyFullTailPrefix C (ell - 1)).length :=
      ⟨t.val, by rw [hlast]; omega⟩
    have hiA : A.length ≤ i.val := by
      change A.length ≤ t.val
      exact ht
    have hi : i.val < A.length + (ell - 1) := by
      change t.val < A.length + (ell - 1)
      have hsum : A.length + ell = T.length := by omega
      omega
    have hmi : D.alpha ∈ MissingColors G phi
        ((HierarchyFullTailPrefix C (ell - 1)).vertex
          (Fin.last (HierarchyFullTailPrefix C (ell - 1)).length)) := by
      have hvtx :
          (HierarchyFullTailPrefix C (ell - 1)).vertex
              (Fin.last (HierarchyFullTailPrefix C (ell - 1)).length) =
            T.vertex D.penultimateVertexIndex := by
        change T.vertex _ = _
        apply congrArg T.vertex
        apply Fin.ext
        change (Fin.last (HierarchyFullTailPrefix C (ell - 1)).length).val =
          D.penultimateVertexIndex.val
        simp only [Fin.val_last]
        rw [hlast]
        have hp := D.penultimateVertexPosition
        omega
      rw [hvtx]
      exact D.alphaMissingPenultimate
    have htail := HierarchyTailMissingColorExclusion G k e0 input T phi ett base H helem
    have hone : 1 ≤ ell - 1 := by omega
    have hltell : ell - 1 < ell := by omega
    have hcon := htail (ell - 1) hone hltell D.alpha hmi i
      hiA hi
    intro he
    have hcase := hcon he
    have hex := hcase.2.2.2
    obtain ⟨f, _, _, _, _, _, hstored⟩ := hex
    exact halphaStored hstored
