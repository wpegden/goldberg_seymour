import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ExtendedTashkinovTree
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyNonparallelFirstEdge
import Tablet.HierarchySituationTwoReorderedTrees
import Tablet.HierarchySituationTwoTailData
import Tablet.HierarchyStarredStage
import Tablet.Incident
import Tablet.TashkinovHierarchy
import Tablet.MaximumPropertyTransport
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumProperty
import Tablet.ModColoring
import Tablet.OrderedTreeUnion
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovAugmentation
import Tablet.TashkinovClosure
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.Td
import Tablet.StableColoring
import Tablet.TreeMissingColors
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceEdgeSet
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequence
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.sc1
import Tablet.HierarchyBaseCorrespondingTransport
import Tablet.TreeSequenceBoundaryEdgeAppendExists
import Tablet.TreeSequenceAdjoinEdgeUnique
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.TashkinovAugmentationSequenceSuffix

-- [TABLET NODE: HierarchySituationTwoReorderedTreesCertified]
theorem HierarchySituationTwoReorderedTreesCertified {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoTailData
      G k e0 input T phi ett base C ctx) :
    ∃ R : HierarchySituationTwoReorderedTrees
        G k e0 input T phi ett base C ctx D,
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let Tn := ett.series.data.tree n.castSucc
      let B := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 2)
      (B = Tn →
          ett.series.data.kind n = some TashkinovExtensionKind.PE) ∧
        ((ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
            TashkinovAugmentationSequence phi Tn R.minus) ∨
          ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
              ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
            ∃ (f : E) (seed : TreeSequence G e0),
              ett.series.data.connectingEdges n = {f} ∧
                TreeSequenceAdjoinEdge Tn f seed ∧
                TashkinovAugmentationSequence phi seed R.minus)) ∧
        ((ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
            TashkinovAugmentationSequence phi Tn R.star) ∨
          ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
              ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
            ∃ (f : E) (seed : TreeSequence G e0),
              ett.series.data.connectingEdges n = {f} ∧
                TreeSequenceAdjoinEdge Tn f seed ∧
                TashkinovAugmentationSequence phi seed R.star)) ∧
        ∃ corrMinus : CorrespondingExtendedTashkinovTree
            G k e0 ett phi R.minus,
          MaximumProperty corrMinus.replacementETT ∧
            ∃ baseMinus : HierarchyBase corrMinus.replacementETT phi,
              baseMinus.core = base.core ∧
                baseMinus.closure = base.closure ∧
                baseMinus.supportPosition.val = base.supportPosition.val ∧
                ∃ HMinus : TashkinovHierarchy
                    corrMinus.replacementETT baseMinus,
                  ∃ hMinusCount :
                      HMinus.dividerCount = C.hierarchy.dividerCount,
                    (∀ j : Fin (HMinus.dividerCount + 1),
                        HMinus.stage j.castSucc =
                          C.hierarchy.stage
                            (Fin.cast
                              (congrArg (fun d => d + 1) hMinusCount) j).castSucc) ∧
                      (∀ j : Fin HMinus.dividerCount,
                        (HMinus.dividerPosition j).val =
                          (C.hierarchy.dividerPosition
                            (Fin.cast hMinusCount j)).val) ∧
                      ∃ corrStar : CorrespondingExtendedTashkinovTree
                          G k e0 ett phi R.star,
                        MaximumProperty corrStar.replacementETT ∧
                          ∃ baseStar : HierarchyBase
                              corrStar.replacementETT phi,
                            baseStar.core = base.core ∧
                              baseStar.closure = base.closure ∧
                              baseStar.supportPosition.val =
                                base.supportPosition.val ∧
                              ∃ HStar : TashkinovHierarchy
                                  corrStar.replacementETT baseStar,
                                ∃ hStarCount :
                                    HStar.dividerCount =
                                      C.hierarchy.dividerCount,
                                  (∀ j : Fin (HStar.dividerCount + 1),
                                      HStar.stage j.castSucc =
                                        C.hierarchy.stage
                                          (Fin.cast
                                            (congrArg (fun d => d + 1)
                                              hStarCount) j).castSucc) ∧
                                    ∀ j : Fin HStar.dividerCount,
                                      (HStar.dividerPosition j).val =
                                        (C.hierarchy.dividerPosition
                                          (Fin.cast hStarCount j)).val := by
-- BODY
  classical
  let H := C.hierarchy
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  let ell := HierarchyFullTailLength C
  let B := HierarchyFullTailPrefix C (ell - 2)
  let P := HierarchyFullTailPrefix C (ell - 1)
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  -- Exact ordered prefixes will be used for both route restriction and hierarchy copying.
  have segmentRefl (X : TreeSequence G e0) : TreeSequenceInitialSegment X X :=
    ⟨le_rfl, (fun _ => rfl), (fun _ => rfl)⟩
  have segmentTrans {X Y Z : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y)
      (hYZ : TreeSequenceInitialSegment Y Z) :
      TreeSequenceInitialSegment X Z := by
    rcases hXY with ⟨hxy, vxy, exy⟩
    rcases hYZ with ⟨hyz, vyz, eyz⟩
    refine ⟨le_trans hxy hyz, ?_, ?_⟩
    · intro i
      simpa using (vyz (Fin.castLE (Nat.succ_le_succ hxy) i)).trans (vxy i)
    · intro i
      simpa using (eyz (Fin.castLE hxy i)).trans (exy i)
  have commonPrefix {X Y Z : TreeSequence G e0}
      (hXZ : TreeSequenceInitialSegment X Z)
      (hYZ : TreeSequenceInitialSegment Y Z) (hXY : X.length ≤ Y.length) :
      TreeSequenceInitialSegment X Y := by
    refine ⟨hXY, ?_, ?_⟩
    · intro i
      have hv := hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY) i)
      exact hv.symm.trans (by simpa using hXZ.2.1 i)
    · intro i
      have he := hYZ.2.2 (Fin.castLE hXY i)
      exact he.symm.trans (by simpa using hXZ.2.2 i)
  have equalTrees {X Y : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y) (hlen : X.length = Y.length) :
      X = Y := by
    cases X with
    | mk lx px vx ex vix eix fx ax =>
      cases Y with
      | mk ly py vy ey viy eiy fy ay =>
        simp only at hlen
        subst ly
        rw [TreeSequence.mk.injEq]
        refine ⟨rfl, ?_, ?_⟩
        · apply heq_of_eq
          funext i
          simpa only [Fin.castLE] using (hXY.2.1 i).symm
        · apply heq_of_eq
          funext i
          simpa only [Fin.castLE] using (hXY.2.2 i).symm
  have prefixSegment (X : TreeSequence G e0) (r : ℕ)
      (hr : 1 ≤ r) (hx : r ≤ X.length) :
      TreeSequenceInitialSegment (TreeSequencePrefix X r hr hx) X :=
    ⟨hx, (fun _ => rfl), (fun _ => rfl)⟩
  have prefixEq {X Y : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y) :
      X = TreeSequencePrefix Y X.length X.positive hXY.1 := by
    apply equalTrees
      (commonPrefix hXY (prefixSegment Y X.length X.positive hXY.1) le_rfl)
    rfl
  have stageSegment : ∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + 1),
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
        (H.stage ⟨a + d, by omega⟩) := by
    intro a d
    induction d with
    | zero => intro hbound; exact segmentRefl _
    | succ d ih =>
      intro hbound
      exact segmentTrans (ih (by omega))
        (by
          convert H.nested ⟨a + d, by omega⟩ using 1 <;>
            congr 1)
  have stageToT (i : Fin (H.dividerCount + 2)) :
      TreeSequenceInitialSegment (H.stage i) T := by
    have hs := stageSegment i.val (H.dividerCount + 1 - i.val) (by omega)
    have hi : (⟨i.val + (H.dividerCount + 1 - i.val), by omega⟩ :
        Fin (H.dividerCount + 2)) = Fin.last (H.dividerCount + 1) := by
      apply Fin.ext
      simp
      omega
    simpa [hi, H.terminalStage] using hs
  have hAstage (hq : 0 < H.dividerCount) :
      A = H.stage ⟨H.dividerCount, by omega⟩ := by
    have hi : (Fin.last H.dividerCount : Fin (H.dividerCount + 1)) =
        (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ := by
      apply Fin.ext
      simp
      omega
    dsimp [A, HierarchyStarredStage]
    rw [hi]
    simp only [Fin.cases]
    apply congrArg H.stage
    apply Fin.ext
    simp
    omega
  have hAcore (hq : H.dividerCount = 0) : A = base.core := by
    simp [A, HierarchyStarredStage, Fin.last, hq]
  have hAT : TreeSequenceInitialSegment A T := by
    by_cases hq : H.dividerCount = 0
    · rw [hAcore hq]
      exact segmentTrans H.coreInsideFirst (stageToT _)
    · rw [hAstage (by omega)]
      exact stageToT _
  have hcoreA : TreeSequenceInitialSegment base.core A := by
    by_cases hq : H.dividerCount = 0
    · rw [hAcore hq]; exact segmentRefl _
    · rw [hAstage (by omega)]
      exact segmentTrans H.coreInsideFirst
        (by
          convert stageSegment 1 (H.dividerCount - 1) (by omega) using 1
          congr 1
          apply Fin.ext
          simp
          omega)
  have hell : ell = T.length - A.length := rfl
  have htwo : 2 ≤ ell := D.tailAtLeastTwo
  have hAlen : A.length ≤ T.length := hAT.1
  have hBlen : B.length = T.length - 2 := by
    change min (A.length + (ell - 2)) T.length = T.length - 2
    omega
  have hPlen : P.length = T.length - 1 := by
    change min (A.length + (ell - 1)) T.length = T.length - 1
    omega
  have hm : 3 ≤ T.length := by have := A.positive; omega
  have hBT : TreeSequenceInitialSegment B T := prefixSegment _ _ _ _
  have hPT : TreeSequenceInitialSegment P T := prefixSegment _ _ _ _
  have hBP : TreeSequenceInitialSegment B P := commonPrefix hBT hPT (by omega)
  have hAB : TreeSequenceInitialSegment A B := commonPrefix hAT hBT (by omega)
  have hTnB : TreeSequenceInitialSegment Tn B := by
    have hncore : TreeSequenceInitialSegment Tn base.core := by
      by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
      · obtain ⟨U⟩ := (base.parallel hp).2.2
        exact U.leftSegment
      · rw [base.nonparallel hp]; exact segmentRefl _
    exact segmentTrans hncore (segmentTrans hcoreA hAB)
  let r : Fin T.length := ⟨T.length - 2, by omega⟩
  let f := T.edge r
  let g := T.edge D.lastEdgeIndex
  let y := T.vertex D.penultimateVertexIndex
  let z := T.vertex D.terminalVertexIndex
  have hr : r.val + 2 = T.length := by dsimp [r]; omega
  have hgpos := D.lastEdgePosition
  have hypos := D.penultimateVertexPosition
  have hzpos := D.terminalVertexPosition
  have hOrigP : TreeSequenceAdjoinEdge B f P := by
    refine ⟨by omega, hBP, ?_⟩
    change T.edge _ = T.edge r
    congr 1
    apply Fin.ext
    change B.length = r.val
    omega
  have hOrigT : TreeSequenceAdjoinEdge P g T := by
    refine ⟨by omega, hPT, ?_⟩
    apply congrArg T.edge
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_last]
    omega
  have hPy : P.vertex (Fin.last P.length) = y := by
    change T.vertex _ = T.vertex D.penultimateVertexIndex
    congr 1
    apply Fin.ext
    change P.length = D.penultimateVertexIndex.val
    omega
  have hTz : T.vertex (Fin.last T.length) = z := by
    apply congrArg T.vertex
    apply Fin.ext
    exact hzpos.symm
  have vertexMem (X : TreeSequence G e0) (i : Fin (X.length + 1)) :
      X.vertex i ∈ TreeSequenceVertexSet X := by simp [TreeSequenceVertexSet]
  have freshLast {X U : TreeSequence G e0} {e : E}
      (ha : TreeSequenceAdjoinEdge X e U) :
      U.vertex (Fin.last U.length) ∉ TreeSequenceVertexSet X := by
    rcases ha with ⟨hl, hs, he⟩
    intro hv
    obtain ⟨i, hi⟩ := by simpa [TreeSequenceVertexSet] using hv
    have hh := U.vertex_injective ((hs.2.1 i).trans hi)
    have hhval := congrArg Fin.val hh
    simp only [Fin.val_castLE, Fin.val_last] at hhval
    omega
  have adjoinSets {X U : TreeSequence G e0} {e : E}
      (ha : TreeSequenceAdjoinEdge X e U) :
      TreeSequenceVertexSet U = insert (U.vertex (Fin.last U.length))
          (TreeSequenceVertexSet X) ∧
        TreeSequenceEdgeSet U = insert e (TreeSequenceEdgeSet X) := by
    rcases ha with ⟨hl, hs, he⟩
    constructor
    · ext v
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
        true_and, Finset.mem_insert]
      constructor
      · rintro ⟨i, rfl⟩
        by_cases hi : i.val < X.length + 1
        · right
          exact ⟨⟨i.val, hi⟩, (hs.2.1 ⟨i.val, hi⟩).symm⟩
        · left
          congr 1
          apply Fin.ext
          simp
          omega
      · rintro (hv | ⟨i, rfl⟩)
        · exact ⟨Fin.last U.length, hv.symm⟩
        · exact ⟨Fin.castLE (Nat.succ_le_succ hs.1) i, hs.2.1 i⟩
    · ext e'
      simp only [TreeSequenceEdgeSet, Finset.mem_image, Finset.mem_univ,
        true_and, Finset.mem_insert]
      constructor
      · rintro ⟨i, rfl⟩
        by_cases hi : i.val < X.length
        · right
          exact ⟨⟨i.val, hi⟩, (hs.2.2 ⟨i.val, hi⟩).symm⟩
        · left
          have hi' : i = Fin.cast hl.symm (Fin.last X.length) := by
            apply Fin.ext
            simp
            omega
          exact hi' ▸ he
      · rintro (hv | ⟨i, rfl⟩)
        · exact ⟨Fin.cast hl.symm (Fin.last X.length), he.trans hv.symm⟩
        · exact ⟨Fin.castLE hs.1 i, hs.2.2 i⟩
  have adjoinVertex {X U : TreeSequence G e0} {e : E} {v w : V}
      (ha : TreeSequenceAdjoinEdge X e U)
      (hv : v ∉ TreeSequenceVertexSet X) (hw : w ∈ TreeSequenceVertexSet X)
      (hends : G.ends e = s(v, w)) : U.vertex (Fin.last U.length) = v := by
    rcases ha with ⟨hl, hs, he⟩
    obtain ⟨i, hi⟩ := U.attaches (Fin.cast hl.symm (Fin.last X.length))
    have hil : i.val < X.length + 1 := by simpa using i.isLt
    let ix : Fin (X.length + 1) := ⟨i.val, hil⟩
    have hvold : U.vertex (Fin.castLT i (by omega)) = X.vertex ix := hs.2.1 ix
    have hnew : (Fin.cast hl.symm (Fin.last X.length)).succ =
        Fin.last U.length := by apply Fin.ext; simp; omega
    rw [he, hnew, hvold] at hi
    rcases Sym2.eq_iff.mp (hi.symm.trans hends) with hh | hh
    · exact hh.1
    · exact False.elim (hv (hh.2 ▸ vertexMem X ix))
  have hzB : z ∉ TreeSequenceVertexSet B := by
    intro hz
    obtain ⟨i, hi⟩ := by simpa [TreeSequenceVertexSet] using hz
    have hidx := T.vertex_injective ((hBT.2.1 i).trans hi)
    have hv := congrArg Fin.val hidx
    simp only [Fin.val_castLE] at hv
    omega
  have hyB : y ∉ TreeSequenceVertexSet B := by
    rw [← hPy]
    exact freshLast hOrigP
  have hyz : y ≠ z := by
    intro hh
    have hi := congrArg Fin.val (T.vertex_injective hh)
    omega
  obtain ⟨ig, hig⟩ := T.attaches D.lastEdgeIndex
  have higbound : ig.val < B.length + 1 := by
    have hine : ig.val ≠ D.penultimateVertexIndex.val := by
      intro hh
      apply D.lastEdgeNotIncidentPenultimate
      change T.vertex D.penultimateVertexIndex ∈ G.ends g
      rw [hig]
      apply Sym2.mem_iff.mpr
      right
      congr 1
      apply Fin.ext
      exact hh.symm
    omega
  let igB : Fin (B.length + 1) := ⟨ig.val, higbound⟩
  have hgends : G.ends g = s(z, B.vertex igB) := by
    have hnew : D.lastEdgeIndex.succ = D.terminalVertexIndex := by
      apply Fin.ext
      simp
      omega
    rw [← hBT.2.1 igB]
    convert hig using 1
    · exact congrArg (fun i => s(T.vertex i, T.vertex (Fin.castLE (Nat.succ_le_succ hBT.1) igB))) hnew.symm
  have hgBoundary : g ∈ BoundaryEdges G (TreeSequenceVertexSet B) := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨B.vertex igB, vertexMem _ _, z, hzB, ?_⟩
    exact hgends.trans (Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩))
  obtain ⟨M, hBM⟩ := TreeSequenceBoundaryEdgeAppendExists B g hgBoundary
  -- The adjoin relation fixes the edge; the endpoint argument fixes its fresh vertex.
  have hMz : M.vertex (Fin.last M.length) = z :=
    adjoinVertex hBM hzB (vertexMem B igB) hgends
  have hMV : TreeSequenceVertexSet M = insert z (TreeSequenceVertexSet B) := by
    simpa [hMz] using (adjoinSets hBM).1
  have hME : TreeSequenceEdgeSet M = insert g (TreeSequenceEdgeSet B) :=
    (adjoinSets hBM).2
  have hyM : y ∉ TreeSequenceVertexSet M := by simpa [hMV, hyz] using hyB
  obtain ⟨if_, hif⟩ := T.attaches r
  have hifbound : if_.val < B.length + 1 := by have := if_.isLt; omega
  let ifB : Fin (B.length + 1) := ⟨if_.val, hifbound⟩
  have hfends : G.ends f = s(y, B.vertex ifB) := by
    have hnew : r.succ = D.penultimateVertexIndex := by
      apply Fin.ext
      simp
      omega
    rw [← hBT.2.1 ifB]
    convert hif using 1
    · exact congrArg (fun i => s(T.vertex i, T.vertex (Fin.castLE (Nat.succ_le_succ hBT.1) ifB))) hnew.symm
  have hfBoundary : f ∈ BoundaryEdges G (TreeSequenceVertexSet M) := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨B.vertex ifB, ?_, y, hyM, ?_⟩
    · rw [hMV]; exact Finset.mem_insert_of_mem (vertexMem _ _)
    · exact hfends.trans (Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩))
  obtain ⟨S, hMS⟩ := TreeSequenceBoundaryEdgeAppendExists M f hfBoundary
  have hSy : S.vertex (Fin.last S.length) = y := by
    apply adjoinVertex hMS hyM
    · rw [hMV]; exact Finset.mem_insert_of_mem (vertexMem B ifB)
    · exact hfends
  have hPV : TreeSequenceVertexSet P = insert y (TreeSequenceVertexSet B) := by
    simpa [hPy] using (adjoinSets hOrigP).1
  have hPE : TreeSequenceEdgeSet P = insert f (TreeSequenceEdgeSet B) :=
    (adjoinSets hOrigP).2
  have hTV : TreeSequenceVertexSet T = insert z (insert y (TreeSequenceVertexSet B)) := by
    simpa [hTz, hPV] using (adjoinSets hOrigT).1
  have hTE : TreeSequenceEdgeSet T = insert g (insert f (TreeSequenceEdgeSet B)) := by
    simpa [hPE] using (adjoinSets hOrigT).2
  have hfB : f ∉ TreeSequenceEdgeSet B := by
    intro hf
    obtain ⟨i, hi⟩ := by simpa [TreeSequenceEdgeSet] using hf
    have hidx := congrArg Fin.val (T.edge_injective ((hBT.2.2 i).trans hi))
    simp only [Fin.val_castLE] at hidx
    omega
  have hfg : f ≠ g := by
    intro hh
    have hi := congrArg Fin.val (T.edge_injective hh)
    omega
  let R : HierarchySituationTwoReorderedTrees
      G k e0 input T phi ett base C ctx D :=
    { penultimateEdgeIndex := r
      penultimateEdgePosition := hr
      minus := M
      star := S
      originalPenultimate := hOrigP
      originalFinal := hOrigT
      minusFinal := hBM
      minusTerminalVertex := hMz
      starFinal := hMS
      starPenultimateVertex := hSy
      minusVertexSet := by
        rw [hMV, hTV]
        ext v
        simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_insert]
        constructor
        · intro hv
          refine ⟨hv.elim Or.inl (fun h => Or.inr (Or.inr h)), ?_⟩
          intro hh
          change v = y at hh
          rcases hv with hv | hv
          · exact hyz (hh.symm.trans hv)
          · exact hyB (hh ▸ hv)
        · rintro ⟨hv, hn⟩
          rcases hv with hv | hv | hv
          · exact Or.inl hv
          · exact False.elim (hn hv)
          · exact Or.inr hv
      minusEdgeSet := by
        rw [hME, hTE]
        ext e
        simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_insert]
        constructor
        · intro he
          refine ⟨he.elim Or.inl (fun h => Or.inr (Or.inr h)), ?_⟩
          intro hh
          change e = f at hh
          rcases he with he | he
          · exact hfg (hh.symm.trans he)
          · exact hfB (hh ▸ he)
        · rintro ⟨he, hn⟩
          rcases he with he | he | he
          · exact Or.inl he
          · exact False.elim (hn he)
          · exact Or.inr he
      starVertexSet := by
        rw [(adjoinSets hMS).1, hSy, hMV, hTV]
        exact Finset.insert_comm _ _ _
      starEdgeSet := by
        rw [(adjoinSets hMS).2, hME, hTE]
        exact Finset.insert_comm _ _ _ }
  have stableClosed (X : TreeSequence G e0) (colors : Finset (Fin k))
      (old new : PartialEdgeColoring E k)
      (ho : IsProperEdgeColoring G old) (huo : IsOneEdgeUncolored old e0)
      (hn : IsProperEdgeColoring G new) (hun : IsOneEdgeUncolored new e0)
      (hstable : StableColoring X colors old new)
      (hclosed : ColoredVertexSetClosed G old (TreeSequenceVertexSet X)) :
      ColoredVertexSetClosed G new (TreeSequenceVertexSet X) := by
    intro e c v he hv hc hmissing
    have hmold : c ∈ MissingColors G old v := by
      rw [← hstable.2 v hv]
      exact hmissing
    have hmTree : c ∈ TreeMissingColors old X := by
      simp only [TreeMissingColors, Finset.mem_biUnion]
      exact ⟨v, hv, hmold⟩
    obtain ⟨u, hu, w, hw, hends⟩ := by
      simpa only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] using he
    have hinc : TreeIncidentEdge X e := by
      refine ⟨u, hu, ?_⟩
      change u ∈ G.ends e
      rw [hends]
      exact Sym2.mem_iff.mpr (Or.inl rfl)
    have heq := (sc1 G e0 X colors old new ho huo hn hun).mp hstable e hinc
      (Or.inr ⟨c, Finset.mem_union_left _ hmTree, hc⟩)
    exact hclosed he hv (heq.symm.trans hc) hmold
  have stepRoute (j : Fin (ett.rounds + 1)) (hj : j ≠ 0) :
      (ett.series.data.kind j = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence (ett.series.data.coloring j)
          (ett.series.data.tree j.castSucc) (ett.series.data.tree j.succ)) ∨
      ((ett.series.data.kind j = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind j = some TashkinovExtensionKind.RE) ∧
        ColoredVertexSetClosed G (ett.series.data.coloring j)
          (TreeSequenceVertexSet (ett.series.data.tree j.castSucc)) ∧
        ∃ (e : E) (seed : TreeSequence G e0),
          ett.series.data.connectingEdges j = {e} ∧
          TreeSequenceAdjoinEdge (ett.series.data.tree j.castSucc) e seed ∧
          TashkinovAugmentationSequence (ett.series.data.coloring j)
            seed (ett.series.data.tree j.succ)) := by
    cases ett.series.certified j with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure => exact False.elim (hj rfl)
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      refine Or.inr ⟨Or.inl currentKind, ?_, choice.edge, adjoined,
        currentEdges, adjoinedExactly, closedExtension.1⟩
      rw [currentColoring]
      exact stableClosed _ _ _ _ previousProper previousOneUncolored
        choice.selectedProper choice.selectedOneUncolored
        choice.selectedStable previousClosed
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
      exact Or.inl ⟨currentKind, closedExtension.1⟩
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      refine Or.inr ⟨Or.inr currentKind, ?_, available.edge, adjoined,
        currentEdges, adjoinedExactly, closedExtension.1⟩
      rw [currentColoring]
      exact previousClosed
  let Z := ett.series.data.tree n.succ
  have hTZ : TreeSequenceInitialSegment T Z := by
    convert ett.belowFinal using 1
    apply congrArg ett.series.data.tree
    apply Fin.ext
    rfl
  have hnzero : n ≠ 0 := by
    intro hn
    have hv := congrArg Fin.val hn
    have hp := C.positive
    simp [n] at hv
    omega
  have terminalRoute := stepRoute n hnzero
  rw [← ett.generatingColoring] at terminalRoute
  change (ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
      TashkinovAugmentationSequence phi Tn Z) ∨
    ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
      ColoredVertexSetClosed G phi (TreeSequenceVertexSet Tn) ∧
      ∃ (e : E) (seed : TreeSequence G e0),
        ett.series.data.connectingEdges n = {e} ∧
          TreeSequenceAdjoinEdge Tn e seed ∧
          TashkinovAugmentationSequence phi seed Z) at terminalRoute
  have seedToT (e : E) (seed : TreeSequence G e0)
      (hkind : ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind n = some TashkinovExtensionKind.RE)
      (he : ett.series.data.connectingEdges n = {e})
      (ha : TreeSequenceAdjoinEdge Tn e seed) :
      TreeSequenceInitialSegment seed T := by
    obtain ⟨ie, hie, hentry⟩ := HierarchyNonparallelFirstEdge H e hkind he
    change ie.val = Tn.length at hie
    have ht := stageToT (⟨1, by omega⟩ : Fin (H.dividerCount + 2))
    have hentryT : T.edge (Fin.castLE ht.1 ie) = e :=
      (ht.2.2 ie).trans hentry
    have hN : Tn.length < T.length := by
      have hlt := ie.isLt
      have hle := ht.1
      omega
    let Q := TreeSequencePrefix T (Tn.length + 1) (by omega) (by omega)
    have hQT : TreeSequenceInitialSegment Q T := prefixSegment _ _ _ _
    have hNQ : TreeSequenceInitialSegment Tn Q :=
      commonPrefix (segmentTrans hTnB hBT) hQT (by change Tn.length ≤ Tn.length + 1; omega)
    have hQ : TreeSequenceAdjoinEdge Tn e Q := by
      refine ⟨rfl, hNQ, ?_⟩
      change T.edge _ = e
      convert hentryT using 1
      congr 1
      apply Fin.ext
      exact hie.symm
    have hseed : seed = Q := TreeSequenceAdjoinEdgeUnique Tn e seed Q ha hQ
    rw [hseed]
    exact hQT
  have oneStep {X Y : TreeSequence G e0}
      (hseq : TashkinovAugmentationSequence phi X Y)
      (hlen : Y.length = X.length + 1) : TashkinovAugmentation phi X Y := by
    unfold TashkinovAugmentationSequence at hseq
    induction hseq with
    | refl => omega
    | @tail W Y hXW hWY ih =>
      have hp := TashkinovAugmentationSequenceInitialSegment phi X W hXW
      have hwlen : X.length = W.length := by have := hWY.1; have := hp.1; omega
      have heq := equalTrees hp hwlen
      subst W
      exact hWY
  have hfinalAug : TashkinovAugmentation phi P T := by
    rcases terminalRoute with ⟨hp, hseq⟩ | ⟨hk, hc, e, seed, he, ha, hseq⟩
    · have hNT := segmentTrans hTnB hBT
      have hseqT := TashkinovAugmentationSequenceRestrict phi Tn T Z hseq hNT hTZ
      have hseqP := TashkinovAugmentationSequenceSuffix phi Tn P T hseqT
        (segmentTrans hTnB hBP) hPT
      exact oneStep hseqP (by omega)
    · have hseedT := seedToT e seed hk he ha
      have hseqT := TashkinovAugmentationSequenceRestrict phi seed T Z hseq hseedT hTZ
      have hseedP : TreeSequenceInitialSegment seed P :=
        commonPrefix hseedT hPT (by have := ha.1; have := hTnB.1; omega)
      have hseqP := TashkinovAugmentationSequenceSuffix phi seed P T hseqT hseedP hPT
      exact oneStep hseqP (by omega)
  have hthetaP : D.theta ∈ TreeMissingColors phi P := by
    rcases hfinalAug with ⟨hl, hs, c, he, hc⟩
    have heg : T.edge (Fin.cast hl.symm (Fin.last P.length)) = g := hOrigT.choose_spec.2
    rw [heg, D.thetaOnLastEdge] at he
    have hct : D.theta = c := Option.some.inj he
    exact hct.symm ▸ hc
  have hthetaB : D.theta ∈ TreeMissingColors phi B := by
    obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp hthetaP
    rw [hPV] at hv
    rcases Finset.mem_insert.mp hv with hv | hv
    · subst v
      exact False.elim (D.thetaPresentPenultimate hc)
    · exact Finset.mem_biUnion.mpr ⟨v, hv, hc⟩
  -- A nonparallel terminal seed cannot begin exactly at B: its old tree is closed.
  have hboundaryPE : B = Tn → ett.series.data.kind n = some TashkinovExtensionKind.PE := by
    intro hBN
    rcases terminalRoute with ⟨hp, hseq⟩ | ⟨hk, hc, e, seed, he, ha, hseq⟩
    · exact hp
    · obtain ⟨v, hv, hmissing⟩ := Finset.mem_biUnion.mp hthetaB
      rw [← hBN] at hc
      exact False.elim (hc hgBoundary hv D.thetaOnLastEdge hmissing)
  have augmentOfAdjoin {X U : TreeSequence G e0} {e : E} {c : Fin k}
      (ha : TreeSequenceAdjoinEdge X e U) (he : phi e = some c)
      (hc : c ∈ TreeMissingColors phi X) : TashkinovAugmentation phi X U := by
    rcases ha with ⟨hl, hs, hedge⟩
    exact ⟨hl, hs, c, hedge ▸ he, hc⟩
  have hBMaug : TashkinovAugmentation phi B M :=
    augmentOfAdjoin hBM D.thetaOnLastEdge hthetaB
  have routes :
      ((ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence phi Tn M) ∨
        ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (e : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges n = {e} ∧
              TreeSequenceAdjoinEdge Tn e seed ∧
              TashkinovAugmentationSequence phi seed M)) ∧
      ((ett.series.data.kind n = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence phi Tn S) ∨
        ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) ∧
          ∃ (e : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges n = {e} ∧
              TreeSequenceAdjoinEdge Tn e seed ∧
              TashkinovAugmentationSequence phi seed S)) := by
    have extendRoute (source : TreeSequence G e0)
        (hsourceB : TreeSequenceInitialSegment source B)
        (hseqT : TashkinovAugmentationSequence phi source T) :
        TashkinovAugmentationSequence phi source M ∧
          TashkinovAugmentationSequence phi source S := by
      have hseqB := TashkinovAugmentationSequenceRestrict phi source B T hseqT hsourceB hBT
      have hseqBT := TashkinovAugmentationSequenceSuffix phi source B T hseqT hsourceB hBT
      have hseqBP := TashkinovAugmentationSequenceRestrict phi B P T hseqBT hBP hPT
      have hBPaug := oneStep hseqBP (by omega)
      rcases hBPaug with ⟨hl, hs, c, he, hc⟩
      have hef : P.edge (Fin.cast hl.symm (Fin.last B.length)) = f := hOrigP.choose_spec.2
      have hcM : c ∈ TreeMissingColors phi M := by
        obtain ⟨v, hv, hmissing⟩ := Finset.mem_biUnion.mp hc
        exact Finset.mem_biUnion.mpr
          ⟨v, TreeSequenceInitialSegmentVertexSetSubset hBM.choose_spec.1 hv, hmissing⟩
      have hMSaug := augmentOfAdjoin hMS (hef ▸ he) hcM
      have hseqM : TashkinovAugmentationSequence phi source M :=
        Relation.ReflTransGen.tail hseqB hBMaug
      exact ⟨hseqM, Relation.ReflTransGen.tail hseqM hMSaug⟩
    rcases terminalRoute with ⟨hp, hseq⟩ | ⟨hk, hc, e, seed, he, ha, hseq⟩
    · have hseqT := TashkinovAugmentationSequenceRestrict phi Tn T Z hseq
        (segmentTrans hTnB hBT) hTZ
      obtain ⟨hm, hs⟩ := extendRoute Tn hTnB hseqT
      exact ⟨Or.inl ⟨hp, hm⟩, Or.inl ⟨hp, hs⟩⟩
    · have hBN : B ≠ Tn := by
        intro hBN
        have hPE := hboundaryPE hBN
        rcases hk with hk | hk <;> rw [hk] at hPE <;> cases hPE
      have hstrict : Tn.length < B.length := by
        have hle := hTnB.1
        by_contra hn
        exact hBN (equalTrees hTnB (by omega)).symm
      have hseedT := seedToT e seed hk he ha
      have hseedB := commonPrefix hseedT hBT (by have := ha.1; omega)
      have hseqT := TashkinovAugmentationSequenceRestrict phi seed T Z hseq hseedT hTZ
      obtain ⟨hm, hs⟩ := extendRoute seed hseedB hseqT
      exact ⟨Or.inr ⟨hk, e, seed, he, ha, hm⟩, Or.inr ⟨hk, e, seed, he, ha, hs⟩⟩
  have hmod : ModColoring ett phi := by
    apply Td G k e0 input T phi ett C.maximum C.positive ctx.lowerRung phi
      ctx.proper ctx.oneEdgeUncolored
    rw [← ett.generatingColoring]
    exact ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩
  have hNM : TreeSequenceInitialSegment Tn M :=
    segmentTrans hTnB hBM.choose_spec.1
  have hNS : TreeSequenceInitialSegment Tn S :=
    segmentTrans hNM hMS.choose_spec.1
  have hMlen : M.length = B.length + 1 := hBM.choose
  have hSlen : S.length = M.length + 1 := hMS.choose
  obtain ⟨corrM⟩ := hmod.2.2 M hNM
    (by change Tn.length < M.length; have := hTnB.1; omega) routes.1
  obtain ⟨corrS⟩ := hmod.2.2 S hNS
    (by change Tn.length < S.length; have := hTnB.1; omega) routes.2
  have hMPM := MaximumPropertyTransport G k e0 ett phi hmod M corrM C.maximum
  have hMPS := MaximumPropertyTransport G k e0 ett phi hmod S corrS C.maximum
  have hlastB : TreeSequenceInitialSegment
      (H.stage (Fin.last H.dividerCount).castSucc) B := by
    by_cases hq : H.dividerCount = 0
    · have hi : (Fin.last H.dividerCount).castSucc =
          (0 : Fin (H.dividerCount + 2)) := by
        apply Fin.ext
        simp [hq]
      rw [hi, H.baseStage]
      exact hTnB
    · have hi : (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) =
          (Fin.last H.dividerCount).castSucc := by apply Fin.ext; rfl
      rw [← hi, ← hAstage (by omega)]
      exact hAB
  have hstageB (i : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (H.stage i.castSucc) B := by
    have hs := stageSegment i.val (H.dividerCount - i.val) (by omega)
    have hfirst : (⟨i.val, by omega⟩ : Fin (H.dividerCount + 2)) = i.castSucc := by
      apply Fin.ext
      rfl
    have hlast : (⟨i.val + (H.dividerCount - i.val), by omega⟩ :
        Fin (H.dividerCount + 2)) = (Fin.last H.dividerCount).castSucc := by
      apply Fin.ext
      simp
      omega
    rw [hfirst, hlast] at hs
    exact segmentTrans hs hlastB
  have terminalTree (X : TreeSequence G e0)
      (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi X) :
      corr.replacementETT.series.data.tree
        (Fin.last corr.replacementETT.rounds).castSucc = Tn := by
    rcases corr with ⟨replacementInput, replacementSeries, replacementETT,
      rungAgreement, seriesPresentation, finalGeneratingColoring,
      ladderTreesAgree, storedColorsAgree, connectingEdgesAgree,
      extensionKindsAgree, replacementProper, replacementOneUncolored,
      replacementStable⟩
    cases replacementETT with
    | mk rounds roundsPositive replacementData above strict below generating =>
      cases rungAgreement
      have hseries : replacementData = replacementSeries := eq_of_heq seriesPresentation
      cases hseries
      let i : Fin ett.rounds := ⟨ett.rounds - 1, by have := ett.roundsPositive; omega⟩
      have hi : i.succ = n := by
        apply Fin.ext
        dsimp [i, n]
        have := ett.roundsPositive
        omega
      change replacementSeries.data.tree n.castSucc = ett.series.data.tree n.castSucc
      rw [← hi]
      exact ladderTreesAgree i
  have copyHierarchy (X : TreeSequence G e0)
      (corr : CorrespondingExtendedTashkinovTree G k e0 ett phi X)
      (hBX : TreeSequenceInitialSegment B X) (hstrictBX : B.length < X.length) :
      ∃ bx : HierarchyBase corr.replacementETT phi,
        bx.core = base.core ∧ bx.closure = base.closure ∧
        bx.supportPosition.val = base.supportPosition.val ∧
        ∃ K : TashkinovHierarchy corr.replacementETT bx,
          ∃ hcount : K.dividerCount = H.dividerCount,
            (∀ j : Fin (K.dividerCount + 1),
              K.stage j.castSucc = H.stage
                (Fin.cast (congrArg (fun d => d + 1) hcount) j).castSucc) ∧
            ∀ j : Fin K.dividerCount,
              (K.dividerPosition j).val =
                (H.dividerPosition (Fin.cast hcount j)).val := by
    -- Transport the base, then retain every stage and divider before the new terminal tree.
    obtain ⟨bx, hcore, hclosure, hsupport⟩ :=
      HierarchyBaseCorrespondingTransport G k e0 input T X phi ett corr base
    let stages : Fin (H.dividerCount + 2) → TreeSequence G e0 :=
      fun i => if hi : i.val < H.dividerCount + 1 then H.stage ⟨i.val, by omega⟩ else X
    have stagesOld (i : Fin (H.dividerCount + 1)) :
        stages i.castSucc = H.stage i.castSucc := by
      simp only [stages, Fin.val_castSucc, dif_pos i.isLt]
      congr 1
    have stagesLast : stages (Fin.last (H.dividerCount + 1)) = X := by
      simp [stages]
    have oldStageLength (i : Fin H.dividerCount) :
        (H.stage i.succ.castSucc).length = (H.dividerPosition i).val := by
      have hd := H.dividerStage i
      have hi : (⟨i.val + 1, by omega⟩ : Fin (H.dividerCount + 2)) = i.succ.castSucc := by
        apply Fin.ext
        rfl
      rw [hi] at hd
      exact congrArg TreeSequence.length hd
    have positionB (i : Fin H.dividerCount) : (H.dividerPosition i).val ≤ B.length := by
      rw [← oldStageLength i]
      exact (hstageB i.succ).1
    let positions : Fin H.dividerCount → Fin (X.length + 1) :=
      fun i => ⟨(H.dividerPosition i).val, by have := positionB i; omega⟩
    let K : TashkinovHierarchy corr.replacementETT bx :=
      { dividerCount := H.dividerCount
        stage := stages
        baseStage := by
          have h0 := stagesOld (0 : Fin (H.dividerCount + 1))
          have hi : (0 : Fin (H.dividerCount + 1)).castSucc =
              (0 : Fin (H.dividerCount + 2)) := by apply Fin.ext; rfl
          rw [hi] at h0
          rw [h0, H.baseStage, terminalTree X corr]
        terminalStage := stagesLast
        nested := by
          intro j
          by_cases hj : j.val < H.dividerCount
          · let i : Fin (H.dividerCount + 1) := ⟨j.val + 1, by omega⟩
            have hi : i.castSucc = j.succ := by apply Fin.ext; rfl
            rw [stagesOld j, ← hi, stagesOld i]
            exact H.nested j
          · have hjlast : j = Fin.last H.dividerCount := by
              apply Fin.ext
              simp
              omega
            have hnext : j.succ = Fin.last (H.dividerCount + 1) := by
              apply Fin.ext
              simp
              omega
            rw [stagesOld j, hnext, stagesLast, hjlast]
            exact segmentTrans hlastB hBX
        strict := by
          intro j
          by_cases hj : j.val < H.dividerCount
          · let i : Fin (H.dividerCount + 1) := ⟨j.val + 1, by omega⟩
            have hi : i.castSucc = j.succ := by apply Fin.ext; rfl
            rw [stagesOld j, ← hi, stagesOld i]
            exact H.strict j
          · have hjlast : j = Fin.last H.dividerCount := by
              apply Fin.ext
              simp
              omega
            have hnext : j.succ = Fin.last (H.dividerCount + 1) := by
              apply Fin.ext
              simp
              omega
            rw [stagesOld j, hnext, stagesLast, hjlast]
            exact lt_of_le_of_lt hlastB.1 hstrictBX
        dividerPosition := positions
        dividerPositive := H.dividerPositive
        dividerIncreasing := H.dividerIncreasing
        dividerStage := by
          intro i
          have hi : (⟨i.val + 1, by omega⟩ : Fin (H.dividerCount + 2)) = i.succ.castSucc := by
            apply Fin.ext
            rfl
          rw [hi, stagesOld i.succ]
          have hstageX := segmentTrans (hstageB i.succ) hBX
          have hp := prefixEq hstageX
          simpa only [oldStageLength i] using hp
        coreInsideFirst := by
          rw [hcore]
          by_cases hq : H.dividerCount = 0
          · have hi : (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) =
                Fin.last (H.dividerCount + 1) := by apply Fin.ext; simp [hq]
            rw [hi, stagesLast]
            exact segmentTrans hcoreA (segmentTrans hAB hBX)
          · let i : Fin (H.dividerCount + 1) := ⟨1, by omega⟩
            have hi : i.castSucc = (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) := by
              apply Fin.ext
              rfl
            rw [← hi, stagesOld i]
            exact H.coreInsideFirst }
    refine ⟨bx, hcore, hclosure, hsupport, K, rfl, ?_, ?_⟩
    · intro j
      exact stagesOld j
    · intro j
      rfl
  obtain ⟨baseM, hcoreM, hclosureM, hsupportM, HM, hcountM, hstageM, hpositionM⟩ :=
    copyHierarchy M corrM hBM.choose_spec.1 (by omega)
  obtain ⟨baseS, hcoreS, hclosureS, hsupportS, HS, hcountS, hstageS, hpositionS⟩ :=
    copyHierarchy S corrS (segmentTrans hBM.choose_spec.1 hMS.choose_spec.1) (by omega)
  exact ⟨R, hboundaryPE, routes.1, routes.2, corrM, hMPM,
    baseM, hcoreM, hclosureM, hsupportM, HM, hcountM, hstageM, hpositionM,
    corrS, hMPS, baseS, hcoreS, hclosureS, hsupportS, HS, hcountS, hstageS, hpositionS⟩
