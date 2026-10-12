import Tablet.HierarchyReplacementPresentationTrans
import Tablet.P2813_T1_BaseDisplayedEdges
import Tablet.P2813_T1_TerminalRoute
import Tablet.P2905_T2_ElementaryTerminalComponent
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TwoColorComponentSwapProper
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TashkinovAugmentationSequenceSuffix
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovAugmentationSequenceColoringTransport
import Tablet.ChangeLemma
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.StableChangeCasesOneTwoSplitTail

-- [TABLET NODE: P2963_T1_TerminalKempeStageSwitch]
theorem P2963_T1_TerminalKempeStageSwitch {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (A B : TreeSequence G e0) (hTlen : 2 ≤ T.length)
    (hA : HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) = A)
    (hB : B = TreeSequencePrefix T (T.length - 1) (by omega) (by omega))
    (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
    (X : TreeSequence G e0) (hAX : TreeSequenceInitialSegment A X)
    (hAXlt : A.length < X.length) (hXB : TreeSequenceInitialSegment X B)
    (a b eta : Fin k)
    (heta : eta ∈ HierarchyStoredColorsAt R.counterexample.hierarchy
      (Fin.last R.counterexample.hierarchy.dividerCount))
    (haGamma : a ∈ R.counterexample.good.gamma
      (Fin.last R.counterexample.hierarchy.dividerCount) eta)
    (hetaCut : (HierarchyFirstMissingPosition R.coloring T eta).val ≤ X.length)
    (jb : Fin (B.length + 1)) (hjb : A.length < jb.val)
    (hjbX : jb.val ≤ X.length)
    (hb : b ∈ MissingColors G R.coloring (B.vertex jb))
    (hw : a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) ∨
      b ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)))
    (haUnused : ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
      R.coloring (T.edge t) ≠ some a)
    (hbException : ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
      R.coloring (T.edge t) = some b →
        TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree
          (Fin.last R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧
        b ∈ TashkinovStoredColors R.corresponding.replacementETT.series.data
          (Fin.last R.corresponding.replacementETT.rounds)) :
    ∃ S : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx,
      (∀ v ∈ TreeSequenceVertexSet B,
        MissingColors G S.coloring v = MissingColors G R.coloring v) ∧
      (∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
        S.coloring (T.edge t) = R.coloring (T.edge t)) ∧
      (a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
        b ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) ∧
      (b ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
        a ∈ MissingColors G S.coloring (T.vertex (Fin.last T.length))) := by
-- BODY
  classical
  subst A
  subst B
  let A := HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)
  have trans {X Y Z : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y)
      (hYZ : TreeSequenceInitialSegment Y Z) :
      TreeSequenceInitialSegment X Z := by
    clear * - hXY hYZ
    refine ⟨hXY.1.trans hYZ.1, ?_, ?_⟩
    · intro i
      exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY.1) i)).trans (hXY.2.1 i)
    · intro i
      exact (hYZ.2.2 (Fin.castLE hXY.1 i)).trans (hXY.2.2 i)
  have common {X Y Z : TreeSequence G e0}
      (hXZ : TreeSequenceInitialSegment X Z)
      (hYZ : TreeSequenceInitialSegment Y Z) (hXY : X.length ≤ Y.length) :
      TreeSequenceInitialSegment X Y := by
    clear * - hXZ hYZ hXY
    refine ⟨hXY, ?_, ?_⟩
    · intro i
      exact (hYZ.2.1 (Fin.castLE (Nat.succ_le_succ hXY) i)).symm.trans (hXZ.2.1 i)
    · intro i
      exact (hYZ.2.2 (Fin.castLE hXY i)).symm.trans (hXZ.2.2 i)
  have componentData (psi : PartialEdgeColoring E k) (a b : Fin k)
      (hne : a ≠ b) (hproper : IsProperEdgeColoring G psi)
      (B : Finset V) (helem : ColoredVertexSetElementary G psi B)
      (u v w : V) (hu : u ∈ B) (hv : v ∈ B) (huv : u ≠ v)
      (hwu : w ≠ u) (hwv : w ≠ v)
      (hau : a ∈ MissingColors G psi u) (hbv : b ∈ MissingColors G psi v)
      (hw : a ∈ MissingColors G psi w ∨ b ∈ MissingColors G psi w)
      (hsame : TwoColorComponent G psi a b (Sum.inl u) =
        TwoColorComponent G psi a b (Sum.inl v)) :
      Disjoint (TwoColorComponent G psi a b (Sum.inl w))
          (TwoColorComponent G psi a b (Sum.inl u)) ∧
        TwoColorPathComponent G psi a b (Sum.inl w) ∧
        (∀ x ∈ B,
          MissingColors G (TwoColorComponentSwap G psi a b (Sum.inl w)) x =
            MissingColors G psi x) := by

    exact P2905_T2_ElementaryTerminalComponent G psi a b hne hproper
      B helem u v w hu hv hwu hwv hau hbv hw hsame
  have sameLast : ∀ {a b : ℕ}
      (s : Fin (a + 2) → TreeSequence G e0)
      (t : Fin (b + 2) → TreeSequence G e0)
      (u v : TreeSequence G e0),
      a = b → HEq s t → u = v →
      Fin.cases (motive := fun _ => TreeSequence G e0)
        u (fun i : Fin a => s i.castSucc.succ) (Fin.last a) =
        Fin.cases (motive := fun _ => TreeSequence G e0)
          v (fun i : Fin b => t i.castSucc.succ) (Fin.last b) := by
    clear * -
    intro a b s t u v hab hst huv
    cases hab
    have he : s = t := eq_of_heq hst
    cases he
    cases huv
    rfl
  have starEq (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      HierarchyStarredStage R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount) = A :=
    (sameLast _ _ _ _ R.sameGood.1.2.1 R.sameGood.1.2.2.1 R.sameGood.1.1).symm
  have hAT : TreeSequenceInitialSegment A T := by
    have starNext (j : Fin (C.hierarchy.dividerCount + 1)) :
        TreeSequenceInitialSegment (HierarchyStarredStage C.hierarchy j)
          (C.hierarchy.stage j.succ) :=
      Fin.cases C.hierarchy.coreInsideFirst (fun i => C.hierarchy.nested i.succ) j
    simpa only [Fin.succ_last, C.hierarchy.terminalStage] using
      starNext (Fin.last C.hierarchy.dividerCount)
  let B := TreeSequencePrefix T (T.length - 1) (by omega) (by omega)
  change TreeSequenceInitialSegment A X at hAX
  change A.length < X.length at hAXlt
  change TreeSequenceInitialSegment X B at hXB
  change A.length < jb.val at hjb
  change b ∈ MissingColors G R.coloring (B.vertex jb) at hb
  change ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
    R.coloring (T.edge t) ≠ some a at haUnused
  change ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
    R.coloring (T.edge t) = some b →
      TreeIncidentEdge (R.corresponding.replacementETT.series.data.tree
        (Fin.last R.corresponding.replacementETT.rounds).castSucc) (T.edge t) ∧
      b ∈ TashkinovStoredColors R.corresponding.replacementETT.series.data
        (Fin.last R.corresponding.replacementETT.rounds) at hbException
  have hBT : TreeSequenceInitialSegment B T :=
    ⟨by dsimp [B, TreeSequencePrefix]; omega, fun _ => rfl, fun _ => rfl⟩
  have hAB : TreeSequenceInitialSegment A B := trans hAX hXB
  have hXlen : X.length ≤ T.length - 1 := hXB.1
  have fullB (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      HierarchyFullTailPrefix R.counterexample
        (HierarchyFullTailLength R.counterexample - 1) = B := by
    have hn : min ((HierarchyStarredStage R.counterexample.hierarchy
        (Fin.last R.counterexample.hierarchy.dividerCount)).length +
        (HierarchyFullTailLength R.counterexample - 1)) T.length = T.length - 1 := by
      unfold HierarchyFullTailLength
      dsimp only
      rw [starEq R]
      omega
    simp only [HierarchyFullTailPrefix, hn]
    rfl
  have elementary (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      ColoredVertexSetElementary G R.coloring (TreeSequenceVertexSet B) := by
    have h : ColoredVertexSetElementary G R.coloring
      (TreeSequenceVertexSet (HierarchyFullTailPrefix R.counterexample
        (HierarchyFullTailLength R.counterexample - 1))) := by
      exact HierarchyCounterexamplePenultimateElementary G k e0
        R.corresponding.replacementInput T R.coloring R.corresponding.replacementETT
        R.replacementBase R.counterexample R.minimumContext.proper
        R.minimumContext.oneEdgeUncolored R.minimumContext.lowerRung
        R.minimumContext.fewerDividers R.minimumContext.lexicographicMinimality
        R.minimumContext.largeMissingSet
    intro u hu v hv hne
    exact h (by rw [fullB R]; exact hu) (by rw [fullB R]; exact hv) hne
  have vertexMem (U : TreeSequence G e0) (j : Fin (U.length + 1)) :
      U.vertex j ∈ TreeSequenceVertexSet U := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨j, rfl⟩
  have firstLe (psi : PartialEdgeColoring E k) (c : Fin k)
      (j : Fin (T.length + 1)) (hj : c ∈ MissingColors G psi (T.vertex j)) :
      HierarchyFirstMissingPosition psi T c ≤ j := by
    clear * - G T psi c j hj
    let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
      c ∈ MissingColors G psi (T.vertex j)
    have hm : j ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    have hn : candidates.Nonempty := ⟨j, hm⟩
    unfold HierarchyFirstMissingPosition
    rw [dif_pos hn]
    exact Finset.min'_le candidates j hm
  have firstMem (psi : PartialEdgeColoring E k) (c : Fin k)
      (hlt : (HierarchyFirstMissingPosition psi T c).val < T.length) :
      c ∈ MissingColors G psi (T.vertex (HierarchyFirstMissingPosition psi T c)) := by
    clear * - G T psi c hlt
    let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
      c ∈ MissingColors G psi (T.vertex j)
    by_cases hn : candidates.Nonempty
    · unfold HierarchyFirstMissingPosition
      rw [dif_pos hn]
      exact (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
    · have hh : (HierarchyFirstMissingPosition psi T c).val = T.length := by
        unfold HierarchyFirstMissingPosition
        rw [dif_neg hn]
        rfl
      omega
  have firstAt (R : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (c : Fin k) (j : Fin (B.length + 1))
      (hc : c ∈ MissingColors G R.coloring (B.vertex j)) :
      (HierarchyFirstMissingPosition R.coloring T c).val = j.val := by
    clear * - G T B R c j hc elementary vertexMem firstLe firstMem hBT
    have hcT : c ∈ MissingColors G R.coloring
        (T.vertex (Fin.castLE (Nat.succ_le_succ hBT.1) j)) := by
      rw [hBT.2.1 j]; exact hc
    have hle := firstLe R.coloring c _ hcT
    have hlt : (HierarchyFirstMissingPosition R.coloring T c).val < T.length := by
      have := j.isLt
      change (HierarchyFirstMissingPosition R.coloring T c).val ≤ j.val at hle
      have hblen : B.length = T.length - 1 := rfl
      omega
    let x : Fin (B.length + 1) := ⟨(HierarchyFirstMissingPosition R.coloring T c).val, by
      change (HierarchyFirstMissingPosition R.coloring T c).val ≤ j.val at hle
      omega⟩
    have hxT : Fin.castLE (Nat.succ_le_succ hBT.1) x =
        HierarchyFirstMissingPosition R.coloring T c := Fin.ext rfl
    have hcx : c ∈ MissingColors G R.coloring (B.vertex x) := by
      rw [← hBT.2.1 x, hxT]
      exact firstMem R.coloring c hlt
    have he : B.vertex x = B.vertex j := by
      by_contra hn
      exact Finset.disjoint_left.mp (elementary R (vertexMem B x) (vertexMem B j) hn) hcx hc
    exact congrArg Fin.val (B.vertex_injective he)
  have firstFixed (psi tau : PartialEdgeColoring E k)
      (hmissing : ∀ v ∈ TreeSequenceVertexSet B,
        MissingColors G tau v = MissingColors G psi v) (c : Fin k) :
      HierarchyFirstMissingPosition tau T c = HierarchyFirstMissingPosition psi T c := by
    clear * - G T B psi tau hmissing c firstLe firstMem hBT vertexMem
    have early (j : Fin (T.length + 1)) (hj : j.val < T.length) :
        MissingColors G tau (T.vertex j) = MissingColors G psi (T.vertex j) := by
      let x : Fin (B.length + 1) := ⟨j.val, by dsimp [B, TreeSequencePrefix]; omega⟩
      have hx : Fin.castLE (Nat.succ_le_succ hBT.1) x = j := Fin.ext rfl
      rw [← hx, hBT.2.1 x]
      exact hmissing _ (vertexMem B x)
    apply Fin.ext
    apply Nat.le_antisymm
    · by_contra hn
      have hlt : (HierarchyFirstMissingPosition psi T c).val < T.length := by
        have := (HierarchyFirstMissingPosition tau T c).isLt
        omega
      have hm := firstMem psi c hlt
      rw [← early _ hlt] at hm
      have := firstLe tau c _ hm
      omega
    · by_contra hn
      have hlt : (HierarchyFirstMissingPosition tau T c).val < T.length := by
        have := (HierarchyFirstMissingPosition psi T c).isLt
        omega
      have hm := firstMem tau c hlt
      rw [early _ hlt] at hm
      have := firstLe psi c _ hm
      omega
  clear * - G T A B R X hAX hAXlt hXB a b eta heta haGamma hetaCut jb hjb hjbX hb hw
    haUnused hbException trans common starEq hAT hAB hBT elementary vertexMem firstLe
    firstMem firstAt firstFixed componentData fullB hXlen
  let H := R.counterexample.hierarchy
  let q := Fin.last H.dividerCount
  let n := Fin.last R.corresponding.replacementETT.rounds
  let Tn := R.corresponding.replacementETT.series.data.tree n.castSucc
  let Dn := TashkinovStoredColors R.corresponding.replacementETT.series.data n
  have chain : ∀ (j : ℕ) (hj : j < H.dividerCount + 2)
      (i : Fin (H.dividerCount + 2)), i.val ≤ j →
      TreeSequenceInitialSegment (H.stage i) (H.stage ⟨j, hj⟩) := by
    intro j
    induction j with
    | zero =>
        intro hj i hi
        have he : i = 0 := Fin.ext (Nat.eq_zero_of_le_zero hi)
        subst i
        exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    | succ j ih =>
        intro hj i hi
        by_cases heq : i.val = j + 1
        · have he : i = ⟨j + 1, hj⟩ := Fin.ext heq
          subst i
          exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
        · exact trans (ih (by omega) i (by omega)) (H.nested ⟨j, by omega⟩)
  have lastPositive (hq : H.dividerCount ≠ 0) :
      HierarchyStarredStage H q = H.stage ⟨H.dividerCount, by omega⟩ := by
    unfold HierarchyStarredStage
    obtain hz | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ q
    · exact (hq (by simpa [q] using congrArg Fin.val hz)).elim
    · rw [hi]
      simp only [Fin.cases_succ]
      congr 1
      exact Fin.ext (by simpa [q] using (congrArg Fin.val hi).symm)
  have hTnCore : TreeSequenceInitialSegment Tn R.replacementBase.core := by
    by_cases hpe : R.corresponding.replacementETT.series.data.kind n =
        some TashkinovExtensionKind.PE
    · exact (R.replacementBase.parallel hpe).2.2.some.leftSegment
    · rw [R.replacementBase.nonparallel hpe]
      exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  have coreA : TreeSequenceInitialSegment R.replacementBase.core A := by
    rw [← starEq R]
    by_cases hq : H.dividerCount = 0
    · have he : HierarchyStarredStage H q = R.replacementBase.core := by
        simp [HierarchyStarredStage, q, hq, Fin.last]
      rw [he]
      exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    · rw [lastPositive hq]
      exact trans H.coreInsideFirst (chain H.dividerCount (by omega) ⟨1, by omega⟩
        (by change 1 ≤ H.dividerCount; omega))
  have hTnA := trans hTnCore coreA
  have stageCase :
      (0 < H.dividerCount ∧ a ∈ TreeMissingColors R.coloring
        (H.stage ⟨H.dividerCount, by omega⟩)) ∨
      (H.dividerCount = 0 ∧ a ∈ TreeMissingColors R.coloring Tn) := by
    have hm := (Finset.mem_sdiff.mp (R.counterexample.good.avoidance q eta heta haGamma)).1
    by_cases hq : H.dividerCount = 0
    · right
      refine ⟨hq, ?_⟩
      simpa [HierarchyStageMissingColors, q, hq, Fin.last, Tn, n] using hm
    · left
      refine ⟨by omega, ?_⟩
      unfold HierarchyStageMissingColors at hm
      dsimp only at hm
      obtain hz | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ q
      · exact (hq (by simpa [q] using congrArg Fin.val hz)).elim
      · rw [hi] at hm
        simp only [Fin.cases_succ] at hm
        have he : i.succ.castSucc = (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) :=
          Fin.ext (by simpa [q] using (congrArg Fin.val hi).symm)
        simpa only [he] using hm
  have haA : a ∈ TreeMissingColors R.coloring A := by
    rcases stageCase with ⟨hq, hm⟩ | ⟨hq, hm⟩
    · rw [← starEq R, lastPositive (by omega)]
      exact hm
    · obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp hm
      exact Finset.mem_biUnion.mpr ⟨v,
        TreeSequenceInitialSegmentVertexSetSubset hTnA hv, hc⟩
  have hbOutside : b ∉ TreeMissingColors R.coloring A := by
    rintro hm
    obtain ⟨v, hvA, hmv⟩ := Finset.mem_biUnion.mp hm
    obtain ⟨j, hj⟩ : ∃ j, A.vertex j = v := by simpa [TreeSequenceVertexSet] using hvA
    have hne : v ≠ B.vertex jb := by
      intro he
      have hh := T.vertex_injective ((hAT.2.1 j).trans
        (hj.trans (he.trans (hBT.2.1 jb).symm)))
      have hh := congrArg Fin.val hh
      have := j.isLt
      change j.val = jb.val at hh
      omega
    exact Finset.disjoint_left.mp (elementary R
      (TreeSequenceInitialSegmentVertexSetSubset hAB hvA) (vertexMem B jb) hne) hmv hb
  have hne : a ≠ b := by rintro rfl; exact hbOutside haA
  have hbB : b ∈ TreeMissingColors R.coloring B :=
    Finset.mem_biUnion.mpr ⟨B.vertex jb, vertexMem B jb, hb⟩
  have haB : a ∈ TreeMissingColors R.coloring B := by
    obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp haA
    exact Finset.mem_biUnion.mpr ⟨v, TreeSequenceInitialSegmentVertexSetSubset hAB hv, hc⟩
  have iaLe : (HierarchyFirstMissingPosition R.coloring T a).val ≤ A.length := by
    obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp haA
    obtain ⟨j, hj⟩ : ∃ j, A.vertex j = v := by simpa [TreeSequenceVertexSet] using hv
    have hcT : a ∈ MissingColors G R.coloring
        (T.vertex (Fin.castLE (Nat.succ_le_succ hAT.1) j)) := by
      rw [hAT.2.1 j, hj]; exact hc
    have hh := firstLe R.coloring a _ hcT
    change (HierarchyFirstMissingPosition R.coloring T a).val ≤ j.val at hh
    have := j.isLt
    omega
  have ibEq := firstAt R b jb hb
  have haFirst := firstMem R.coloring a (by
    have := hAB.1
    have hblen : B.length = T.length - 1 := rfl
    omega)
  let ja : Fin (B.length + 1) := ⟨(HierarchyFirstMissingPosition R.coloring T a).val,
    by have := hAB.1; omega⟩
  have jaEq : Fin.castLE (Nat.succ_le_succ hBT.1) ja =
      HierarchyFirstMissingPosition R.coloring T a := Fin.ext rfl
  have jbEq : Fin.castLE (Nat.succ_le_succ hBT.1) jb =
      HierarchyFirstMissingPosition R.coloring T b := Fin.ext ibEq.symm
  have haFirstB : a ∈ MissingColors G R.coloring (B.vertex ja) := by
    rw [← hBT.2.1 ja, jaEq]; exact haFirst
  have hordered : TreeVertexOrder T
      (T.vertex (HierarchyFirstMissingPosition R.coloring T a))
      (T.vertex (HierarchyFirstMissingPosition R.coloring T b)) :=
    ⟨_, _, rfl, rfl, by omega⟩
  have hunused : a ∉ (Finset.univ.filter fun c => ∃ t : Fin T.length,
      A.length ≤ t.val ∧ t.val < (HierarchyFirstMissingPosition R.coloring T b).val ∧
        R.coloring (T.edge t) = some c) := by
    intro hh
    obtain ⟨_, t, hlo, hhi, hc⟩ := Finset.mem_filter.mp hh
    exact haUnused t hlo (by omega) hc
  have hprefixR : ColoredVertexSetElementary G R.coloring
      (TreeSequenceVertexSet (HierarchyFullTailPrefix R.counterexample
        (HierarchyFullTailLength R.counterexample - 1))) := by
    rw [fullB R]
    exact elementary R
  have hmissingR : a ∈ TreeMissingColors R.coloring
      (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - 1)) ∧
      b ∈ TreeMissingColors R.coloring
      (HierarchyFullTailPrefix R.counterexample (HierarchyFullTailLength R.counterexample - 1)) := by
    rw [fullB R]
    exact ⟨haB, hbB⟩
  have change := ChangeLemma G k e0 R.corresponding.replacementInput T R.coloring
    R.corresponding.replacementETT R.replacementBase R.counterexample
    R.minimumContext.proper R.minimumContext.oneEdgeUncolored R.minimumContext.lowerRung
    R.minimumContext.fewerDividers R.minimumContext.lexicographicMinimality
    hprefixR
    R.minimumContext.largeMissingSet a b hne
    hmissingR
    (by
      dsimp only
      rw [starEq R]
      intro _
      exact ⟨hordered, hunused⟩)
  have hsame : TwoColorComponent G R.coloring a b (Sum.inl (B.vertex ja)) =
      TwoColorComponent G R.coloring a b (Sum.inl (B.vertex jb)) := by
    have hh : TwoColorComponent G R.coloring a b
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition R.coloring T a))) =
        TwoColorComponent G R.coloring a b
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition R.coloring T b))) := by
      rcases stageCase with ⟨hq, hm⟩ | ⟨hq, hm⟩
      · exact change.1 ⟨hq, Or.inl hm⟩
      · exact change.2.1 ⟨hq, Or.inl hm⟩
    rw [← jaEq, ← jbEq, hBT.2.1 ja, hBT.2.1 jb] at hh
    exact hh
  obtain ⟨hdis, hpath, hmissing⟩ := componentData R.coloring a b hne
    R.minimumContext.proper (TreeSequenceVertexSet B) (elementary R)
    (B.vertex ja) (B.vertex jb) (T.vertex (Fin.last T.length))
    (vertexMem B ja) (vertexMem B jb)
    (by intro hh; have := congrArg Fin.val (B.vertex_injective hh); dsimp [ja] at this; omega)
    (by intro hh; have hh := T.vertex_injective (hh.trans (hBT.2.1 ja).symm)
        have hh := congrArg Fin.val hh
        change T.length = ja.val at hh
        have := ja.isLt
        have hblen : B.length = T.length - 1 := rfl
        omega)
    (by intro hh; have hh := T.vertex_injective (hh.trans (hBT.2.1 jb).symm)
        have hh := congrArg Fin.val hh
        change T.length = jb.val at hh
        have := jb.isLt
        have hblen : B.length = T.length - 1 := rfl
        omega)
    haFirstB hb hw hsame
  let sigma := TwoColorComponentSwap G R.coloring a b (Sum.inl (T.vertex (Fin.last T.length)))
  have hsproper : IsProperEdgeColoring G sigma :=
    TwoColorComponentSwapProper G R.coloring a b hne R.minimumContext.proper _
  have hsone : IsOneEdgeUncolored sigma e0 := by
    refine ⟨?_, ?_⟩
    · simp [sigma, TwoColorComponentSwap, R.minimumContext.oneEdgeUncolored.1]
    · intro e he
      obtain ⟨c, hc⟩ := R.minimumContext.oneEdgeUncolored.2 e he
      by_cases hm : Sum.inr e ∈ TwoColorComponent G R.coloring a b
          (Sum.inl (T.vertex (Fin.last T.length)))
      · by_cases hca : c = a
        · subst c; exact ⟨b, by simp [sigma, TwoColorComponentSwap, hm, hc]⟩
        · by_cases hcb : c = b
          · subst c; exact ⟨a, by simp [sigma, TwoColorComponentSwap, hm, hc, hne.symm]⟩
          · exact ⟨c, by simp [sigma, TwoColorComponentSwap, hm, hc, hca, hcb]⟩
      · exact ⟨c, by simp [sigma, TwoColorComponentSwap, hm, hc]⟩
  have hcase :
      (0 < H.dividerCount ∧ a ∈ TreeMissingColors R.coloring (H.stage ⟨H.dividerCount, by omega⟩)) ∨
      (H.dividerCount = 0 ∧ (a ∈ TreeMissingColors R.coloring Tn ∨
        (a ∈ TreeMissingColors R.coloring (HierarchyStarredStage H q) ∧ a ∉ Dn ∧ b ∉ Dn))) := by
    rcases stageCase with h | ⟨hq, hm⟩
    · exact Or.inl h
    · exact Or.inr ⟨hq, Or.inl hm⟩
  have hdisFirst : Disjoint (TwoColorComponent G R.coloring a b
      (Sum.inl (T.vertex (Fin.last T.length))))
      (TwoColorComponent G R.coloring a b
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition R.coloring T a)))) := by
    rw [← jaEq, hBT.2.1 ja]
    exact hdis
  have changed := StableChangeCasesOneTwo G k e0 R.corresponding.replacementInput T R.coloring
    R.corresponding.replacementETT R.replacementBase R.counterexample
    R.minimumContext.proper R.minimumContext.oneEdgeUncolored R.minimumContext.lowerRung
    R.minimumContext.fewerDividers R.minimumContext.lexicographicMinimality
    hprefixR
    R.minimumContext.largeMissingSet a b hne
    hmissingR
    _ hpath sigma rfl hcase hdisFirst
  have hweak : HierarchyWeaklyStable H q sigma := changed.1
  have baseStable : if R.corresponding.replacementETT.series.data.kind n =
      some TashkinovExtensionKind.PE then
      CombinedStableColoring Tn R.replacementBase.closure Dn R.coloring sigma
    else StableColoring Tn Dn R.coloring sigma := by
    have extract (j : Fin (H.dividerCount + 1)) : HierarchyWeaklyStable H j sigma →
        (if R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE then
          CombinedStableColoring Tn R.replacementBase.closure Dn R.coloring sigma
        else StableColoring Tn Dn R.coloring sigma) :=
      Fin.cases (fun h => h) (fun _ h => h.1) j
    exact extract q hweak
  have stable : StableColoring Tn Dn R.coloring sigma := by
    by_cases hp : R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE
    · exact (if_pos hp ▸ baseStable).1
    · simpa only [hp, if_false] using baseStable
  have fixedA : ∀ t : Fin A.length, sigma (A.edge t) = R.coloring (A.edge t) := by
    have fixed (j : Fin (H.dividerCount + 1)) : HierarchyWeaklyStable H j sigma →
        ∀ t : Fin (HierarchyStarredStage H j).length,
          sigma ((HierarchyStarredStage H j).edge t) = R.coloring ((HierarchyStarredStage H j).edge t) := by
      refine Fin.cases ?_ (fun i => ?_) j
      · intro _
        exact P2813_T1_BaseDisplayedEdges G k e0 R.corresponding.replacementInput T R.coloring
          R.corresponding.replacementETT R.replacementBase sigma
          R.minimumContext.oneEdgeUncolored hsone baseStable
      · intro hh t
        change sigma ((H.stage i.succ.castSucc).edge t) =
          R.coloring ((H.stage i.succ.castSucc).edge t)
        by_cases ht : t.val = 0
        · have he : (H.stage i.succ.castSucc).edge t = e0 := by
            rw [show t = ⟨0, (H.stage i.succ.castSucc).positive⟩ from Fin.ext ht]
            exact (H.stage i.succ.castSucc).first_edge
          rw [he, hsone.1, R.minimumContext.oneEdgeUncolored.1]
        · exact hh.2.1 t (by omega)
    rw [← starEq R]
    exact fixed q hweak
  have fixedPrefix : ∀ t : Fin T.length, A.length ≤ t.val → t.val < X.length →
      sigma (T.edge t) = R.coloring (T.edge t) := by
    intro t hlo hhi
    by_cases hbcol : R.coloring (T.edge t) = some b
    · obtain ⟨hi, hc⟩ := hbException t hlo hhi hbcol
      exact stable.1 _ hi ⟨b, Finset.mem_union_right _ hc, hbcol⟩
    · have haNo := haUnused t hlo hhi
      simp [sigma, TwoColorComponentSwap, haNo, hbcol]
  have hXT := trans hXB hBT
  let XM := TreeSequencePrefix X (X.length - 1) (by have := A.positive; omega) (by omega)
  have hXMX : TreeSequenceInitialSegment XM X :=
    ⟨by dsimp [XM, TreeSequencePrefix]; omega, fun _ => rfl, fun _ => rfl⟩
  have prefixFixed (t : Fin X.length) (ht : Tn.length ≤ t.val) :
      sigma (X.edge t) = R.coloring (X.edge t) := by
    by_cases hlow : t.val < A.length
    · let j : Fin A.length := ⟨t.val, hlow⟩
      have he : Fin.castLE hAX.1 j = t := Fin.ext rfl
      rw [← he, hAX.2.2 j]
      exact fixedA j
    · rw [← hXT.2.2 t]
      exact fixedPrefix (Fin.castLE hXT.1 t) (by change A.length ≤ t.val; omega) t.isLt
  have routes :
      ((R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn X) ∨
      ((R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.SE ∨
        R.corresponding.replacementETT.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        ∃ f seed, R.corresponding.replacementETT.series.data.connectingEdges n = {f} ∧
          TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovAugmentationSequence sigma seed X)) ∧
      TashkinovAugmentationSequence R.coloring X T := by
    rcases P2813_T1_TerminalRoute G k e0 R.corresponding.replacementInput T R.coloring
        R.corresponding.replacementETT with ⟨hp, hseq⟩ |
        ⟨hp, f, seed, hedges, hseed, hincident, hcontrol, hseq⟩
    · have hsourceX := trans hTnA hAX
      have hpre := TashkinovAugmentationSequenceRestrict R.coloring Tn X T hseq hsourceX hXT
      refine ⟨Or.inl ⟨hp, ?_⟩,
        TashkinovAugmentationSequenceSuffix R.coloring Tn X T hseq hsourceX hXT⟩
      exact TashkinovAugmentationSequenceColoringTransport R.coloring sigma Tn XM X
        hpre hXMX (by dsimp [XM, TreeSequencePrefix]; have := X.positive; omega) prefixFixed
        (fun v hv => hmissing v (TreeSequenceInitialSegmentVertexSetSubset
          (trans hXMX hXB) hv))
    · have hseedX := common
        (TashkinovAugmentationSequenceInitialSegment R.coloring seed T hseq) hXT
        (by have hl := hseed.1; have := hTnA.1; change seed.length = Tn.length + 1 at hl; omega)
      have hpre := TashkinovAugmentationSequenceRestrict R.coloring seed X T hseq hseedX hXT
      refine ⟨Or.inr ⟨hp, f, seed, hedges, hseed, ?_⟩,
        TashkinovAugmentationSequenceSuffix R.coloring seed X T hseq hseedX hXT⟩
      exact TashkinovAugmentationSequenceColoringTransport R.coloring sigma seed XM X
        hpre hXMX (by dsimp [XM, TreeSequencePrefix]; have := X.positive; omega)
        (fun t ht => prefixFixed t (by have hl := hseed.1; change seed.length = Tn.length + 1 at hl; omega))
        (fun v hv => hmissing v (TreeSequenceInitialSegmentVertexSetSubset
          (trans hXMX hXB) hv))
  have hsplit : a ∈ TreeMissingColors sigma X ∧ b ∈ TreeMissingColors sigma X := by
    have subset (j : Fin (B.length + 1)) (hj : j.val ≤ X.length) :
        B.vertex j ∈ TreeSequenceVertexSet X := by
      let x : Fin (X.length + 1) := ⟨j.val, by omega⟩
      have hx : Fin.castLE (Nat.succ_le_succ hXB.1) x = j := Fin.ext rfl
      rw [← hx, hXB.2.1 x]
      exact vertexMem X x
    refine ⟨Finset.mem_biUnion.mpr ⟨B.vertex ja, subset ja (by dsimp [ja]; omega), ?_⟩,
      Finset.mem_biUnion.mpr ⟨B.vertex jb, subset jb hjbX, ?_⟩⟩
    · rw [hmissing _ (vertexMem B ja)]; exact haFirstB
    · rw [hmissing _ (vertexMem B jb)]; exact hb
  have gammaCut : ∀ eta', eta' ∈ HierarchyStoredColorsAt H q →
      (a ∈ R.counterexample.good.gamma q eta' ∨ b ∈ R.counterexample.good.gamma q eta') →
        (HierarchyFirstMissingPosition R.coloring T eta').val ≤ X.length := by
    intro eta' heta' hh
    rcases hh with hh | hh
    · have he : eta' = eta := by
        by_contra hn
        exact Finset.disjoint_left.mp
          (R.counterexample.good.disjointPairs q eta' eta heta' heta hn) hh haGamma
      simpa only [he] using hetaCut
    · have hm := (Finset.mem_sdiff.mp (R.counterexample.good.avoidance q eta' heta' hh)).1
      have hmb : b ∈ TreeMissingColors R.coloring A := by
        rcases stageCase with ⟨hq, _⟩ | ⟨hq, _⟩
        · have hhq : H.dividerCount ≠ 0 := by omega
          unfold HierarchyStageMissingColors at hm
          dsimp only at hm
          obtain hz | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ q
          · exact (hhq (by simpa [q] using congrArg Fin.val hz)).elim
          · rw [hi] at hm
            simp only [Fin.cases_succ] at hm
            have he : HierarchyStarredStage H q = H.stage i.succ.castSucc := by
              change Fin.cases (motive := fun _ => TreeSequence G e0)
                R.replacementBase.core (fun i => H.stage i.succ.castSucc) q = _
              rw [hi]
              rfl
            rw [← starEq R, he]
            exact hm
        · have hmT : b ∈ TreeMissingColors R.coloring Tn := by
            simpa [HierarchyStageMissingColors, q, hq, Fin.last, Tn, n] using hm
          obtain ⟨v, hv, hc⟩ := Finset.mem_biUnion.mp hmT
          exact Finset.mem_biUnion.mpr ⟨v, TreeSequenceInitialSegmentVertexSetSubset hTnA hv, hc⟩
      exact (hbOutside hmb).elim
  obtain ⟨_, _, corr, hmaximum, bs, K, goodK, hsameGood⟩ :=
    StableChangeCasesOneTwoSplitTail G k e0 R.corresponding.replacementInput T R.coloring
      R.corresponding.replacementETT R.replacementBase R.counterexample R.minimumContext
      a b hne (by rw [fullB R]; exact ⟨haB, hbB⟩)
      _ hpath sigma rfl hcase hdisFirst X (by dsimp only; rw [starEq R]; exact hAX)
      (by dsimp only; rw [starEq R]; exact hAXlt) (by rw [fullB R]; exact hXB)
      (by dsimp only; rw [starEq R]; exact fixedPrefix) routes.1 routes.2 hsplit
      (by rw [fullB R]; exact hmissing)
      (fun c _ => firstFixed R.coloring sigma hmissing c) gammaCut
  have terminal := TwoColorComponentSwapMissingBehavior G R.coloring a b hne
    R.minimumContext.proper (Sum.inl (T.vertex (Fin.last T.length)))
  have hterminalA : a ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
      b ∈ MissingColors G sigma (T.vertex (Fin.last T.length)) :=
    terminal.2.1 _ (by rfl)
  have hterminalB : b ∈ MissingColors G R.coloring (T.vertex (Fin.last T.length)) →
      a ∈ MissingColors G sigma (T.vertex (Fin.last T.length)) :=
    terminal.2.2.1 _ (by rfl)
  have hnotElementary : ¬ ColoredVertexSetElementary G sigma (TreeSequenceVertexSet T) := by
    intro he
    rcases hw with hw | hw
    · have hbNew : b ∈ MissingColors G sigma (B.vertex jb) := by
        rw [hmissing _ (vertexMem B jb)]; exact hb
      exact Finset.disjoint_left.mp (he
        (TreeSequenceInitialSegmentVertexSetSubset hBT (vertexMem B jb))
        (vertexMem T (Fin.last T.length)) (by
          intro hh
          have hh := T.vertex_injective ((hBT.2.1 jb).trans hh)
          have hh := congrArg Fin.val hh
          change jb.val = T.length at hh
          have := jb.isLt
          have hblen : B.length = T.length - 1 := rfl
          omega))
        hbNew (hterminalA hw)
    · have haNew : a ∈ MissingColors G sigma (B.vertex ja) := by
        rw [hmissing _ (vertexMem B ja)]; exact haFirstB
      exact Finset.disjoint_left.mp (he
        (TreeSequenceInitialSegmentVertexSetSubset hBT (vertexMem B ja))
        (vertexMem T (Fin.last T.length)) (by
          intro hh
          have hh := T.vertex_injective ((hBT.2.1 ja).trans hh)
          have hh := congrArg Fin.val hh; dsimp [ja] at hh; omega))
        haNew (hterminalB hw)
  let CS : HierarchyCounterexample bs := {
    positive := by rw [corr.rungAgreement]; exact R.counterexample.positive
    hierarchy := K
    good := goodK
    maximum := hmaximum
    notElementary := hnotElementary }
  obtain ⟨S, hS⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi ett base C ctx
    R sigma corr bs CS hsameGood
  refine ⟨S, ?_, ?_, ?_, ?_⟩ <;> rw [hS]
  · exact hmissing
  · exact fixedPrefix
  · exact hterminalA
  · exact hterminalB
