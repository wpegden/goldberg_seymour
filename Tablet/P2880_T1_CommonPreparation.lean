import Tablet.P2880_T1_SplitSwapData
import Tablet.P2880_T1_ElementaryPrefixSwap
import Tablet.P2752_T2_HierarchyMeasures
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyFirstMissingPositionPrefixCutoff
import Tablet.P2813_T1_TerminalRoute
import Tablet.TashkinovAugmentationSequenceSuffix
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovAugmentationSequenceColoringTransport
import Tablet.TashkinovAugmentationSequenceComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorComponentsDisjoint
import Tablet.MissingColorIncidenceEndpoint

set_option maxHeartbeats 3000000

-- [TABLET NODE: P2880_T1_CommonPreparation]
theorem P2880_T1_CommonPreparation
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
    (alpha beta : Fin k)
    (hpathLower : 2 ≤ HierarchyPathNumber C.hierarchy)
    (hpathUpper : HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C)
    (halpha :
      let H := P.counterexample.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
        Fin.last P.corresponding.replacementETT.rounds
      let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
      let j := HierarchyPathNumber C.hierarchy
      let B := HierarchyFullTailPrefix C (j - 2)
      let D := HierarchyStoredColorsAt H q
      let Gamma := D.biUnion (P.counterexample.good.gamma q)
      let baseExtraMissing :=
        ((TreeSequenceVertexSet P.replacementBase.core \
            TreeSequenceVertexSet Tn).biUnion
          fun v => MissingColors G P.coloring v)
      alpha ∈ MissingColors G P.coloring
          (T.vertex (Fin.last T.length)) ∧
        alpha ∈ TreeMissingColors P.coloring B ∧
        (alpha ∉ Gamma ∪ baseExtraMissing ∨
          ∃ eta : Fin k, eta ∈ D ∧
            alpha ∈ P.counterexample.good.gamma q eta ∧
            (HierarchyFirstMissingPosition P.coloring T eta).val ≤
              B.length))
    (hbeta :
      let H := P.counterexample.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let j := HierarchyPathNumber C.hierarchy
      let A := HierarchyStarredStage H q
      let B := HierarchyFullTailPrefix C (j - 2)
      let D := HierarchyStoredColorsAt H q
      let Gamma := D.biUnion (P.counterexample.good.gamma q)
      let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
        Fin.last P.corresponding.replacementETT.rounds
      let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
      let baseExtraMissing :=
        ((TreeSequenceVertexSet P.replacementBase.core \
            TreeSequenceVertexSet Tn).biUnion
          fun v => MissingColors G P.coloring v)
      let tailUsedThroughJ :=
        (Finset.univ : Finset (Fin k)).filter fun c =>
          ∃ r : Fin T.length,
            A.length ≤ r.val ∧ r.val < A.length + j ∧
              P.coloring (T.edge r) = some c
      beta ≠ alpha ∧
        beta ∈ TreeMissingColors P.coloring B ∧
        beta ∉ Gamma ∧ beta ∉ tailUsedThroughJ ∧
        (beta ∉ baseExtraMissing ∪ D ∨
          beta ∈ D ∧
            Disjoint (P.counterexample.good.gamma q beta ∪ {beta})
              tailUsedThroughJ))
    (hcomponentDisjoint :
      let j := HierarchyPathNumber C.hierarchy
      let X := HierarchyFullTailPrefix C (j - 1)
      let Q := TwoColorComponent G P.coloring alpha beta
        (Sum.inl (T.vertex (Fin.last T.length)))
      ∀ v ∈ TreeSequenceVertexSet X, Sum.inl v ∉ Q) :
    Nonempty (P2880_T1_SplitSwapData G k e0 input T phi ett base C ctx P
      alpha beta (TwoColorComponentSwap G P.coloring alpha beta
        (Sum.inl (T.vertex (Fin.last T.length))))) := by
-- BODY
  classical
  let H := P.counterexample.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let j := HierarchyPathNumber C.hierarchy
  let A := HierarchyStarredStage H q
  let B := HierarchyFullTailPrefix C (j - 2)
  let X := HierarchyFullTailPrefix C (j - 1)
  let Y := HierarchyFullTailPrefix C j
  let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
    Fin.last P.corresponding.replacementETT.rounds
  let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
  let D := HierarchyStoredColorsAt H q
  let Gamma := D.biUnion (P.counterexample.good.gamma q)
  let K := TwoColorComponent G P.coloring alpha beta
    (Sum.inl (T.vertex (Fin.last T.length)))
  let sigma := TwoColorComponentSwap G P.coloring alpha beta
    (Sum.inl (T.vertex (Fin.last T.length)))
  rcases halpha with ⟨hAlphaTerminal, hAlphaB, hAlphaChoice⟩
  rcases hbeta with ⟨hBetaNe, hBetaB, hBetaNotGamma, hBetaNotUsed, hBetaChoice⟩
  have hne : alpha ≠ beta := by
    intro he
    exact hBetaNe he.symm
  have hpath : TwoColorPathComponent G P.coloring alpha beta
      (Sum.inl (T.vertex (Fin.last T.length))) := by
    refine ⟨hne, Sum.inl (T.vertex (Fin.last T.length)), rfl, ?_⟩
    have hd := MissingColorIncidenceEndpoint G P.coloring alpha beta hne
      P.minimumContext.proper (T.vertex (Fin.last T.length)) hAlphaTerminal
    rw [← SimpleGraph.card_neighborFinset_eq_degree] at hd
    intro x hx y hy
    change (TwoColorIncidenceGraph G P.coloring alpha beta).Adj
      (Sum.inl (T.vertex (Fin.last T.length))) x at hx
    change (TwoColorIncidenceGraph G P.coloring alpha beta).Adj
      (Sum.inl (T.vertex (Fin.last T.length))) y at hy
    exact Finset.card_le_one.mp hd x
      (by simpa only [SimpleGraph.mem_neighborFinset] using hx) y
      (by simpa only [SimpleGraph.mem_neighborFinset] using hy)
  have hsigma : sigma = TwoColorComponentSwap G P.coloring alpha beta
      (Sum.inl (T.vertex (Fin.last T.length))) := rfl
  have hsigmaProper : IsProperEdgeColoring G sigma := by
    dsimp [sigma]
    exact TwoColorComponentSwapProper G P.coloring alpha beta hne
      P.minimumContext.proper _
  have hsigmaOne : IsOneEdgeUncolored sigma e0 := by
    dsimp [sigma]
    refine ⟨?_, ?_⟩
    · simp [TwoColorComponentSwap, P.minimumContext.oneEdgeUncolored.1]
    · intro f hf
      obtain ⟨c, hc⟩ := P.minimumContext.oneEdgeUncolored.2 f hf
      by_cases ha : c = alpha
      · subst c
        by_cases hK : Sum.inr f ∈ K
        · exact ⟨beta, by simp [TwoColorComponentSwap, K, hK, hc]⟩
        · exact ⟨alpha, by simp [TwoColorComponentSwap, K, hK, hc]⟩
      · by_cases hb : c = beta
        · subst c
          by_cases hK : Sum.inr f ∈ K
          · exact ⟨alpha, by simp [TwoColorComponentSwap, K, hK, hc, hne.symm]⟩
          · exact ⟨beta, by simp [TwoColorComponentSwap, K, hK, hc]⟩
        · exact ⟨c, by
            simp [TwoColorComponentSwap, K, hne, ha, hb, hc]⟩
  have hsplitAvoid : ∀ v ∈ TreeSequenceVertexSet X, Sum.inl v ∉ K := by
    simpa only [X, K] using hcomponentDisjoint
  have hstar : HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount) = A :=
    (P2752_T2_HierarchyMeasures C.hierarchy P.counterexample.hierarchy P.sameGood.1).1
  have hstarToTOriginal : TreeSequenceInitialSegment
      (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount)) T := by
    let H₀ := C.hierarchy
    let q₀ : Fin (H₀.dividerCount + 1) := Fin.last H₀.dividerCount
    have starStep : TreeSequenceInitialSegment
        (HierarchyStarredStage H₀ q₀) (H₀.stage q₀.succ) := by
      refine Fin.cases ?_ (fun i => ?_) q₀
      · exact H₀.coreInsideFirst
      · exact H₀.nested i.succ
    have hlast : q₀.succ = Fin.last (H₀.dividerCount + 1) := by
      apply Fin.ext
      rfl
    simpa [H₀, q₀, hlast, H₀.terminalStage] using starStep
  have hA_T : TreeSequenceInitialSegment A T := by
    rw [← hstar]
    exact hstarToTOriginal
  have commonPrefix {S U W : TreeSequence G e0}
      (hSW : TreeSequenceInitialSegment S W)
      (hUW : TreeSequenceInitialSegment U W) (hSU : S.length ≤ U.length) :
      TreeSequenceInitialSegment S U := by
    rcases hSW with ⟨hSWl, hSWv, hSWe⟩
    rcases hUW with ⟨hUWl, hUWv, hUWe⟩
    refine ⟨hSU, ?_, ?_⟩
    · intro i
      calc
        U.vertex (Fin.castLE (Nat.succ_le_succ hSU) i) =
            W.vertex (Fin.castLE (Nat.succ_le_succ hUWl)
              (Fin.castLE (Nat.succ_le_succ hSU) i)) :=
          (hUWv _).symm
        _ = W.vertex (Fin.castLE (Nat.succ_le_succ hSWl) i) := by congr 1
        _ = S.vertex i := hSWv i
    · intro i
      calc
        U.edge (Fin.castLE hSU i) = W.edge (Fin.castLE hUWl (Fin.castLE hSU i)) :=
          (hUWe _).symm
        _ = W.edge (Fin.castLE hSWl i) := by congr 1
        _ = S.edge i := hSWe i
  have hprefixA_B : TreeSequenceInitialSegment A B := by
    dsimp only [B, HierarchyFullTailPrefix]
    rw [← hstar]
    have hlen :
        (HierarchyStarredStage C.hierarchy
          (Fin.last C.hierarchy.dividerCount)).length ≤
          min ((HierarchyStarredStage C.hierarchy
            (Fin.last C.hierarchy.dividerCount)).length + (j - 2)) T.length := by
      have hj : 2 ≤ j := by dsimp [j]; exact hpathLower
      exact Nat.le_min.mpr ⟨by omega, hstarToTOriginal.1⟩
    refine ⟨hlen, ?_, ?_⟩
    · intro i
      exact hstarToTOriginal.2.1 i
    · intro i
      exact hstarToTOriginal.2.2 i
  have prefixOfT (S : TreeSequence G e0) (m : ℕ)
      (hm : 1 ≤ m) (hmS : m ≤ S.length) :
      TreeSequenceInitialSegment (TreeSequencePrefix S m hm hmS) S := by
    refine ⟨hmS, ?_, ?_⟩
    · intro i
      simp [TreeSequencePrefix]
    · intro i
      simp [TreeSequencePrefix]
  have hB_T : TreeSequenceInitialSegment B T := by
    dsimp [B, HierarchyFullTailPrefix]
    apply prefixOfT T _ ?_ (Nat.min_le_right _ _)
    apply Nat.le_min.mpr
    constructor
    · have hA := (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount)).positive
      omega
    · exact T.positive
  have hX_T : TreeSequenceInitialSegment X T := by
    dsimp [X, HierarchyFullTailPrefix]
    apply prefixOfT T _ ?_ (Nat.min_le_right _ _)
    apply Nat.le_min.mpr
    constructor
    · have hA := (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount)).positive
      omega
    · exact T.positive
  have hY_T : TreeSequenceInitialSegment Y T := by
    dsimp [Y, HierarchyFullTailPrefix]
    apply prefixOfT T _ ?_ (Nat.min_le_right _ _)
    apply Nat.le_min.mpr
    constructor
    · have hA := (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount)).positive
      omega
    · exact T.positive
  have hprefixB_X : TreeSequenceInitialSegment B X := by
    apply commonPrefix hB_T hX_T
    change min ((HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length + (j - 2)) T.length ≤
      min ((HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length + (j - 1)) T.length
    have hj : 2 ≤ j := by dsimp [j]; exact hpathLower
    exact min_le_min (by omega) le_rfl
  have hprefixX_Y : TreeSequenceInitialSegment X Y := by
    apply commonPrefix hX_T hY_T
    change min ((HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length + (j - 1)) T.length ≤
      min ((HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length + j) T.length
    exact min_le_min (by omega) le_rfl
  have prefixTrans {S U W : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U)
      (hUW : TreeSequenceInitialSegment U W) :
      TreeSequenceInitialSegment S W := by
    rcases hSU with ⟨hSUl, hSUv, hSUe⟩
    rcases hUW with ⟨hUWl, hUWv, hUWe⟩
    refine ⟨hSUl.trans hUWl, ?_, ?_⟩
    · intro i
      exact (hUWv (Fin.castLE (Nat.succ_le_succ hSUl) i)).trans (hSUv i)
    · intro i
      exact (hUWe (Fin.castLE hSUl i)).trans (hSUe i)
  have stageSegment : ∀ (a d : ℕ)
      (hbound : a + d ≤ H.dividerCount + 1),
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
        (H.stage ⟨a + d, by omega⟩) := by
    intro a d
    induction d with
    | zero => intro _; exact ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
    | succ d ih =>
      intro hbound
      have hp := ih (by omega)
      have hn := H.nested ⟨a + d, by omega⟩
      have hn' : TreeSequenceInitialSegment
          (H.stage ⟨a + d, by omega⟩)
          (H.stage ⟨a + (d + 1), by omega⟩) := by
        simpa [Nat.add_assoc] using hn
      exact prefixTrans hp hn'
  have coreA : TreeSequenceInitialSegment P.replacementBase.core A := by
    by_cases hz : H.dividerCount = 0
    · have hAeq : A = P.replacementBase.core := by
        obtain hq0 | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ q
        · change HierarchyStarredStage H q = P.replacementBase.core
          rw [hq0]
          rfl
        · have hcount : H.dividerCount ≠ 0 := by
            intro h
            have hv := congrArg Fin.val hi
            simp [q, h] at hv
          exact False.elim (hcount hz)
      rw [hAeq]
      exact ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
    · have hstarStage : A = H.stage ⟨H.dividerCount, by omega⟩ := by
        obtain hzero | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ q
        · have hcount : H.dividerCount = 0 := by
            have hv := congrArg Fin.val hzero
            simp [q] at hv
            omega
          exact False.elim (hz hcount)
        · change HierarchyStarredStage H q = H.stage ⟨H.dividerCount, by omega⟩
          rw [hi]
          unfold HierarchyStarredStage
          simp only [Fin.cases_succ]
          congr 1
          apply Fin.ext
          simpa [q] using (congrArg Fin.val hi).symm
      rw [hstarStage]
      have hfirst : TreeSequenceInitialSegment P.replacementBase.core
          (H.stage ⟨1, by omega⟩) := H.coreInsideFirst
      have hrest := stageSegment 1 (H.dividerCount - 1) (by omega)
      convert prefixTrans hfirst hrest using 1 <;>
        apply congrArg H.stage <;> apply Fin.ext <;> simp <;> omega
  have hTnCore : TreeSequenceInitialSegment Tn P.replacementBase.core := by
    by_cases hpe : P.corresponding.replacementETT.series.data.kind n =
        some TashkinovExtensionKind.PE
    · obtain ⟨_, _, ⟨u⟩⟩ := P.replacementBase.parallel hpe
      simpa [Tn, n] using u.leftSegment
    · rw [P.replacementBase.nonparallel hpe]
      exact ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
  have hTnA : TreeSequenceInitialSegment Tn A := prefixTrans hTnCore coreA
  have hTnX : TreeSequenceInitialSegment Tn X :=
    prefixTrans hTnA (prefixTrans hprefixA_B hprefixB_X)
  have terminalRoute := P2813_T1_TerminalRoute G k e0
    P.corresponding.replacementInput T P.coloring
    P.corresponding.replacementETT
  have htailP : HierarchyFullTailLength P.counterexample = HierarchyFullTailLength C := by
    change T.length - A.length =
      T.length - (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount)).length
    rw [← hstar]
  have hprefixP : ∀ i : Nat, HierarchyFullTailPrefix P.counterexample i =
      HierarchyFullTailPrefix C i := by
    intro i
    have hs : HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount) =
        HierarchyStarredStage P.counterexample.hierarchy
          (Fin.last P.counterexample.hierarchy.dividerCount) := hstar
    unfold HierarchyFullTailPrefix
    dsimp only
    simp only [← hs]
  let Z := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)
  have hZeq : HierarchyFullTailPrefix P.counterexample
      (HierarchyFullTailLength P.counterexample - 1) = Z := by
    rw [htailP, hprefixP]
  have hZ_T : TreeSequenceInitialSegment Z T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hX_Z : TreeSequenceInitialSegment X Z := by
    apply commonPrefix hX_T hZ_T
    change min ((HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length + (j - 1)) T.length ≤
      min ((HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length +
        (T.length - (HierarchyStarredStage C.hierarchy
          (Fin.last C.hierarchy.dividerCount)).length - 1)) T.length
    have hu : j < T.length - (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount)).length := hpathUpper
    exact min_le_min (by omega) le_rfl
  have hZElementary : ColoredVertexSetElementary G P.coloring
      (TreeSequenceVertexSet Z) := by
    rw [← hZeq]
    exact HierarchyCounterexamplePenultimateElementary G k e0
      P.corresponding.replacementInput T P.coloring
      P.corresponding.replacementETT P.replacementBase P.counterexample
      P.minimumContext.proper P.minimumContext.oneEdgeUncolored
      P.minimumContext.lowerRung P.minimumContext.fewerDividers
      P.minimumContext.lexicographicMinimality P.minimumContext.largeMissingSet
  obtain ⟨hincidentFixed, hpenMissing⟩ := P2880_T1_ElementaryPrefixSwap G P.coloring
    alpha beta hne P.minimumContext.proper B X Z hprefixB_X hX_Z hZElementary
    hAlphaB hBetaB (Sum.inl (T.vertex (Fin.last T.length))) hsplitAvoid
  have hB_missingEq : ∀ v, v ∈ TreeSequenceVertexSet B →
      MissingColors G sigma v = MissingColors G P.coloring v := by
    intro v hv
    have hvX : v ∈ TreeSequenceVertexSet X :=
      TreeSequenceInitialSegmentVertexSetSubset hprefixB_X hv
    have hbehavior := TwoColorComponentSwapMissingBehavior G P.coloring
      alpha beta hne P.minimumContext.proper
      (Sum.inl (T.vertex (Fin.last T.length)))
    exact hbehavior.1 v (hsplitAvoid v hvX)
  have hfixedX : ∀ t : Fin X.length, sigma (X.edge t) = P.coloring (X.edge t) := by
    intro t
    obtain ⟨i, hi⟩ := X.attaches t
    apply hincidentFixed (X.vertex t.succ) (by simp [TreeSequenceVertexSet])
      (X.edge t)
    change X.vertex t.succ ∈ G.ends (X.edge t)
    rw [hi]
    exact Sym2.mem_mk_left _ _
  have hlenBX : X.length = B.length + 1 := by
    change min ((HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length + (j - 1)) T.length =
      min ((HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length + (j - 2)) T.length + 1
    have hj : j < T.length -
        (HierarchyStarredStage C.hierarchy
          (Fin.last C.hierarchy.dividerCount)).length := by
      change j < HierarchyFullTailLength C at hpathUpper
      simpa [HierarchyFullTailLength] using hpathUpper
    have hlow : (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount)).length + j ≤ T.length := by omega
    simp [Nat.min_eq_left (by omega :
      (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount)).length + (j - 1) ≤ T.length),
      Nat.min_eq_left (by omega :
      (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount)).length + (j - 2) ≤ T.length)]
    omega
  have hAXstrict : A.length < X.length := by
    rw [← hstar]
    change (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount)).length <
      min ((HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount)).length + (j - 1)) T.length
    have hj : j < T.length -
        (HierarchyStarredStage C.hierarchy
          (Fin.last C.hierarchy.dividerCount)).length := by
      change j < HierarchyFullTailLength C at hpathUpper
      simpa [HierarchyFullTailLength] using hpathUpper
    exact Nat.lt_min.mpr ⟨by omega, by omega⟩
  have seedPrefixX {f : E} {seed : TreeSequence G e0}
      (hadjoin : TreeSequenceAdjoinEdge Tn f seed)
      (hroute : TashkinovAugmentationSequence P.coloring seed T) :
      TreeSequenceInitialSegment seed X := by
    have hseedT := TashkinovAugmentationSequenceInitialSegment
      P.coloring seed T hroute
    have hlen : seed.length ≤ X.length := by
      rw [hadjoin.1]
      have hAX := prefixTrans hprefixA_B hprefixB_X
      have hTnA_len := hTnA.1
      have hAXstrict' := hAXstrict
      omega
    exact commonPrefix hseedT hX_T hlen
  have switchedRoute {S : TreeSequence G e0}
      (hroute : TashkinovAugmentationSequence P.coloring S X) :
      TashkinovAugmentationSequence sigma S X := by
    exact TashkinovAugmentationSequenceColoringTransport
      P.coloring sigma S B X hroute hprefixB_X hlenBX
        (by intro t _; exact hfixedX t) hB_missingEq
  have oldSuffix : TashkinovAugmentationSequence P.coloring X T := by
    rcases terminalRoute with ⟨_, hroute⟩ |
      ⟨_, f, seed, _, hadjoin, _, _, hroute⟩
    · exact TashkinovAugmentationSequenceSuffix P.coloring Tn X T hroute
        hTnX hX_T
    · exact TashkinovAugmentationSequenceSuffix P.coloring seed X T hroute
        (seedPrefixX hadjoin hroute) hX_T
  have routeToX :
      (P.corresponding.replacementETT.series.data.kind n =
          some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma Tn X) ∨
      ((P.corresponding.replacementETT.series.data.kind n =
            some TashkinovExtensionKind.SE ∨
          P.corresponding.replacementETT.series.data.kind n =
            some TashkinovExtensionKind.RE) ∧
        ∃ f : E, ∃ seed : TreeSequence G e0,
          P.corresponding.replacementETT.series.data.connectingEdges n = {f} ∧
            TreeSequenceAdjoinEdge Tn f seed ∧
              TashkinovAugmentationSequence sigma seed X) := by
    rcases terminalRoute with ⟨hPE, hroute⟩ |
      ⟨hNonPE, f, seed, hconnecting, hadjoin, _, _, hroute⟩
    · exact Or.inl ⟨hPE,
        switchedRoute (TashkinovAugmentationSequenceRestrict P.coloring Tn X T
          hroute hTnX hX_T)⟩
    · rcases hNonPE with hs | hr
      · exact Or.inr ⟨Or.inl hs, f, seed, hconnecting, hadjoin,
          switchedRoute (TashkinovAugmentationSequenceRestrict P.coloring seed X T
            hroute (seedPrefixX hadjoin hroute)
            hX_T)⟩
      · exact Or.inr ⟨Or.inr hr, f, seed, hconnecting, hadjoin,
          switchedRoute (TashkinovAugmentationSequenceRestrict P.coloring seed X T
            hroute (seedPrefixX hadjoin hroute)
            hX_T)⟩
  have hAlphaMissingX : alpha ∈ TreeMissingColors sigma X := by
    unfold TreeMissingColors at hAlphaB ⊢
    rcases Finset.mem_biUnion.mp hAlphaB with ⟨v, hv, hmiss⟩
    refine Finset.mem_biUnion.mpr ⟨v,
      TreeSequenceInitialSegmentVertexSetSubset hprefixB_X hv, ?_⟩
    rw [hB_missingEq v hv]
    exact hmiss
  have hBetaMissingX : beta ∈ TreeMissingColors sigma X := by
    unfold TreeMissingColors at hBetaB ⊢
    rcases Finset.mem_biUnion.mp hBetaB with ⟨v, hv, hmiss⟩
    refine Finset.mem_biUnion.mpr ⟨v,
      TreeSequenceInitialSegmentVertexSetSubset hprefixB_X hv, ?_⟩
    rw [hB_missingEq v hv]
    exact hmiss
  have hsplitMissing : alpha ∈ TreeMissingColors sigma X ∧
      beta ∈ TreeMissingColors sigma X := ⟨hAlphaMissingX, hBetaMissingX⟩
  have switchedSuffix : TashkinovAugmentationSequence sigma X T :=
    TashkinovAugmentationSequenceComponentSwap G k e0 P.coloring alpha beta
      hne (Sum.inl (T.vertex (Fin.last T.length))) X T oldSuffix
      hsplitMissing.1 hsplitMissing.2
  have firstPositionOnB (eta : Fin k) :
      HierarchyFirstMissingPosition sigma B eta =
        HierarchyFirstMissingPosition P.coloring B eta := by
    let cs : Finset (Fin (B.length + 1)) := Finset.univ.filter
      fun i => eta ∈ MissingColors G sigma (B.vertex i)
    let cp : Finset (Fin (B.length + 1)) := Finset.univ.filter
      fun i => eta ∈ MissingColors G P.coloring (B.vertex i)
    have hsets : cs = cp := by
      ext i
      simp only [cs, cp, Finset.mem_filter, Finset.mem_univ, true_and]
      have hv : B.vertex i ∈ TreeSequenceVertexSet B := by
        simp [TreeSequenceVertexSet]
      rw [hB_missingEq (B.vertex i) hv]
    unfold HierarchyFirstMissingPosition
    change (if h : cs.Nonempty then cs.min' h else Fin.last B.length) =
      (if h : cp.Nonempty then cp.min' h else Fin.last B.length)
    rw [hsets]
  have firstPositionBoundOnT {rho : PartialEdgeColoring E k} {eta : Fin k}
      (hm : eta ∈ TreeMissingColors rho B) :
      (HierarchyFirstMissingPosition rho T eta).val ≤ B.length := by
    unfold TreeMissingColors at hm
    rcases Finset.mem_biUnion.mp hm with ⟨v, hv, hmiss⟩
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hv
    rcases hv with ⟨i, rfl⟩
    let it : Fin (T.length + 1) := Fin.castLE
      (Nat.succ_le_succ hB_T.1) i
    have hmissT : eta ∈ MissingColors G rho (T.vertex it) := by
      rw [hB_T.2.1 i]
      exact hmiss
    have hne : (Finset.univ : Finset (Fin (T.length + 1))).filter
        (fun r => eta ∈ MissingColors G rho (T.vertex r)) |>.Nonempty := by
      exact ⟨it, by simp [hmissT]⟩
    unfold HierarchyFirstMissingPosition
    dsimp only
    rw [dif_pos hne]
    have hle := Finset.min'_le
      ((Finset.univ : Finset (Fin (T.length + 1))).filter
        (fun r => eta ∈ MissingColors G rho (T.vertex r))) it
      (by simp [hmissT])
    exact le_trans hle (by simp [it]; omega)
  have firstPositionEqualOnTail (eta : Fin k)
      (hm : eta ∈ TreeMissingColors P.coloring B) :
      HierarchyFirstMissingPosition sigma T eta =
        HierarchyFirstMissingPosition P.coloring T eta := by
    have hmSigma : eta ∈ TreeMissingColors sigma B := by
      simp only [TreeMissingColors, Finset.mem_biUnion] at hm ⊢
      rcases hm with ⟨v, hv, hmiss⟩
      exact ⟨v, hv, by rw [hB_missingEq v hv]; exact hmiss⟩
    have hcutSigma := HierarchyFirstMissingPositionPrefixCutoff
      sigma B T hB_T eta B.length le_rfl
    have hcutPhi := HierarchyFirstMissingPositionPrefixCutoff
      P.coloring B T hB_T eta B.length le_rfl
    have htrunc :
        min (HierarchyFirstMissingPosition sigma T eta).val B.length =
          min (HierarchyFirstMissingPosition P.coloring T eta).val
            B.length := by
      calc
        _ = min (HierarchyFirstMissingPosition sigma B eta).val
              B.length := hcutSigma.symm
        _ = min (HierarchyFirstMissingPosition P.coloring B eta).val
              B.length := by rw [firstPositionOnB eta]
        _ = _ := hcutPhi
    have hboundSigma := firstPositionBoundOnT hmSigma
    have hboundPhi := firstPositionBoundOnT hm
    apply Fin.ext
    rw [min_eq_left hboundSigma, min_eq_left hboundPhi] at htrunc
    exact htrunc
  have firstPositionGloballyEqual (eta : Fin k)
      (hα : eta ≠ alpha) (hβ : eta ≠ beta) :
      HierarchyFirstMissingPosition sigma T eta =
        HierarchyFirstMissingPosition P.coloring T eta := by
    let cs : Finset (Fin (T.length + 1)) := Finset.univ.filter
      fun i => eta ∈ MissingColors G sigma (T.vertex i)
    let cp : Finset (Fin (T.length + 1)) := Finset.univ.filter
      fun i => eta ∈ MissingColors G P.coloring (T.vertex i)
    have hsets : cs = cp := by
      ext i
      simp only [cs, cp, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (TwoColorComponentSwapMissingBehavior G P.coloring alpha beta hne
        P.minimumContext.proper (Sum.inl (T.vertex (Fin.last T.length)))).2.2.2
          (T.vertex i) eta hα hβ
    unfold HierarchyFirstMissingPosition
    change (if h : cs.Nonempty then cs.min' h else Fin.last T.length) =
      (if h : cp.Nonempty then cp.min' h else Fin.last T.length)
    rw [hsets]
  have hstoredFirst : ∀ eta, eta ∈ D →
      HierarchyFirstMissingPosition sigma T eta =
        HierarchyFirstMissingPosition P.coloring T eta := by
    intro eta hD
    by_cases hα : eta = alpha
    · subst eta
      exact firstPositionEqualOnTail alpha hAlphaB
    · by_cases hβ : eta = beta
      · subst eta
        exact firstPositionEqualOnTail beta hBetaB
      · exact firstPositionGloballyEqual eta hα hβ
  have hgammaCutoff : ∀ eta, eta ∈ D →
      (alpha ∈ P.counterexample.good.gamma q eta ∨
        beta ∈ P.counterexample.good.gamma q eta) →
      (HierarchyFirstMissingPosition P.coloring T eta).val ≤ X.length := by
    intro eta hD hgamma
    rcases hAlphaChoice with houtside | ⟨eta₀, hD₀, howner, hcut⟩
    · rcases hgamma with hα | hβ
      · exact (houtside (Finset.mem_union_left _
          (Finset.mem_biUnion.mpr ⟨eta, hD, hα⟩))).elim
      · exact (hBetaNotGamma
          (Finset.mem_biUnion.mpr ⟨eta, hD, hβ⟩)).elim
    · have hβNotGamma := hBetaNotGamma
      rcases hgamma with hα | hβ
      · have heq : eta = eta₀ := by
          by_contra hneEta
          have hdisjoint := P.counterexample.good.disjointPairs
            q eta eta₀ hD hD₀ hneEta
          exact Finset.disjoint_left.mp hdisjoint hα howner
        subst eta
        exact le_trans hcut hprefixB_X.1
      · exact (hβNotGamma (Finset.mem_biUnion.mpr ⟨eta, hD, hβ⟩)).elim
  have hAX : TreeSequenceInitialSegment A X :=
    prefixTrans hprefixA_B hprefixB_X
  have fixedUntilSplitEnd (r : Fin T.length) (hr : r.val ≤ X.length) :
      sigma (T.edge r) = P.coloring (T.edge r) := by
    obtain ⟨i, hi⟩ := T.attaches r
    let ix : Fin (X.length + 1) := ⟨i.val, by omega⟩
    let it : Fin (T.length + 1) :=
      Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ r.isLt))
    have hcast : Fin.castLE (Nat.succ_le_succ hX_T.1) ix = it := Fin.ext rfl
    have hv : T.vertex it = X.vertex ix := by
      rw [← hcast]
      exact hX_T.2.1 ix
    apply hincidentFixed (T.vertex it)
      (by rw [hv]; simp [TreeSequenceVertexSet]) (T.edge r)
    change T.vertex it ∈ G.ends (T.edge r)
    rw [hi]
    exact Sym2.mem_mk_right _ _
  have hXlen : X.length = A.length + (j - 1) := by
    rw [← hstar]
    change min ((HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length + (j - 1)) T.length =
      (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)).length +
        (j - 1)
    have hu : j < T.length - (HierarchyStarredStage C.hierarchy
        (Fin.last C.hierarchy.dividerCount)).length := hpathUpper
    omega
  have hseparated (c : Fin k) (hc : c ∈ TreeMissingColors P.coloring B) :
      Disjoint K (TwoColorComponent G P.coloring alpha beta
        (Sum.inl (T.vertex (HierarchyFirstMissingPosition P.coloring T c)))) := by
    let p := HierarchyFirstMissingPosition P.coloring T c
    have hp : p.val ≤ B.length := firstPositionBoundOnT hc
    let ib : Fin (B.length + 1) := ⟨p.val, by omega⟩
    have hcast : Fin.castLE (Nat.succ_le_succ hB_T.1) ib = p := Fin.ext rfl
    have hvB : T.vertex p ∈ TreeSequenceVertexSet B := by
      rw [← hcast, hB_T.2.1 ib]
      simp [TreeSequenceVertexSet]
    have hvX := TreeSequenceInitialSegmentVertexSetSubset hprefixB_X hvB
    apply Set.disjoint_left.mpr
    intro x hx hy
    apply hsplitAvoid (T.vertex p) hvX
    change (TwoColorIncidenceGraph G P.coloring alpha beta).connectedComponentMk x =
      (TwoColorIncidenceGraph G P.coloring alpha beta).connectedComponentMk
        (Sum.inl (T.vertex (Fin.last T.length))) at hx
    change (TwoColorIncidenceGraph G P.coloring alpha beta).connectedComponentMk x =
      (TwoColorIncidenceGraph G P.coloring alpha beta).connectedComponentMk
        (Sum.inl (T.vertex p)) at hy
    exact hy.symm.trans hx
  have missingOnB {c : Fin k} (hc : c ∈ TreeMissingColors P.coloring B) :
      c ∈ TreeMissingColors sigma B := by
    obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr ⟨v, hv, by rw [hB_missingEq v hv]; exact hm⟩
  have oldMissingOnZ {c : Fin k} (hc : c ∈ TreeMissingColors P.coloring B) :
      c ∈ TreeMissingColors P.coloring Z := by
    obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr ⟨v, TreeSequenceInitialSegmentVertexSetSubset hX_Z
      (TreeSequenceInitialSegmentVertexSetSubset hprefixB_X hv), hm⟩
  refine ⟨{
    swapped := hsigma
    distinct := hne
    path := hpath
    splitOutside := hsplitAvoid
    twoBeforeInSplit := hprefixB_X
    splitInFull := hX_T
    splitAboveStar := ⟨hAX, hAXstrict⟩
    splitInPenultimate := ?_
    coreInSplit := prefixTrans coreA hAX
    penultimateElementary := ?_
    proper := hsigmaProper
    oneEdgeUncolored := hsigmaOne
    invariant := ?_
    incidentFixed := hincidentFixed
    fixedOnSplit := fun r hr => fixedUntilSplitEnd r (Nat.le_of_lt hr)
    fixedThroughJ := ?_
    missingTwoBefore := ⟨missingOnB hAlphaB, missingOnB hBetaB⟩
    missingOnSplit := hsplitMissing
    oldMissingOnPenultimate := ?_
    missingTerminal := ?_
    penultimateMissing := ?_
    storedFirst := hstoredFirst
    gammaCutoff := hgammaCutoff
    separatedAlpha := hseparated alpha hAlphaB
    separatedBeta := hseparated beta hBetaB
    prefixRoute := routeToX
    oldSuffix := oldSuffix
    newSuffix := switchedSuffix }⟩
  · rw [hZeq]
    exact hX_Z
  · rw [hZeq]
    exact hZElementary
  · refine ⟨fun r _ => hfixedX r, ?_⟩
    intro v hv
    exact hpenMissing v (TreeSequenceInitialSegmentVertexSetSubset hX_Z hv)
  · dsimp only
    intro r _ hr
    apply fixedUntilSplitEnd r
    rw [hXlen]
    change r.val < A.length + j at hr
    have hj : 2 ≤ j := hpathLower
    omega
  · rw [hZeq]
    exact ⟨oldMissingOnZ hAlphaB, oldMissingOnZ hBetaB⟩
  · exact (TwoColorComponentSwapMissingBehavior G P.coloring alpha beta hne
      P.minimumContext.proper (Sum.inl (T.vertex (Fin.last T.length)))).2.1
        (T.vertex (Fin.last T.length)) rfl hAlphaTerminal
  · rw [hZeq]
    exact hpenMissing
