import Tablet.ChangeLemma
import Tablet.ColoredVertexSetElementary
import Tablet.CombinedStableClosurePreserved
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.GoodHierarchyReservedDisjoint
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyNonparallelFirstEdge
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchySegmentColors
import Tablet.HierarchySituationTwoCaseOneData
import Tablet.HierarchySituationTwoCaseOneTwoData
import Tablet.HierarchySituationTwoCaseTwoData
import Tablet.HierarchySituationTwoSubcaseOneOne
import Tablet.HierarchySituationTwoSubcaseTwoOne
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyTailMissingColorExclusion
import Tablet.HierarchyWeaklyStable
import Tablet.IsOneEdgeUncolored
import Tablet.MissingColors
import Tablet.ModColoring
import Tablet.OrderedTreeUnion
import Tablet.SameGoodHierarchy
import Tablet.StableColoring
import Tablet.StableChangeCasesOneTwo
import Tablet.StableChangeCasesOneTwoFullTail
import Tablet.StableChangeCasesOneTwoSplitTail
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceColoringTransport
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovClosure
import Tablet.TashkinovHierarchy
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeColoringInvariant
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent
import Tablet.sc2
import Tablet.HierarchyReplacementPresentationTrans
import Tablet.MissingColorIncidenceEndpoint
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TreeSequenceInitialSegmentVertexSetSubset

-- [TABLET NODE: HierarchySituationTwoSubcaseOneTwo]
theorem HierarchySituationTwoSubcaseOneTwo {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseOneTwoData
      G k e0 input T phi ett base C ctx) :
    False := by
-- BODY
  classical
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let B := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)
  have htail : 2 ≤ T.length - A.length := D.tailAtLeastTwo
  have hBlen : B.length + 1 = T.length := by
    simp only [B, HierarchyFullTailPrefix, HierarchyFullTailLength,
      TreeSequencePrefix]
    change min (A.length + (T.length - A.length - 1)) T.length + 1 = T.length
    omega
  have hBT : TreeSequenceInitialSegment B T := by
    refine ⟨?_, ?_, ?_⟩
    · omega
    · intro i
      rfl
    · intro i
      rfl
  have hApositive (hq : 0 < H.dividerCount) :
      A = H.stage ⟨H.dividerCount, by omega⟩ := by
    have hi : q = (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ := by
      apply Fin.ext
      simp [q]
      omega
    change HierarchyStarredStage H q = _
    rw [hi]
    simp [HierarchyStarredStage]
    congr 1
    apply Fin.ext
    simp
    omega
  have hAzero (hq : H.dividerCount = 0) : A = base.core := by
    have hi : q = 0 := by apply Fin.ext; simp [q, hq]
    change HierarchyStarredStage H q = _
    rw [hi]
    rfl
  have hAT : TreeSequenceInitialSegment A T := by
    by_cases hz : H.dividerCount = 0
    · have hi : (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) =
          Fin.last (H.dividerCount + 1) := by apply Fin.ext; simp [hz]
      simpa [hAzero hz, hi, H.terminalStage] using H.coreInsideFirst
    · rw [hApositive (Nat.pos_of_ne_zero hz)]
      have hi : (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) =
          q.castSucc := Fin.ext rfl
      have hj : H.stage q.succ = T := by
        convert H.terminalStage using 1
        congr 1
      simpa only [hi, hj] using H.nested q
  have hAB : TreeSequenceInitialSegment A B := by
    refine ⟨by omega, ?_, ?_⟩
    · intro i
      exact hAT.2.1 i
    · intro i
      exact hAT.2.2 i
  have hBterminal : B.vertex (Fin.last B.length) = T.vertex D.penultimateVertexIndex := by
    rw [← hBT.2.1 (Fin.last B.length)]
    congr 1
    apply Fin.ext
    have hp := D.penultimateVertexPosition
    simp only [Fin.val_castLE, Fin.val_last]
    omega
  have hyB : T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet B := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨Fin.last B.length, hBterminal⟩
  have hElementary : ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) :=
    HierarchyCounterexamplePenultimateElementary G k e0 input T phi ett base C
      ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
      ctx.lexicographicMinimality ctx.largeMissingSet
  have firstAt {c : Fin k}
      (hc : c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex)) :
      HierarchyFirstMissingPosition phi T c = D.penultimateVertexIndex := by
    let candidates := Finset.univ.filter fun i : Fin (T.length + 1) =>
      c ∈ MissingColors G phi (T.vertex i)
    have hy : D.penultimateVertexIndex ∈ candidates := by simp [candidates, hc]
    have hn : candidates.Nonempty := ⟨_, hy⟩
    have hmin := Finset.min'_le candidates _ hy
    have hm : c ∈ MissingColors G phi (T.vertex (candidates.min' hn)) :=
      (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
    have hmem : T.vertex (candidates.min' hn) ∈ TreeSequenceVertexSet B := by
      let j : Fin (B.length + 1) := ⟨(candidates.min' hn).val, by
        have hp := D.penultimateVertexPosition
        change (candidates.min' hn).val ≤ D.penultimateVertexIndex.val at hmin
        omega⟩
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      refine ⟨j, ?_⟩
      rfl
    have heq : candidates.min' hn = D.penultimateVertexIndex := by
      by_contra hne
      have hvne := fun h => hne (T.vertex_injective h)
      exact Finset.disjoint_left.mp (hElementary hmem hyB hvne) hm hc
    simpa only [HierarchyFirstMissingPosition, candidates, dif_pos hn] using heq
  have hfirstAlpha := firstAt D.alphaMissingPenultimate
  have hfirstTheta := firstAt D.thetaMissingPenultimate
  have hnotA {c : Fin k}
      (hc : c ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex)) :
      c ∉ TreeMissingColors phi A := by
    intro ha
    rcases Finset.mem_biUnion.mp ha with ⟨v, hv, hvc⟩
    have hvB := TreeSequenceInitialSegmentVertexSetSubset hAB hv
    have hvne : v ≠ T.vertex D.penultimateVertexIndex := by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
      rcases hv with ⟨i, rfl⟩
      intro he
      have hi := T.vertex_injective ((hAT.2.1 i).trans he)
      have hp := D.penultimateVertexPosition
      have hib := i.isLt
      have hiv := congrArg Fin.val hi
      simp only [Fin.val_castLE] at hiv
      omega
    exact Finset.disjoint_left.mp (hElementary hvB hyB hvne) hvc hc
  have hthetaGamma : D.theta ∉ (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) := by
    intro hc
    rcases Finset.mem_biUnion.mp hc with ⟨eta, heta, hpair⟩
    exact hnotA D.thetaMissingPenultimate
      ((GoodHierarchyReservedDisjoint C.good q).1 eta heta hpair)
  have hgammaPair : D.gammaOne ∈ C.good.gamma q D.alpha := by
    rw [D.gammaPair]
    simp
  have hgammaA : D.gammaOne ∈ TreeMissingColors phi A :=
    (GoodHierarchyReservedDisjoint C.good q).1 D.alpha D.alphaStored hgammaPair
  have hgammaTheta : D.gammaOne ≠ D.theta := by
    intro he
    exact hnotA D.thetaMissingPenultimate (he ▸ hgammaA)
  have hgammaAlpha : D.gammaOne ≠ D.alpha := by
    intro he
    exact hnotA D.alphaMissingPenultimate (he ▸ hgammaA)
  have hthetaExclusion := HierarchyTailMissingColorExclusion G k e0 input T phi
    ett base H hElementary (HierarchyFullTailLength C - 1)
    (by change 1 ≤ T.length - A.length - 1; omega)
    (by change T.length - A.length - 1 < T.length - A.length; omega)
    D.theta (by
      change D.theta ∈ MissingColors G phi (B.vertex (Fin.last B.length))
      rw [hBterminal]
      exact D.thetaMissingPenultimate)
  have hgammaUnused : ∀ t : Fin T.length, A.length ≤ t.val →
      phi (T.edge t) ≠ some D.gammaOne := by
    intro t ht he
    by_cases hlast : t = D.lastEdgeIndex
    · rw [hlast, D.thetaOnLastEdge] at he
      exact hgammaTheta (Option.some.inj he).symm
    · have hav := (Finset.mem_sdiff.mp
        (C.good.avoidance q D.alpha D.alphaStored hgammaPair)).2
      apply hav
      unfold HierarchySegmentColors
      simp only
      have hend : H.stage q.succ = T := by
        convert H.terminalStage using 1
        congr 1
      rw [hend, hfirstAlpha]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, t, ht, ?_, he⟩
      have hp := D.penultimateVertexPosition
      have hl := D.lastEdgePosition
      have hvne : t.val ≠ D.lastEdgeIndex.val := fun he => hlast (Fin.ext he)
      have hb := t.isLt
      omega
  have halphaExclusion := HierarchyTailMissingColorExclusion G k e0 input T phi
    ett base H hElementary (HierarchyFullTailLength C - 1)
    (by change 1 ≤ T.length - A.length - 1; omega)
    (by change T.length - A.length - 1 < T.length - A.length; omega)
    D.alpha (by
      change D.alpha ∈ MissingColors G phi (B.vertex (Fin.last B.length))
      rw [hBterminal]
      exact D.alphaMissingPenultimate)
  have firstWitness (rho : PartialEdgeColoring E k) (X : TreeSequence G e0)
      (hXT : TreeSequenceInitialSegment X T) (c : Fin k)
      (hc : c ∈ TreeMissingColors rho X) :
      c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
      (HierarchyFirstMissingPosition rho T c).val ≤ X.length := by
    clear * - G T rho X hXT c hc
    rcases Finset.mem_biUnion.mp hc with ⟨v, hv, hvc⟩
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv
    rcases hv with ⟨i, rfl⟩
    let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
      c ∈ MissingColors G rho (T.vertex j)
    have hi : Fin.castLE (Nat.succ_le_succ hXT.1) i ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hXT.2.1 i]
      exact hvc
    have hn : candidates.Nonempty := ⟨_, hi⟩
    have hm := (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
    have hle := Finset.min'_le candidates _ hi
    have hib := i.isLt
    unfold HierarchyFirstMissingPosition
    change (c ∈ MissingColors G rho (T.vertex (if h : candidates.Nonempty then
      candidates.min' h else Fin.last T.length))) ∧ _
    rw [dif_pos hn]
    refine ⟨hm, ?_⟩
    change (candidates.min' hn).val ≤ X.length
    change (candidates.min' hn).val ≤ i.val at hle
    omega
  let ig := HierarchyFirstMissingPosition phi T D.gammaOne
  have hfirstGamma := firstWitness phi A hAT D.gammaOne hgammaA
  have higB : T.vertex ig ∈ TreeSequenceVertexSet B := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    have hg : ig.val ≤ A.length := hfirstGamma.2
    refine ⟨⟨ig.val, by omega⟩, ?_⟩
    rfl
  have hgammaStage : D.gammaOne ∈ HierarchyStageMissingColors H q :=
    (Finset.mem_sdiff.mp (C.good.avoidance q D.alpha D.alphaStored hgammaPair)).1
  have hcase :
      (0 < H.dividerCount ∧ D.gammaOne ∈ TreeMissingColors phi
        (H.stage ⟨H.dividerCount, by omega⟩)) ∨
      (H.dividerCount = 0 ∧ D.gammaOne ∈ TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) := by
    by_cases hz : H.dividerCount = 0
    · right
      refine ⟨hz, ?_⟩
      have hi : q = 0 := by apply Fin.ext; simp [q, hz]
      simp only [hi, HierarchyStageMissingColors, Fin.cases] at hgammaStage
      convert hgammaStage using 1 <;> congr 2 <;> apply Fin.ext <;> simp <;> omega
    · left
      refine ⟨Nat.pos_of_ne_zero hz, ?_⟩
      have hi : q = (⟨H.dividerCount - 1, by omega⟩ : Fin H.dividerCount).succ := by
        apply Fin.ext
        simp [q]
        omega
      have hg := hgammaStage
      rw [hi] at hg
      simp [HierarchyStageMissingColors] at hg
      convert hg using 1 <;> congr 2 <;> apply Fin.ext <;> simp <;> omega
  have hmissing : D.gammaOne ∈ TreeMissingColors phi B ∧
      D.alpha ∈ TreeMissingColors phi B := by
    refine ⟨?_, Finset.mem_biUnion.mpr ⟨_, hyB, D.alphaMissingPenultimate⟩⟩
    rcases Finset.mem_biUnion.mp hgammaA with ⟨v, hv, hm⟩
    exact Finset.mem_biUnion.mpr ⟨v, TreeSequenceInitialSegmentVertexSetSubset hAB hv, hm⟩
  have hchange := ChangeLemma G k e0 input T phi ett base C ctx.proper
    ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers ctx.lexicographicMinimality
    hElementary ctx.largeMissingSet D.gammaOne D.alpha hgammaAlpha hmissing
    (by
      dsimp only
      intro _
      rw [hfirstAlpha]
      refine ⟨⟨ig, D.penultimateVertexIndex, rfl, rfl, ?_⟩, ?_⟩
      · have hp := D.penultimateVertexPosition
        have hg : ig.val ≤ A.length := hfirstGamma.2
        clear * - hp hg htail
        omega
      · intro hc
        rcases (Finset.mem_filter.mp hc).2 with ⟨t, ht, _, he⟩
        exact hgammaUnused t ht he)
  have hsame : TwoColorComponent G phi D.gammaOne D.alpha (Sum.inl (T.vertex ig)) =
      TwoColorComponent G phi D.gammaOne D.alpha
        (Sum.inl (T.vertex D.penultimateVertexIndex)) := by
    rw [← hfirstAlpha]
    rcases hcase with ⟨hq, hm⟩ | ⟨hq, hm⟩
    · exact hchange.1 ⟨hq, Or.inl hm⟩
    · exact hchange.2.1 ⟨hq, Or.inl hm⟩
  have self (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V) :
      Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v) := by
    change (TwoColorIncidenceGraph G rho a b).connectedComponentMk (Sum.inl v) = _
    rfl
  have leaf (rho : PartialEdgeColoring E k) (a b : Fin k) (hne : a ≠ b)
      (hp : IsProperEdgeColoring G rho) (v : V)
      (hm : a ∈ MissingColors G rho v ∨ b ∈ MissingColors G rho v) :
      Set.Subsingleton ((TwoColorIncidenceGraph G rho a b).neighborSet (Sum.inl v)) := by
    clear * - G rho a b hne hp v hm
    have hd : @SimpleGraph.degree _ (TwoColorIncidenceGraph G rho a b)
        (Sum.inl v) (Fintype.ofFinite _) ≤ 1 := by
      rcases hm with ha | hb
      · exact MissingColorIncidenceEndpoint G rho a b hne hp v ha
      · have he : TwoColorIncidenceGraph G rho a b = TwoColorIncidenceGraph G rho b a := by
          ext x y
          cases x <;> cases y <;> simp [TwoColorIncidenceGraph, or_comm]
        rw [he]
        exact MissingColorIncidenceEndpoint G rho b a hne.symm hp v hb
    rw [← SimpleGraph.card_neighborFinset_eq_degree] at hd
    intro x hx y hy
    exact Finset.card_le_one_iff.mp hd
      (by simpa [SimpleGraph.mem_neighborFinset] using hx)
      (by simpa [SimpleGraph.mem_neighborFinset] using hy)
  have separate (rho : PartialEdgeColoring E k) (a b : Fin k) (hne : a ≠ b)
      (hp : IsProperEdgeColoring G rho) (u v w : V)
      (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
      (hu : a ∈ MissingColors G rho u) (hv : b ∈ MissingColors G rho v)
      (hw : a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w)
      (hsame : TwoColorComponent G rho a b (Sum.inl u) =
        TwoColorComponent G rho a b (Sum.inl v)) :
      Disjoint (TwoColorComponent G rho a b (Sum.inl w))
        (TwoColorComponent G rho a b (Sum.inl u)) := by
    clear * - G rho a b hne hp u v w huv huw hvw hu hv hw hsame leaf self
    rcases TwoColorComponentsDisjoint G rho a b (Sum.inl w) (Sum.inl u) with he | hd
    · exfalso
      obtain ⟨s, t, p, hpPath, hsupport⟩ :=
        TwoColorComponentSpanningPath G rho a b hp (Sum.inl w)
      have ends (x : V) (hx : Sum.inl x ∈ TwoColorComponent G rho a b (Sum.inl w))
          (hm : a ∈ MissingColors G rho x ∨ b ∈ MissingColors G rho x) :
          Sum.inl x = s ∨ Sum.inl x = t := by
        by_contra hnot
        push_neg at hnot
        have hs : Sum.inl x ∈ p.support := by
          change Sum.inl x ∈ {z | z ∈ p.support}
          rw [hsupport]
          exact hx
        exact hpPath.isTrail.not_mem_support_of_subsingleton_neighborSet
          hnot.1 hnot.2 (leaf rho a b hne hp x hm) hs
      have hue := ends u (he ▸ self rho a b u) (Or.inl hu)
      have hve := ends v (by rw [he, hsame]; exact self rho a b v) (Or.inr hv)
      have hwe := ends w (self rho a b w) hw
      rcases hue with hu | hu <;> rcases hve with hv | hv <;> rcases hwe with hw | hw
      all_goals first
        | exact huv (Sum.inl.inj (hu.trans hv.symm))
        | exact huw (Sum.inl.inj (hu.trans hw.symm))
        | exact hvw (Sum.inl.inj (hv.trans hw.symm))
    · exact hd
  have hgy : T.vertex ig ≠ T.vertex D.penultimateVertexIndex := by
    intro he
    have hi := congrArg Fin.val (T.vertex_injective he)
    have hp := D.penultimateVertexPosition
    have hg : ig.val ≤ A.length := hfirstGamma.2
    omega
  have hgt : T.vertex ig ≠ T.vertex D.terminalVertexIndex := by
    intro he
    have hi := congrArg Fin.val (T.vertex_injective he)
    have hp := D.terminalVertexPosition
    have hg : ig.val ≤ A.length := hfirstGamma.2
    omega
  have hyt : T.vertex D.penultimateVertexIndex ≠ T.vertex D.terminalVertexIndex := by
    intro he
    have hi := congrArg Fin.val (T.vertex_injective he)
    have hp := D.penultimateVertexPosition
    have ht := D.terminalVertexPosition
    omega
  have hdisjoint := separate phi D.gammaOne D.alpha hgammaAlpha ctx.proper
    (T.vertex ig) (T.vertex D.penultimateVertexIndex) (T.vertex D.terminalVertexIndex)
    hgy hgt hyt hfirstGamma.1 D.alphaMissingPenultimate (Or.inr D.alphaMissingTerminal) hsame
  let z : Sum V E := Sum.inl (T.vertex D.terminalVertexIndex)
  let muOne := TwoColorComponentSwap G phi D.gammaOne D.alpha z
  have hpath : TwoColorPathComponent G phi D.gammaOne D.alpha z :=
    ⟨hgammaAlpha, _, self phi D.gammaOne D.alpha _,
      leaf phi D.gammaOne D.alpha hgammaAlpha ctx.proper _ (Or.inr D.alphaMissingTerminal)⟩
  have hstableOne := StableChangeCasesOneTwo G k e0 input T phi ett base C
    ctx.proper ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers
    ctx.lexicographicMinimality hElementary ctx.largeMissingSet
    D.gammaOne D.alpha hgammaAlpha hmissing z hpath muOne rfl
    (by
      dsimp only
      rcases hcase with hpos | ⟨hzero, hm⟩
      · exact Or.inl hpos
      · exact Or.inr ⟨hzero, Or.inl hm⟩)
    hdisjoint
  have prefixMissing (rho : PartialEdgeColoring E k) (a b : Fin k) (hne : a ≠ b)
      (hp : IsProperEdgeColoring G rho)
      (helem : ColoredVertexSetElementary G rho (TreeSequenceVertexSet B))
      (u v : V) (huB : u ∈ TreeSequenceVertexSet B) (hvB : v ∈ TreeSequenceVertexSet B)
      (hu : a ∈ MissingColors G rho u) (hv : b ∈ MissingColors G rho v)
      (hdu : Sum.inl u ∉ TwoColorComponent G rho a b z)
      (hdv : Sum.inl v ∉ TwoColorComponent G rho a b z) :
      ∀ w ∈ TreeSequenceVertexSet B,
        MissingColors G (TwoColorComponentSwap G rho a b z) w = MissingColors G rho w := by
    clear * - G rho a b hne hp helem u v huB hvB hu hv hdu hdv B z
    have behavior := TwoColorComponentSwapMissingBehavior G rho a b hne hp z
    intro w hwB
    by_cases hw : Sum.inl w ∈ TwoColorComponent G rho a b z
    · have hwa : a ∉ MissingColors G rho w := by
        intro hm
        have hwu : w ≠ u := fun he => hdu (he ▸ hw)
        exact Finset.disjoint_left.mp (helem hwB huB hwu) hm hu
      have hwb : b ∉ MissingColors G rho w := by
        intro hm
        have hwv : w ≠ v := fun he => hdv (he ▸ hw)
        exact Finset.disjoint_left.mp (helem hwB hvB hwv) hm hv
      have presentSwapped (c d : Fin k)
          (hd : d ∉ MissingColors G rho w)
          (hdab : (d = a ∧ c = b) ∨ (d = b ∧ c = a)) :
          c ∉ MissingColors G (TwoColorComponentSwap G rho a b z) w := by
        have hpres : d ∈ PresentColors G rho w := by simpa [MissingColors] using hd
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hpres
        rcases hpres with ⟨e, hwe, he⟩
        have hadj : (TwoColorIncidenceGraph G rho a b).Adj (Sum.inr e) (Sum.inl w) := by
          simp only [TwoColorIncidenceGraph]
          exact ⟨hwe, hdab.elim (fun h => Or.inl (he.trans (congrArg some h.1)))
            (fun h => Or.inr (he.trans (congrArg some h.1)))⟩
        have heC : Sum.inr e ∈ TwoColorComponent G rho a b z := by
          change (TwoColorIncidenceGraph G rho a b).connectedComponentMk (Sum.inl w) = _ at hw
          change (TwoColorIncidenceGraph G rho a b).connectedComponentMk (Sum.inr e) = _
          exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hw
        have heSwap : TwoColorComponentSwap G rho a b z e = some c := by
          rcases hdab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · simp [TwoColorComponentSwap, heC, he]
          · simp [TwoColorComponentSwap, heC, he, hne]
        have hpresent : c ∈ PresentColors G (TwoColorComponentSwap G rho a b z) w := by
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨e, hwe, heSwap⟩
        simpa [MissingColors] using hpresent
      have hnewa := presentSwapped a b hwb (Or.inr ⟨rfl, rfl⟩)
      have hnewb := presentSwapped b a hwa (Or.inl ⟨rfl, rfl⟩)
      apply Finset.ext
      intro c
      by_cases hca : c = a
      · subst c
        simp only [Finset.mem_coe, hnewa, hwa]
      · by_cases hcb : c = b
        · subst c
          simp only [Finset.mem_coe, hnewb, hwb]
        · exact behavior.2.2.2 w c hca hcb
    · exact behavior.1 w hw
  have houtsideGamma : Sum.inl (T.vertex ig) ∉ TwoColorComponent G phi D.gammaOne D.alpha z := by
    intro hm
    exact Set.disjoint_left.mp hdisjoint hm (self phi D.gammaOne D.alpha _)
  have houtsideAlpha : Sum.inl (T.vertex D.penultimateVertexIndex) ∉
      TwoColorComponent G phi D.gammaOne D.alpha z := by
    intro hm
    apply Set.disjoint_left.mp hdisjoint hm
    rw [hsame]
    exact self phi D.gammaOne D.alpha _
  have hmissingOne := prefixMissing phi D.gammaOne D.alpha hgammaAlpha ctx.proper
    hElementary _ _ higB hyB hfirstGamma.1 D.alphaMissingPenultimate
    houtsideGamma houtsideAlpha
  have predecessorIncident (X : TreeSequence G e0)
      (hXT : TreeSequenceInitialSegment X T) (t : Fin T.length)
      (ht : t.val = X.length) : TreeIncidentEdge X (T.edge t) := by
    clear * - G T X hXT t ht
    obtain ⟨i, hi⟩ := T.attaches t
    let j : Fin (X.length + 1) := ⟨i.val, by have hib := i.isLt; omega⟩
    refine ⟨X.vertex j, ?_, ?_⟩
    · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨j, rfl⟩
    · have hvertices : X.vertex j =
          T.vertex (Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ t.isLt))) := by
        rw [← hXT.2.1 j]
        rfl
      rw [hvertices]
      change _ ∈ G.ends (T.edge t)
      rw [hi]
      exact Sym2.mem_mk_right _ _
  have terminalIncident : Incident G (T.vertex D.terminalVertexIndex) (T.edge D.lastEdgeIndex) := by
    obtain ⟨i, hi⟩ := T.attaches D.lastEdgeIndex
    have hj : D.lastEdgeIndex.succ = D.terminalVertexIndex := by
      apply Fin.ext
      have hl := D.lastEdgePosition
      have ht := D.terminalVertexPosition
      simp only [Fin.val_succ]
      omega
    change _ ∈ G.ends (T.edge D.lastEdgeIndex)
    rw [hi, hj]
    exact Sym2.mem_mk_left _ _
  have missingNotColored (rho : PartialEdgeColoring E k) (c : Fin k) (v : V)
      (hm : c ∈ MissingColors G rho v) (e : E) (hi : Incident G v e) :
      rho e ≠ some c := by
    intro he
    have hnot : c ∉ PresentColors G rho v := (Finset.mem_sdiff.mp hm).2
    apply hnot
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨e, hi, he⟩
  have seedStable {input' : PartialEdgeColoring E k}
      (rho sigma : PartialEdgeColoring E k)
      (ett' : ExtendedTashkinovTree G k e0 input' T rho)
      (base' : HierarchyBase ett' rho) (K : TashkinovHierarchy ett' base')
      (hw : HierarchyWeaklyStable K (Fin.last K.dividerCount) sigma)
      (hq : K.dividerCount = 0) :
      StableColoring (ett'.series.data.tree (Fin.last ett'.rounds).castSucc)
        (TashkinovStoredColors ett'.series.data (Fin.last ett'.rounds)) rho sigma := by
    have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) = 0 := by
      apply Fin.ext
      simp [hq]
    rw [hi] at hw
    change (if ett'.series.data.kind (Fin.last ett'.rounds) =
        some TashkinovExtensionKind.PE then _ else _) at hw
    split_ifs at hw with hpe
    · exact hw.1
    · exact hw
  have hfixedOne : ∀ t : Fin T.length, A.length ≤ t.val →
      muOne (T.edge t) = phi (T.edge t) := by
    intro t ht
    have hng := hgammaUnused t ht
    by_cases ha : phi (T.edge t) = some D.alpha
    · have hnotlast : t ≠ D.lastEdgeIndex := by
        intro he
        exact missingNotColored phi D.alpha _ D.alphaMissingTerminal _ terminalIncident (he ▸ ha)
      have hbound : t.val < B.length := by
        have hlast := D.lastEdgePosition
        have hb := t.isLt
        have hn : t.val ≠ D.lastEdgeIndex.val := fun he => hnotlast (Fin.ext he)
        omega
      let tB : Fin B.length := ⟨t.val, hbound⟩
      have hcast : Fin.castLE hBT.1 tB = t := Fin.ext rfl
      have heB : phi (B.edge tB) = some D.alpha := by rw [← hBT.2.2 tB, hcast]; exact ha
      obtain ⟨hqzero, hcore, hpos, f, hstep, hkind, hedges, heq, hcolor, hstored⟩ :=
        halphaExclusion tB ht (by
          change tB.val < A.length + (T.length - A.length - 1)
          have hb := tB.isLt
          omega) heB
      have hAX : A = ett.series.data.tree (Fin.last ett.rounds).castSucc :=
        (hAzero hqzero).trans hcore
      have hinc : TreeIncidentEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc)
          (T.edge t) := by
        rw [← hAX]
        exact predecessorIncident A hAT t hpos
      exact (seedStable phi muOne ett base H hstableOne.1 hqzero).1 _ hinc
        ⟨D.alpha, Finset.mem_union_right _ hstored, ha⟩
    · simp [muOne, TwoColorComponentSwap, hng, ha]
  have firstPreserved (rho sigma : PartialEdgeColoring E k) (c : Fin k)
      (hmiss : ∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G rho v)
      (hc : c ∈ TreeMissingColors rho B) :
      HierarchyFirstMissingPosition sigma T c = HierarchyFirstMissingPosition rho T c := by
    clear * - G T B rho sigma c hmiss hc firstWitness hBT
    have hr := firstWitness rho B hBT c hc
    have hc' : c ∈ TreeMissingColors sigma B := by
      rcases Finset.mem_biUnion.mp hc with ⟨v, hv, hm⟩
      exact Finset.mem_biUnion.mpr ⟨v, hv, (hmiss v hv).symm ▸ hm⟩
    have hs := firstWitness sigma B hBT c hc'
    let cr := Finset.univ.filter fun i : Fin (T.length + 1) => c ∈ MissingColors G rho (T.vertex i)
    let cs := Finset.univ.filter fun i : Fin (T.length + 1) => c ∈ MissingColors G sigma (T.vertex i)
    have hrmem : HierarchyFirstMissingPosition rho T c ∈ cr := by simp [cr, hr.1]
    have hsmem : HierarchyFirstMissingPosition sigma T c ∈ cs := by simp [cs, hs.1]
    have hrn : cr.Nonempty := ⟨_, hrmem⟩
    have hsn : cs.Nonempty := ⟨_, hsmem⟩
    have pref (i : Fin (T.length + 1)) (hi : i.val ≤ B.length) :
        T.vertex i ∈ TreeSequenceVertexSet B := by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨i.val, by omega⟩, rfl⟩
    have hrSigma : HierarchyFirstMissingPosition rho T c ∈ cs := by
      simp only [cs, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hmiss _ (pref _ hr.2)]
      exact hr.1
    have hsRho : HierarchyFirstMissingPosition sigma T c ∈ cr := by
      simp only [cr, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hmiss _ (pref _ hs.2)]
      exact hs.1
    apply Fin.ext
    have hrs := Finset.min'_le cr _ hsRho
    have hsr := Finset.min'_le cs _ hrSigma
    have heqr : HierarchyFirstMissingPosition rho T c = cr.min' hrn := by
      simp [HierarchyFirstMissingPosition, cr, hrn]
    have heqs : HierarchyFirstMissingPosition sigma T c = cs.min' hsn := by
      simp [HierarchyFirstMissingPosition, cs, hsn]
    rw [← heqr] at hrs
    rw [← heqs] at hsr
    exact Nat.le_antisymm hsr hrs
  have firstUnaffected (rho : PartialEdgeColoring E k) (a b c : Fin k)
      (hne : a ≠ b) (hp : IsProperEdgeColoring G rho) (hca : c ≠ a) (hcb : c ≠ b) :
      HierarchyFirstMissingPosition (TwoColorComponentSwap G rho a b z) T c =
        HierarchyFirstMissingPosition rho T c := by
    clear * - G T z rho a b c hne hp hca hcb
    have hb := TwoColorComponentSwapMissingBehavior G rho a b hne hp z
    have he : (Finset.univ.filter fun i : Fin (T.length + 1) =>
        c ∈ MissingColors G (TwoColorComponentSwap G rho a b z) (T.vertex i)) =
        (Finset.univ.filter fun i : Fin (T.length + 1) =>
          c ∈ MissingColors G rho (T.vertex i)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hb.2.2.2 _ c hca hcb
    unfold HierarchyFirstMissingPosition
    rw [he]
  have hstoredOne : ∀ c ∈ HierarchyStoredColorsAt H q,
      HierarchyFirstMissingPosition muOne T c = HierarchyFirstMissingPosition phi T c := by
    intro c hc
    have hcg : c ≠ D.gammaOne := by
      intro he
      exact (Finset.mem_sdiff.mp hc).2 (he ▸ hgammaA)
    by_cases hca : c = D.alpha
    · subst c
      exact firstPreserved phi muOne D.alpha hmissingOne hmissing.2
    · exact firstUnaffected phi D.gammaOne D.alpha c hgammaAlpha ctx.proper hcg hca
  obtain ⟨corrOne, hmaxOne, baseOne, KOne, goodOne, hsameOne⟩ :=
    (StableChangeCasesOneTwoFullTail G k e0 input T phi ett base C ctx
      D.gammaOne D.alpha hgammaAlpha hmissing z hpath muOne rfl
      (by
        dsimp only
        rcases hcase with hpos | ⟨hzero, hm⟩
        · exact Or.inl hpos
        · exact Or.inr ⟨hzero, Or.inl hm⟩)
      hdisjoint hfixedOne hmissingOne hstoredOne).2.2.2.2
  have hgammaTerminalOne : D.gammaOne ∈ MissingColors G muOne (T.vertex D.terminalVertexIndex) :=
    (TwoColorComponentSwapMissingBehavior G phi D.gammaOne D.alpha hgammaAlpha ctx.proper z).2.2.1
      _ (self phi D.gammaOne D.alpha _) D.alphaMissingTerminal
  have hgammaWitnessOne : D.gammaOne ∈ MissingColors G muOne (T.vertex ig) := by
    rw [hmissingOne _ higB]
    exact hfirstGamma.1
  let COne : HierarchyCounterexample baseOne :=
    { positive := by rw [corrOne.rungAgreement]; exact C.positive
      hierarchy := KOne
      good := goodOne
      maximum := hmaxOne
      notElementary := by
        intro he
        have hg : T.vertex ig ∈ TreeSequenceVertexSet T := by simp [TreeSequenceVertexSet]
        have ht : T.vertex D.terminalVertexIndex ∈ TreeSequenceVertexSet T := by simp [TreeSequenceVertexSet]
        exact Finset.disjoint_left.mp (he hg ht hgt) hgammaWitnessOne hgammaTerminalOne }
  have seriesFacts : ∀ j : Fin (ett.rounds + 1),
      IsProperEdgeColoring G (ett.series.data.coloring j) ∧
        IsOneEdgeUncolored (ett.series.data.coloring j) e0 := by
    clear * - G ett e0
    intro j
    have certificate := ett.series.certified j
    cases certificate with
    | initial triple seedLength initialColoring initialStored initialEdges initialKind
        initialVertex initialOutside initialDelta initialGamma initialClosure =>
        simpa [initialColoring] using triple.2.2.2
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
        rw [currentColoring]
        exact ⟨choice.selectedProper, choice.selectedOneUncolored⟩
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma closedExtension orderedExtension
        strictExtension =>
        exact ⟨currentProper, currentOneUncolored⟩
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored currentEdges
        currentKind currentVertex currentOutside currentDelta currentGamma adjoined
        adjoinedExactly closedExtension orderedExtension strictExtension =>
        rw [currentColoring]
        exact ⟨previousProper, previousOneUncolored⟩
  let corrRefl : CorrespondingExtendedTashkinovTree G k e0 ett phi T :=
    { replacementInput := input
      replacementSeries := ett.series
      replacementETT := ett
      rungAgreement := rfl
      seriesPresentation := HEq.rfl
      finalGeneratingColoring := ett.generatingColoring
      ladderTreesAgree := fun _ => rfl
      storedColorsAgree := fun _ => rfl
      connectingEdgesAgree := fun _ => rfl
      extensionKindsAgree := fun _ => rfl
      replacementProper := fun j => (seriesFacts j).1
      replacementOneUncolored := fun j => (seriesFacts j).2
      replacementStable := fun _ => ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩ }
  let PRefl : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx :=
    { coloring := phi
      corresponding := corrRefl
      maximum := C.maximum
      replacementBase := base
      counterexample := C
      sameGood := ⟨⟨rfl, rfl, HEq.rfl, HEq.rfl, Iff.rfl, fun _ => rfl⟩,
        rfl, fun _ => ⟨rfl, fun _ _ => rfl⟩⟩
      minimumContext := ctx }
  obtain ⟨POne, hPOne⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi
    ett base C ctx PRefl muOne corrOne baseOne COne hsameOne
  have sameStar (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      HierarchyStarredStage P.counterexample.hierarchy
        (Fin.last P.counterexample.hierarchy.dividerCount) = A := by
    have helper : ∀ (n m : ℕ) (X Y : TreeSequence G e0)
        (s : Fin (n + 2) → TreeSequence G e0) (t : Fin (m + 2) → TreeSequence G e0),
        n = m → X = Y → HEq s t →
        Fin.cases (motive := fun _ => TreeSequence G e0)
          X (fun i : Fin n => s i.succ.castSucc) (Fin.last n) =
          Fin.cases (motive := fun _ => TreeSequence G e0)
            Y (fun i : Fin m => t i.succ.castSucc) (Fin.last m) := by
      intro n m X Y s t hnm hXY hst
      subst m
      have he := eq_of_heq hst
      simp [hXY, he]
    exact (helper _ _ base.core P.replacementBase.core H.stage
      P.counterexample.hierarchy.stage P.sameGood.1.2.1 P.sameGood.1.1
      P.sameGood.1.2.2.1).symm
  have samePrefix (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      HierarchyFullTailPrefix P.counterexample (HierarchyFullTailLength P.counterexample - 1) = B := by
    simp only [HierarchyFullTailPrefix, HierarchyFullTailLength, sameStar P]
    rfl
  let rho := POne.coloring
  let ettOne := POne.corresponding.replacementETT
  let baseOne' := POne.replacementBase
  let COne' := POne.counterexample
  let ctxOne := POne.minimumContext
  let HOne := COne'.hierarchy
  let qOne : Fin (HOne.dividerCount + 1) := Fin.last HOne.dividerCount
  have hmissingOne' : ∀ v ∈ TreeSequenceVertexSet B,
      MissingColors G rho v = MissingColors G phi v := by
    rw [show rho = muOne from hPOne]
    exact hmissingOne
  have hElementaryOne : ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) := by
    intro u hu v hv huv
    rw [hmissingOne' u hu, hmissingOne' v hv]
    exact hElementary hu hv huv
  have hthetaPenOne : D.theta ∈ MissingColors G rho (T.vertex D.penultimateVertexIndex) := by
    rw [hmissingOne' _ hyB]
    exact D.thetaMissingPenultimate
  have hgammaPenOne : D.gammaOne ∉ MissingColors G rho (T.vertex D.penultimateVertexIndex) := by
    rw [hmissingOne' _ hyB]
    intro hm
    exact Finset.disjoint_left.mp (hElementary higB hyB hgy) hfirstGamma.1 hm
  have hgammaTermOne : D.gammaOne ∈ MissingColors G rho (T.vertex D.terminalVertexIndex) := by
    rw [show rho = muOne from hPOne]
    exact hgammaTerminalOne
  have hgammaWitnessOne' : D.gammaOne ∈ MissingColors G rho (T.vertex ig) := by
    rw [hmissingOne' _ higB]
    exact hfirstGamma.1
  have hgammaAOne : D.gammaOne ∈ TreeMissingColors rho A := by
    rcases Finset.mem_biUnion.mp hgammaA with ⟨v, hv, hm⟩
    refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
    rw [hmissingOne' _ (TreeSequenceInitialSegmentVertexSetSubset hAB hv)]
    exact hm
  have hfirstGammaOne : HierarchyFirstMissingPosition rho T D.gammaOne = ig :=
    firstPreserved phi rho D.gammaOne hmissingOne' hmissing.1
  have hfirstThetaOne : HierarchyFirstMissingPosition rho T D.theta = D.penultimateVertexIndex :=
    (firstPreserved phi rho D.theta hmissingOne'
      (Finset.mem_biUnion.mpr ⟨_, hyB, D.thetaMissingPenultimate⟩)).trans hfirstTheta
  have hfirstAlphaOne : HierarchyFirstMissingPosition rho T D.alpha = D.penultimateVertexIndex :=
    (firstPreserved phi rho D.alpha hmissingOne' hmissing.2).trans hfirstAlpha
  have hgammaUnusedOne : ∀ t : Fin T.length, A.length ≤ t.val →
      rho (T.edge t) ≠ some D.gammaOne := by
    intro t ht
    rw [show rho = muOne from hPOne, hfixedOne t ht]
    exact hgammaUnused t ht
  have hpairDataOne : D.alpha ∈ HierarchyStoredColorsAt HOne qOne ∧
      POne.counterexample.good.gamma qOne D.alpha = {D.gammaOne, D.gammaTwo} := by
    rcases POne.sameGood.2 with ⟨hcount, hdata⟩
    have hi : Fin.cast (congrArg (fun n => n + 1) hcount) q = qOne := by
      apply Fin.ext
      simp [q, qOne, H, HOne, COne', hcount]
    have hd := hdata q
    dsimp only at hd
    rw [hi] at hd
    refine ⟨hd.1 ▸ D.alphaStored, ?_⟩
    exact (hd.2 D.alpha D.alphaStored).symm.trans D.gammaPair
  have hgammaStageOne : D.gammaOne ∈ HierarchyStageMissingColors HOne qOne := by
    apply (Finset.mem_sdiff.mp
      (POne.counterexample.good.avoidance qOne D.alpha hpairDataOne.1 ?_)).1
    rw [hpairDataOne.2]
    simp
  have hcaseOne :
      (0 < HOne.dividerCount ∧ D.gammaOne ∈ TreeMissingColors rho
        (HOne.stage ⟨HOne.dividerCount, by omega⟩)) ∨
      (HOne.dividerCount = 0 ∧ D.gammaOne ∈ TreeMissingColors rho
        (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc)) := by
    by_cases hz : HOne.dividerCount = 0
    · right
      refine ⟨hz, ?_⟩
      have hi : qOne = 0 := by apply Fin.ext; simp [qOne, hz]
      simpa [hi, HierarchyStageMissingColors] using hgammaStageOne
    · left
      refine ⟨Nat.pos_of_ne_zero hz, ?_⟩
      have hi : qOne = (⟨HOne.dividerCount - 1, by omega⟩ : Fin HOne.dividerCount).succ := by
        apply Fin.ext
        simp [qOne]
        omega
      have hg := hgammaStageOne
      rw [hi] at hg
      simp [HierarchyStageMissingColors] at hg
      convert hg using 1 <;> congr 2 <;> apply Fin.ext <;> simp <;> omega
  have hmissingPairOne : D.gammaOne ∈ TreeMissingColors rho B ∧
      D.theta ∈ TreeMissingColors rho B := by
    exact ⟨Finset.mem_biUnion.mpr ⟨_, higB, hgammaWitnessOne'⟩,
      Finset.mem_biUnion.mpr ⟨_, hyB, hthetaPenOne⟩⟩
  have hchangeOne := ChangeLemma G k e0 POne.corresponding.replacementInput T rho ettOne
    baseOne' COne' ctxOne.proper ctxOne.oneEdgeUncolored ctxOne.lowerRung
    ctxOne.fewerDividers ctxOne.lexicographicMinimality
    (by change ColoredVertexSetElementary G rho (TreeSequenceVertexSet
        (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1)))
        rw [samePrefix POne]; exact hElementaryOne)
    ctxOne.largeMissingSet D.gammaOne D.theta hgammaTheta
    (by change D.gammaOne ∈ TreeMissingColors rho (HierarchyFullTailPrefix COne'
          (HierarchyFullTailLength COne' - 1)) ∧ D.theta ∈ TreeMissingColors rho
            (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1))
        rw [samePrefix POne]; exact hmissingPairOne)
    (by
      dsimp only
      rw [sameStar POne, hfirstGammaOne, hfirstThetaOne]
      intro _
      refine ⟨⟨ig, D.penultimateVertexIndex, rfl, rfl, ?_⟩, ?_⟩
      · have hp := D.penultimateVertexPosition
        have hg : ig.val ≤ A.length := hfirstGamma.2
        clear * - hp hg htail
        omega
      · intro hc
        rcases (Finset.mem_filter.mp hc).2 with ⟨t, ht, _, he⟩
        exact hgammaUnusedOne t ht he)
  have hsameTwo : TwoColorComponent G rho D.gammaOne D.theta (Sum.inl (T.vertex ig)) =
      TwoColorComponent G rho D.gammaOne D.theta
        (Sum.inl (T.vertex D.penultimateVertexIndex)) := by
    rw [← hfirstGammaOne, ← hfirstThetaOne]
    rcases hcaseOne with ⟨hq, hm⟩ | ⟨hq, hm⟩
    · exact hchangeOne.1 ⟨hq, Or.inl hm⟩
    · exact hchangeOne.2.1 ⟨hq, Or.inl hm⟩
  have hdisjointTwo := separate rho D.gammaOne D.theta hgammaTheta ctxOne.proper
    (T.vertex ig) (T.vertex D.penultimateVertexIndex) (T.vertex D.terminalVertexIndex)
    hgy hgt hyt hgammaWitnessOne' hthetaPenOne (Or.inl hgammaTermOne) hsameTwo
  let muTwo := TwoColorComponentSwap G rho D.gammaOne D.theta z
  have hpathTwo : TwoColorPathComponent G rho D.gammaOne D.theta z :=
    ⟨hgammaTheta, _, self rho D.gammaOne D.theta _,
      leaf rho D.gammaOne D.theta hgammaTheta ctxOne.proper _ (Or.inl hgammaTermOne)⟩
  have hstableTwo := StableChangeCasesOneTwo G k e0 POne.corresponding.replacementInput T rho
    ettOne baseOne' COne' ctxOne.proper ctxOne.oneEdgeUncolored ctxOne.lowerRung
    ctxOne.fewerDividers ctxOne.lexicographicMinimality
    (by change ColoredVertexSetElementary G rho (TreeSequenceVertexSet
        (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1)))
        rw [samePrefix POne]; exact hElementaryOne)
    ctxOne.largeMissingSet D.gammaOne D.theta hgammaTheta
    (by change D.gammaOne ∈ TreeMissingColors rho (HierarchyFullTailPrefix COne'
          (HierarchyFullTailLength COne' - 1)) ∧ D.theta ∈ TreeMissingColors rho
            (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1))
        rw [samePrefix POne]; exact hmissingPairOne)
    z hpathTwo muTwo rfl
    (by dsimp only; rcases hcaseOne with hpos | ⟨hzero, hm⟩
        · exact Or.inl hpos
        · exact Or.inr ⟨hzero, Or.inl hm⟩)
    (by dsimp only; rw [hfirstGammaOne]; exact hdisjointTwo)
  have houtsideGammaTwo : Sum.inl (T.vertex ig) ∉ TwoColorComponent G rho D.gammaOne D.theta z := by
    intro hm
    exact Set.disjoint_left.mp hdisjointTwo hm (self rho D.gammaOne D.theta _)
  have houtsideThetaTwo : Sum.inl (T.vertex D.penultimateVertexIndex) ∉
      TwoColorComponent G rho D.gammaOne D.theta z := by
    intro hm
    apply Set.disjoint_left.mp hdisjointTwo hm
    rw [hsameTwo]
    exact self rho D.gammaOne D.theta _
  have hmissingTwo := prefixMissing rho D.gammaOne D.theta hgammaTheta ctxOne.proper
    hElementaryOne _ _ higB hyB hgammaWitnessOne' hthetaPenOne
    houtsideGammaTwo houtsideThetaTwo
  have hfixedTailTwo : ∀ t : Fin T.length, A.length ≤ t.val → t.val < B.length →
      muTwo (T.edge t) = rho (T.edge t) := by
    intro t ht hb
    have hng := hgammaUnusedOne t ht
    by_cases htheta : rho (T.edge t) = some D.theta
    · let tB : Fin B.length := ⟨t.val, hb⟩
      have hcast : Fin.castLE hBT.1 tB = t := Fin.ext rfl
      have heOld : phi (T.edge t) = some D.theta := by
        rw [show rho = muOne from hPOne, hfixedOne t ht] at htheta
        exact htheta
      have heB : phi (B.edge tB) = some D.theta := by
        rw [← hBT.2.2 tB, hcast]
        exact heOld
      obtain ⟨hzero, hcore, hpos, f, hstep, hkind, hedges, heq, hcolor, hstored⟩ :=
        hthetaExclusion tB ht (by
          change tB.val < A.length + (T.length - A.length - 1)
          have hb := tB.isLt
          omega) heB
      rcases POne.sameGood.1 with ⟨hcoreSame, hcount, hstages, hpositions, hpe, hclosure⟩
      have hzeroOne : HOne.dividerCount = 0 := hcount.symm.trans hzero
      have hnotPE : ett.series.data.kind (Fin.last ett.rounds) ≠
          some TashkinovExtensionKind.PE := by
        intro he
        rcases hkind with hs | hr
        · rw [hs] at he
          simp at he
        · rw [hr] at he
          simp at he
      have hnotPEOne : ettOne.series.data.kind (Fin.last ettOne.rounds) ≠
          some TashkinovExtensionKind.PE := fun hp => hnotPE (hpe.mpr hp)
      have hAX : A = ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc :=
        (hAzero hzero).trans (hcoreSame.trans (baseOne'.nonparallel hnotPEOne))
      have hinc : TreeIncidentEdge (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc)
          (T.edge t) := by
        rw [← hAX]
        exact predecessorIncident A hAT t hpos
      have hthetaStored : D.theta ∈ HierarchyStoredColorsAt H q :=
        Finset.mem_sdiff.mpr ⟨hstored, hnotA D.thetaMissingPenultimate⟩
      rcases POne.sameGood.2 with ⟨hcount', hdata⟩
      have hi : Fin.cast (congrArg (fun n => n + 1) hcount') q = qOne := by
        apply Fin.ext
        simp [q, qOne, H, HOne, COne']
      have hd := (hdata q).1
      rw [hi] at hd
      have hs : D.theta ∈ HierarchyStoredColorsAt HOne qOne := hd ▸ hthetaStored
      have hs' := (Finset.mem_sdiff.mp hs).1
      exact (seedStable rho muTwo ettOne baseOne' HOne hstableTwo.1 hzeroOne).1 _ hinc
        ⟨D.theta, Finset.mem_union_right _ hs', htheta⟩
    · simp [muTwo, TwoColorComponentSwap, hng, htheta]
  have edgeCast (X Y : TreeSequence G e0) (h : X = Y) (i : Fin X.length) :
      X.edge i = Y.edge (Fin.cast (congrArg TreeSequence.length h) i) := by
    subst Y
    rfl
  have weakEdges {input' : PartialEdgeColoring E k}
      (old new : PartialEdgeColoring E k)
      (ett' : ExtendedTashkinovTree G k e0 input' T old)
      (base' : HierarchyBase ett' old) (K : TashkinovHierarchy ett' base')
      (hST : TreeSequenceInitialSegment (HierarchyStarredStage K (Fin.last K.dividerCount)) T)
      (hw : HierarchyWeaklyStable K (Fin.last K.dividerCount) new)
      (hp : IsProperEdgeColoring G old) (ho : IsOneEdgeUncolored old e0)
      (hnp : IsProperEdgeColoring G new) (hno : IsOneEdgeUncolored new e0) :
      ∀ t : Fin T.length, t.val < (HierarchyStarredStage K (Fin.last K.dividerCount)).length →
        new (T.edge t) = old (T.edge t) := by
    clear * - G T e0 old new ett' base' K hST hw hp ho hnp hno edgeCast
    let S := HierarchyStarredStage K (Fin.last K.dividerCount)
    intro t ht
    let tS : Fin S.length := ⟨t.val, ht⟩
    have hcast : Fin.castLE hST.1 tS = t := Fin.ext rfl
    rw [← hcast, hST.2.2 tS]
    by_cases hzero : K.dividerCount = 0
    · have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) = 0 := by
        apply Fin.ext
        simp [hzero]
      have hS : S = base'.core := by change HierarchyStarredStage K _ = _; rw [hi]; rfl
      rw [hi] at hw
      change (if ett'.series.data.kind (Fin.last ett'.rounds) =
        some TashkinovExtensionKind.PE then _ else _) at hw
      by_cases hpe : ett'.series.data.kind (Fin.last ett'.rounds) = some TashkinovExtensionKind.PE
      · rw [if_pos hpe] at hw
        have hc := CombinedStableClosurePreserved G k e0 input' T old old new ett'
          (by have h := ett'.roundsPositive; omega) base' ett'.generatingColoring hpe hp ho hnp hno hw
        obtain ⟨_, _, ⟨hunion⟩⟩ := base'.parallel hpe
        let tc : Fin base'.core.length := Fin.cast (congrArg TreeSequence.length hS) tS
        have he : S.edge tS = base'.core.edge tc := edgeCast S base'.core hS tS
        rw [he]
        by_cases hbelow : tc.val < (ett'.series.data.tree (Fin.last ett'.rounds).castSucc).length
        · let tn : Fin (ett'.series.data.tree (Fin.last ett'.rounds).castSucc).length := ⟨tc.val, hbelow⟩
          have heq : Fin.castLE hunion.leftSegment.1 tn = tc := Fin.ext rfl
          rw [← heq, hunion.leftSegment.2.2 tn]
          exact hc.1 tn
        · obtain ⟨j, heq, _⟩ := hunion.newEntryFromRight tc (by omega)
          rw [heq]
          exact hc.2.1 j
      · rw [if_neg hpe] at hw
        have hcore := base'.nonparallel hpe
        have hS' := hS.trans hcore
        let tn : Fin (ett'.series.data.tree (Fin.last ett'.rounds).castSucc).length :=
          Fin.cast (congrArg TreeSequence.length hS') tS
        have he : S.edge tS = (ett'.series.data.tree (Fin.last ett'.rounds).castSucc).edge tn := by
          exact edgeCast S _ hS' tS
        rw [he]
        let r : Fin ett'.rounds := ⟨ett'.rounds - 1, by have h := ett'.roundsPositive; omega⟩
        have hr : r.succ = Fin.last ett'.rounds := by
          have hn := ett'.roundsPositive
          apply Fin.ext
          simp [r]
          omega
        have hfix := (HkuTreeColorsControlled G k ett'.rounds e0 input' ett'.series r).2.2 new
          hnp hno (by rw [hr, ← ett'.generatingColoring]; exact hw)
        rw [hr, ← ett'.generatingColoring] at hfix
        exact hfix tn
    · have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) =
          (⟨K.dividerCount - 1, by omega⟩ : Fin K.dividerCount).succ := by
        apply Fin.ext
        simp
        omega
      have hS : S = K.stage (⟨K.dividerCount - 1, by omega⟩ : Fin K.dividerCount).succ.castSucc := by
        change HierarchyStarredStage K _ = _
        rw [hi]
        simp [HierarchyStarredStage]
      rw [hi] at hw
      simp [HierarchyWeaklyStable] at hw
      have hinv : TreeColoringInvariant S old new := hS.symm ▸ hw.2
      by_cases hpos : 1 ≤ tS.val
      · exact hinv.1 tS hpos
      · have hi : tS = ⟨0, S.positive⟩ := by
          apply Fin.ext
          change tS.val = 0
          omega
        rw [hi, S.first_edge, hno.1, ho.1]
  have hfixedCoreTwo : ∀ t : Fin T.length, t.val < A.length → muTwo (T.edge t) = rho (T.edge t) := by
    have h := weakEdges rho muTwo ettOne baseOne' HOne
      (by rw [sameStar POne]; exact hAT) hstableTwo.1 ctxOne.proper ctxOne.oneEdgeUncolored
      hstableTwo.2.1.1 hstableTwo.2.1.2.1
    change ∀ t : Fin T.length, t.val < (HierarchyStarredStage POne.counterexample.hierarchy
      (Fin.last POne.counterexample.hierarchy.dividerCount)).length → _ at h
    rw [sameStar POne] at h
    exact h
  have hfixedPrefixTwo : ∀ t : Fin T.length, t.val < B.length →
      muTwo (T.edge t) = rho (T.edge t) := by
    intro t ht
    by_cases ha : t.val < A.length
    · exact hfixedCoreTwo t ha
    · exact hfixedTailTwo t (by omega) ht
  have hstoredTwo : ∀ c ∈ HierarchyStoredColorsAt HOne qOne,
      HierarchyFirstMissingPosition muTwo T c = HierarchyFirstMissingPosition rho T c := by
    intro c hc
    have hcg : c ≠ D.gammaOne := by
      intro he
      apply (Finset.mem_sdiff.mp hc).2
      rw [sameStar POne]
      exact he ▸ hgammaAOne
    by_cases hct : c = D.theta
    · subst c
      exact firstPreserved rho muTwo D.theta hmissingTwo hmissingPairOne.2
    · exact firstUnaffected rho D.gammaOne D.theta c hgammaTheta ctxOne.proper hcg hct
  have commonPrefix {X Y F : TreeSequence G e0}
      (hXF : TreeSequenceInitialSegment X F) (hYF : TreeSequenceInitialSegment Y F)
      (hXY : X.length ≤ Y.length) : TreeSequenceInitialSegment X Y := by
    refine ⟨hXY, ?_, ?_⟩
    · intro i
      rw [← hYF.2.1 (Fin.castLE (Nat.succ_le_succ hXY) i)]
      exact hXF.2.1 i
    · intro i
      rw [← hYF.2.2 (Fin.castLE hXY i)]
      exact hXF.2.2 i
  have segmentTrans {X Y F : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y) (hYF : TreeSequenceInitialSegment Y F) :
      TreeSequenceInitialSegment X F := by
    refine ⟨hXY.1.trans hYF.1, ?_, ?_⟩
    · intro i
      exact (hYF.2.1 (Fin.castLE (Nat.succ_le_succ hXY.1) i)).trans (hXY.2.1 i)
    · intro i
      exact (hYF.2.2 (Fin.castLE hXY.1 i)).trans (hXY.2.2 i)
  have hcoreLength : baseOne'.core.length ≤ A.length := by
    by_cases hz : HOne.dividerCount = 0
    · have hi : qOne = 0 := by apply Fin.ext; simp [qOne, hz]
      have he := sameStar POne
      change HierarchyStarredStage HOne qOne = A at he
      rw [hi] at he
      change baseOne'.core = A at he
      exact le_of_eq (congrArg TreeSequence.length he)
    · have hmono : Monotone (fun i : Fin (HOne.dividerCount + 2) => (HOne.stage i).length) :=
        Fin.monotone_iff_le_succ.mpr fun i => (HOne.nested i).1
      have hi : qOne = (⟨HOne.dividerCount - 1, by omega⟩ : Fin HOne.dividerCount).succ := by
        apply Fin.ext
        simp [qOne]
        omega
      have he := sameStar POne
      change HierarchyStarredStage HOne qOne = A at he
      rw [hi] at he
      simp [HierarchyStarredStage] at he
      have hle := hmono (show (⟨1, by omega⟩ : Fin (HOne.dividerCount + 2)) ≤
          (⟨HOne.dividerCount - 1, by omega⟩ : Fin HOne.dividerCount).succ.castSucc by
        change 1 ≤ HOne.dividerCount - 1 + 1
        omega)
      change (HOne.stage ⟨1, by omega⟩).length ≤
        (HOne.stage ⟨HOne.dividerCount - 1 + 1, by omega⟩).length at hle
      rw [he] at hle
      exact HOne.coreInsideFirst.1.trans hle
  have transportRoute (S : TreeSequence G e0) (hs : TashkinovAugmentationSequence rho S B) :
      TashkinovAugmentationSequence muTwo S B := by
    unfold TashkinovAugmentationSequence at hs ⊢
    induction hs using Relation.ReflTransGen.head_induction_on with
    | refl => exact Relation.ReflTransGen.refl
    | @head X Y hstep htail ih =>
      have hYB := TashkinovAugmentationSequenceInitialSegment rho Y B htail
      rcases hstep with ⟨hlen, hXY, c, hedge, hm⟩
      have hXB := segmentTrans hXY hYB
      refine Relation.ReflTransGen.head ⟨hlen, hXY, c, ?_, ?_⟩ ih
      · let tY : Fin Y.length := Fin.cast hlen.symm (Fin.last X.length)
        let tB : Fin B.length := Fin.castLE hYB.1 tY
        have hfixed := hfixedPrefixTwo (Fin.castLE hBT.1 tB) (by
          simp only [Fin.val_castLE]
          exact tB.isLt)
        rw [hBT.2.2 tB, hYB.2.2 tY] at hfixed
        exact hfixed.trans hedge
      · rcases Finset.mem_biUnion.mp hm with ⟨v, hv, hvc⟩
        refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
        rw [hmissingTwo v (TreeSequenceInitialSegmentVertexSetSubset hXB hv)]
        exact hvc
  have hrouteTwo :
      (ettOne.series.data.kind (Fin.last ettOne.rounds) = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence muTwo
          (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) B) ∨
      ((ettOne.series.data.kind (Fin.last ettOne.rounds) = some TashkinovExtensionKind.SE ∨
          ettOne.series.data.kind (Fin.last ettOne.rounds) = some TashkinovExtensionKind.RE) ∧
        ∃ f seed, ettOne.series.data.connectingEdges (Fin.last ettOne.rounds) = {f} ∧
          TreeSequenceAdjoinEdge (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) f seed ∧
          TashkinovAugmentationSequence muTwo seed B) := by
    let n : Fin (ettOne.rounds + 1) := Fin.last ettOne.rounds
    let Tn := ettOne.series.data.tree n.castSucc
    let F := ettOne.series.data.tree (Fin.last (ettOne.rounds + 1))
    have hBF : TreeSequenceInitialSegment B F := segmentTrans hBT ettOne.belowFinal
    have hn : n.succ = Fin.last (ettOne.rounds + 1) := Fin.ext rfl
    have hTnT : TreeSequenceInitialSegment Tn T := ettOne.abovePenultimate
    have hTnB : TreeSequenceInitialSegment Tn B := commonPrefix hTnT hBT (by
      have hs := ettOne.strictAbovePenultimate
      change Tn.length < T.length at hs
      omega)
    have nonparallel (hkind : ettOne.series.data.kind n = some TashkinovExtensionKind.SE ∨
        ettOne.series.data.kind n = some TashkinovExtensionKind.RE)
        (f : E) (seed : TreeSequence G e0)
        (hedges : ettOne.series.data.connectingEdges n = {f})
        (hadjoin : TreeSequenceAdjoinEdge Tn f seed)
        (hclosure : TashkinovClosure rho seed F) :
        ∃ f seed, ettOne.series.data.connectingEdges (Fin.last ettOne.rounds) = {f} ∧
          TreeSequenceAdjoinEdge (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) f seed ∧
          TashkinovAugmentationSequence muTwo seed B := by
      have hnotPE : ettOne.series.data.kind n ≠ some TashkinovExtensionKind.PE := by
        intro he
        rcases hkind with hs | hr
        · rw [hs] at he
          simp at he
        · rw [hr] at he
          simp at he
      have hc : baseOne'.core = Tn := baseOne'.nonparallel hnotPE
      have hseedF := TashkinovAugmentationSequenceInitialSegment rho seed F hclosure.1
      have hsBound : seed.length ≤ B.length := by
        have hlen : Tn.length ≤ A.length := hc ▸ hcoreLength
        have hab : A.length + 1 ≤ B.length := by
          clear * - htail hBlen
          omega
        exact hadjoin.1.le.trans ((Nat.add_le_add_right hlen 1).trans hab)
      have hseedB : TreeSequenceInitialSegment seed B := commonPrefix hseedF hBF hsBound
      exact ⟨f, seed, hedges, hadjoin,
        transportRoute seed (TashkinovAugmentationSequenceRestrict rho seed B F
          hclosure.1 hseedB hBF)⟩
    have cert := ettOne.series.certified n
    generalize hindex : n = j at cert
    cases cert with
    | initial triple seedLength initialColoring initialStored initialEdges initialKind
        initialVertex initialOutside initialDelta initialGamma initialClosure =>
        have hnzero : n = 0 := by simpa using hindex
        have hv := congrArg Fin.val hnzero
        have hp := ettOne.roundsPositive
        simp [n] at hv
        omega
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
        have hk : ettOne.series.data.kind n = some TashkinovExtensionKind.SE := by rw [hindex]; exact currentKind
        refine Or.inr ⟨Or.inl hk, ?_⟩
        apply nonparallel (Or.inl hk) choice.edge adjoined
        · rw [hindex]; exact currentEdges
        · simpa [Tn, hindex] using adjoinedExactly
        · rw [← hindex, hn, ← ettOne.generatingColoring] at closedExtension
          exact closedExtension
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma closedExtension orderedExtension
        strictExtension =>
        have hk : ettOne.series.data.kind n = some TashkinovExtensionKind.PE := by rw [hindex]; exact currentKind
        refine Or.inl ⟨hk, transportRoute Tn ?_⟩
        rw [← hindex, hn, ← ettOne.generatingColoring] at closedExtension
        exact TashkinovAugmentationSequenceRestrict rho Tn B F closedExtension.1 hTnB hBF
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored currentEdges
        currentKind currentVertex currentOutside currentDelta currentGamma adjoined
        adjoinedExactly closedExtension orderedExtension strictExtension =>
        have hk : ettOne.series.data.kind n = some TashkinovExtensionKind.RE := by rw [hindex]; exact currentKind
        refine Or.inr ⟨Or.inr hk, ?_⟩
        apply nonparallel (Or.inr hk) available.edge adjoined
        · rw [hindex]; exact currentEdges
        · simpa [Tn, hindex] using adjoinedExactly
        · rw [← hindex, hn, ← ettOne.generatingColoring] at closedExtension
          exact closedExtension
  have hthetaLastOne : rho (T.edge D.lastEdgeIndex) = some D.theta := by
    rw [show rho = muOne from hPOne, hfixedOne D.lastEdgeIndex (by
      have hl := D.lastEdgePosition
      clear * - hl htail
      omega)]
    exact D.thetaOnLastEdge
  have hsuffix : TashkinovAugmentationSequence rho B T := by
    apply Relation.ReflTransGen.single
    refine ⟨hBlen.symm, hBT, D.theta, ?_, hmissingPairOne.2⟩
    have hi : Fin.cast hBlen (Fin.last B.length) = D.lastEdgeIndex := by
      apply Fin.ext
      have hl := D.lastEdgePosition
      simp
      clear * - hBlen hl
      omega
    rw [hi]
    exact hthetaLastOne
  have hgammaCutoff : ∀ c ∈ HierarchyStoredColorsAt HOne qOne,
      (D.gammaOne ∈ POne.counterexample.good.gamma qOne c ∨
        D.theta ∈ POne.counterexample.good.gamma qOne c) →
      (HierarchyFirstMissingPosition rho T c).val ≤ B.length := by
    intro c hc hpair
    rcases hpair with hgamma | htheta
    · have hca : c = D.alpha := by
        by_contra hne
        have hdis := POne.counterexample.good.disjointPairs qOne c D.alpha hc hpairDataOne.1 hne
        exact Finset.disjoint_left.mp hdis hgamma (by rw [hpairDataOne.2]; simp)
      subst c
      rw [hfirstAlphaOne]
      have hp := D.penultimateVertexPosition
      clear * - hBlen hp
      omega
    · have htA := (GoodHierarchyReservedDisjoint POne.counterexample.good qOne).1 c hc htheta
      rw [sameStar POne] at htA
      have htB : D.theta ∈ TreeMissingColors phi A := by
        rcases Finset.mem_biUnion.mp htA with ⟨v, hv, hm⟩
        refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
        rw [hmissingOne' _ (TreeSequenceInitialSegmentVertexSetSubset hAB hv)] at hm
        exact hm
      exact (hnotA D.thetaMissingPenultimate htB).elim
  obtain ⟨corrTwo, hmaxTwo, baseTwo, KTwo, goodTwo, hsameGoodTwo⟩ :=
    (StableChangeCasesOneTwoSplitTail G k e0 POne.corresponding.replacementInput T rho ettOne
      baseOne' COne' ctxOne D.gammaOne D.theta hgammaTheta
      (by rw [samePrefix POne]; exact hmissingPairOne)
      z hpathTwo muTwo rfl
      (by dsimp only; rcases hcaseOne with hpos | ⟨hzero, hm⟩
          · exact Or.inl hpos
          · exact Or.inr ⟨hzero, Or.inl hm⟩)
      (by dsimp only; rw [hfirstGammaOne]; exact hdisjointTwo)
      B (by dsimp only; rw [sameStar POne]; exact hAB)
      (by dsimp only; rw [sameStar POne]; clear * - htail hBlen; omega)
      (by rw [samePrefix POne]; exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩)
      (by dsimp only; intro t _ ht; exact hfixedPrefixTwo t ht)
      hrouteTwo hsuffix
      (by
        constructor
        · exact Finset.mem_biUnion.mpr ⟨_, higB, (hmissingTwo _ higB).symm ▸ hgammaWitnessOne'⟩
        · exact Finset.mem_biUnion.mpr ⟨_, hyB, (hmissingTwo _ hyB).symm ▸ hthetaPenOne⟩)
      (by rw [samePrefix POne]; exact hmissingTwo)
      hstoredTwo hgammaCutoff).2.2
  have hlastComponent : Sum.inr (T.edge D.lastEdgeIndex) ∈ TwoColorComponent G rho D.gammaOne D.theta z := by
    have hadj : (TwoColorIncidenceGraph G rho D.gammaOne D.theta).Adj
        (Sum.inr (T.edge D.lastEdgeIndex)) z := by
      exact ⟨terminalIncident, Or.inr hthetaLastOne⟩
    change (TwoColorIncidenceGraph G rho D.gammaOne D.theta).connectedComponentMk
      (Sum.inr (T.edge D.lastEdgeIndex)) = _
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
  have hlastTwo : muTwo (T.edge D.lastEdgeIndex) = some D.gammaOne := by
    simp [muTwo, TwoColorComponentSwap, hlastComponent, hthetaLastOne, hgammaTheta.symm]
  have hthetaTermTwo : D.theta ∈ MissingColors G muTwo (T.vertex D.terminalVertexIndex) :=
    (TwoColorComponentSwapMissingBehavior G rho D.gammaOne D.theta hgammaTheta ctxOne.proper z).2.1
      _ (self rho D.gammaOne D.theta _) hgammaTermOne
  have hthetaPenTwo : D.theta ∈ MissingColors G muTwo (T.vertex D.penultimateVertexIndex) := by
    rw [hmissingTwo _ hyB]
    exact hthetaPenOne
  have hgammaPenTwo : D.gammaOne ∉ MissingColors G muTwo (T.vertex D.penultimateVertexIndex) := by
    rw [hmissingTwo _ hyB]
    exact hgammaPenOne
  let CTwo : HierarchyCounterexample baseTwo :=
    { positive := by rw [corrTwo.rungAgreement]; exact COne'.positive
      hierarchy := KTwo
      good := goodTwo
      maximum := hmaxTwo
      notElementary := by
        intro he
        have hy : T.vertex D.penultimateVertexIndex ∈ TreeSequenceVertexSet T := by simp [TreeSequenceVertexSet]
        have ht : T.vertex D.terminalVertexIndex ∈ TreeSequenceVertexSet T := by simp [TreeSequenceVertexSet]
        exact Finset.disjoint_left.mp (he hy ht hyt) hthetaPenTwo hthetaTermTwo }
  obtain ⟨PTwo, hPTwo⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi
    ett base C ctx POne muTwo corrTwo baseTwo CTwo hsameGoodTwo
  let tailTwo : HierarchySituationTwoTailData G k e0 PTwo.corresponding.replacementInput T
      PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase
      PTwo.counterexample PTwo.minimumContext :=
    { tailAtLeastTwo := by
        change 2 ≤ T.length - (HierarchyStarredStage PTwo.counterexample.hierarchy
          (Fin.last PTwo.counterexample.hierarchy.dividerCount)).length
        rw [sameStar PTwo]
        exact htail
      pathNumberFull := by
        have hp := D.pathNumberFull
        unfold HierarchyPathNumber HierarchyFullTailLength at hp ⊢
        dsimp only at hp ⊢
        rw [sameStar PTwo]
        exact hp
      lastEdgeIndex := D.lastEdgeIndex
      penultimateVertexIndex := D.penultimateVertexIndex
      terminalVertexIndex := D.terminalVertexIndex
      lastEdgePosition := D.lastEdgePosition
      penultimateVertexPosition := D.penultimateVertexPosition
      terminalVertexPosition := D.terminalVertexPosition
      lastEdgeNotIncidentPenultimate := D.lastEdgeNotIncidentPenultimate
      theta := D.gammaOne
      thetaOnLastEdge := hPTwo.symm ▸ hlastTwo
      thetaPresentPenultimate := hPTwo.symm ▸ hgammaPenTwo }
  by_cases hstored : D.theta ∈ HierarchyStoredColorsAt PTwo.counterexample.hierarchy
      (Fin.last PTwo.counterexample.hierarchy.dividerCount)
  · obtain ⟨g1, g2, hne, hpair⟩ := Finset.card_eq_two.mp
      (PTwo.counterexample.good.twoColors _ D.theta hstored)
    let finalData : HierarchySituationTwoCaseOneData G k e0 PTwo.corresponding.replacementInput T
        PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase
        PTwo.counterexample PTwo.minimumContext :=
      { toHierarchySituationTwoTailData := tailTwo
        alpha := D.theta
        gammaOne := g1
        gammaTwo := g2
        alphaMissingPenultimate := by
          change D.theta ∈ MissingColors G PTwo.coloring (T.vertex D.penultimateVertexIndex)
          rw [hPTwo]
          exact hthetaPenTwo
        alphaMissingTerminal := by
          change D.theta ∈ MissingColors G PTwo.coloring (T.vertex D.terminalVertexIndex)
          rw [hPTwo]
          exact hthetaTermTwo
        alphaStored := hstored
        gammaPair := hpair
        gammaDistinct := hne }
    exact HierarchySituationTwoSubcaseOneOne G k e0 PTwo.corresponding.replacementInput T
      PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase
      PTwo.counterexample PTwo.minimumContext finalData
  · let finalData : HierarchySituationTwoCaseTwoData G k e0 PTwo.corresponding.replacementInput T
        PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase
        PTwo.counterexample PTwo.minimumContext :=
      { toHierarchySituationTwoTailData := tailTwo
        alpha := D.theta
        alphaMissingPenultimate := by
          change D.theta ∈ MissingColors G PTwo.coloring (T.vertex D.penultimateVertexIndex)
          rw [hPTwo]
          exact hthetaPenTwo
        alphaMissingTerminal := by
          change D.theta ∈ MissingColors G PTwo.coloring (T.vertex D.terminalVertexIndex)
          rw [hPTwo]
          exact hthetaTermTwo
        alphaOutsideStored := hstored }
    exact HierarchySituationTwoSubcaseTwoOne G k e0 PTwo.corresponding.replacementInput T
      PTwo.coloring PTwo.corresponding.replacementETT PTwo.replacementBase
      PTwo.counterexample PTwo.minimumContext finalData
