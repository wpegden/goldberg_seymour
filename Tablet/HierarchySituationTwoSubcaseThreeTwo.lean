import Tablet.ChangeLemma
import Tablet.ColoredVertexSetElementary
import Tablet.CombinedStableClosurePreserved
import Tablet.CombinedStableColoring
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.ExtendedTashkinovTree
import Tablet.GoodHierarchy
import Tablet.GoodHierarchyReservedDisjoint
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexampleMeasure
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyBase
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyNonparallelFirstEdge
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchySegmentColors
import Tablet.HierarchySituationTwoCaseOneData
import Tablet.HierarchySituationTwoCaseThreeNormalizedData
import Tablet.HierarchySituationTwoCaseThreeTwoData
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
import Tablet.StableChangeCaseThree
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
import Tablet.TreeVertexOrder
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
import Tablet.P2813_T1_BaseDisplayedEdges
import Tablet.P2813_T1_TerminalRoute

-- [TABLET NODE: HierarchySituationTwoSubcaseThreeTwo]
theorem HierarchySituationTwoSubcaseThreeTwo {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseThreeTwoData
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
  let Bshort := HierarchyFullTailPrefix C (HierarchyFullTailLength C - 2)
  have hshortLen : Bshort.length + 2 = T.length := by
    change min (A.length + (T.length - A.length - 2)) T.length + 2 = T.length
    omega
  have hshortT : TreeSequenceInitialSegment Bshort T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have hshortB : TreeSequenceInitialSegment Bshort B := by
    refine ⟨by omega, ?_, ?_⟩
    · intro i
      rfl
    · intro i
      rfl
  have hterminalIncident :
      Incident G (T.vertex D.terminalVertexIndex) (T.edge D.lastEdgeIndex) := by
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
  have firstWitness (rho : PartialEdgeColoring E k) (X : TreeSequence G e0)
      (hXT : TreeSequenceInitialSegment X T) (c : Fin k)
      (hc : c ∈ TreeMissingColors rho X) :
      c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)) ∧
      (HierarchyFirstMissingPosition rho T c).val ≤ X.length := by
    as_aux_lemma =>
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
  have self (rho : PartialEdgeColoring E k) (a b : Fin k) (v : V) :
      Sum.inl v ∈ TwoColorComponent G rho a b (Sum.inl v) := by
    change (TwoColorIncidenceGraph G rho a b).connectedComponentMk (Sum.inl v) = _
    rfl
  have missingSubset (rho : PartialEdgeColoring E k) {X Y : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y) :
      TreeMissingColors rho X ⊆ TreeMissingColors rho Y := by
    as_aux_lemma =>
      clear * - rho hXY
      intro c hc
      obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hc
      exact Finset.mem_biUnion.mpr
        ⟨v, TreeSequenceInitialSegmentVertexSetSubset hXY hv, hm⟩
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
  -- Coincident first witnesses miss both colors, so their component is isolated.
  have separateAny (rho : PartialEdgeColoring E k) (a b : Fin k) (hne : a ≠ b)
      (hp : IsProperEdgeColoring G rho) (u v w : V)
      (huw : u ≠ w) (hvw : v ≠ w)
      (hu : a ∈ MissingColors G rho u) (hv : b ∈ MissingColors G rho v)
      (hw : a ∈ MissingColors G rho w ∨ b ∈ MissingColors G rho w)
      (hsame : TwoColorComponent G rho a b (Sum.inl u) =
        TwoColorComponent G rho a b (Sum.inl v)) :
      Disjoint (TwoColorComponent G rho a b (Sum.inl w))
        (TwoColorComponent G rho a b (Sum.inl u)) := by
    by_cases huv : u = v
    · subst v
      rcases TwoColorComponentsDisjoint G rho a b (Sum.inl w) (Sum.inl u) with he | hd
      · have noColor (c : Fin k) (hc : c ∈ MissingColors G rho u)
            (f : E) (hf : Incident G u f) : rho f ≠ some c := by
          intro hcol
          exact (Finset.mem_sdiff.mp hc).2
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, f, hf, hcol⟩)
        have hn : (TwoColorIncidenceGraph G rho a b).neighborSet (Sum.inl u) = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro x hx
          cases x with
          | inl x => exact hx
          | inr f =>
            rcases hx with ⟨hi, hc⟩
            exact hc.elim (noColor a hu f hi) (noColor b hv f hi)
        have hwIn : Sum.inl w ∈ TwoColorComponent G rho a b (Sum.inl u) :=
          he ▸ self rho a b w
        change (TwoColorIncidenceGraph G rho a b).connectedComponentMk (Sum.inl w) =
          (TwoColorIncidenceGraph G rho a b).connectedComponentMk (Sum.inl u) at hwIn
        exact False.elim (SimpleGraph.not_reachable_of_neighborSet_left_eq_empty
          (fun h => huw (Sum.inl.inj h)) hn
          (SimpleGraph.ConnectedComponent.exact hwIn).symm)
      · exact hd
    · exact separate rho a b hne hp u v w huv huw hvw hu hv hw hsame
  have prefixMissing (z : Sum V E) (rho : PartialEdgeColoring E k) (a b : Fin k) (hne : a ≠ b)
      (hp : IsProperEdgeColoring G rho)
      (helem : ColoredVertexSetElementary G rho (TreeSequenceVertexSet B))
      (u v : V) (huB : u ∈ TreeSequenceVertexSet B) (hvB : v ∈ TreeSequenceVertexSet B)
      (hu : a ∈ MissingColors G rho u) (hv : b ∈ MissingColors G rho v)
      (hdu : Sum.inl u ∉ TwoColorComponent G rho a b z)
      (hdv : Sum.inl v ∉ TwoColorComponent G rho a b z) :
      ∀ w ∈ TreeSequenceVertexSet B,
        MissingColors G (TwoColorComponentSwap G rho a b z) w = MissingColors G rho w := by
    as_aux_lemma =>
      clear_value B
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
  have firstPreserved (rho sigma : PartialEdgeColoring E k) (c : Fin k)
      (helem : ColoredVertexSetElementary G rho (TreeSequenceVertexSet B))
      (hmiss : ∀ v ∈ TreeSequenceVertexSet B, MissingColors G sigma v = MissingColors G rho v)
      (hc : c ∈ TreeMissingColors rho B) :
      HierarchyFirstMissingPosition sigma T c = HierarchyFirstMissingPosition rho T c := by
    as_aux_lemma =>
      clear_value B
      clear * - G T B rho sigma c helem hmiss hc firstWitness hBT
      have hr := firstWitness rho B hBT c hc
      have hc' : c ∈ TreeMissingColors sigma B := by
        obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp hc
        exact Finset.mem_biUnion.mpr ⟨v, hv, (hmiss v hv).symm ▸ hm⟩
      have hs := firstWitness sigma B hBT c hc'
      have pref (i : Fin (T.length + 1)) (hi : i.val ≤ B.length) :
          T.vertex i ∈ TreeSequenceVertexSet B := by
        let j : Fin (B.length + 1) := ⟨i.val, Nat.lt_succ_of_le hi⟩
        have he : Fin.castLE (Nat.succ_le_succ hBT.1) j = i := Fin.ext rfl
        exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr
          ⟨j, Finset.mem_univ _, (hBT.2.1 j).symm.trans (congrArg T.vertex he)⟩
      by_contra hne
      have hvne : T.vertex (HierarchyFirstMissingPosition sigma T c) ≠
          T.vertex (HierarchyFirstMissingPosition rho T c) :=
        fun he => hne (T.vertex_injective he)
      have hsOld := (hmiss _ (pref _ hs.2)) ▸ hs.1
      exact Finset.disjoint_left.mp (helem (pref _ hs.2) (pref _ hr.2) hvne) hsOld hr.1
  have firstUnaffected (z : Sum V E) (rho : PartialEdgeColoring E k) (a b c : Fin k)
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
  have sameTn (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      P.corresponding.replacementETT.series.data.tree
        (Fin.last P.corresponding.replacementETT.rounds).castSucc =
          ett.series.data.tree (Fin.last ett.rounds).castSucc := by
    have hs := (Fin.heq_fun_iff
      (congrArg (fun n => n + 2) P.sameGood.1.2.1)).mp P.sameGood.1.2.2.1 0
    exact P.counterexample.hierarchy.baseStage.symm.trans (hs.symm.trans H.baseStage)
  have sameLast (P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx) :
      HierarchyStoredColorsAt H q =
        HierarchyStoredColorsAt P.counterexample.hierarchy
          (Fin.last P.counterexample.hierarchy.dividerCount) ∧
      ∀ eta ∈ HierarchyStoredColorsAt H q,
        C.good.gamma q eta = P.counterexample.good.gamma
          (Fin.last P.counterexample.hierarchy.dividerCount) eta := by
    obtain ⟨hc, hd⟩ := P.sameGood.2
    have hi : Fin.cast (congrArg (fun n => n + 1) hc) q =
        Fin.last P.counterexample.hierarchy.dividerCount := Fin.ext hc
    simpa only [hi] using hd q
  have commonPrefix {X Y F : TreeSequence G e0}
      (hXF : TreeSequenceInitialSegment X F) (hYF : TreeSequenceInitialSegment Y F)
      (hXY : X.length ≤ Y.length) : TreeSequenceInitialSegment X Y := by
    clear * - hXF hYF hXY
    refine ⟨hXY, ?_, ?_⟩
    · intro i
      exact (hYF.2.1 (Fin.castLE (Nat.succ_le_succ hXY) i)).symm.trans (hXF.2.1 i)
    · intro i
      exact (hYF.2.2 (Fin.castLE hXY i)).symm.trans (hXF.2.2 i)
  have hcoreLength : base.core.length ≤ A.length := by
    by_cases hz : H.dividerCount = 0
    · exact le_of_eq (congrArg TreeSequence.length (hAzero hz).symm)
    · rw [hApositive (Nat.pos_of_ne_zero hz)]
      have hm : Monotone (fun i : Fin (H.dividerCount + 2) => (H.stage i).length) :=
        Fin.monotone_iff_le_succ.mpr fun i => (H.nested i).1
      exact H.coreInsideFirst.1.trans (hm (show
        (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) ≤
          ⟨H.dividerCount, by omega⟩ from Nat.pos_of_ne_zero hz))
  have predecessorIncident (X : TreeSequence G e0)
      (hXT : TreeSequenceInitialSegment X T) (t : Fin T.length)
      (ht : t.val = X.length) : TreeIncidentEdge X (T.edge t) := by
    clear * - G T X hXT t ht
    obtain ⟨i, hi⟩ := T.attaches t
    let j : Fin (X.length + 1) := ⟨i.val, by have := i.isLt; omega⟩
    have he : Fin.castLE (Nat.succ_le_succ hXT.1) j =
        Fin.castLE (by omega : t.val + 1 ≤ T.length + 1) i := Fin.ext rfl
    refine ⟨X.vertex j, (@Finset.mem_image _ _ (Classical.decEq V)).mpr
      ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [← hXT.2.1 j, he, Incident, hi]
    exact Sym2.mem_mk_right _ _
  have seedStable {input' : PartialEdgeColoring E k}
      (rho sigma : PartialEdgeColoring E k)
      (ett' : ExtendedTashkinovTree G k e0 input' T rho)
      (base' : HierarchyBase ett' rho) (K : TashkinovHierarchy ett' base')
      (hw : HierarchyWeaklyStable K (Fin.last K.dividerCount) sigma)
      (hq : K.dividerCount = 0) :
      StableColoring (ett'.series.data.tree (Fin.last ett'.rounds).castSucc)
        (TashkinovStoredColors ett'.series.data (Fin.last ett'.rounds)) rho sigma := by
    clear * - ett' K hw hq
    have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) = 0 := Fin.ext hq
    rw [hi] at hw
    change (if ett'.series.data.kind (Fin.last ett'.rounds) =
        some TashkinovExtensionKind.PE then _ else _) at hw
    split_ifs at hw with hpe
    · exact hw.1
    · exact hw
  have weakEdges {input' : PartialEdgeColoring E k}
      (old new : PartialEdgeColoring E k)
      (ett' : ExtendedTashkinovTree G k e0 input' T old)
      (base' : HierarchyBase ett' old) (K : TashkinovHierarchy ett' base')
      (hw : HierarchyWeaklyStable K (Fin.last K.dividerCount) new)
      (ho : IsOneEdgeUncolored old e0) (hno : IsOneEdgeUncolored new e0) :
      ∀ t : Fin (HierarchyStarredStage K (Fin.last K.dividerCount)).length,
        new ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t) =
          old ((HierarchyStarredStage K (Fin.last K.dividerCount)).edge t) := by
    clear * - G k e0 input' T old new ett' base' K hw ho hno
    by_cases hz : K.dividerCount = 0
    · have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) = 0 := Fin.ext hz
      rw [hi] at hw ⊢
      exact P2813_T1_BaseDisplayedEdges G k e0 input' T old ett' base' new ho hno hw
    · have hi : (Fin.last K.dividerCount : Fin (K.dividerCount + 1)) =
          (⟨K.dividerCount - 1, by omega⟩ : Fin K.dividerCount).succ :=
        Fin.ext (by simp only [Fin.val_last, Fin.val_succ, Fin.val_mk]; omega)
      rw [hi] at hw ⊢
      intro t
      have hinv := hw.2
      by_cases ht : 1 ≤ t.val
      · exact hinv.1 t ht
      · let S := HierarchyStarredStage K
          (⟨K.dividerCount - 1, by omega⟩ : Fin K.dividerCount).succ
        have he : t = ⟨0, S.positive⟩ := Fin.ext (by change t.val = 0; omega)
        rw [he, S.first_edge, hno.1, ho.1]
  -- Swap the last-edge color, preserving the certified prefix route and Gamma cutoffs.
  have finish (beta : Fin k)
      (hbetaMissing : beta ∈ TreeMissingColors phi Bshort)
      (hbetaUnused : ∀ t : Fin T.length, A.length ≤ t.val →
        phi (T.edge t) ≠ some beta)
      (hbetaStored : beta ∉ HierarchyStoredColorsAt H q)
      (houtside : beta ∉ TreeMissingColors phi A →
        D.theta ∉ HierarchyStoredColorsAt H q)
      (hcutoff : ∀ eta ∈ HierarchyStoredColorsAt H q,
        beta ∈ C.good.gamma q eta →
          eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort)
      (POne : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx)
      (hprefix : ∀ v ∈ TreeSequenceVertexSet B,
        MissingColors G POne.coloring v = MissingColors G phi v)
      (hterm : beta ∈ MissingColors G POne.coloring (T.vertex D.terminalVertexIndex))
      (hlast : POne.coloring (T.edge D.lastEdgeIndex) = some D.theta)
      (hfixed : ∀ t : Fin T.length, A.length ≤ t.val →
        POne.coloring (T.edge t) = phi (T.edge t))
      (hUnused : ∀ t : Fin T.length, A.length ≤ t.val →
        POne.coloring (T.edge t) ≠ some beta)
      (hzero : POne.counterexample.hierarchy.dividerCount = 0 →
        beta ∈ TreeMissingColors POne.coloring A →
        beta ∈ TreeMissingColors POne.coloring
          (POne.corresponding.replacementETT.series.data.tree
            (Fin.last POne.corresponding.replacementETT.rounds).castSucc) ∨
        (beta ∉ TashkinovStoredColors POne.corresponding.replacementETT.series.data
          (Fin.last POne.corresponding.replacementETT.rounds) ∧
         D.theta ∉ TashkinovStoredColors POne.corresponding.replacementETT.series.data
          (Fin.last POne.corresponding.replacementETT.rounds))) : False := by
    as_aux_lemma =>
      let z : Sum V E := Sum.inl (T.vertex D.terminalVertexIndex)
      have hbetaTheta : beta ≠ D.theta := by
        intro he
        exact hbetaUnused D.lastEdgeIndex (by
          have hp := D.lastEdgePosition
          clear * - hp htail
          omega) (D.thetaOnLastEdge.trans (congrArg some he.symm))
      let ib := HierarchyFirstMissingPosition phi T beta
      have hbFirst := firstWitness phi Bshort hshortT beta hbetaMissing
      have hibB : T.vertex ib ∈ TreeSequenceVertexSet B := by
        let i : Fin (Bshort.length + 1) := ⟨ib.val, by have := hbFirst.2; omega⟩
        exact TreeSequenceInitialSegmentVertexSetSubset hshortB
          ((@Finset.mem_image _ _ (Classical.decEq V)).mpr ⟨i, Finset.mem_univ _, rfl⟩)
      have hby : T.vertex ib ≠ T.vertex D.penultimateVertexIndex := by
        intro he
        have hi := congrArg Fin.val (T.vertex_injective he)
        have hp := D.penultimateVertexPosition
        have hb : ib.val ≤ Bshort.length := hbFirst.2
        clear * - hi hp hb hshortLen
        omega
      have hbt : T.vertex ib ≠ T.vertex D.terminalVertexIndex := by
        intro he
        have hi := congrArg Fin.val (T.vertex_injective he)
        have hp := D.terminalVertexPosition
        have hb : ib.val ≤ Bshort.length := hbFirst.2
        clear * - hi hp hb hshortLen
        omega
      have hyt : T.vertex D.penultimateVertexIndex ≠ T.vertex D.terminalVertexIndex := by
        intro he
        have hi := congrArg Fin.val (T.vertex_injective he)
        have hp := D.penultimateVertexPosition
        have ht := D.terminalVertexPosition
        clear * - hi hp ht
        omega
      have horder : TreeVertexOrder T (T.vertex ib) (T.vertex D.penultimateVertexIndex) :=
        ⟨ib, D.penultimateVertexIndex, rfl, rfl, by
          have hb : ib.val ≤ Bshort.length := hbFirst.2
          have hp := D.penultimateVertexPosition
          clear * - hb hp hshortLen
          omega⟩
      have firstAfter (rho : PartialEdgeColoring E k) (c : Fin k)
          (hc : c ∈ MissingColors G rho (T.vertex (HierarchyFirstMissingPosition rho T c)))
          (hn : c ∉ TreeMissingColors rho A) :
          A.length < (HierarchyFirstMissingPosition rho T c).val := by
        clear * - G T A hAT rho c hc hn
        by_contra h
        have hi : (HierarchyFirstMissingPosition rho T c).val ≤ A.length := Nat.le_of_not_gt h
        let i : Fin (A.length + 1) := ⟨(HierarchyFirstMissingPosition rho T c).val, by omega⟩
        have he : Fin.castLE (Nat.succ_le_succ hAT.1) i =
            HierarchyFirstMissingPosition rho T c := Fin.ext rfl
        apply hn
        refine Finset.mem_biUnion.mpr ⟨A.vertex i, (@Finset.mem_image _ _ (Classical.decEq V)).mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
        rw [← hAT.2.1 i, he]
        exact hc
      let rho := POne.coloring
      let ettOne := POne.corresponding.replacementETT
      let baseOne' := POne.replacementBase
      let COne' := POne.counterexample
      let ctxOne := POne.minimumContext
      let HOne := COne'.hierarchy
      let qOne : Fin (HOne.dividerCount + 1) := Fin.last HOne.dividerCount
      have hmissingOne' : ∀ v ∈ TreeSequenceVertexSet B,
          MissingColors G rho v = MissingColors G phi v := by
        exact hprefix
      have hElementaryOne : ColoredVertexSetElementary G rho (TreeSequenceVertexSet B) := by
        intro u hu v hv huv
        rw [hmissingOne' u hu, hmissingOne' v hv]
        exact hElementary hu hv huv
      have missingEq (X : TreeSequence G e0) (hXB : TreeSequenceInitialSegment X B) :
          TreeMissingColors rho X = TreeMissingColors phi X := by
        unfold TreeMissingColors
        exact Finset.biUnion_congr rfl (fun v hv =>
          hmissingOne' v (TreeSequenceInitialSegmentVertexSetSubset hXB hv))
      have hmissingA := missingEq A hAB
      have hbetaStoredOne : beta ∉ HierarchyStoredColorsAt HOne qOne := by
        rw [← (sameLast POne).1]
        exact hbetaStored
      have hthetaPenOne : D.theta ∈ MissingColors G rho (T.vertex D.penultimateVertexIndex) := by
        rw [hmissingOne' _ hyB]
        exact D.thetaMissingPenultimate
      have hgammaPenOne : beta ∉ MissingColors G rho (T.vertex D.penultimateVertexIndex) := by
        rw [hmissingOne' _ hyB]
        intro hm
        exact Finset.disjoint_left.mp (hElementary hibB hyB hby) hbFirst.1 hm
      have hgammaTermOne : beta ∈ MissingColors G rho (T.vertex D.terminalVertexIndex) := by
        exact hterm
      have hgammaWitnessOne' : beta ∈ MissingColors G rho (T.vertex ib) := by
        rw [hmissingOne' _ hibB]
        exact hbFirst.1
      have hfirstGammaOne : HierarchyFirstMissingPosition rho T beta = ib :=
        firstPreserved phi rho beta hElementary hmissingOne'
          (Finset.mem_biUnion.mpr ⟨_, hibB, hbFirst.1⟩)
      have hfirstThetaOne : HierarchyFirstMissingPosition rho T D.theta = D.penultimateVertexIndex :=
        (firstPreserved phi rho D.theta hElementary hmissingOne'
          (Finset.mem_biUnion.mpr ⟨_, hyB, D.thetaMissingPenultimate⟩)).trans hfirstTheta
      have hgammaUnusedOne : ∀ t : Fin T.length, A.length ≤ t.val →
          rho (T.edge t) ≠ some beta := by
        exact hUnused
      have hcaseOne (hm : beta ∈ TreeMissingColors phi A) :
          (0 < HOne.dividerCount ∧ beta ∈ TreeMissingColors rho
            (HOne.stage ⟨HOne.dividerCount, by omega⟩)) ∨
          (HOne.dividerCount = 0 ∧
            (beta ∈ TreeMissingColors rho
              (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) ∨
            (beta ∈ TreeMissingColors rho A ∧
              beta ∉ TashkinovStoredColors ettOne.series.data (Fin.last ettOne.rounds) ∧
              D.theta ∉ TashkinovStoredColors ettOne.series.data (Fin.last ettOne.rounds)))) := by
        have hcount : H.dividerCount = HOne.dividerCount := POne.sameGood.1.2.1
        by_cases hz : HOne.dividerCount = 0
        · refine Or.inr ⟨hz, ?_⟩
          have hmNew : beta ∈ TreeMissingColors rho A := hmissingA.symm ▸ hm
          rcases hzero hz hmNew with hn | hn
          · exact Or.inl hn
          · exact Or.inr ⟨hmNew, hn⟩
        · refine Or.inl ⟨Nat.pos_of_ne_zero hz, ?_⟩
          have hi : qOne =
              (⟨HOne.dividerCount - 1, by omega⟩ : Fin HOne.dividerCount).succ :=
            Fin.ext (by simp only [qOne, Fin.val_last, Fin.val_succ, Fin.val_mk]; omega)
          have hs := sameStar POne
          change HierarchyStarredStage HOne qOne = A at hs
          rw [hi] at hs
          have hind : (⟨HOne.dividerCount - 1, by omega⟩ : Fin HOne.dividerCount).succ.castSucc =
              (⟨HOne.dividerCount, by omega⟩ : Fin (HOne.dividerCount + 2)) :=
            Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_mk]; omega)
          change HOne.stage _ = A at hs
          rw [hind] at hs
          rw [hs, hmissingA]
          exact hm
      have hmissingPairOne : beta ∈ TreeMissingColors rho B ∧ D.theta ∈ TreeMissingColors rho B :=
        ⟨Finset.mem_biUnion.mpr ⟨_, hibB, hgammaWitnessOne'⟩,
          Finset.mem_biUnion.mpr ⟨_, hyB, hthetaPenOne⟩⟩
      have hchangeOne := ChangeLemma G k e0 POne.corresponding.replacementInput T rho ettOne
        baseOne' COne' ctxOne.proper ctxOne.oneEdgeUncolored ctxOne.lowerRung
        ctxOne.fewerDividers ctxOne.lexicographicMinimality
        (by
          change ColoredVertexSetElementary G rho
            (TreeSequenceVertexSet (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1)))
          rw [samePrefix POne]
          exact hElementaryOne)
        ctxOne.largeMissingSet beta D.theta hbetaTheta
        (by
          change beta ∈ TreeMissingColors rho
            (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1)) ∧
            D.theta ∈ TreeMissingColors rho
              (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1))
          rw [samePrefix POne]
          exact hmissingPairOne)
        (by
          dsimp only
          rw [sameStar POne, hfirstGammaOne, hfirstThetaOne]
          intro _
          refine ⟨horder, ?_⟩
          intro hc
          obtain ⟨t, ht, _, he⟩ := (Finset.mem_filter.mp hc).2
          exact hgammaUnusedOne t ht he)
      have hsameTwo : TwoColorComponent G rho beta D.theta (Sum.inl (T.vertex ib)) =
          TwoColorComponent G rho beta D.theta
            (Sum.inl (T.vertex D.penultimateVertexIndex)) := by
        rw [← hfirstGammaOne, ← hfirstThetaOne]
        by_cases hm : beta ∈ TreeMissingColors phi A
        · rcases hcaseOne hm with ⟨hp, hb⟩ | ⟨hz, hb⟩
          · exact hchangeOne.1 ⟨hp, Or.inl hb⟩
          · apply hchangeOne.2.1
            refine ⟨hz, ?_⟩
            rcases hb with hb | ⟨_, hbn, htn⟩
            · exact Or.inl hb
            · right
              rw [Finset.disjoint_left]
              intro c hc hd
              rcases Finset.mem_insert.mp hc with rfl | hc
              · exact hbn hd
              · exact htn (Finset.mem_singleton.mp hc ▸ hd)
        · have hnTheta : D.theta ∉ HierarchyStoredColorsAt HOne qOne := by
            rw [← (sameLast POne).1]
            exact houtside hm
          by_cases hz : HOne.dividerCount = 0
          · apply hchangeOne.2.1
            refine ⟨hz, Or.inr ?_⟩
            rw [Finset.disjoint_left]
            intro c hc hd
            rcases Finset.mem_insert.mp hc with rfl | hc
            · apply hbetaStoredOne
              refine Finset.mem_sdiff.mpr ⟨hd, ?_⟩
              rw [sameStar POne, hmissingA]
              exact hm
            · have he : c = D.theta := Finset.mem_singleton.mp hc
              subst c
              apply hnTheta
              refine Finset.mem_sdiff.mpr ⟨hd, ?_⟩
              rw [sameStar POne, hmissingA]
              exact hnotA (c := D.theta) D.thetaMissingPenultimate
          · apply hchangeOne.1
            refine ⟨Nat.pos_of_ne_zero hz, Or.inr ?_⟩
            rw [Finset.disjoint_left]
            intro c hc hd
            rcases Finset.mem_insert.mp hc with rfl | hc
            · exact hbetaStoredOne hd
            · exact hnTheta (Finset.mem_singleton.mp hc ▸ hd)
      have hdisjointTwo := separate rho beta D.theta hbetaTheta ctxOne.proper
        (T.vertex ib) (T.vertex D.penultimateVertexIndex) (T.vertex D.terminalVertexIndex)
        hby hbt hyt hgammaWitnessOne' hthetaPenOne (Or.inl hgammaTermOne) hsameTwo
      let muTwo := TwoColorComponentSwap G rho beta D.theta z
      have hpathTwo : TwoColorPathComponent G rho beta D.theta z :=
        ⟨hbetaTheta, _, self rho beta D.theta _,
          leaf rho beta D.theta hbetaTheta ctxOne.proper _ (Or.inl hgammaTermOne)⟩
      have houtsideBetaTwo : Sum.inl (T.vertex ib) ∉ TwoColorComponent G rho beta D.theta z := by
        intro hm
        exact Set.disjoint_left.mp hdisjointTwo hm (self rho beta D.theta _)
      have houtsideThetaTwo : Sum.inl (T.vertex D.penultimateVertexIndex) ∉
          TwoColorComponent G rho beta D.theta z := by
        intro hm
        apply Set.disjoint_left.mp hdisjointTwo hm
        rw [hsameTwo]
        exact self rho beta D.theta _
      have hmissingTwo := prefixMissing z rho beta D.theta hbetaTheta ctxOne.proper
        hElementaryOne _ _ hibB hyB hgammaWitnessOne' hthetaPenOne
        houtsideBetaTwo houtsideThetaTwo
      have hstoredTwo : ∀ c ∈ HierarchyStoredColorsAt HOne qOne,
          HierarchyFirstMissingPosition muTwo T c = HierarchyFirstMissingPosition rho T c := by
        intro c hc
        have hcb : c ≠ beta := fun he => hbetaStoredOne (he ▸ hc)
        by_cases hct : c = D.theta
        · exact hct.symm ▸
            firstPreserved rho muTwo D.theta hElementaryOne hmissingTwo hmissingPairOne.2
        · exact firstUnaffected z rho beta D.theta c hbetaTheta ctxOne.proper hcb hct
      have hthetaLastOne : rho (T.edge D.lastEdgeIndex) = some D.theta := hlast
      have hsuffix : TashkinovAugmentationSequence rho B T := by
        apply Relation.ReflTransGen.single
        refine ⟨hBlen.symm, hBT, D.theta, ?_, hmissingPairOne.2⟩
        have hi : Fin.cast hBlen (Fin.last B.length) = D.lastEdgeIndex :=
          Fin.ext (by
            have hl := D.lastEdgePosition
            simp only [Fin.val_cast, Fin.val_last]
            clear * - hBlen hl
            omega)
        rw [hi]
        exact hthetaLastOne
      have hthetaBound : (HierarchyFirstMissingPosition rho T D.theta).val ≤ B.length := by
        rw [hfirstThetaOne]
        have hp := D.penultimateVertexPosition
        clear * - hp hBlen
        omega
      have hgammaCutoff : ∀ c ∈ HierarchyStoredColorsAt HOne qOne,
          (beta ∈ POne.counterexample.good.gamma qOne c ∨
            D.theta ∈ POne.counterexample.good.gamma qOne c) →
          (HierarchyFirstMissingPosition rho T c).val ≤ B.length := by
        intro c hc hpair
        have hcOld : c ∈ HierarchyStoredColorsAt H q :=
          Finset.subset_of_eq (sameLast POne).1.symm hc
        have hpairOld : beta ∈ C.good.gamma q c ∨ D.theta ∈ C.good.gamma q c :=
          ((sameLast POne).2 c hcOld).symm ▸ hpair
        rcases hpairOld with hb | ht
        · rcases hcutoff c hcOld hb with he | hm
          · exact he.symm ▸ hthetaBound
          · have hmB : c ∈ TreeMissingColors phi B := missingSubset (X := Bshort) (Y := B) phi hshortB hm
            exact (le_of_eq (congrArg Fin.val
              (firstPreserved phi rho c hElementary hmissingOne' hmB))).trans
                ((firstWitness phi Bshort hshortT c hm).2.trans hshortB.1)
        · exact False.elim (hnotA (c := D.theta) D.thetaMissingPenultimate
            ((GoodHierarchyReservedDisjoint C.good q).1 c hcOld ht))
      obtain ⟨corrTwo, hmaxTwo, baseTwo, KTwo, goodTwo, hsameGoodTwo⟩ : ∃ corrTwo :
          CorrespondingExtendedTashkinovTree G k e0 ettOne muTwo T,
          MaximumProperty corrTwo.replacementETT ∧
            ∃ baseTwo : HierarchyBase corrTwo.replacementETT muTwo,
              ∃ KTwo : TashkinovHierarchy corrTwo.replacementETT baseTwo,
                ∃ goodTwo : GoodHierarchy KTwo, SameGoodHierarchy COne'.good goodTwo := by
        by_cases hm : beta ∈ TreeMissingColors phi A
        · have hstableTwo := StableChangeCasesOneTwo G k e0 POne.corresponding.replacementInput T rho
            ettOne baseOne' COne' ctxOne.proper ctxOne.oneEdgeUncolored ctxOne.lowerRung
            ctxOne.fewerDividers ctxOne.lexicographicMinimality
            (by
              change ColoredVertexSetElementary G rho (TreeSequenceVertexSet
                (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1)))
              rw [samePrefix POne]
              exact hElementaryOne)
            ctxOne.largeMissingSet beta D.theta hbetaTheta
            (by
              change beta ∈ TreeMissingColors rho
                (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1)) ∧
                D.theta ∈ TreeMissingColors rho
                  (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1))
              rw [samePrefix POne]
              exact hmissingPairOne)
            z hpathTwo muTwo rfl
            (by dsimp only; rcases hcaseOne hm with hpos | ⟨hz, hb⟩
                · exact Or.inl hpos
                · exact Or.inr ⟨hz, by
                    rcases hb with hb | ⟨hm, hn⟩
                    · exact Or.inl hb
                    · exact Or.inr ⟨by rw [sameStar POne]; exact hm, hn⟩⟩)
            (by dsimp only; rw [hfirstGammaOne]; exact hdisjointTwo)
          have hthetaExclusion := HierarchyTailMissingColorExclusion G k e0 input T phi
            ett base H hElementary (HierarchyFullTailLength C - 1)
            (by change 1 ≤ T.length - A.length - 1; clear * - htail; omega)
            (by change T.length - A.length - 1 < T.length - A.length; clear * - htail; omega)
            D.theta (by
              change D.theta ∈ MissingColors G phi (B.vertex (Fin.last B.length))
              rw [hBterminal]
              exact D.thetaMissingPenultimate)
          have hfixedTailTwo : ∀ t : Fin T.length, A.length ≤ t.val → t.val < B.length →
              muTwo (T.edge t) = rho (T.edge t) := by
            intro t ht hb
            have hng := hgammaUnusedOne t ht
            by_cases htheta : rho (T.edge t) = some D.theta
            · let tB : Fin B.length := ⟨t.val, hb⟩
              have hcast : Fin.castLE hBT.1 tB = t := Fin.ext rfl
              have heOld : phi (T.edge t) = some D.theta := by
                exact (hfixed t ht).symm.trans htheta
              have heB : phi (B.edge tB) = some D.theta := by
                rw [← hBT.2.2 tB, hcast]
                exact heOld
              obtain ⟨hz, hcore, hpos, f, _, _, _, _, _, hs⟩ :=
                hthetaExclusion tB ht (by
                  change tB.val < A.length + (T.length - A.length - 1)
                  have hv := tB.isLt
                  clear * - hv htail hBlen
                  change tB.val < B.length at hv
                  omega) heB
              have hzOne : HOne.dividerCount = 0 := POne.sameGood.1.2.1.symm.trans hz
              have htn : ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc = A :=
                (sameTn POne).trans ((hAzero hz).trans hcore).symm
              have hinc : TreeIncidentEdge
                  (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) (T.edge t) := by
                rw [htn]
                exact predecessorIncident A hAT t hpos
              have hsOld : D.theta ∈ HierarchyStoredColorsAt H q :=
                Finset.mem_sdiff.mpr ⟨hs, hnotA (c := D.theta) D.thetaMissingPenultimate⟩
              have hsOne : D.theta ∈ HierarchyStoredColorsAt HOne qOne :=
                (sameLast POne).1 ▸ hsOld
              exact (seedStable rho muTwo ettOne baseOne' HOne hstableTwo.1 hzOne).1 _ hinc
                ⟨D.theta, Finset.mem_union_right _ (Finset.mem_sdiff.mp hsOne).1, htheta⟩
            · simp only [muTwo, TwoColorComponentSwap, hng, htheta, if_false, ite_self]
          have hfixedCore := weakEdges rho muTwo ettOne baseOne' HOne hstableTwo.1
            ctxOne.oneEdgeUncolored hstableTwo.2.1.2.1
          change ∀ t : Fin (HierarchyStarredStage POne.counterexample.hierarchy
            (Fin.last POne.counterexample.hierarchy.dividerCount)).length,
            muTwo ((HierarchyStarredStage POne.counterexample.hierarchy
              (Fin.last POne.counterexample.hierarchy.dividerCount)).edge t) =
            rho ((HierarchyStarredStage POne.counterexample.hierarchy
              (Fin.last POne.counterexample.hierarchy.dividerCount)).edge t) at hfixedCore
          rw [sameStar POne] at hfixedCore
          have hfixedPrefix : ∀ t : Fin T.length, t.val < B.length →
              muTwo (T.edge t) = rho (T.edge t) := by
            intro t ht
            by_cases ha : t.val < A.length
            · let ta : Fin A.length := ⟨t.val, ha⟩
              have he : Fin.castLE hAT.1 ta = t := Fin.ext rfl
              rw [← he, hAT.2.2 ta]
              exact hfixedCore ta
            · exact hfixedTailTwo t (Nat.le_of_not_gt ha) ht
          have transportRoute (S : TreeSequence G e0)
              (hs : TashkinovAugmentationSequence rho S B) :
              TashkinovAugmentationSequence muTwo S B := by
            clear * - G T B rho muTwo hBT hfixedPrefix hmissingTwo commonPrefix hs
            unfold TashkinovAugmentationSequence at hs ⊢
            induction hs using Relation.ReflTransGen.head_induction_on with
            | refl => exact Relation.ReflTransGen.refl
            | @head X Y hstep htail ih =>
              have hYB := TashkinovAugmentationSequenceInitialSegment rho Y B htail
              obtain ⟨hlen, hXY, c, hedge, hm⟩ := hstep
              have hXB : TreeSequenceInitialSegment X B :=
                ⟨hXY.1.trans hYB.1,
                  fun i => (hYB.2.1 (Fin.castLE (Nat.succ_le_succ hXY.1) i)).trans (hXY.2.1 i),
                  fun i => (hYB.2.2 (Fin.castLE hXY.1 i)).trans (hXY.2.2 i)⟩
              refine Relation.ReflTransGen.head ⟨hlen, hXY, c, ?_, ?_⟩ ih
              · let tY : Fin Y.length := Fin.cast hlen.symm (Fin.last X.length)
                let tB : Fin B.length := Fin.castLE hYB.1 tY
                have hf := hfixedPrefix (Fin.castLE hBT.1 tB) tB.isLt
                rw [hBT.2.2 tB, hYB.2.2 tY] at hf
                exact hf.trans hedge
              · obtain ⟨v, hv, hvc⟩ := Finset.mem_biUnion.mp hm
                exact Finset.mem_biUnion.mpr ⟨v, hv,
                  (hmissingTwo v (TreeSequenceInitialSegmentVertexSetSubset hXB hv)).symm ▸ hvc⟩
          have hrouteTwo :
              (ettOne.series.data.kind (Fin.last ettOne.rounds) = some TashkinovExtensionKind.PE ∧
                TashkinovAugmentationSequence muTwo
                  (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) B) ∨
              ((ettOne.series.data.kind (Fin.last ettOne.rounds) = some TashkinovExtensionKind.SE ∨
                  ettOne.series.data.kind (Fin.last ettOne.rounds) = some TashkinovExtensionKind.RE) ∧
                ∃ f seed, ettOne.series.data.connectingEdges (Fin.last ettOne.rounds) = {f} ∧
                  TreeSequenceAdjoinEdge (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc) f seed ∧
                  TashkinovAugmentationSequence muTwo seed B) := by
            rcases P2813_T1_TerminalRoute G k e0 POne.corresponding.replacementInput T rho ettOne with
              ⟨hp, hseq⟩ | ⟨hp, f, seed, hedges, hseed, _, _, hseq⟩
            · have hTnB := commonPrefix ettOne.abovePenultimate hBT (by
                have hs := ettOne.strictAbovePenultimate
                clear * - hs hBlen
                omega)
              exact Or.inl ⟨hp, transportRoute _ (TashkinovAugmentationSequenceRestrict rho _ B T
                hseq hTnB hBT)⟩
            · have hseedT := TashkinovAugmentationSequenceInitialSegment rho seed T hseq
              have hTnCore : (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc).length ≤
                  baseOne'.core.length := by
                have hnp : ettOne.series.data.kind (Fin.last ettOne.rounds) ≠
                    some TashkinovExtensionKind.PE := by
                  intro he
                  rcases hp with he' | he' <;> rw [he'] at he <;> cases he
                rw [baseOne'.nonparallel hnp]
              have hcLen : baseOne'.core.length ≤ A.length := by
                rw [← POne.sameGood.1.1]
                exact hcoreLength
              have hsLen : seed.length ≤ B.length := by
                have hl := hseed.1
                change seed.length = (ettOne.series.data.tree (Fin.last ettOne.rounds).castSucc).length + 1 at hl
                clear * - hl hTnCore hcLen htail hBlen
                omega
              have hseedB := commonPrefix hseedT hBT hsLen
              exact Or.inr ⟨hp, f, seed, hedges, hseed,
                transportRoute seed (TashkinovAugmentationSequenceRestrict rho seed B T hseq hseedB hBT)⟩
          exact (StableChangeCasesOneTwoSplitTail G k e0 POne.corresponding.replacementInput T rho
            ettOne baseOne' COne' ctxOne beta D.theta hbetaTheta
            (by rw [samePrefix POne]; exact hmissingPairOne)
            z hpathTwo muTwo rfl
            (by dsimp only; rcases hcaseOne hm with hpos | ⟨hz, hb⟩
                · exact Or.inl hpos
                · exact Or.inr ⟨hz, by
                    rcases hb with hb | ⟨hm, hn⟩
                    · exact Or.inl hb
                    · exact Or.inr ⟨by rw [sameStar POne]; exact hm, hn⟩⟩)
            (by dsimp only; rw [hfirstGammaOne]; exact hdisjointTwo)
            B (by dsimp only; rw [sameStar POne]; exact hAB)
            (by dsimp only; rw [sameStar POne]; clear * - htail hBlen; omega)
            (by rw [samePrefix POne]; exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩)
            (by dsimp only; intro t _ ht; exact hfixedPrefix t ht)
            hrouteTwo hsuffix
            ⟨Finset.mem_biUnion.mpr ⟨_, hibB, (hmissingTwo _ hibB).symm ▸ hgammaWitnessOne'⟩,
              Finset.mem_biUnion.mpr ⟨_, hyB, (hmissingTwo _ hyB).symm ▸ hthetaPenOne⟩⟩
            (by rw [samePrefix POne]; exact hmissingTwo) hstoredTwo hgammaCutoff).2.2
        · have hnotAOne : beta ∉ TreeMissingColors rho A := by rw [hmissingA]; exact hm
          have ha := firstAfter rho beta (by rw [hfirstGammaOne]; exact hgammaWitnessOne') hnotAOne
          rw [hfirstGammaOne] at ha
          exact (StableChangeCaseThree G k e0 POne.corresponding.replacementInput T rho ettOne
            baseOne' COne' ctxOne.proper ctxOne.oneEdgeUncolored ctxOne.lowerRung ctxOne.fewerDividers
            ctxOne.lexicographicMinimality
            (by
              change ColoredVertexSetElementary G rho (TreeSequenceVertexSet
                (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1)))
              rw [samePrefix POne]
              exact hElementaryOne)
            ctxOne.largeMissingSet beta D.theta hbetaTheta
            (by
              change beta ∈ TreeMissingColors rho
                (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1)) ∧
                D.theta ∈ TreeMissingColors rho
                  (HierarchyFullTailPrefix COne' (HierarchyFullTailLength COne' - 1))
              rw [samePrefix POne]
              exact hmissingPairOne)
            z muTwo rfl
            (by
              dsimp only
              rw [sameStar POne, hfirstGammaOne]
              intro u hu
              obtain ⟨i, _, rfl⟩ := (@Finset.mem_image _ _ (Classical.decEq V)).mp hu
              exact ⟨Fin.castLE (Nat.succ_le_succ hAT.1) i, ib, hAT.2.1 i, rfl,
                lt_of_le_of_lt (Nat.le_of_lt_succ i.isLt) ha⟩)
            (by dsimp only; rw [hfirstGammaOne, hfirstThetaOne]; exact horder)
            (by dsimp only; rw [← (sameLast POne).1]; exact ⟨hbetaStored, houtside hm⟩)
            (by
              dsimp only
              rw [hfirstGammaOne]
              intro hc
              obtain ⟨t, ht, _, he⟩ := (Finset.mem_filter.mp hc).2
              exact hgammaUnusedOne t (by clear * - ht ha; omega) he)).2.2.2.2
      have hlastComponent : Sum.inr (T.edge D.lastEdgeIndex) ∈ TwoColorComponent G rho beta D.theta z := by
        have hadj : (TwoColorIncidenceGraph G rho beta D.theta).Adj
            (Sum.inr (T.edge D.lastEdgeIndex)) z := by
          exact ⟨hterminalIncident, Or.inr hthetaLastOne⟩
        change (TwoColorIncidenceGraph G rho beta D.theta).connectedComponentMk
          (Sum.inr (T.edge D.lastEdgeIndex)) = _
        exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
      have hlastTwo : muTwo (T.edge D.lastEdgeIndex) = some beta := by
        simp [muTwo, TwoColorComponentSwap, hlastComponent, hthetaLastOne, hbetaTheta.symm]
      have hthetaTermTwo : D.theta ∈ MissingColors G muTwo (T.vertex D.terminalVertexIndex) :=
        (TwoColorComponentSwapMissingBehavior G rho beta D.theta hbetaTheta ctxOne.proper z).2.1
          _ (self rho beta D.theta _) hgammaTermOne
      have hthetaPenTwo : D.theta ∈ MissingColors G muTwo (T.vertex D.penultimateVertexIndex) := by
        rw [hmissingTwo _ hyB]
        exact hthetaPenOne
      have hgammaPenTwo : beta ∉ MissingColors G muTwo (T.vertex D.penultimateVertexIndex) := by
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
          theta := beta
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
  -- A tail-unused stage color can replace alpha without changing any tail edge.
  have recolor (beta : Fin k)
      (hbetaA : beta ∈ TreeMissingColors phi A)
      (hbetaUnused : ∀ t : Fin T.length, A.length ≤ t.val →
        phi (T.edge t) ≠ some beta)
      (hbetaStored : beta ∉ HierarchyStoredColorsAt H q)
      (hbetaAlpha : beta ≠ D.alpha)
      (hzeroBeta : H.dividerCount = 0 →
        beta ∈ TreeMissingColors phi
          (ett.series.data.tree (Fin.last ett.rounds).castSucc)) :
      ∃ P : HierarchyReplacementPresentation G k e0 input T phi ett base C ctx,
        (∀ v ∈ TreeSequenceVertexSet B,
          MissingColors G P.coloring v = MissingColors G phi v) ∧
        beta ∈ MissingColors G P.coloring (T.vertex D.terminalVertexIndex) ∧
        (∀ t : Fin T.length, A.length ≤ t.val →
          P.coloring (T.edge t) = phi (T.edge t)) := by
    as_aux_lemma =>
      let ib := HierarchyFirstMissingPosition phi T beta
      let ia := HierarchyFirstMissingPosition phi T D.alpha
      have hb := firstWitness phi A hAT beta hbetaA
      have ha := firstWitness phi Bshort hshortT D.alpha D.alphaMissingTwoBefore
      have inPrefix (i : Fin (T.length + 1)) (hi : i.val ≤ B.length) :
          T.vertex i ∈ TreeSequenceVertexSet B := by
        let j : Fin (B.length + 1) := ⟨i.val, Nat.lt_succ_of_le hi⟩
        have hj : Fin.castLE (Nat.succ_le_succ hBT.1) j = i := Fin.ext rfl
        exact (@Finset.mem_image _ _ (Classical.decEq V)).mpr
          ⟨j, Finset.mem_univ _, (hBT.2.1 j).symm.trans (congrArg T.vertex hj)⟩
      have hibB := inPrefix ib (hb.2.trans hAB.1)
      have hiaB := inPrefix ia (ha.2.trans hshortB.1)
      have hbt : T.vertex ib ≠ T.vertex D.terminalVertexIndex := by
        intro he
        have hi := congrArg Fin.val (T.vertex_injective he)
        have hv : ib.val ≤ A.length := hb.2
        have ht := D.terminalVertexPosition
        clear * - hi hv ht htail
        omega
      have hat : T.vertex ia ≠ T.vertex D.terminalVertexIndex := by
        intro he
        have hi := congrArg Fin.val (T.vertex_injective he)
        have hv : ia.val ≤ Bshort.length := ha.2
        have ht := D.terminalVertexPosition
        clear * - hi hv ht hshortLen
        omega
      have hmissing : beta ∈ TreeMissingColors phi B ∧ D.alpha ∈ TreeMissingColors phi B :=
        ⟨Finset.mem_biUnion.mpr ⟨_, hibB, hb.1⟩,
          Finset.mem_biUnion.mpr ⟨_, hiaB, ha.1⟩⟩
      have hchange := ChangeLemma G k e0 input T phi ett base C ctx.proper
        ctx.oneEdgeUncolored ctx.lowerRung ctx.fewerDividers ctx.lexicographicMinimality
        hElementary ctx.largeMissingSet beta D.alpha hbetaAlpha hmissing
        (by
          dsimp only
          intro hn
          have hnAlpha : D.alpha ∉ TreeMissingColors phi A :=
            hn.resolve_left (not_not.mpr hbetaA)
          have hafter : A.length < ia.val := by
            by_contra hn
            have hi : ia.val ≤ A.length := Nat.le_of_not_gt hn
            let i : Fin (A.length + 1) := ⟨ia.val, Nat.lt_succ_of_le hi⟩
            have he : Fin.castLE (Nat.succ_le_succ hAT.1) i = ia := Fin.ext rfl
            apply hnAlpha
            refine Finset.mem_biUnion.mpr ⟨A.vertex i,
              (@Finset.mem_image _ _ (Classical.decEq V)).mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
            rw [← hAT.2.1 i, he]
            exact ha.1
          refine ⟨⟨ib, ia, rfl, rfl, lt_of_le_of_lt hb.2 hafter⟩, ?_⟩
          intro hc
          obtain ⟨t, ht, _, he⟩ := (Finset.mem_filter.mp hc).2
          exact hbetaUnused t ht he)
      have hcase :
          (0 < H.dividerCount ∧ beta ∈ TreeMissingColors phi
            (H.stage ⟨H.dividerCount, by omega⟩)) ∨
          (H.dividerCount = 0 ∧ beta ∈ TreeMissingColors phi
            (ett.series.data.tree (Fin.last ett.rounds).castSucc)) := by
        by_cases hz : H.dividerCount = 0
        · exact Or.inr ⟨hz, hzeroBeta hz⟩
        · exact Or.inl ⟨Nat.pos_of_ne_zero hz, hApositive (Nat.pos_of_ne_zero hz) ▸ hbetaA⟩
      have hsame : TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex ib)) =
          TwoColorComponent G phi beta D.alpha (Sum.inl (T.vertex ia)) := by
        rcases hcase with hp | hz
        · exact hchange.1 ⟨hp.1, Or.inl hp.2⟩
        · exact hchange.2.1 ⟨hz.1, Or.inl hz.2⟩
      let z : Sum V E := Sum.inl (T.vertex D.terminalVertexIndex)
      let mu := TwoColorComponentSwap G phi beta D.alpha z
      have hdisjoint := separateAny phi beta D.alpha hbetaAlpha ctx.proper
        (T.vertex ib) (T.vertex ia) (T.vertex D.terminalVertexIndex)
        hbt hat hb.1 ha.1 (Or.inr D.alphaMissingTerminal) hsame
      have hpath : TwoColorPathComponent G phi beta D.alpha z :=
        ⟨hbetaAlpha, _, self phi beta D.alpha _,
          leaf phi beta D.alpha hbetaAlpha ctx.proper _ (Or.inr D.alphaMissingTerminal)⟩
      have hdu : Sum.inl (T.vertex ib) ∉ TwoColorComponent G phi beta D.alpha z := by
        intro hm
        exact Set.disjoint_left.mp hdisjoint hm (self phi beta D.alpha _)
      have hdv : Sum.inl (T.vertex ia) ∉ TwoColorComponent G phi beta D.alpha z := by
        intro hm
        apply Set.disjoint_left.mp hdisjoint hm
        rw [hsame]
        exact self phi beta D.alpha _
      have hmissingNew := prefixMissing z phi beta D.alpha hbetaAlpha ctx.proper
        hElementary _ _ hibB hiaB hb.1 ha.1 hdu hdv
      have hfixed : ∀ t : Fin T.length, A.length ≤ t.val →
          mu (T.edge t) = phi (T.edge t) := by
        intro t ht
        have hb := hbetaUnused t ht
        have ha := D.alphaUnusedOnFullTail t ht
        simp only [mu, TwoColorComponentSwap, hb, ha, if_false, ite_self]
      have hstored : ∀ c ∈ HierarchyStoredColorsAt H q,
          HierarchyFirstMissingPosition mu T c = HierarchyFirstMissingPosition phi T c := by
        intro c hc
        have hcb : c ≠ beta := fun he => hbetaStored (he ▸ hc)
        by_cases hca : c = D.alpha
        · subst c
          exact firstPreserved phi mu D.alpha hElementary hmissingNew hmissing.2
        · exact firstUnaffected z phi beta D.alpha c hbetaAlpha ctx.proper hcb hca
      obtain ⟨corr, hmax, baseNew, K, good, hsameGood⟩ :=
        (StableChangeCasesOneTwoFullTail G k e0 input T phi ett base C ctx
          beta D.alpha hbetaAlpha hmissing z hpath mu rfl
          (by dsimp only; rcases hcase with hp | ⟨hz, hm⟩
              · exact Or.inl hp
              · exact Or.inr ⟨hz, Or.inl hm⟩)
          hdisjoint hfixed hmissingNew hstored).2.2.2.2
      have hterm : beta ∈ MissingColors G mu (T.vertex D.terminalVertexIndex) :=
        (TwoColorComponentSwapMissingBehavior G phi beta D.alpha hbetaAlpha ctx.proper z).2.2.1
          _ (self phi beta D.alpha _) D.alphaMissingTerminal
      let CNew : HierarchyCounterexample baseNew :=
        { positive := by rw [corr.rungAgreement]; exact C.positive
          hierarchy := K
          good := good
          maximum := hmax
          notElementary := by
            intro he
            have hv : T.vertex ib ∈ TreeSequenceVertexSet T := by simp [TreeSequenceVertexSet]
            have ht : T.vertex D.terminalVertexIndex ∈ TreeSequenceVertexSet T := by simp [TreeSequenceVertexSet]
            exact Finset.disjoint_left.mp (he hv ht hbt)
              ((hmissingNew _ hibB).symm ▸ hb.1) hterm }
      obtain ⟨P, hP⟩ := HierarchyReplacementPresentationTrans G k e0 input T phi
        ett base C ctx PRefl mu corr baseNew CNew hsameGood
      exact ⟨P, hP.symm ▸ hmissingNew, hP.symm ▸ hterm, hP.symm ▸ hfixed⟩
  -- Both stored-color branches use the same two swaps and compose their provenance.
  have gammaReduction (eta beta : Fin k)
      (heta : eta ∈ HierarchyStoredColorsAt H q)
      (hbeta : beta ∈ C.good.gamma q eta)
      (hUnused : ∀ t : Fin T.length, A.length ≤ t.val →
        phi (T.edge t) ≠ some beta)
      (hposition : eta = D.theta ∨ eta ∈ TreeMissingColors phi Bshort) : False := by
    as_aux_lemma =>
      have hbetaA := (GoodHierarchyReservedDisjoint C.good q).1 eta heta hbeta
      have hbetaStored : beta ∉ HierarchyStoredColorsAt H q := by
        intro hc
        exact Finset.disjoint_left.mp (GoodHierarchyReservedDisjoint C.good q).2
          (Finset.mem_biUnion.mpr ⟨eta, heta, hbeta⟩) hc
      have hbetaAlpha : beta ≠ D.alpha := by
        intro he
        have haGamma : D.alpha ∈ (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) :=
          Finset.mem_biUnion.mpr ⟨eta, heta, he ▸ hbeta⟩
        rcases D.normalizedAlternative with hp | hz | hs
        · exact hp.2.2 haGamma
        · exact hz.2.2 haGamma
        · exact hbetaStored (he.symm ▸ hs.1)
      have hzeroBeta (hz : H.dividerCount = 0) :
          beta ∈ TreeMissingColors phi
            (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by
        have hi : q = 0 := Fin.ext (by simpa only [q, Fin.val_last, Fin.val_zero] using hz)
        have hm := (Finset.mem_sdiff.mp (C.good.avoidance q eta heta hbeta)).1
        rw [hi] at hm
        exact hm
      obtain ⟨P, hprefix, hterm, hfixed⟩ :=
        recolor beta hbetaA hUnused hbetaStored hbetaAlpha hzeroBeta
      have hAS : TreeSequenceInitialSegment A Bshort :=
        ⟨by omega, hAT.2.1, hAT.2.2⟩
      apply finish beta (missingSubset phi hAS hbetaA) hUnused hbetaStored
        (fun hn => False.elim (hn hbetaA)) ?_ P hprefix hterm ?_ hfixed ?_ ?_
      · intro c hc hb
        have he : c = eta := by
          by_contra hne
          exact Finset.disjoint_left.mp (C.good.disjointPairs q c eta hc heta hne) hb hbeta
        exact he.symm ▸ hposition
      · exact (hfixed D.lastEdgeIndex (by
          have hl := D.lastEdgePosition
          clear * - hl htail
          omega)).trans D.thetaOnLastEdge
      · intro t ht
        rw [hfixed t ht]
        exact hUnused t ht
      · intro hz _
        left
        rw [sameTn P]
        have hm := hzeroBeta (P.sameGood.1.2.1.trans hz)
        obtain ⟨v, hv, hvc⟩ := Finset.mem_biUnion.mp hm
        have hTnB := commonPrefix ett.abovePenultimate hBT (by
          have hs := ett.strictAbovePenultimate
          clear * - hs hBlen
          omega)
        exact Finset.mem_biUnion.mpr ⟨v, hv,
          (hprefix v (TreeSequenceInitialSegmentVertexSetSubset hTnB hv)).symm ▸ hvc⟩
  by_cases hthetaStored : D.theta ∈ HierarchyStoredColorsAt H q
  · obtain ⟨g1, g2, hne, hpair⟩ := Finset.card_eq_two.mp
      (C.good.twoColors q D.theta hthetaStored)
    have hg : g1 ∈ C.good.gamma q D.theta := by rw [hpair]; simp
    have hgA := (GoodHierarchyReservedDisjoint C.good q).1 D.theta hthetaStored hg
    have hgTheta : g1 ≠ D.theta := by
      intro he
      exact hnotA (c := D.theta) D.thetaMissingPenultimate (he ▸ hgA)
    apply gammaReduction D.theta g1 hthetaStored hg ?_ (Or.inl rfl)
    intro t ht he
    by_cases hl : t = D.lastEdgeIndex
    · rw [hl, D.thetaOnLastEdge] at he
      exact hgTheta (Option.some.inj he).symm
    · have hav := (Finset.mem_sdiff.mp
        (C.good.avoidance q D.theta hthetaStored hg)).2
      apply hav
      unfold HierarchySegmentColors
      dsimp only
      have hend : H.stage q.succ = T := by
        convert H.terminalStage using 1
        congr 1
      rw [hend, hfirstTheta]
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, ht, ?_, he⟩
      have hp := D.penultimateVertexPosition
      have hlast := D.lastEdgePosition
      have hvne : t.val ≠ D.lastEdgeIndex.val := fun he => hl (Fin.ext he)
      have hv := t.isLt
      omega
  · by_cases halphaStored : D.alpha ∈ HierarchyStoredColorsAt H q
    · obtain ⟨g1, g2, hne, hpair⟩ := Finset.card_eq_two.mp
        (C.good.twoColors q D.alpha halphaStored)
      have hg : g1 ∈ C.good.gamma q D.alpha := by rw [hpair]; simp
      apply gammaReduction D.alpha g1 halphaStored hg ?_ (Or.inr D.alphaMissingTwoBefore)
      have havoid : Disjoint (C.good.gamma q D.alpha)
          (Finset.univ.filter fun c =>
            ∃ t : Fin T.length, A.length ≤ t.val ∧ phi (T.edge t) = some c) := by
        rcases D.normalizedAlternative with hp | hz | hs
        · exact False.elim (hp.2.1 halphaStored)
        · exact False.elim (hz.2.1 (Finset.mem_sdiff.mp halphaStored).1)
        · exact hs.2
      intro t ht he
      exact Finset.disjoint_left.mp havoid hg
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, ht, he⟩)
    · apply finish D.alpha D.alphaMissingTwoBefore D.alphaUnusedOnFullTail halphaStored
        (fun _ => hthetaStored) ?_ PRefl (fun _ _ => rfl) D.alphaMissingTerminal
        D.thetaOnLastEdge (fun _ _ => rfl) D.alphaUnusedOnFullTail ?_
      · intro eta heta ha
        have hGamma : D.alpha ∈ (HierarchyStoredColorsAt H q).biUnion (C.good.gamma q) :=
          Finset.mem_biUnion.mpr ⟨eta, heta, ha⟩
        rcases D.normalizedAlternative with hp | hz | hs
        · exact False.elim (hp.2.2 hGamma)
        · exact False.elim (hz.2.2 hGamma)
        · exact False.elim (halphaStored hs.1)
      · intro hz _
        right
        have halphaRaw : D.alpha ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds) := by
          rcases D.normalizedAlternative with hp | hzero | hs
          · have hpos := hp.1
            change 0 < H.dividerCount at hpos
            change H.dividerCount = 0 at hz
            omega
          · exact hzero.2.1
          · exact False.elim (halphaStored hs.1)
        have hthetaRaw : D.theta ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds) := by
          intro hc
          exact hthetaStored (Finset.mem_sdiff.mpr
            ⟨hc, hnotA (c := D.theta) D.thetaMissingPenultimate⟩)
        exact ⟨halphaRaw, hthetaRaw⟩
