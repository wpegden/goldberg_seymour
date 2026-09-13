import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtendedTashkinovTree
import Tablet.ExtendedTashkinovLadderStage
import Tablet.HkuMissingStoredMonotone
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumProperty
import Tablet.MaximumDefectiveChoice
import Tablet.ParallelExtensionColor
import Tablet.StableColoring
import Tablet.StableColoringBeforeVertex
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeExit
import Tablet.TreeExitComponentMeetsTreeOnlyAtExit
import Tablet.TreeExitPath
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequenceVertexSet
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TreeVerticesBefore
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.sc2

-- [TABLET NODE: ExtensionRulesTerminalLastAppearance]
theorem ExtensionRulesTerminalLastAppearance {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (v : V)
    (hkind : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (hvertex : ett.series.data.chosenVertex (Fin.last ett.rounds) = some v)
    (hvFinal : v ∈ TreeSequenceVertexSet T)
    (j : Fin (ett.rounds + 1))
    (hfirst : ETTFirstAppearanceIndex ett v hvFinal = j.val + 1)
    (hj : j.val + 1 = ett.rounds)
    (sigma : PartialEdgeColoring E k)
    (hproper : IsProperEdgeColoring G sigma)
    (hone : IsOneEdgeUncolored sigma e0)
    (hstable : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      (ett.series.data.coloring (Fin.last ett.rounds)) sigma) :
    StableColoringBeforeVertex T v hvFinal
        (TashkinovStoredColors ett.series.data j)
        (ett.series.data.coloring j) sigma ∧
      (0 < j.val →
        StableColoring (ett.series.data.tree j.castSucc)
          (TashkinovStoredColors ett.series.data j)
          (ett.series.data.coloring j) sigma) := by
-- BODY
  classical
  letI : DecidableEq V := Classical.decEq V
  have stepSegment : ∀ a : Fin (ett.rounds + 1), 0 < a.val →
      TreeSequenceInitialSegment (ett.series.data.tree a.castSucc)
        (ett.series.data.tree a.succ) := by
    intro a ha
    have certified := ett.series.certified a
    cases certified with
    | initial => simp at ha
    | SE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => assumption
    | PE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => assumption
    | RE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => assumption
  have orderTransfer : ∀ {A B : TreeSequence G e0},
      TreeSequenceInitialSegment A B → ∀ u w,
        TreeVertexOrder A u w → TreeVertexOrder B u w := by
    intro A B hAB u w huw
    rcases hAB with ⟨hlen, hvertices, _⟩
    rcases huw with ⟨iu, iw, hu, hw, hi⟩
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) iu,
      Fin.castLE (Nat.succ_le_succ hlen) iw,
      (hvertices iu).trans hu, (hvertices iw).trans hw, hi⟩
  have stableTreeMissingEq : ∀ {A : TreeSequence G e0}
      {C : Finset (Fin k)} {phi pi : PartialEdgeColoring E k},
      StableColoring A C phi pi →
        TreeMissingColors pi A = TreeMissingColors phi A := by
    intro A C phi pi h
    ext c
    simp only [TreeMissingColors, Finset.mem_biUnion]
    constructor
    · rintro ⟨w, hw, hc⟩
      rw [h.2 w hw] at hc
      exact ⟨w, hw, hc⟩
    · rintro ⟨w, hw, hc⟩
      rw [← h.2 w hw] at hc
      exact ⟨w, hw, hc⟩
  let q : Fin ett.rounds := ⟨j.val, by omega⟩
  have hqj : q.castSucc = j := by
    apply Fin.ext
    rfl
  have hqn : q.succ = Fin.last ett.rounds := by
    apply Fin.ext
    simp [q]
    omega
  have hkindQ : ett.series.data.kind q.succ =
      some TashkinovExtensionKind.PE := by
    rw [hqn]
    exact hkind
  have hvertexQ : ett.series.data.chosenVertex q.succ = some v := by
    rw [hqn]
    exact hvertex
  generalize htarget : q.succ = target
  cases ett.series.certified target with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    exact (Fin.succ_ne_zero q htarget).elim
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hbad : some TashkinovExtensionKind.SE =
        some TashkinovExtensionKind.PE :=
      currentKind.symm.trans (by simpa [htarget] using hkindQ)
    cases hbad
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hbad : some TashkinovExtensionKind.RE =
        some TashkinovExtensionKind.PE :=
      currentKind.symm.trans (by simpa [htarget] using hkindQ)
    cases hbad
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
    have hci : ci = q := by
      apply Fin.ext
      simpa using (congrArg Fin.val htarget).symm
    subst ci
    have hvchoice : choice.vertex = v :=
      Option.some.inj
        (currentVertex.symm.trans (by simpa [htarget] using hvertexQ))
    let Tn := ett.series.data.tree q.succ.castSucc
    let B := TreeVerticesBefore T v hvFinal
    have hvN : v ∈ TreeSequenceVertexSet Tn := by
      simpa [Tn, hvchoice] using choice.vertexDefective.1
    have hstableN : StableColoring Tn
        (TashkinovStoredColors ett.series.data q.succ)
        (ett.series.data.coloring q.succ) sigma := by
      simpa [Tn, hqn] using hstable
    have terminalSegment : TreeSequenceInitialSegment Tn T := by
      have hindex : q.succ.castSucc =
          (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) := by
        apply Fin.ext
        simpa using congrArg Fin.val hqn
      change TreeSequenceInitialSegment
        (ett.series.data.tree q.succ.castSucc) T
      rw [hindex]
      exact ett.abovePenultimate
    have beforeInN : ∀ w : V, w ∈ B → w ∈ TreeSequenceVertexSet Tn := by
      intro w hw
      unfold B TreeVerticesBefore at hw
      rcases Finset.mem_filter.mp hw with
        ⟨hwT, iw, iv, hiw, hiv, hlt⟩
      rcases Finset.mem_image.mp hwT with ⟨iwT, _, hiwT⟩
      rcases Finset.mem_image.mp hvN with ⟨ivN, _, hivN⟩
      rcases terminalSegment with ⟨hlen', hvertices', hedges'⟩
      let ivT := Fin.castLE (Nat.succ_le_succ hlen') ivN
      have hivEq : iv = ivT := by
        apply T.vertex_injective
        exact hiv.trans ((hvertices' ivN).trans hivN).symm
      have hiwEq : iwT = iw := by
        apply T.vertex_injective
        exact hiwT.trans hiw.symm
      have hiBound : iwT.val < Tn.length + 1 := by
        rw [hivEq, ← hiwEq] at hlt
        simp [ivT] at hlt
        omega
      let iwN : Fin (Tn.length + 1) := ⟨iwT.val, hiBound⟩
      apply Finset.mem_image.mpr
      refine ⟨iwN, Finset.mem_univ _, ?_⟩
      have hcast : Fin.castLE (Nat.succ_le_succ hlen') iwN = iwT := by
        apply Fin.ext
        rfl
      exact (hvertices' iwN).symm.trans (by simpa [hcast] using hiwT)
    have beforeNe : ∀ w : V, w ∈ B → w ≠ choice.vertex := by
      intro w hw heq
      unfold B TreeVerticesBefore at hw
      have horder := (Finset.mem_filter.mp hw).2
      have heqv : w = v := heq.trans hvchoice
      rcases horder with ⟨a, b, ha, hb, hab⟩
      have : a = b := T.vertex_injective (ha.trans (heqv ▸ hb).symm)
      omega
    have hgammaMissing : gamma ∈ MissingColors G secondStable choice.vertex := by
      rw [secondStableRelation.2 choice.vertex choice.vertexDefective.1]
      exact gammaRule.1
    have componentOnly := TreeExitComponentMeetsTreeOnlyAtExit Tn secondStable
      gamma choice.color choice.vertex secondStableProper hgammaMissing exitWitness
    have swapFixed : ∀ f : E, (∃ w ∈ B, Incident G w f) →
        TwoColorComponentSwap G secondStable gamma choice.color
          (Sum.inl choice.vertex) f = secondStable f := by
      intro f hf
      rcases hf with ⟨w, hw, hwf⟩
      have hfOutside : Sum.inr f ∉
          TwoColorComponent G secondStable gamma choice.color
            (Sum.inl choice.vertex) := by
        intro hfComponent
        let graph := TwoColorIncidenceGraph G secondStable gamma choice.color
        have hfSupport : Sum.inr f ∈ graph.support := by
          apply SimpleGraph.mem_support_of_reachable
            (G := graph) (u := Sum.inr f) (v := Sum.inl choice.vertex)
          · simp
          · exact SimpleGraph.ConnectedComponent.eq.mp hfComponent
        obtain ⟨z, hz⟩ := graph.mem_support.mp hfSupport
        have hfColor : secondStable f = some gamma ∨
            secondStable f = some choice.color := by
          cases z with
          | inl z => exact hz.2
          | inr z => simpa [graph, TwoColorIncidenceGraph] using hz
        have hwComponent : Sum.inl w ∈
            TwoColorComponent G secondStable gamma choice.color
              (Sum.inl choice.vertex) := by
          change graph.connectedComponentMk (Sum.inl w) =
            graph.connectedComponentMk (Sum.inl choice.vertex)
          exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            (by simp [graph, TwoColorIncidenceGraph, hwf, hfColor])).trans
              hfComponent
        exact beforeNe w hw
          ((componentOnly w (beforeInN w hw)).mp hwComponent)
      simp [TwoColorComponentSwap, hfOutside]
    have swapMissing : ∀ w : V, w ∈ B →
        MissingColors G
            (TwoColorComponentSwap G secondStable gamma choice.color
              (Sum.inl choice.vertex)) w =
          MissingColors G secondStable w := by
      intro w hw
      apply Finset.ext
      intro c
      simp only [MissingColors, PresentColors, Finset.mem_sdiff,
        Finset.mem_univ, true_and, Finset.mem_filter]
      constructor
      · intro hc
        rintro ⟨f, hwf, hfc⟩
        apply hc
        exact ⟨f, hwf, by
          rw [swapFixed f ⟨w, hw, hwf⟩]
          exact hfc⟩
      · intro hc
        rintro ⟨f, hwf, hfc⟩
        apply hc
        exact ⟨f, hwf, by
          rw [← swapFixed f ⟨w, hw, hwf⟩]
          exact hfc⟩
    have oldControlInN : ∀ c : Fin k,
        c ∈ (B.biUnion fun w =>
              MissingColors G (ett.series.data.coloring q.castSucc) w) ∪
            TashkinovStoredColors ett.series.data q.castSucc →
          c ∈ TreeMissingColors (ett.series.data.coloring q.castSucc) Tn ∪
            TashkinovStoredColors ett.series.data q.castSucc := by
      intro c hc
      rcases Finset.mem_union.mp hc with hc | hc
      · apply Finset.mem_union.mpr
        left
        simp only [Finset.mem_biUnion] at hc
        rcases hc with ⟨w, hw, hc⟩
        simp only [TreeMissingColors, Finset.mem_biUnion]
        exact ⟨w, beforeInN w hw, hc⟩
      · exact Finset.mem_union.mpr (Or.inr hc)
    have currentEdgeEq : ∀ f : E, (∃ w ∈ B, Incident G w f) →
        (∃ c ∈ (B.biUnion fun w =>
              MissingColors G (ett.series.data.coloring q.castSucc) w) ∪
            TashkinovStoredColors ett.series.data q.castSucc,
          ett.series.data.coloring q.castSucc f = some c) →
        ett.series.data.coloring q.succ f =
          ett.series.data.coloring q.castSucc f := by
      intro f hf hcolor
      rcases hcolor with ⟨c, hc, hcf⟩
      have hfN : TreeIncidentEdge Tn f := by
        rcases hf with ⟨w, hw, hwf⟩
        exact ⟨w, beforeInN w hw, hwf⟩
      have hcN := oldControlInN c hc
      have hselected : choice.selected f =
          ett.series.data.coloring q.castSucc f :=
        choice.selectedStable.1 f hfN ⟨c, hcN, hcf⟩
      have hcSecond : c ∈
          TreeMissingColors choice.selected Tn ∪
            insert choice.color
              (TashkinovStoredColors ett.series.data q.castSucc) := by
        rcases Finset.mem_union.mp hcN with hcN | hcN
        · apply Finset.mem_union.mpr
          left
          rw [stableTreeMissingEq choice.selectedStable]
          exact hcN
        · exact Finset.mem_union.mpr
            (Or.inr (Finset.mem_insert_of_mem hcN))
      have hsecond : secondStable f = choice.selected f :=
        secondStableRelation.1 f hfN
          ⟨c, hcSecond, hselected.trans hcf⟩
      calc
        ett.series.data.coloring q.succ f =
            TwoColorComponentSwap G secondStable gamma choice.color
              (Sum.inl choice.vertex) f := congrFun currentColoring f
        _ = secondStable f := swapFixed f hf
        _ = choice.selected f := hsecond
        _ = ett.series.data.coloring q.castSucc f := hselected
    have currentMissingEq : ∀ w : V, w ∈ B →
        MissingColors G (ett.series.data.coloring q.succ) w =
          MissingColors G (ett.series.data.coloring q.castSucc) w := by
      intro w hw
      calc
        MissingColors G (ett.series.data.coloring q.succ) w =
            MissingColors G
              (TwoColorComponentSwap G secondStable gamma choice.color
                (Sum.inl choice.vertex)) w :=
          congrArg (fun phi => MissingColors G phi w) currentColoring
        _ = MissingColors G secondStable w := swapMissing w hw
        _ = MissingColors G choice.selected w :=
          secondStableRelation.2 w (beforeInN w hw)
        _ = MissingColors G (ett.series.data.coloring q.castSucc) w :=
          choice.selectedStable.2 w (beforeInN w hw)
    have hmonotone :=
      (HkuMissingStoredMonotone G k ett.rounds e0 input ett.series q).1
    have beforeStableQ : StableColoringBeforeVertex T v hvFinal
        (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc) sigma := by
      unfold StableColoringBeforeVertex
      change (∀ f, (∃ w ∈ B, Incident G w f) → _ → _) ∧ _
      constructor
      · intro f hf hcolor
        rcases hcolor with ⟨c, hc, hcf⟩
        have hfN : TreeIncidentEdge Tn f := by
          rcases hf with ⟨w, hw, hwf⟩
          exact ⟨w, beforeInN w hw, hwf⟩
        have hcN := oldControlInN c hc
        have hcurrent := currentEdgeEq f hf ⟨c, hc, hcf⟩
        have hsigma : sigma f = ett.series.data.coloring q.succ f :=
          hstableN.1 f hfN
            ⟨c, hmonotone hcN, hcurrent.trans hcf⟩
        exact hsigma.trans hcurrent
      · intro w hw
        exact (hstableN.2 w (beforeInN w hw)).trans
          (currentMissingEq w hw)
    constructor
    · simpa [hqj] using beforeStableQ
    · intro hjPositive
      have hqPositive : 0 < q.val := by
        simpa [q] using hjPositive
      let Tprev := ett.series.data.tree q.castSucc.castSucc
      have prevToN : TreeSequenceInitialSegment Tprev Tn := by
        have hs := stepSegment q.castSucc (by simpa using hqPositive)
        simpa [Tprev, Tn] using hs
      have hvNotPrev : v ∉ TreeSequenceVertexSet Tprev := by
        intro hvPrev
        let r : Fin ett.rounds := ⟨q.val - 1, by omega⟩
        have hrq : r.succ = q.castSucc := by
          apply Fin.ext
          simp [r]
          exact Nat.sub_add_cancel hqPositive
        have hvStage : v ∈ TreeSequenceVertexSet
            (ExtendedTashkinovLadderStage ett r.castSucc) := by
          rw [show ExtendedTashkinovLadderStage ett r.castSucc =
              ett.series.data.tree r.succ.castSucc by
            unfold ExtendedTashkinovLadderStage
            exact @Fin.lastCases_castSucc ett.rounds
              (fun _ : Fin (ett.rounds + 1) => TreeSequence G e0) T
              (fun a => ett.series.data.tree a.succ.castSucc) r]
          rw [hrq]
          exact hvPrev
        have hbound : ETTFirstAppearanceIndex ett v hvFinal ≤
            q.val := by
          unfold ETTFirstAppearanceIndex
          dsimp
          have hmem : r.castSucc ∈
              Finset.univ.filter
                (fun a : Fin (ett.rounds + 1) =>
                  v ∈ TreeSequenceVertexSet
                    (ExtendedTashkinovLadderStage ett a)) := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact hvStage
          have hle := Finset.min'_le
            (Finset.univ.filter
              (fun a : Fin (ett.rounds + 1) =>
                v ∈ TreeSequenceVertexSet
                  (ExtendedTashkinovLadderStage ett a))) r.castSucc hmem
          have hnat := Fin.le_iff_val_le_val.mp hle
          rw [Fin.val_castSucc] at hnat
          calc
            _ + 1 ≤ r.val + 1 := Nat.succ_le_succ hnat
            _ = q.val := by
              simp [r]
              exact Nat.sub_add_cancel hqPositive
        have hfirstQ : ETTFirstAppearanceIndex ett v hvFinal =
            q.val + 1 := by
          simpa [q] using hfirst
        omega
      have prevInBefore : ∀ w : V, w ∈ TreeSequenceVertexSet Tprev →
          w ∈ B := by
        intro w hw
        have hwN := TreeSequenceInitialSegmentVertexSetSubset prevToN hw
        have hwT := TreeSequenceInitialSegmentVertexSetSubset
          terminalSegment hwN
        apply Finset.mem_filter.mpr
        refine ⟨hwT, ?_⟩
        rcases prevToN with ⟨hlen, hvertices, _⟩
        rcases Finset.mem_image.mp hw with ⟨iw, _, hiw⟩
        rcases Finset.mem_image.mp hvN with ⟨iv, _, hiv⟩
        have hleniv : Tprev.length < iv.val := by
          by_contra hnot
          have hivBound : iv.val < Tprev.length + 1 := by omega
          let ivPrev : Fin (Tprev.length + 1) := ⟨iv.val, hivBound⟩
          apply hvNotPrev
          apply Finset.mem_image.mpr
          refine ⟨ivPrev, Finset.mem_univ _, ?_⟩
          calc
            Tprev.vertex ivPrev =
                Tn.vertex (Fin.castLE (Nat.succ_le_succ hlen) ivPrev) :=
              (hvertices ivPrev).symm
            _ = Tn.vertex iv := by
              congr 1
            _ = v := hiv
        have horderN : TreeVertexOrder Tn w v := by
          refine ⟨Fin.castLE (Nat.succ_le_succ hlen) iw, iv,
            (hvertices iw).trans hiw, hiv, ?_⟩
          have hiwBound : iw.val ≤ Tprev.length := by omega
          simp only [Fin.val_castLE]
          omega
        exact orderTransfer terminalSegment w v horderN
      have stablePrevQ : StableColoring Tprev
          (TashkinovStoredColors ett.series.data q.castSucc)
          (ett.series.data.coloring q.castSucc) sigma := by
        constructor
        · intro f hf hcolor
          rcases hf with ⟨w, hw, hwf⟩
          rcases hcolor with ⟨c, hc, hcf⟩
          apply beforeStableQ.1 f ⟨w, prevInBefore w hw, hwf⟩
          refine ⟨c, ?_, hcf⟩
          rcases Finset.mem_union.mp hc with hc | hc
          · apply Finset.mem_union.mpr
            left
            simp only [TreeMissingColors, Finset.mem_biUnion] at hc
            rcases hc with ⟨z, hz, hzc⟩
            simp only [Finset.mem_biUnion]
            exact ⟨z, prevInBefore z hz, hzc⟩
          · exact Finset.mem_union.mpr (Or.inr hc)
        · intro w hw
          exact beforeStableQ.2 w (prevInBefore w hw)
      simpa [Tprev, hqj] using stablePrevQ
