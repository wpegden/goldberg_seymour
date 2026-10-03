import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryColorVertex
import Tablet.BoundaryEdges
import Tablet.CertifiedETTRestriction
import Tablet.DefectiveColor
import Tablet.DefectiveEdge
import Tablet.DefectiveVertex
import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtendedTashkinovTree
import Tablet.ExtensionBase
import Tablet.ExtensionRules
import Tablet.HkuMissingStoredMonotone
import Tablet.HkuParallelBoundaryStructure
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumProperty
import Tablet.MissingColors
import Tablet.ParallelExtensionColor
import Tablet.ParallelExtensionUndoStable
import Tablet.StableColoring
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.sc1
import Tablet.sc2

-- [TABLET NODE: Basic2TerminalPE]
theorem Basic2TerminalPE {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E)
    (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett)
    (hpositive : 0 < ett.rounds)
    (hlower : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input' T' generating'),
      0 < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
      ColoredVertexSetElementary G generating'
          (TreeSequenceVertexSet T') ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tnext : TreeSequence G e0 :=
           lower.series.data.tree (Fin.last (lower.rounds + 1))
         ∀ sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
           StableColoring Tnext
             (TashkinovStoredColors lower.series.data n)
             (lower.series.data.coloring n) sigma →
           ∀ alpha beta : Fin k,
             (alpha ∈ TreeMissingColors sigma Tnext ∨
               beta ∈ TreeMissingColors sigma Tnext) →
             TreeInterchangeable G Tnext sigma alpha beta) ∧
        ((∀ (q : Fin lower.rounds) (v : V),
          lower.series.data.kind q.succ =
              some TashkinovExtensionKind.PE →
          lower.series.data.chosenVertex q.succ = some v →
          ∀ hvFinal : v ∈ TreeSequenceVertexSet T',
          ∀ j : Fin (lower.rounds + 1),
            ETTFirstAppearanceIndex lower v hvFinal = j.val + 1 →
            ∀ sigma : PartialEdgeColoring E k,
              IsProperEdgeColoring G sigma →
              IsOneEdgeUncolored sigma e0 →
              StableColoring
                (lower.series.data.tree q.succ.castSucc)
                (TashkinovStoredColors lower.series.data q.succ)
                (lower.series.data.coloring q.succ) sigma →
              StableColoringBeforeVertex T' v hvFinal
                  (TashkinovStoredColors lower.series.data j)
                  (lower.series.data.coloring j) sigma ∧
                (0 < j.val →
                  StableColoring (lower.series.data.tree j.castSucc)
                    (TashkinovStoredColors lower.series.data j)
                    (lower.series.data.coloring j) sigma)) ∧
          ∀ (q r : Fin lower.rounds) (vq vr : V),
            q ≠ r → vq ≠ vr →
            lower.series.data.kind q.succ =
                some TashkinovExtensionKind.PE →
            lower.series.data.kind r.succ =
                some TashkinovExtensionKind.PE →
            lower.series.data.chosenVertex q.succ = some vq →
            lower.series.data.chosenVertex r.succ = some vr →
            ∀ (hvq : vq ∈ TreeSequenceVertexSet T')
              (hvr : vr ∈ TreeSequenceVertexSet T'),
              ETTFirstAppearanceIndex lower vq hvq =
                  ETTFirstAppearanceIndex lower vr hvr →
              Disjoint (lower.series.data.stored q.succ)
                (lower.series.data.stored r.succ)) ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tn : TreeSequence G e0 :=
           lower.series.data.tree n.castSucc
         ∀ (v : V) (gamma delta : Fin k),
           lower.series.data.kind n = some TashkinovExtensionKind.PE →
           lower.series.data.chosenVertex n = some v →
           lower.series.data.gamma n = some gamma →
           lower.series.data.delta n = some delta →
           ∀ sigma : PartialEdgeColoring E k,
             IsProperEdgeColoring G sigma →
             IsOneEdgeUncolored sigma e0 →
             StableColoring Tn
               (TashkinovStoredColors lower.series.data n)
               (lower.series.data.coloring n) sigma →
             ∀ w, w ∈ TreeSequenceVertexSet Tn →
               (Sum.inl w ∈ TwoColorComponent G sigma gamma delta
                   (Sum.inl v) ↔ w = v)) ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tn : TreeSequence G e0 :=
           lower.series.data.tree n.castSucc
         ∀ sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
           StableColoring Tn
             (TashkinovStoredColors lower.series.data n)
             (lower.series.data.coloring n) sigma →
           ∀ (delta : Fin k),
             DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta →
             ∀ (v : V),
               BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn)
                   delta v →
               (∃ w, BoundaryColorVertex G sigma
                   (TreeSequenceVertexSet Tn) delta w ∧
                 TreeVertexOrder Tn w v) →
               ∀ (hvFinal : v ∈ TreeSequenceVertexSet T')
                 (q : Fin lower.rounds) (vi : V),
                 (lower.series.data.kind q.succ =
                      some TashkinovExtensionKind.PE ∨
                    lower.series.data.kind q.succ =
                      some TashkinovExtensionKind.SE) →
                 lower.series.data.chosenVertex q.succ = some vi →
                 ETTFirstAppearanceIndex lower v hvFinal ≤ q.val + 1 →
                 v = vi ∨ TreeVertexOrder T' v vi) ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tn : TreeSequence G e0 :=
           lower.series.data.tree n.castSucc
         ∀ sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
           StableColoring Tn
             (TashkinovStoredColors lower.series.data n)
             (lower.series.data.coloring n) sigma →
           ModColoring lower sigma))
    (hterminalKind :
      ett.series.data.kind (Fin.last ett.rounds) =
        some TashkinovExtensionKind.PE) :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
    ∀ sigma : PartialEdgeColoring E k,
      IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
      StableColoring Tn
        (TashkinovStoredColors ett.series.data n)
        (ett.series.data.coloring n) sigma →
      ∀ (delta : Fin k),
        DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta →
        ∀ (v : V),
          BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta v →
          (∃ w, BoundaryColorVertex G sigma
              (TreeSequenceVertexSet Tn) delta w ∧
            TreeVertexOrder Tn w v) →
          ∀ (hvFinal : v ∈ TreeSequenceVertexSet T)
            (q : Fin ett.rounds) (vi : V),
            (ett.series.data.kind q.succ =
                 some TashkinovExtensionKind.PE ∨
               ett.series.data.kind q.succ =
                 some TashkinovExtensionKind.SE) →
            ett.series.data.chosenVertex q.succ = some vi →
            ETTFirstAppearanceIndex ett v hvFinal ≤ q.val + 1 →
            v = vi ∨ TreeVertexOrder T v vi := by
-- BODY
  classical
  letI : DecidableEq V := Classical.decEq V
  have segmentRefl (A : TreeSequence G e0) :
      TreeSequenceInitialSegment A A :=
    ⟨le_rfl, (by intro i; rfl), (by intro i; rfl)⟩
  have segmentTrans {A B C : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B)
      (hBC : TreeSequenceInitialSegment B C) :
      TreeSequenceInitialSegment A C := by
    rcases hAB with ⟨hab, hvab, heab⟩
    rcases hBC with ⟨hbc, hvbc, hebc⟩
    refine ⟨hab.trans hbc, ?_, ?_⟩
    · intro i
      have hmid := hvbc (Fin.castLE (Nat.succ_le_succ hab) i)
      exact (by simpa using hmid.trans (hvab i))
    · intro i
      have hmid := hebc (Fin.castLE hab i)
      exact (by simpa using hmid.trans (heab i))
  have stepSegment : ∀ i : Fin (ett.rounds + 1), 0 < i.val →
      TreeSequenceInitialSegment (ett.series.data.tree i.castSucc)
        (ett.series.data.tree i.succ) := by
    intro i hi
    have cert := ett.series.certified i
    cases cert with
    | initial => exact (by simpa using hi)
    | SE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => assumption
    | PE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => assumption
    | RE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => assumption
  have stageToStage : ∀ (a b : ℕ) (_ha : 1 ≤ a) (_hab : a ≤ b)
      (_hb : b ≤ ett.rounds),
      TreeSequenceInitialSegment
        (ett.series.data.tree ⟨a, by omega⟩)
        (ett.series.data.tree ⟨b, by omega⟩) := by
    intro a b ha hab hb
    have chain : ∀ (d : ℕ) (_hd : a + d ≤ b),
        TreeSequenceInitialSegment
          (ett.series.data.tree ⟨a, by omega⟩)
          (ett.series.data.tree ⟨a + d, by omega⟩) := by
      intro d hd
      induction d with
      | zero => simpa using segmentRefl (ett.series.data.tree ⟨a, by omega⟩)
      | succ d ih =>
          have hprev := ih (by omega)
          let idx : Fin (ett.rounds + 1) := ⟨a + d, by omega⟩
          have hone := stepSegment idx (by dsimp [idx]; omega)
          have hone' : TreeSequenceInitialSegment
              (ett.series.data.tree ⟨a + d, by omega⟩)
              (ett.series.data.tree ⟨a + (d + 1), by omega⟩) := by
            simpa [idx, Nat.add_assoc] using hone
          exact segmentTrans hprev hone'
    have hchain := chain (b - a) (by omega)
    convert hchain using 1 <;> apply congrArg ett.series.data.tree <;>
      apply Fin.ext <;> simp <;> omega
  have orderTransfer : ∀ {A B : TreeSequence G e0},
      TreeSequenceInitialSegment A B → ∀ u w,
        TreeVertexOrder A u w → TreeVertexOrder B u w := by
    intro A B hAB u w huw
    rcases hAB with ⟨hlen, hvertices, _⟩
    rcases huw with ⟨iu, iw, hu, hw, hi⟩
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) iu,
      Fin.castLE (Nat.succ_le_succ hlen) iw,
      (hvertices iu).trans hu, (hvertices iw).trans hw, hi⟩
  dsimp only
  intro sigma hproper hone hstable delta hdefective v hvBoundary
    hvNonminimum hvFinal q vi hkind hchosen hfirstBound
  rcases hvBoundary with ⟨hvN, a, haColor, hva⟩
  rcases hvNonminimum with
    ⟨w, ⟨hwN, b, hbColor, hwb⟩, hwv⟩
  let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let previous : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
  have hpreviousSucc : previous.succ = terminal := by
    apply Fin.ext
    simp [previous, terminal]
    omega
  have htreeTerminal :
      ett.series.data.tree terminal.castSucc =
        ett.series.data.tree ⟨ett.rounds, by omega⟩ := by
    congr 1
  have cert := ett.series.certified terminal
  generalize hslot : terminal = slot at cert
  cases cert with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    have hz := congrArg Fin.val hslot
    simp [terminal] at hz
    omega
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hterm := hterminalKind
    change ett.series.data.kind terminal =
      some TashkinovExtensionKind.PE at hterm
    rw [hslot, currentKind] at hterm
    simp at hterm
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hterm := hterminalKind
    change ett.series.data.kind terminal =
      some TashkinovExtensionKind.PE at hterm
    rw [hslot, currentKind] at hterm
    simp at hterm
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
    have hci : ci = previous := by
      apply Fin.ext
      have hs := congrArg Fin.val hslot
      simp [terminal, previous] at hs ⊢
      omega
    subst ci
    have hterminalEq : terminal = previous.succ := hslot
    have htreeEq : ett.series.data.tree terminal.castSucc =
        ett.series.data.tree previous.succ.castSucc := by
      rw [hterminalEq]
    have hchoiceVertex : choice.vertex ∈
        TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc) := by
      simpa [htreeEq] using choice.vertexDefective.1
    have hgammaSecond : gamma ∈ MissingColors G secondStable
        choice.vertex := by
      rw [secondStableRelation.2 choice.vertex choice.vertexDefective.1]
      exact gammaRule.1
    have hchoiceSecond : secondStable choice.edge = some choice.color := by
      have hfix := secondStableRelation.1 choice.edge
        ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
        ⟨choice.color, Finset.mem_union_right _
          (Finset.mem_insert_self _ _), choice.edgeColor⟩
      exact hfix.trans choice.edgeColor
    have hgammaDeltaNe : gamma ≠ choice.color := by
      intro heq
      have hpresent : gamma ∈ PresentColors G secondStable choice.vertex := by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨choice.edge, choice.edgeIncident, heq ▸ hchoiceSecond⟩
      have hnot : gamma ∉ PresentColors G secondStable choice.vertex := by
        simpa [MissingColors] using hgammaSecond
      exact hnot hpresent
    have hchoiceSecondComponent : Sum.inr choice.edge ∈
        TwoColorComponent G secondStable gamma choice.color
          (Sum.inl choice.vertex) := by
      apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      simp [TwoColorIncidenceGraph, choice.edgeIncident, hchoiceSecond]
    have hdeltaCurrentMissing : choice.color ∈ MissingColors G
        (ett.series.data.coloring terminal) choice.vertex := by
      rw [hterminalEq, MissingColors]
      simp only [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hpresent
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
        true_and] at hpresent
      rcases hpresent with ⟨f, hfIncident, hfCurrent⟩
      rw [currentColoring] at hfCurrent
      by_cases hfComponent : Sum.inr f ∈
          TwoColorComponent G secondStable gamma choice.color
            (Sum.inl choice.vertex)
      · by_cases hfg : secondStable f = some gamma
        · have hp : gamma ∈ PresentColors G secondStable choice.vertex := by
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
              true_and]
            exact ⟨f, hfIncident, hfg⟩
          have hnot : gamma ∉ PresentColors G secondStable choice.vertex := by
            simpa [MissingColors] using hgammaSecond
          exact hnot hp
        · by_cases hfd : secondStable f = some choice.color
          · have heq : choice.color = gamma := by
              simpa [TwoColorComponentSwap, hfComponent, hfg, hfd,
                hgammaDeltaNe] using hfCurrent
            exact hgammaDeltaNe heq.symm
          · simp [TwoColorComponentSwap, hfComponent, hfg, hfd] at hfCurrent
      · have hfd : secondStable f = some choice.color := by
          simpa [TwoColorComponentSwap, hfComponent] using hfCurrent
        by_cases hfeq : f = choice.edge
        · subst f
          exact hfComponent hchoiceSecondComponent
        · exact (secondStableProper hfeq
            ⟨choice.vertex, hfIncident, choice.edgeIncident⟩
            hfd hchoiceSecond).elim
    have hdeltaSigmaMissing : choice.color ∈ MissingColors G sigma
        choice.vertex := by
      rw [hstable.2 choice.vertex hchoiceVertex]
      exact hdeltaCurrentMissing
    have hgammaControl : gamma ∈
        TreeMissingColors (ett.series.data.coloring terminal)
            (ett.series.data.tree terminal.castSucc) ∪
          TashkinovStoredColors ett.series.data terminal := by
      by_cases hm : gamma ∈
          TreeMissingColors (ett.series.data.coloring terminal)
            (ett.series.data.tree terminal.castSucc)
      · exact Finset.mem_union_left _ hm
      · apply Finset.mem_union_right
        rw [TashkinovStoredColors]
        simp only [show terminal.val ≠ 0 by simp [terminal]; omega,
          if_false, Finset.mem_sdiff]
        refine ⟨?_, hm⟩
        simp only [Finset.mem_biUnion]
        refine ⟨terminal, Finset.mem_univ _, ?_⟩
        rw [hterminalEq, currentStored]
        simp
    have hfixBoth := (sc1 G e0
        (ett.series.data.tree terminal.castSucc)
        (TashkinovStoredColors ett.series.data terminal)
        (ett.series.data.coloring terminal) sigma
        (by simpa [hterminalEq] using currentProper)
        (by simpa [hterminalEq] using currentOneUncolored)
        hproper hone).mp hstable
    have boundaryIncident : ∀ {f : E},
        f ∈ BoundaryEdges G
            (TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc)) →
          TreeIncidentEdge (ett.series.data.tree terminal.castSucc) f := by
      intro f hf
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] at hf
      rcases hf with ⟨x, hx, y, hy, hxy⟩
      exact ⟨x, hx, by simpa [Incident, hxy]⟩
    have hgammaBoundaryCurrent :
        BoundaryColorEdges G (ett.series.data.coloring terminal)
          (TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc))
          gamma = {choice.edge} := by
      have hbound := HkuParallelBoundaryStructure G k ett.rounds e0 input
        ett.series previous choice.edge choice.color gamma choice.vertex
        currentKind currentEdges currentDelta currentGamma currentVertex
      simpa [hterminalEq] using hbound.1
    have hgammaBoundarySigma :
        BoundaryColorEdges G sigma
          (TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc))
          gamma = {choice.edge} := by
      rw [← hgammaBoundaryCurrent]
      apply Finset.ext
      intro f
      simp only [BoundaryColorEdges, Finset.mem_filter]
      constructor
      · rintro ⟨hfBoundary, hfSigma⟩
        refine ⟨hfBoundary, ?_⟩
        have hfix := hfixBoth f (boundaryIncident hfBoundary)
          (Or.inr ⟨gamma, hgammaControl, hfSigma⟩)
        exact hfix.symm.trans hfSigma
      · rintro ⟨hfBoundary, hfCurrent⟩
        refine ⟨hfBoundary, ?_⟩
        have hfix := hfixBoth f (boundaryIncident hfBoundary)
          (Or.inl ⟨gamma, hgammaControl, hfCurrent⟩)
        exact hfix.trans hfCurrent
    have hdeltaGammaNe : delta ≠ gamma := by
      intro heq
      subst delta
      unfold DefectiveColor at hdefective
      rw [hgammaBoundarySigma] at hdefective
      simp at hdefective
    have hcomponent : ∀ x,
        x ∈ TreeSequenceVertexSet
            (ett.series.data.tree terminal.castSucc) →
        (Sum.inl x ∈ TwoColorComponent G sigma gamma choice.color
            (Sum.inl choice.vertex) ↔ x = choice.vertex) := by
      have hbase := ExtensionBase G k e0 input T generating ett hMP hpositive
        hlower choice.vertex gamma choice.color
        (by simpa only [← hpreviousSucc, terminal] using currentKind)
        (by simpa only [← hpreviousSucc, terminal] using currentVertex)
        (by simpa only [← hpreviousSucc, terminal] using currentGamma)
        (by simpa only [← hpreviousSucc, terminal] using currentDelta)
        sigma hproper hone hstable
      simpa [terminal] using hbase
    obtain ⟨selected, recoveredSecond, hselectedProper, hselectedOne,
        hselectedStable, hrecoveredSecondProper, hrecoveredSecondOne,
        hrecoveredSecondStable, hcurrentSwap, hundoneSecond,
        hundoneSelected, hundonePrevious⟩ :=
      ParallelExtensionUndoStable G k ett.rounds e0 input ett.series previous
        choice.vertex gamma choice.color currentKind currentVertex currentGamma
        currentDelta sigma hproper hone
        (by simpa only [hpreviousSucc, terminal] using hstable)
        choice.vertexDefective.1
        (by simpa only [hpreviousSucc, terminal] using hcomponent)
    let recovered := TwoColorComponentSwap G sigma gamma choice.color
      (Sum.inl choice.vertex)
    have hrecoveredProper : IsProperEdgeColoring G recovered := by
      exact TwoColorComponentSwapProper G sigma gamma choice.color
        hgammaDeltaNe hproper (Sum.inl choice.vertex)
    have hrecoveredOne : IsOneEdgeUncolored recovered e0 := by
      unfold IsOneEdgeUncolored
      constructor
      · by_cases he : Sum.inr e0 ∈
            TwoColorComponent G sigma gamma choice.color
              (Sum.inl choice.vertex)
        · simp [recovered, TwoColorComponentSwap, he, hone.1]
        · simp [recovered, TwoColorComponentSwap, he, hone.1]
      · intro e he0
        obtain ⟨c, hc⟩ := hone.2 e he0
        by_cases he : Sum.inr e ∈
            TwoColorComponent G sigma gamma choice.color
              (Sum.inl choice.vertex)
        · by_cases hcg : c = gamma
          · exact ⟨choice.color, by
              simp [recovered, TwoColorComponentSwap, he, hc, hcg]⟩
          · by_cases hcd : c = choice.color
            · exact ⟨gamma, by
                simp [recovered, TwoColorComponentSwap, he, hc, hcd,
                  hgammaDeltaNe, hgammaDeltaNe.symm]⟩
            · exact ⟨c, by
                simp [recovered, TwoColorComponentSwap, he, hc, hcg, hcd]⟩
        · exact ⟨c, by
            simp [recovered, TwoColorComponentSwap, he, hc]⟩
    have hrecoveredStable : StableColoring
        (ett.series.data.tree terminal.castSucc)
        (TashkinovStoredColors ett.series.data previous.castSucc)
        (ett.series.data.coloring previous.castSucc) recovered := by
      simpa [recovered, hterminalEq] using hundonePrevious
    have hcomponentEdgeColor : ∀ f,
        Sum.inr f ∈ TwoColorComponent G sigma gamma choice.color
            (Sum.inl choice.vertex) →
          sigma f = some gamma ∨ sigma f = some choice.color := by
      intro f hf
      have hs : Sum.inr f ∈
          (TwoColorIncidenceGraph G sigma gamma choice.color).support := by
        apply SimpleGraph.mem_support_of_reachable
          (G := TwoColorIncidenceGraph G sigma gamma choice.color)
          (u := Sum.inr f) (v := Sum.inl choice.vertex) (by simp)
        exact SimpleGraph.ConnectedComponent.eq.mp hf
      obtain ⟨r, hr⟩ :=
        (TwoColorIncidenceGraph G sigma gamma choice.color).mem_support.mp hs
      cases r with
      | inl x => exact hr.2
      | inr x => simpa [TwoColorIncidenceGraph] using hr
    have targetEdgeOutside : ∀ (f : E) (x : V),
        x ∈ TreeSequenceVertexSet
            (ett.series.data.tree terminal.castSucc) →
        Incident G x f → sigma f = some delta →
        Sum.inr f ∉ TwoColorComponent G sigma gamma choice.color
          (Sum.inl choice.vertex) := by
      intro f x hx hxf hfd hfComponent
      rcases hcomponentEdgeColor f hfComponent with hfg | hfc
      · apply hdeltaGammaNe
        exact Option.some.inj (hfd.symm.trans hfg)
      · have hxComponent : Sum.inl x ∈
            TwoColorComponent G sigma gamma choice.color
              (Sum.inl choice.vertex) := by
          change (TwoColorIncidenceGraph G sigma gamma choice.color).connectedComponentMk
              (Sum.inl x) =
            (TwoColorIncidenceGraph G sigma gamma choice.color).connectedComponentMk
              (Sum.inl choice.vertex)
          calc
            _ = (TwoColorIncidenceGraph G sigma gamma choice.color).connectedComponentMk
                (Sum.inr f) := by
              apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              simp [TwoColorIncidenceGraph, hxf, hfc]
            _ = _ := hfComponent
        have hxEq : x = choice.vertex := (hcomponent x hx).mp hxComponent
        have hnot : choice.color ∉ PresentColors G sigma choice.vertex := by
          simpa [MissingColors] using hdeltaSigmaMissing
        apply hnot
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨f, by simpa [hxEq] using hxf, hfc⟩
    have haSigma : sigma a = some delta := (Finset.mem_filter.mp haColor).2
    have hbSigma : sigma b = some delta := (Finset.mem_filter.mp hbColor).2
    have haOutside := targetEdgeOutside a v hvN hva haSigma
    have hbOutside := targetEdgeOutside b w hwN hwb hbSigma
    have haRecoveredValue : recovered a = some delta := by
      simp [recovered, TwoColorComponentSwap, haOutside, haSigma]
    have hbRecoveredValue : recovered b = some delta := by
      simp [recovered, TwoColorComponentSwap, hbOutside, hbSigma]
    have haRecovered : a ∈ BoundaryColorEdges G recovered
        (TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc))
        delta := by
      simp only [BoundaryColorEdges, Finset.mem_filter]
      exact ⟨(Finset.mem_filter.mp haColor).1, haRecoveredValue⟩
    have hbRecovered : b ∈ BoundaryColorEdges G recovered
        (TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc))
        delta := by
      simp only [BoundaryColorEdges, Finset.mem_filter]
      exact ⟨(Finset.mem_filter.mp hbColor).1, hbRecoveredValue⟩
    have boundaryEndpoint : ∀ (x : V) (hx : x ∈
        TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc))
        (f : E) (hf : f ∈ BoundaryColorEdges G sigma
          (TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc)) delta),
        Incident G x f →
        ∃ z, z ∉ TreeSequenceVertexSet
          (ett.series.data.tree terminal.castSucc) ∧ G.ends f = s(x, z) := by
      intro x hx f hf hxf
      have hfBoundary := (Finset.mem_filter.mp hf).1
      rcases (by
        simpa only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
          true_and] using hfBoundary) with ⟨u, hu, z, hz, hends⟩
      have hxEnds : x = u ∨ x = z := by
        change x ∈ G.ends f at hxf
        rw [hends] at hxf
        simpa using hxf
      rcases hxEnds with hxu | hxz
      · exact ⟨z, hz, by simpa [hxu] using hends⟩
      · exact (hz (hxz ▸ hx)).elim
    obtain ⟨za, hzaOutside, haEnds⟩ :=
      boundaryEndpoint v hvN a haColor hva
    obtain ⟨zb, hzbOutside, hbEnds⟩ :=
      boundaryEndpoint w hwN b hbColor hwb
    have hwne : w ≠ v := by
      intro hwvEq
      rcases hwv with ⟨iw, iv, hiw, hiv, hlt⟩
      have hieq : iw = iv := by
        apply (ett.series.data.tree terminal.castSucc).vertex_injective
        exact hiw.trans (hiv.trans hwvEq.symm).symm
      omega
    have hab : a ≠ b := by
      intro habEq
      subst b
      have hwEnds : w = v ∨ w = za := by
        change w ∈ G.ends a at hwb
        rw [haEnds] at hwb
        simpa using hwb
      rcases hwEnds with hwvEq | hwza
      · exact hwne hwvEq
      · exact hzaOutside (hwza ▸ hwN)
    have hdefectiveRecovered : DefectiveColor G recovered
        (TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc))
        delta := by
      unfold DefectiveColor
      have hc : 1 < (BoundaryColorEdges G recovered
          (TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc))
          delta).card := Finset.one_lt_card.mpr
            ⟨a, haRecovered, b, hbRecovered, hab⟩
      omega
    have hvBoundaryRecovered : BoundaryColorVertex G recovered
        (TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc))
        delta v := ⟨hvN, a, haRecovered, hva⟩
    have hwBoundaryRecovered : BoundaryColorVertex G recovered
        (TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc))
        delta w := ⟨hwN, b, hbRecovered, hwb⟩
    by_cases hqTerminal : q.succ = terminal
    · have hchoice : choice.vertex = vi := by
        apply Option.some.inj
        exact currentVertex.symm.trans
          (by simpa [hqTerminal, hpreviousSucc] using hchosen)
      have hvDefective : DefectiveVertex G recovered
          (TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc)) v :=
        ⟨hvN, a, ⟨delta, hdefectiveRecovered, haRecovered⟩, hva⟩
      have hmaximal := choice.maximal recovered v hrecoveredProper
        hrecoveredOne (by simpa [hpreviousSucc] using hrecoveredStable)
        (by simpa [hpreviousSucc] using hvDefective)
      rcases hmaximal with heq | horder
      · exact Or.inl (heq.trans hchoice)
      · apply Or.inr
        have hsegment : TreeSequenceInitialSegment
            (ett.series.data.tree terminal.castSucc) T := by
          rw [htreeTerminal]
          exact ett.abovePenultimate
        exact orderTransfer hsegment v vi
          (by simpa [hpreviousSucc, hchoice] using horder)
    · have hqBefore : q.val + 1 < ett.rounds := by
        have hle : q.val + 1 ≤ ett.rounds := by omega
        have hne : q.val + 1 ≠ ett.rounds := by
          intro heq
          apply hqTerminal
          apply Fin.ext
          simpa [terminal] using heq
        omega
      have appearanceInStage : ∀ (x : V)
          (hxFinal : x ∈ TreeSequenceVertexSet T) (s : ℕ)
          (_hsPositive : 1 ≤ s) (_hsRound : s ≤ ett.rounds),
          ETTFirstAppearanceIndex ett x hxFinal ≤ s →
          x ∈ TreeSequenceVertexSet
            (ett.series.data.tree ⟨s, by omega⟩) := by
        intro x hxFinal s hsPositive hsRound hbound
        unfold ETTFirstAppearanceIndex at hbound
        dsimp at hbound
        let candidates : Finset (Fin (ett.rounds + 1)) :=
          Finset.univ.filter fun i =>
            x ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)
        have hnonempty : candidates.Nonempty := by
          refine ⟨Fin.last ett.rounds, ?_⟩
          simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [show ExtendedTashkinovLadderStage ett
              (Fin.last ett.rounds) = T by
            unfold ExtendedTashkinovLadderStage
            exact Fin.lastCases_last]
          exact hxFinal
        let m := candidates.min' hnonempty
        have hmBound : m.val + 1 ≤ s := by
          dsimp [m, candidates]
          convert hbound using 1
        have hmRounds : m.val < ett.rounds := by omega
        let mi : Fin ett.rounds := ⟨m.val, hmRounds⟩
        have hmEq : m = mi.castSucc := by
          apply Fin.ext
          rfl
        have hmem := Finset.min'_mem candidates hnonempty
        change m ∈ candidates at hmem
        have hxStart : x ∈ TreeSequenceVertexSet
            (ett.series.data.tree ⟨m.val + 1, by omega⟩) := by
          rw [hmEq] at hmem
          have hstage : ExtendedTashkinovLadderStage ett mi.castSucc =
              ett.series.data.tree mi.succ.castSucc := by
            unfold ExtendedTashkinovLadderStage
            exact @Fin.lastCases_castSucc ett.rounds
              (fun _ : Fin (ett.rounds + 1) => TreeSequence G e0) T
              (fun j => ett.series.data.tree j.succ.castSucc) mi
          have hxMi : x ∈ TreeSequenceVertexSet
              (ett.series.data.tree mi.succ.castSucc) := by
            simpa only [candidates, Finset.mem_filter, Finset.mem_univ,
              true_and, hstage] using hmem
          convert hxMi using 1
          apply congrArg TreeSequenceVertexSet
          apply congrArg ett.series.data.tree
          apply Fin.ext
          simp [mi]
        exact TreeSequenceInitialSegmentVertexSetSubset
          (stageToStage (m.val + 1) s (by omega) hmBound hsRound) hxStart
      let r := ett.rounds - 1
      have hrPositive : 1 ≤ r := by
        dsimp [r]
        omega
      have hrBefore : r < ett.rounds := by
        dsimp [r]
        omega
      have hfirstToR : ETTFirstAppearanceIndex ett v hvFinal ≤ r := by
        dsimp [r]
        omega
      have hvR : v ∈ TreeSequenceVertexSet
          (ett.series.data.tree ⟨r, by omega⟩) :=
        appearanceInStage v hvFinal r hrPositive (by dsimp [r]; omega)
          hfirstToR
      have hvAtQ : v ∈ TreeSequenceVertexSet
          (ett.series.data.tree ⟨q.val + 1, by omega⟩) :=
        appearanceInStage v hvFinal (q.val + 1) (by omega) (by omega)
          hfirstBound
      have hRTerminal : TreeSequenceInitialSegment
          (ett.series.data.tree ⟨r, by omega⟩)
          (ett.series.data.tree terminal.castSucc) := by
        rw [htreeTerminal]
        exact stageToStage r ett.rounds hrPositive (by dsimp [r]; omega)
          le_rfl
      have earlierInPrefix : ∀ {A B : TreeSequence G e0} (x y : V),
          TreeSequenceInitialSegment A B →
          y ∈ TreeSequenceVertexSet A →
          TreeVertexOrder B x y →
          x ∈ TreeSequenceVertexSet A ∧ TreeVertexOrder A x y := by
        intro A B x y hAB hyA hxy
        rcases hAB with ⟨hlen, hvertices, _⟩
        rcases Finset.mem_image.mp hyA with ⟨iyA, _, hiyA⟩
        rcases hxy with ⟨ixB, iyB, hixB, hiyB, hlt⟩
        let iyCast := Fin.castLE (Nat.succ_le_succ hlen) iyA
        have hiyEq : iyB = iyCast := by
          apply B.vertex_injective
          exact hiyB.trans ((hvertices iyA).trans hiyA).symm
        have hixBound : ixB.val < A.length + 1 := by
          rw [hiyEq] at hlt
          simp [iyCast] at hlt
          omega
        let ixA : Fin (A.length + 1) := ⟨ixB.val, hixBound⟩
        have hixCast : Fin.castLE (Nat.succ_le_succ hlen) ixA = ixB := by
          apply Fin.ext
          rfl
        have hixA : A.vertex ixA = x := by
          exact (hvertices ixA).symm.trans (by simpa [hixCast] using hixB)
        constructor
        · apply Finset.mem_image.mpr
          exact ⟨ixA, Finset.mem_univ _, hixA⟩
        · refine ⟨ixA, iyA, hixA, hiyA, ?_⟩
          rw [hiyEq] at hlt
          simpa [ixA, iyCast] using hlt
      obtain ⟨hwR, hwvR⟩ := earlierInPrefix w v hRTerminal hvR hwv
      have hzaR : za ∉ TreeSequenceVertexSet
          (ett.series.data.tree ⟨r, by omega⟩) := by
        intro hza
        exact hzaOutside
          (TreeSequenceInitialSegmentVertexSetSubset hRTerminal hza)
      have hzbR : zb ∉ TreeSequenceVertexSet
          (ett.series.data.tree ⟨r, by omega⟩) := by
        intro hzb
        exact hzbOutside
          (TreeSequenceInitialSegmentVertexSetSubset hRTerminal hzb)
      have haR : a ∈ BoundaryColorEdges G recovered
          (TreeSequenceVertexSet (ett.series.data.tree ⟨r, by omega⟩))
          delta := by
        simp only [BoundaryColorEdges, Finset.mem_filter]
        refine ⟨?_, haRecoveredValue⟩
        simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨v, hvR, za, hzaR, haEnds⟩
      have hbR : b ∈ BoundaryColorEdges G recovered
          (TreeSequenceVertexSet (ett.series.data.tree ⟨r, by omega⟩))
          delta := by
        simp only [BoundaryColorEdges, Finset.mem_filter]
        refine ⟨?_, hbRecoveredValue⟩
        simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨w, hwR, zb, hzbR, hbEnds⟩
      have hdefectiveR : DefectiveColor G recovered
          (TreeSequenceVertexSet (ett.series.data.tree ⟨r, by omega⟩))
          delta := by
        unfold DefectiveColor
        have hc : 1 < (BoundaryColorEdges G recovered
            (TreeSequenceVertexSet (ett.series.data.tree ⟨r, by omega⟩))
            delta).card := Finset.one_lt_card.mpr
              ⟨a, haR, b, hbR, hab⟩
        omega
      have hvBoundaryR : BoundaryColorVertex G recovered
          (TreeSequenceVertexSet (ett.series.data.tree ⟨r, by omega⟩))
          delta v := ⟨hvR, a, haR, hva⟩
      have hwBoundaryR : BoundaryColorVertex G recovered
          (TreeSequenceVertexSet (ett.series.data.tree ⟨r, by omega⟩))
          delta w := ⟨hwR, b, hbR, hwb⟩
      obtain ⟨lower, hr, hmaxLower, htree, hdata⟩ :=
        CertifiedETTRestriction G k e0 input T generating ett hMP r
          hrPositive hrBefore
      let nLower : Fin (lower.rounds + 1) := Fin.last lower.rounds
      have hnCast : Fin.castLE (by omega) nLower = previous.castSucc := by
        apply Fin.ext
        simp [nLower, hr, previous, r]
      have hnTreeCast : Fin.castLE (by omega) nLower.castSucc =
          previous.castSucc.castSucc := by
        apply Fin.ext
        simp [nLower, hr, previous, r]
      have hrTree : ett.series.data.tree ⟨r, by omega⟩ =
          ett.series.data.tree previous.castSucc.castSucc := by
        apply congrArg ett.series.data.tree
        apply Fin.ext
        simp [previous, r]
      have hdisplay : ett.series.data.tree ⟨r + 1, by omega⟩ =
          ett.series.data.tree terminal.castSucc := by
        congr 1
        apply Fin.ext
        simp [r, terminal]
        omega
      have hvLower : v ∈ TreeSequenceVertexSet
          (ett.series.data.tree ⟨r + 1, by omega⟩) := by
        rw [hdisplay]
        exact hvN
      rcases hdata nLower with
        ⟨hnColor, hnRawStored, hnEdges, hnKind, hnVertex, hnOutside,
          hnDelta, hnGamma, hnStored, hnCert⟩
      have hnColor' : lower.series.data.coloring nLower =
          ett.series.data.coloring previous.castSucc := by
        rw [hnColor, hnCast]
      have hnStored' : TashkinovStoredColors lower.series.data nLower =
          TashkinovStoredColors ett.series.data previous.castSucc := by
        rw [hnStored, hnCast]
      have hnTree' : lower.series.data.tree nLower.castSucc =
          ett.series.data.tree ⟨r, by omega⟩ := by
        rw [htree nLower.castSucc, hnTreeCast, ← hrTree]
      have hstableR : StableColoring
          (ett.series.data.tree ⟨r, by omega⟩)
          (TashkinovStoredColors ett.series.data previous.castSucc)
          (ett.series.data.coloring previous.castSucc) recovered := by
        constructor
        · intro f hf hcontrol
          apply hrecoveredStable.1 f
          · rcases hf with ⟨x, hx, hxf⟩
            exact ⟨x, TreeSequenceInitialSegmentVertexSetSubset
              hRTerminal hx, hxf⟩
          · rcases hcontrol with ⟨c, hc, hcf⟩
            refine ⟨c, ?_, hcf⟩
            rcases Finset.mem_union.mp hc with hc | hc
            · apply Finset.mem_union.mpr
              left
              simp only [TreeMissingColors, Finset.mem_biUnion] at hc ⊢
              rcases hc with ⟨x, hx, hxc⟩
              exact ⟨x, TreeSequenceInitialSegmentVertexSetSubset
                hRTerminal hx, hxc⟩
            · exact Finset.mem_union.mpr (Or.inr hc)
        · intro x hx
          exact hrecoveredStable.2 x
            (TreeSequenceInitialSegmentVertexSetSubset hRTerminal hx)
      have hstableLower : StableColoring
          (lower.series.data.tree nLower.castSucc)
          (TashkinovStoredColors lower.series.data nLower)
          (lower.series.data.coloring nLower) recovered := by
        rw [hnTree', hnStored', hnColor']
        exact hstableR
      let qLower : Fin lower.rounds := ⟨q.val, by omega⟩
      have hqCast : Fin.castLE (by omega) qLower.succ = q.succ := by
        apply Fin.ext
        rfl
      rcases hdata qLower.succ with
        ⟨_, _, _, hqKind, hqVertex, _, _, _, _, _⟩
      have hkindLower : lower.series.data.kind qLower.succ =
            some TashkinovExtensionKind.PE ∨
          lower.series.data.kind qLower.succ =
            some TashkinovExtensionKind.SE := by
        rw [hqKind, hqCast]
        exact hkind
      have hchosenLower : lower.series.data.chosenVertex qLower.succ =
          some vi := by
        rw [hqVertex, hqCast]
        exact hchosen
      have hfirstLower : ETTFirstAppearanceIndex lower v hvLower ≤
          qLower.val + 1 := by
        unfold ETTFirstAppearanceIndex
        dsimp
        have hqTreeCast : Fin.castLE (by omega) qLower.succ.castSucc =
            (⟨q.val + 1, by omega⟩ : Fin (ett.rounds + 2)) := by
          apply Fin.ext
          rfl
        have hmem : qLower.castSucc ∈
            Finset.univ.filter
              (fun i : Fin (lower.rounds + 1) =>
                v ∈ TreeSequenceVertexSet
                  (ExtendedTashkinovLadderStage lower i)) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [show ExtendedTashkinovLadderStage lower qLower.castSucc =
              lower.series.data.tree qLower.succ.castSucc by
            unfold ExtendedTashkinovLadderStage
            exact @Fin.lastCases_castSucc lower.rounds
              (fun _ : Fin (lower.rounds + 1) => TreeSequence G e0)
              (ett.series.data.tree ⟨r + 1, by omega⟩)
              (fun j => lower.series.data.tree j.succ.castSucc) qLower]
          rw [htree qLower.succ.castSucc, hqTreeCast]
          exact hvAtQ
        have hle := Finset.min'_le
          (Finset.univ.filter
            (fun i : Fin (lower.rounds + 1) =>
              v ∈ TreeSequenceVertexSet
                (ExtendedTashkinovLadderStage lower i))) qLower.castSucc hmem
        have hnat := Fin.le_iff_val_le_val.mp hle
        simpa [qLower] using Nat.succ_le_succ hnat
      have hdefectiveLower : DefectiveColor G recovered
          (TreeSequenceVertexSet (lower.series.data.tree nLower.castSucc))
          delta := by
        rw [hnTree']
        exact hdefectiveR
      have hvBoundaryLower : BoundaryColorVertex G recovered
          (TreeSequenceVertexSet (lower.series.data.tree nLower.castSucc))
          delta v := by
        rw [hnTree']
        exact hvBoundaryR
      have hwBoundaryLower : BoundaryColorVertex G recovered
          (TreeSequenceVertexSet (lower.series.data.tree nLower.castSucc))
          delta w := by
        rw [hnTree']
        exact hwBoundaryR
      have hwvLower : TreeVertexOrder
          (lower.series.data.tree nLower.castSucc) w v := by
        rw [hnTree']
        exact hwvR
      have hlowerFive :=
        (hlower lower (by omega) (by omega) hmaxLower).2.2.2.2.1
      have hresult := hlowerFive recovered hrecoveredProper hrecoveredOne
        hstableLower delta hdefectiveLower v hvBoundaryLower
        ⟨w, hwBoundaryLower, hwvLower⟩ hvLower qLower vi hkindLower
        hchosenLower hfirstLower
      rcases hresult with heq | horder
      · exact Or.inl heq
      · apply Or.inr
        have hdisplayToT : TreeSequenceInitialSegment
            (ett.series.data.tree ⟨r + 1, by omega⟩) T := by
          rw [hdisplay]
          rw [htreeTerminal]
          exact ett.abovePenultimate
        exact orderTransfer hdisplayToT v vi horder
