import Tablet.Basic2
import Tablet.BoundaryEdges
import Tablet.CertifiedETTRestriction
import Tablet.ColoredVertexSetStronglyClosed
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.CorrespondingTerminalClosureEq
import Tablet.DefectiveColor
import Tablet.DefectiveEdge
import Tablet.DefectiveVertex
import Tablet.ExtendedTashkinovTree
import Tablet.ExtensionBase
import Tablet.ExtensionRules
import Tablet.HkuMissingStoredMonotone
import Tablet.HkuTreeColorsControlled
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumProperty
import Tablet.MaximumPropertyTransport
import Tablet.MissingColors
import Tablet.ModColoring
import Tablet.ParallelExtensionColor
import Tablet.ParallelExtensionUndoStable
import Tablet.PresentColors
import Tablet.RevisitingExtensionCertificate
import Tablet.StableColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TashkinovClosureExists
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TechnicalTheoremBase
import Tablet.TreeExit
import Tablet.TreeExitPath
import Tablet.TreeIncidentEdge
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorCycle
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorPathComponent
import Tablet.TwoColorNontrivialPathComponent
import Tablet.sc1
import Tablet.sc2

set_option maxHeartbeats 800000

-- [TABLET NODE: TdReplacementPrefixExact]
theorem TdReplacementPrefixExact {V E : Type*} [Fintype V] [Fintype E]
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
           ModColoring lower sigma)) :    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let p : Fin (ett.rounds + 1) := ⟨ett.rounds - 1, by omega⟩
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
    ∀ sigma : PartialEdgeColoring E k,
      IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
      StableColoring Tn
        (TashkinovStoredColors ett.series.data n)
        (ett.series.data.coloring n) sigma →
      ∃ sigmaPrev : PartialEdgeColoring E k,
        IsProperEdgeColoring G sigmaPrev ∧
        IsOneEdgeUncolored sigmaPrev e0 ∧
        StableColoring Tn
          (TashkinovStoredColors ett.series.data p)
          (ett.series.data.coloring p) sigmaPrev ∧
        ((ett.series.data.kind n = some TashkinovExtensionKind.SE ∨
            ett.series.data.kind n = some TashkinovExtensionKind.RE) →
          sigmaPrev = sigma) ∧
        (ett.series.data.kind n = some TashkinovExtensionKind.PE →
          ∃ (v : V) (gamma delta : Fin k),
            ett.series.data.chosenVertex n = some v ∧
            ett.series.data.gamma n = some gamma ∧
            ett.series.data.delta n = some delta ∧
            sigmaPrev =
              TwoColorComponentSwap G sigma gamma delta (Sum.inl v)) ∧
        ((ett.rounds = 1 ∧
            ∃ (prefixInput : PartialEdgeColoring E k)
              (zeroPrefix : TashkinovSeries G k 0 e0 prefixInput),
              zeroPrefix.data.tree (Fin.last 1) = Tn ∧
              zeroPrefix.data.coloring (Fin.last 0) = sigmaPrev) ∨
          (1 < ett.rounds ∧
            ∃ originalPrefix : ExtendedTashkinovTree G k e0 input Tn
                (ett.series.data.coloring p),
              ∃ hr : originalPrefix.rounds = ett.rounds - 1,
                MaximumProperty originalPrefix ∧
                (∀ i : Fin (originalPrefix.rounds + 2),
                  originalPrefix.series.data.tree i =
                    ett.series.data.tree (Fin.castLE (by omega) i)) ∧
                (∀ i : Fin (originalPrefix.rounds + 1),
                  originalPrefix.series.data.coloring i =
                      ett.series.data.coloring (Fin.castLE (by omega) i) ∧
                  originalPrefix.series.data.stored i =
                      ett.series.data.stored (Fin.castLE (by omega) i) ∧
                  originalPrefix.series.data.connectingEdges i =
                      ett.series.data.connectingEdges
                        (Fin.castLE (by omega) i) ∧
                  originalPrefix.series.data.kind i =
                      ett.series.data.kind (Fin.castLE (by omega) i) ∧
                  TashkinovStoredColors originalPrefix.series.data i =
                    TashkinovStoredColors ett.series.data
                      (Fin.castLE (by omega) i)) ∧
                ∃ corr : CorrespondingExtendedTashkinovTree G k e0
                    originalPrefix sigmaPrev Tn,
                  corr.replacementSeries.data.tree
                      (Fin.last (originalPrefix.rounds + 1)) = Tn ∧
                    corr.replacementSeries.data.coloring
                      (Fin.last originalPrefix.rounds) = sigmaPrev ∧
                    MaximumProperty corr.replacementETT)) := by
-- BODY
  classical
  dsimp
  intro sigma hsigmaProper hsigmaOne hsigmaStable
  let q : Fin ett.rounds :=
    ⟨ett.rounds - 1,
      Nat.sub_lt (Nat.zero_lt_of_lt hpositive) (by omega)⟩
  have hqSucc : q.succ = Fin.last ett.rounds := by
    apply Fin.ext
    simp [q]
    omega
  have hqCast : q.castSucc =
      (⟨ett.rounds - 1, by omega⟩ : Fin (ett.rounds + 1)) := by
    apply Fin.ext
    rfl
  have hsigmaStableQ : StableColoring
      (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.succ)
      (ett.series.data.coloring q.succ) sigma := by
    simpa [hqSucc] using hsigmaStable
  have hpredecessor : ∃ sigmaPrev : PartialEdgeColoring E k,
      IsProperEdgeColoring G sigmaPrev ∧
      IsOneEdgeUncolored sigmaPrev e0 ∧
      StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc) sigmaPrev ∧
      ((ett.series.data.kind q.succ = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind q.succ = some TashkinovExtensionKind.RE) →
        sigmaPrev = sigma) ∧
      (ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
        ∃ (v : V) (gamma delta : Fin k),
          ett.series.data.chosenVertex q.succ = some v ∧
          ett.series.data.gamma q.succ = some gamma ∧
          ett.series.data.delta q.succ = some delta ∧
          sigmaPrev =
            TwoColorComponentSwap G sigma gamma delta (Sum.inl v)) := by
    have hstep := ett.series.certified q.succ
    generalize htarget : q.succ = target at hstep
    cases hstep with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
      exact (Fin.succ_ne_zero q htarget).elim
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      have hi : i = q := by
        apply Fin.ext
        have hv := congrArg Fin.val htarget
        simp at hv
        omega
      subst i
      have hstablePrev : StableColoring
          (ett.series.data.tree q.succ.castSucc)
          (TashkinovStoredColors ett.series.data q.castSucc)
          (ett.series.data.coloring q.castSucc) sigma := by
        constructor
        · intro f hf hcolor
          rcases hcolor with ⟨c, hc, hfc⟩
          have hc' :=
            (HkuMissingStoredMonotone G k ett.rounds e0 input
              ett.series q).1 hc
          have hcopy := hsigmaStableQ.1 f hf
            ⟨c, by simpa [currentColoring] using hc', by
              simpa [currentColoring] using hfc⟩
          simpa [currentColoring] using hcopy
        · intro v hv
          simpa [currentColoring] using hsigmaStableQ.2 v hv
      refine ⟨sigma, hsigmaProper, hsigmaOne, hstablePrev, ?_, ?_⟩
      · intro hkind
        rfl
      · intro hkind
        rw [currentKind] at hkind
        cases hkind
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      have hi : i = q := by
        apply Fin.ext
        have hv := congrArg Fin.val htarget
        simp at hv
        omega
      subst i
      have hselectedSigma : StableColoring
          (ett.series.data.tree q.succ.castSucc)
          (TashkinovStoredColors ett.series.data q.castSucc)
          choice.selected sigma := by
        constructor
        · intro f hf hcolor
          rcases hcolor with ⟨c, hc, hfc⟩
          have hc' : c ∈
              TreeMissingColors (ett.series.data.coloring q.succ)
                  (ett.series.data.tree q.succ.castSucc) ∪
                TashkinovStoredColors ett.series.data q.succ := by
            rcases Finset.mem_union.mp hc with hc | hc
            · exact Finset.mem_union_left _ (by
                simpa [currentColoring] using hc)
            · have hc'' :=
                (HkuMissingStoredMonotone G k ett.rounds e0 input
                  ett.series q).1
                  (Finset.mem_union_right _ hc)
              simpa [currentColoring] using hc''
          have hcopy := hsigmaStableQ.1 f hf
            ⟨c, hc', by simpa [currentColoring] using hfc⟩
          simpa [currentColoring] using hcopy
        · intro v hv
          simpa [currentColoring] using hsigmaStableQ.2 v hv
      have hstablePrev : StableColoring
          (ett.series.data.tree q.succ.castSucc)
          (TashkinovStoredColors ett.series.data q.castSucc)
          (ett.series.data.coloring q.castSucc) sigma := by
        exact (sc2 G e0 (ett.series.data.tree q.succ.castSucc)
          (TashkinovStoredColors ett.series.data q.castSucc)).trans
          (x := ⟨ett.series.data.coloring q.castSucc,
            ⟨previousProper, previousOneUncolored⟩⟩)
          (y := ⟨choice.selected,
            ⟨choice.selectedProper, choice.selectedOneUncolored⟩⟩)
          (z := ⟨sigma, ⟨hsigmaProper, hsigmaOne⟩⟩)
          choice.selectedStable hselectedSigma
      refine ⟨sigma, hsigmaProper, hsigmaOne, hstablePrev, ?_, ?_⟩
      · intro hkind
        rfl
      · intro hkind
        rw [currentKind] at hkind
        cases hkind
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
      have hi : i = q := by
        apply Fin.ext
        have hv := congrArg Fin.val htarget
        simp at hv
        omega
      subst i
      have hcomponent := ExtensionBase G k e0 input T generating ett hMP
        hpositive hlower choice.vertex gamma choice.color
        (by simpa [hqSucc] using currentKind)
        (by simpa [hqSucc] using currentVertex)
        (by simpa [hqSucc] using currentGamma)
        (by simpa [hqSucc] using currentDelta) sigma hsigmaProper
        hsigmaOne (by simpa [hqSucc] using hsigmaStableQ)
      obtain ⟨selected, secondStable', hselectedProper, hselectedOne,
          hselectedStable, hsecondProper, hsecondOne, hsecondStable,
          hcurrent, hundoneSecond, hundoneSelected, hundonePrev⟩ :=
        ParallelExtensionUndoStable G k ett.rounds e0 input ett.series q
          choice.vertex gamma choice.color currentKind currentVertex
          currentGamma currentDelta sigma hsigmaProper hsigmaOne
          hsigmaStableQ choice.vertexDefective.1
          (by simpa [hqSucc] using hcomponent)
      let sigmaPrev :=
        TwoColorComponentSwap G sigma gamma choice.color
          (Sum.inl choice.vertex)
      have hne : gamma ≠ choice.color := by
        intro heq
        have hpresent : gamma ∈ PresentColors G choice.selected choice.vertex := by
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact ⟨choice.edge, choice.edgeIncident, by simpa [heq] using
            choice.edgeColor⟩
        have hnot : gamma ∉ PresentColors G choice.selected choice.vertex := by
          simpa [MissingColors] using gammaRule.1
        exact hnot hpresent
      refine ⟨sigmaPrev, ?_, ?_, ?_, ?_, ?_⟩
      · exact TwoColorComponentSwapProper G sigma gamma choice.color hne
          hsigmaProper (Sum.inl choice.vertex)
      · unfold IsOneEdgeUncolored
        constructor
        · by_cases he : Sum.inr e0 ∈
              TwoColorComponent G sigma gamma choice.color
                (Sum.inl choice.vertex)
          · simp [sigmaPrev, TwoColorComponentSwap, he, hsigmaOne.1]
          · simp [sigmaPrev, TwoColorComponentSwap, he, hsigmaOne.1]
        · intro e he0
          obtain ⟨c, hc⟩ := hsigmaOne.2 e he0
          by_cases he : Sum.inr e ∈
              TwoColorComponent G sigma gamma choice.color
                (Sum.inl choice.vertex)
          · by_cases hcg : c = gamma
            · exact ⟨choice.color, by
                simp [sigmaPrev, TwoColorComponentSwap, he, hc, hcg]⟩
            · by_cases hcd : c = choice.color
              · exact ⟨gamma, by
                  simp [sigmaPrev, TwoColorComponentSwap, he, hc, hcd,
                    hne, hne.symm]⟩
              · exact ⟨c, by
                  simp [sigmaPrev, TwoColorComponentSwap, he, hc, hcg, hcd]⟩
          · exact ⟨c, by
              simp [sigmaPrev, TwoColorComponentSwap, he, hc]⟩
      · exact hundonePrev
      · intro hkind
        rcases hkind with hkind | hkind <;> rw [currentKind] at hkind <;>
          cases hkind
      · intro hkind
        exact ⟨choice.vertex, gamma, choice.color, currentVertex,
          currentGamma, currentDelta, rfl⟩
  obtain ⟨sigmaPrev, hsigmaPrevProper, hsigmaPrevOne, hsigmaPrevStable,
    hsigmaPrevNonPE, hsigmaPrevPE⟩ := hpredecessor
  have vertexSegment {A B : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B) {v : V}
      (hv : v ∈ TreeSequenceVertexSet A) :
      v ∈ TreeSequenceVertexSet B := by
    simp only [TreeSequenceVertexSet, Finset.mem_image] at hv ⊢
    rcases hv with ⟨i, hi, rfl⟩
    rcases hAB with ⟨hlen, hvertices, hedges⟩
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i,
      Finset.mem_univ _, hvertices i⟩
  have vertexReach {A B : TreeSequence G e0}
      {phi : PartialEdgeColoring E k}
      (hAB : TashkinovAugmentationSequence phi A B) {v : V}
      (hv : v ∈ TreeSequenceVertexSet A) :
      v ∈ TreeSequenceVertexSet B := by
    unfold TashkinovAugmentationSequence at hAB
    induction hAB using Relation.ReflTransGen.head_induction_on with
    | refl => exact hv
    | @head A B hstep htail ih =>
      exact ih (vertexSegment hstep.2.1 hv)
  have displayedEdgeIncident {A : TreeSequence G e0}
      (j : Fin A.length) : TreeIncidentEdge A (A.edge j) := by
    rcases A.attaches j with ⟨i, hi⟩
    refine ⟨A.vertex j.succ, ?_, ?_⟩
    · simp [TreeSequenceVertexSet]
    · change A.vertex j.succ ∈ G.ends (A.edge j)
      rw [hi]
      exact Sym2.mem_mk_left _ _
  have hreferenceGood :
      IsProperEdgeColoring G (ett.series.data.coloring q.castSucc) ∧
      IsOneEdgeUncolored (ett.series.data.coloring q.castSucc) e0 := by
    have hstep := ett.series.certified q.succ
    generalize htarget : q.succ = target at hstep
    cases hstep with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
      exact (Fin.succ_ne_zero q htarget).elim
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      have hi : i = q := by
        apply Fin.ext
        have hv := congrArg Fin.val htarget
        simp at hv
        omega
      subst i
      exact ⟨previousProper, previousOneUncolored⟩
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
      have hi : i = q := by
        apply Fin.ext
        have hv := congrArg Fin.val htarget
        simp at hv
        omega
      subst i
      exact ⟨previousProper, previousOneUncolored⟩
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      have hi : i = q := by
        apply Fin.ext
        have hv := congrArg Fin.val htarget
        simp at hv
        omega
      subst i
      exact ⟨previousProper, previousOneUncolored⟩
  have copyClosure {seed : TreeSequence G e0}
      (hclosure : TashkinovClosure
        (ett.series.data.coloring q.castSucc) seed
        (ett.series.data.tree q.succ.castSucc)) :
      TashkinovClosure sigmaPrev seed
        (ett.series.data.tree q.succ.castSucc) := by
    have hseq : TashkinovAugmentationSequence sigmaPrev seed
        (ett.series.data.tree q.succ.castSucc) := by
      have transport : ∀ {A : TreeSequence G e0},
          Relation.ReflTransGen
              (TashkinovAugmentation
                (ett.series.data.coloring q.castSucc)) A
              (ett.series.data.tree q.succ.castSucc) →
            Relation.ReflTransGen (TashkinovAugmentation sigmaPrev) A
              (ett.series.data.tree q.succ.castSucc) := by
        intro A holdSeq
        induction holdSeq using Relation.ReflTransGen.head_induction_on with
        | refl => exact Relation.ReflTransGen.refl
        | @head A B hstep htail ih =>
          refine Relation.ReflTransGen.head ?_ ih
          rcases hstep with ⟨hlen, hsegment, c, hcolor, hmissing⟩
          refine ⟨hlen, hsegment, c, ?_, ?_⟩
          · let last : Fin B.length :=
              Fin.cast hlen.symm (Fin.last A.length)
            have hincB := displayedEdgeIncident last
            have hincFinal : TreeIncidentEdge
                (ett.series.data.tree q.succ.castSucc) (B.edge last) := by
              rcases hincB with ⟨v, hv, hve⟩
              exact ⟨v, vertexReach htail hv, hve⟩
            have hcFinal : c ∈ TreeMissingColors
                (ett.series.data.coloring q.castSucc)
                (ett.series.data.tree q.succ.castSucc) := by
              simp only [TreeMissingColors, Finset.mem_biUnion] at hmissing ⊢
              rcases hmissing with ⟨v, hv, hvc⟩
              exact ⟨v, vertexReach htail (vertexSegment hsegment hv), hvc⟩
            have hcopy := hsigmaPrevStable.1 (B.edge last) hincFinal
              ⟨c, Finset.mem_union_left _ hcFinal, hcolor⟩
            exact hcopy.trans hcolor
          · simp only [TreeMissingColors, Finset.mem_biUnion] at hmissing ⊢
            rcases hmissing with ⟨v, hv, hvc⟩
            refine ⟨v, hv, ?_⟩
            rw [hsigmaPrevStable.2 v
              (vertexReach htail (vertexSegment hsegment hv))]
            exact hvc
      exact transport hclosure.1
    refine ⟨hseq, ?_⟩
    intro f c v hf hv hfc
    intro hmissing
    have hinc : TreeIncidentEdge
        (ett.series.data.tree q.succ.castSucc) f := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] at hf
      rcases hf with ⟨u, hu, w, hw, he⟩
      refine ⟨u, hu, ?_⟩
      change u ∈ G.ends f
      rw [he]
      exact Sym2.mem_mk_left _ _
    have hmissingOld : c ∈ MissingColors G
        (ett.series.data.coloring q.castSucc) v := by
      rw [← hsigmaPrevStable.2 v hv]
      exact hmissing
    have htreeMissingOld : c ∈ TreeMissingColors
        (ett.series.data.coloring q.castSucc)
        (ett.series.data.tree q.succ.castSucc) := by
      simp only [TreeMissingColors, Finset.mem_biUnion]
      exact ⟨v, hv, hmissingOld⟩
    have hedgeCriterion :=
      (sc1 G e0 (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.castSucc)
        (ett.series.data.coloring q.castSucc) sigmaPrev
        hreferenceGood.1 hreferenceGood.2 hsigmaPrevProper
        hsigmaPrevOne).mp hsigmaPrevStable
    have hedgeEq := hedgeCriterion f hinc (Or.inr
      ⟨c, Finset.mem_union_left _ htreeMissingOld, hfc⟩)
    have hfcOld : ett.series.data.coloring q.castSucc f = some c :=
      hedgeEq.symm.trans hfc
    exact (hclosure.2 hf hv hfcOld) hmissingOld
  refine ⟨sigmaPrev, hsigmaPrevProper, hsigmaPrevOne, ?_, ?_, ?_, ?_⟩
  · simpa [hqSucc, hqCast] using hsigmaPrevStable
  · simpa [hqSucc] using hsigmaPrevNonPE
  · simpa [hqSucc] using hsigmaPrevPE
  · by_cases hroundOne : ett.rounds = 1
    · left
      refine ⟨hroundOne, ?_⟩
      have hqZero : q.castSucc = (0 : Fin (ett.rounds + 1)) := by
        apply Fin.ext
        simp [q, hroundOne]
      have hqTree : q.succ.castSucc =
          (1 : Fin (ett.rounds + 2)) := by
        apply Fin.ext
        simp [q, hroundOne]
      have hinitial := ett.series.certified (0 : Fin (ett.rounds + 1))
      generalize htarget : (0 : Fin (ett.rounds + 1)) = target at hinitial
      cases hinitial with
      | initial triple seedLength initialColoring initialStored initialEdges
          initialKind initialVertex initialOutside initialDelta initialGamma
          initialClosure =>
        let zeroData : TashkinovSeriesData G k 0 e0 :=
          { tree := fun i =>
              ett.series.data.tree ⟨i.val, by omega⟩
            coloring := fun _ => sigmaPrev
            stored := fun _ => ∅
            connectingEdges := fun _ => ∅
            kind := fun _ => none
            chosenVertex := fun _ => none
            outsideVertex := fun _ => none
            delta := fun _ => none
            gamma := fun _ => none }
        have htriplePrev : KTriple G k e0 sigmaPrev :=
          ⟨triple.1, triple.2.1, triple.2.2.1,
            hsigmaPrevProper, hsigmaPrevOne⟩
        have hclosurePrev : TashkinovClosure sigmaPrev
            (zeroData.tree 0) (zeroData.tree 1) := by
          have hcopy := copyClosure (seed := ett.series.data.tree 0)
            (by simpa [hqZero, hqTree] using initialClosure)
          simpa [zeroData, hqTree] using hcopy
        let zeroPrefix : TashkinovSeries G k 0 e0 sigmaPrev :=
          { data := zeroData
            certified := by
              intro i
              have hi : i = 0 := Fin.eq_zero i
              subst i
              exact TashkinovSeriesStep.initial htriplePrev
                (by simpa [zeroData] using seedLength) rfl rfl rfl rfl
                rfl rfl rfl rfl hclosurePrev }
        refine ⟨sigmaPrev, zeroPrefix, ?_, ?_⟩
        · change ett.series.data.tree 1 =
            ett.series.data.tree (Fin.last ett.rounds).castSucc
          congr 1
          apply Fin.ext
          simp [hroundOne]
        · rfl
      | SE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting choice seriesAlternative
          currentColoring currentStored currentEdges currentKind currentVertex
          currentOutside currentDelta currentGamma adjoined adjoinedExactly
          closedExtension orderedExtension strictExtension =>
        exact (Fin.succ_ne_zero i htarget.symm).elim
      | PE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
          gamma gammaRule secondStable secondStableProper
          secondStableOneUncolored secondStableRelation exitWitness
          currentColoring currentProper currentOneUncolored currentStored
          currentEdges currentKind currentVertex currentOutside currentDelta
          currentGamma closedExtension orderedExtension strictExtension =>
        exact (Fin.succ_ne_zero i htarget.symm).elim
      | RE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed available currentColoring currentStored
          currentEdges currentKind currentVertex currentOutside currentDelta
          currentGamma adjoined adjoinedExactly closedExtension orderedExtension
          strictExtension =>
        exact (Fin.succ_ne_zero i htarget.symm).elim
    · right
      have hroundLarge : 1 < ett.rounds := by omega
      refine ⟨hroundLarge, ?_⟩
      have hroundSub : ett.rounds - 1 + 1 = ett.rounds := by omega
      obtain ⟨originalPrefix, hr, hprefixMP, hprefixTrees,
          hprefixData⟩ := (by
        simpa only [hroundSub] using
          (CertifiedETTRestriction G k e0 input T generating ett hMP
            (ett.rounds - 1) (by omega) (by omega)))
      have hfinalTree : ett.series.data.tree
          ⟨ett.rounds - 1 + 1, by omega⟩ =
          ett.series.data.tree (Fin.last ett.rounds).castSucc := by
        congr 1
        apply Fin.ext
        simp
        omega
      let originalPrefix' : ExtendedTashkinovTree G k e0 input
          (ett.series.data.tree (Fin.last ett.rounds).castSucc)
          (ett.series.data.coloring ⟨ett.rounds - 1, by omega⟩) :=
        { rounds := originalPrefix.rounds
          roundsPositive := originalPrefix.roundsPositive
          series := originalPrefix.series
          abovePenultimate := by
            simpa only [hfinalTree] using originalPrefix.abovePenultimate
          strictAbovePenultimate := by
            simpa only [hfinalTree] using originalPrefix.strictAbovePenultimate
          belowFinal := by
            simpa only [hfinalTree] using originalPrefix.belowFinal
          generatingColoring := originalPrefix.generatingColoring }
      have hr' : originalPrefix'.rounds = ett.rounds - 1 := hr
      have hprefixMP' : MaximumProperty originalPrefix' := hprefixMP
      have hprefixTrees' : ∀ i : Fin (originalPrefix'.rounds + 2),
          originalPrefix'.series.data.tree i =
            ett.series.data.tree (Fin.castLE (by omega) i) := hprefixTrees
      have hprefixData' : ∀ i : Fin (originalPrefix'.rounds + 1),
          originalPrefix'.series.data.coloring i =
              ett.series.data.coloring (Fin.castLE (by omega) i) ∧
          originalPrefix'.series.data.stored i =
              ett.series.data.stored (Fin.castLE (by omega) i) ∧
          originalPrefix'.series.data.connectingEdges i =
              ett.series.data.connectingEdges (Fin.castLE (by omega) i) ∧
          originalPrefix'.series.data.kind i =
              ett.series.data.kind (Fin.castLE (by omega) i) ∧
          originalPrefix'.series.data.chosenVertex i =
              ett.series.data.chosenVertex (Fin.castLE (by omega) i) ∧
          originalPrefix'.series.data.outsideVertex i =
              ett.series.data.outsideVertex (Fin.castLE (by omega) i) ∧
          originalPrefix'.series.data.delta i =
              ett.series.data.delta (Fin.castLE (by omega) i) ∧
          originalPrefix'.series.data.gamma i =
              ett.series.data.gamma (Fin.castLE (by omega) i) ∧
          TashkinovStoredColors originalPrefix'.series.data i =
              TashkinovStoredColors ett.series.data
                (Fin.castLE (by omega) i) ∧
          HEq (originalPrefix'.series.certified i)
            (ett.series.certified (Fin.castLE (by omega) i)) := hprefixData
      refine ⟨originalPrefix', hr', hprefixMP', hprefixTrees', ?_, ?_⟩
      · intro i
        rcases hprefixData' i with
          ⟨hc, hs, he, hk, hv, ho, hd, hg, hD, hcert⟩
        exact ⟨hc, hs, he, hk, hD⟩
      · let rLast : Fin (originalPrefix'.rounds + 1) :=
          Fin.last originalPrefix'.rounds
        have hlastMap : Fin.castLE (by omega) rLast = q.castSucc := by
          apply Fin.ext
          simp [rLast, q, hr']
        have hlastColor : originalPrefix'.series.data.coloring rLast =
            ett.series.data.coloring q.castSucc := by
          simpa [hlastMap] using (hprefixData' rLast).1
        have hlastStored :
            TashkinovStoredColors originalPrefix'.series.data rLast =
              TashkinovStoredColors ett.series.data q.castSucc := by
          simpa [hlastMap] using (hprefixData' rLast).2.2.2.2.2.2.2.2.1
        have hterminalTree :
            ett.series.data.tree (Fin.last ett.rounds).castSucc =
              ett.series.data.tree q.succ.castSucc := by
          rw [hqSucc]
        have incidentSegment {A B : TreeSequence G e0}
            (hAB : TreeSequenceInitialSegment A B) {f : E}
            (hf : TreeIncidentEdge A f) : TreeIncidentEdge B f := by
          rcases hf with ⟨v, hv, hve⟩
          exact ⟨v, vertexSegment hAB hv, hve⟩
        have missingSegment {A B : TreeSequence G e0}
            (hAB : TreeSequenceInitialSegment A B)
            {phi : PartialEdgeColoring E k} :
            TreeMissingColors phi A ⊆ TreeMissingColors phi B := by
          intro c hc
          simp only [TreeMissingColors, Finset.mem_biUnion] at hc ⊢
          rcases hc with ⟨v, hv, hvc⟩
          exact ⟨v, vertexSegment hAB hv, hvc⟩
        have hstableRestricted : StableColoring
            (originalPrefix'.series.data.tree rLast.castSucc)
            (TashkinovStoredColors originalPrefix'.series.data rLast)
            (originalPrefix'.series.data.coloring rLast) sigmaPrev := by
          constructor
          · intro f hf hcolor
            have hfFull : TreeIncidentEdge
                (ett.series.data.tree q.succ.castSucc) f := by
              simpa only [hterminalTree] using
                (incidentSegment originalPrefix'.abovePenultimate hf)
            rcases hcolor with ⟨c, hc, hfc⟩
            have hcFull : c ∈
                TreeMissingColors (ett.series.data.coloring q.castSucc)
                    (ett.series.data.tree q.succ.castSucc) ∪
                  TashkinovStoredColors ett.series.data q.castSucc := by
              rcases Finset.mem_union.mp hc with hc | hc
              · apply Finset.mem_union_left
                have hc' : c ∈ TreeMissingColors
                    (ett.series.data.coloring q.castSucc)
                    (originalPrefix'.series.data.tree rLast.castSucc) := by
                  simpa [hlastColor] using hc
                simpa only [hterminalTree] using
                  (missingSegment originalPrefix'.abovePenultimate hc')
              · apply Finset.mem_union_right
                simpa [hlastStored] using hc
            have hcopy := hsigmaPrevStable.1 f hfFull
              ⟨c, hcFull, by simpa [hlastColor] using hfc⟩
            simpa [hlastColor] using hcopy
          · intro v hv
            have hvFull : v ∈ TreeSequenceVertexSet
                (ett.series.data.tree q.succ.castSucc) := by
              simpa only [hterminalTree] using
                (vertexSegment originalPrefix'.abovePenultimate hv)
            have hcopy := hsigmaPrevStable.2 v hvFull
            simpa [hlastColor] using hcopy
        have hlowerPrefix := hlower originalPrefix'
          (by rw [hr']; omega) (by rw [hr']; omega) hprefixMP'
        have hmod : ModColoring originalPrefix' sigmaPrev := by
          exact hlowerPrefix.2.2.2.2.2 sigmaPrev hsigmaPrevProper
            hsigmaPrevOne hstableRestricted
        have hlastTreeMap : Fin.castLE (by omega) rLast.castSucc =
            q.castSucc.castSucc := by
          apply Fin.ext
          simp [rLast, q, hr']
        have hlastTree :
            originalPrefix'.series.data.tree rLast.castSucc =
              ett.series.data.tree q.castSucc.castSucc := by
          simpa [hlastTreeMap] using hprefixTrees' rLast.castSucc
        have hlastEdges :
            originalPrefix'.series.data.connectingEdges rLast =
              ett.series.data.connectingEdges q.castSucc := by
          simpa [hlastMap] using (hprefixData' rLast).2.2.1
        have hlastKind : originalPrefix'.series.data.kind rLast =
            ett.series.data.kind q.castSucc := by
          simpa [hlastMap] using (hprefixData' rLast).2.2.2.1
        have hseedPackage : ∃ seed : TreeSequence G e0,
            (((originalPrefix'.series.data.kind rLast =
                  some TashkinovExtensionKind.PE ∧
                seed = originalPrefix'.series.data.tree rLast.castSucc) ∨
              ((originalPrefix'.series.data.kind rLast =
                    some TashkinovExtensionKind.SE ∨
                  originalPrefix'.series.data.kind rLast =
                    some TashkinovExtensionKind.RE) ∧
                ∃ f : E,
                  originalPrefix'.series.data.connectingEdges rLast = {f} ∧
                  TreeSequenceAdjoinEdge
                    (originalPrefix'.series.data.tree rLast.castSucc)
                    f seed)) ∧
            TashkinovClosure sigmaPrev seed
              (ett.series.data.tree q.succ.castSucc)) := by
          have hstep := ett.series.certified q.castSucc
          generalize htarget : q.castSucc = target at hstep
          cases hstep with
          | initial triple seedLength initialColoring initialStored initialEdges
              initialKind initialVertex initialOutside initialDelta initialGamma
              initialClosure =>
            have hv := congrArg Fin.val htarget
            simp [q] at hv
            omega
          | SE i previousProper previousOneUncolored previousClosed
              previousNotStronglyClosed noRevisiting choice seriesAlternative
              currentColoring currentStored currentEdges currentKind currentVertex
              currentOutside currentDelta currentGamma adjoined adjoinedExactly
              closedExtension orderedExtension strictExtension =>
            have hnext : i.succ.succ = q.succ.castSucc := by
              apply Fin.ext
              have hv := congrArg Fin.val htarget
              simp at hv ⊢
              omega
            have hclosureOld : TashkinovClosure
                (ett.series.data.coloring q.castSucc) adjoined
                (ett.series.data.tree q.succ.castSucc) := by
              simpa only [htarget, hnext] using closedExtension
            refine ⟨adjoined, ?_, copyClosure hclosureOld⟩
            right
            constructor
            · left
              exact hlastKind.trans (by simpa only [htarget] using currentKind)
            · refine ⟨choice.edge, ?_, ?_⟩
              · exact hlastEdges.trans
                  (by simpa only [htarget] using currentEdges)
              · simpa only [hlastTree, htarget] using adjoinedExactly
          | PE i previousProper previousOneUncolored previousClosed
              previousNotStronglyClosed noRevisiting choice
              seriesAlternativeFails gamma gammaRule secondStable
              secondStableProper secondStableOneUncolored secondStableRelation
              exitWitness currentColoring currentProper currentOneUncolored
              currentStored currentEdges currentKind currentVertex currentOutside
              currentDelta currentGamma closedExtension orderedExtension
              strictExtension =>
            have hnext : i.succ.succ = q.succ.castSucc := by
              apply Fin.ext
              have hv := congrArg Fin.val htarget
              simp at hv ⊢
              omega
            have hclosureOld : TashkinovClosure
                (ett.series.data.coloring q.castSucc)
                (ett.series.data.tree q.castSucc.castSucc)
                (ett.series.data.tree q.succ.castSucc) := by
              simpa only [htarget, hnext] using closedExtension
            refine ⟨ett.series.data.tree q.castSucc.castSucc, ?_,
              copyClosure hclosureOld⟩
            left
            refine ⟨hlastKind.trans
              (by simpa only [htarget] using currentKind), ?_⟩
            exact hlastTree.symm
          | RE i previousProper previousOneUncolored previousClosed
              previousNotStronglyClosed available currentColoring currentStored
              currentEdges currentKind currentVertex currentOutside currentDelta
              currentGamma adjoined adjoinedExactly closedExtension
              orderedExtension strictExtension =>
            have hnext : i.succ.succ = q.succ.castSucc := by
              apply Fin.ext
              have hv := congrArg Fin.val htarget
              simp at hv ⊢
              omega
            have hclosureOld : TashkinovClosure
                (ett.series.data.coloring q.castSucc) adjoined
                (ett.series.data.tree q.succ.castSucc) := by
              simpa only [htarget, hnext] using closedExtension
            refine ⟨adjoined, ?_, copyClosure hclosureOld⟩
            right
            constructor
            · right
              exact hlastKind.trans (by simpa only [htarget] using currentKind)
            · refine ⟨available.edge, ?_, ?_⟩
              · exact hlastEdges.trans
                  (by simpa only [htarget] using currentEdges)
              · simpa only [hlastTree, htarget] using adjoinedExactly
        rcases hseedPackage with ⟨seed, hseedRoute, hclosureQ⟩
        have hclosureFinal : TashkinovClosure sigmaPrev seed
            (ett.series.data.tree (Fin.last ett.rounds).castSucc) := by
          simpa only [hterminalTree] using hclosureQ
        have heligible :
            ((originalPrefix'.series.data.kind rLast =
                  some TashkinovExtensionKind.PE ∧
                TashkinovAugmentationSequence sigmaPrev
                  (originalPrefix'.series.data.tree rLast.castSucc)
                  (ett.series.data.tree (Fin.last ett.rounds).castSucc)) ∨
              ((originalPrefix'.series.data.kind rLast =
                    some TashkinovExtensionKind.SE ∨
                  originalPrefix'.series.data.kind rLast =
                    some TashkinovExtensionKind.RE) ∧
                ∃ (f : E) (seed' : TreeSequence G e0),
                  originalPrefix'.series.data.connectingEdges rLast = {f} ∧
                  TreeSequenceAdjoinEdge
                    (originalPrefix'.series.data.tree rLast.castSucc) f seed' ∧
                  TashkinovAugmentationSequence sigmaPrev seed'
                    (ett.series.data.tree
                      (Fin.last ett.rounds).castSucc))) := by
          rcases hseedRoute with hPE | hSER
          · left
            refine ⟨hPE.1, ?_⟩
            rw [← hPE.2]
            exact hclosureFinal.1
          · right
            rcases hSER with ⟨hkind, f, hedges, hadjoin⟩
            exact ⟨hkind, f, seed, hedges, hadjoin, hclosureFinal.1⟩
        have hcorrNonempty := hmod.2.2
          (ett.series.data.tree (Fin.last ett.rounds).castSucc)
          originalPrefix'.abovePenultimate
          originalPrefix'.strictAbovePenultimate heligible
        rcases hcorrNonempty with ⟨corr⟩
        have hfinalEq := CorrespondingTerminalClosureEq G k e0 input
          (ett.series.data.tree (Fin.last ett.rounds).castSucc)
          (ett.series.data.coloring ⟨ett.rounds - 1, by omega⟩)
          originalPrefix' sigmaPrev
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) seed corr
          (by simpa [rLast] using hseedRoute) hclosureFinal
        refine ⟨corr, ?_, corr.finalGeneratingColoring.symm, ?_⟩
        · simpa [rLast] using hfinalEq
        · exact MaximumPropertyTransport G k e0 originalPrefix'
            sigmaPrev hmod
            (ett.series.data.tree (Fin.last ett.rounds).castSucc)
            corr hprefixMP'
