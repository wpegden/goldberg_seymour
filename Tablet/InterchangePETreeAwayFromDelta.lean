import Tablet.BoundaryColorEdges
import Tablet.BoundaryColorVertex
import Tablet.BoundaryEdges
import Tablet.CertifiedETTPredecessor
import Tablet.ColoredVertexSetElementary
import Tablet.CombinedStableClosurePreserved
import Tablet.CombinedStableColoring
import Tablet.DefectiveColor
import Tablet.ElementarySingleBoundaryInterchangeable
import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtendedTashkinovTree
import Tablet.ExtensionBase
import Tablet.HierarchyBase
import Tablet.HkuParallelBoundaryStructure
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.LooplessMultigraph
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumProperty
import Tablet.MissingColors
import Tablet.ModColoring
import Tablet.OrderedTreeUnion
import Tablet.ParallelClosureUnionElementary
import Tablet.ParallelExtensionColor
import Tablet.ParallelExtensionUndoStable
import Tablet.PartialEdgeColoring
import Tablet.PresentColors
import Tablet.StableColoring
import Tablet.StableColoringBeforeVertex
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TechnicalTheoremBase
import Tablet.TreeInterchangeable
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent
import Tablet.sc2

-- [TABLET NODE: InterchangePETreeAwayFromDelta]
theorem InterchangePETreeAwayFromDelta {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
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
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (base : HierarchyBase ett generating)
    (hproper : IsProperEdgeColoring G sigma)
    (hone : IsOneEdgeUncolored sigma e0)
    (hstable : CombinedStableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      base.closure
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      generating sigma)
    (support : V) (gamma delta alpha beta : Fin k)
    (hsupport : ett.series.data.chosenVertex (Fin.last ett.rounds) =
      some support)
    (hgamma : ett.series.data.gamma (Fin.last ett.rounds) = some gamma)
    (hdelta : ett.series.data.delta (Fin.last ett.rounds) = some delta) :
    let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
    alpha ∈ TreeMissingColors sigma Tn →
      alpha ≠ delta →
      beta ≠ delta →
      TreeInterchangeable G Tn sigma alpha beta := by
-- BODY
  classical
  dsimp
  intro halpha hne hbeta
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
  have hgen : generating = ett.series.data.coloring n := by
    simpa [n] using ett.generatingColoring
  have hstableTree : StableColoring Tn
      (TashkinovStoredColors ett.series.data n) generating sigma := by
    simpa [Tn, hgen] using hstable.1
  have hproperGen : IsProperEdgeColoring G generating := by
    have hstep := ett.series.certified n
    generalize targetEq : n = target at hstep
    cases hstep with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
      have hn : n ≠ 0 := by simp [n]; omega
      exact (hn targetEq).elim
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma closedExtension orderedExtension
        strictExtension =>
      have hi : i.succ = n := by
        apply Fin.ext
        have hv := congrArg Fin.val targetEq
        simp at hv
        omega
      simpa [hgen, hi] using currentProper
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      have hp : ett.series.data.kind n =
          some TashkinovExtensionKind.PE := by simpa [n] using hPE
      rw [targetEq, currentKind] at hp
      contradiction
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      have hp : ett.series.data.kind n =
          some TashkinovExtensionKind.PE := by simpa [n] using hPE
      rw [targetEq, currentKind] at hp
      contradiction
  have honeGen : IsOneEdgeUncolored generating e0 := by
    have hstep := ett.series.certified n
    generalize targetEq : n = target at hstep
    cases hstep with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
      have hn : n ≠ 0 := by simp [n]; omega
      exact (hn targetEq).elim
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma closedExtension orderedExtension
        strictExtension =>
      have hi : i.succ = n := by
        apply Fin.ext
        have hv := congrArg Fin.val targetEq
        simp at hv
        omega
      simpa [hgen, hi] using currentOneUncolored
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      have hp : ett.series.data.kind n =
          some TashkinovExtensionKind.PE := by simpa [n] using hPE
      rw [targetEq, currentKind] at hp
      contradiction
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      have hp : ett.series.data.kind n =
          some TashkinovExtensionKind.PE := by simpa [n] using hPE
      rw [targetEq, currentKind] at hp
      contradiction
  have hstep := ett.series.certified n
  generalize targetEq : n = target at hstep
  cases hstep with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    have hn : n ≠ 0 := by simp [n]; omega
    exact (hn targetEq).elim
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hp : ett.series.data.kind n =
        some TashkinovExtensionKind.PE := by simpa [n] using hPE
    rw [targetEq, currentKind] at hp
    contradiction
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hp : ett.series.data.kind n =
        some TashkinovExtensionKind.PE := by simpa [n] using hPE
    rw [targetEq, currentKind] at hp
    contradiction
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      terminalGamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta terminalGammaValue closedExtension orderedExtension
      strictExtension =>
    have hi : i.succ = n := by
      apply Fin.ext
      have hv := congrArg Fin.val targetEq
      simp at hv
      omega
    have hvertex : ett.series.data.chosenVertex n = some choice.vertex := by
      rw [← hi]
      exact currentVertex
    have hcolor : ett.series.data.gamma n = some terminalGamma := by
      rw [← hi]
      exact terminalGammaValue
    have hdelta' : ett.series.data.delta n = some choice.color := by
      rw [← hi]
      exact currentDelta
    have hlowerElem : ColoredVertexSetElementary G
        (ett.series.data.coloring ⟨ett.rounds - 1, by omega⟩)
        (TreeSequenceVertexSet Tn) := by
      set_option maxHeartbeats 800000 in
        by_cases honeRound : ett.rounds = 1
        · have htech := TechnicalTheoremBase G k ett.rounds e0 input ett.series
          have hT : Tn = ett.series.data.tree ⟨1, by omega⟩ := by
            apply congrArg (fun j : Fin (ett.rounds + 2) => ett.series.data.tree j)
            apply Fin.ext
            simp [Tn, n, honeRound]
          have hc : (⟨ett.rounds - 1, by omega⟩ : Fin (ett.rounds + 1)) = 0 := by
            apply Fin.ext
            simp [honeRound]
          rw [hT, hc]
          exact htech.1
        · have hgt : 1 < ett.rounds := by omega
          obtain ⟨pred, hpredRound, hpredMP, htrees, hdata⟩ :=
            CertifiedETTPredecessor G k e0 input T generating ett hMP hgt
          have hpredElem := hlower pred (by omega) (by omega) hpredMP
          have hp : ColoredVertexSetElementary G
              (ett.series.data.coloring ⟨ett.rounds - 1, by omega⟩)
              (TreeSequenceVertexSet
                (ett.series.data.tree ⟨ett.rounds, by omega⟩)) := hpredElem.1
          have heq : (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) =
              (Fin.last ett.rounds).castSucc := by
            apply Fin.ext
            rfl
          rw [heq] at hp
          exact hp
    have hbound := HkuParallelBoundaryStructure G k ett.rounds e0 input ett.series i
      choice.edge choice.color terminalGamma choice.vertex
      (by simpa using currentKind) (by simpa using currentEdges)
      (by simpa using currentDelta) (by simpa using terminalGammaValue)
      (by simpa using currentVertex)
    have hpre : ColoredVertexSetElementary G
        (ett.series.data.coloring i.castSucc)
        (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) := by
      have hidx : i.castSucc = (⟨ett.rounds - 1, by omega⟩ : Fin (ett.rounds + 1)) := by
        apply Fin.ext
        have hv := congrArg Fin.val hi
        simp [n] at hv ⊢
        omega
      have htree : Tn = ett.series.data.tree i.succ.castSucc := by
        have hidx2 : n.castSucc = i.succ.castSucc := by
          apply Fin.ext
          have hv := congrArg Fin.val hi
          simp [n] at hv ⊢
          omega
        simpa [Tn] using congrArg (fun j => ett.series.data.tree j) hidx2
      have hcolor : ett.series.data.coloring i.castSucc =
          ett.series.data.coloring (⟨ett.rounds - 1, by omega⟩) :=
        congrArg ett.series.data.coloring hidx
      unfold ColoredVertexSetElementary at hlowerElem ⊢
      rw [hcolor, ← htree]
      exact fun {u} hu {v} hv huv => hlowerElem hu hv huv
    have hnegc : terminalGamma ≠ choice.color := by
      intro heq
      have hp : choice.color ∈ PresentColors G choice.selected choice.vertex := by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨choice.edge, choice.edgeIncident, choice.edgeColor⟩
      have hm : terminalGamma ∉ PresentColors G choice.selected choice.vertex := by
        simpa [MissingColors] using gammaRule.1
      exact hm (heq ▸ hp)
    have hsecondEdge : secondStable choice.edge = some choice.color := by
      have hs := secondStableRelation.1 choice.edge
        ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
        ⟨choice.color, Finset.mem_union_right _ (Finset.mem_insert_self _ _),
          choice.edgeColor⟩
      exact hs.trans choice.edgeColor
    have hcomponentEdge : Sum.inr choice.edge ∈
        TwoColorComponent G secondStable terminalGamma choice.color
          (Sum.inl choice.vertex) := by
      change (TwoColorIncidenceGraph G secondStable terminalGamma choice.color).connectedComponentMk
          (Sum.inr choice.edge) =
        (TwoColorIncidenceGraph G secondStable terminalGamma choice.color).connectedComponentMk
          (Sum.inl choice.vertex)
      apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      simp [TwoColorIncidenceGraph, choice.edgeIncident, hsecondEdge]
    have hcurrentEdge : ett.series.data.coloring n choice.edge =
        some terminalGamma := by
      have hcur : ett.series.data.coloring n =
          TwoColorComponentSwap G secondStable terminalGamma choice.color
            (Sum.inl choice.vertex) := by
        simpa [hi] using currentColoring
      rw [hcur]
      simp [TwoColorComponentSwap, hcomponentEdge, hsecondEdge]
    have hgammaNotTree : terminalGamma ∉ TreeMissingColors generating Tn := by
      intro hm
      have hm' : terminalGamma ∈ TreeMissingColors
          (ett.series.data.coloring i.succ)
          (ett.series.data.tree i.succ.castSucc) := by
        simpa [hgen, Tn, hi] using hm
      have hx := hbound.2.2 hpre terminalGamma hm' hnegc
      rw [hbound.1] at hx
      simpa using hx
    have hgammaStored : terminalGamma ∈
        TashkinovStoredColors ett.series.data n := by
      have hn : n.val ≠ 0 := by simp [n]; omega
      rw [TashkinovStoredColors]
      simp only [hn, ↓reduceIte]
      apply Finset.mem_sdiff.mpr
      constructor
      · simp only [Finset.mem_biUnion]
        refine ⟨n, Finset.mem_univ _, ?_⟩
        rw [← hi, currentStored]
        simp
      · intro hm
        apply hgammaNotTree
        simpa [hgen] using hm
    have hstableRev : StableColoring Tn
        (TashkinovStoredColors ett.series.data n) sigma generating := by
      let left : {psi : PartialEdgeColoring E k //
          IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
        ⟨generating, hproperGen, honeGen⟩
      let right : {psi : PartialEdgeColoring E k //
          IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
        ⟨sigma, hproper, hone⟩
      have forward : StableColoring Tn
          (TashkinovStoredColors ett.series.data n) left.1 right.1 := by
        simpa [left, right] using hstableTree
      have reverse := (sc2 G e0 Tn
        (TashkinovStoredColors ett.series.data n)).symm forward
      simpa [left, right] using reverse
    have hgenMissing : alpha ∈ TreeMissingColors generating Tn := by
      unfold TreeMissingColors at halpha ⊢
      obtain ⟨v, hv, hm⟩ := Finset.mem_biUnion.mp halpha
      refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
      rw [← hstableTree.2 v hv]
      exact hm
    have halphaGamma : alpha ≠ terminalGamma := by
      intro heq
      apply hgammaNotTree
      simpa [heq] using hgenMissing
    have hgenEmpty : BoundaryColorEdges G generating
        (TreeSequenceVertexSet Tn) alpha = {} := by
      have hx := hbound.2.2 hpre alpha
        (by simpa [hgen, Tn, hi] using hgenMissing)
        (by
          have hcd : choice.color = delta := by
            rw [← Option.some.injEq]
            rw [← hdelta', hdelta]
          intro ha
          apply hne
          exact ha.trans hcd)
      simpa [hgen, Tn, hi] using hx
    have hsigmaEmpty : BoundaryColorEdges G sigma
        (TreeSequenceVertexSet Tn) alpha = {} := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro g hg
      have hg' : g ∈ BoundaryEdges G (TreeSequenceVertexSet Tn) ∧
          sigma g = some alpha := by
        simpa [BoundaryColorEdges] using hg
      have hinc : TreeIncidentEdge Tn g := by
        unfold TreeIncidentEdge
        obtain ⟨u, hu, v, hv, he⟩ := by
          simpa [BoundaryEdges] using hg'.1
        refine ⟨u, hu, ?_⟩
        change u ∈ G.ends g
        rw [he]
        simp
      have hctrl : ∃ c ∈ TreeMissingColors sigma Tn ∪
          TashkinovStoredColors ett.series.data n, sigma g = some c :=
        ⟨alpha, Finset.mem_union_left _ halpha, hg'.2⟩
      have heq : generating g = sigma g := hstableRev.1 g hinc hctrl
      have : g ∈ BoundaryColorEdges G generating (TreeSequenceVertexSet Tn) alpha := by
        simpa [BoundaryColorEdges, hg'.1, heq, hg'.2]
      rw [hgenEmpty] at this
      simpa using this
    have hgammaSingleton : BoundaryColorEdges G sigma
        (TreeSequenceVertexSet Tn) terminalGamma = {choice.edge} := by
      apply Finset.Subset.antisymm
      · intro g hg
        have hg' : g ∈ BoundaryEdges G (TreeSequenceVertexSet Tn) ∧
            sigma g = some terminalGamma := by
          simpa [BoundaryColorEdges] using hg
        have hinc : TreeIncidentEdge Tn g := by
          unfold TreeIncidentEdge
          obtain ⟨u, hu, v, hv, he⟩ := by
            simpa [BoundaryEdges] using hg'.1
          refine ⟨u, hu, ?_⟩
          change u ∈ G.ends g
          rw [he]
          simp
        have hctrl : ∃ c ∈ TreeMissingColors sigma Tn ∪
            TashkinovStoredColors ett.series.data n, sigma g = some c :=
          ⟨terminalGamma, Finset.mem_union_right _ hgammaStored, hg'.2⟩
        have heq : generating g = sigma g := hstableRev.1 g hinc hctrl
        have : g ∈ BoundaryColorEdges G generating (TreeSequenceVertexSet Tn)
            terminalGamma := by
          simpa [BoundaryColorEdges, hg'.1, heq, hg'.2]
        have ht : g ∈ BoundaryColorEdges G
            (ett.series.data.coloring i.succ)
            (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) terminalGamma := by
          simpa [hgen, Tn, hi] using this
        rw [hbound.1] at ht
        simpa using ht
      · intro g hg
        have : g = choice.edge := by simpa using hg
        subst g
        have hce : generating choice.edge = some terminalGamma := by
          simpa [hgen, Tn, hi] using hcurrentEdge
        have hb : choice.edge ∈ BoundaryEdges G (TreeSequenceVertexSet Tn) := by
          obtain ⟨c, hc, hm⟩ := choice.edgeDefective
          have hm' := hm
          simp only [BoundaryColorEdges, Finset.mem_filter] at hm'
          simpa [Tn, hi] using hm'.1
        have hinc : TreeIncidentEdge Tn choice.edge := by
          unfold TreeIncidentEdge
          obtain ⟨u, hu, v, hv, he⟩ := by simpa [BoundaryEdges] using hb
          refine ⟨u, hu, ?_⟩
          change u ∈ G.ends choice.edge
          rw [he]
          simp
        have hs : sigma choice.edge = generating choice.edge :=
          hstableTree.1 choice.edge hinc
            ⟨terminalGamma, Finset.mem_union_right _ hgammaStored, hce⟩
        have hcs : sigma choice.edge = some terminalGamma := hs.trans hce
        simpa [BoundaryColorEdges, hb, hcs]
    have hnonempty : choice.edge ∈ BoundaryColorEdges G sigma
        (TreeSequenceVertexSet Tn) terminalGamma := by
      rw [hgammaSingleton]
      simp
    have hnonemptyData : choice.edge ∈ BoundaryEdges G
        (TreeSequenceVertexSet Tn) ∧
        sigma choice.edge = some terminalGamma := by
      simpa [BoundaryColorEdges] using hnonempty
    have hbad : choice.edge ∈ BoundaryColorEdges G generating
        (TreeSequenceVertexSet Tn) terminalGamma := by
      have hinc : TreeIncidentEdge Tn choice.edge := by
        unfold TreeIncidentEdge
        have hb := hnonemptyData.1
        obtain ⟨u, hu, v, hv, he⟩ := by simpa [BoundaryEdges] using hb
        refine ⟨u, hu, ?_⟩
        change u ∈ G.ends choice.edge
        rw [he]
        simp
      have hc : generating choice.edge = sigma choice.edge := by
        exact hstableRev.1 choice.edge hinc
          ⟨terminalGamma, Finset.mem_union_right _ hgammaStored,
            hnonemptyData.2⟩
      simpa [BoundaryColorEdges, hnonemptyData.1, hc, hnonemptyData.2]
    have hmissEq : TreeMissingColors sigma Tn =
        TreeMissingColors generating Tn := by
      unfold TreeMissingColors
      apply Finset.ext
      intro c
      constructor <;> intro hc
      · obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
        refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
        exact hstableTree.2 v hv ▸ hcv
      · obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
        refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
        exact (hstableTree.2 v hv).symm ▸ hcv
    have hclosure := CombinedStableClosurePreserved G k e0 input T generating generating sigma ett
      hpositive base (by simpa [n] using hgen) hPE hproperGen honeGen hproper hone hstable
    let baseSigma : HierarchyBase ett sigma :=
      { core := base.core
        closure := base.closure
        supportPosition := base.supportPosition
        supportPositive := base.supportPositive
        terminalMissingColors := by
          simpa [hgen] using hmissEq
        parallel := by
          dsimp
          intro hp
          have hh := base.parallel hp
          exact ⟨hh.1, hclosure.2.2, hh.2.2⟩
        nonparallel := base.nonparallel }
    have hcoreElem : ColoredVertexSetElementary G sigma
        (TreeSequenceVertexSet base.core) := ParallelClosureUnionElementary G k e0 input T generating
      ett hMP hpositive hlower hPE sigma hproper hone hstableTree baseSigma
    have helemSigma : ColoredVertexSetElementary G sigma
        (TreeSequenceVertexSet Tn) := by
      intro u hu v hv huv
      have huCore : u ∈ TreeSequenceVertexSet base.core := by
        obtain ⟨ou⟩ := (base.parallel hPE).2.2
        rw [ou.vertexSet]
        exact Finset.mem_union_left _ hu
      have hvCore : v ∈ TreeSequenceVertexSet base.core := by
        obtain ⟨ou⟩ := (base.parallel hPE).2.2
        rw [ou.vertexSet]
        exact Finset.mem_union_left _ hv
      exact hcoreElem huCore hvCore huv
    have hext := ExtensionBase G k e0 input T generating ett hMP hpositive hlower
      
    dsimp at hext
    have hstableLast : StableColoring
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
        (ett.series.data.coloring (Fin.last ett.rounds)) sigma := by
      simpa [Tn, n, hgen] using hstableTree
    have hstableI : StableColoring
        (ett.series.data.tree i.succ.castSucc)
        (TashkinovStoredColors ett.series.data i.succ)
        (ett.series.data.coloring i.succ) sigma := by
      simpa [Tn, n, hgen, hi] using hstableTree
    have hcomponent := hext choice.vertex terminalGamma choice.color
      (by simpa [n, hi] using currentKind) (by simpa [n, hi] using currentVertex)
      (by simpa [n, hi] using terminalGammaValue) (by simpa [n, hi] using currentDelta)
      sigma hproper hone hstableLast
    have hvchoice : choice.vertex ∈ TreeSequenceVertexSet Tn := by
      simpa [Tn, hi] using choice.vertexDefective.1
    have hvchoiceI : choice.vertex ∈
        TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc) := by
      simpa [Tn, hi] using hvchoice
    have hcomponentI : ∀ w, w ∈
        TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc) →
        (Sum.inl w ∈ TwoColorComponent G sigma terminalGamma choice.color
          (Sum.inl choice.vertex) ↔ w = choice.vertex) := by
      intro w hw
      apply hcomponent w
      simpa [Tn, hi] using hw
    have hundo := ParallelExtensionUndoStable G k ett.rounds e0 input ett.series i
      choice.vertex terminalGamma choice.color
      (by simpa using currentKind) (by simpa using currentVertex)
      (by simpa using terminalGammaValue) (by simpa using currentDelta)
      sigma hproper hone hstableI hvchoiceI hcomponentI
    by_cases hbg : beta = terminalGamma
    · subst beta
      apply ElementarySingleBoundaryInterchangeable G sigma Tn alpha terminalGamma hproper
      · exact helemSigma
      · exact hsigmaEmpty
      · rw [hgammaSingleton]
        simp
    · rcases hundo with ⟨selected, undoneStable, selectedProper, selectedOne,
        selectedStable, undoneProper, undoneOne, undoneRelation, currentSwap,
        finalStable⟩
      dsimp at finalStable
      rcases finalStable with ⟨stableSecondUndone, stableSelectedUndone,
        stablePreviousUndone⟩
      let undone := TwoColorComponentSwap G sigma terminalGamma choice.color
        (Sum.inl choice.vertex)
      have undoneProper' : IsProperEdgeColoring G undone := by
        exact TwoColorComponentSwapProper G sigma terminalGamma choice.color
          hnegc hproper (Sum.inl choice.vertex)
      have undoneOne' : IsOneEdgeUncolored undone e0 := by
        dsimp [undone]
        unfold IsOneEdgeUncolored
        have hone' := hone
        unfold IsOneEdgeUncolored at hone'
        constructor
        · simp [TwoColorComponentSwap, hone'.1]
        · intro e he
          obtain ⟨c, hc⟩ := hone'.2 e he
          by_cases hem : Sum.inr e ∈
              TwoColorComponent G sigma terminalGamma choice.color
                (Sum.inl choice.vertex)
          · by_cases hcg : c = terminalGamma
            · exact ⟨choice.color, by simp [undone, TwoColorComponentSwap, hem, hc, hcg]⟩
            · by_cases hcd : c = choice.color
              · exact ⟨terminalGamma, by simp [undone, TwoColorComponentSwap, hem, hc, hcd,
                  hnegc, hnegc.symm]⟩
              · exact ⟨c, by simp [undone, TwoColorComponentSwap, hem, hc, hcg, hcd]⟩
          · exact ⟨c, by simp [undone, TwoColorComponentSwap, hem, hc]⟩
      have halphaDelta : alpha ≠ choice.color := by
        intro heq
        apply hne
        have hcd : choice.color = delta := by
          rw [← Option.some.injEq]
          rw [← hdelta', hdelta]
        exact heq.trans hcd
      have hbetaGamma : beta ≠ terminalGamma := hbg
      have hbetaDelta : beta ≠ choice.color := by
        intro heq
        apply hbeta
        have hcd : choice.color = delta := by
          rw [← Option.some.injEq]
          rw [← hdelta', hdelta]
        exact heq.trans hcd
      have hswapAlpha : ∀ e, undone e = some alpha ↔ sigma e = some alpha := by
        intro e
        by_cases he : Sum.inr e ∈
            TwoColorComponent G sigma terminalGamma choice.color
              (Sum.inl choice.vertex)
        · by_cases h1 : sigma e = some terminalGamma <;>
            by_cases h2 : sigma e = some choice.color <;>
            simp [undone, TwoColorComponentSwap, he, h1, h2,
              halphaGamma, halphaGamma.symm, halphaDelta, halphaDelta.symm,
              hnegc, hnegc.symm]
        · simp [undone, TwoColorComponentSwap, he]
      have hswapBeta : ∀ e, undone e = some beta ↔ sigma e = some beta := by
        intro e
        by_cases he : Sum.inr e ∈
            TwoColorComponent G sigma terminalGamma choice.color
              (Sum.inl choice.vertex)
        · by_cases h1 : sigma e = some terminalGamma <;>
            by_cases h2 : sigma e = some choice.color <;>
            simp [undone, TwoColorComponentSwap, he, h1, h2,
              hbetaGamma, hbetaGamma.symm, hbetaDelta, hbetaDelta.symm,
              hnegc, hnegc.symm]
        · simp [undone, TwoColorComponentSwap, he]
      have hadj : ∀ x y,
          (TwoColorIncidenceGraph G undone alpha beta).Adj x y ↔
            (TwoColorIncidenceGraph G sigma alpha beta).Adj x y := by
        intro x y
        cases x <;> cases y <;>
          simp [TwoColorIncidenceGraph, hswapAlpha, hswapBeta]
      have hreach : ∀ {x y},
          (TwoColorIncidenceGraph G undone alpha beta).Reachable x y ↔
            (TwoColorIncidenceGraph G sigma alpha beta).Reachable x y := by
        intro x y
        constructor <;> intro hp
        · rcases hp with ⟨p⟩
          refine ⟨?_⟩
          induction p with
          | nil => exact .nil
          | cons ha p ih => exact .cons ((hadj _ _).mp ha) ih
        · rcases hp with ⟨p⟩
          refine ⟨?_⟩
          induction p with
          | nil => exact .nil
          | cons ha p ih => exact .cons ((hadj _ _).mpr ha) ih
      have hcomponentEq : ∀ z,
          TwoColorComponent G undone alpha beta z =
            TwoColorComponent G sigma alpha beta z := by
        intro z
        apply Set.ext
        intro x
        change (TwoColorIncidenceGraph G undone alpha beta).connectedComponentMk x =
          (TwoColorIncidenceGraph G undone alpha beta).connectedComponentMk z ↔
          (TwoColorIncidenceGraph G sigma alpha beta).connectedComponentMk x =
          (TwoColorIncidenceGraph G sigma alpha beta).connectedComponentMk z
        rw [SimpleGraph.ConnectedComponent.eq, SimpleGraph.ConnectedComponent.eq]
        exact hreach
      have htransport : TreeInterchangeable G Tn undone alpha beta →
          TreeInterchangeable G Tn sigma alpha beta := by
        intro hinter
        unfold TreeInterchangeable at hinter ⊢
        intro z w hz hw hzX hwX
        rw [← hcomponentEq z, ← hcomponentEq w]
        apply hinter z w
        · rcases hz with ⟨hn, x, hx, hs⟩
          refine ⟨hn, x, ?_, ?_⟩
          · rw [← hcomponentEq z] at hx
            exact hx
          · intro y hy z hz
            apply hs
            · exact (hadj x y).mp hy
            · exact (hadj x z).mp hz
        · rcases hw with ⟨hn, x, hx, hs⟩
          refine ⟨hn, x, ?_, ?_⟩
          · rw [← hcomponentEq w] at hx
            exact hx
          · intro y hy z hz
            apply hs
            · exact (hadj x y).mp hy
            · exact (hadj x z).mp hz
        · rcases hzX with ⟨v, hv, hx⟩
          exact ⟨v, hv, by rw [hcomponentEq z]; exact hx⟩
        · rcases hwX with ⟨v, hv, hx⟩
          exact ⟨v, hv, by rw [hcomponentEq w]; exact hx⟩
      by_cases honeRound : ett.rounds = 1
      · have htech := TechnicalTheoremBase G k ett.rounds e0 input ett.series
        let undone := TwoColorComponentSwap G sigma terminalGamma choice.color
          (Sum.inl choice.vertex)
        have hi0 : i = (⟨0, by omega⟩ : Fin ett.rounds) := by
          apply Fin.ext
          have hv := congrArg Fin.val hi
          simp [n, honeRound] at hv ⊢
          omega
        have htree0 : ett.series.data.tree (⟨1, by omega⟩ : Fin (ett.rounds + 2)) = Tn := by
          apply congrArg ett.series.data.tree
          apply Fin.ext
          simp [Tn, n, honeRound, hi0]
        have htreeLast : ett.series.data.tree (Fin.last ett.rounds).castSucc =
            ett.series.data.tree (⟨1, by omega⟩ : Fin (ett.rounds + 2)) := by
          apply congrArg ett.series.data.tree
          apply Fin.ext
          simp [honeRound]
        have hstable0 : StableColoring
            (ett.series.data.tree ⟨1, by omega⟩)
            (TashkinovStoredColors ett.series.data 0)
            (ett.series.data.coloring 0) undone := by
          have hci : i.castSucc = 0 := by
            apply Fin.ext
            simp [hi0, honeRound]
          have hti : i.castSucc.succ = (⟨1, by omega⟩ : Fin (ett.rounds + 2)) := by
            apply Fin.ext
            simp [hi0, honeRound]
          convert stablePreviousUndone using 1 <;> simp [undone, hci, hti]
        have hmissing0 : alpha ∈ TreeMissingColors undone
            (ett.series.data.tree ⟨1, by omega⟩) := by
          unfold TreeMissingColors
          obtain ⟨v, hv, hmv⟩ := Finset.mem_biUnion.mp halpha
          refine Finset.mem_biUnion.mpr ⟨v, ?_, ?_⟩
          · rw [htreeLast] at hv
            exact hv
          · have hnot : ∀ x, Incident G v x → ¬undone x = some alpha := by
              intro x hx hxa
              unfold MissingColors at hmv
              have hmv' : ∀ x, Incident G v x → ¬sigma x = some alpha := by
                simpa [PresentColors] using (Finset.mem_sdiff.mp hmv).2
              exact hmv' x hx ((hswapAlpha x).mp hxa)
            simpa [MissingColors, PresentColors] using hnot
        have hres := htech.2 undone undoneProper' undoneOne' hstable0 alpha beta
        have htemp := hres (Or.inl hmissing0)
        have htemp' : TreeInterchangeable G Tn undone alpha beta := by
          rw [← htree0]
          exact htemp
        simpa [Tn] using (htransport htemp') <;> omega
      · have hgt : 1 < ett.rounds := by omega
        have hpred := CertifiedETTPredecessor G k e0 input T generating ett hMP hgt
        rcases hpred with ⟨pred, predRound, predMP, predTrees, predData⟩
        have hiVal : i.val + 1 = ett.rounds := by
          have hv := congrArg Fin.val hi
          simp [n] at hv
          omega
        have low := (hlower pred (by omega) (by omega) predMP).2.1
        let undone := TwoColorComponentSwap G sigma terminalGamma choice.color
          (Sum.inl choice.vertex)
        have undoneProper' : IsProperEdgeColoring G undone := by
          exact TwoColorComponentSwapProper G sigma terminalGamma choice.color
            hnegc hproper (Sum.inl choice.vertex)
        have undoneOne' : IsOneEdgeUncolored undone e0 := by
          dsimp [undone]
          unfold IsOneEdgeUncolored
          have hone' := hone
          unfold IsOneEdgeUncolored at hone'
          constructor
          · simp [TwoColorComponentSwap, hone'.1]
          · intro e he
            obtain ⟨c, hc⟩ := hone'.2 e he
            by_cases hem : Sum.inr e ∈
                TwoColorComponent G sigma terminalGamma choice.color
                  (Sum.inl choice.vertex)
            · by_cases hcg : c = terminalGamma
              · exact ⟨choice.color, by simp [undone, TwoColorComponentSwap, hem, hc, hcg]
                ⟩
              · by_cases hcd : c = choice.color
                · exact ⟨terminalGamma, by simp [undone, TwoColorComponentSwap, hem, hc, hcd,
                    hnegc, hnegc.symm]⟩
                · exact ⟨c, by simp [undone, TwoColorComponentSwap, hem, hc, hcg, hcd]⟩
            · exact ⟨c, by simp [undone, TwoColorComponentSwap, hem, hc]⟩
        have hpredNext : pred.series.data.tree
            (Fin.last (pred.rounds + 1)) = Tn := by
          have hh := predTrees (Fin.last (pred.rounds + 1))
          have hidx : (Fin.castLE (by omega) (Fin.last (pred.rounds + 1))) = n.castSucc := by
            apply Fin.ext
            simp [predRound, n, hiVal]
            omega
          simpa [Tn] using hh.trans (congrArg ett.series.data.tree hidx)
        have hpredColor : pred.series.data.coloring (Fin.last pred.rounds) =
            ett.series.data.coloring i.castSucc := by
          have hh := (predData (Fin.last pred.rounds)).1
          have hidx : (Fin.castLE (by omega) (Fin.last pred.rounds)) = i.castSucc := by
            apply Fin.ext
            simp [predRound, hiVal]
            omega
          rw [hidx] at hh
          exact hh
        have hpredStored : TashkinovStoredColors pred.series.data
            (Fin.last pred.rounds) = TashkinovStoredColors ett.series.data i.castSucc := by
          have hh := (predData (Fin.last pred.rounds)).2.2.2.2.2.2.2.2.1
          have hidx : (Fin.castLE (by omega) (Fin.last pred.rounds)) = i.castSucc := by
            apply Fin.ext
            simp [predRound, hiVal]
            omega
          rw [hidx] at hh
          exact hh
        have hstablePred : StableColoring
            (pred.series.data.tree (Fin.last (pred.rounds + 1)))
            (TashkinovStoredColors pred.series.data (Fin.last pred.rounds))
            (pred.series.data.coloring (Fin.last pred.rounds)) undone := by
          rw [hpredStored, hpredColor]
          have htreeI : i.castSucc.succ = n.castSucc := by
            apply Fin.ext
            have hv := congrArg Fin.val hi
            simp [n] at hv ⊢
            omega
          rw [hpredNext]
          change StableColoring (ett.series.data.tree n.castSucc)
            (TashkinovStoredColors ett.series.data i.castSucc)
            (ett.series.data.coloring i.castSucc) undone
          rw [← htreeI]
          simpa [undone] using stablePreviousUndone
        have halphaDelta : alpha ≠ choice.color := by
          intro heq
          apply hne
          have hcd : choice.color = delta := by
            rw [← Option.some.injEq]
            rw [← hdelta', hdelta]
          exact heq.trans hcd
        have hbetaGamma : beta ≠ terminalGamma := hbg
        have hbetaDelta : beta ≠ choice.color := by
          intro heq
          apply hbeta
          have hcd : choice.color = delta := by
            rw [← Option.some.injEq]
            rw [← hdelta', hdelta]
          exact heq.trans hcd
        have hswapAlpha : ∀ e, undone e = some alpha ↔ sigma e = some alpha := by
          intro e
          by_cases he : Sum.inr e ∈
              TwoColorComponent G sigma terminalGamma choice.color
                (Sum.inl choice.vertex)
          · by_cases h1 : sigma e = some terminalGamma <;>
              by_cases h2 : sigma e = some choice.color <;>
              simp [undone, TwoColorComponentSwap, he, h1, h2,
                halphaGamma, halphaGamma.symm, halphaDelta, halphaDelta.symm,
                hnegc, hnegc.symm]
          · simp [undone, TwoColorComponentSwap, he]
        have hswapBeta : ∀ e, undone e = some beta ↔ sigma e = some beta := by
          intro e
          by_cases he : Sum.inr e ∈
              TwoColorComponent G sigma terminalGamma choice.color
                (Sum.inl choice.vertex)
          · by_cases h1 : sigma e = some terminalGamma <;>
              by_cases h2 : sigma e = some choice.color <;>
              simp [undone, TwoColorComponentSwap, he, h1, h2,
                hbetaGamma, hbetaGamma.symm, hbetaDelta, hbetaDelta.symm,
                hnegc, hnegc.symm]
          · simp [undone, TwoColorComponentSwap, he]
        have hadj : ∀ x y,
            (TwoColorIncidenceGraph G undone alpha beta).Adj x y ↔
              (TwoColorIncidenceGraph G sigma alpha beta).Adj x y := by
          intro x y
          cases x <;> cases y <;>
            simp [TwoColorIncidenceGraph, hswapAlpha, hswapBeta]
        have hreach : ∀ {x y},
            (TwoColorIncidenceGraph G undone alpha beta).Reachable x y ↔
              (TwoColorIncidenceGraph G sigma alpha beta).Reachable x y := by
          intro x y
          constructor <;> intro hp
          · rcases hp with ⟨p⟩
            refine ⟨?_⟩
            induction p with
            | nil => exact .nil
            | cons ha p ih => exact .cons ((hadj _ _).mp ha) ih
          · rcases hp with ⟨p⟩
            refine ⟨?_⟩
            induction p with
            | nil => exact .nil
            | cons ha p ih => exact .cons ((hadj _ _).mpr ha) ih
        have hcomponentEq : ∀ z,
            TwoColorComponent G undone alpha beta z =
              TwoColorComponent G sigma alpha beta z := by
          intro z
          apply Set.ext
          intro x
          change (TwoColorIncidenceGraph G undone alpha beta).connectedComponentMk x =
            (TwoColorIncidenceGraph G undone alpha beta).connectedComponentMk z ↔
            (TwoColorIncidenceGraph G sigma alpha beta).connectedComponentMk x =
            (TwoColorIncidenceGraph G sigma alpha beta).connectedComponentMk z
          rw [SimpleGraph.ConnectedComponent.eq, SimpleGraph.ConnectedComponent.eq]
          exact hreach
        have htransport : TreeInterchangeable G Tn undone alpha beta →
            TreeInterchangeable G Tn sigma alpha beta := by
          intro hinter
          unfold TreeInterchangeable at hinter ⊢
          intro z w hz hw hzX hwX
          rw [← hcomponentEq z, ← hcomponentEq w]
          apply hinter z w
          · rcases hz with ⟨hn, x, hx, hs⟩
            refine ⟨hn, x, ?_, ?_⟩
            · rw [← hcomponentEq z] at hx
              exact hx
            · intro y hy z hz
              apply hs
              · exact (hadj x y).mp hy
              · exact (hadj x z).mp hz
          · rcases hw with ⟨hn, x, hx, hs⟩
            refine ⟨hn, x, ?_, ?_⟩
            · rw [← hcomponentEq w] at hx
              exact hx
            · intro y hy z hz
              apply hs
              · exact (hadj x y).mp hy
              · exact (hadj x z).mp hz
          · rcases hzX with ⟨v, hv, hx⟩
            exact ⟨v, hv, by rw [hcomponentEq z]; exact hx⟩
          · rcases hwX with ⟨v, hv, hx⟩
            exact ⟨v, hv, by rw [hcomponentEq w]; exact hx⟩
        have hmissingPred : alpha ∈ TreeMissingColors undone
            (pred.series.data.tree (Fin.last (pred.rounds + 1))) := by
          rw [hpredNext]
          unfold TreeMissingColors
          obtain ⟨v, hv, hmv⟩ := Finset.mem_biUnion.mp halpha
          refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
          simpa [MissingColors, PresentColors, hswapAlpha] using hmv
        have hstablePredNext : StableColoring
            (pred.series.data.tree (Fin.last (pred.rounds + 1)))
            (TashkinovStoredColors pred.series.data (Fin.last pred.rounds))
            (pred.series.data.coloring (Fin.last pred.rounds)) undone := by
          exact hstablePred
        have hmissingPredNext : alpha ∈ TreeMissingColors undone
            (pred.series.data.tree (Fin.last (pred.rounds + 1))) := by
          exact hmissingPred
        apply htransport
        simpa [hpredNext] using
          (low undone undoneProper' undoneOne' hstablePredNext alpha beta
            (Or.inl hmissingPredNext))
