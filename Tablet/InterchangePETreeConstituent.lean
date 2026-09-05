import Tablet.BoundaryColorVertex
import Tablet.ColoredVertexSetElementary
import Tablet.CombinedStableColoring
import Tablet.DefectiveColor
import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtendedTashkinovTree
import Tablet.HierarchyBase
import Tablet.InterchangePEClosedCore
import Tablet.InterchangePECommonMissingClosed
import Tablet.InterchangePETreeAwayFromDelta
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.LooplessMultigraph
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumProperty
import Tablet.ModColoring
import Tablet.ParallelExtensionColor
import Tablet.PartialEdgeColoring
import Tablet.StableColoring
import Tablet.StableColoringBeforeVertex
import Tablet.TashkinovClosure
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent

-- [TABLET NODE: InterchangePETreeConstituent]
theorem InterchangePETreeConstituent {V E : Type*}
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
    (alpha beta : Fin k) :
    let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
    alpha ∈ TreeMissingColors sigma Tn →
      TreeInterchangeable G Tn sigma alpha beta := by
-- BODY
  dsimp
  intro halpha
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
  have hqn : q.succ = n := by
    apply Fin.ext
    simp [q, n]
    omega
  have hlast : q.succ = Fin.last ett.rounds := by
    apply Fin.ext
    simp [q]
    omega
  generalize target_eq : q.succ = target
  cases ett.series.certified target with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    exact (Fin.succ_ne_zero q target_eq).elim
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hci : ci = q := by
      apply Fin.ext
      have hv := congrArg Fin.val target_eq
      simp at hv
      omega
    subst ci
    have hp : ett.series.data.kind q.succ =
        some TashkinovExtensionKind.PE := by rw [hlast]; exact hPE
    rw [currentKind] at hp
    simp at hp
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hci : ci = q := by
      apply Fin.ext
      have hv := congrArg Fin.val target_eq
      simp at hv
      omega
    subst ci
    have hp : ett.series.data.kind q.succ =
        some TashkinovExtensionKind.PE := by rw [hlast]; exact hPE
    rw [currentKind] at hp
    simp at hp
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
    have hci : ci = q := by
      apply Fin.ext
      have hv := congrArg Fin.val target_eq
      simp at hv
      omega
    subst ci
    have hsupport : ett.series.data.chosenVertex n = some choice.vertex := by
      rw [← hqn]
      exact currentVertex
    have hgamma : ett.series.data.gamma n = some gamma := by
      rw [← hqn]
      exact currentGamma
    have hdel : ett.series.data.delta n = some choice.color := by
      rw [← hqn]
      exact currentDelta
    have hPE' : ett.series.data.kind n =
        some TashkinovExtensionKind.PE := by
      change ett.series.data.kind (Fin.last ett.rounds) = _
      exact hPE
    have sharedCore : choice.color ∈ TreeMissingColors sigma base.core ∧
        TreeColorSetClosed G sigma base.core {choice.color} := by
      have hgm : gamma ∈ MissingColors G secondStable choice.vertex := by
        exact (secondStableRelation.2 choice.vertex choice.vertexDefective.1).symm ▸ gammaRule.1
      have hse : secondStable choice.edge = some choice.color := by
        have hs := secondStableRelation.1 choice.edge
          ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
          ⟨choice.color, Finset.mem_union_right _ (Finset.mem_insert_self _ _),
            choice.edgeColor⟩
        exact hs.trans choice.edgeColor
      have hdn : choice.color ∉ MissingColors G secondStable choice.vertex := by
        intro hm
        have hp : choice.color ∈ PresentColors G secondStable choice.vertex := by
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨choice.edge, choice.edgeIncident, hse⟩
        have hn : choice.color ∉ PresentColors G secondStable choice.vertex := by
          simpa [MissingColors] using hm
        exact hn hp
      have hswap : choice.color ∈ MissingColors G
          (TwoColorComponentSwap G secondStable gamma choice.color
            (Sum.inl choice.vertex)) choice.vertex := by
        unfold MissingColors
        simp only [Finset.mem_sdiff]
        constructor
        · exact Finset.mem_univ _
        · intro hp
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          rcases hp with ⟨e, he, hec⟩
          have heold : secondStable e = some gamma ∨
              secondStable e = some choice.color := by
            by_cases hc : Sum.inr e ∈ TwoColorComponent G secondStable gamma choice.color
              (Sum.inl choice.vertex)
            · simp [TwoColorComponentSwap, hc] at hec
              by_cases hg : secondStable e = some gamma
              · exact Or.inl hg
              · by_cases hd : secondStable e = some choice.color
                · exact Or.inr hd
                · simp [hg, hd] at hec
            · right
              simpa [TwoColorComponentSwap, hc] using hec
          have heK : Sum.inr e ∈ TwoColorComponent G secondStable gamma choice.color
              (Sum.inl choice.vertex) := by
            change (TwoColorIncidenceGraph G secondStable gamma choice.color).connectedComponentMk
              (Sum.inr e) = (TwoColorIncidenceGraph G secondStable gamma choice.color).connectedComponentMk
              (Sum.inl choice.vertex)
            rcases heold with hg | hd
            · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                (by simp [TwoColorIncidenceGraph, he, hg])
            · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                (by simp [TwoColorIncidenceGraph, he, hd])
          have hneq : gamma ≠ choice.color := by
            intro heq
            have hgp : gamma ∈ PresentColors G secondStable choice.vertex := by
              simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨choice.edge, choice.edgeIncident, heq ▸ hse⟩
            have hnot : gamma ∉ PresentColors G secondStable choice.vertex := by
              simpa [MissingColors] using hgm
            exact hnot hgp
          have hgp : gamma ∈ PresentColors G secondStable choice.vertex := by
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
            rcases heold with heold | heold
            · exact ⟨e, he, heold⟩
            · exfalso
              have hs : TwoColorComponentSwap G secondStable gamma choice.color
                  (Sum.inl choice.vertex) e = some gamma := by
                simp [TwoColorComponentSwap, heK, heold]
              exact hneq (Option.some.inj (hs.symm.trans hec))
          have hnot : gamma ∉ PresentColors G secondStable choice.vertex := by
            simpa [MissingColors] using hgm
          exact hnot hgp
      have hgen : choice.color ∈ MissingColors G generating choice.vertex := by
        have hcur : ett.series.data.coloring n =
            TwoColorComponentSwap G secondStable gamma choice.color
              (Sum.inl choice.vertex) := by
          rw [← hqn]
      
          exact currentColoring
        have hcur' : ett.series.data.coloring (Fin.last ett.rounds) =
            TwoColorComponentSwap G secondStable gamma choice.color
              (Sum.inl choice.vertex) := by
          rw [← hlast]
          exact currentColoring
        apply (congrArg (fun c => choice.color ∈ MissingColors G c choice.vertex)
          ett.generatingColoring).mpr
        apply (congrArg (fun c => choice.color ∈ MissingColors G c choice.vertex)
          hcur').mpr
        exact hswap
      have hvt : choice.vertex ∈ TreeSequenceVertexSet
          (ett.series.data.tree n.castSucc) := by
        simpa [hqn] using choice.vertexDefective.1
      have hdt : choice.color ∈ TreeMissingColors sigma
          (ett.series.data.tree n.castSucc) := by
        simp only [TreeMissingColors, Finset.mem_biUnion]
        exact ⟨choice.vertex, hvt, (hstable.1.2 choice.vertex hvt).symm ▸ hgen⟩
      have hdtcore : choice.color ∈ TreeMissingColors sigma base.core := by
        obtain ⟨unionData⟩ := (base.parallel hPE).2.2
        simp only [TreeMissingColors, Finset.mem_biUnion]
        refine ⟨choice.vertex, ?_, ?_⟩
        · rw [unionData.vertexSet]
          apply Finset.mem_union_left
          simpa [n] using hvt
        · exact (hstable.1.2 choice.vertex hvt).symm ▸ hgen
      have hcore : TreeColorSetClosed G sigma base.core {choice.color} := by
        apply InterchangePECommonMissingClosed G k e0 input T generating sigma ett
          hMP hpositive hlower hPE' base hproper hone hstable choice.color
        · exact hdt
        · have augmentSubset : ∀ {A B : TreeSequence G e0},
              TashkinovAugmentationSequence generating A B →
              TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
            intro A B hab
            have initialSubset : ∀ {C D : TreeSequence G e0},
                TreeSequenceInitialSegment C D →
                TreeSequenceVertexSet C ⊆ TreeSequenceVertexSet D := by
              intro C D hCD x hx
              unfold TreeSequenceVertexSet at hx ⊢
              simp only [Finset.mem_image] at hx ⊢
              obtain ⟨i, hi, rfl⟩ := hx
              obtain ⟨hlen, hvertices, hedges⟩ := hCD
              exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i,
                Finset.mem_univ _, hvertices i⟩
            unfold TashkinovAugmentationSequence at hab
            induction hab using Relation.ReflTransGen.head_induction_on with
            | refl => exact fun x hx => hx
            | head hstep htail ih =>
              intro x hx
              exact ih (initialSubset hstep.2.1 hx)
          obtain ⟨unionData⟩ := (base.parallel hPE).2.2
          have prefixSubset : TreeSequenceVertexSet
              (TreeSequencePrefix
                (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                base.supportPosition.val base.supportPositive
                (Nat.le_of_lt_succ base.supportPosition.isLt)) ⊆
              TreeSequenceVertexSet base.closure := by
            exact augmentSubset (base.parallel hPE).2.1.1
          have hprefix : choice.vertex ∈ TreeSequenceVertexSet
              (TreeSequencePrefix
                (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                base.supportPosition.val base.supportPositive
                (Nat.le_of_lt_succ base.supportPosition.isLt)) := by
            simp only [TreeSequenceVertexSet, Finset.mem_image]
            refine ⟨⟨base.supportPosition.val, Nat.lt_succ_self _⟩, Finset.mem_univ _, ?_⟩
            change (ett.series.data.tree (Fin.last ett.rounds).castSucc).vertex base.supportPosition = _
            have cv : ett.series.data.chosenVertex (Fin.last ett.rounds) =
                some choice.vertex := by
              rw [← hlast]
              exact currentVertex
            exact Option.some.inj ((base.parallel hPE).1.symm.trans cv)
          have hclosureVertex : choice.vertex ∈ TreeSequenceVertexSet base.closure :=
            prefixSubset hprefix
          have hdc : choice.color ∈ TreeMissingColors sigma base.closure := by
            simp only [TreeMissingColors, Finset.mem_biUnion]
            exact ⟨choice.vertex, hclosureVertex,
              (hstable.2.2 choice.vertex hclosureVertex).symm ▸ hgen⟩
          exact hdc
      exact ⟨hdtcore, hcore⟩
    by_cases ha : alpha = choice.color
    · have hgm : gamma ∈ MissingColors G secondStable choice.vertex := by
        exact (secondStableRelation.2 choice.vertex choice.vertexDefective.1).symm ▸ gammaRule.1
      have hse : secondStable choice.edge = some choice.color := by
        have hs := secondStableRelation.1 choice.edge
          ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
          ⟨choice.color, Finset.mem_union_right _ (Finset.mem_insert_self _ _),
            choice.edgeColor⟩
        exact hs.trans choice.edgeColor
      have hdn : choice.color ∉ MissingColors G secondStable choice.vertex := by
        intro hm
        have hp : choice.color ∈ PresentColors G secondStable choice.vertex := by
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨choice.edge, choice.edgeIncident, hse⟩
        have hn : choice.color ∉ PresentColors G secondStable choice.vertex := by
          simpa [MissingColors] using hm
        exact hn hp
      have hswap : choice.color ∈ MissingColors G
          (TwoColorComponentSwap G secondStable gamma choice.color
            (Sum.inl choice.vertex)) choice.vertex := by
        unfold MissingColors
        simp only [Finset.mem_sdiff]
        constructor
        · exact Finset.mem_univ _
        · intro hp
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          rcases hp with ⟨e, he, hec⟩
          have heold : secondStable e = some gamma ∨
              secondStable e = some choice.color := by
            by_cases hc : Sum.inr e ∈ TwoColorComponent G secondStable gamma choice.color
              (Sum.inl choice.vertex)
            · simp [TwoColorComponentSwap, hc] at hec
              by_cases hg : secondStable e = some gamma
              · exact Or.inl hg
              · by_cases hd : secondStable e = some choice.color
                · exact Or.inr hd
                · simp [hg, hd] at hec
            · right
              simpa [TwoColorComponentSwap, hc] using hec
          have heK : Sum.inr e ∈ TwoColorComponent G secondStable gamma choice.color
              (Sum.inl choice.vertex) := by
            change (TwoColorIncidenceGraph G secondStable gamma choice.color).connectedComponentMk
              (Sum.inr e) = (TwoColorIncidenceGraph G secondStable gamma choice.color).connectedComponentMk
              (Sum.inl choice.vertex)
            rcases heold with hg | hd
            · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                (by simp [TwoColorIncidenceGraph, he, hg])
            · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                (by simp [TwoColorIncidenceGraph, he, hd])
          have hneq : gamma ≠ choice.color := by
            intro heq
            have hgp : gamma ∈ PresentColors G secondStable choice.vertex := by
              simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨choice.edge, choice.edgeIncident, heq ▸ hse⟩
            have hnot : gamma ∉ PresentColors G secondStable choice.vertex := by
              simpa [MissingColors] using hgm
            exact hnot hgp
          have hgp : gamma ∈ PresentColors G secondStable choice.vertex := by
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
            rcases heold with heold | heold
            · exact ⟨e, he, heold⟩
            · exfalso
              have hs : TwoColorComponentSwap G secondStable gamma choice.color
                  (Sum.inl choice.vertex) e = some gamma := by
                simp [TwoColorComponentSwap, heK, heold]
              exact hneq (Option.some.inj (hs.symm.trans hec))
          have hnot : gamma ∉ PresentColors G secondStable choice.vertex := by
            simpa [MissingColors] using hgm
          exact hnot hgp
      have hgen : choice.color ∈ MissingColors G generating choice.vertex := by
        have hcur : ett.series.data.coloring n =
            TwoColorComponentSwap G secondStable gamma choice.color
              (Sum.inl choice.vertex) := by
          rw [← hqn]
          exact currentColoring
        have hcur' : ett.series.data.coloring (Fin.last ett.rounds) =
            TwoColorComponentSwap G secondStable gamma choice.color
              (Sum.inl choice.vertex) := by
          rw [← hlast]
          exact currentColoring
        apply (congrArg (fun c => choice.color ∈ MissingColors G c choice.vertex)
          ett.generatingColoring).mpr
        apply (congrArg (fun c => choice.color ∈ MissingColors G c choice.vertex)
          hcur').mpr
        exact hswap
      have hvt : choice.vertex ∈ TreeSequenceVertexSet
          (ett.series.data.tree n.castSucc) := by
        simpa [hqn] using choice.vertexDefective.1
      have hdt : choice.color ∈ TreeMissingColors sigma
          (ett.series.data.tree n.castSucc) := by
        simp only [TreeMissingColors, Finset.mem_biUnion]
        exact ⟨choice.vertex, hvt, (hstable.1.2 choice.vertex hvt).symm ▸ hgen⟩
      have hdtcore : choice.color ∈ TreeMissingColors sigma base.core := by
        obtain ⟨unionData⟩ := (base.parallel hPE).2.2
        simp only [TreeMissingColors, Finset.mem_biUnion]
        refine ⟨choice.vertex, ?_, ?_⟩
        · rw [unionData.vertexSet]
          apply Finset.mem_union_left
          simpa [n] using hvt
        · exact (hstable.1.2 choice.vertex hvt).symm ▸ hgen
      have hcore : TreeColorSetClosed G sigma base.core {choice.color} := by
        apply InterchangePECommonMissingClosed G k e0 input T generating sigma ett
          hMP hpositive hlower hPE' base hproper hone hstable choice.color
        · exact hdt
        · have augmentSubset : ∀ {A B : TreeSequence G e0},
              TashkinovAugmentationSequence generating A B →
              TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
            intro A B hab
            have initialSubset : ∀ {C D : TreeSequence G e0},
                TreeSequenceInitialSegment C D →
                TreeSequenceVertexSet C ⊆ TreeSequenceVertexSet D := by
              intro C D hCD x hx
              unfold TreeSequenceVertexSet at hx ⊢
              simp only [Finset.mem_image] at hx ⊢
              obtain ⟨i, hi, rfl⟩ := hx
              obtain ⟨hlen, hvertices, hedges⟩ := hCD
              exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i,
                Finset.mem_univ _, hvertices i⟩
            unfold TashkinovAugmentationSequence at hab
            induction hab using Relation.ReflTransGen.head_induction_on with
            | refl => exact fun x hx => hx
            | head hstep htail ih =>
              intro x hx
              exact ih (initialSubset hstep.2.1 hx)
          obtain ⟨unionData⟩ := (base.parallel hPE).2.2
          have prefixSubset : TreeSequenceVertexSet
              (TreeSequencePrefix
                (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                base.supportPosition.val base.supportPositive
                (Nat.le_of_lt_succ base.supportPosition.isLt)) ⊆
              TreeSequenceVertexSet base.closure := by
            exact augmentSubset (base.parallel hPE).2.1.1
          have hprefix : choice.vertex ∈ TreeSequenceVertexSet
              (TreeSequencePrefix
                (ett.series.data.tree (Fin.last ett.rounds).castSucc)
                base.supportPosition.val base.supportPositive
                (Nat.le_of_lt_succ base.supportPosition.isLt)) := by
            simp only [TreeSequenceVertexSet, Finset.mem_image]
            refine ⟨⟨base.supportPosition.val, Nat.lt_succ_self _⟩, Finset.mem_univ _, ?_⟩
            change (ett.series.data.tree (Fin.last ett.rounds).castSucc).vertex base.supportPosition = _
            have cv : ett.series.data.chosenVertex (Fin.last ett.rounds) =
                some choice.vertex := by
              rw [← hlast]
              exact currentVertex
            exact Option.some.inj ((base.parallel hPE).1.symm.trans cv)
          have hclosureVertex : choice.vertex ∈ TreeSequenceVertexSet base.closure :=
            prefixSubset hprefix
          have hdc : choice.color ∈ TreeMissingColors sigma base.closure := by
            simp only [TreeMissingColors, Finset.mem_biUnion]
            exact ⟨choice.vertex, hclosureVertex,
              (hstable.2.2 choice.vertex hclosureVertex).symm ▸ hgen⟩
          exact hdc
      subst alpha
      have hci := InterchangePEClosedCore G k e0 input T generating sigma ett hMP
        hpositive hlower hPE' base hproper hone hstable choice.color beta hdtcore hcore
      have hsub : TreeSequenceVertexSet
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) ⊆
          TreeSequenceVertexSet base.core := by
        obtain ⟨unionData⟩ := (base.parallel hPE).2.2
        intro v hv
        rw [unionData.vertexSet]
        exact Finset.mem_union_left _ hv
      unfold TreeInterchangeable at hci ⊢
      intro z w hz hw hzT hwT
      apply hci z w hz hw
      · obtain ⟨v, hv, hvc⟩ := hzT
        exact ⟨v, hsub hv, hvc⟩
      · obtain ⟨v, hv, hvc⟩ := hwT
        exact ⟨v, hsub hv, hvc⟩
    by_cases hb : beta = choice.color
    · subst beta
      have hci := InterchangePEClosedCore G k e0 input T generating sigma ett hMP
        hpositive hlower hPE' base hproper hone hstable choice.color alpha
        sharedCore.1 sharedCore.2
      have graphSwap : TwoColorIncidenceGraph G sigma alpha choice.color =
          TwoColorIncidenceGraph G sigma choice.color alpha := by
        ext x y
        cases x <;> cases y <;> simp [TwoColorIncidenceGraph, or_comm]
      have componentSwap (z : Sum V E) :
          TwoColorComponent G sigma alpha choice.color z =
            TwoColorComponent G sigma choice.color alpha z := by
        unfold TwoColorComponent
        rw [graphSwap]
      have pathSwap (z : Sum V E) :
          TwoColorPathComponent G sigma alpha choice.color z →
            TwoColorPathComponent G sigma choice.color alpha z := by
        intro hz
        rcases hz with ⟨hne, x, hx, hs⟩
        refine ⟨hne.symm, x, ?_, ?_⟩
        · exact (congrArg (fun s : Set (Sum V E) => x ∈ s)
            (componentSwap z)).mp hx
        · exact (congrArg (fun g : SimpleGraph (Sum V E) =>
            Set.Subsingleton (g.neighborSet x)) graphSwap).mp hs
      have hsub : TreeSequenceVertexSet
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) ⊆
          TreeSequenceVertexSet base.core := by
        obtain ⟨unionData⟩ := (base.parallel hPE).2.2
        intro v hv
        rw [unionData.vertexSet]
        exact Finset.mem_union_left _ hv
      have hreverse : TreeInterchangeable G base.core sigma alpha choice.color := by
        unfold TreeInterchangeable at hci ⊢
        intro z w hz hw hzT hwT
        have hz' : ∃ v ∈ TreeSequenceVertexSet base.core,
            Sum.inl v ∈ TwoColorComponent G sigma choice.color alpha z := by
          obtain ⟨v, hv, hvc⟩ := hzT
          exact ⟨v, hv, componentSwap z ▸ hvc⟩
        have hw' : ∃ v ∈ TreeSequenceVertexSet base.core,
            Sum.inl v ∈ TwoColorComponent G sigma choice.color alpha w := by
          obtain ⟨v, hv, hvc⟩ := hwT
          exact ⟨v, hv, componentSwap w ▸ hvc⟩
        exact (componentSwap z).trans
          ((hci z w (pathSwap z hz) (pathSwap w hw) hz' hw').trans
            (componentSwap w).symm)
      unfold TreeInterchangeable at hreverse ⊢
      intro z w hz hw hzT hwT
      apply hreverse z w hz hw
      · obtain ⟨v, hv, hvc⟩ := hzT
        exact ⟨v, hsub hv, hvc⟩
      · obtain ⟨v, hv, hvc⟩ := hwT
        exact ⟨v, hsub hv, hvc⟩
    exact InterchangePETreeAwayFromDelta G k e0 input T generating sigma ett
      hMP hpositive hlower hPE' base hproper hone hstable choice.vertex gamma
      choice.color alpha beta (by simpa [n] using hsupport)
      (by simpa [n] using hgamma) (by simpa [n] using hdel) halpha ha hb
