import Tablet.AlgorithmThreeOneChoiceDataExists
import Tablet.ParallelExtensionColorAppend
import Tablet.RevisitingExtensionCertificateAppend
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.TashkinovClosureExists
import Tablet.TashkinovSeriesAppend
import Tablet.TashkinovStoredColorsAppend
import Tablet.TreeExitComponentMeetsTreeOnlyAtExit
import Tablet.TreeSequenceBoundaryEdgeAppendExists
import Tablet.TwoColorComponentSwapProper

open scoped Sym2

-- [TABLET NODE: AlgorithmThreeOneStepExists]
theorem AlgorithmThreeOneStepExists {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k rounds : Nat) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input)
    (hdegree : MaximumDegree G + 1 ≤ k)
    (hproper : IsProperEdgeColoring G
      (series.data.coloring (Fin.last rounds)))
    (hone : IsOneEdgeUncolored
      (series.data.coloring (Fin.last rounds)) e0)
    (hclosed : ColoredVertexSetClosed G
      (series.data.coloring (Fin.last rounds))
      (TreeSequenceVertexSet (series.data.tree (Fin.last (rounds + 1)))))
    (hnotStrong : ¬ ColoredVertexSetStronglyClosed G
      (series.data.coloring (Fin.last rounds))
      (TreeSequenceVertexSet (series.data.tree (Fin.last (rounds + 1))))) :
    ∃ (newTree : TreeSequence G e0)
      (newColoring : PartialEdgeColoring E k)
      (newStored : Finset (Fin k)) (newConnectingEdges : Finset E)
      (newKind : Option TashkinovExtensionKind)
      (newChosenVertex newOutsideVertex : Option V)
      (newDelta newGamma : Option (Fin k))
      (extended : TashkinovSeries G k (rounds + 1) e0 input),
      extended.data = TashkinovSeriesDataAppend series.data newTree
        newColoring newStored newConnectingEdges newKind newChosenVertex
        newOutsideVertex newDelta newGamma ∧
      (series.data.tree (Fin.last (rounds + 1))).length < newTree.length := by
-- BODY
  classical
  let i : Fin (rounds + 1) := Fin.last rounds
  let T := series.data.tree i.succ
  have hiColor : series.data.coloring i =
      series.data.coloring (Fin.last rounds) := by rfl
  have hiTree : series.data.tree i.succ =
      series.data.tree (Fin.last (rounds + 1)) := by
    congr 1
  have proper : IsProperEdgeColoring G (series.data.coloring i) := by
    simpa [hiColor] using hproper
  have one : IsOneEdgeUncolored (series.data.coloring i) e0 := by
    simpa [hiColor] using hone
  have closed : ColoredVertexSetClosed G (series.data.coloring i)
      (TreeSequenceVertexSet T) := by
    change ColoredVertexSetClosed G
      (series.data.coloring (Fin.last rounds))
      (TreeSequenceVertexSet (series.data.tree (Fin.last (rounds + 1))))
    exact hclosed
  have notStrong : ¬ ColoredVertexSetStronglyClosed G
      (series.data.coloring i) (TreeSequenceVertexSet T) := by
    simpa [T, hiColor, hiTree] using hnotStrong
  have segmentTrans : ∀ (A B C : TreeSequence G e0),
      TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B C →
        TreeSequenceInitialSegment A C := by
    intro A B C hab hbc
    rcases hab with ⟨hab, hvab, heab⟩
    rcases hbc with ⟨hbc, hvbc, hebc⟩
    refine ⟨Nat.le_trans hab hbc, ?_, ?_⟩
    · intro j
      calc
        C.vertex (Fin.castLE (Nat.succ_le_succ (Nat.le_trans hab hbc)) j) =
            C.vertex (Fin.castLE (Nat.succ_le_succ hbc)
              (Fin.castLE (Nat.succ_le_succ hab) j)) := by congr 1
        _ = B.vertex (Fin.castLE (Nat.succ_le_succ hab) j) := hvbc _
        _ = A.vertex j := hvab _
    · intro j
      calc
        C.edge (Fin.castLE (Nat.le_trans hab hbc) j) =
            C.edge (Fin.castLE hbc (Fin.castLE hab j)) := by congr 1
        _ = B.edge (Fin.castLE hab j) := hebc _
        _ = A.edge j := heab _
  rcases AlgorithmThreeOneChoiceDataExists G k rounds e0 input series i
      hdegree proper one closed notStrong with revisiting | seriesOrParallel
  · obtain ⟨cert⟩ := revisiting
    obtain ⟨adjoined, hadjoined⟩ := TreeSequenceBoundaryEdgeAppendExists
      T cert.edge (by simpa [T] using cert.edgeBoundary)
    obtain ⟨newTree, hclosure⟩ :=
      TashkinovClosureExists (series.data.coloring i) adjoined
    have hclosureSegment : TreeSequenceInitialSegment adjoined newTree :=
      TashkinovAugmentationSequenceInitialSegment _ _ _ hclosure.1
    have hordered : TreeSequenceInitialSegment T newTree :=
      segmentTrans T adjoined newTree hadjoined.2.1 hclosureSegment
    have hstrict : T.length < newTree.length := by
      rcases hadjoined with ⟨hlen, hadjoined⟩
      have hle := hclosureSegment.1
      omega
    let newColoring := series.data.coloring i
    let newStored : Finset (Fin k) := {cert.delta, cert.gamma}
    let newEdges : Finset E := {cert.edge}
    let newKind := some TashkinovExtensionKind.RE
    let newVertex := some cert.insideEndpoint
    let newOutside := some cert.outsideEndpoint
    let newDelta := some cert.delta
    let newGamma := some cert.gamma
    let appended := TashkinovSeriesDataAppend series.data newTree newColoring
      newStored newEdges newKind newVertex newOutside newDelta newGamma
    obtain ⟨newCert, hgamma, hdelta, hedge, hins, hout⟩ :=
      (RevisitingExtensionCertificateAppend series.data newTree newColoring
        newStored newEdges newKind newVertex newOutside newDelta newGamma i).2 cert
    have lastStep : TashkinovSeriesStep G k (rounds + 1) e0 input appended
        (Fin.last (rounds + 1)) := by
      have hlast : i.succ = Fin.last (rounds + 1) := by ext; simp [i]
      rw [← hlast]
      apply TashkinovSeriesStep.RE (i := i) (available := newCert)
        (adjoined := adjoined)
      · simpa [appended, TashkinovSeriesDataAppend, i] using proper
      · simpa [appended, TashkinovSeriesDataAppend, i] using one
      · simp only [appended, TashkinovSeriesDataAppend,
          Fin.lastCases_castSucc]
        exact closed
      · simp only [appended, TashkinovSeriesDataAppend,
          Fin.lastCases_castSucc]
        exact notStrong
      · simp [appended, TashkinovSeriesDataAppend, newColoring, i]
      · simp [appended, TashkinovSeriesDataAppend, newStored, hdelta, hgamma, i]
      · simp [appended, TashkinovSeriesDataAppend, newEdges, hedge, i]
      · simp [appended, TashkinovSeriesDataAppend, newKind, i]
      · simp [appended, TashkinovSeriesDataAppend, newVertex, hins, i]
      · simp [appended, TashkinovSeriesDataAppend, newOutside, hout, i]
      · simp [appended, TashkinovSeriesDataAppend, newDelta, hdelta, i]
      · simp [appended, TashkinovSeriesDataAppend, newGamma, hgamma, i]
      · simpa [appended, TashkinovSeriesDataAppend, T, hedge, i] using hadjoined
      · simpa [appended, TashkinovSeriesDataAppend, newColoring, i] using hclosure
      · simpa [appended, TashkinovSeriesDataAppend, T, i] using hordered
      · simpa [appended, TashkinovSeriesDataAppend, T, i] using hstrict
    obtain ⟨extended, hextended⟩ := TashkinovSeriesAppend G k rounds e0 input
      series newTree newColoring newStored newEdges newKind newVertex newOutside
      newDelta newGamma lastStep
    refine ⟨newTree, newColoring, newStored, newEdges, newKind, newVertex,
      newOutside, newDelta, newGamma, extended, hextended, ?_⟩
    simpa [T, hiTree] using hstrict
  · rcases seriesOrParallel with seriesCase | parallelCase
    · rcases seriesCase with ⟨noRevisiting, choice, seriesAlternative⟩
      have hedgeBoundary : choice.edge ∈ BoundaryEdges G (TreeSequenceVertexSet T) := by
        rcases choice.edgeDefective with ⟨c, hcdef, hcmem⟩
        exact (Finset.mem_filter.mp hcmem).1
      obtain ⟨adjoined, hadjoined⟩ := TreeSequenceBoundaryEdgeAppendExists
        T choice.edge hedgeBoundary
      obtain ⟨newTree, hclosure⟩ :=
        TashkinovClosureExists choice.selected adjoined
      have hclosureSegment : TreeSequenceInitialSegment adjoined newTree :=
        TashkinovAugmentationSequenceInitialSegment _ _ _ hclosure.1
      have hordered : TreeSequenceInitialSegment T newTree :=
        segmentTrans T adjoined newTree hadjoined.2.1 hclosureSegment
      have hstrict : T.length < newTree.length := by
        rcases hadjoined with ⟨hlen, hadjoined⟩
        have hle := hclosureSegment.1
        omega
      let newColoring := choice.selected
      let newStored : Finset (Fin k) := {choice.color}
      let newEdges : Finset E := {choice.edge}
      let newKind := some TashkinovExtensionKind.SE
      let newVertex := some choice.vertex
      let newOutside := some choice.otherEndpoint
      let newDelta := some choice.color
      let newGamma : Option (Fin k) := none
      let appended := TashkinovSeriesDataAppend series.data newTree newColoring
        newStored newEdges newKind newVertex newOutside newDelta newGamma
      have storedEq : TashkinovStoredColors appended i.castSucc =
          TashkinovStoredColors series.data i := by
        exact TashkinovStoredColorsAppend series.data newTree newColoring
          newStored newEdges newKind newVertex newOutside newDelta newGamma i
      let newChoice : MaximumDefectiveChoice G e0
          (appended.tree i.succ.castSucc)
          (TashkinovStoredColors appended i.castSucc)
          (appended.coloring i.castSucc) := {
        selected := choice.selected
        selectedProper := choice.selectedProper
        selectedOneUncolored := choice.selectedOneUncolored
        selectedStable := by
          rw [storedEq]
          simpa only [appended, TashkinovSeriesDataAppend,
            Fin.lastCases_castSucc] using choice.selectedStable
        vertex := choice.vertex
        vertexDefective := by
          simpa only [appended, TashkinovSeriesDataAppend,
            Fin.lastCases_castSucc] using choice.vertexDefective
        maximal := by
          rw [storedEq]
          simpa only [appended, TashkinovSeriesDataAppend,
            Fin.lastCases_castSucc] using choice.maximal
        edge := choice.edge
        edgeDefective := by
          simpa only [appended, TashkinovSeriesDataAppend,
            Fin.lastCases_castSucc] using choice.edgeDefective
        edgeIncident := choice.edgeIncident
        otherEndpoint := choice.otherEndpoint
        otherOutside := by
          simpa only [appended, TashkinovSeriesDataAppend,
            Fin.lastCases_castSucc] using choice.otherOutside
        edgeEnds := choice.edgeEnds
        color := choice.color
        edgeColor := choice.edgeColor }
      have newNoRevisiting : ¬ Nonempty
          (RevisitingExtensionCertificate appended i.castSucc) := by
        rintro ⟨newCert⟩
        obtain ⟨oldCert, hgamma, hdelta, hedge, hins, hout⟩ :=
          (RevisitingExtensionCertificateAppend series.data newTree newColoring
            newStored newEdges newKind newVertex newOutside newDelta newGamma i).1
            newCert
        exact noRevisiting ⟨oldCert⟩
      have newSeriesAlternative : ∀ pi : PartialEdgeColoring E k,
          IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
          StableColoring (appended.tree i.succ.castSucc)
            (insert newChoice.color (TashkinovStoredColors appended i.castSucc))
            newChoice.selected pi →
          Disjoint (MissingColors G pi newChoice.otherEndpoint)
            (TreeMissingColors pi (appended.tree i.succ.castSucc)) := by
        intro pi piProper piOne piStable
        have result := seriesAlternative pi piProper piOne
        change StableColoring (appended.tree i.succ.castSucc)
          (insert choice.color (TashkinovStoredColors appended i.castSucc))
          choice.selected pi at piStable
        rw [storedEq] at piStable
        have oldStable : StableColoring (series.data.tree i.succ)
            (insert choice.color (TashkinovStoredColors series.data i))
            choice.selected pi := by
          simpa only [appended, TashkinovSeriesDataAppend,
            Fin.lastCases_castSucc] using piStable
        simpa only [newChoice, appended, TashkinovSeriesDataAppend,
          Fin.lastCases_castSucc] using result oldStable
      have lastStep : TashkinovSeriesStep G k (rounds + 1) e0 input appended
          (Fin.last (rounds + 1)) := by
        have hlast : i.succ = Fin.last (rounds + 1) := by ext; simp [i]
        rw [← hlast]
        apply TashkinovSeriesStep.SE (i := i) (choice := newChoice)
          (adjoined := adjoined)
        · simpa [appended, TashkinovSeriesDataAppend, i] using proper
        · simpa [appended, TashkinovSeriesDataAppend, i] using one
        · simp only [appended, TashkinovSeriesDataAppend,
            Fin.lastCases_castSucc]
          exact closed
        · simp only [appended, TashkinovSeriesDataAppend,
            Fin.lastCases_castSucc]
          exact notStrong
        · exact newNoRevisiting
        · exact newSeriesAlternative
        · simp [appended, TashkinovSeriesDataAppend, newColoring, newChoice, i]
        · simp [appended, TashkinovSeriesDataAppend, newStored, newChoice, i]
        · simp [appended, TashkinovSeriesDataAppend, newEdges, newChoice, i]
        · simp [appended, TashkinovSeriesDataAppend, newKind, i]
        · simp [appended, TashkinovSeriesDataAppend, newVertex, newChoice, i]
        · simp [appended, TashkinovSeriesDataAppend, newOutside, newChoice, i]
        · simp [appended, TashkinovSeriesDataAppend, newDelta, newChoice, i]
        · simp [appended, TashkinovSeriesDataAppend, newGamma, i]
        · simpa [appended, TashkinovSeriesDataAppend, T, newChoice, i] using hadjoined
        · simpa [appended, TashkinovSeriesDataAppend, newColoring, i] using hclosure
        · simpa [appended, TashkinovSeriesDataAppend, T, i] using hordered
        · simpa [appended, TashkinovSeriesDataAppend, T, i] using hstrict
      obtain ⟨extended, hextended⟩ := TashkinovSeriesAppend G k rounds e0 input
        series newTree newColoring newStored newEdges newKind newVertex newOutside
        newDelta newGamma lastStep
      refine ⟨newTree, newColoring, newStored, newEdges, newKind, newVertex,
        newOutside, newDelta, newGamma, extended, hextended, ?_⟩
      simpa [T, hiTree] using hstrict
    · rcases parallelCase with ⟨noRevisiting, choice,
        seriesAlternativeFails, gamma, gammaRule, secondStable,
        secondStableProper, secondStableOne, secondStableRelation, exitWitness⟩
      let X := TreeSequenceVertexSet T
      have hchoiceBoundary : choice.edge ∈
          BoundaryColorEdges G choice.selected X choice.color := by
        rcases choice.edgeDefective with ⟨c, hcDefective, hcBoundary⟩
        have hcColor : choice.selected choice.edge = some c :=
          (Finset.mem_filter.mp hcBoundary).2
        have hc : c = choice.color :=
          Option.some.inj (hcColor.symm.trans choice.edgeColor)
        simpa [X, hc] using hcBoundary
      have hdefective : DefectiveColor G choice.selected X choice.color := by
        rcases choice.edgeDefective with ⟨c, hcDefective, hcBoundary⟩
        have hcColor : choice.selected choice.edge = some c :=
          (Finset.mem_filter.mp hcBoundary).2
        have hc : c = choice.color :=
          Option.some.inj (hcColor.symm.trans choice.edgeColor)
        simpa [X, hc] using hcDefective
      obtain ⟨g, hgBoundary, hgne⟩ : ∃ g,
          g ∈ BoundaryColorEdges G choice.selected X choice.color ∧
            g ≠ choice.edge := by
        obtain ⟨a, ha, b, hb, hab⟩ :=
          Finset.one_lt_card.mp (show 1 <
            (BoundaryColorEdges G choice.selected X choice.color).card by
              exact lt_of_lt_of_le Nat.one_lt_two hdefective)
        by_cases haChoice : a = choice.edge
        · exact ⟨b, hb, by
            intro hbChoice
            exact hab (haChoice.trans hbChoice.symm)⟩
        · exact ⟨a, ha, haChoice⟩
      have boundaryIncident : ∀ {f : E}, f ∈ BoundaryEdges G X →
          TreeIncidentEdge T f := by
        intro f hf
        simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
          true_and] at hf
        obtain ⟨v, hv, u, hu, hends⟩ := hf
        exact ⟨v, hv, by simpa [Incident, hends]⟩
      have hgRaw : g ∈ BoundaryEdges G X :=
        (Finset.mem_filter.mp hgBoundary).1
      have hchoiceRaw : choice.edge ∈ BoundaryEdges G X :=
        (Finset.mem_filter.mp hchoiceBoundary).1
      have hgSecond : secondStable g = some choice.color := by
        have fixed := secondStableRelation.1 g (boundaryIncident hgRaw)
          ⟨choice.color,
            Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self _ _)),
            (Finset.mem_filter.mp hgBoundary).2⟩
        exact fixed.trans (Finset.mem_filter.mp hgBoundary).2
      have hchoiceSecond : secondStable choice.edge = some choice.color := by
        have fixed := secondStableRelation.1 choice.edge
          (boundaryIncident hchoiceRaw)
          ⟨choice.color,
            Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self _ _)),
            choice.edgeColor⟩
        exact fixed.trans choice.edgeColor
      have hgammaMissing : gamma ∈ MissingColors G secondStable choice.vertex := by
        rw [secondStableRelation.2 choice.vertex choice.vertexDefective.1]
        exact gammaRule.1
      have hgammaNe : gamma ≠ choice.color := by
        intro h
        have hpresent : gamma ∈ PresentColors G secondStable choice.vertex := by
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨choice.edge, choice.edgeIncident, h ▸ hchoiceSecond⟩
        have hnot : gamma ∉ PresentColors G secondStable choice.vertex := by
          simpa [MissingColors] using hgammaMissing
        exact hnot hpresent
      have hgOutside : Sum.inr g ∉
          TwoColorComponent G secondStable gamma choice.color
            (Sum.inl choice.vertex) := by
        intro hgComponent
        rcases (Finset.mem_filter.mp hgBoundary).1 with hgRaw'
        simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
          true_and] at hgRaw'
        obtain ⟨w, hw, u, hu, hends⟩ := hgRaw'
        have hwIncident : Incident G w g := by
          simpa [Incident, hends]
        have hwComponent : Sum.inl w ∈
            TwoColorComponent G secondStable gamma choice.color
              (Sum.inl choice.vertex) := by
          change (TwoColorIncidenceGraph G secondStable gamma choice.color).connectedComponentMk
              (Sum.inl w) =
            (TwoColorIncidenceGraph G secondStable gamma choice.color).connectedComponentMk
              (Sum.inl choice.vertex)
          exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            (by simp [TwoColorIncidenceGraph, hwIncident, hgSecond])).trans hgComponent
        have hwEq := (TreeExitComponentMeetsTreeOnlyAtExit T secondStable
          gamma choice.color choice.vertex secondStableProper hgammaMissing
          exitWitness w hw).mp hwComponent
        subst w
        exact (secondStableProper hgne
          ⟨choice.vertex, hwIncident, choice.edgeIncident⟩ hgSecond)
          hchoiceSecond
      let newColoring := TwoColorComponentSwap G secondStable gamma choice.color
        (Sum.inl choice.vertex)
      have hgCurrent : newColoring g = some choice.color := by
        simp [newColoring, TwoColorComponentSwap, hgOutside, hgSecond]
      have currentProper : IsProperEdgeColoring G newColoring := by
        exact TwoColorComponentSwapProper G secondStable gamma choice.color
          hgammaNe secondStableProper (Sum.inl choice.vertex)
      have currentOne : IsOneEdgeUncolored newColoring e0 := by
        unfold IsOneEdgeUncolored
        constructor
        · simp [newColoring, TwoColorComponentSwap, secondStableOne.1]
        · intro f hf
          obtain ⟨c, hc⟩ := secondStableOne.2 f hf
          by_cases hcomponent : Sum.inr f ∈
              TwoColorComponent G secondStable gamma choice.color
                (Sum.inl choice.vertex)
          · by_cases hcg : c = gamma
            · exact ⟨choice.color, by
                simp [newColoring, TwoColorComponentSwap, hcomponent, hc, hcg]⟩
            · by_cases hcd : c = choice.color
              · exact ⟨gamma, by
                  simp [newColoring, TwoColorComponentSwap, hcomponent, hc,
                    hcg, hcd]⟩
              · exact ⟨c, by
                  simp [newColoring, TwoColorComponentSwap, hcomponent, hc,
                    hcg, hcd]⟩
          · exact ⟨c, by
              simpa [newColoring, TwoColorComponentSwap, hcomponent] using hc⟩
      have hdeltaMissing : choice.color ∈
          MissingColors G newColoring choice.vertex := by
        unfold MissingColors
        simp only [Finset.mem_sdiff]
        constructor
        · exact Finset.mem_univ _
        · intro hpresent
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
            true_and] at hpresent
          rcases hpresent with ⟨f, hfIncident, hfCurrent⟩
          have hfOld : secondStable f = some gamma ∨
              secondStable f = some choice.color := by
            by_cases hfComponent : Sum.inr f ∈
                TwoColorComponent G secondStable gamma choice.color
                  (Sum.inl choice.vertex)
            · simp [newColoring, TwoColorComponentSwap, hfComponent] at hfCurrent
              by_cases hfg : secondStable f = some gamma
              · exact Or.inl hfg
              · by_cases hfd : secondStable f = some choice.color
                · exact Or.inr hfd
                · simp [hfg, hfd] at hfCurrent
            · right
              simpa [newColoring, TwoColorComponentSwap, hfComponent] using hfCurrent
          have hfComponent : Sum.inr f ∈
              TwoColorComponent G secondStable gamma choice.color
                (Sum.inl choice.vertex) := by
            change (TwoColorIncidenceGraph G secondStable gamma choice.color).connectedComponentMk
                (Sum.inr f) =
              (TwoColorIncidenceGraph G secondStable gamma choice.color).connectedComponentMk
                (Sum.inl choice.vertex)
            rcases hfOld with hfg | hfd
            · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                (by simp [TwoColorIncidenceGraph, hfIncident, hfg])
            · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                (by simp [TwoColorIncidenceGraph, hfIncident, hfd])
          have hgammaPresent : gamma ∈ PresentColors G secondStable choice.vertex := by
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
            rcases hfOld with hfg | hfd
            · exact ⟨f, hfIncident, hfg⟩
            · exfalso
              have hswap : newColoring f = some gamma := by
                simp [newColoring, TwoColorComponentSwap, hfComponent, hfd]
              exact hgammaNe (Option.some.inj (hswap.symm.trans hfCurrent))
          have hgammaNotPresent : gamma ∉
              PresentColors G secondStable choice.vertex := by
            simpa [MissingColors] using hgammaMissing
          exact hgammaNotPresent hgammaPresent
      have hnotClosed : ¬ ColoredVertexSetClosed G newColoring X := by
        intro hcurrentClosed
        exact (hcurrentClosed hgRaw choice.vertexDefective.1 hgCurrent)
          hdeltaMissing
      obtain ⟨newTree, hclosure⟩ := TashkinovClosureExists newColoring T
      have hordered : TreeSequenceInitialSegment T newTree :=
        TashkinovAugmentationSequenceInitialSegment _ _ _ hclosure.1
      have hstrict : T.length < newTree.length := by
        rcases hclosure with ⟨hreach, hnewClosed⟩
        unfold TashkinovAugmentationSequence at hreach
        cases hreach with
        | refl => exact (hnotClosed hnewClosed).elim
        | tail hprefix hlast =>
            have hsegment :=
              TashkinovAugmentationSequenceInitialSegment newColoring _ _ hprefix
            have hle := hsegment.1
            rcases hlast with ⟨hlen, hseg, hc, hcolor, hmissing⟩
            rw [hlen]
            omega
      let newStored : Finset (Fin k) := {choice.color, gamma}
      let newEdges : Finset E := {choice.edge}
      let newKind := some TashkinovExtensionKind.PE
      let newVertex := some choice.vertex
      let newOutside := some choice.otherEndpoint
      let newDelta := some choice.color
      let newGamma := some gamma
      let appended := TashkinovSeriesDataAppend series.data newTree newColoring
        newStored newEdges newKind newVertex newOutside newDelta newGamma
      have storedEq : TashkinovStoredColors appended i.castSucc =
          TashkinovStoredColors series.data i := by
        exact TashkinovStoredColorsAppend series.data newTree newColoring
          newStored newEdges newKind newVertex newOutside newDelta newGamma i
      let newChoice : MaximumDefectiveChoice G e0
          (appended.tree i.succ.castSucc)
          (TashkinovStoredColors appended i.castSucc)
          (appended.coloring i.castSucc) := {
        selected := choice.selected
        selectedProper := choice.selectedProper
        selectedOneUncolored := choice.selectedOneUncolored
        selectedStable := by
          rw [storedEq]
          simpa only [appended, TashkinovSeriesDataAppend,
            Fin.lastCases_castSucc] using choice.selectedStable
        vertex := choice.vertex
        vertexDefective := by
          simpa only [appended, TashkinovSeriesDataAppend,
            Fin.lastCases_castSucc] using choice.vertexDefective
        maximal := by
          rw [storedEq]
          simpa only [appended, TashkinovSeriesDataAppend,
            Fin.lastCases_castSucc] using choice.maximal
        edge := choice.edge
        edgeDefective := by
          simpa only [appended, TashkinovSeriesDataAppend,
            Fin.lastCases_castSucc] using choice.edgeDefective
        edgeIncident := choice.edgeIncident
        otherEndpoint := choice.otherEndpoint
        otherOutside := by
          simpa only [appended, TashkinovSeriesDataAppend,
            Fin.lastCases_castSucc] using choice.otherOutside
        edgeEnds := choice.edgeEnds
        color := choice.color
        edgeColor := choice.edgeColor }
      have newNoRevisiting : ¬ Nonempty
          (RevisitingExtensionCertificate appended i.castSucc) := by
        rintro ⟨newCert⟩
        obtain ⟨oldCert, hcertGamma, hcertDelta, hcertEdge,
            hcertInside, hcertOutside⟩ :=
          (RevisitingExtensionCertificateAppend series.data newTree newColoring
            newStored newEdges newKind newVertex newOutside newDelta newGamma i).1
            newCert
        exact noRevisiting ⟨oldCert⟩
      have newFailure : ∃ rho : PartialEdgeColoring E k,
          IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
          StableColoring (appended.tree i.succ.castSucc)
            (insert newChoice.color (TashkinovStoredColors appended i.castSucc))
            newChoice.selected rho ∧
          ¬ Disjoint (MissingColors G rho newChoice.otherEndpoint)
            (TreeMissingColors rho (appended.tree i.succ.castSucc)) := by
        obtain ⟨rho, rhoProper, rhoOne, rhoStable, rhoFailure⟩ :=
          seriesAlternativeFails
        refine ⟨rho, rhoProper, rhoOne, ?_, ?_⟩
        · change StableColoring (appended.tree i.succ.castSucc)
            (insert choice.color (TashkinovStoredColors appended i.castSucc))
            choice.selected rho
          rw [storedEq]
          simpa only [appended, TashkinovSeriesDataAppend,
            Fin.lastCases_castSucc] using rhoStable
        · simpa only [newChoice, appended, TashkinovSeriesDataAppend,
            Fin.lastCases_castSucc] using rhoFailure
      have newGammaRule : ParallelExtensionColor appended i.castSucc
          newChoice.selected newChoice.vertex gamma := by
        change ParallelExtensionColor appended i.castSucc
          choice.selected choice.vertex gamma
        exact (ParallelExtensionColorAppend series.data newTree newColoring
          newStored newEdges newKind newVertex newOutside newDelta newGamma i
          choice.selected choice.vertex gamma).2 gammaRule
      have newSecondStableRelation : StableColoring
          (appended.tree i.succ.castSucc)
          (insert newChoice.color (TashkinovStoredColors appended i.castSucc))
          newChoice.selected secondStable := by
        change StableColoring (appended.tree i.succ.castSucc)
          (insert choice.color (TashkinovStoredColors appended i.castSucc))
          choice.selected secondStable
        rw [storedEq]
        simpa only [appended, TashkinovSeriesDataAppend,
          Fin.lastCases_castSucc] using secondStableRelation
      have newExit : TreeExit (appended.tree i.succ.castSucc) secondStable
          gamma newChoice.color newChoice.vertex := by
        simpa only [newChoice, appended, TashkinovSeriesDataAppend,
          Fin.lastCases_castSucc] using exitWitness
      have lastStep : TashkinovSeriesStep G k (rounds + 1) e0 input appended
          (Fin.last (rounds + 1)) := by
        have hlast : i.succ = Fin.last (rounds + 1) := by ext; simp [i]
        rw [← hlast]
        apply TashkinovSeriesStep.PE (i := i) (choice := newChoice)
          (gamma := gamma) (secondStable := secondStable)
        · simpa [appended, TashkinovSeriesDataAppend, i] using proper
        · simpa [appended, TashkinovSeriesDataAppend, i] using one
        · simp only [appended, TashkinovSeriesDataAppend,
            Fin.lastCases_castSucc]
          exact closed
        · simp only [appended, TashkinovSeriesDataAppend,
            Fin.lastCases_castSucc]
          exact notStrong
        · exact newNoRevisiting
        · exact newFailure
        · exact newGammaRule
        · exact secondStableProper
        · exact secondStableOne
        · exact newSecondStableRelation
        · exact newExit
        · simp [appended, TashkinovSeriesDataAppend, newColoring, newChoice, i]
        · simpa [appended, TashkinovSeriesDataAppend, newColoring, i] using
            currentProper
        · simpa [appended, TashkinovSeriesDataAppend, newColoring, i] using
            currentOne
        · simp [appended, TashkinovSeriesDataAppend, newStored, newChoice, i]
        · simp [appended, TashkinovSeriesDataAppend, newEdges, newChoice, i]
        · simp [appended, TashkinovSeriesDataAppend, newKind, i]
        · simp [appended, TashkinovSeriesDataAppend, newVertex, newChoice, i]
        · simp [appended, TashkinovSeriesDataAppend, newOutside, newChoice, i]
        · simp [appended, TashkinovSeriesDataAppend, newDelta, newChoice, i]
        · simp [appended, TashkinovSeriesDataAppend, newGamma, i]
        · simpa [appended, TashkinovSeriesDataAppend, newColoring, T, i] using
            hclosure
        · simpa [appended, TashkinovSeriesDataAppend, T, i] using hordered
        · simpa [appended, TashkinovSeriesDataAppend, T, i] using hstrict
      obtain ⟨extended, hextended⟩ := TashkinovSeriesAppend G k rounds e0 input
        series newTree newColoring newStored newEdges newKind newVertex newOutside
        newDelta newGamma lastStep
      refine ⟨newTree, newColoring, newStored, newEdges, newKind, newVertex,
        newOutside, newDelta, newGamma, extended, hextended, ?_⟩
      simpa [T, hiTree] using hstrict
