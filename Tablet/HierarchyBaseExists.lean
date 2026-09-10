import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.DefectiveColor
import Tablet.DefectiveEdge
import Tablet.DefectiveVertex
import Tablet.ExtendedTashkinovTree
import Tablet.HierarchyBase
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDefectiveChoice
import Tablet.OrderedTreeUnionExists
import Tablet.TashkinovClosureExists
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeSequencePrefix
import Tablet.TreeVertexOrder

-- [TABLET NODE: HierarchyBaseExists]
theorem HierarchyBaseExists
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating) :
    Nonempty (HierarchyBase ett generating) := by
-- BODY
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  have cert := ett.series.certified n
  let j : Fin (ett.rounds + 1) := n
  generalize hj : n = j at cert
  cases cert with
  | initial triple seedLength initialColoring initialStored initialEdges initialKind
      initialVertex initialOutside initialDelta initialGamma initialClosure =>
      have hn : n = 0 := by simpa [hj]
      have hne : n ≠ 0 := by
        intro h
        have hv : ett.rounds = 0 := by
          simpa [n] using congrArg Fin.val h
        have hp := ett.roundsPositive
        omega
      exact (hne hn).elim
  | SE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternative currentColoring currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma adjoined
      adjoinedExactly closedExtension orderedExtension strictExtension =>
      skip
      let Tn := ett.series.data.tree n.castSucc
      have hi : i.succ = n := by simpa [j] using hj.symm
      have htree : ett.series.data.tree i.succ.castSucc = Tn := by
        simp [Tn, hi]
      have hlen : 1 ≤ Tn.length := by
        rw [← htree]
        exact (ett.series.data.tree i.succ.castSucc).positive
      let support : Fin (Tn.length + 1) := ⟨1, by omega⟩
      refine ⟨{
        core := Tn
        closure := Tn
        supportPosition := support
        supportPositive := by dsimp [support]; omega
        terminalMissingColors := by simpa [ett.generatingColoring]
        parallel := by
          dsimp [Tn, n]
          intro h
          have hh : ett.series.data.kind i.succ = some TashkinovExtensionKind.PE := by
            simpa [hi] using h
          rw [currentKind] at hh
          cases hh
        nonparallel := by
          dsimp [Tn, n]
          intro h
          rfl }⟩
  | PE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternativeFails gamma gammaRule secondStable
      secondStableProper secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
      orderedExtension strictExtension =>
      skip
      let Tn := ett.series.data.tree n.castSucc
      have hi : i.succ = n := by simpa [j] using hj.symm
      have htree : ett.series.data.tree i.succ.castSucc = Tn := by
        simp [Tn, hi]
      rcases choice.edgeDefective with ⟨alpha, alphaDefective, edgeMem⟩
      have cardLarge : 1 < (BoundaryColorEdges G choice.selected
          (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) alpha).card := by
        have hc : 2 ≤ (BoundaryColorEdges G choice.selected
            (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) alpha).card := by
          simpa [DefectiveColor] using alphaDefective
        omega
      obtain ⟨otherEdge, otherMem, otherNe⟩ :=
        Finset.exists_mem_ne cardLarge choice.edge
      have boundaryOther : ∃ w ∈ TreeSequenceVertexSet
          (ett.series.data.tree i.succ.castSucc), ∃ z ∉ TreeSequenceVertexSet
          (ett.series.data.tree i.succ.castSucc), G.ends otherEdge = s(w, z) := by
        have hm : (∃ u ∈ TreeSequenceVertexSet
            (ett.series.data.tree i.succ.castSucc), ∃ v ∉ TreeSequenceVertexSet
            (ett.series.data.tree i.succ.castSucc), G.ends otherEdge = s(u, v)) ∧
            choice.selected otherEdge = some alpha := by
          simpa [BoundaryColorEdges, BoundaryEdges] using otherMem
        exact hm.1
      obtain ⟨w, wInside, z, zOutside, otherEnds⟩ := boundaryOther
      have wDefective : DefectiveVertex G choice.selected
          (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) w := by
        refine ⟨wInside, otherEdge, ?_, ?_⟩
        · exact ⟨alpha, alphaDefective, otherMem⟩
        · unfold Incident
          rw [otherEnds]
          exact Sym2.mem_iff.mpr (Or.inl rfl)
      have orderChoice := choice.maximal choice.selected w choice.selectedProper
        choice.selectedOneUncolored choice.selectedStable wDefective
      have wne : w ≠ choice.vertex := by
        intro equal
        subst w
        have edgeIncidentOther : Incident G choice.vertex otherEdge := by
          unfold Incident
          rw [otherEnds]
          exact Sym2.mem_iff.mpr (Or.inl rfl)
        have adjacent : AdjacentEdges G choice.edge otherEdge :=
          ⟨choice.vertex, choice.edgeIncident, edgeIncidentOther⟩
        have otherColor : choice.selected otherEdge = some alpha := by
          have hm : (∃ u ∈ TreeSequenceVertexSet
              (ett.series.data.tree i.succ.castSucc), ∃ v ∉ TreeSequenceVertexSet
              (ett.series.data.tree i.succ.castSucc), G.ends otherEdge = s(u, v)) ∧
              choice.selected otherEdge = some alpha := by
            simpa [BoundaryColorEdges, BoundaryEdges] using otherMem
          exact hm.2
        have edgeAlpha : choice.selected choice.edge = some alpha := by
          have hm : (∃ u ∈ TreeSequenceVertexSet
              (ett.series.data.tree i.succ.castSucc), ∃ v ∉ TreeSequenceVertexSet
              (ett.series.data.tree i.succ.castSucc), G.ends choice.edge = s(u, v)) ∧
              choice.selected choice.edge = some alpha := by
            simpa [BoundaryColorEdges, BoundaryEdges] using edgeMem
          exact hm.2
        have alphaChoice : alpha = choice.color := by
          simpa [choice.edgeColor] using edgeAlpha.symm
        rw [alphaChoice] at otherColor
        exact (choice.selectedProper otherNe.symm adjacent choice.edgeColor)
          otherColor
      have orderStrict : TreeVertexOrder
          (ett.series.data.tree i.succ.castSucc) w choice.vertex := by
        rcases orderChoice with equal | order
        · exact (wne equal).elim
        · exact order
      rcases orderStrict with ⟨r, s, hr, hs, hrs⟩
      have supportPositive : 1 ≤ s.val := by omega
      have supportLe : s.val ≤ Tn.length := by
        have hl := congrArg TreeSequence.length htree
        omega
      have hlen : (ett.series.data.tree i.succ.castSucc).length = Tn.length :=
        congrArg TreeSequence.length htree
      let support : Fin (Tn.length + 1) :=
        Fin.cast (congrArg (fun q => q + 1) hlen) s
      have castVertexValue : ∀ (A B : TreeSequence G e0) (h : A = B)
          (x : Fin (A.length + 1)),
          (cast (congrArg (fun q => Fin (q.length + 1)) h) x).val = x.val := by
        intro A B h x
        cases h
        rfl
      have chosenAt : choice.vertex = Tn.vertex support := by
        have hv : HEq (Tn.vertex support)
            ((ett.series.data.tree i.succ.castSucc).vertex s) := by
          congr
          · exact htree.symm
          · dsimp [support]
            apply heq_of_cast_eq (congrArg (fun q => Fin (q.length + 1)) htree.symm)
            apply Fin.ext
            have hsfin : Fin.cast (congrArg (fun q => q + 1) hlen) s =
                ⟨s.val, by omega⟩ := by
              apply Fin.ext
              rfl
            rw [hsfin]
            exact castVertexValue _ _ htree.symm _
        exact hs.symm.trans (eq_of_heq hv).symm
      obtain ⟨closure, closureCert⟩ := TashkinovClosureExists generating
        (TreeSequencePrefix Tn support.val supportPositive (by omega))
      obtain ⟨core, unionCert⟩ := OrderedTreeUnionExists Tn closure
      refine ⟨{
        core := core
        closure := closure
        supportPosition := support
        supportPositive := supportPositive
        terminalMissingColors := by simpa [ett.generatingColoring]
        parallel := by
          dsimp [Tn, n]
          intro h
          refine ⟨?_, ?_, unionCert⟩
          · simpa [n, hi, chosenAt] using currentVertex
          · exact closureCert
        nonparallel := by
          dsimp [Tn, n]
          intro h
          have hh : ett.series.data.kind i.succ = some TashkinovExtensionKind.PE := by
            simpa [n, hi] using currentKind
          exact (h (by simpa [n, hi] using hh)).elim }⟩
  | RE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      available currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly closedExtension
      orderedExtension strictExtension =>
      skip
      let Tn := ett.series.data.tree n.castSucc
      have hi : i.succ = n := by simpa [j] using hj.symm
      have htree : ett.series.data.tree i.succ.castSucc = Tn := by
        simp [Tn, hi]
      have hpos : 1 ≤ Tn.length := by
        rw [← htree]
        exact (ett.series.data.tree i.succ.castSucc).positive
      let support : Fin (Tn.length + 1) := ⟨1, by omega⟩
      refine ⟨{
        core := Tn
        closure := Tn
        supportPosition := support
        supportPositive := by dsimp [support]; omega
        terminalMissingColors := by simpa [ett.generatingColoring]
        parallel := by
          dsimp [Tn, n]
          intro h
          have hh : ett.series.data.kind i.succ = some TashkinovExtensionKind.PE := by
            simpa [hi] using h
          rw [currentKind] at hh
          cases hh
        nonparallel := by
          dsimp [Tn, n]
          intro h
          rfl }⟩
