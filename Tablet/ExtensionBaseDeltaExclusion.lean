import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryColorVertex
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.DefectiveColor
import Tablet.DefectiveEdge
import Tablet.DefectiveVertex
import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtendedTashkinovTree
import Tablet.ExtensionBaseActiveIndices
import Tablet.ExtensionBaseLeastActiveDeltaTransport
import Tablet.ExtensionBasePESlotDeltaNotMissing
import Tablet.ExtensionBaseStrictDeltaExclusion
import Tablet.ExtensionBaseSupportOrder
import Tablet.HkuMissingStoredMonotone
import Tablet.HkuUnsupportedVertexColors
import Tablet.Incident
import Tablet.InternalEdges
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDefectiveChoice
import Tablet.MissingColors
import Tablet.ParallelExtensionColor
import Tablet.PresentColors
import Tablet.SameColorSeriesPreserved
import Tablet.StableColoring
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder
import Tablet.sc2

-- [TABLET NODE: ExtensionBaseDeltaExclusion]
theorem ExtensionBaseDeltaExclusion {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (q : Fin ett.rounds) (hqTerminal : q.val + 1 = ett.rounds)
    (hqKind : ett.series.data.kind q.succ =
      some TashkinovExtensionKind.PE)
    (hqVertex : ett.series.data.chosenVertex q.succ = some terminalSupport)
    (jSlot : Fin ett.rounds)
    (hjSlot : jSlot.val + 1 =
      ETTFirstAppearanceIndex ett terminalSupport hterminalSupport)
    (hLowerElementary : ∀ r : Fin ett.rounds, r.val < q.val →
      ColoredVertexSetElementary G (ett.series.data.coloring r.castSucc)
        (TreeSequenceVertexSet
          (ett.series.data.tree r.succ.castSucc)))
    (hLowerPartV : ∀ (r a : Fin ett.rounds), a.val < r.val →
      ∀ sigma : PartialEdgeColoring E k,
        IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
        StableColoring (ett.series.data.tree r.succ.castSucc)
          (TashkinovStoredColors ett.series.data r.castSucc)
          (ett.series.data.coloring r.castSucc) sigma →
        ∀ delta : Fin k,
          DefectiveColor G sigma
            (TreeSequenceVertexSet
              (ett.series.data.tree r.succ.castSucc)) delta →
          ∀ v : V,
            BoundaryColorVertex G sigma
              (TreeSequenceVertexSet
                (ett.series.data.tree r.succ.castSucc)) delta v →
            (∃ w : V, BoundaryColorVertex G sigma
                (TreeSequenceVertexSet
                  (ett.series.data.tree r.succ.castSucc)) delta w ∧
              TreeVertexOrder (ett.series.data.tree r.succ.castSucc) w v) →
            ∀ hvFinal : v ∈ TreeSequenceVertexSet T,
              ETTFirstAppearanceIndex ett v hvFinal ≤ a.val + 1 →
              ∀ va : V,
                (ett.series.data.kind a.succ =
                    some TashkinovExtensionKind.PE ∨
                  ett.series.data.kind a.succ =
                    some TashkinovExtensionKind.SE) →
                ett.series.data.chosenVertex a.succ = some va →
                v = va ∨
                  TreeVertexOrder
                    (ett.series.data.tree r.succ.castSucc) v va) :
    (∀ (s t : Fin ett.rounds) (vs vt : V)
      (hvsFinal : vs ∈ TreeSequenceVertexSet T)
      (hvtFinal : vt ∈ TreeSequenceVertexSet T)
      (deltaT gammaS : Fin k),
      s ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      t ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      s.val ≤ t.val →
      ett.series.data.chosenVertex s.succ = some vs →
      ett.series.data.chosenVertex t.succ = some vt →
      ett.series.data.delta t.succ = some deltaT →
      ett.series.data.gamma s.succ = some gammaS →
      deltaT ∉ TreeMissingColors (ett.series.data.coloring s.castSucc)
          (ett.series.data.tree s.succ.castSucc) ∧
        deltaT ≠ gammaS) ∧
    ∀ (t : Fin ett.rounds) (vt : V)
      (hvtFinal : vt ∈ TreeSequenceVertexSet T) (deltaT : Fin k),
      t ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      ett.series.data.chosenVertex t.succ = some vt →
      ett.series.data.delta t.succ = some deltaT →
      deltaT ∉ TreeMissingColors (ett.series.data.coloring jSlot.castSucc)
        (ett.series.data.tree jSlot.succ.castSucc) := by
-- BODY
  classical
  have pairExclusion : ∀ (s t : Fin ett.rounds) (vs vt : V)
      (hvsFinal : vs ∈ TreeSequenceVertexSet T)
      (hvtFinal : vt ∈ TreeSequenceVertexSet T)
      (deltaT : Fin k),
      s ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      t ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      s.val ≤ t.val →
      ett.series.data.chosenVertex s.succ = some vs →
      ett.series.data.chosenVertex t.succ = some vt →
      ett.series.data.delta t.succ = some deltaT →
      deltaT ∉ TreeMissingColors (ett.series.data.coloring s.castSucc)
        (ett.series.data.tree s.succ.castSucc) := by
    intro s t vs vt hvsFinal hvtFinal deltaT hsActive htActive hst
      hsVertex htVertex htDelta
    by_cases heq : s.val = t.val
    · have hstEq : s = t := Fin.ext heq
      subst t
      have hsData := hsActive
      simp [ExtensionBaseActiveIndices] at hsData
      exact ExtensionBasePESlotDeltaNotMissing G k ett.rounds e0 input
        ett.series s deltaT hsData.2.1 htDelta
    · have hstrict : s.val < t.val := lt_of_le_of_ne hst heq
      exact ExtensionBaseStrictDeltaExclusion ett terminalSupport
        hterminalSupport q hqTerminal hqKind hqVertex hLowerElementary
        hLowerPartV s t vs vt hvsFinal hvtFinal deltaT hsActive htActive
        hstrict hsVertex htVertex htDelta
  constructor
  · intro s t vs vt hvsFinal hvtFinal deltaT gammaS hsActive htActive
      hst hsVertex htVertex htDelta hsGamma
    have hdelta := pairExclusion s t vs vt hvsFinal hvtFinal deltaT
      hsActive htActive hst hsVertex htVertex htDelta
    have hsData := hsActive
    simp [ExtensionBaseActiveIndices] at hsData
    have hsKind : ett.series.data.kind s.succ =
        some TashkinovExtensionKind.PE := hsData.2.1
    have hgammaMissing : gammaS ∈
        TreeMissingColors (ett.series.data.coloring s.castSucc)
          (ett.series.data.tree s.succ.castSucc) := by
      have step := ett.series.certified s.succ
      generalize hz : s.succ = z at step
      cases step with
      | initial triple seedLength initialColoring initialStored initialEdges
          initialKind initialVertex initialOutside initialDelta initialGamma
          initialClosure =>
          have hv := congrArg Fin.val hz
          simp at hv
      | SE r previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting choice seriesAlternative
          currentColoring currentStored currentEdges currentKind currentVertex
          currentOutside currentDelta currentGamma adjoined adjoinedExactly
          closedExtension orderedExtension strictExtension =>
          have hrs : r = s := by
            apply Fin.ext
            have hv := congrArg Fin.val hz
            simp at hv ⊢
            omega
          subst r
          rw [currentKind] at hsKind
          simp at hsKind
      | RE r previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed available currentColoring currentStored
          currentEdges currentKind currentVertex currentOutside currentDelta
          currentGamma adjoined adjoinedExactly closedExtension
          orderedExtension strictExtension =>
          have hrs : r = s := by
            apply Fin.ext
            have hv := congrArg Fin.val hz
            simp at hv ⊢
            omega
          subst r
          rw [currentKind] at hsKind
          simp at hsKind
      | PE r previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting choice
          seriesAlternativeFails gamma gammaRule secondStable
          secondStableProper secondStableOneUncolored secondStableRelation
          exitWitness currentColoring currentProper currentOneUncolored
          currentStored currentEdges currentKind currentVertex currentOutside
          currentDelta currentGamma closedExtension orderedExtension
          strictExtension =>
          have hrs : r = s := by
            apply Fin.ext
            have hv := congrArg Fin.val hz
            simp at hv ⊢
            omega
          subst r
          have hgamma : gamma = gammaS := by
            rw [currentGamma] at hsGamma
            exact Option.some.inj hsGamma
          subst gammaS
          simp only [TreeMissingColors, Finset.mem_biUnion]
          refine ⟨choice.vertex, choice.vertexDefective.1, ?_⟩
          rw [← choice.selectedStable.2 choice.vertex
            choice.vertexDefective.1]
          exact gammaRule.1
    refine ⟨hdelta, ?_⟩
    intro heq
    apply hdelta
    simpa [heq] using hgammaMissing
  · exact ExtensionBaseLeastActiveDeltaTransport ett terminalSupport
      hterminalSupport q hqTerminal hqKind hqVertex jSlot hjSlot
      pairExclusion
