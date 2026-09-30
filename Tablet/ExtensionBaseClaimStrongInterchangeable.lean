import Tablet.ETTStrongInterchangeable
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ExtensionBaseActiveIndices
import Tablet.HkuMissingStoredMonotone
import Tablet.InternalEdges
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDefectiveChoice
import Tablet.MissingColors
import Tablet.ParallelExtensionColor
import Tablet.PresentColors
import Tablet.RevisitingExtensionCertificate
import Tablet.SameColorSeriesPreserved
import Tablet.StableColoring
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeInterchangeable
import Tablet.TreeExit
import Tablet.TreeExitPath
import Tablet.TreeSequenceInitialSegment
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentCycle
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorCycle
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent
import Tablet.TwoColorNontrivialPathComponent
import Tablet.sc2
import Tablet.InterchangeableNonrootComponentCycle
import Tablet.ParallelStepRootComponentSetup
import Tablet.RevisitingPriorityCycleContainment
import Tablet.StableSeriesCycleComponentTransport

-- [TABLET NODE: ExtensionBaseClaimStrongInterchangeable]
theorem ExtensionBaseClaimStrongInterchangeable {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (q : Fin ett.rounds)
    (hqTerminal : q.val + 1 = ett.rounds)
    (hqKind : ett.series.data.kind q.succ =
      some TashkinovExtensionKind.PE)
    (hqVertex : ett.series.data.chosenVertex q.succ = some terminalSupport)
    (hLowerInterchange : ∀ (t : Fin ett.rounds) (vt : V)
      (gamma delta : Fin k),
      t ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      t.val < q.val →
      ett.series.data.chosenVertex t.succ = some vt →
      ett.series.data.gamma t.succ = some gamma →
      ett.series.data.delta t.succ = some delta →
      TreeInterchangeable G (ett.series.data.tree t.succ.succ)
        (ett.series.data.coloring t.succ) gamma delta)
    (sigma : PartialEdgeColoring E k)
    (hsigmaProper : IsProperEdgeColoring G sigma)
    (hsigmaOne : IsOneEdgeUncolored sigma e0)
    (hsigmaStable : StableColoring
      (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.succ)
      (ett.series.data.coloring q.succ) sigma) :
    ∀ (t : Fin ett.rounds) (vt : V) (gamma delta : Fin k),
      t ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      t.val < q.val →
      ett.series.data.chosenVertex t.succ = some vt →
      ett.series.data.gamma t.succ = some gamma →
      ett.series.data.delta t.succ = some delta →
      ETTStrongInterchangeable ett t vt sigma gamma delta := by
-- BODY
  intro t vt gamma delta htActive htq htVertex htGamma htDelta
  have htKind : ett.series.data.kind t.succ =
      some TashkinovExtensionKind.PE := by
    simp only [ExtensionBaseActiveIndices, Finset.mem_filter,
      Finset.mem_univ, true_and] at htActive
    exact htActive.2.1
  obtain ⟨hcolors, htProper, htSegment, hsupport, hrootPath, hrootOnly,
      hnonisolated⟩ :=
    ParallelStepRootComponentSetup ett.series t vt gamma delta
      htKind htVertex htGamma htDelta
  have hcycles := InterchangeableNonrootComponentCycle
    (ett.series.data.tree t.succ.castSucc)
    (ett.series.data.tree t.succ.succ)
    (ett.series.data.coloring t.succ) gamma delta vt htProper htSegment
    (hLowerInterchange t vt gamma delta htActive htq htVertex htGamma htDelta)
    hrootPath hsupport hrootOnly hnonisolated
  obtain ⟨epsilon, htEpsilon, hepsilonQ, hepsilonKind,
      hintervening, hcontained⟩ :=
    RevisitingPriorityCycleContainment ett.series t q vt gamma delta htq
      hqKind htKind htGamma htDelta
      (fun v hv hne => (hcycles v hv hne).1)
  refine ⟨hcolors, htKind, htVertex, epsilon, htEpsilon,
    hepsilonKind, hintervening, ?_⟩
  intro v hv hne
  obtain ⟨hcycle, havoid⟩ := hcycles v hv hne
  obtain ⟨hcomponent, hcycleSigma⟩ :=
    StableSeriesCycleComponentTransport ett.series t epsilon q gamma delta
      htEpsilon hepsilonQ htKind htGamma htDelta hintervening hqKind
      sigma hsigmaProper hsigmaOne hsigmaStable (Sum.inl v) hcycle
      (hcontained v hv hne)
  refine ⟨hcycleSigma, ?_, ?_⟩
  · rw [hcomponent]
    exact havoid
  · intro w hw
    apply hcontained v hv hne w
    rw [← hcomponent]
    exact hw
