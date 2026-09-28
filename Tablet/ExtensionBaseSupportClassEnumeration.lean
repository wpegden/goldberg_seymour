import Tablet.DefectiveVertex
import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtensionBaseActiveIndices
import Tablet.ExtensionBaseSupportClass
import Tablet.MaximumDefectiveChoice
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: ExtensionBaseSupportClassEnumeration]
theorem ExtensionBaseSupportClassEnumeration {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (q : Fin ett.rounds) (hqTerminal : q.val + 1 = ett.rounds)
    (w : V)
    (hcommon : ∀ (s : Fin ett.rounds) (v : V)
      (hvFinal : v ∈ TreeSequenceVertexSet T),
      s ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      ett.series.data.chosenVertex s.succ = some v →
      ETTFirstAppearanceIndex ett v hvFinal =
        ETTFirstAppearanceIndex ett terminalSupport hterminalSupport)
    (hclassNonempty :
      (ExtensionBaseSupportClass ett terminalSupport hterminalSupport w).Nonempty) :
    ∃ (p : ℕ) (indices : Fin (p + 1) → Fin ett.rounds),
      w ∈ TreeSequenceVertexSet
          (ett.series.data.tree q.succ.castSucc) ∧
      (∀ a b, a.val < b.val →
        (indices a).val < (indices b).val) ∧
      (∀ r : Fin ett.rounds,
        r ∈ ExtensionBaseSupportClass ett terminalSupport
              hterminalSupport w ↔
          ∃ a : Fin (p + 1), indices a = r) ∧
      ∀ r : Fin ett.rounds,
        (r.val ≤ q.val ∧
          ett.series.data.kind r.succ =
            some TashkinovExtensionKind.PE ∧
          ett.series.data.chosenVertex r.succ = some w) ↔
        ∃ a : Fin (p + 1), indices a = r := by
-- BODY
  sorry
