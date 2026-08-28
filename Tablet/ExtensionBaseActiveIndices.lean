import Tablet.ETTFirstAppearanceIndex
import Tablet.TashkinovExtensionKind

-- [TABLET NODE: ExtensionBaseActiveIndices]
noncomputable def ExtensionBaseActiveIndices {V E : Type*} [Fintype V]
    [Fintype E] [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ}
    {e0 : E} {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T) :
    Finset (Fin ett.rounds) := by
-- BODY
  classical
  let j := ETTFirstAppearanceIndex ett terminalSupport hterminalSupport
  exact Finset.univ.filter fun s =>
    j ≤ s.val + 1 ∧
      ett.series.data.kind s.succ = some TashkinovExtensionKind.PE ∧
      ∃ v : V, ∃ hv : v ∈ TreeSequenceVertexSet T,
        ett.series.data.chosenVertex s.succ = some v ∧
          ETTFirstAppearanceIndex ett v hv ≤ j
