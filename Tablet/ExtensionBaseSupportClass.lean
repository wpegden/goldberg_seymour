import Tablet.ExtensionBaseActiveIndices

-- [TABLET NODE: ExtensionBaseSupportClass]
noncomputable def ExtensionBaseSupportClass {V E : Type*} [Fintype V]
    [Fintype E] [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ}
    {e0 : E} {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (w : V) : Finset (Fin ett.rounds) := by
-- BODY
  classical
  exact (ExtensionBaseActiveIndices ett terminalSupport hterminalSupport).filter
    fun s => ett.series.data.chosenVertex s.succ = some w
