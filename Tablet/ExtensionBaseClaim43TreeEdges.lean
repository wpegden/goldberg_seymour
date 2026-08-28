import Tablet.ExtensionBaseClaimTreeEdgeColors
import Tablet.ExtensionBaseRestorationInvariant

-- [TABLET NODE: ExtensionBaseClaim43TreeEdges]
theorem ExtensionBaseClaim43TreeEdges {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (jSlot q : Fin ett.rounds) (hjle : jSlot.val ≤ q.val)
    (hqTerminal : q.val + 1 = ett.rounds)
    (sigmaN : PartialEdgeColoring E k)
    (hsigmaProper : IsProperEdgeColoring G sigmaN)
    (hsigmaOne : IsOneEdgeUncolored sigmaN e0)
    (hsigmaStable : StableColoring
      (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.succ)
      (ett.series.data.coloring q.succ) sigmaN)
    (trace : ExtensionBaseRestorationTrace ett terminalSupport
      hterminalSupport sigmaN)
    (hinvariant : ExtensionBaseRestorationInvariant ett terminalSupport
      hterminalSupport jSlot q sigmaN trace) :
    ∀ a : Fin (ett.series.data.tree jSlot.succ.castSucc).length,
      trace.coloring (Fin.last trace.steps)
          ((ett.series.data.tree jSlot.succ.castSucc).edge a) =
        sigmaN ((ett.series.data.tree jSlot.succ.castSucc).edge a) ∧
      sigmaN ((ett.series.data.tree jSlot.succ.castSucc).edge a) =
        ett.series.data.coloring jSlot.castSucc
          ((ett.series.data.tree jSlot.succ.castSucc).edge a) := by
-- BODY
  sorry
