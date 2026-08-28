import Tablet.ExtensionBaseClaimMissingColors
import Tablet.ExtensionBaseClaimStrongInterchangeable
import Tablet.ExtensionBaseRestorationInvariant
import Tablet.ExtensionBaseStoredPairOverlap
import Tablet.ExtensionBaseSupportOrder
import Tablet.StrongInterchangeabilityKempePreserved
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwapProper

-- [TABLET NODE: ExtensionBaseAlgorithmA]
theorem ExtensionBaseAlgorithmA {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (jSlot q : Fin ett.rounds) (sigmaN : PartialEdgeColoring E k)
    (hqTerminal : q.val + 1 = ett.rounds)
    (hqKind : ett.series.data.kind q.succ =
      some TashkinovExtensionKind.PE)
    (hqVertex : ett.series.data.chosenVertex q.succ =
      some terminalSupport)
    (hjSlot : jSlot.val + 1 =
      ETTFirstAppearanceIndex ett terminalSupport hterminalSupport)
    (hsigmaProper : IsProperEdgeColoring G sigmaN)
    (hsigmaOne : IsOneEdgeUncolored sigmaN e0)
    (hterminalBefore : ∀ (t : Fin ett.rounds) (vt : V),
      t ∈ ExtensionBaseRestorationIndices ett terminalSupport
          hterminalSupport →
      ett.series.data.chosenVertex t.succ = some vt →
      TreeVertexOrder T terminalSupport vt)
    (hjInitial : ∀ t : Fin ett.rounds,
      t ∈ ExtensionBaseRestorationIndices ett terminalSupport
          hterminalSupport →
      TreeSequenceInitialSegment
        (ett.series.data.tree jSlot.succ.castSucc)
        (ett.series.data.tree t.succ.castSucc))
    (hslotData : ∀ t : Fin ett.rounds,
      t ∈ ExtensionBaseRestorationIndices ett terminalSupport
          hterminalSupport →
      ∃ vt : V, ∃ gammaT deltaT : Fin k,
        ett.series.data.chosenVertex t.succ = some vt ∧
          ett.series.data.gamma t.succ = some gammaT ∧
          ett.series.data.delta t.succ = some deltaT)
    (hinitialSI : ∀ (t : Fin ett.rounds) (vt : V)
      (gammaT deltaT : Fin k),
      t ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      t ≠ q →
      ett.series.data.chosenVertex t.succ = some vt →
      ett.series.data.gamma t.succ = some gammaT →
      ett.series.data.delta t.succ = some deltaT →
      ETTStrongInterchangeable ett t vt sigmaN gammaT deltaT)
    (hlastMissing : ∀ (t : Fin ett.rounds) (vt : V)
      (gammaT deltaT : Fin k),
      t ∈ ExtensionBaseRestorationIndices ett terminalSupport
          hterminalSupport →
      ett.series.data.chosenVertex t.succ = some vt →
      ett.series.data.gamma t.succ = some gammaT →
      ett.series.data.delta t.succ = some deltaT →
      (∀ s : Fin ett.rounds,
        s ∈ ExtensionBaseRestorationIndices ett terminalSupport
            hterminalSupport →
        ett.series.data.chosenVertex s.succ = some vt → s.val ≤ t.val) →
      deltaT ∈ MissingColors G sigmaN vt ∧
        gammaT ∉ MissingColors G sigmaN vt)
    (hpairOverlap : ∀ (s t : Fin ett.rounds) (vs vt : V)
      (gammaS deltaS gammaT deltaT : Fin k),
      s ∈ ExtensionBaseRestorationIndices ett terminalSupport
          hterminalSupport →
      t ∈ ExtensionBaseRestorationIndices ett terminalSupport
          hterminalSupport →
      s.val < t.val →
      ett.series.data.chosenVertex s.succ = some vs →
      ett.series.data.chosenVertex t.succ = some vt →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      ett.series.data.gamma t.succ = some gammaT →
      ett.series.data.delta t.succ = some deltaT →
      ((({gammaS, deltaS} : Finset (Fin k)) ∩ {gammaT, deltaT}).Nonempty ↔
        vs = vt ∧
          ¬ ∃ r : Fin ett.rounds,
            r ∈ ExtensionBaseRestorationIndices ett terminalSupport
                hterminalSupport ∧
            s.val < r.val ∧ r.val < t.val ∧
            ett.series.data.chosenVertex r.succ = some vs) ∧
      ((({gammaS, deltaS} : Finset (Fin k)) ∩ {gammaT, deltaT}).Nonempty →
        ({gammaS, deltaS} : Finset (Fin k)) ∩ {gammaT, deltaT} =
            {gammaT} ∧
          ({gammaS, deltaS} : Finset (Fin k)) ∩ {gammaT, deltaT} =
            {deltaS})) :
    ∃ trace : ExtensionBaseRestorationTrace ett terminalSupport
        hterminalSupport sigmaN,
      ExtensionBaseRestorationInvariant ett terminalSupport
        hterminalSupport jSlot q sigmaN trace := by
-- BODY
  sorry
