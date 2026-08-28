import Tablet.ExtensionBaseAlgorithmB
import Tablet.IsProperEdgeColoring
import Tablet.MissingColors
import Tablet.StableColoringBeforeVertex
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TreeSequence
import Tablet.TreeVerticesBefore
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ExtensionBaseClaim44]
theorem ExtensionBaseClaim44 {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (jSlot : Fin ett.rounds) (rho1 phiJ : PartialEdgeColoring E k)
    (C : Finset (Fin k)) (u : V)
    (TjPrime seed : TreeSequence G e0)
    (huPrime : u ∈ TreeSequenceVertexSet TjPrime)
    (p : ℕ) (indices : Fin (p + 1) → Fin ett.rounds)
    (gamma delta : Fin (p + 1) → Fin k) (b : Fin (p + 1))
    (trace : ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u
      p indices b)
    (hinvariant : ExtensionBaseAlgorithmBInvariant ett terminalSupport
      jSlot rho1 u p indices b trace)
    (hbaseStable : StableColoringBeforeVertex T terminalSupport
      hterminalSupport C phiJ rho1)
    (hbeforeContained : ∀ w : V,
      w ∈ TreeVerticesBefore T terminalSupport hterminalSupport →
      w ∈ TreeSequenceVertexSet
        (ett.series.data.tree jSlot.succ.castSucc))
    (huOutsideTj : u ∉ TreeSequenceVertexSet
      (ett.series.data.tree jSlot.succ.castSucc))
    (hclosure : TashkinovClosure rho1 seed TjPrime)
    (hseedEdgesTj : ∀ a : Fin seed.length,
      ∃ c : Fin (ett.series.data.tree jSlot.succ.castSucc).length,
        seed.edge a =
          (ett.series.data.tree jSlot.succ.castSucc).edge c)
    (hprefixAvoids :
      (TreeVerticesBefore TjPrime u huPrime).biUnion
          (fun v => MissingColors G rho1 v) ∩
        ((ExtensionBaseCaseOneIndices ett p indices b).biUnion
          fun t => ett.series.data.stored t.succ) = ∅)
    (hselected : gamma b ∈ MissingColors G rho1 u)
    (hminimal : ∀ a : Fin (p + 1), a.val < b.val →
      gamma a ∉ MissingColors G rho1 u)
    (hgamma : ∀ a,
      ett.series.data.gamma (indices a).succ = some (gamma a))
    (hdelta : ∀ a,
      ett.series.data.delta (indices a).succ = some (delta a))
    (hchain : ∀ a : Fin p, gamma a.succ = delta a.castSucc)
    (hstored : ∀ a,
      ett.series.data.stored (indices a).succ = {gamma a, delta a}) :
    let rho2 := trace.coloring (Fin.last trace.steps)
    StableColoringBeforeVertex T terminalSupport hterminalSupport C phiJ
        rho2 ∧
      ((∀ v : V,
        v ∈ TreeSequenceVertexSet
              (ett.series.data.tree jSlot.succ.castSucc) ∪
            TreeVerticesBefore TjPrime u huPrime →
        MissingColors G rho2 v = MissingColors G rho1 v) ∧
       ∀ f : E,
        ((∃ a : Fin (ett.series.data.tree
              jSlot.succ.castSucc).length,
            (ett.series.data.tree jSlot.succ.castSucc).edge a = f) ∨
          ∃ (a : Fin TjPrime.length) (z : Fin (TjPrime.length + 1)),
            TjPrime.vertex z = u ∧ a.val < z.val ∧
              TjPrime.edge a = f) →
        rho2 f = rho1 f) ∧
      gamma 0 ∈ MissingColors G rho2 u := by
-- BODY
  sorry
