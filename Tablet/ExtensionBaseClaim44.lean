import Tablet.ExtensionBaseAlgorithmB
import Tablet.ExtensionBaseSupportClass
import Tablet.ETTFirstAppearanceIndex
import Tablet.IsProperEdgeColoring
import Tablet.MissingColors
import Tablet.StableColoringBeforeVertex
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TreeSequence
import Tablet.TreeSequencePrefix
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
    (jSlot : Fin ett.rounds)
    (hjSlot : jSlot.val + 1 =
      ETTFirstAppearanceIndex ett terminalSupport hterminalSupport)
    (rho1 : PartialEdgeColoring E k)
    (C : Finset (Fin k)) (u : V)
    (TjPrime seed : TreeSequence G e0)
    (terminalPosition : Fin
      ((ett.series.data.tree jSlot.succ.castSucc).length + 1))
    (hterminalAt :
      (ett.series.data.tree jSlot.succ.castSucc).vertex terminalPosition =
        terminalSupport)
    (hterminalPositionPositive : 1 ≤ terminalPosition.val)
    (hseed : seed = TreeSequencePrefix
      (ett.series.data.tree jSlot.succ.castSucc) terminalPosition.val
      hterminalPositionPositive
      (Nat.le_of_lt_succ terminalPosition.isLt))
    (huPrime : u ∈ TreeSequenceVertexSet TjPrime)
    (p : ℕ) (indices : Fin (p + 1) → Fin ett.rounds)
    (gamma delta : Fin (p + 1) → Fin k) (b : Fin (p + 1))
    (hincreasing : ∀ a c, a.val < c.val →
      (indices a).val < (indices c).val)
    (hclass : ∀ r : Fin ett.rounds,
      r ∈ ExtensionBaseSupportClass ett terminalSupport
          hterminalSupport terminalSupport ↔
        ∃ a : Fin (p + 1), indices a = r)
    (trace : ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u
      p indices b)
    (hinvariant : ExtensionBaseAlgorithmBInvariant ett terminalSupport
      jSlot rho1 u p indices b trace)
    (hbaseStable : StableColoringBeforeVertex
      (ett.series.data.tree jSlot.succ.castSucc) terminalSupport
      (by
        rw [← hterminalAt]
        simp [TreeSequenceVertexSet])
      C (ett.series.data.coloring jSlot.castSucc) rho1)
    (huOutsideTj : u ∉ TreeSequenceVertexSet
      (ett.series.data.tree jSlot.succ.castSucc))
    (hclosure : TashkinovClosure rho1 seed TjPrime)
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
    (hdistinct : Function.Injective (Fin.cons (gamma 0) delta))
    (hstored : ∀ a,
      ett.series.data.stored (indices a).succ = {gamma a, delta a}) :
    let rho2 := trace.coloring (Fin.last trace.steps)
    StableColoringBeforeVertex
        (ett.series.data.tree jSlot.succ.castSucc) terminalSupport
        (by
          rw [← hterminalAt]
          simp [TreeSequenceVertexSet])
        C (ett.series.data.coloring jSlot.castSucc) rho2 ∧
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
