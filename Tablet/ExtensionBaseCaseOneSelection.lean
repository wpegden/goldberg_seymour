import Tablet.ColoredVertexSetElementary
import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtensionBaseCaseOneIndices
import Tablet.ExtensionBaseClosure
import Tablet.ExtensionBaseSupportClass
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder
import Tablet.TreeVerticesBefore

-- [TABLET NODE: ExtensionBaseCaseOneSelection]
theorem ExtensionBaseCaseOneSelection {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (jSlot q : Fin ett.rounds) (hjle : jSlot.val ≤ q.val)
    (hqTerminal : q.val + 1 = ett.rounds)
    (hjSlot : jSlot.val + 1 =
      ETTFirstAppearanceIndex ett terminalSupport hterminalSupport)
    (rho1 : PartialEdgeColoring E k)
    (seed TjPrime : TreeSequence G e0)
    (terminalPosition : Fin
      ((ett.series.data.tree jSlot.succ.castSucc).length + 1))
    (hterminalAt :
      (ett.series.data.tree jSlot.succ.castSucc).vertex terminalPosition =
        terminalSupport)
    (hterminalPositionPositive : 1 ≤ terminalPosition.val)
    (hseed : seed = TreeSequencePrefix
      (ett.series.data.tree jSlot.succ.castSucc) terminalPosition.val
      hterminalPositionPositive (Nat.le_of_lt_succ terminalPosition.isLt))
    (hclosure : TashkinovClosure rho1 seed TjPrime)
    (hterminalPrime : terminalSupport ∈ TreeSequenceVertexSet TjPrime)
    (p : ℕ) (indices : Fin (p + 1) → Fin ett.rounds)
    (gamma delta : Fin (p + 1) → Fin k)
    (hincreasing : ∀ a b, a.val < b.val →
      (indices a).val < (indices b).val)
    (hclass : ∀ r : Fin ett.rounds,
      r ∈ ExtensionBaseSupportClass ett terminalSupport
          hterminalSupport terminalSupport ↔
        ∃ a : Fin (p + 1), indices a = r)
    (hqLast : indices (Fin.last p) = q)
    (hgamma : ∀ a,
      ett.series.data.gamma (indices a).succ = some (gamma a))
    (hdelta : ∀ a,
      ett.series.data.delta (indices a).succ = some (delta a))
    (hstored : ∀ a,
      ett.series.data.stored (indices a).succ = {gamma a, delta a})
    (hchain : ∀ a : Fin p, gamma a.succ = delta a.castSucc)
    (hdistinct : Function.Injective (Fin.cons (gamma 0) delta))
    (hcase :
      (((TreeSequenceVertexSet TjPrime).erase terminalSupport).biUnion
          (fun v => MissingColors G rho1 v) ∩
        (Finset.univ.biUnion fun a : Fin (p + 1) =>
          ett.series.data.stored (indices a).succ)).Nonempty)
    (hprimeElementary : ColoredVertexSetElementary G rho1
      (TreeSequenceVertexSet TjPrime))
    (hterminalIntersection :
      MissingColors G rho1 terminalSupport ∩
          (Finset.univ.biUnion fun a : Fin (p + 1) =>
            ett.series.data.stored (indices a).succ) =
        {delta (Fin.last p)})
    (hTjElementary : ColoredVertexSetElementary G
      (ett.series.data.coloring jSlot.castSucc)
      (TreeSequenceVertexSet
        (ett.series.data.tree jSlot.succ.castSucc)))
    (hrhoAgreement : ∀ v : V,
      v ∈ (TreeSequenceVertexSet
          (ett.series.data.tree jSlot.succ.castSucc)).erase
            terminalSupport →
      MissingColors G rho1 v = MissingColors G
        (ett.series.data.coloring jSlot.castSucc) v)
    (hfirstGammaMissing : gamma 0 ∈ MissingColors G
      (ett.series.data.coloring jSlot.castSucc) terminalSupport)
    (hdeltaAvoidsTj : ∀ a : Fin (p + 1),
      delta a ∉ TreeMissingColors
        (ett.series.data.coloring jSlot.castSucc)
        (ett.series.data.tree jSlot.succ.castSucc)) :
    ∃ (u : V) (hu : u ∈ TreeSequenceVertexSet TjPrime)
      (b : Fin (p + 1)),
      u ≠ terminalSupport ∧
        gamma b ∈ MissingColors G rho1 u ∧
        (∀ a : Fin (p + 1), a.val < b.val →
          gamma a ∉ MissingColors G rho1 u) ∧
        (∀ w : V,
          w ∈ (TreeSequenceVertexSet TjPrime).erase terminalSupport →
          (MissingColors G rho1 w ∩
            (Finset.univ.biUnion fun a : Fin (p + 1) =>
              ett.series.data.stored (indices a).succ)).Nonempty →
          w = u ∨ TreeVertexOrder TjPrime u w) ∧
        u ∉ TreeSequenceVertexSet
          (ett.series.data.tree jSlot.succ.castSucc) ∧
        (let supportColors := Finset.univ.biUnion
            fun a : Fin (p + 1) =>
              ett.series.data.stored (indices a).succ
         let prefixColors :=
           (ExtensionBaseCaseOneIndices ett p indices b).biUnion
             fun t => ett.series.data.stored t.succ
         ((TreeVerticesBefore TjPrime u hu).biUnion
              (fun v => MissingColors G rho1 v) ∩
            (supportColors \ {delta (Fin.last p)}) = ∅) ∧
           delta (Fin.last p) ∉ prefixColors ∧
           MissingColors G rho1 terminalSupport ∩ prefixColors = ∅) := by
-- BODY
  sorry
