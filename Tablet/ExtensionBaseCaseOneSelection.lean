import Tablet.ColoredVertexSetElementary
import Tablet.ExtensionBaseCaseOneIndices
import Tablet.ExtensionBaseClosure
import Tablet.ExtensionBaseSupportClass
import Tablet.TashkinovClosure
import Tablet.TreeMissingColors
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
    (rho1 phiJ : PartialEdgeColoring E k)
    (seed TjPrime : TreeSequence G e0)
    (hclosure : TashkinovClosure rho1 seed TjPrime)
    (hterminalJ : terminalSupport ∈ TreeSequenceVertexSet
      (ett.series.data.tree jSlot.succ.castSucc))
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
    (hTjElementary : ColoredVertexSetElementary G phiJ
      (TreeSequenceVertexSet
        (ett.series.data.tree jSlot.succ.castSucc)))
    (hrhoAgreement : ∀ v : V,
      v ∈ (TreeSequenceVertexSet
          (ett.series.data.tree jSlot.succ.castSucc)).erase
            terminalSupport →
      MissingColors G rho1 v = MissingColors G phiJ v)
    (hfirstGammaMissing : gamma 0 ∈ MissingColors G phiJ terminalSupport)
    (hdeltaAvoidsTj : ∀ a : Fin (p + 1),
      delta a ∉ TreeMissingColors phiJ
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
