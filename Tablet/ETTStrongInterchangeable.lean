import Tablet.ExtendedTashkinovTree
import Tablet.TashkinovExtensionKind
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentCycle

-- [TABLET NODE: ETTStrongInterchangeable]
def ETTStrongInterchangeable {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (t : Fin ett.rounds) (support : V) (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) : Prop :=
-- BODY
  alpha ≠ beta ∧
    ett.series.data.kind t.succ = some TashkinovExtensionKind.PE ∧
    ett.series.data.chosenVertex t.succ = some support ∧
    ∃ epsilon : Fin ett.rounds,
      t.val < epsilon.val ∧
      ett.series.data.kind epsilon.succ ≠
        some TashkinovExtensionKind.RE ∧
      (∀ q : Fin ett.rounds, t.val < q.val → q.val < epsilon.val →
        ett.series.data.kind q.succ = some TashkinovExtensionKind.RE) ∧
      ∀ v : V,
        v ∈ TreeSequenceVertexSet
            (ett.series.data.tree t.succ.castSucc) →
        v ≠ support →
        TwoColorComponentCycle G phi alpha beta (Sum.inl v) ∧
          Sum.inl support ∉
            TwoColorComponent G phi alpha beta (Sum.inl v) ∧
          ∀ w : V,
            Sum.inl w ∈
                TwoColorComponent G phi alpha beta (Sum.inl v) →
            w ∈ TreeSequenceVertexSet
              (ett.series.data.tree epsilon.succ.castSucc)
