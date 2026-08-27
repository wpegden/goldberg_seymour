import Tablet.TreeMissingColors
import Tablet.TreeSequenceInitialSegment

-- [TABLET NODE: TashkinovAugmentation]
def TashkinovAugmentation {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (phi : PartialEdgeColoring E k) (T T' : TreeSequence G e0) : Prop :=
-- BODY
  ∃ hlen : T'.length = T.length + 1,
    TreeSequenceInitialSegment T T' ∧
      ∃ c : Fin k,
        phi (T'.edge (Fin.cast hlen.symm (Fin.last T.length))) = some c ∧
          c ∈ TreeMissingColors phi T
