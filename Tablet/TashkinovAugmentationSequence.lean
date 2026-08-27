import Tablet.TashkinovAugmentation

-- [TABLET NODE: TashkinovAugmentationSequence]
def TashkinovAugmentationSequence {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (phi : PartialEdgeColoring E k) (T T' : TreeSequence G e0) : Prop :=
-- BODY
  Relation.ReflTransGen (TashkinovAugmentation phi) T T'
