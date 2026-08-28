import Tablet.ExtendedTashkinovTree

-- [TABLET NODE: ExtensionBaseCaseOneIndices]
noncomputable def ExtensionBaseCaseOneIndices {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (p : ℕ) (indices : Fin (p + 1) → Fin ett.rounds)
    (b : Fin (p + 1)) : Finset (Fin ett.rounds) :=
-- BODY
  (Finset.univ.filter fun a : Fin (p + 1) => a.val < b.val).image indices
