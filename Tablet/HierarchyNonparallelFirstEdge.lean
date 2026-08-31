import Tablet.TashkinovHierarchy

-- [TABLET NODE: HierarchyNonparallelFirstEdge]
theorem HierarchyNonparallelFirstEdge {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T phi}
    {base : HierarchyBase ett phi} (H : TashkinovHierarchy ett base)
    (f : E)
    (hkind : ett.series.data.kind (Fin.last ett.rounds) =
        some TashkinovExtensionKind.SE ∨
      ett.series.data.kind (Fin.last ett.rounds) =
        some TashkinovExtensionKind.RE)
    (hedges : ett.series.data.connectingEdges (Fin.last ett.rounds) = {f}) :
    let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
    ∃ r : Fin (H.stage ⟨1, by omega⟩).length,
      r.val = Tn.length ∧ (H.stage ⟨1, by omega⟩).edge r = f := by
-- BODY
  sorry
