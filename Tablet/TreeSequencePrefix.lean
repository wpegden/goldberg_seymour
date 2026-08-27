import Tablet.TreeSequence

-- [TABLET NODE: TreeSequencePrefix]
noncomputable def TreeSequencePrefix {V E : Type*} {G : LooplessMultigraph V E}
    {e0 : E} (T : TreeSequence G e0) (q : ℕ) (hq : 1 ≤ q)
    (hqt : q ≤ T.length) : TreeSequence G e0 := by
-- BODY
  classical
  refine
    { length := q
      positive := hq
      vertex := fun i => T.vertex (Fin.castLE (Nat.succ_le_succ hqt) i)
      edge := fun i => T.edge (Fin.castLE hqt i)
      vertex_injective := ?_
      edge_injective := ?_
      first_edge := ?_
      attaches := ?_ }
  · intro i j hij
    apply Fin.ext
    simpa only [Fin.castLE] using
      congrArg (fun x => x.val) (T.vertex_injective hij)
  · intro i j hij
    apply Fin.ext
    simpa only [Fin.castLE] using
      congrArg (fun x => x.val) (T.edge_injective hij)
  · simpa only [Fin.castLE] using T.first_edge
  · intro j
    obtain ⟨i, hi⟩ := T.attaches (Fin.castLE hqt j)
    refine ⟨i, ?_⟩
    simpa only [Fin.castLE, Fin.castLT, Fin.succ] using hi
