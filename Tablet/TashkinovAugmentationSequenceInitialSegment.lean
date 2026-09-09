import Tablet.TashkinovAugmentationSequence
import Tablet.TreeSequenceInitialSegment

-- [TABLET NODE: TashkinovAugmentationSequenceInitialSegment]
theorem TashkinovAugmentationSequenceInitialSegment
    {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (phi : PartialEdgeColoring E k) (A B : TreeSequence G e0)
    (hAB : TashkinovAugmentationSequence phi A B) :
    TreeSequenceInitialSegment A B := by
-- BODY
  unfold TashkinovAugmentationSequence at hAB
  induction hAB with
  | refl =>
      exact ⟨le_rfl, (fun _ => rfl), (fun _ => rfl)⟩
  | @tail B C hAB hBC ih =>
      rcases hBC with ⟨hlenEq, hsegBC, _⟩
      rcases ih with ⟨hlenAB, hvertexAB, hedgeAB⟩
      rcases hsegBC with ⟨hlenBC, hvertexBC, hedgeBC⟩
      refine ⟨Nat.le_trans hlenAB hlenBC, ?_, ?_⟩
      · intro i
        calc
          C.vertex (Fin.castLE
              (Nat.succ_le_succ (Nat.le_trans hlenAB hlenBC)) i) =
              C.vertex (Fin.castLE (Nat.succ_le_succ hlenBC)
                (Fin.castLE (Nat.succ_le_succ hlenAB) i)) := by congr 1
          _ = B.vertex (Fin.castLE (Nat.succ_le_succ hlenAB) i) :=
            hvertexBC _
          _ = A.vertex i := hvertexAB i
      · intro i
        calc
          C.edge (Fin.castLE (Nat.le_trans hlenAB hlenBC) i) =
              C.edge (Fin.castLE hlenBC (Fin.castLE hlenAB i)) := by congr 1
          _ = B.edge (Fin.castLE hlenAB i) := hedgeBC _
          _ = A.edge i := hedgeAB i
