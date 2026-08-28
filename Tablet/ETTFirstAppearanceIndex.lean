import Tablet.ExtendedTashkinovLadderStage
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: ETTFirstAppearanceIndex]
noncomputable def ETTFirstAppearanceIndex {V E : Type*} [Fintype V]
    [Fintype E] [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ}
    {e0 : E} {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating) (v : V)
    (hv : v ∈ TreeSequenceVertexSet T) : ℕ := by
-- BODY
  classical
  let candidates : Finset (Fin (ett.rounds + 1)) :=
    Finset.univ.filter fun i =>
      v ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)
  have hfinal :
      ExtendedTashkinovLadderStage ett (Fin.last ett.rounds) = T := by
    unfold ExtendedTashkinovLadderStage
    exact Fin.lastCases_last
  have hlast : Fin.last ett.rounds ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hfinal]
    exact hv
  exact (candidates.min' ⟨Fin.last ett.rounds, hlast⟩).val + 1
