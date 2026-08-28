import Tablet.DefectiveColors
import Tablet.GlobalMaximumTriple
import Tablet.ScheideGlobalMaximumOrder
import Tablet.TreeFreeColors

-- [TABLET NODE: ScheideGlobalMaximumUnused]
theorem ScheideGlobalMaximumUnused {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T) :
    Disjoint (DefectiveColors G phi (TreeSequenceVertexSet T))
        (TreeUsedColors phi T) ∧
      Disjoint (TreeFreeColors phi T) (TreeUsedColors phi T) := by
-- BODY
  classical
  have horder := ScheideGlobalMaximumOrder G k e0 phi T hglobal
  have hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) :=
    horder.2.2.2.2
  constructor
  · rw [Finset.disjoint_left]
    intro alpha hdef hused
    have hcard : 2 ≤ (BoundaryColorEdges G phi
        (TreeSequenceVertexSet T) alpha).card := by
      change alpha ∈ Finset.univ.filter
        (fun alpha => DefectiveColor G phi (TreeSequenceVertexSet T) alpha) at hdef
      exact (Finset.mem_filter.mp hdef).2
    have hpos : 0 < (BoundaryColorEdges G phi
        (TreeSequenceVertexSet T) alpha).card :=
      lt_of_lt_of_le Nat.zero_lt_two hcard
    obtain ⟨f, hf⟩ := Finset.card_pos.mp hpos
    have hfb : f ∈ BoundaryEdges G (TreeSequenceVertexSet T) := by
      exact (Finset.mem_filter.mp hf).1
    have hfc : phi f = some alpha := by
      exact (Finset.mem_filter.mp hf).2
    have hnot : ∀ v, v ∈ TreeSequenceVertexSet T →
        alpha ∉ MissingColors G phi v := by
      intro v hv hm
      exact (hclosed hfb hv hfc) hm
    have htree := hglobal.2.1
    simp [TreeUsedColors] at hused
    obtain ⟨j, hj, hje⟩ := hused
    obtain ⟨i, c, hcolor, hmiss⟩ := htree j hj
    have hac : c = alpha := by
      have hac' : alpha = c := by simpa [hje] using hcolor
      exact hac'.symm
    have hv : T.vertex (Fin.castLT i
        (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))) ∈
        TreeSequenceVertexSet T := by
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    exact hnot _ hv (hac ▸ hmiss)
  · change Disjoint (TreeMissingColors phi T \ TreeUsedColors phi T)
      (TreeUsedColors phi T)
    exact Finset.sdiff_disjoint
