import Tablet.ScheideAbsorbingElementary
import Tablet.ScheideEnlargedVertexSet
import Tablet.ScheideReplacementAbsorbing

-- [TABLET NODE: ScheideEnlargedElementary]
theorem ScheideEnlargedElementary {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d) :
    ColoredVertexSetElementary G phi (ScheideEnlargedVertexSet R) := by
-- BODY
  classical
  have hbase : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T ∪ AbsorbingVertices T phi) :=
    ScheideAbsorbingElementary G k e0 phi T C.globally_maximum
  unfold ColoredVertexSetElementary at hbase ⊢
  intro u hu v hv huv
  apply hbase
  · exact (by
      have hsub : ScheideEnlargedVertexSet R ⊆
          TreeSequenceVertexSet T ∪ AbsorbingVertices T phi := by
        unfold ScheideEnlargedVertexSet
        intro w hw
        simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ,
          Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with hw | ⟨d, _, hw | hw⟩
        · exact Finset.mem_union_left _ hw
        · exact Finset.mem_union_right _
            ((ScheideReplacementAbsorbing G k e0 phi T C D d (R d))
              (by simp [hw]))
        · exact Finset.mem_union_right _
            ((ScheideReplacementAbsorbing G k e0 phi T C D d (R d))
              (by simp [hw]))
      exact hsub hu)
  · exact (by
      have hsub : ScheideEnlargedVertexSet R ⊆
          TreeSequenceVertexSet T ∪ AbsorbingVertices T phi := by
        unfold ScheideEnlargedVertexSet
        intro w hw
        simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ,
          Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with hw | ⟨d, _, hw | hw⟩
        · exact Finset.mem_union_left _ hw
        · exact Finset.mem_union_right _
            ((ScheideReplacementAbsorbing G k e0 phi T C D d (R d))
              (by simp [hw]))
        · exact Finset.mem_union_right _
            ((ScheideReplacementAbsorbing G k e0 phi T C D d (R d))
              (by simp [hw]))
      exact hsub hv)
  exact huv
