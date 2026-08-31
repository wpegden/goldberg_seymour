import Tablet.IncidentCoreChromaticIndex
import Tablet.IncidentCoreKTriple
import Tablet.IncidentCoreTreeTransport
import Tablet.TashkinovOrder

-- [TABLET NODE: IncidentCoreTashkinovOrder]
theorem IncidentCoreTashkinovOrder {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) :
    TashkinovOrder (IncidentCore G) = TashkinovOrder G := by
-- BODY
  classical
  have hindex := (IncidentCoreChromaticIndex G).1
  have hforward := (IncidentCoreTreeTransport G).1
  have hbackward := (IncidentCoreTreeTransport G).2
  let k := ChromaticIndex G - 1
  unfold TashkinovOrder
  dsimp only
  apply Nat.le_antisymm
  · apply Finset.max'_le
    intro n hn
    rcases Finset.mem_insert.mp hn with rfl | hn
    · exact Nat.zero_le _
    · rcases Finset.mem_filter.mp hn with ⟨hnrange, ⟨e0, phi, Tc, htriple, htree, hcard⟩⟩
      obtain ⟨T, hlen, hvertices, hedges, hsize, htreeeq⟩ :=
        hbackward e0 (ChromaticIndex (IncidentCore G) - 1) phi Tc
      have hbound : (TreeSequenceVertexSet T).card ≤ Fintype.card V := by
        simpa [TreeSequenceVertexSet, Finset.card_image_of_injective _ T.vertex_injective] using
          (Fintype.card_le_of_injective T.vertex T.vertex_injective)
      apply Finset.le_max' _ _
      apply Finset.mem_insert.mpr
      right
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_range.mpr (by omega)
      · have hmem : ∃ (e : E) (p : PartialEdgeColoring E (ChromaticIndex (IncidentCore G) - 1))
            (S : TreeSequence G e),
            KTriple G (ChromaticIndex (IncidentCore G) - 1) e p ∧
              TashkinovTree G e p S ∧ (TreeSequenceVertexSet S).card = n := by
          refine ⟨e0, phi, T, ?_, htreeeq.mpr htree, hsize.symm.trans hcard⟩
          exact (IncidentCoreKTriple G (ChromaticIndex (IncidentCore G) - 1) e0 phi).mp htriple
        have bridge :
            (∃ (e : E) (p : PartialEdgeColoring E (ChromaticIndex (IncidentCore G) - 1))
              (S : TreeSequence G e),
              KTriple G (ChromaticIndex (IncidentCore G) - 1) e p ∧
                TashkinovTree G e p S ∧ (TreeSequenceVertexSet S).card = n) =
            (∃ (e : E) (p : PartialEdgeColoring E (ChromaticIndex G - 1))
              (S : TreeSequence G e),
              KTriple G (ChromaticIndex G - 1) e p ∧
                TashkinovTree G e p S ∧ (TreeSequenceVertexSet S).card = n) := by
          exact congrArg (fun q => ∃ (e : E) (p : PartialEdgeColoring E (q - 1))
            (S : TreeSequence G e), KTriple G (q - 1) e p ∧
              TashkinovTree G e p S ∧ (TreeSequenceVertexSet S).card = n) hindex
        exact bridge ▸ hmem
  · apply Finset.max'_le
    intro n hn
    rcases Finset.mem_insert.mp hn with rfl | hn
    · exact Nat.zero_le _
    · rcases Finset.mem_filter.mp hn with ⟨hnrange, ⟨e0, phi, T, htriple, htree, hcard⟩⟩
      obtain ⟨Tc, hlen, hvertices, hedges, hsize, htreeeq⟩ :=
        hforward e0 k phi T
      have hbound : (TreeSequenceVertexSet Tc).card ≤ Fintype.card (IncidentVertex G) := by
        simpa [TreeSequenceVertexSet, Finset.card_image_of_injective _ Tc.vertex_injective] using
          (Fintype.card_le_of_injective Tc.vertex Tc.vertex_injective)
      apply Finset.le_max' _ _
      apply Finset.mem_insert.mpr
      right
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_range.mpr (by omega)
      · have hmem : ∃ (e : E) (p : PartialEdgeColoring E (ChromaticIndex G - 1))
            (S : TreeSequence (IncidentCore G) e),
            KTriple (IncidentCore G) (ChromaticIndex G - 1) e p ∧
              TashkinovTree (IncidentCore G) e p S ∧ (TreeSequenceVertexSet S).card = n := by
          refine ⟨e0, phi, Tc, (IncidentCoreKTriple G k e0 phi).mpr htriple,
            htreeeq.mpr htree, hsize.trans hcard⟩
        have bridge :
            (∃ (e : E) (p : PartialEdgeColoring E (ChromaticIndex G - 1))
              (S : TreeSequence (IncidentCore G) e),
              KTriple (IncidentCore G) (ChromaticIndex G - 1) e p ∧
                TashkinovTree (IncidentCore G) e p S ∧ (TreeSequenceVertexSet S).card = n) =
            (∃ (e : E) (p : PartialEdgeColoring E (ChromaticIndex (IncidentCore G) - 1))
              (S : TreeSequence (IncidentCore G) e),
              KTriple (IncidentCore G) (ChromaticIndex (IncidentCore G) - 1) e p ∧
                TashkinovTree (IncidentCore G) e p S ∧ (TreeSequenceVertexSet S).card = n) := by
          exact congrArg (fun q => ∃ (e : E) (p : PartialEdgeColoring E (q - 1))
            (S : TreeSequence (IncidentCore G) e), KTriple (IncidentCore G) (q - 1) e p ∧
              TashkinovTree (IncidentCore G) e p S ∧ (TreeSequenceVertexSet S).card = n) hindex.symm
        exact bridge ▸ hmem
