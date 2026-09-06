import Tablet.HierarchySituationTwoSubcaseOneOneNonexceptional
import Tablet.HierarchySituationTwoSubcaseOneOneStoredException
import Tablet.HierarchySituationTwoCaseOneData
import Tablet.HierarchyStoredColorsAt

-- [TABLET NODE: HierarchySituationTwoSubcaseOneOne]
theorem HierarchySituationTwoSubcaseOneOne {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (D : HierarchySituationTwoCaseOneData
      G k e0 input T phi ett base C ctx) :
    False := by
-- BODY
  classical
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let stored := HierarchyStoredColorsAt H q
  by_cases htheta :
      D.theta ∈ stored.biUnion (C.good.gamma q)
  · rw [Finset.mem_biUnion] at htheta
    rcases htheta with ⟨eta, hetaStored, hthetaPair⟩
    by_cases hetaMissing :
        eta ∈ MissingColors G phi (T.vertex D.penultimateVertexIndex)
    · exact HierarchySituationTwoSubcaseOneOneStoredException
        G k e0 input T phi ett base C ctx D eta
        (by simpa [stored, q, H] using hetaStored)
        (by simpa [q, H] using hthetaPair) hetaMissing
    · exact HierarchySituationTwoSubcaseOneOneNonexceptional
        G k e0 input T phi ett base C ctx D
        (Or.inr ⟨eta, by simpa [stored, q, H] using hetaStored,
          by simpa [q, H] using hthetaPair, hetaMissing⟩)
  · exact HierarchySituationTwoSubcaseOneOneNonexceptional
      G k e0 input T phi ett base C ctx D
      (Or.inl (by simpa [stored, q, H] using htheta))
