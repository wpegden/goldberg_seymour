import Tablet.GeneralHighIndexElementary

-- [TABLET NODE: ThmGS]
theorem ThmGS {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) :
    ChromaticIndex G ≤ max (MaximumDegree G + 1) (DensityCeil G) := by
-- BODY
  by_cases hbound : ChromaticIndex G ≤ MaximumDegree G + 1
  · exact le_max_of_le_left hbound
  · have hhigh : MaximumDegree G + 2 ≤ ChromaticIndex G := by
      omega
    have helementary : Elementary G := GeneralHighIndexElementary G hhigh
    have hequality : ChromaticIndex G = DensityCeil G := helementary
    rw [hequality]
    exact le_max_of_le_right (le_refl _)
