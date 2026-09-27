import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: TwoColorComponentSwapDisjointPairGraph]
theorem TwoColorComponentSwapDisjointPairGraph {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) {k : ℕ}
    (phi : PartialEdgeColoring E k) (alpha beta gamma delta : Fin k)
    (z : Sum V E)
    (hdisjoint : Disjoint ({alpha, beta} : Finset (Fin k)) {gamma, delta}) :
    TwoColorIncidenceGraph G
        (TwoColorComponentSwap G phi gamma delta z) alpha beta =
      TwoColorIncidenceGraph G phi alpha beta := by
-- BODY
  classical
  have hag : alpha ≠ gamma := by
    intro h
    subst gamma
    have := Finset.disjoint_left.mp hdisjoint (Finset.mem_insert_self alpha {beta})
      (Finset.mem_insert_self alpha {delta})
    exact this
  have had : alpha ≠ delta := by
    intro h
    subst delta
    have := Finset.disjoint_left.mp hdisjoint (Finset.mem_insert_self alpha {beta})
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self alpha))
    exact this
  have hbg : beta ≠ gamma := by
    intro h
    subst gamma
    have := Finset.disjoint_left.mp hdisjoint
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self beta))
      (Finset.mem_insert_self beta {delta})
    exact this
  have hbd : beta ≠ delta := by
    intro h
    subst delta
    have := Finset.disjoint_left.mp hdisjoint
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self beta))
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self beta))
    exact this
  have hga : gamma ≠ alpha := Ne.symm hag
  have hgb : gamma ≠ beta := Ne.symm hbg
  have hda : delta ≠ alpha := Ne.symm had
  have hdb : delta ≠ beta := Ne.symm hbd
  ext x y
  cases x with
  | inl v =>
      cases y with
      | inl w => simp [TwoColorIncidenceGraph]
      | inr e =>
          simp only [TwoColorIncidenceGraph, and_congr_right_iff]
          intro hinc
          simp only [TwoColorComponentSwap]
          by_cases he : Sum.inr e ∈ TwoColorComponent G phi gamma delta z
          · simp only [if_pos he]
            by_cases heg : phi e = some gamma
            · simp [heg, hga, hgb, hda, hdb]
            · by_cases hed : phi e = some delta
              · have hgd : gamma ≠ delta := by
                  intro hgd
                  apply heg
                  simpa [hgd] using hed
                simp [heg, hed, hgd.symm, hga, hgb, hda, hdb]
              · simp [heg, hed]
          · simp [he]
  | inr e =>
      cases y with
      | inl v =>
          simp only [TwoColorIncidenceGraph, and_congr_right_iff]
          intro hinc
          simp only [TwoColorComponentSwap]
          by_cases he : Sum.inr e ∈ TwoColorComponent G phi gamma delta z
          · simp only [if_pos he]
            by_cases heg : phi e = some gamma
            · simp [heg, hga, hgb, hda, hdb]
            · by_cases hed : phi e = some delta
              · have hgd : gamma ≠ delta := by
                  intro hgd
                  apply heg
                  simpa [hgd] using hed
                simp [heg, hed, hgd.symm, hga, hgb, hda, hdb]
              · simp [heg, hed]
          · simp [he]
      | inr f => simp [TwoColorIncidenceGraph]
