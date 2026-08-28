import Tablet.TashkinovSeriesData
import Tablet.TreeMissingColors

-- [TABLET NODE: TashkinovStoredColors]
noncomputable def TashkinovStoredColors {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    (data : TashkinovSeriesData G k rounds e0) (i : Fin (rounds + 1)) :
    Finset (Fin k) := by
-- BODY
  classical
  exact if i.val = 0 then ∅ else
    (Finset.univ.biUnion fun h : Fin (rounds + 1) =>
      if h.val ≤ i.val then data.stored h else ∅) \
      TreeMissingColors (data.coloring i) (data.tree i.castSucc)
