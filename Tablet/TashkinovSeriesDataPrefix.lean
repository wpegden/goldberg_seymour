import Tablet.TashkinovSeriesData

-- [TABLET NODE: TashkinovSeriesDataPrefix]
def TashkinovSeriesDataPrefix {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    (m : ℕ) (hm : m ≤ rounds) (data : TashkinovSeriesData G k rounds e0) :
    TashkinovSeriesData G k m e0 :=
-- BODY
  { tree := fun i => data.tree (Fin.castLE (by omega) i)
    coloring := fun i => data.coloring (Fin.castLE (by omega) i)
    stored := fun i => data.stored (Fin.castLE (by omega) i)
    connectingEdges := fun i => data.connectingEdges (Fin.castLE (by omega) i)
    kind := fun i => data.kind (Fin.castLE (by omega) i)
    chosenVertex := fun i => data.chosenVertex (Fin.castLE (by omega) i)
    outsideVertex := fun i => data.outsideVertex (Fin.castLE (by omega) i)
    delta := fun i => data.delta (Fin.castLE (by omega) i)
    gamma := fun i => data.gamma (Fin.castLE (by omega) i) }
