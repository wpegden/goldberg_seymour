import Tablet.IncidentCoreCritical
import Tablet.IncidentCoreElementaryTransfer
import Tablet.IncidentCoreEndpoints
import Tablet.IncidentCoreMaximumDegree
import Tablet.IncidentCoreNoIsolated
import Tablet.IncidentCoreTashkinovOrder

-- [TABLET NODE: IncidentCoreReduction]
theorem IncidentCoreReduction {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) :
    let H := IncidentCore G
    (∀ e : E,
      Sym2.map (fun x : IncidentVertex G => x.1) (H.ends e) = G.ends e) ∧
    (∀ x : IncidentVertex G, ∃ e : E, Incident H x e) ∧
    (Critical H ↔ Critical G) ∧
    ChromaticIndex H = ChromaticIndex G ∧
    MaximumDegree H = MaximumDegree G ∧
    TashkinovOrder H = TashkinovOrder G ∧
    (Elementary H → Elementary G) := by
-- BODY
  dsimp
  exact ⟨IncidentCoreEndpoints G, IncidentCoreNoIsolated G,
    IncidentCoreCritical G, (IncidentCoreChromaticIndex G).1,
    IncidentCoreMaximumDegree G, IncidentCoreTashkinovOrder G,
    IncidentCoreElementaryTransfer G⟩
