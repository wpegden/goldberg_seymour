import Tablet.Incident
import Tablet.MissingColors
import Tablet.PartialEdgeColoring
import Tablet.TreeVerticesBefore

-- [TABLET NODE: StableColoringBeforeVertex]
def StableColoringBeforeVertex {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (v : V) (C : Finset (Fin k))
    (phi pi : PartialEdgeColoring E k) : Prop :=
-- BODY
  (∀ f, (∃ w ∈ TreeVerticesBefore T v, Incident G w f) →
      (∃ c ∈ ((TreeVerticesBefore T v).biUnion fun w =>
          MissingColors G phi w) ∪ C, phi f = some c) →
      pi f = phi f) ∧
    ∀ w ∈ TreeVerticesBefore T v,
      MissingColors G pi w = MissingColors G phi w
