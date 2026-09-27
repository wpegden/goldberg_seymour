import Tablet.TwoColorComponentCycle
import Tablet.TwoColorPathComponent

-- [TABLET NODE: TwoColorPathComponentNotCycle]
theorem TwoColorPathComponentNotCycle {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) {k : ℕ}
    (phi : PartialEdgeColoring E k) (alpha beta : Fin k) (z : Sum V E)
    (hpath : TwoColorPathComponent G phi alpha beta z) :
    ¬ TwoColorComponentCycle G phi alpha beta z := by
-- BODY
  classical
  rintro ⟨cycle, hcycle⟩
  obtain ⟨_, x, hxComponent, hxLeaf⟩ := hpath
  have hxSupport : x ∈ cycle.walk.support := (hcycle x).2 hxComponent
  let rotated := cycle.walk.rotate x hxSupport
  have hrotated : rotated.IsCycle := cycle.isCycle.rotate hxSupport
  have hfirst : (TwoColorIncidenceGraph G phi alpha beta).Adj x rotated.snd :=
    rotated.adj_snd hrotated.not_nil
  have hlast : (TwoColorIncidenceGraph G phi alpha beta).Adj x rotated.penultimate :=
    (rotated.adj_penultimate hrotated.not_nil).symm
  exact hrotated.snd_ne_penultimate (hxLeaf hfirst hlast)
