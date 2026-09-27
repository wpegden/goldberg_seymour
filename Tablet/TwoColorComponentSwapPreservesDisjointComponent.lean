import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: TwoColorComponentSwapPreservesDisjointComponent]
theorem TwoColorComponentSwapPreservesDisjointComponent {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) {k : ℕ}
    (phi : PartialEdgeColoring E k) (alpha beta gamma delta : Fin k)
    (z x : Sum V E)
    (hactive : ∀ e : E,
      Sum.inr e ∈ TwoColorComponent G phi gamma delta z →
        phi e = some gamma ∨ phi e = some delta)
    (hdisjoint : Disjoint (TwoColorComponent G phi alpha beta x)
      (TwoColorComponent G phi gamma delta z)) :
    TwoColorComponent G (TwoColorComponentSwap G phi gamma delta z)
        alpha beta x =
      TwoColorComponent G phi alpha beta x := by
-- BODY
  classical
  let H := TwoColorIncidenceGraph G phi alpha beta
  let Hstar := TwoColorIncidenceGraph G
    (TwoColorComponentSwap G phi gamma delta z) alpha beta
  let C := TwoColorComponent G phi alpha beta x
  let K := TwoColorComponent G phi gamma delta z
  have old_neighbor {a b : Sum V E} (ha : a ∈ C) (hab : H.Adj a b) : b ∈ C := by
    let component := H.connectedComponentMk x
    exact (component.mem_supp_congr_adj hab).mp ha
  have forward_step {a b : Sum V E} (ha : a ∈ C) (hab : H.Adj a b) :
      b ∈ C ∧ Hstar.Adj a b := by
    have hb := old_neighbor ha hab
    refine ⟨hb, ?_⟩
    cases a with
    | inl v =>
        cases b with
        | inl w => simpa [H, TwoColorIncidenceGraph] using hab
        | inr e =>
            have heNotK : Sum.inr e ∉ K := by
              intro heK
              exact Set.disjoint_left.mp hdisjoint hb heK
            simpa [H, Hstar, TwoColorIncidenceGraph, TwoColorComponentSwap,
              K, heNotK] using hab
    | inr e =>
        cases b with
        | inl v =>
            have heNotK : Sum.inr e ∉ K := by
              intro heK
              exact Set.disjoint_left.mp hdisjoint ha heK
            simpa [H, Hstar, TwoColorIncidenceGraph, TwoColorComponentSwap,
              K, heNotK] using hab
        | inr f => simpa [H, TwoColorIncidenceGraph] using hab
  have reverse_step {a b : Sum V E} (ha : a ∈ C) (hab : Hstar.Adj a b) :
      b ∈ C ∧ H.Adj a b := by
    cases a with
    | inl v =>
        cases b with
        | inl w => simpa [Hstar, TwoColorIncidenceGraph] using hab
        | inr e =>
            have heNotK : Sum.inr e ∉ K := by
              intro heK
              have heColor := hactive e (by simpa [K] using heK)
              have hvK : Sum.inl v ∈ K := by
                change (TwoColorIncidenceGraph G phi gamma delta).connectedComponentMk
                    (Sum.inl v) =
                  (TwoColorIncidenceGraph G phi gamma delta).connectedComponentMk z
                have hedge : (TwoColorIncidenceGraph G phi gamma delta).Adj
                    (Sum.inl v) (Sum.inr e) := by
                  have hinc : Incident G v e := by
                    simpa [Hstar, TwoColorIncidenceGraph] using hab.1
                  simpa [TwoColorIncidenceGraph] using ⟨hinc, heColor⟩
                have heComponent :
                    (TwoColorIncidenceGraph G phi gamma delta).connectedComponentMk
                        (Sum.inr e) =
                      (TwoColorIncidenceGraph G phi gamma delta).connectedComponentMk z :=
                  heK
                exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                  hedge).trans heComponent
              exact Set.disjoint_left.mp hdisjoint ha hvK
            have hold : H.Adj (Sum.inl v) (Sum.inr e) := by
              simpa [H, Hstar, TwoColorIncidenceGraph, TwoColorComponentSwap,
                K, heNotK] using hab
            exact ⟨old_neighbor ha hold, hold⟩
    | inr e =>
        cases b with
        | inl v =>
            have heNotK : Sum.inr e ∉ K := by
              intro heK
              exact Set.disjoint_left.mp hdisjoint ha heK
            have hold : H.Adj (Sum.inr e) (Sum.inl v) := by
              simpa [H, Hstar, TwoColorIncidenceGraph, TwoColorComponentSwap,
                K, heNotK] using hab
            exact ⟨old_neighbor ha hold, hold⟩
        | inr f => simpa [Hstar, TwoColorIncidenceGraph] using hab
  have forward_walk {a b : Sum V E} (ha : a ∈ C) (p : H.Walk a b) :
      b ∈ C ∧ Nonempty (Hstar.Walk a b) := by
    induction p with
    | nil => exact ⟨ha, ⟨SimpleGraph.Walk.nil⟩⟩
    | @cons u v w huv p ih =>
        obtain ⟨hv, huvStar⟩ := forward_step ha huv
        obtain ⟨hw, ⟨pStar⟩⟩ := ih hv
        exact ⟨hw, ⟨SimpleGraph.Walk.cons huvStar pStar⟩⟩
  have reverse_walk {a b : Sum V E} (ha : a ∈ C) (p : Hstar.Walk a b) :
      b ∈ C ∧ Nonempty (H.Walk a b) := by
    induction p with
    | nil => exact ⟨ha, ⟨SimpleGraph.Walk.nil⟩⟩
    | @cons u v w huv p ih =>
        obtain ⟨hv, huvOld⟩ := reverse_step ha huv
        obtain ⟨hw, ⟨pOld⟩⟩ := ih hv
        exact ⟨hw, ⟨SimpleGraph.Walk.cons huvOld pOld⟩⟩
  ext y
  constructor
  · intro hy
    change Hstar.connectedComponentMk y = Hstar.connectedComponentMk x at hy
    have p : Hstar.Reachable x y :=
      SimpleGraph.ConnectedComponent.exact hy.symm
    obtain ⟨hyC, -⟩ := reverse_walk (a := x) (b := y) (by rfl) p.some
    exact hyC
  · intro hy
    change y ∈ C at hy
    change Hstar.connectedComponentMk y = Hstar.connectedComponentMk x
    have p : H.Reachable x y := by
      exact SimpleGraph.ConnectedComponent.exact hy.symm
    obtain ⟨-, hp⟩ := forward_walk (a := x) (b := y) (by rfl) p.some
    exact (SimpleGraph.ConnectedComponent.sound hp).symm
