import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetElementary
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.OutsideTreeColorSwap
import Tablet.OutsideTreeColorSwapStable
import Tablet.PresentColors
import Tablet.P2966_T1_OutsideSwapPrefixEffects
import Tablet.StableColoringBeforeVertex
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVerticesBefore
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph

set_option maxHeartbeats 400000

-- [TABLET NODE: ExtensionBaseClaim45Singleton]
theorem ExtensionBaseClaim45Singleton {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (Tn Tj seed TjPrime : TreeSequence G e0)
    (phiJ rho1 : PartialEdgeColoring E k)
    (Dprev supportColors : Finset (Fin k))
    (gammaFirst gammaN deltaN beta : Fin k)
    (terminalSupport u x z : V)
    (p : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk
      (Sum.inl terminalSupport) (Sum.inl x))
    (exitPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk
      (Sum.inl x) (Sum.inl u))
    (zPosition : Fin (Tj.length + 1))
    (hgammaFirst : gammaFirst = gammaN)
    (hrhoProper : IsProperEdgeColoring G rho1)
    (hrhoOne : IsOneEdgeUncolored rho1 e0)
    (hTjN : TreeSequenceInitialSegment Tj Tn)
    (hseedJ : TreeSequenceInitialSegment seed Tj)
    (hseedPrime : TreeSequenceInitialSegment seed TjPrime)
    (hseedTerminal : seed.vertex (Fin.last seed.length) = terminalSupport)
    (hterminalTj : terminalSupport ∈ TreeSequenceVertexSet Tj)
    (hterminalSeed : terminalSupport ∈ TreeSequenceVertexSet seed)
    (hclosure : TashkinovClosure rho1 seed TjPrime)
    (hprimeElementary : ColoredVertexSetElementary G rho1
      (TreeSequenceVertexSet TjPrime))
    (hgammaDelta : gammaN ≠ deltaN)
    (hbetaGamma : beta ≠ gammaN)
    (hbetaDelta : beta ≠ deltaN)
    (hbeta : beta ∈ MissingColors G rho1 u)
    (hdeltaMissing : deltaN ∈ MissingColors G rho1 terminalSupport)
    (hpath : p.IsPath)
    (hcomponent : {y : Sum V E | y ∈ p.support} =
      TwoColorComponent G rho1 gammaN deltaN (Sum.inl terminalSupport))
    (hxOutside : x ∉
      TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime)
    (huPrime : u ∈ TreeSequenceVertexSet TjPrime)
    (huOutside : u ∉ TreeSequenceVertexSet Tn)
    (hexitPath : exitPath.IsPath)
    (hexitLength : 2 ≤ exitPath.length)
    (hexitSupport : ∀ y : Sum V E, y ∈ exitPath.support → y ∈ p.support)
    (hexitIntersection : ∀ w : V,
      w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime →
      (Sum.inl w ∈ exitPath.support ↔ w = u))
    (hexitBoundary : ∃ g ∈ BoundaryColorEdges G rho1
        (TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime) gammaN,
      Incident G u g ∧ Sum.inr g ∈ exitPath.support)
    (hb1 : StableColoringBeforeVertex Tj terminalSupport hterminalTj
      Dprev phiJ rho1)
    (hb2Missing : ∀ v : V,
      v ∈ (TreeSequenceVertexSet Tj).erase terminalSupport →
      MissingColors G rho1 v = MissingColors G phiJ v)
    (haugmentation : TashkinovAugmentationSequence phiJ seed Tj)
    (hb2Edges : ∀ a : Fin Tj.length, seed.length ≤ a.val →
      rho1 (Tj.edge a) = phiJ (Tj.edge a))
    (hdeltaPhiJ : deltaN ∉ TreeMissingColors phiJ Tj)
    (hz : z ∈ TreeSequenceVertexSet Tj)
    (hzPosition : Tj.vertex zPosition = z)
    (hzAfter : seed.length ≤ zPosition.val)
    (hzChoice :
      (seed.length < zPosition.val ∧
          beta ∈ MissingColors G rho1 z ∧
          ∀ r : Fin (Tj.length + 1),
            seed.length < r.val → r.val < zPosition.val →
            beta ∉ MissingColors G rho1 (Tj.vertex r)) ∨
        (zPosition = Fin.last Tj.length ∧
          ∀ r : Fin (Tj.length + 1), seed.length < r.val →
            beta ∉ MissingColors G rho1 (Tj.vertex r)))
    (hzBefore : ∀ w ∈ TreeVerticesBefore Tj z hz,
      beta ∉ MissingColors G rho1 w)
    (hzEdges : ∀ a : Fin Tj.length, seed.length ≤ a.val →
      a.val < zPosition.val → rho1 (Tj.edge a) ≠ some beta) :
    let rho0 := OutsideTreeColorSwap TjPrime rho1 beta deltaN
    let rho3 := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u)
    IsProperEdgeColoring G rho3 ∧ IsOneEdgeUncolored rho3 e0 ∧
      StableColoringBeforeVertex Tj terminalSupport hterminalTj
        Dprev phiJ rho3 ∧
      ((∀ v : V,
        v ∈ (((TreeVerticesBefore Tj z hz ∪ {z}) ∪
            (TreeVerticesBefore TjPrime u huPrime ∪ {u})).erase u).erase z →
        MissingColors G rho3 v = MissingColors G rho1 v) ∧
        (∀ f : E,
          ((∃ a : Fin Tj.length,
              seed.length ≤ a.val ∧ a.val < zPosition.val ∧
                Tj.edge a = f) ∨
            (∃ (a : Fin TjPrime.length)
              (uPosition : Fin (TjPrime.length + 1)),
              TjPrime.vertex uPosition = u ∧ a.val < uPosition.val ∧
                TjPrime.edge a = f)) →
          rho3 f = rho1 f) ∧
        (beta ∈ MissingColors G rho1 z →
          deltaN ∈ MissingColors G rho3 z) ∧
        (z ∈ TreeVerticesBefore TjPrime u huPrime →
          MissingColors G rho3 z = MissingColors G rho1 z)) ∧
      gammaFirst ∈ MissingColors G rho3 u := by
-- BODY
  classical
  have initial_subset {A B : TreeSequence G e0}
      (h : TreeSequenceInitialSegment A B) :
      TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro v hv
    simp only [TreeSequenceVertexSet, Finset.mem_image] at hv ⊢
    obtain ⟨i, hi, hvi⟩ := hv
    obtain ⟨hlen, hvertices, hedges⟩ := h
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i, Finset.mem_univ _,
      (hvertices i).trans hvi⟩
  have hterminalPrime : terminalSupport ∈ TreeSequenceVertexSet TjPrime :=
    initial_subset hseedPrime hterminalSeed
  have huSeed : u ∉ TreeSequenceVertexSet seed := by
    intro hu
    exact huOutside (initial_subset hTjN (initial_subset hseedJ hu))
  let rho0 := OutsideTreeColorSwap TjPrime rho1 beta deltaN
  let rho3 := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u)
  have hbetaTree : beta ∈ TreeMissingColors rho1 TjPrime := by
    unfold TreeMissingColors
    exact Finset.mem_biUnion.mpr ⟨u, huPrime, hbeta⟩
  have hdeltaTree : deltaN ∈ TreeMissingColors rho1 TjPrime := by
    unfold TreeMissingColors
    exact Finset.mem_biUnion.mpr ⟨terminalSupport, hterminalPrime,
      hdeltaMissing⟩
  have houtside := OutsideTreeColorSwapStable TjPrime supportColors rho1
    beta deltaN hrhoProper hrhoOne hclosure.2 hbetaTree hdeltaTree
    hbetaDelta
  change IsProperEdgeColoring G rho0 ∧ IsOneEdgeUncolored rho0 e0 ∧
      StableColoring TjPrime supportColors rho1 rho0 ∧
      ∀ f : E, TreeIncidentEdge TjPrime f → rho0 f = rho1 f at houtside
  rcases houtside with ⟨hrho0Proper, hrho0One, hrho0Stable, hrho0Fixed⟩
  have hgammaBeta : gammaN ≠ beta := Ne.symm hbetaGamma
  have hrho3Proper : IsProperEdgeColoring G rho3 :=
    TwoColorComponentSwapProper G rho0 gammaN beta hgammaBeta
      hrho0Proper (Sum.inl u)
  have hrho3One : IsOneEdgeUncolored rho3 e0 := by
    unfold IsOneEdgeUncolored at hrho0One ⊢
    constructor
    · simp [rho3, TwoColorComponentSwap, hrho0One.1]
    · intro f hfe
      obtain ⟨c, hc⟩ := hrho0One.2 f hfe
      have hne : rho3 f ≠ none := by
        by_cases hK : Sum.inr f ∈
            TwoColorComponent G rho0 gammaN beta (Sum.inl u)
        · by_cases hcg : c = gammaN
          · simp [rho3, TwoColorComponentSwap, hK, hc, hcg]
          · by_cases hcb : c = beta
            · simp [rho3, TwoColorComponentSwap, hK, hc, hcg, hcb,
                hgammaBeta, hbetaGamma]
            · simp [rho3, TwoColorComponentSwap, hK, hc, hcg, hcb]
        · simp [rho3, TwoColorComponentSwap, hK, hc]
      obtain ⟨d, hd⟩ := Option.ne_none_iff_exists.mp hne
      exact ⟨d, hd.symm⟩
  have hbetaRho0 : beta ∈ MissingColors G rho0 u := by
    rw [hrho0Stable.2 u huPrime]
    exact hbeta
  obtain ⟨g, hgBoundary, hug, hgExit⟩ := hexitBoundary
  have hgRho1 : rho1 g = some gammaN :=
    (Finset.mem_filter.mp hgBoundary).2
  have hgRho0 : rho0 g = some gammaN := by
    rw [hrho0Fixed g ⟨u, huPrime, hug⟩]
    exact hgRho1
  have hgComponent : Sum.inr g ∈
      TwoColorComponent G rho0 gammaN beta (Sum.inl u) := by
    change (TwoColorIncidenceGraph G rho0 gammaN beta).connectedComponentMk
        (Sum.inr g) =
      (TwoColorIncidenceGraph G rho0 gammaN beta).connectedComponentMk
        (Sum.inl u)
    have hadj : (TwoColorIncidenceGraph G rho0 gammaN beta).Adj
        (Sum.inl u) (Sum.inr g) := ⟨hug, Or.inl hgRho0⟩
    exact
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm
  have hgRho3 : rho3 g = some beta := by
    simp [rho3, TwoColorComponentSwap, hgComponent, hgRho0,
      hgammaBeta, hbetaGamma]
  have hbetaRho3 : beta ∉ MissingColors G rho3 u := by
    intro hb
    have hbPresent : beta ∉ PresentColors G rho3 u := by
      simpa [MissingColors] using hb
    apply hbPresent
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨g, hug, hgRho3⟩
  have hgammaRho3 : gammaN ∈ MissingColors G rho3 u := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hgPresent
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
      true_and] at hgPresent
    obtain ⟨f, huf, hfRho3⟩ := hgPresent
    by_cases hfComponent : Sum.inr f ∈
        TwoColorComponent G rho0 gammaN beta (Sum.inl u)
    · by_cases hfGamma : rho0 f = some gammaN
      · have : (some beta : Option (Fin k)) = some gammaN := by
          simpa [rho3, TwoColorComponentSwap, hfComponent, hfGamma,
            hgammaBeta, hbetaGamma] using hfRho3
        exact hbetaGamma (Option.some.inj this)
      · by_cases hfBeta : rho0 f = some beta
        · have hnotPresent : beta ∉ PresentColors G rho0 u := by
            simpa [MissingColors] using hbetaRho0
          exact hnotPresent (by
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
              true_and]
            exact ⟨f, huf, hfBeta⟩)
        · have : rho0 f = some gammaN := by
            simpa [rho3, TwoColorComponentSwap, hfComponent, hfGamma,
              hfBeta] using hfRho3
          exact hfGamma this
    · have hfRho0 : rho0 f = some gammaN := by
        simpa [rho3, TwoColorComponentSwap, hfComponent] using hfRho3
      have hadj : (TwoColorIncidenceGraph G rho0 gammaN beta).Adj
          (Sum.inl u) (Sum.inr f) := ⟨huf, Or.inl hfRho0⟩
      apply hfComponent
      change (TwoColorIncidenceGraph G rho0 gammaN beta).connectedComponentMk
          (Sum.inr f) =
        (TwoColorIncidenceGraph G rho0 gammaN beta).connectedComponentMk
          (Sum.inl u)
      exact
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm
  have hcomponentExit :
      {y : Sum V E | y ∈ exitPath.support} =
        TwoColorComponent G rho0 gammaN beta (Sum.inl u) := by
    let H1 := TwoColorIncidenceGraph G rho1 gammaN deltaN
    let H0 := TwoColorIncidenceGraph G rho0 gammaN beta
    have path_edge_data : ∀ {a b : V}
        (q : H1.Walk (Sum.inl a) (Sum.inl b)) (hq : q.IsPath) {e : E},
        Sum.inr e ∈ q.support →
          ∃ j : ℕ, 0 < j ∧ j < q.length ∧ q.getVert j = Sum.inr e ∧
            ∃ v w : V, q.getVert (j - 1) = Sum.inl v ∧
              q.getVert (j + 1) = Sum.inl w ∧ v ≠ w ∧
                G.ends e = s(v, w) := by
      intro a b q hq e he
      obtain ⟨j, hj, hjle⟩ :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mp he
      have hjpos : 0 < j := by
        by_contra hn
        have hjzero : j = 0 := Nat.eq_zero_of_not_pos hn
        have : (Sum.inl a : Sum V E) = Sum.inr e := by
          simpa [hjzero] using hj
        exact Sum.inl_ne_inr this
      have hjlt : j < q.length := by
        by_contra hn
        have hjend : j = q.length := by omega
        have : (Sum.inl b : Sum V E) = Sum.inr e := by
          simpa [hjend] using hj
        exact Sum.inl_ne_inr this
      have hprev := q.adj_getVert_succ (i := j - 1) (by omega)
      rw [show j - 1 + 1 = j by omega, hj] at hprev
      have hnext := q.adj_getVert_succ (i := j) hjlt
      rw [hj] at hnext
      obtain ⟨v, hv⟩ : ∃ v : V, q.getVert (j - 1) = Sum.inl v := by
        cases hc : q.getVert (j - 1) with
        | inl v => exact ⟨v, rfl⟩
        | inr f =>
            rw [hc] at hprev
            exact False.elim (by simpa [H1, TwoColorIncidenceGraph] using hprev)
      obtain ⟨w, hw⟩ : ∃ w : V, q.getVert (j + 1) = Sum.inl w := by
        cases hc : q.getVert (j + 1) with
        | inl w => exact ⟨w, rfl⟩
        | inr f =>
            rw [hc] at hnext
            exact False.elim (by simpa [H1, TwoColorIncidenceGraph] using hnext)
      have hve : Incident G v e := by
        rw [hv] at hprev
        change Incident G v e ∧
          (rho1 e = some gammaN ∨ rho1 e = some deltaN) at hprev
        exact hprev.1
      have hwe : Incident G w e := by
        rw [hw] at hnext
        change Incident G w e ∧
          (rho1 e = some gammaN ∨ rho1 e = some deltaN) at hnext
        exact hnext.1
      have hvw : v ≠ w := by
        intro hvw
        have hindex := hq.getVert_injOn
          (show j - 1 ≤ q.length by omega)
          (show j + 1 ≤ q.length by omega)
          (by rw [hv, hw, hvw])
        omega
      have hends : G.ends e = s(v, w) := by
        induction heq : G.ends e using Sym2.inductionOn with
        | _ c d =>
            simp only [Incident, heq, Sym2.mem_iff] at hve hwe
            rcases hve with rfl | rfl <;> rcases hwe with rfl | rfl <;>
              simp_all [Sym2.eq_iff]
      exact ⟨j, hjpos, hjlt, hj, v, w, hv, hw, hvw, hends⟩
    have path_incident_vertex_mem : ∀ {a b : V}
        (q : H1.Walk (Sum.inl a) (Sum.inl b)) (hq : q.IsPath)
        {e : E}, Sum.inr e ∈ q.support → ∀ {w : V}, Incident G w e →
          Sum.inl w ∈ q.support := by
      intro a b q hq e he w hwe
      obtain ⟨j, hjpos, hjlt, hj, v, t, hv, ht, hvt, hends⟩ :=
        path_edge_data q hq he
      have hwends : w ∈ s(v, t) := by
        rw [← hends]
        exact hwe
      simp only [Sym2.mem_iff] at hwends
      apply SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
      rcases hwends with hwv | hwt
      · exact ⟨j - 1, by simpa [hwv] using hv, by omega⟩
      · exact ⟨j + 1, by simpa [hwt] using ht, by omega⟩
    have path_incident_end_last : ∀ {a b : V}
        (q : H1.Walk (Sum.inl a) (Sum.inl b)) (hq : q.IsPath)
        {e : E}, Sum.inr e ∈ q.support → Incident G b e →
          q.getVert (q.length - 1) = Sum.inr e := by
      intro a b q hq e he hbe
      obtain ⟨j, hjpos, hjlt, hj, v, w, hv, hw, hvw, hends⟩ :=
        path_edge_data q hq he
      have hbends : b ∈ s(v, w) := by
        rw [← hends]
        exact hbe
      simp only [Sym2.mem_iff] at hbends
      rcases hbends with hbv | hbw
      · have hindex := hq.getVert_injOn
            (show j - 1 ≤ q.length by omega)
            (show q.length ≤ q.length by rfl)
            (by rw [hv, q.getVert_length, hbv])
        omega
      · have hindex := hq.getVert_injOn
            (show j + 1 ≤ q.length by omega)
            (show q.length ≤ q.length by rfl)
            (by rw [hw, q.getVert_length, hbw])
        have hjlast : j = q.length - 1 := by omega
        simpa [hjlast] using hj
    have hgLast : exitPath.getVert (exitPath.length - 1) = Sum.inr g :=
      path_incident_end_last exitPath hexitPath hgExit hug
    have exit_edge_color : ∀ e : E, Sum.inr e ∈ exitPath.support →
        (rho1 e = some gammaN ∨ rho1 e = some deltaN) →
          rho0 e = some gammaN ∨ rho0 e = some beta := by
      intro e he hcolor
      rcases hcolor with hgamma | hdelta
      · left
        by_cases heIncident : TreeIncidentEdge TjPrime e
        · rw [hrho0Fixed e heIncident]
          exact hgamma
        · unfold rho0 OutsideTreeColorSwap
          rw [if_neg heIncident]
          rw [if_neg (by
            intro heb
            exact hgammaBeta (Option.some.inj (hgamma.symm.trans heb)))]
          rw [if_neg (by
            intro hed
            exact hgammaDelta (Option.some.inj (hgamma.symm.trans hed)))]
          exact hgamma
      · have hnotIncident : ¬ TreeIncidentEdge TjPrime e := by
          intro heIncident
          obtain ⟨w, hwPrime, hwe⟩ := heIncident
          have hwExit : Sum.inl w ∈ exitPath.support :=
            path_incident_vertex_mem exitPath hexitPath he hwe
          have hwu : w = u :=
            (hexitIntersection w
              (Finset.mem_union.mpr (Or.inr hwPrime))).mp hwExit
          subst w
          have heLast := path_incident_end_last exitPath hexitPath he hwe
          have heg : e = g := Sum.inr.inj (heLast.symm.trans hgLast)
          subst e
          exact hgammaDelta (Option.some.inj (hgRho1.symm.trans hdelta))
        right
        unfold rho0 OutsideTreeColorSwap
        rw [if_neg hnotIncident]
        rw [if_neg (by
          intro heb
          exact hbetaDelta (Option.some.inj (heb.symm.trans hdelta)))]
        rw [if_pos hdelta]
    have exit_adj_rho0 : ∀ i : ℕ, i < exitPath.length →
        H0.Adj (exitPath.getVert i) (exitPath.getVert (i + 1)) := by
      intro i hi
      have hadj := exitPath.adj_getVert_succ (i := i) hi
      cases hx : exitPath.getVert i with
      | inl v =>
          cases hy : exitPath.getVert (i + 1) with
          | inl w =>
              rw [hx, hy] at hadj
              exact False.elim (by simpa [H1, TwoColorIncidenceGraph] using hadj)
          | inr e =>
              rw [hx, hy] at hadj
              change Incident G v e ∧
                  (rho1 e = some gammaN ∨ rho1 e = some deltaN) at hadj
              change Incident G v e ∧
                  (rho0 e = some gammaN ∨ rho0 e = some beta)
              exact ⟨hadj.1, exit_edge_color e
                (by simpa [hy] using exitPath.getVert_mem_support (i + 1)) hadj.2⟩
      | inr e =>
          cases hy : exitPath.getVert (i + 1) with
          | inl v =>
              rw [hx, hy] at hadj
              change Incident G v e ∧
                  (rho1 e = some gammaN ∨ rho1 e = some deltaN) at hadj
              change Incident G v e ∧
                  (rho0 e = some gammaN ∨ rho0 e = some beta)
              exact ⟨hadj.1, exit_edge_color e
                (by simpa [hx] using exitPath.getVert_mem_support i) hadj.2⟩
          | inr f =>
              rw [hx, hy] at hadj
              exact False.elim (by simpa [H1, TwoColorIncidenceGraph] using hadj)
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨i, hi, hile⟩ :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hy
      have htoStart : ∀ j : ℕ, j ≤ exitPath.length →
          H0.connectedComponentMk (exitPath.getVert j) =
            H0.connectedComponentMk (exitPath.getVert 0) := by
        intro j hj
        induction j with
        | zero => rfl
        | succ j ih =>
            exact
              (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                (exit_adj_rho0 j (by omega))).symm.trans (ih (by omega))
      change H0.connectedComponentMk y = H0.connectedComponentMk (Sum.inl u)
      simpa only [hi, exitPath.getVert_length] using
        (htoStart i hile).trans (htoStart exitPath.length le_rfl).symm
    · intro y hy
      have hxPrime : x ∉ TreeSequenceVertexSet TjPrime := by
        intro hx
        exact hxOutside (Finset.mem_union.mpr (Or.inr hx))
      have new_x_adj_old : ∀ e : E, Incident G x e →
          (rho0 e = some gammaN ∨ rho0 e = some beta) →
            rho1 e = some gammaN ∨ rho1 e = some deltaN := by
        intro e hxe hcolor
        by_cases heIncident : TreeIncidentEdge TjPrime e
        · have hfixed := hrho0Fixed e heIncident
          obtain ⟨w, hwPrime, hwe⟩ := heIncident
          have hwx : w ≠ x := by
            intro hwx
            apply hxPrime
            simpa [← hwx] using hwPrime
          have hends : G.ends e = s(w, x) := by
            induction heq : G.ends e using Sym2.inductionOn with
            | _ a b =>
                simp only [Incident, heq, Sym2.mem_iff] at hwe hxe
                rcases hwe with rfl | rfl <;> rcases hxe with rfl | rfl <;>
                  simp_all [Sym2.eq_iff]
          have heBoundary : e ∈ BoundaryEdges G
              (TreeSequenceVertexSet TjPrime) := by
            unfold BoundaryEdges
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨w, hwPrime, x, hxPrime, hends⟩
          rcases hcolor with hgamma | hbetaColor
          · exact Or.inl (hfixed.symm.trans hgamma)
          · have hbetaOld : rho1 e = some beta :=
              hfixed.symm.trans hbetaColor
            exact False.elim
              ((hclosure.2 heBoundary huPrime hbetaOld) hbeta)
        · unfold rho0 OutsideTreeColorSwap at hcolor
          rw [if_neg heIncident] at hcolor
          by_cases hbetaOld : rho1 e = some beta
          · rw [if_pos hbetaOld] at hcolor
            rcases hcolor with hdeltaGamma | hdeltaBeta
            · exact False.elim
                (hgammaDelta (Option.some.inj hdeltaGamma).symm)
            · exact False.elim
                (hbetaDelta (Option.some.inj hdeltaBeta).symm)
          · by_cases hdeltaOld : rho1 e = some deltaN
            · exact Or.inr hdeltaOld
            · rw [if_neg hbetaOld, if_neg hdeltaOld] at hcolor
              rcases hcolor with hgammaOld | hbetaOld'
              · exact Or.inl hgammaOld
              · exact False.elim (hbetaOld hbetaOld')
      have first_old_adj : H1.Adj (Sum.inl x) (exitPath.getVert 1) := by
        simpa [H1] using exitPath.adj_getVert_succ
          (show 0 < exitPath.length by omega)
      have first_p_last :
          p.getVert (p.length - 1) = exitPath.getVert 1 := by
        cases hfirst : exitPath.getVert 1 with
        | inl v =>
            rw [hfirst] at first_old_adj
            exact False.elim
              (by simpa [H1, TwoColorIncidenceGraph] using first_old_adj)
        | inr e =>
            have heExit : Sum.inr e ∈ exitPath.support := by
              simpa [hfirst] using exitPath.getVert_mem_support 1
            have heP : Sum.inr e ∈ p.support := hexitSupport _ heExit
            have hxe : Incident G x e := by
              rw [hfirst] at first_old_adj
              change Incident G x e ∧
                (rho1 e = some gammaN ∨ rho1 e = some deltaN) at first_old_adj
              exact first_old_adj.1
            exact path_incident_end_last p hpath heP hxe
      have old_x_neighbor_unique : ∀ z : Sum V E,
          H1.Adj (Sum.inl x) z → z = exitPath.getVert 1 := by
        intro z hxz
        cases hz : z with
        | inl v =>
            rw [hz] at hxz
            exact False.elim (by simpa [H1, TwoColorIncidenceGraph] using hxz)
        | inr e =>
            have hxzE : H1.Adj (Sum.inl x) (Sum.inr e) := by
              simpa [hz] using hxz
            have hxe : Incident G x e := by
              change Incident G x e ∧
                (rho1 e = some gammaN ∨ rho1 e = some deltaN) at hxzE
              exact hxzE.1
            have hxComponent : H1.connectedComponentMk (Sum.inl x) =
                H1.connectedComponentMk (Sum.inl terminalSupport) := by
              change Sum.inl x ∈
                TwoColorComponent G rho1 gammaN deltaN
                  (Sum.inl terminalSupport)
              rw [← hcomponent]
              exact p.end_mem_support
            have heComponent : H1.connectedComponentMk (Sum.inr e) =
                H1.connectedComponentMk (Sum.inl terminalSupport) :=
              (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                hxzE).symm.trans hxComponent
            have heP : Sum.inr e ∈ p.support := by
              change Sum.inr e ∈ {q : Sum V E | q ∈ p.support}
              rw [hcomponent]
              exact heComponent
            have heLast := path_incident_end_last p hpath heP hxe
            exact heLast.symm.trans first_p_last
      have x_neighbor_unique : ∀ z : Sum V E,
          H0.Adj (Sum.inl x) z → z = exitPath.getVert 1 := by
        intro z hxz
        apply old_x_neighbor_unique z
        cases hz : z with
        | inl v =>
            rw [hz] at hxz
            exact False.elim (by simpa [H0, TwoColorIncidenceGraph] using hxz)
        | inr e =>
            have hxzE : H0.Adj (Sum.inl x) (Sum.inr e) := by
              simpa [hz] using hxz
            change Incident G x e ∧
              (rho0 e = some gammaN ∨ rho0 e = some beta) at hxzE
            change Incident G x e ∧
              (rho1 e = some gammaN ∨ rho1 e = some deltaN)
            exact ⟨hxzE.1, new_x_adj_old e hxzE.1 hxzE.2⟩
      have u_neighbor_unique : ∀ z : Sum V E,
          H0.Adj (Sum.inl u) z →
            z = exitPath.getVert (exitPath.length - 1) := by
        intro z huz
        cases hz : z with
        | inl v =>
            rw [hz] at huz
            exact False.elim (by simpa [H0, TwoColorIncidenceGraph] using huz)
        | inr e =>
            rw [hz] at huz
            change Incident G u e ∧
              (rho0 e = some gammaN ∨ rho0 e = some beta) at huz
            have heGamma : rho0 e = some gammaN := by
              rcases huz.2 with heGamma | heBeta
              · exact heGamma
              · have hnotPresent : beta ∉ PresentColors G rho0 u := by
                  simpa [MissingColors] using hbetaRho0
                exact False.elim (hnotPresent (by
                  simp only [PresentColors, Finset.mem_filter,
                    Finset.mem_univ, true_and]
                  exact ⟨e, huz.1, heBeta⟩))
            have heg : e = g := by
              by_contra hne
              exact (hrho0Proper hne ⟨u, huz.1, hug⟩ heGamma) hgRho0
            exact (congrArg Sum.inr heg).trans hgLast.symm
      have support_closed : ∀ w : Sum V E, w ∈ exitPath.support →
          ∀ z : Sum V E, H0.Adj w z → z ∈ exitPath.support := by
        intro w hw z hwz
        obtain ⟨n, hn, hnle⟩ :=
          SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw
        by_cases hn0 : n = 0
        · subst n
          have hwstart : w = Sum.inl x := by simpa using hn.symm
          have hz := x_neighbor_unique z (by simpa [hwstart] using hwz)
          simpa [hz] using exitPath.getVert_mem_support 1
        by_cases hnend : n = exitPath.length
        · have hwend : w = Sum.inl u := by
            rw [← hn, hexitPath.getVert_eq_end_iff hnle]
            exact hnend
          have hz := u_neighbor_unique z (by simpa [hwend] using hwz)
          simpa [hz] using
            exitPath.getVert_mem_support (exitPath.length - 1)
        have hleft : H0.Adj (exitPath.getVert n)
            (exitPath.getVert (n - 1)) := by
          rw [← show n - 1 + 1 = n by omega]
          exact (exit_adj_rho0 (n - 1) (by omega)).symm
        have hright : H0.Adj (exitPath.getVert n)
            (exitPath.getVert (n + 1)) :=
          exit_adj_rho0 n (by omega)
        by_contra hznot
        have hwz' := hwz
        rw [← hn] at hwz'
        have hneleft : exitPath.getVert (n - 1) ≠ z := by
          intro he
          apply hznot
          rw [← he]
          exact exitPath.getVert_mem_support _
        have hneright : exitPath.getVert (n + 1) ≠ z := by
          intro he
          apply hznot
          rw [← he]
          exact exitPath.getVert_mem_support _
        have hnelr : exitPath.getVert (n - 1) ≠
            exitPath.getVert (n + 1) := by
          intro he
          have hindex := hexitPath.getVert_injOn
            (show n - 1 ≤ exitPath.length by omega)
            (show n + 1 ≤ exitPath.length by omega) he
          omega
        letI : Fintype (H0.neighborSet (exitPath.getVert n)) :=
          Fintype.ofFinite _
        have hthree : 3 ≤ H0.degree (exitPath.getVert n) := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          let s : Finset (Sum V E) :=
            {z, exitPath.getVert (n - 1), exitPath.getVert (n + 1)}
          have hs : s ⊆ H0.neighborFinset (exitPath.getVert n) := by
            intro t ht
            simp only [s, Finset.mem_insert, Finset.mem_singleton] at ht
            rcases ht with rfl | rfl | rfl
            · simpa [SimpleGraph.mem_neighborFinset] using hwz'
            · simpa [SimpleGraph.mem_neighborFinset] using hleft
            · simpa [SimpleGraph.mem_neighborFinset] using hright
          have hcard : 3 ≤ s.card := by
            simp [s, hneleft, hneright, hnelr, hneleft.symm,
              hneright.symm, hnelr.symm]
          exact hcard.trans (Finset.card_le_card hs)
        have hupper : H0.degree (exitPath.getVert n) ≤ 2 := by
          simpa [H0] using TwoColorIncidenceDegreeAtMostTwo
            G rho0 gammaN beta hrho0Proper (exitPath.getVert n)
        omega
      have reach : H0.Reachable (Sum.inl u) y := by
        change H0.connectedComponentMk y =
            H0.connectedComponentMk (Sum.inl u) at hy
        exact SimpleGraph.ConnectedComponent.eq.mp hy |>.symm
      apply reach.mem_subgraphVerts
        (H := (⊤ : H0.Subgraph).induce {w | w ∈ exitPath.support})
        (fun w hw z hadj => by
          exact ⟨by simpa using hw,
            support_closed w (by simpa using hw) z hadj, hadj⟩)
        (by simpa using exitPath.getVert_mem_support exitPath.length)
  have hcomponentIntersection : ∀ w : V,
      w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime →
      (Sum.inl w ∈ TwoColorComponent G rho0 gammaN beta (Sum.inl u) ↔
        w = u) := by
    intro w hw
    rw [← hcomponentExit]
    exact hexitIntersection w hw
  have component_edge_avoids : ∀ (w : V),
      w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime →
      w ≠ u → ∀ f : E, Incident G w f →
      Sum.inr f ∉ TwoColorComponent G rho0 gammaN beta (Sum.inl u) := by
    intro w hw hwu f hwf hf
    let H := TwoColorIncidenceGraph G rho0 gammaN beta
    have hfSupport : Sum.inr f ∈ H.support := by
      apply SimpleGraph.mem_support_of_reachable
        (G := H) (u := Sum.inr f) (v := Sum.inl u)
      · simp
      · exact SimpleGraph.ConnectedComponent.eq.mp hf
    obtain ⟨y, hy⟩ := H.mem_support.mp hfSupport
    have hfColor : rho0 f = some gammaN ∨ rho0 f = some beta := by
      cases y with
      | inl y => exact hy.2
      | inr y => simpa [H, TwoColorIncidenceGraph] using hy
    have hadj : H.Adj (Sum.inl w) (Sum.inr f) := by
      simpa [H, TwoColorIncidenceGraph] using And.intro hwf hfColor
    have hwComponent :
        Sum.inl w ∈ TwoColorComponent G rho0 gammaN beta (Sum.inl u) := by
      change H.connectedComponentMk (Sum.inl w) =
        H.connectedComponentMk (Sum.inl u)
      change H.connectedComponentMk (Sum.inr f) =
        H.connectedComponentMk (Sum.inl u) at hf
      exact
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hf
    exact hwu ((hcomponentIntersection w hw).mp hwComponent)
  have hmuRho0Fixed : ∀ (w : V),
      w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime →
      w ≠ u → ∀ f : E, Incident G w f → rho3 f = rho0 f := by
    intro w hw hwu f hwf
    have hf := component_edge_avoids w hw hwu f hwf
    simp [rho3, TwoColorComponentSwap, hf]
  have hmuRho1PrimeFixed : ∀ (w : V),
      w ∈ TreeSequenceVertexSet TjPrime → w ≠ u →
      ∀ f : E, Incident G w f → rho3 f = rho1 f := by
    intro w hw hwu f hwf
    rw [hmuRho0Fixed w (Finset.mem_union.mpr (Or.inr hw)) hwu f hwf]
    exact hrho0Fixed f ⟨w, hw, hwf⟩
  have missing_eq_of_incident_eq : ∀ (w : V),
      (∀ f : E, Incident G w f → rho3 f = rho1 f) →
      MissingColors G rho3 w = MissingColors G rho1 w := by
    intro w hfixed
    apply Finset.ext
    intro c
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
      PresentColors, Finset.mem_filter]
    constructor
    · intro hnew hold
      obtain ⟨f, hwf, hfc⟩ := hold
      exact hnew ⟨f, hwf, (hfixed f hwf).trans hfc⟩
    · intro hold hnew
      obtain ⟨f, hwf, hfc⟩ := hnew
      exact hold ⟨f, hwf, (hfixed f hwf).symm.trans hfc⟩
  have before_seed : ∀ w : V,
      w ∈ TreeVerticesBefore Tj terminalSupport hterminalTj →
      w ∈ TreeSequenceVertexSet seed := by
    intro w hw
    unfold TreeVerticesBefore at hw
    obtain ⟨hwJ, i, j, hiw, hjt, hij⟩ := Finset.mem_filter.mp hw
    obtain ⟨hlen, hvertices, hedges⟩ := hseedJ
    have hjLast : j = Fin.castLE (Nat.succ_le_succ hlen)
        (Fin.last seed.length) := by
      apply Tj.vertex_injective
      rw [hjt, hvertices, hseedTerminal]
    have hiBound : i.val < seed.length + 1 := by
      have hjVal : j.val = seed.length := by
        simpa using congrArg Fin.val hjLast
      rw [hjVal] at hij
      omega
    let iSeed : Fin (seed.length + 1) := ⟨i.val, hiBound⟩
    have hiCast : Fin.castLE (Nat.succ_le_succ hlen) iSeed = i := by
      apply Fin.ext
      rfl
    simp only [TreeSequenceVertexSet, Finset.mem_image]
    refine ⟨iSeed, Finset.mem_univ _, ?_⟩
    rw [← hvertices iSeed, hiCast]
    exact hiw
  have before_prime : ∀ w : V,
      w ∈ TreeVerticesBefore Tj terminalSupport hterminalTj →
      w ∈ TreeSequenceVertexSet TjPrime := by
    intro w hw
    exact initial_subset hseedPrime (before_seed w hw)
  have hE1 : StableColoringBeforeVertex Tj terminalSupport hterminalTj
      Dprev phiJ rho3 := by
    unfold StableColoringBeforeVertex at hb1 ⊢
    have before_ne : ∀ w : V,
        w ∈ TreeVerticesBefore Tj terminalSupport hterminalTj → w ≠ u := by
      intro w hw hwu
      subst w
      exact huSeed (before_seed u hw)
    constructor
    · intro f hf hcolor
      obtain ⟨w, hw, hwf⟩ := hf
      rw [hmuRho1PrimeFixed w (before_prime w hw) (before_ne w hw) f hwf]
      exact hb1.1 f ⟨w, hw, hwf⟩ hcolor
    · intro w hw
      exact (missing_eq_of_incident_eq w
        (hmuRho1PrimeFixed w (before_prime w hw) (before_ne w hw))).trans
          (hb1.2 w hw)
  have hmissingPrime : ∀ w : V,
      w ∈ TreeSequenceVertexSet TjPrime → w ≠ u →
      MissingColors G rho3 w = MissingColors G rho1 w := by
    intro w hw hwu
    exact missing_eq_of_incident_eq w (hmuRho1PrimeFixed w hw hwu)
  have htreeEdgeFixed : ∀ a : Fin TjPrime.length,
      rho3 (TjPrime.edge a) = rho1 (TjPrime.edge a) := by
    intro a
    obtain ⟨i, hi⟩ := TjPrime.attaches a
    let earlier : Fin (TjPrime.length + 1) :=
      Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ a.isLt))
    have hlaterSet : TjPrime.vertex a.succ ∈
        TreeSequenceVertexSet TjPrime := by
      simp [TreeSequenceVertexSet]
    have hearlierSet : TjPrime.vertex earlier ∈
        TreeSequenceVertexSet TjPrime := by
      simp [TreeSequenceVertexSet]
    have hlaterInc : Incident G (TjPrime.vertex a.succ)
        (TjPrime.edge a) := by
      change TjPrime.vertex a.succ ∈ G.ends (TjPrime.edge a)
      rw [hi]
      simp
    have hearlierInc : Incident G (TjPrime.vertex earlier)
        (TjPrime.edge a) := by
      change TjPrime.vertex earlier ∈ G.ends (TjPrime.edge a)
      rw [hi]
      simp [earlier]
    have hverticesNe : TjPrime.vertex a.succ ≠ TjPrime.vertex earlier := by
      apply TjPrime.vertex_injective.ne
      intro heq
      have hval := congrArg Fin.val heq
      simp [earlier] at hval
      omega
    by_cases hlu : TjPrime.vertex a.succ = u
    · exact hmuRho1PrimeFixed (TjPrime.vertex earlier) hearlierSet
        (by intro heu; exact hverticesNe (hlu.trans heu.symm))
        (TjPrime.edge a) hearlierInc
    · exact hmuRho1PrimeFixed (TjPrime.vertex a.succ) hlaterSet hlu
        (TjPrime.edge a) hlaterInc
  have rho0_unaffected : ∀ (c : Fin k), c ≠ beta → c ≠ deltaN →
      ∀ f : E, (rho0 f = some c ↔ rho1 f = some c) := by
    intro c hcb hcd f
    unfold rho0 OutsideTreeColorSwap
    by_cases ht : TreeIncidentEdge TjPrime f
    · simp [ht]
    · simp only [if_neg ht]
      by_cases hfb : rho1 f = some beta
      · rw [if_pos hfb]
        constructor
        · intro h
          exact False.elim (hcd (Option.some.inj h).symm)
        · intro h
          exact False.elim (hcb (Option.some.inj (h.symm.trans hfb)))
      · rw [if_neg hfb]
        by_cases hfd : rho1 f = some deltaN
        · rw [if_pos hfd]
          constructor
          · intro h
            exact False.elim (hcb (Option.some.inj h).symm)
          · intro h
            exact False.elim (hcd (Option.some.inj (h.symm.trans hfd)))
        · rw [if_neg hfd]
  have hE2 := P2966_T1_OutsideSwapPrefixEffects Tn Tj seed TjPrime
    phiJ rho1 rho0 rho3 deltaN beta terminalSupport u z zPosition
    hTjN hterminalPrime hclosure.2 hprimeElementary hbetaDelta hbeta
    hdeltaMissing hb2Missing haugmentation hb2Edges hdeltaPhiJ hz
    hzPosition hzAfter huPrime huOutside hzBefore hzEdges rfl hrho0Fixed hmuRho0Fixed
    hmissingPrime htreeEdgeFixed rho0_unaffected
  have hgammaFirstRho3 : gammaFirst ∈ MissingColors G rho3 u := by
    rw [hgammaFirst]
    exact hgammaRho3
  exact ⟨hrho3Proper, hrho3One, hE1, hE2, hgammaFirstRho3⟩
