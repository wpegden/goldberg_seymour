import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.DefectiveColors
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideDefectiveSwitchEffect
import Tablet.ScheideEnlargedBoundarySelection
import Tablet.ScheideEnlargedVertexSet
import Tablet.ScheideExitVertex
import Tablet.ScheideExitVertices
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideReplacementData
import Tablet.ScheideReplacementMaximum
import Tablet.ScheideStructuralConfiguration
import Tablet.ScheideStructuralExitsInBase
import Tablet.ScheideSymmetricDefectiveInternal
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceGraph

open scoped Sym2

-- [TABLET NODE: ScheideEnlargedSwitchTransport]
theorem ScheideEnlargedSwitchTransport {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d)
    (hnot : ¬ ColoredVertexSetStronglyClosed G phi
      (ScheideEnlargedVertexSet R)) :
    ∃ (alpha : Fin k)
      (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
      (f : E) (w u : V),
      let phiD := TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) d.1 (Sum.inl (D.v0 d))
      let Q := TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u)
      let psi := TwoColorComponentSwap G phiD D.alpha0 alpha (Sum.inl u)
      alpha ≠ D.alpha0 ∧
        G.ends f = s(w, u) ∧
        phiD f = some alpha ∧
        Sum.inr f ∈ Q ∧
        (∀ v ∈ TreeSequenceVertexSet T, Sum.inl v ∉ Q) ∧
        GlobalMaximumTriple G k e0 psi (R d).replacementTree ∧
        D.alpha0 ∈ MissingColors G phiD
          (C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩) ∧
        C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ ∈
          TreeSequenceVertexSet (R d).replacementTree ∧
        w ∈ TreeSequenceVertexSet (R d).replacementTree ∧
        u ∉ TreeSequenceVertexSet (R d).replacementTree ∧
        f ∉ Finset.univ.image (R d).replacementTree.edge := by
-- BODY
  classical
  obtain ⟨alpha, d, f, w, u, hα, hfα, hfends, hwX, hwT, huX,
    hwpair, hfComp, havoid⟩ :=
    ScheideEnlargedBoundarySelection G k e0 phi T C D R hnot
  let VT := TreeSequenceVertexSet T
  let X := ScheideEnlargedVertexSet R
  let y0 : V := C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
  let gamma := C.gamma (D.gammaIndex d)
  let phiD := TwoColorComponentSwap G phi gamma d.1 (Sum.inl (D.v0 d))
  let K := TwoColorComponent G phi D.alpha0 alpha (Sum.inl u)
  have hclosed : ColoredVertexSetClosed G phi X :=
    ScheideEnlargedClosed G k e0 phi T C D R
  have hproper : IsProperEdgeColoring G phi :=
    C.globally_maximum.1.2.2.2.1
  have hy0T : y0 ∈ VT := by
    have hp : (0 : ℕ) < T.length + 1 := by omega
    have hv := C.base_vertex_position
      ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
    simpa [y0, VT, TreeSequenceVertexSet] using
      (show ∃ i : Fin (T.length + 1), T.vertex i = y0 from
        ⟨⟨0, hp⟩, by simpa [y0] using hv⟩)
  have hy0X : y0 ∈ X := by
    unfold X ScheideEnlargedVertexSet
    exact Finset.mem_union_left _ hy0T
  have hfBoundary : f ∈ BoundaryEdges G X := by
    unfold BoundaryEdges
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hwX, u, huX, hfends⟩
  have hα0δ : D.alpha0 ≠ d.1 := by
    intro he
    have htclosed : ColoredVertexSetClosed G phi VT :=
      (ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum).2.2.2.2
    have hdcard : 2 ≤ (BoundaryColorEdges G phi VT d.1).card := by
      have hd : DefectiveColor G phi VT d.1 := by
        simpa [DefectiveColors] using d.property
      exact hd
    obtain ⟨q, hq⟩ := Finset.card_pos.mp
      (lt_of_lt_of_le Nat.zero_lt_two hdcard)
    have hq' : q ∈ BoundaryEdges G VT := (Finset.mem_filter.mp hq).1
    have hqc : phi q = some d.1 := (Finset.mem_filter.mp hq).2
    have hδmiss : d.1 ∉ MissingColors G phi y0 := by
      intro hm
      exact (htclosed hq' hy0T hqc) hm
    exact hδmiss (he ▸ D.alpha0_missing_at_y0)
  have hαδ : alpha ≠ d.1 := by
    intro he
    have hu1X : (R d).u1 ∈ X := by
      unfold X ScheideEnlargedVertexSet
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨d, Finset.mem_univ _, by simp⟩
    have hu2X : (R d).u2 ∈ X := by
      unfold X ScheideEnlargedVertexSet
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨d, Finset.mem_univ _, by simp⟩
    rcases hwpair with hw1 | hw2
    · have hne : f ≠ (R d).f1 := by
        intro heq
        have hv1X : (R d).v1 ∈ X := by
          unfold X ScheideEnlargedVertexSet
          apply Finset.mem_union_left
          exact (Finset.mem_sdiff.mp (R d).v1_in_remainder).1
        have hu : u = (R d).u1 := by
          rw [heq, (R d).f1_ends] at hfends
          rcases (by simpa [hw1] using hfends) with h | h
          · exact h.2.symm
          · exfalso
            exact huX (h.symm ▸ hv1X)
        exact huX (hu ▸ hu1X)
      apply (hproper hne)
      · refine ⟨w, ?_, ?_⟩
        · unfold Incident
          rw [hfends]
          simp
        · unfold Incident
          rw [(R d).f1_ends, ← hw1]
          simp
      · exact hfα
      · rw [he]
        exact (R d).f1_color
    · have hne : f ≠ (R d).f2 := by
        intro heq
        have hv2X : (R d).v2 ∈ X := by
          unfold X ScheideEnlargedVertexSet
          apply Finset.mem_union_left
          exact (Finset.mem_sdiff.mp (R d).v2_in_remainder).1
        have hu : u = (R d).u2 := by
          rw [heq, (R d).f2_ends] at hfends
          rcases (by simpa [hw2] using hfends) with h | h
          · exact h.2.symm
          · exfalso
            exact huX (h.symm ▸ hv2X)
        exact huX (hu ▸ hu2X)
      apply (hproper hne)
      · refine ⟨w, ?_, ?_⟩
        · unfold Incident
          rw [hfends]
          simp
        · unfold Incident
          rw [(R d).f2_ends, ← hw2]
          simp
      · exact hfα
      · rw [he]
        exact (R d).f2_color
  have hαgamma : alpha ≠ gamma := by
    intro he
    obtain ⟨g, hgc, hge⟩ :=
      (ScheideSymmetricDefectiveInternal G k e0 phi T C D d (R d)).2
    have hu1X : (R d).u1 ∈ X := by
      unfold X ScheideEnlargedVertexSet
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨d, Finset.mem_univ _, by simp⟩
    have hu2X : (R d).u2 ∈ X := by
      unfold X ScheideEnlargedVertexSet
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨d, Finset.mem_univ _, by simp⟩
    rcases hwpair with hw1 | hw2
    · have hne : f ≠ g := by
        intro hfg
        have hu : u = (R d).u1 := by
          rw [hfg, hge] at hfends
          rcases (by simpa [hw1] using hfends) with h | h
          · exfalso
            exact huX (h.symm ▸ hu2X)
          · exact h.1.symm
        exact huX (hu ▸ hu1X)
      apply (hproper hne)
      · refine ⟨w, ?_, ?_⟩
        · unfold Incident; rw [hfends]; simp
        · unfold Incident; rw [hge, ← hw1]; simp
      · exact hfα
      · rw [he]; exact hgc
    · have hne : f ≠ g := by
        intro hfg
        have hu : u = (R d).u2 := by
          rw [hfg, hge] at hfends
          rcases (by simpa [hw2] using hfends) with h | h
          · exact h.2.symm
          · exfalso
            exact huX (h.symm ▸ hu1X)
        exact huX (hu ▸ hu2X)
      apply (hproper hne)
      · refine ⟨w, ?_, ?_⟩
        · unfold Incident; rw [hfends]; simp
        · unfold Incident; rw [hge, ← hw2]; simp
      · exact hfα
      · rw [he]; exact hgc
  have h0gamma : D.alpha0 ≠ gamma := D.alpha0_not_block _
  have heffect := ScheideDefectiveSwitchEffect G k e0 phi T C D d
  dsimp [phiD, gamma] at heffect
  have hfirst : ∀ (e : E) (c : Fin k), c ≠ gamma → c ≠ d.1 →
      (phiD e = some c ↔ phi e = some c) := by
    intro e c hc hd
    by_cases he : Sum.inr e ∈ TwoColorComponent G phi gamma d.1
        (Sum.inl (D.v0 d))
    · by_cases hcg : phi e = some gamma
      · have hv : phiD e = some d.1 := by
          simp [phiD, TwoColorComponentSwap, he, hcg]
        rw [hv, hcg]
        simp [hc.symm, hd.symm]
      · by_cases hcd : phi e = some d.1
        · have hv : phiD e = some gamma := by
            simp [phiD, TwoColorComponentSwap, he, hcg, hcd]
          rw [hv, hcd]
          simp [hc.symm, hd.symm]
        · simp [phiD, TwoColorComponentSwap, he, hcg, hcd]
    · simp [phiD, TwoColorComponentSwap, he]
  have hfixed : ∀ e : E,
      (phiD e = some D.alpha0 ↔ phi e = some D.alpha0) ∧
      (phiD e = some alpha ↔ phi e = some alpha) := by
    intro e
    exact ⟨hfirst e D.alpha0 h0gamma hα0δ,
      hfirst e alpha hαgamma hαδ⟩
  have hgraph : TwoColorIncidenceGraph G phiD D.alpha0 alpha =
      TwoColorIncidenceGraph G phi D.alpha0 alpha := by
    ext z z'
    cases z with
    | inl v => cases z' with
      | inl w => simp [TwoColorIncidenceGraph]
      | inr e => simp only [TwoColorIncidenceGraph]; rw [(hfixed e).1, (hfixed e).2]
    | inr e => cases z' with
      | inl v => simp only [TwoColorIncidenceGraph]; rw [(hfixed e).1, (hfixed e).2]
      | inr g => simp [TwoColorIncidenceGraph]
  have hcomponent : TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) = K := by
    change ((TwoColorIncidenceGraph G phiD D.alpha0 alpha).connectedComponentMk
      (Sum.inl u)).supp = ((TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
      (Sum.inl u)).supp
    rw [hgraph]
  have hQavoid : ∀ v ∈ VT, Sum.inl v ∉
      TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) := by
    intro v hv
    rw [hcomponent]
    exact havoid v hv
  have hfD : phiD f = some alpha := (hfixed f).2.mpr hfα
  have hmax := ScheideReplacementMaximum G k e0 phi T C D d (R d)
  dsimp [phiD, gamma] at hmax
  have hcomponentColor : ∀ e : E, Sum.inr e ∈ K →
      ∃ c : Fin k, phi e = some c ∧ (c = D.alpha0 ∨ c = alpha) := by
    intro e he
    change (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
        (Sum.inr e) =
      (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
        (Sum.inl u) at he
    have heq := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp he
    have hp : (TwoColorIncidenceGraph G phi D.alpha0 alpha).Reachable
        (Sum.inr e) (Sum.inl u) := SimpleGraph.ConnectedComponent.exact heq
    have hsupp := SimpleGraph.mem_support_of_reachable (by simp) hp
    obtain ⟨z, hz⟩ := ((TwoColorIncidenceGraph G phi D.alpha0 alpha).mem_support).mp hsupp
    cases z with
    | inl v =>
      rcases hz.2 with h | h
      · exact ⟨D.alpha0, h, Or.inl rfl⟩
      · exact ⟨alpha, h, Or.inr rfl⟩
    | inr g => simp [TwoColorIncidenceGraph] at hz
  have hrepEdgeAvoid : ∀ r : Fin (R d).replacementTree.length,
      Sum.inr ((R d).replacementTree.edge r) ∉ K := by
    intro r hr
    have hm : (R d).replacementTree.edge r ∈
        Finset.univ.image (R d).replacementTree.edge := by simp
    rw [(R d).replacement_edges] at hm
    rcases Finset.mem_union.mp hm with hold | hnew
    · have hold' := (Finset.mem_erase.mp (Finset.mem_erase.mp hold).2).2
      obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hold'
      obtain ⟨i, hi⟩ := T.attaches q
      have hv : T.vertex q.succ ∈ VT := by simp [VT, TreeSequenceVertexSet]
      have he : Incident G (T.vertex q.succ) ((R d).replacementTree.edge r) := by
        unfold Incident
        rw [← hq, hi]
        simp
      obtain ⟨c, hce, hc⟩ := hcomponentColor _ (by simpa [K] using hr)
      have hadj : (TwoColorIncidenceGraph G phi D.alpha0 alpha).Adj
          (Sum.inr ((R d).replacementTree.edge r)) (Sum.inl (T.vertex q.succ)) := by
        simp [TwoColorIncidenceGraph, he, hce, hc]
      have hc := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
      have heq : (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
          (Sum.inr ((R d).replacementTree.edge r)) =
          (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
          (Sum.inl u) := by
            change (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
              (Sum.inr ((R d).replacementTree.edge r)) = _ at hr
            exact hr
      exact havoid _ hv (hc.symm.trans heq)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hnew
      rcases hnew with hnew | hnew
      · have hv : (R d).v1 ∈ VT :=
          (Finset.mem_sdiff.mp (R d).v1_in_remainder).1
        have he : Incident G (R d).v1 ((R d).replacementTree.edge r) := by
          unfold Incident
          rw [hnew, (R d).f1_ends]
          simp
        obtain ⟨c, hce, hc⟩ := hcomponentColor _ (by simpa [K] using hr)
        have hadj : (TwoColorIncidenceGraph G phi D.alpha0 alpha).Adj
            (Sum.inr ((R d).replacementTree.edge r)) (Sum.inl (R d).v1) := by
          simp [TwoColorIncidenceGraph, he, hce, hc]
        have hc := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
        have heq : (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
            (Sum.inr ((R d).replacementTree.edge r)) =
            (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
            (Sum.inl u) := by
              change (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
                (Sum.inr ((R d).replacementTree.edge r)) = _ at hr
              exact hr
        exact havoid _ hv (hc.symm.trans heq)
      · have hv : (R d).v2 ∈ VT :=
          (Finset.mem_sdiff.mp (R d).v2_in_remainder).1
        have he : Incident G (R d).v2 ((R d).replacementTree.edge r) := by
          unfold Incident
          rw [hnew, (R d).f2_ends]
          simp
        obtain ⟨c, hce, hc⟩ := hcomponentColor _ (by simpa [K] using hr)
        have hadj : (TwoColorIncidenceGraph G phi D.alpha0 alpha).Adj
            (Sum.inr ((R d).replacementTree.edge r)) (Sum.inl (R d).v2) := by
          simp [TwoColorIncidenceGraph, he, hce, hc]
        have hc := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
        have heq : (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
            (Sum.inr ((R d).replacementTree.edge r)) =
            (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
            (Sum.inl u) := by
              change (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
                (Sum.inr ((R d).replacementTree.edge r)) = _ at hr
              exact hr
        exact havoid _ hv (hc.symm.trans heq)
  have hrepEdgeAvoidD : ∀ r : Fin (R d).replacementTree.length,
      Sum.inr ((R d).replacementTree.edge r) ∉
        TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) := by
    intro r hr
    apply hrepEdgeAvoid r
    rw [← hcomponent]
    exact hr
  let psi := TwoColorComponentSwap G phiD D.alpha0 alpha (Sum.inl u)
  have hmissFixed : ∀ v ∈ VT, MissingColors G psi v = MissingColors G phiD v := by
    intro v hv
    have hefix : ∀ e, Incident G v e → psi e = phiD e := by
      intro e he
      have hn : Sum.inr e ∉ TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u) := by
        intro heQ
        rw [hcomponent] at heQ
        have hadj : (TwoColorIncidenceGraph G phi D.alpha0 alpha).Adj
            (Sum.inr e) (Sum.inl v) := by
          obtain ⟨c, hce, hc⟩ := hcomponentColor e (by simpa [K] using heQ)
          simp [TwoColorIncidenceGraph, he, hce, hc]
        have hc := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
        have heq : (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
            (Sum.inr e) =
            (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
            (Sum.inl u) := by
              change (TwoColorIncidenceGraph G phi D.alpha0 alpha).connectedComponentMk
                (Sum.inr e) = _ at heQ
              exact heQ
        exact havoid v hv (hc.symm.trans heq)
      simp [psi, TwoColorComponentSwap, hn]
    apply Finset.ext
    intro c
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · intro hc hpresent
      rcases (by simpa [PresentColors] using hpresent) with ⟨e, he, hec⟩
      apply hc
      unfold PresentColors
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e, he, (hefix e he).trans hec⟩
    · intro hc hpresent
      rcases (by simpa [PresentColors] using hpresent) with ⟨e, he, hec⟩
      apply hc
      unfold PresentColors
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e, he, (hefix e he).symm.trans hec⟩
  have htreePsi : TashkinovTree G e0 psi (R d).replacementTree := by
    intro r hr
    obtain ⟨i, c, hc, hm⟩ := hmax.2.2.2.1 r hr
    have he : psi ((R d).replacementTree.edge r) =
        phiD ((R d).replacementTree.edge r) := by
      simp [psi, TwoColorComponentSwap, hrepEdgeAvoidD r]
    refine ⟨i, c, he.trans hc, ?_⟩
    have hiv : (R d).replacementTree.vertex
        (Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ r.isLt))) ∈ VT := by
      have hvset : (R d).replacementTree.vertex
          (Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ r.isLt))) ∈
          TreeSequenceVertexSet (R d).replacementTree := by
        simp [TreeSequenceVertexSet]
      rw [(R d).replacement_vertices] at hvset
      rcases Finset.mem_union.mp hvset with hold | hpairs
      · exact (Finset.mem_sdiff.mp hold).1
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hpairs
        rcases hpairs with hi1 | hi2
        · have hlast := (R d).replacement_last_vertices.1
          have hidx : i.val = (R d).replacementTree.length - 1 := by
            have hlast' : (R d).replacementTree.vertex
                ⟨(R d).replacementTree.length - 1, by omega⟩ = (R d).u1 := by
              simpa [(R d).replacement_length] using hlast
            have hiEq : (Fin.castLT i (Nat.lt_trans i.isLt
                (Nat.succ_lt_succ r.isLt))) =
                ⟨(R d).replacementTree.length - 1, by omega⟩ := by
              apply (R d).replacementTree.vertex_injective
              exact hi1.trans hlast'.symm
            exact congrArg Fin.val hiEq
          have hrlast : r.val = (R d).replacementTree.length - 1 := by omega
          have hredge := (R d).replacement_last_edges.2
          have her : (R d).replacementTree.edge r = (R d).f2 := by
            have hri : r = ⟨(R d).replacementTree.length - 1, by omega⟩ := by
              apply Fin.ext
              exact hrlast
            rw [hri]
            simpa [(R d).replacement_length] using hredge
          have hf2 : phiD ((R d).f2) = some d.1 := by
            have hh := heffect.2.2.2.2.1 (R d).f2
              ⟨(R d).v2, (Finset.mem_sdiff.mp (R d).v2_in_remainder).1,
                by unfold Incident; rw [(R d).f2_ends]; simp⟩ (R d).f0_ne_f2.symm
            have hh' : phiD (R d).f2 = phi ((R d).f2) := by
              simpa [phiD, gamma] using hh
            rw [hh', (R d).f2_color]
          have hcf : c = d.1 := by
            rw [her] at hc
            exact Option.some.inj (hc.symm.trans hf2)
          have hf1 : phiD ((R d).f1) = some d.1 := by
            have hh := heffect.2.2.2.2.1 (R d).f1
              ⟨(R d).v1, (Finset.mem_sdiff.mp (R d).v1_in_remainder).1,
                by unfold Incident; rw [(R d).f1_ends]; simp⟩ (R d).f0_ne_f1.symm
            have hh' : phiD (R d).f1 = phi ((R d).f1) := by
              simpa [phiD, gamma] using hh
            rw [hh', (R d).f1_color]
          exfalso
          have hpresent : d.1 ∈ PresentColors G phiD (R d).u1 := by
            unfold PresentColors
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨(R d).f1, by unfold Incident; rw [(R d).f1_ends]; simp, hf1⟩
          have hnotmiss : d.1 ∉ MissingColors G phiD (R d).u1 := by
            simpa [MissingColors] using hpresent
          have hm' : c ∈ MissingColors G phiD (R d).u1 := by
            simpa [hi1] using hm
          exact hnotmiss (hcf ▸ hm')
        · have hlast := (R d).replacement_last_vertices.2
          have hlast' : (R d).replacementTree.vertex
              ⟨(R d).replacementTree.length, by omega⟩ = (R d).u2 := by
            simpa [(R d).replacement_length] using hlast
          have hidx : i.val = (R d).replacementTree.length := by
            have hiEq : (Fin.castLT i (Nat.lt_trans i.isLt
                (Nat.succ_lt_succ r.isLt))) =
                ⟨(R d).replacementTree.length, by omega⟩ := by
              apply (R d).replacementTree.vertex_injective
              exact hi2.trans hlast'.symm
            exact congrArg Fin.val hiEq
          omega
    rw [hmissFixed _ hiv]
    exact hm
  have hproperPsi : IsProperEdgeColoring G psi :=
    TwoColorComponentSwapProper G phiD D.alpha0 alpha hα.symm hmax.1
      (Sum.inl u)
  have honePsi : IsOneEdgeUncolored psi e0 := by
    constructor
    · have he := hmax.2.1.1
      change phiD e0 = none at he
      simp [psi, TwoColorComponentSwap, he]
    · intro e he
      obtain ⟨c, hc⟩ := hmax.2.1.2 e he
      change phiD e = some c at hc
      by_cases heQ : Sum.inr e ∈
          TwoColorComponent G phiD D.alpha0 alpha (Sum.inl u)
      · by_cases hc0 : c = D.alpha0
        · refine ⟨alpha, ?_⟩
          simp [psi, TwoColorComponentSwap, heQ, hc, hc0, hα]
        · by_cases hca : c = alpha
          · refine ⟨D.alpha0, ?_⟩
            simp [psi, TwoColorComponentSwap, heQ, hc, hca]
          · refine ⟨c, ?_⟩
            simp [psi, TwoColorComponentSwap, heQ, hc, hc0, hca]
      · exact ⟨c, by simp [psi, TwoColorComponentSwap, heQ, hc]⟩
  have hglobal : GlobalMaximumTriple G k e0 psi (R d).replacementTree := by
    refine ⟨?_, htreePsi, hmax.2.2.2.2⟩
    exact ⟨hmax.2.2.1.1, hmax.2.2.1.2.1, hmax.2.2.1.2.2.1,
      hproperPsi, honePsi⟩
  have hy0Rep : y0 ∈ TreeSequenceVertexSet (R d).replacementTree := by
    have hp0 : (0 : ℕ) ≤ C.p - 1 + 2 * (D.gammaIndex d).val := by omega
    have ho : (0 : ℕ) < T.length + 1 := by omega
    have hn : (0 : ℕ) < (R d).replacementTree.length + 1 := by
      rw [(R d).replacement_length]
      omega
    have hv := (R d).retained_vertices_before 0 hp0 ho
    have hbase := C.base_vertex_position
      ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
    have heq : (R d).replacementTree.vertex ⟨0, hn⟩ = y0 := by
      simpa [y0] using hv.trans hbase
    simpa [TreeSequenceVertexSet] using
      (show ∃ i : Fin ((R d).replacementTree.length + 1),
          (R d).replacementTree.vertex i = y0 from ⟨⟨0, hn⟩, heq⟩)
  have hy0D : D.alpha0 ∈ MissingColors G phiD y0 := by
    by_cases hy : y0 = D.v0 d
    · rw [hy]
      change D.alpha0 ∈ MissingColors G
        (TwoColorComponentSwap G phi gamma d.1 (Sum.inl (D.v0 d))) (D.v0 d)
      rw [heffect.2.2.2.1]
      apply Finset.mem_insert_of_mem
      exact Finset.mem_erase.mpr ⟨h0gamma, hy ▸ D.alpha0_missing_at_y0⟩
    · rw [heffect.2.2.2.2.2.1 y0 hy0T hy]
      exact D.alpha0_missing_at_y0
  have hsub : TreeSequenceVertexSet (R d).replacementTree ⊆ X := by
    intro z hz
    rw [(R d).replacement_vertices] at hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact (by
        unfold X ScheideEnlargedVertexSet
        exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hz).1)
    · unfold X ScheideEnlargedVertexSet
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨d, Finset.mem_univ _, hz⟩
  have huRep : u ∉ TreeSequenceVertexSet (R d).replacementTree := by
    intro hu
    exact huX (hsub hu)
  have hwRep : w ∈ TreeSequenceVertexSet (R d).replacementTree := by
    rw [(R d).replacement_vertices]
    apply Finset.mem_union_right
    rcases hwpair with h | h
    · simp [h]
    · simp [h]
  have hfFresh : f ∉ Finset.univ.image (R d).replacementTree.edge := by
    intro hf
    obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hf
    have hfK : Sum.inr f ∈ K := by simpa [K, TwoColorComponent] using hfComp
    apply hrepEdgeAvoid r
    simpa [hr] using hfK
  refine ⟨alpha, d, f, w, u, hα, hfends, hfD, ?_, ?_, hglobal, hy0D,
    hy0Rep, hwRep, huRep, hfFresh⟩
  · rw [hcomponent]
    exact hfComp
  · exact hQavoid
