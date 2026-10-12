import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.DefectiveColor
import Tablet.DefectiveColors
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.PartialEdgeColoring
import Tablet.PresentColors
import Tablet.ScheideDefectiveChainPath
import Tablet.P2968_T1_DefectiveColorComponentPath
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideExitVertex
import Tablet.ScheideExitVertices
import Tablet.ScheideGlobalMaximumMissingCounts
import Tablet.ScheideGlobalMaximumBoundaryFacts
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideStructuralConfiguration
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideDefectiveSetupExists]
theorem ScheideDefectiveSetupExists {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (hdef : DefectiveColors G phi (TreeSequenceVertexSet T) ≠ ∅) :
    Nonempty (ScheideDefectiveSetup G k e0 phi T C) := by
-- BODY
  classical
  have hglobal : GlobalMaximumTriple G k e0 phi T := C.globally_maximum
  have pathLemma : ∀ (alpha gamma : Fin k),
      ∀ (halpha : alpha ∈ DefectiveColors G phi (TreeSequenceVertexSet T)),
      ∀ (u : V), u ∈ TreeSequenceVertexSet T →
      ∀ (hgamma : gamma ∈ MissingColors G phi u),
      ∃ (z : V) (p : (TwoColorIncidenceGraph G phi alpha gamma).Walk
        (Sum.inl u) (Sum.inl z)),
        ScheideDefectiveChainPath T phi alpha gamma u z p := by
    exact P2968_T1_DefectiveColorComponentPath G k e0 phi T hglobal

  let X := TreeSequenceVertexSet T
  let y0 : V := C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
  have hy0 : y0 ∈ X := by
    simp only [X, TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨⟨0, Nat.zero_lt_succ _⟩, ?_⟩
    change T.vertex ⟨0, Nat.zero_lt_succ _⟩ =
      C.y ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
    exact C.base_vertex_position ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
  have he0 : Incident G y0 e0 := by
    obtain ⟨q, hq⟩ := T.attaches ⟨0, T.positive⟩
    have hq0 : q = ⟨0, by omega⟩ := by
      apply Fin.ext
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ q.isLt)
    have he : T.edge ⟨0, T.positive⟩ = e0 := T.first_edge
    have hv0 := C.base_vertex_position ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
    have hv1 := C.base_vertex_position ⟨1, Nat.lt_of_lt_of_le (by decide) C.p_ge_two⟩
    change y0 ∈ G.ends e0
    rw [← he, hq, hq0]
    rw [Sym2.mem_iff]
    right
    calc
      y0 = C.y ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ := rfl
      _ = T.vertex ⟨0, Nat.zero_lt_succ _⟩ := hv0.symm
      _ = T.vertex (⟨0, by omega⟩ : Fin (T.length + 1)) := by
        rfl
  have hcounts := ScheideGlobalMaximumMissingCounts G k e0 phi T hglobal y0 hy0
  have hcard : 2 ≤ (MissingColors G phi y0).card := hcounts.1 he0 |>.2
  have hblock : ∀ i : Fin C.s, C.gamma i ∈ MissingColors G phi y0 →
      ∀ j : Fin C.s, C.gamma j ∈ MissingColors G phi y0 → i = j := by
    intro i hi j hj
    have hexitbase : ∀ v ∈ ScheideExitVertices T phi,
        v ∈ X := by
      intro v hv
      have hv' : ScheideExitVertex T phi v := by
        simpa [ScheideExitVertices] using hv
      rcases hv' with ⟨u, a, d, hu, ha, hd, z, p, hp, q, hq, hvq, hafter⟩
      exact hvq
    obtain ⟨v, hv, hvm⟩ := C.every_block_color_at_exit i
    have hvX := hexitbase v hv
    have hsame : v = y0 := by
      by_contra hne
      have hd := (ScheideGlobalMaximumOrder G k e0 phi T hglobal).2.2.2.1
        hvX hy0 hne
      exact (Finset.disjoint_left.1 hd hvm hi).elim
    have hyexit : y0 ∈ ScheideExitVertices T phi := hsame ▸ hv
    obtain ⟨q, hq, huq⟩ := C.exit_exactly_one y0 hyexit
    have hiq : i = q := huq i hi
    have hjq : j = q := huq j hj
    exact hiq.trans hjq.symm
  have hgamma_bound : (Finset.univ.filter (fun i : Fin C.s =>
      C.gamma i ∈ MissingColors G phi y0)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact hblock i (Finset.mem_filter.mp hi).2 j (Finset.mem_filter.mp hj).2
  have hchoose : ∃ a : Fin k, a ∈ MissingColors G phi y0 ∧
      ∀ i : Fin C.s, a ≠ C.gamma i := by
    by_contra hn
    push_neg at hn
    have hc : (MissingColors G phi y0).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      obtain ⟨i, hi⟩ := hn a ha
      obtain ⟨j, hj⟩ := hn b hb
      have hij : i = j := hblock i (by simpa [hi] using ha)
        j (by simpa [hj] using hb)
      simpa [hi, hj, hij]
    omega
  obtain ⟨alpha0, halpha0, hab⟩ := hchoose
  have extractPath : ∀ {a b : Fin k} {u z : V}
      {p : (TwoColorIncidenceGraph G phi a b).Walk (Sum.inl u) (Sum.inl z)},
      ScheideDefectiveChainPath T phi a b u z p →
      ∃ (v : V) (f : E) (w : V) (i j l : Fin (p.length + 1)),
        p.getVert i.val = Sum.inl v ∧
        v ∈ X ∧
        p.getVert j.val = Sum.inr f ∧
        p.getVert l.val = Sum.inl w ∧
        j.val = i.val + 1 ∧ l.val = i.val + 2 ∧
        (∀ r : Fin (p.length + 1), i.val < r.val →
          ∀ x : V, p.getVert r.val = Sum.inl x → x ∉ X) ∧
        w ∉ X := by
    intro a b u z p hp
    let indices : Finset (Fin (p.length + 1)) :=
      Finset.univ.filter (fun r => ∃ x : V, p.getVert r.val = Sum.inl x ∧ x ∈ X)
    have hindices : indices.Nonempty := by
      refine ⟨⟨0, Nat.zero_lt_succ _⟩, ?_⟩
      simp only [indices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨u, p.getVert_zero, hp.1⟩
    let i : Fin (p.length + 1) := indices.max' hindices
    have hi : i ∈ indices := Finset.max'_mem indices hindices
    obtain ⟨v, hiv, hvX⟩ := (Finset.mem_filter.mp hi).2
    have hilength : i.val < p.length := by
      by_contra hn
      have heq : i.val = p.length := by omega
      have hend : p.getVert i.val = Sum.inl z := by
        rw [heq, p.getVert_length]
      have hzv : v = z := Sum.inl.inj (hiv.symm.trans hend)
      exact hp.2.2.1 (hzv ▸ hvX)
    have hi1 : i.val + 1 < p.length + 1 := by omega
    have hside1 : ∃ f : E, p.getVert (i.val + 1) = Sum.inr f := by
      cases hnode : p.getVert (i.val + 1) with
      | inl x =>
          have hadj := p.adj_getVert_succ hilength
          rw [hiv, hnode] at hadj
          simp [TwoColorIncidenceGraph] at hadj
      | inr f => exact ⟨f, rfl⟩
    obtain ⟨f, hf⟩ := hside1
    have hnotend : i.val + 1 ≠ p.length := by
      intro he
      have hend := p.getVert_length
      rw [he] at hf
      exact Sum.inr_ne_inl (hf.symm.trans hend)
    have hi2 : i.val + 1 < p.length := by omega
    have hside2 : ∃ w : V, p.getVert (i.val + 2) = Sum.inl w := by
      cases hnode : p.getVert (i.val + 2) with
      | inr e =>
          have hadj := p.adj_getVert_succ hi2
          rw [hf, hnode] at hadj
          simp [TwoColorIncidenceGraph] at hadj
      | inl w => exact ⟨w, rfl⟩
    obtain ⟨w, hw⟩ := hside2
    have hmax : ∀ r : Fin (p.length + 1), i.val < r.val →
        ∀ x : V, p.getVert r.val = Sum.inl x → x ∉ X := by
      intro r hir x hxr hx
      have hr : r ∈ indices := by
        simp only [indices, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨x, hxr, hx⟩
      have hle := Finset.le_max' indices r hr
      have hleval : r.val ≤ i.val := Fin.le_iff_val_le_val.mp hle
      omega
    have hwX : w ∉ X := by
      intro hwX
      have hr : (⟨i.val + 2, by omega⟩ : Fin (p.length + 1)) ∈ indices := by
        simp only [indices, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨w, hw, hwX⟩
      have hle := Finset.le_max' indices _ hr
      change i.val + 2 ≤ i.val at hle
      have hleval : i.val + 2 ≤ i.val := hle
      omega
    exact ⟨v, f, w, i, ⟨i.val + 1, hi1⟩, ⟨i.val + 2, by omega⟩,
      hiv, hvX, hf, hw, by rfl, by rfl, hmax, hwX⟩
  have initialData : ∀ d : {delta // delta ∈ DefectiveColors G phi X},
      ∃ (v : V) (f : E) (u : V) (z : V)
        (p : (TwoColorIncidenceGraph G phi alpha0 d.1).Walk
          (Sum.inl y0) (Sum.inl z))
        (i j l : Fin (p.length + 1)),
        p.IsPath ∧ {x | x ∈ p.support} =
          TwoColorComponent G phi alpha0 d.1 (Sum.inl y0) ∧
        ScheideDefectiveChainPath T phi alpha0 d.1 y0 z p ∧
        p.getVert i.val = Sum.inl v ∧ p.getVert j.val = Sum.inr f ∧
        p.getVert l.val = Sum.inl u ∧ j.val = i.val + 1 ∧
        l.val = i.val + 2 ∧
        (∀ r : Fin (p.length + 1), i.val < r.val →
          ∀ w : V, p.getVert r.val = Sum.inl w → w ∉ X) ∧
        u ∉ X ∧ v ∈ ScheideExitVertices T phi := by
    intro d
    obtain ⟨z, p, hp⟩ := pathLemma d.1 alpha0 d.2 y0 hy0 halpha0
    have hp' : ScheideDefectiveChainPath T phi d.1 alpha0 y0 z p := hp
    let graphSwap : TwoColorIncidenceGraph G phi d.1 alpha0 =
        TwoColorIncidenceGraph G phi alpha0 d.1 := by
      ext x y
      simp [TwoColorIncidenceGraph, or_comm]
    let graphHom : TwoColorIncidenceGraph G phi d.1 alpha0 →g
        TwoColorIncidenceGraph G phi alpha0 d.1 :=
      ⟨id, by intro x y h; simpa [TwoColorIncidenceGraph, or_comm] using h⟩
    let pnew := p.map graphHom
    have componentSwap : TwoColorComponent G phi d.1 alpha0 (Sum.inl y0) =
        TwoColorComponent G phi alpha0 d.1 (Sum.inl y0) := by
      change ((TwoColorIncidenceGraph G phi d.1 alpha0).connectedComponentMk
          (Sum.inl y0) : Set (Sum V E)) =
        ((TwoColorIncidenceGraph G phi alpha0 d.1).connectedComponentMk
          (Sum.inl y0) : Set (Sum V E))
      ext x
      change x ∈ ((TwoColorIncidenceGraph G phi d.1 alpha0).connectedComponentMk
          (Sum.inl y0)).supp ↔
        x ∈ ((TwoColorIncidenceGraph G phi alpha0 d.1).connectedComponentMk
          (Sum.inl y0)).supp
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff,
        SimpleGraph.ConnectedComponent.mem_supp_iff,
        SimpleGraph.ConnectedComponent.eq,
        SimpleGraph.ConnectedComponent.eq]
      constructor
      · intro h
        simpa [graphHom] using h.map graphHom
      · intro h
        let reverseHom : TwoColorIncidenceGraph G phi alpha0 d.1 →g
            TwoColorIncidenceGraph G phi d.1 alpha0 :=
          ⟨id, by intro x y h; simpa [TwoColorIncidenceGraph, or_comm] using h⟩
        simpa [reverseHom] using h.map reverseHom
    have hpnew : ScheideDefectiveChainPath T phi alpha0 d.1 y0 z pnew := by
      change y0 ∈ TreeSequenceVertexSet T ∧ pnew.IsPath ∧
        z ∉ TreeSequenceVertexSet T ∧
        {x | x ∈ pnew.support} =
          TwoColorComponent G phi alpha0 d.1 (Sum.inl y0)
      refine ⟨hp.1, (pnew.isPath_def).2 ?_, hp.2.2.1, ?_⟩
      · simpa [pnew, graphHom] using (p.isPath_def.mp hp.2.1)
      · have hsupp : pnew.support = p.support := by simp [pnew, graphHom]
        rw [hsupp, ← componentSwap]
        exact hp.2.2.2
    obtain ⟨v, f, u, i, j, l, hiv, hv, hjf, hlu, hij, hil, hlast, hu⟩ :=
      extractPath hpnew
    have hexit : v ∈ ScheideExitVertices T phi := by
      simp only [ScheideExitVertices, Finset.mem_filter, Finset.mem_univ, true_and]
      have hy0' : y0 ∈ TreeSequenceVertexSet T := by
        exact hy0
      let iBack : Fin (p.length + 1) := ⟨i.val, by
        simpa [pnew] using i.isLt⟩
      refine ⟨y0, alpha0, d.1, hy0', halpha0, d.2, z, p, hp, iBack, ?_, hv, ?_⟩
      · simpa [iBack, pnew, graphHom] using hiv
      · intro r hr w hw
        let rnew : Fin (pnew.length + 1) := ⟨r.val, by
          simpa [pnew] using r.isLt⟩
        change i.val < r.val at hr
        apply hlast rnew (by simpa [rnew] using hr) w
        simpa [rnew, pnew, graphHom] using hw
    refine ⟨v, f, u, z, pnew, ?_⟩
    exact ⟨i, j, l, hpnew.2.1, hpnew.2.2.2, hpnew, hiv, hjf, hlu, hij, hil, hlast, hu, hexit⟩
  choose v0 f0 u0 z0 p0 i0 j0 l0 hinitial using initialData
  have gammaData : ∀ d : {delta // delta ∈ DefectiveColors G phi X},
      ∃ i : Fin C.s, C.gamma i ∈ MissingColors G phi (v0 d) := by
    intro d
    have he := (hinitial d).2.2.2.2.2.2.2.2.2.2
    have hvX : v0 d ∈ X := by
      simp only [ScheideExitVertices, Finset.mem_filter, Finset.mem_univ, true_and] at he
      rcases he with ⟨u, a, q, hu, ha, hq, z, p, hp, i, hi, hv, hl⟩
      exact hv
    exact (C.exit_exactly_one (v0 d) he).exists
  choose gammaIndex gamma_missing using gammaData
  have v0mem : ∀ d : {delta // delta ∈ DefectiveColors G phi X}, v0 d ∈ X := by
    intro d
    have he := (hinitial d).2.2.2.2.2.2.2.2.2.2
    simp only [ScheideExitVertices, Finset.mem_filter, Finset.mem_univ, true_and] at he
    rcases he with ⟨u, a, q, hu, ha, hq, z, p, hp, i, hi, hv, hl⟩
    exact hv
  have replacementData : ∀ d : {delta // delta ∈ DefectiveColors G phi X},
      ∃ z : V, ∃ p : (TwoColorIncidenceGraph G phi
          (C.gamma (gammaIndex d)) d.1).Walk
          (Sum.inl (v0 d)) (Sum.inl z),
        ScheideDefectiveChainPath T phi (C.gamma (gammaIndex d)) d.1
          (v0 d) z p := by
    intro d
    obtain ⟨z, p, hp⟩ := pathLemma d.1 (C.gamma (gammaIndex d)) d.2
      (v0 d) (v0mem d) (gamma_missing d)
    have graphSwap : TwoColorIncidenceGraph G phi d.1 (C.gamma (gammaIndex d)) =
        TwoColorIncidenceGraph G phi (C.gamma (gammaIndex d)) d.1 := by
      ext x y
      simp [TwoColorIncidenceGraph, or_comm]
    let graphHom : TwoColorIncidenceGraph G phi d.1 (C.gamma (gammaIndex d)) →g
        TwoColorIncidenceGraph G phi (C.gamma (gammaIndex d)) d.1 :=
      ⟨id, by intro x y h; simpa [TwoColorIncidenceGraph, or_comm] using h⟩
    let pnew := p.map graphHom
    have componentSwap : TwoColorComponent G phi d.1 (C.gamma (gammaIndex d))
        (Sum.inl (v0 d)) = TwoColorComponent G phi (C.gamma (gammaIndex d)) d.1
          (Sum.inl (v0 d)) := by
      change ((TwoColorIncidenceGraph G phi d.1 (C.gamma (gammaIndex d))).connectedComponentMk
          (Sum.inl (v0 d)) : Set (Sum V E)) =
        ((TwoColorIncidenceGraph G phi (C.gamma (gammaIndex d)) d.1).connectedComponentMk
          (Sum.inl (v0 d)) : Set (Sum V E))
      ext x
      change x ∈ ((TwoColorIncidenceGraph G phi d.1 (C.gamma (gammaIndex d))).connectedComponentMk
          (Sum.inl (v0 d))).supp ↔
        x ∈ ((TwoColorIncidenceGraph G phi (C.gamma (gammaIndex d)) d.1).connectedComponentMk
          (Sum.inl (v0 d))).supp
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff,
        SimpleGraph.ConnectedComponent.mem_supp_iff,
        SimpleGraph.ConnectedComponent.eq,
        SimpleGraph.ConnectedComponent.eq]
      constructor
      · intro h
        simpa [graphHom] using h.map graphHom
      · intro h
        let reverseHom : TwoColorIncidenceGraph G phi (C.gamma (gammaIndex d)) d.1 →g
            TwoColorIncidenceGraph G phi d.1 (C.gamma (gammaIndex d)) :=
          ⟨id, by intro x y h; simpa [TwoColorIncidenceGraph, or_comm] using h⟩
        simpa [reverseHom] using h.map reverseHom
    refine ⟨z, pnew, ?_⟩
    change v0 d ∈ TreeSequenceVertexSet T ∧ pnew.IsPath ∧
      z ∉ TreeSequenceVertexSet T ∧
      {x | x ∈ pnew.support} =
        TwoColorComponent G phi (C.gamma (gammaIndex d)) d.1 (Sum.inl (v0 d))
    refine ⟨hp.1, (pnew.isPath_def).2 ?_, hp.2.2.1, ?_⟩
    · simpa [pnew, graphHom] using (p.isPath_def.mp hp.2.1)
    · have hsupp : pnew.support = p.support := by simp [pnew, graphHom]
      rw [hsupp, ← componentSwap]
      exact hp.2.2.2
  choose replacementZ replacementPath replacement_full using replacementData
  have endpointData : ∀ d : {delta // delta ∈ DefectiveColors G phi X},
      G.ends (f0 d) = s(v0 d, u0 d) := by
    intro d
    rcases hinitial d with ⟨hp, hs, hf, hi, hj, hl, hij, hil, hm, ho, he⟩
    have hav := p0 d |>.adj_getVert_succ (by omega : (i0 d).val < (p0 d).length)
    rw [← hij, hi, hj] at hav
    have hav' : Incident G (v0 d) (f0 d) := by
      have htemp : Incident G (v0 d) (f0 d) ∧
          (phi (f0 d) = some alpha0 ∨ phi (f0 d) = some d.1) := by
        simpa [TwoColorIncidenceGraph] using hav
      exact htemp.1
    have hjl : (l0 d).val = (j0 d).val + 1 := by omega
    have haw := p0 d |>.adj_getVert_succ (by omega : (j0 d).val < (p0 d).length)
    rw [← hjl, hj, hl] at haw
    have haw' : Incident G (u0 d) (f0 d) := by
      have htemp : Incident G (u0 d) (f0 d) ∧
          (phi (f0 d) = some alpha0 ∨ phi (f0 d) = some d.1) := by
        simpa [TwoColorIncidenceGraph] using haw
      exact htemp.1
    let a := (Quot.out (G.ends (f0 d))).1
    let b := (Quot.out (G.ends (f0 d))).2
    have hab : s(a, b) = G.ends (f0 d) := Quot.out_eq _
    have hva : v0 d = a ∨ v0 d = b := by
      have hmem : v0 d ∈ s(a, b) := by
        rw [hab]
        exact hav'
      exact (Sym2.mem_iff.mp hmem)
    have hua : u0 d = a ∨ u0 d = b := by
      have hmem : u0 d ∈ s(a, b) := by
        rw [hab]
        exact haw'
      exact (Sym2.mem_iff.mp hmem)
    have hvu : v0 d ≠ u0 d := by
      intro h
      have hh := hp.getVert_injOn (show (i0 d).val ≤ (p0 d).length by omega)
        (show (l0 d).val ≤ (p0 d).length by omega)
        (hi.trans (h ▸ hl).symm)
      omega
    rw [← hab, Sym2.eq_iff]
    rcases hva with hva | hva
    · rcases hua with hua | hua
      · exact (hvu (hva.trans hua.symm)).elim
      · exact Or.inl ⟨hva.symm, hua.symm⟩
    · rcases hua with hua | hua
      · exact Or.inr ⟨hua.symm, hva.symm⟩
      · exact (hvu (hva.trans hua.symm)).elim
  refine ⟨{
    alpha0 := alpha0
    alpha0_missing_at_y0 := by simpa [y0] using halpha0
    alpha0_not_block := hab
    v0 := v0
    f0 := f0
    u0 := u0
    gammaIndex := gammaIndex
    initialZ := z0
    initialPath := p0
    initial_path_full := by
      intro d
      rcases hinitial d with ⟨hp, hs, hf, hi, hj, hl, hij, hil, hm, ho, he⟩
      exact hf
    v0Index := i0
    f0Index := j0
    u0Index := l0
    v0_at_index := by
      intro d
      exact (hinitial d).2.2.2.1
    f0_at_index := by
      intro d
      exact (hinitial d).2.2.2.2.1
    u0_at_index := by
      intro d
      exact (hinitial d).2.2.2.2.2.1
    successive_indices := by
      intro d
      exact ⟨(hinitial d).2.2.2.2.2.2.1, (hinitial d).2.2.2.2.2.2.2.1⟩
    v0_is_last_tree_vertex := by
      intro d
      exact (hinitial d).2.2.2.2.2.2.2.2.1
    v0_is_exit := by
      intro d
      exact (hinitial d).2.2.2.2.2.2.2.2.2.2
    gamma_missing_at_v0 := gamma_missing
    f0_color := by
      intro d
      rcases hinitial d with ⟨hp, hs, hf, hi, hj, hl, hij, hil, hm, ho, he⟩
      have hadj := p0 d |>.adj_getVert_succ (by omega : (i0 d).val < (p0 d).length)
      rw [← hij, hi, hj] at hadj
      have hcol : phi (f0 d) = some alpha0 ∨ phi (f0 d) = some d.1 := by
        have htemp : Incident G (v0 d) (f0 d) ∧
            (phi (f0 d) = some alpha0 ∨ phi (f0 d) = some d.1) := by
          simpa [TwoColorIncidenceGraph] using hadj
        exact htemp.2
      rcases hcol with hcol | hcol
      · have hboundary : f0 d ∈ BoundaryEdges G X := by
          simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨v0 d, v0mem d, u0 d, ho, endpointData d⟩
        have halphaTree : alpha0 ∈ TreeMissingColors phi T := by
          simp only [TreeMissingColors, Finset.mem_biUnion]
          exact ⟨y0, hy0, halpha0⟩
        have hempty := (ScheideGlobalMaximumBoundaryFacts G k e0 phi T hglobal).2.1
          alpha0 halphaTree
        have hbad : f0 d ∈ BoundaryColorEdges G phi X alpha0 := by
          simp only [BoundaryColorEdges, Finset.mem_filter, hboundary, true_and]
          exact hcol
        rw [hempty] at hbad
        simpa using hbad
      · exact hcol
    f0_ends := by
      intro d
      rcases hinitial d with ⟨hp, hs, hf, hi, hj, hl, hij, hil, hm, ho, he⟩
      have hav := p0 d |>.adj_getVert_succ (by omega : (i0 d).val < (p0 d).length)
      rw [← hij, hi, hj] at hav
      have hav' : Incident G (v0 d) (f0 d) := by
        have htemp : Incident G (v0 d) (f0 d) ∧
            (phi (f0 d) = some alpha0 ∨ phi (f0 d) = some d.1) := by
          simpa [TwoColorIncidenceGraph] using hav
        exact htemp.1
      have haw := p0 d |>.adj_getVert_succ (by omega : (j0 d).val < (p0 d).length)
      have hjl : (l0 d).val = (j0 d).val + 1 := by omega
      rw [← hjl, hj, hl] at haw
      have haw' : Incident G (u0 d) (f0 d) := by
        have htemp : Incident G (u0 d) (f0 d) ∧
            (phi (f0 d) = some alpha0 ∨ phi (f0 d) = some d.1) := by
          simpa [TwoColorIncidenceGraph] using haw
        exact htemp.1
      let a := (Quot.out (G.ends (f0 d))).1
      let b := (Quot.out (G.ends (f0 d))).2
      have hab : s(a, b) = G.ends (f0 d) := Quot.out_eq _
      have hva : v0 d = a ∨ v0 d = b := by
        have hmem : v0 d ∈ s(a, b) := by
          rw [hab]
          exact hav'
        exact (Sym2.mem_iff.mp hmem)
      have hua : u0 d = a ∨ u0 d = b := by
        have hmem : u0 d ∈ s(a, b) := by
          rw [hab]
          exact haw'
        exact (Sym2.mem_iff.mp hmem)
      have hvu : v0 d ≠ u0 d := by
        intro h
        have hh := hp.getVert_injOn (show (i0 d).val ≤ (p0 d).length by omega)
          (show (l0 d).val ≤ (p0 d).length by omega)
          (hi.trans (h ▸ hl).symm)
        omega
      rw [← hab, Sym2.eq_iff]
      rcases hva with hva | hva
      · rcases hua with hua | hua
        · exact (hvu (hva.trans hua.symm)).elim
        · exact Or.inl ⟨hva.symm, hua.symm⟩
      · rcases hua with hua | hua
        · exact Or.inr ⟨hua.symm, hva.symm⟩
        · exact (hvu (hva.trans hua.symm)).elim
    u0_outside := by
      intro d
      exact (hinitial d).2.2.2.2.2.2.2.2.2.1
    v0_on_initial_component := by
      intro d
      rcases hinitial d with ⟨hp, hs, hf, hi, hj, hl, hij, hil, hm, ho, he⟩
      rw [← hs]
      have hmem := p0 d |>.getVert_mem_support (i0 d).val
      simpa [hi] using hmem
    f0_on_initial_component := by
      intro d
      rcases hinitial d with ⟨hp, hs, hf, hi, hj, hl, hij, hil, hm, ho, he⟩
      rw [← hs]
      have hmem := p0 d |>.getVert_mem_support (j0 d).val
      simpa [hj] using hmem
    replacementZ := replacementZ
    replacementPath := replacementPath
    replacement_path_full := replacement_full
  }⟩
