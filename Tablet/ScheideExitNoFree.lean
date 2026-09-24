import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.DefectiveColors
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.MissingColorIncidenceEndpoint
import Tablet.OutsideTreeColorSwap
import Tablet.OutsideTreeColorSwapStable
import Tablet.PresentColors
import Tablet.ScheideDefectiveChainBoundaryEdges
import Tablet.ScheideDefectiveChainDepartureReturn
import Tablet.ScheideDefectiveChainLastReturnNoFree
import Tablet.ScheideDefectiveChainPath
import Tablet.ScheideDefectiveChainPathExists
import Tablet.ScheideDepartureReturn
import Tablet.ScheideExitVertex
import Tablet.ScheideExitVertexTreeExit
import Tablet.ScheideExitVertices
import Tablet.ScheideGlobalMaximumBoundaryFacts
import Tablet.ScheideGlobalMaximumOrder
import Tablet.TashkinovTree
import Tablet.TreeFreeColors
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TreeUsedColors
import Tablet.TwoColorComponent
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideExitNoFree]
theorem ScheideExitNoFree {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T) :
    ∀ v ∈ ScheideExitVertices T phi,
      Disjoint (MissingColors G phi v) (TreeFreeColors phi T) := by
-- BODY
  classical
  intro v hvExit
  rw [Finset.disjoint_left]
  intro alpha hAlphaMissing hAlphaFree
  have hExit : ScheideExitVertex T phi v := by
    simpa [ScheideExitVertices] using hvExit
  rcases hExit with
    ⟨u, gamma, delta, hu, hGammaMissing, hDelta, z, p, hp,
      i, hiVertex, hvT, hAfter⟩
  let X := TreeSequenceVertexSet T
  have horder := ScheideGlobalMaximumOrder G k e0 phi T hglobal
  have hproper : IsProperEdgeColoring G phi := hglobal.1.2.2.2.1
  have hone : IsOneEdgeUncolored phi e0 := hglobal.1.2.2.2.2
  have htree : TashkinovTree G e0 phi T := hglobal.2.1
  have helem : ColoredVertexSetElementary G phi X := by
    exact horder.2.2.2.1
  have hclosed : ColoredVertexSetClosed G phi X := by
    exact horder.2.2.2.2
  by_cases hAlphaGamma : alpha = gamma
  · subst gamma
    have huv : u = v := by
      by_contra hne
      have hd := Finset.disjoint_left.mp
        (helem (by simpa [X] using hu) (by simpa [X] using hvT) hne)
      exact hd hGammaMissing hAlphaMissing
    rcases ScheideDefectiveChainDepartureReturn G k e0 phi T hglobal
        delta alpha hDelta hAlphaFree u hu hGammaMissing z p hp with
      ⟨i1, i2, v1, v2, hdepart⟩
    have hiEq : i.val = i2.val := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hv2out := hAfter i2 hlt v2 hdepart.2.2.2.2.2.1
        exact hv2out hdepart.2.2.2.2.2.2.1
      · have hvout := hdepart.2.2.2.2.2.2.2 i hgt v hiVertex
        exact hvout hvT
    have hvEq : v = v2 := by
      apply Sum.inl.inj
      calc
        Sum.inl v = p.getVert i.val := hiVertex.symm
        _ = p.getVert i2.val := by rw [hiEq]
        _ = Sum.inl v2 := hdepart.2.2.2.2.2.1
    have hno := ScheideDefectiveChainLastReturnNoFree G k e0 phi T hglobal
      delta alpha hDelta hAlphaFree u hu hGammaMissing z p hp
      i1 i2 v1 v2 hdepart
    exact (Finset.disjoint_left.mp hno) (hvEq ▸ hAlphaMissing) hAlphaFree
  · have hfacts := ScheideGlobalMaximumBoundaryFacts G k e0 phi T hglobal
    have hAlphaTree : alpha ∈ TreeMissingColors phi T := by
      simp only [TreeMissingColors, Finset.mem_biUnion]
      exact ⟨v, hvT, hAlphaMissing⟩
    have hGammaTree : gamma ∈ TreeMissingColors phi T := by
      simp only [TreeMissingColors, Finset.mem_biUnion]
      exact ⟨u, hu, hGammaMissing⟩
    have hAlphaBoundary : BoundaryColorEdges G phi X alpha = ∅ := by
      simpa [X] using hfacts.2.1 alpha hAlphaTree
    have hGammaBoundary : BoundaryColorEdges G phi X gamma = ∅ := by
      simpa [X] using hfacts.2.1 gamma hGammaTree
    have hDeltaPresent : ∀ w, w ∈ X → delta ∈ PresentColors G phi w := by
      intro w hw
      have hcard : 0 < (BoundaryColorEdges G phi X delta).card := by
        have hc : 3 ≤ (BoundaryColorEdges G phi X delta).card := by
          simpa [X] using (hfacts.2.2 delta hDelta).2
        omega
      obtain ⟨f, hf⟩ := Finset.card_pos.mp hcard
      have hnot : delta ∉ MissingColors G phi w := by
        intro hm
        exact hclosed (Finset.mem_filter.mp hf).1 hw
          (Finset.mem_filter.mp hf).2 hm
      simpa [MissingColors] using hnot
    have hDeltaGamma : delta ≠ gamma := by
      intro h
      have hpresent := hDeltaPresent u (by simpa [X] using hu)
      have hnot : gamma ∉ PresentColors G phi u := by
        simpa [MissingColors] using hGammaMissing
      exact hnot (h ▸ hpresent)
    have hDeltaAlpha : delta ≠ alpha := by
      intro h
      have hpresent := hDeltaPresent v (by simpa [X] using hvT)
      have hnot : alpha ∉ PresentColors G phi v := by
        simpa [MissingColors] using hAlphaMissing
      exact hnot (h ▸ hpresent)
    have ends_eq_of_mem : ∀ {q : Sym2 V} {x y : V}, x ∈ q → y ∈ q → x ≠ y →
        q = s(x, y) := by
      intro q x y hx hy hxy
      induction q using Sym2.inductionOn with
      | _ a b =>
        simp only [Sym2.mem_iff] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
          simp_all [Sym2.eq_iff]

    let phi1 := OutsideTreeColorSwap T phi alpha gamma
    have hswap := OutsideTreeColorSwapStable T ∅ phi alpha gamma hproper hone
      hclosed hAlphaTree hGammaTree hAlphaGamma
    have hproper1 : IsProperEdgeColoring G phi1 := by
      simpa [phi1] using hswap.1
    have hone1 : IsOneEdgeUncolored phi1 e0 := by
      simpa [phi1] using hswap.2.1
    have hmissing1 : ∀ w, w ∈ X →
        MissingColors G phi1 w = MissingColors G phi w := by
      intro w hw
      simpa [phi1, X] using hswap.2.2.1.2 w (by simpa [X] using hw)
    have htreeFixed1 : ∀ f, TreeIncidentEdge T f → phi1 f = phi f := by
      intro f hf
      simpa [phi1] using hswap.2.2.2 f hf
    have hAlphaMissing1 : alpha ∈ MissingColors G phi1 v := by
      rw [hmissing1 v (by simpa [X] using hvT)]
      exact hAlphaMissing
    have boundary_tree_incident : ∀ {f}, f ∈ BoundaryEdges G X →
        TreeIncidentEdge T f := by
      intro f hf
      obtain ⟨x, hx, y, hy, hxy⟩ := by
        simpa [BoundaryEdges] using hf
      exact ⟨x, by simpa [X] using hx, by simp [Incident, hxy]⟩
    have hboundaryColors : ∀ c,
        BoundaryColorEdges G phi1 X c = BoundaryColorEdges G phi X c := by
      intro c
      ext f
      simp only [BoundaryColorEdges, Finset.mem_filter]
      constructor
      · rintro ⟨hf, hc⟩
        exact ⟨hf, (htreeFixed1 f (boundary_tree_incident hf)).symm.trans hc⟩
      · rintro ⟨hf, hc⟩
        exact ⟨hf, (htreeFixed1 f (boundary_tree_incident hf)).trans hc⟩
    have hDelta1 : delta ∈ DefectiveColors G phi1 X := by
      have hDeltaDef : DefectiveColor G phi X delta := by
        change delta ∈ Finset.univ.filter (fun c => DefectiveColor G phi X c) at hDelta
        exact (Finset.mem_filter.mp hDelta).2
      change delta ∈ Finset.univ.filter (fun c => DefectiveColor G phi1 X c)
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      unfold DefectiveColor at hDeltaDef ⊢
      rw [hboundaryColors delta]
      exact hDeltaDef
    have tree_edge_incident : ∀ j : Fin T.length,
        TreeIncidentEdge T (T.edge j) := by
      intro j
      obtain ⟨a, ha⟩ := T.attaches j
      refine ⟨T.vertex j.succ, ?_, ?_⟩
      · simp [TreeSequenceVertexSet]
      · simp [Incident, ha]
    have hAlphaFree1 : alpha ∈ TreeFreeColors phi1 T := by
      simp only [TreeFreeColors, Finset.mem_sdiff] at hAlphaFree ⊢
      refine ⟨?_, ?_⟩
      · simp only [TreeMissingColors, Finset.mem_biUnion]
        exact ⟨v, hvT, hAlphaMissing1⟩
      · intro hused
        simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and] at hused
        rcases hused with ⟨j, hj, hc⟩
        apply hAlphaFree.2
        simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨j, hj, (htreeFixed1 (T.edge j) (tree_edge_incident j)).symm.trans hc⟩
    have htree1 : TashkinovTree G e0 phi1 T := by
      intro j hj
      obtain ⟨a, c, hcolor, hmiss⟩ := htree j hj
      refine ⟨a, c, ?_, ?_⟩
      · exact (htreeFixed1 (T.edge j) (tree_edge_incident j)).trans hcolor
      · let w := T.vertex (Fin.castLT a
          (Nat.lt_trans a.isLt (Nat.succ_lt_succ j.isLt)))
        have hwX : w ∈ X := by simp [w, X, TreeSequenceVertexSet]
        rw [hmissing1 w hwX]
        exact hmiss
    have hglobal1 : GlobalMaximumTriple G k e0 phi1 T := by
      refine ⟨?_, htree1, hglobal.2.2⟩
      exact ⟨hglobal.1.1, hglobal.1.2.1, hglobal.1.2.2.1, hproper1, hone1⟩

    have hiLt : i.val < p.length := by
      by_contra hn
      have hiEq : i.val = p.length := by omega
      have hz : p.getVert i.val = Sum.inl z := by simp [hiEq]
      have hvz : v = z := Sum.inl.inj (hiVertex.symm.trans hz)
      exact hp.2.2.1 (hvz ▸ hvT)
    have hfirstNode : ∃ fR : E, p.getVert (i.val + 1) = Sum.inr fR := by
      have hadj := p.adj_getVert_succ hiLt
      rw [hiVertex] at hadj
      cases hq : p.getVert (i.val + 1) with
      | inl w =>
        rw [hq] at hadj
        exfalso
        simpa [TwoColorIncidenceGraph] using hadj
      | inr f => exact ⟨f, rfl⟩
    obtain ⟨fR, hfRnode⟩ := hfirstNode
    have hfRdata : Incident G v fR ∧
        (phi fR = some delta ∨ phi fR = some gamma) := by
      have hadj := p.adj_getVert_succ hiLt
      rw [hiVertex, hfRnode] at hadj
      simpa [TwoColorIncidenceGraph] using hadj
    have hfirstLt : i.val + 1 < p.length := by
      by_contra hn
      have heq : i.val + 1 = p.length := by omega
      have hz : p.getVert (i.val + 1) = Sum.inl z := by simp [heq]
      rw [hfRnode] at hz
      simp at hz
    have hnextNode : ∃ wR : V, p.getVert (i.val + 2) = Sum.inl wR := by
      have hadj := p.adj_getVert_succ hfirstLt
      rw [hfRnode] at hadj
      cases hq : p.getVert (i.val + 2) with
      | inl w => exact ⟨w, rfl⟩
      | inr f =>
        rw [hq] at hadj
        exfalso
        simpa [TwoColorIncidenceGraph] using hadj
    obtain ⟨wR, hwRnode⟩ := hnextNode
    have hwRout : wR ∉ X := by
      have hibound : i.val + 2 < p.length + 1 := by omega
      let r : Fin (p.length + 1) := ⟨i.val + 2, hibound⟩
      have hir : i.val < r.val := by simp [r]
      have hout := hAfter r hir wR (by simpa [r] using hwRnode)
      simpa [X] using hout
    have hwRinc : Incident G wR fR := by
      have hadj := p.adj_getVert_succ hfirstLt
      rw [hfRnode, hwRnode] at hadj
      simpa [TwoColorIncidenceGraph] using hadj.1
    have hvwR : v ≠ wR := by
      intro h
      exact hwRout (h ▸ (by simpa [X] using hvT))
    have hfRBoundary : fR ∈ BoundaryEdges G X := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨v, by simpa [X] using hvT, wR, hwRout,
        ends_eq_of_mem hfRdata.1 hwRinc hvwR⟩
    have hfRDelta : phi fR = some delta := by
      rcases hfRdata.2 with hd | hg
      · exact hd
      · have : fR ∈ BoundaryColorEdges G phi X gamma :=
          Finset.mem_filter.mpr ⟨hfRBoundary, hg⟩
        rw [hGammaBoundary] at this
        simp at this

    let H := TwoColorIncidenceGraph G phi delta gamma
    have adjacent_indices_forward : ∀ (n m : ℕ), n ≤ p.length → m ≤ p.length →
        n < m → H.Adj (p.getVert n) (p.getVert m) → m = n + 1 := by
      intro n m hn hm hnm hadj
      by_contra hne
      have hgap : n + 1 < m := by omega
      by_cases hn0 : n = 0
      · subst n
        have hfirstAdj := p.adj_getVert_succ (by omega : 0 < p.length)
        have hdeg : @SimpleGraph.degree _ H (Sum.inl u) (Fintype.ofFinite _) ≤ 1 := by
          have hd := MissingColorIncidenceEndpoint G phi gamma delta hDeltaGamma.symm
            hproper u hGammaMissing
          have hgraph : TwoColorIncidenceGraph G phi gamma delta = H := by
            ext x y
            cases x <;> cases y <;> simp [H, TwoColorIncidenceGraph, or_comm]
          rw [← hgraph]
          exact hd
        have hstart : p.getVert 0 = Sum.inl u := by simp
        have hneigh : p.getVert 1 ≠ p.getVert m := by
          intro heq
          have h1m : 1 ≤ m := by omega
          have := hp.2.1.getVert_injOn (h1m.trans hm) hm heq
          omega
        have htwo : 2 ≤ (@SimpleGraph.neighborFinset (Sum V E) H (Sum.inl u)
            (Fintype.ofFinite _)).card := by
          have hs : ({p.getVert 1, p.getVert m} : Finset (Sum V E)) ⊆
              @SimpleGraph.neighborFinset (Sum V E) H (Sum.inl u)
                (Fintype.ofFinite _) := by
            intro q hq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl
            · simpa [SimpleGraph.mem_neighborFinset, H, hstart] using hfirstAdj
            · simpa [SimpleGraph.mem_neighborFinset, H, hstart] using hadj
          have hc : ({p.getVert 1, p.getVert m} : Finset (Sum V E)).card = 2 := by
            simp [hneigh]
          rw [← hc]
          exact Finset.card_le_card hs
        rw [← SimpleGraph.card_neighborFinset_eq_degree] at hdeg
        have : 2 ≤ 1 := htwo.trans hdeg
        omega
      · have hnlt : n < p.length := by omega
        have hleft : H.Adj (p.getVert n) (p.getVert (n - 1)) := by
          have h := p.adj_getVert_succ (i := n - 1) (by omega)
          have heq : n - 1 + 1 = n := by omega
          simpa [H, heq] using h.symm
        have hright : H.Adj (p.getVert n) (p.getVert (n + 1)) := by
          simpa [H] using p.adj_getVert_succ hnlt
        have hnm1 : p.getVert (n - 1) ≠ p.getVert (n + 1) := by
          intro heq
          have := hp.2.1.getVert_injOn (Nat.sub_le n 1 |>.trans hn)
            (Nat.succ_le_of_lt hnlt) heq
          omega
        have hnm2 : p.getVert (n - 1) ≠ p.getVert m := by
          intro heq
          have := hp.2.1.getVert_injOn (Nat.sub_le n 1 |>.trans hn) hm heq
          omega
        have hnm3 : p.getVert (n + 1) ≠ p.getVert m := by
          intro heq
          have := hp.2.1.getVert_injOn (Nat.succ_le_of_lt hnlt) hm heq
          omega
        have hthree : 3 ≤ (@SimpleGraph.neighborFinset (Sum V E) H (p.getVert n)
            (Fintype.ofFinite _)).card := by
          let S : Finset (Sum V E) :=
            {p.getVert (n - 1), p.getVert (n + 1), p.getVert m}
          have hs : S ⊆ @SimpleGraph.neighborFinset (Sum V E) H (p.getVert n)
              (Fintype.ofFinite _) := by
            intro q hq
            simp only [S, Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl
            · simpa [SimpleGraph.mem_neighborFinset] using hleft
            · simpa [SimpleGraph.mem_neighborFinset] using hright
            · simpa [SimpleGraph.mem_neighborFinset, H] using hadj
          have hc : S.card = 3 := by
            simp [S, hnm1, hnm2, hnm3, hnm1.symm, hnm2.symm, hnm3.symm]
          rw [← hc]
          exact Finset.card_le_card hs
        have hdeg := TwoColorIncidenceDegreeAtMostTwo G phi delta gamma hproper
          (p.getVert n)
        change @SimpleGraph.degree _ H (p.getVert n) (Fintype.ofFinite _) ≤ 2 at hdeg
        rw [← SimpleGraph.card_neighborFinset_eq_degree] at hdeg
        have : 3 ≤ 2 := hthree.trans hdeg
        omega
    have old_adjacent_indices : ∀ (n m : ℕ), n ≤ p.length → m ≤ p.length →
        H.Adj (p.getVert n) (p.getVert m) → n + 1 = m ∨ m + 1 = n := by
      intro n m hn hm hadj
      have hne : n ≠ m := by
        intro h
        subst m
        exact H.loopless.irrefl _ hadj
      rcases lt_or_gt_of_ne hne with hnm | hmn
      · exact Or.inl (adjacent_indices_forward n m hn hm hnm hadj).symm
      · exact Or.inr (adjacent_indices_forward m n hm hn hmn hadj.symm).symm

    let R : Set (Sum V E) := {q | ∃ n : ℕ, i.val ≤ n ∧ n ≤ p.length ∧
      p.getVert n = q}
    have hvR : Sum.inl v ∈ R := by
      exact ⟨i.val, le_rfl, by omega, hiVertex⟩
    have tail_vertex : ∀ {n : ℕ} {w : V}, i.val ≤ n → n ≤ p.length →
        p.getVert n = Sum.inl w →
        (n = i.val ∧ w = v) ∨ (i.val < n ∧ w ∉ X) := by
      intro n w hn hnl hget
      by_cases heq : n = i.val
      · left
        refine ⟨heq, ?_⟩
        apply Sum.inl.inj
        rw [← hget, heq, hiVertex]
      · right
        have hlt : i.val < n := by omega
        refine ⟨hlt, ?_⟩
        exact hAfter ⟨n, by omega⟩ hlt w hget
    have boundary_of_tree_incident_outside : ∀ {e : E} {w : V},
        TreeIncidentEdge T e → w ∉ X → Incident G w e → e ∈ BoundaryEdges G X := by
      intro e w he hwout hwe
      obtain ⟨x, hx, hxe⟩ := he
      have hxX : x ∈ X := by simpa [X] using hx
      have hxw : x ≠ w := by
        intro h
        exact hwout (h ▸ hxX)
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x, hxX, w, hwout, ends_eq_of_mem hxe hwe hxw⟩
    have new_adj_old : ∀ {q r : Sum V E}, q ∈ R →
        (TwoColorIncidenceGraph G phi1 delta alpha).Adj q r → H.Adj q r := by
      intro q r hq hadj
      obtain ⟨n, hn, hnl, hget⟩ := hq
      cases q with
      | inl w =>
        cases r with
        | inl x => simp [TwoColorIncidenceGraph] at hadj
        | inr e =>
          have hnew : Incident G w e ∧
              (phi1 e = some delta ∨ phi1 e = some alpha) := by
            simpa [TwoColorIncidenceGraph] using hadj
          have hold : phi e = some delta ∨ phi e = some gamma := by
            by_cases hti : TreeIncidentEdge T e
            · have hfix := htreeFixed1 e hti
              rcases hnew.2 with hd | ha
              · exact Or.inl (hfix.symm.trans hd)
              · have hAlphaOld : phi e = some alpha := hfix.symm.trans ha
                rcases tail_vertex hn hnl hget with hbase | hout
                · have hwAlpha : alpha ∈ PresentColors G phi w := by
                    simp [PresentColors]
                    exact ⟨e, hnew.1, hAlphaOld⟩
                  have hwMissing : alpha ∈ MissingColors G phi w := by
                    simpa [hbase.2] using hAlphaMissing
                  have hnotPresent : alpha ∉ PresentColors G phi w := by
                    simpa [MissingColors] using hwMissing
                  exact False.elim (hnotPresent hwAlpha)
                · have heb := boundary_of_tree_incident_outside hti hout.2 hnew.1
                  have hec : e ∈ BoundaryColorEdges G phi X alpha :=
                    Finset.mem_filter.mpr ⟨heb, hAlphaOld⟩
                  rw [hAlphaBoundary] at hec
                  simp at hec
            · rcases hnew.2 with hd | ha
              · by_cases heA : phi e = some alpha
                · have heq : some gamma = some delta := by
                    simpa [phi1, OutsideTreeColorSwap, hti, heA, hAlphaGamma] using hd
                  exact False.elim (hDeltaGamma (Option.some.inj heq).symm)
                · by_cases heG : phi e = some gamma
                  · have heq : some alpha = some delta := by
                      simpa [phi1, OutsideTreeColorSwap, hti, heA, heG,
                        Ne.symm hAlphaGamma] using hd
                    exact False.elim (hDeltaAlpha (Option.some.inj heq).symm)
                  · exact Or.inl (by
                      simpa [phi1, OutsideTreeColorSwap, hti, heA, heG] using hd)
              · by_cases heA : phi e = some alpha
                · have heq : some gamma = some alpha := by
                    simpa [phi1, OutsideTreeColorSwap, hti, heA, hAlphaGamma] using ha
                  exact False.elim (hAlphaGamma (Option.some.inj heq).symm)
                · by_cases heG : phi e = some gamma
                  · exact Or.inr heG
                  · have : phi e = some alpha := by
                      simpa [phi1, OutsideTreeColorSwap, hti, heA, heG] using ha
                    exact False.elim (heA this)
          simpa [H, TwoColorIncidenceGraph] using And.intro hnew.1 hold
      | inr e =>
        cases r with
        | inr f => simp [TwoColorIncidenceGraph] at hadj
        | inl w =>
          have hn0 : 0 < n := by
            by_contra hz
            have hz0 : n = 0 := by omega
            rw [hz0] at hget
            simp at hget
          have hprev := p.adj_getVert_succ (i := n - 1) (by omega)
          have hidx : n - 1 + 1 = n := by omega
          rw [hidx, hget] at hprev
          cases hprevNode : p.getVert (n - 1) with
          | inr f =>
            rw [hprevNode] at hprev
            exfalso
            simpa [H, TwoColorIncidenceGraph] using hprev
          | inl x =>
            have hold : phi e = some delta ∨ phi e = some gamma := by
              rw [hprevNode] at hprev
              simpa [H, TwoColorIncidenceGraph] using hprev.2
            have hinc : Incident G w e := by
              simpa [TwoColorIncidenceGraph] using hadj.1
            simpa [H, TwoColorIncidenceGraph] using And.intro hinc hold
    have R_closed : ∀ {q r : Sum V E}, q ∈ R →
        (TwoColorIncidenceGraph G phi1 delta alpha).Adj q r → r ∈ R := by
      intro q r hq hadj
      have holdAdj := new_adj_old hq hadj
      obtain ⟨n, hn, hnl, hget⟩ := hq
      have hqOld : q ∈ TwoColorComponent G phi delta gamma (Sum.inl u) := by
        rw [← hp.2.2.2]
        rw [← hget]
        exact p.getVert_mem_support n
      have hrOld : r ∈ TwoColorComponent G phi delta gamma (Sum.inl u) := by
        change H.connectedComponentMk r = H.connectedComponentMk (Sum.inl u)
        change H.connectedComponentMk q = H.connectedComponentMk (Sum.inl u) at hqOld
        exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          holdAdj.symm).trans hqOld
      have hrSupport : r ∈ p.support := by
        have : r ∈ {x | x ∈ p.support} := by
          rw [hp.2.2.2]
          exact hrOld
        exact this
      obtain ⟨m, hmget, hml⟩ :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hrSupport
      have hindices := old_adjacent_indices n m hnl hml
        (by simpa [H, hget, hmget] using holdAdj)
      rcases hindices with hforward | hback
      · exact ⟨m, by omega, hml, hmget⟩
      · by_cases hm : i.val ≤ m
        · exact ⟨m, hm, hml, hmget⟩
        · have hnbase : n = i.val := by omega
          have hmbase : m + 1 = i.val := by omega
          have hqv : q = Sum.inl v := by
            rw [← hget, hnbase, hiVertex]
          cases hr : r with
          | inl w =>
            have hbad : (TwoColorIncidenceGraph G phi1 delta alpha).Adj
                (Sum.inl v) (Sum.inl w) := by
              simpa [hqv, hr] using hadj
            exfalso
            simpa [TwoColorIncidenceGraph] using hbad
          | inr e =>
            have hadj' : (TwoColorIncidenceGraph G phi1 delta alpha).Adj
                (Sum.inl v) (Sum.inr e) := by
              simpa [hqv, hr] using hadj
            have hnew : Incident G v e ∧
                (phi1 e = some delta ∨ phi1 e = some alpha) := by
              simpa [TwoColorIncidenceGraph] using hadj'
            have hnotAlpha : phi1 e ≠ some alpha := by
              intro he
              have hpresent : alpha ∈ PresentColors G phi1 v := by
                simp [PresentColors]
                exact ⟨e, hnew.1, he⟩
              have hnotPresent : alpha ∉ PresentColors G phi1 v := by
                simpa [MissingColors] using hAlphaMissing1
              exact hnotPresent hpresent
            have heDelta : phi1 e = some delta := hnew.2.resolve_right hnotAlpha
            have heTree : TreeIncidentEdge T e := by
              exact ⟨v, hvT, hnew.1⟩
            have heOld : phi e = some delta :=
              (htreeFixed1 e heTree).symm.trans heDelta
            have hef : e ≠ fR := by
              intro hef
              have hnodes : p.getVert m = p.getVert (i.val + 1) := by
                rw [hmget, hr, hef, hfRnode]
              have hidx := hp.2.1.getVert_injOn hml
                (Nat.le_of_lt hfirstLt) hnodes
              omega
            exact False.elim
              ((hproper hef ⟨v, hnew.1, hfRdata.1⟩ heOld) hfRDelta)
    let C := TwoColorComponent G phi1 delta alpha (Sum.inl v)
    have hcomponentTail : C ⊆ R := by
      intro q hq
      change (TwoColorIncidenceGraph G phi1 delta alpha).connectedComponentMk q =
        (TwoColorIncidenceGraph G phi1 delta alpha).connectedComponentMk
          (Sum.inl v) at hq
      have hreach := SimpleGraph.ConnectedComponent.exact hq
      obtain ⟨walk⟩ := hreach
      have propagate : ∀ {a b : Sum V E},
          (TwoColorIncidenceGraph G phi1 delta alpha).Walk a b → a ∈ R → b ∈ R := by
        intro a b walk ha
        induction walk with
        | nil => exact ha
        | @cons a c b hac rest ih => exact ih (R_closed ha hac)
      exact propagate walk.reverse hvR
    have boundary_tail_unique : ∀ f : E, f ∈ BoundaryEdges G X →
        Sum.inr f ∈ R → f = fR := by
      intro f hf hfr
      obtain ⟨n, hn, hnl, hget⟩ := hfr
      have hnstrict : i.val < n := by
        have hne : n ≠ i.val := by
          intro heq
          have : Sum.inr f = Sum.inl v := by
            rw [← hget, heq, hiVertex]
          simp at this
        omega
      by_cases heq : n = i.val + 1
      · apply Sum.inr.inj
        rw [← hget, heq, hfRnode]
      · have hfar : i.val + 1 < n := by omega
        have hn0 : 0 < n := by omega
        have hnlt : n < p.length := by
          by_contra hnot
          have hnend : n = p.length := by omega
          have hz : p.getVert n = Sum.inl z := by simp [hnend]
          rw [hget] at hz
          simp at hz
        have hleftAdj := p.adj_getVert_succ (i := n - 1) (by omega)
        have hleftIdx : n - 1 + 1 = n := by omega
        rw [hleftIdx, hget] at hleftAdj
        have hrightAdj := p.adj_getVert_succ (i := n) hnlt
        rw [hget] at hrightAdj
        cases hl : p.getVert (n - 1) with
        | inr e =>
          rw [hl] at hleftAdj
          exfalso
          simpa [TwoColorIncidenceGraph] using hleftAdj
        | inl a =>
          rw [hl] at hleftAdj
          cases hr : p.getVert (n + 1) with
          | inr e =>
            rw [hr] at hrightAdj
            exfalso
            simpa [TwoColorIncidenceGraph] using hrightAdj
          | inl b =>
            rw [hr] at hrightAdj
            have haout : a ∉ X := by
              have hi : i.val < n - 1 := by omega
              exact hAfter
                ⟨n - 1, Nat.lt_succ_of_le ((Nat.sub_le n 1).trans hnl)⟩ hi a hl
            have hbout : b ∉ X := by
              have hi : i.val < n + 1 := by omega
              exact hAfter
                ⟨n + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hnlt)⟩ hi b hr
            obtain ⟨x, hx, y, hy, hends⟩ := by
              simpa [BoundaryEdges] using hf
            have habv : a ≠ b := by
              intro habv
              have hnodes : p.getVert (n - 1) = p.getVert (n + 1) := by
                rw [hl, hr, habv]
              have hidx := hp.2.1.getVert_injOn
                (Nat.sub_le _ _ |>.trans hnl) (Nat.succ_le_of_lt hnlt) hnodes
              omega
            have habEnds : G.ends f = s(a, b) :=
              ends_eq_of_mem hleftAdj.1 hrightAdj.1 habv
            have hxab : x = a ∨ x = b := by
              have hxmem : x ∈ s(a, b) := by
                rw [← habEnds]
                exact hends ▸ Sym2.mem_iff.mpr (Or.inl rfl)
              simpa using hxmem
            rcases hxab with rfl | rfl
            · exact False.elim (haout hx)
            · exact False.elim (hbout hx)

    obtain ⟨z1, q, hq⟩ := ScheideDefectiveChainPathExists G k e0 phi1 T
      hglobal1 delta alpha hDelta1 hAlphaFree1 v hvT hAlphaMissing1
    have hboundary := ScheideDefectiveChainBoundaryEdges G k e0 phi1 T
      hglobal1 delta alpha hDelta1 hAlphaFree1 v hvT hAlphaMissing1 z1 q hq
    have hnewFacts := ScheideGlobalMaximumBoundaryFacts G k e0 phi1 T hglobal1
    have hcard : 3 ≤ (BoundaryColorEdges G phi1 X delta).card := by
      simpa [X] using (hnewFacts.2.2 delta (by simpa [X] using hDelta1)).2
    obtain ⟨f, hf⟩ := Finset.card_pos.mp (by omega :
      0 < (BoundaryColorEdges G phi1 X delta).card)
    obtain ⟨g, hg, hgf⟩ :=
      (BoundaryColorEdges G phi1 X delta).exists_mem_ne (by omega) f
    have edge_in_tail : ∀ e ∈ BoundaryColorEdges G phi1 X delta,
        Sum.inr e ∈ R := by
      intro e he
      have heq := (hboundary e).mp (by simpa [X] using he)
      apply hcomponentTail
      change Sum.inr e ∈ TwoColorComponent G phi1 delta alpha (Sum.inl v)
      have hs : Sum.inr e ∈ {x | x ∈ q.support} := heq.2
      rw [hq.2.2.2] at hs
      exact hs
    have hfEq : f = fR := by
      exact boundary_tail_unique f (Finset.mem_filter.mp hf).1 (edge_in_tail f hf)
    have hgEq : g = fR := by
      exact boundary_tail_unique g (Finset.mem_filter.mp hg).1 (edge_in_tail g hg)
    exact hgf (hgEq.trans hfEq.symm)
