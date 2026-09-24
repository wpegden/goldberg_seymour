import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.ColoredVertexSetClosed
import Tablet.DefectiveColors
import Tablet.GlobalMaximumTriple
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.OutsideTreeColorSwap
import Tablet.OutsideTreeColorSwapStable
import Tablet.PresentColors
import Tablet.ScheideDefectiveReturnData
import Tablet.ScheideDefectiveChainPath
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideReducedConfiguration
import Tablet.StableColoring
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideDefectiveSecondTerminalComponent]
theorem ScheideDefectiveSecondTerminalComponent {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideDefectiveReturnData G k e0 phi T C D d) :
    let gamma := C.gamma (D.gammaIndex d)
    let gammaJ := C.gamma R.blockIndex
    let psi1 := OutsideTreeColorSwap T phi gamma gammaJ
    let K := TwoColorComponent G psi1 gammaJ d.1 (Sum.inl R.v1)
    let psi2 := TwoColorComponentSwap G psi1 gammaJ d.1 (Sum.inl R.v1)
    IsProperEdgeColoring G psi1 ∧ IsOneEdgeUncolored psi1 e0 ∧
      StableColoring T ∅ phi psi1 ∧
      (∀ f : E, TreeIncidentEdge T f → psi1 f = phi f) ∧
      {q | ∃ r : Fin ((D.replacementPath d).length + 1),
        R.pathIndex.val ≤ r.val ∧
          (D.replacementPath d).getVert r.val = q} = K ∧
      Sum.inr R.f1 ∈ K ∧
      (∀ v : V, v ∈ TreeSequenceVertexSet T →
        (Sum.inl v ∈ K ↔ v = R.v1)) ∧
      (∀ q : Fin T.length, Sum.inr (T.edge q) ∉ K) ∧
      psi1 R.f1 = some d.1 ∧
      IsProperEdgeColoring G psi2 ∧ IsOneEdgeUncolored psi2 e0 ∧
      d.1 ∈ MissingColors G psi2 R.v1 ∧
      (∀ v ∈ TreeSequenceVertexSet T, v ≠ R.v1 →
        MissingColors G psi2 v = MissingColors G phi v) ∧
      psi2 (D.f0 d) = some d.1 := by
-- BODY
  classical
  dsimp only
  let X := TreeSequenceVertexSet T
  let v0 := D.v0 d
  let gamma := C.gamma (D.gammaIndex d)
  let gammaJ := C.gamma R.blockIndex
  let phi1 := OutsideTreeColorSwap T phi gamma gammaJ
  let p := D.replacementPath d
  let i := R.pathIndex
  let H0 := TwoColorIncidenceGraph G phi gamma d.1
  let H1 := TwoColorIncidenceGraph G phi1 gammaJ d.1
  let S : Set (Sum V E) := {q | ∃ r : Fin (p.length + 1),
    i.val ≤ r.val ∧ p.getVert r.val = q}
  let K := TwoColorComponent G phi1 gammaJ d.1 (Sum.inl R.v1)
  let psi2 := TwoColorComponentSwap G phi1 gammaJ d.1 (Sum.inl R.v1)

  have hproper : IsProperEdgeColoring G phi := C.globally_maximum.1.2.2.2.1
  have hone : IsOneEdgeUncolored phi e0 := C.globally_maximum.1.2.2.2.2
  have horder := ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum
  have hclosed0 : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) :=
    horder.2.2.2.2
  have hclosed : ColoredVertexSetClosed G phi X := by
    exact hclosed0
  have hv0X : v0 ∈ X := by
    simpa [v0, X] using (D.replacement_path_full d).1
  have hv1X : R.v1 ∈ X := by
    simpa [X] using R.v1_mem
  have hpath : ScheideDefectiveChainPath T phi gamma d.1
      v0 (D.replacementZ d) p := by
    simpa [v0, p] using D.replacement_path_full d
  have hpathIs : p.IsPath := hpath.2.1
  have hsupport : {q | q ∈ p.support} =
      TwoColorComponent G phi gamma d.1 (Sum.inl v0) := hpath.2.2.2

  have hdefective : DefectiveColor G phi X d.1 := by
    have hd := d.2
    change d.1 ∈ (Finset.univ.filter fun delta =>
      DefectiveColor G phi X delta) at hd
    exact (Finset.mem_filter.mp hd).2
  have hdeltaPresent : ∀ v, v ∈ X → d.1 ∈ PresentColors G phi v := by
    intro v hv
    have hcard : 0 < (BoundaryColorEdges G phi X d.1).card := by
      change 2 ≤ (BoundaryColorEdges G phi X d.1).card at hdefective
      omega
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hcard
    have hnot : d.1 ∉ MissingColors G phi v := by
      intro hm
      exact hclosed (Finset.mem_filter.mp hb).1 hv
        (Finset.mem_filter.mp hb).2 hm
    simpa [MissingColors] using hnot
  have hgammaDelta : gamma ≠ d.1 := by
    simpa [gamma] using R.gamma_ne_delta
  have hgammaJDelta : gammaJ ≠ d.1 := by
    simpa [gammaJ] using R.gammaJ_ne_delta
  have hgammaGammaJ : gamma ≠ gammaJ := by
    simpa [gammaJ] using R.gamma_ne_gammaJ
  have hgammaTree : gamma ∈ TreeMissingColors phi T := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨v0, by simpa [X] using hv0X, by simpa [v0, gamma] using D.gamma_missing_at_v0 d⟩
  have hgammaJTree : gammaJ ∈ TreeMissingColors phi T := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨R.v1, by simpa [X] using hv1X,
      by simpa [gammaJ] using R.gammaJ_missing⟩
  have hswap := OutsideTreeColorSwapStable T ∅ phi gamma gammaJ
    hproper hone hclosed0 hgammaTree hgammaJTree hgammaGammaJ
  have hproper1 : IsProperEdgeColoring G phi1 := by
    simpa [phi1] using hswap.1
  have hone1 : IsOneEdgeUncolored phi1 e0 := by
    simpa [phi1] using hswap.2.1
  have hstable1 : StableColoring T ∅ phi phi1 := by
    simpa [phi1] using hswap.2.2.1
  have hfixed : ∀ f, TreeIncidentEdge T f → phi1 f = phi f := by
    intro f hf
    simpa [phi1] using hswap.2.2.2 f hf

  have hsucc := R.successive_indices
  have hiTwo : i.val + 2 < p.length + 1 := by
    dsimp [i, p]
    rw [← hsucc.2]
    exact (R.outsideIndex).isLt
  have hiOneLt : i.val + 1 < p.length := by omega
  have hv1At : p.getVert i.val = Sum.inl (R.v1) := by
    simpa [p, i] using R.v1_at_index
  have hf1At : p.getVert (i.val + 1) = Sum.inr (R.f1) := by
    rw [← hsucc.1]
    simpa [p] using R.f1_at_index

  have ends_eq_of_mem : ∀ {q : Sym2 V} {x y : V}, x ∈ q → y ∈ q → x ≠ y →
      q = s(x, y) := by
    intro q x y hx hy hxy
    induction q using Sym2.inductionOn with
    | _ a b =>
      simp only [Sym2.mem_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
        simp_all [Sym2.eq_iff]
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
  have missing_no_incident : ∀ {c : Fin k} {v : V} {e : E},
      c ∈ MissingColors G phi v → Incident G v e → phi e ≠ some c := by
    intro c v e hm hinc hc
    have hp : c ∈ PresentColors G phi v := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e, hinc, hc⟩
    have hnot : c ∉ PresentColors G phi v := by
      simpa [MissingColors] using hm
    exact hnot hp
  have tail_vertex : ∀ {r : Fin (p.length + 1)} {w : V}, i.val ≤ r.val →
      p.getVert r.val = Sum.inl w →
      (r.val = i.val ∧ w = R.v1) ∨ (i.val < r.val ∧ w ∉ X) := by
    intro r w hir hget
    by_cases hri : r.val = i.val
    · left
      refine ⟨hri, ?_⟩
      apply Sum.inl.inj
      rw [← hget, hri, hv1At]
    · right
      have hlt : i.val < r.val := by omega
      refine ⟨hlt, ?_⟩
      simpa [X, p, i] using R.after_last_tree_vertex r hlt w (by simpa [p] using hget)

  have hy0Degree : @SimpleGraph.degree _ H0 (Sum.inl v0)
      (Fintype.ofFinite _) ≤ 1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [SimpleGraph.mem_neighborFinset] at ha hb
    cases a with
    | inl a => simp [H0, TwoColorIncidenceGraph] at ha
    | inr e =>
      cases b with
      | inl b => simp [H0, TwoColorIncidenceGraph] at hb
      | inr f =>
        simp only [H0, TwoColorIncidenceGraph] at ha hb
        have hea : phi e = some d.1 := ha.2.resolve_left
          (missing_no_incident
            (by simpa [gamma, v0] using D.gamma_missing_at_v0 d) ha.1)
        have hfa : phi f = some d.1 := hb.2.resolve_left
          (missing_no_incident
            (by simpa [gamma, v0] using D.gamma_missing_at_v0 d) hb.1)
        by_cases hef : e = f
        · exact congrArg Sum.inr hef
        · exact False.elim ((hproper hef ⟨v0, ha.1, hb.1⟩ hea) hfa)
  have adjacent_indices_forward : ∀ (n m : ℕ), n ≤ p.length → m ≤ p.length →
      n < m → H0.Adj (p.getVert n) (p.getVert m) → m = n + 1 := by
    intro n m hn hm hnm hadj
    by_contra hne
    have hgap : n + 1 < m := by omega
    by_cases hn0 : n = 0
    · subst n
      have hfirstAdj := p.adj_getVert_succ (by omega : 0 < p.length)
      have hstart : p.getVert 0 = Sum.inl v0 := by simp [p, v0]
      have hneigh : p.getVert 1 ≠ p.getVert m := by
        intro heq
        have := hpathIs.getVert_injOn (show 1 ≤ p.length by omega) hm heq
        omega
      have htwo : 2 ≤ (@SimpleGraph.neighborFinset (Sum V E) H0 (Sum.inl v0)
          (Fintype.ofFinite _)).card := by
        have hs : ({p.getVert 1, p.getVert m} : Finset (Sum V E)) ⊆
            @SimpleGraph.neighborFinset (Sum V E) H0 (Sum.inl v0)
              (Fintype.ofFinite _) := by
          intro q hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl
          · simpa [SimpleGraph.mem_neighborFinset, H0, hstart] using hfirstAdj
          · simpa [SimpleGraph.mem_neighborFinset, H0, hstart] using hadj
        have hc : ({p.getVert 1, p.getVert m} : Finset (Sum V E)).card = 2 := by
          simp [hneigh]
        rw [← hc]
        exact Finset.card_le_card hs
      rw [← SimpleGraph.card_neighborFinset_eq_degree] at hy0Degree
      omega
    · have hnlt : n < p.length := by omega
      have hleft : H0.Adj (p.getVert n) (p.getVert (n - 1)) := by
        have h := p.adj_getVert_succ (i := n - 1) (by omega)
        have heq : n - 1 + 1 = n := by omega
        simpa [H0, heq] using h.symm
      have hright : H0.Adj (p.getVert n) (p.getVert (n + 1)) := by
        simpa [H0] using p.adj_getVert_succ hnlt
      have hnm1 : p.getVert (n - 1) ≠ p.getVert (n + 1) := by
        intro heq
        have := hpathIs.getVert_injOn (Nat.sub_le n 1 |>.trans hn)
          (Nat.succ_le_of_lt hnlt) heq
        omega
      have hnm2 : p.getVert (n - 1) ≠ p.getVert m := by
        intro heq
        have := hpathIs.getVert_injOn (Nat.sub_le n 1 |>.trans hn) hm heq
        omega
      have hnm3 : p.getVert (n + 1) ≠ p.getVert m := by
        intro heq
        have := hpathIs.getVert_injOn (Nat.succ_le_of_lt hnlt) hm heq
        omega
      have hthree : 3 ≤ (@SimpleGraph.neighborFinset (Sum V E) H0 (p.getVert n)
          (Fintype.ofFinite _)).card := by
        let S : Finset (Sum V E) :=
          {p.getVert (n - 1), p.getVert (n + 1), p.getVert m}
        have hs : S ⊆ @SimpleGraph.neighborFinset (Sum V E) H0 (p.getVert n)
            (Fintype.ofFinite _) := by
          intro q hq
          simp only [S, Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl
          · simpa [SimpleGraph.mem_neighborFinset] using hleft
          · simpa [SimpleGraph.mem_neighborFinset] using hright
          · simpa [SimpleGraph.mem_neighborFinset] using hadj
        have hc : S.card = 3 := by
          simp [S, hnm1, hnm2, hnm3, hnm1.symm, hnm2.symm, hnm3.symm]
        rw [← hc]
        exact Finset.card_le_card hs
      have hdeg := TwoColorIncidenceDegreeAtMostTwo G phi gamma d.1 hproper
        (p.getVert n)
      change @SimpleGraph.degree _ H0 (p.getVert n) (Fintype.ofFinite _) ≤ 2 at hdeg
      rw [← SimpleGraph.card_neighborFinset_eq_degree] at hdeg
      omega
  have old_adjacent_indices : ∀ (n m : ℕ), n ≤ p.length → m ≤ p.length →
      H0.Adj (p.getVert n) (p.getVert m) → n + 1 = m ∨ m + 1 = n := by
    intro n m hn hm hadj
    have hne : n ≠ m := by
      intro h
      subst m
      exact H0.loopless.irrefl _ hadj
    rcases lt_or_gt_of_ne hne with hnm | hmn
    · exact Or.inl (adjacent_indices_forward n m hn hm hnm hadj).symm
    · exact Or.inr (adjacent_indices_forward m n hm hn hmn hadj.symm).symm

  have outside_edge_effect : ∀ {w : V} {e : E}, w ∉ X → Incident G w e →
      (phi e = some gamma ∨ phi e = some d.1) →
      phi1 e = some gammaJ ∨ phi1 e = some d.1 := by
    intro w e hwout hinc hold
    by_cases hti : TreeIncidentEdge T e
    · have hb := boundary_of_tree_incident_outside hti hwout hinc
      have hnotAlpha : phi e ≠ some gamma := by
        intro ha
        exact (hclosed hb hv0X ha)
          (by simpa [v0, gamma] using D.gamma_missing_at_v0 d)
      have hd : phi e = some d.1 := hold.resolve_left hnotAlpha
      exact Or.inr ((hfixed e hti).trans hd)
    · rcases hold with ha | hd
      · left
        simp [phi1, OutsideTreeColorSwap, hti, ha]
      · right
        simp [phi1, OutsideTreeColorSwap, hti, hd, hgammaDelta,
          hgammaJDelta, hgammaDelta.symm, hgammaJDelta.symm]
  have tail_step_new : ∀ n : ℕ, i.val ≤ n → n < p.length →
      H1.Adj (p.getVert n) (p.getVert (n + 1)) := by
    intro n hin hnlt
    have hold := p.adj_getVert_succ hnlt
    cases hleft : p.getVert n with
    | inl w =>
      cases hright : p.getVert (n + 1) with
      | inl x =>
        rw [hleft, hright] at hold
        simp [H0, TwoColorIncidenceGraph] at hold
      | inr e =>
        rw [hleft, hright] at hold
        have hdata : Incident G w e ∧
            (phi e = some gamma ∨ phi e = some d.1) := by
          simpa [H0, TwoColorIncidenceGraph] using hold
        let rn : Fin (p.length + 1) := ⟨n, by omega⟩
        have htv := tail_vertex (r := rn) (w := w) (by simpa [rn] using hin)
          (by simpa [rn] using hleft)
        have hnew : phi1 e = some gammaJ ∨ phi1 e = some d.1 := by
          rcases htv with hbase | hout
          · have hnbase : n = i.val := hbase.1
            have heq : e = R.f1 := by
              apply Sum.inr.inj
              rw [← hright, hnbase, hf1At]
            subst e
            right
            apply (hfixed (R.f1) ?_).trans (R.f1_color)
            exact ⟨R.v1, by simpa [X] using hv1X, by simpa [hbase.2] using hdata.1⟩
          · exact outside_edge_effect hout.2 hdata.1 hdata.2
        simpa [H1, TwoColorIncidenceGraph] using And.intro hdata.1 hnew
    | inr e =>
      cases hright : p.getVert (n + 1) with
      | inr f =>
        rw [hleft, hright] at hold
        simp [H0, TwoColorIncidenceGraph] at hold
      | inl w =>
        rw [hleft, hright] at hold
        have hdata : Incident G w e ∧
            (phi e = some gamma ∨ phi e = some d.1) := by
          simpa [H0, TwoColorIncidenceGraph] using hold
        let rn : Fin (p.length + 1) := ⟨n + 1, by omega⟩
        have htv := tail_vertex (r := rn) (w := w) (by simp [rn]; omega)
          (by simpa [rn] using hright)
        have hwout : w ∉ X := by
          rcases htv with hbase | hout
          · simp [rn] at hbase
            omega
          · exact hout.2
        have hnew := outside_edge_effect hwout hdata.1 hdata.2
        simpa [H1, TwoColorIncidenceGraph] using And.intro hdata.1 hnew

  have new_edge_old : ∀ {r : Fin (p.length + 1)} {w : V} {e : E},
      i.val ≤ r.val → p.getVert r.val = Sum.inl w → Incident G w e →
      (phi1 e = some gammaJ ∨ phi1 e = some d.1) →
      phi e = some gamma ∨ phi e = some d.1 := by
    intro r w e hir hget hinc hnew
    have htv := tail_vertex hir hget
    by_cases hti : TreeIncidentEdge T e
    · have hfix := hfixed e hti
      rcases hnew with hg | hd
      · have hgold : phi e = some gammaJ := hfix.symm.trans hg
        rcases htv with hbase | hout
        · exact False.elim ((missing_no_incident
            (by simpa [gammaJ] using R.gammaJ_missing)
            (by simpa [hbase.2] using hinc)) hgold)
        · have hb := boundary_of_tree_incident_outside hti hout.2 hinc
          exact False.elim ((hclosed hb hv1X hgold)
            (by simpa [gammaJ] using R.gammaJ_missing))
      · exact Or.inr (hfix.symm.trans hd)
    · rcases hnew with hg | hd
      · by_cases ha : phi e = some gamma
        · exact Or.inl ha
        · by_cases hgc : phi e = some gammaJ
          · have heq : some gamma = some gammaJ := by
              simpa [phi1, OutsideTreeColorSwap, hti, ha, hgc, hgammaGammaJ,
                hgammaGammaJ.symm] using hg
            exact False.elim (hgammaGammaJ (Option.some.inj heq))
          · have : phi e = some gammaJ := by
              simpa [phi1, OutsideTreeColorSwap, hti, ha, hgc] using hg
            exact False.elim (hgc this)
      · by_cases ha : phi e = some gamma
        · have heq : some gammaJ = some d.1 := by
            simpa [phi1, OutsideTreeColorSwap, hti, ha] using hd
          exact False.elim (hgammaJDelta (Option.some.inj heq))
        · by_cases hgc : phi e = some gammaJ
          · have heq : some gamma = some d.1 := by
              simpa [phi1, OutsideTreeColorSwap, hti, ha, hgc, hgammaGammaJ,
                hgammaGammaJ.symm] using hd
            exact False.elim (hgammaDelta (Option.some.inj heq))
          · exact Or.inr (by
              simpa [phi1, OutsideTreeColorSwap, hti, ha, hgc] using hd)

  have new_adj_old : ∀ {q r : Sum V E}, q ∈ S → H1.Adj q r → H0.Adj q r := by
    intro q r hq hadj
    obtain ⟨n, hn, hget⟩ := hq
    cases q with
    | inl w =>
      cases r with
      | inl x => simp [H1, TwoColorIncidenceGraph] at hadj
      | inr e =>
        have hnew : Incident G w e ∧
            (phi1 e = some gammaJ ∨ phi1 e = some d.1) := by
          simpa [H1, TwoColorIncidenceGraph] using hadj
        have hold := new_edge_old hn hget hnew.1 hnew.2
        simpa [H0, TwoColorIncidenceGraph] using And.intro hnew.1 hold
    | inr e =>
      cases r with
      | inr f => simp [H1, TwoColorIncidenceGraph] at hadj
      | inl w =>
        have hn0 : 0 < n.val := by
          by_contra hz
          have hz0 : n.val = 0 := by omega
          rw [hz0] at hget
          have : Sum.inr e = Sum.inl v0 := by simpa [p, v0] using hget.symm
          simp at this
        have hprev := p.adj_getVert_succ (i := n.val - 1) (by omega)
        have hidx : n.val - 1 + 1 = n.val := by omega
        rw [hidx, hget] at hprev
        cases hprevNode : p.getVert (n.val - 1) with
        | inr f =>
          rw [hprevNode] at hprev
          simp [H0, TwoColorIncidenceGraph] at hprev
        | inl x =>
          rw [hprevNode] at hprev
          have hold : phi e = some gamma ∨ phi e = some d.1 := by
            simpa [H0, TwoColorIncidenceGraph] using hprev.2
          have hinc : Incident G w e := by
            simpa [H1, TwoColorIncidenceGraph] using hadj.1
          simpa [H0, TwoColorIncidenceGraph] using And.intro hinc hold

  have S_closed : ∀ {q r : Sum V E}, q ∈ S → H1.Adj q r → r ∈ S := by
    intro q r hq hadj
    have holdAdj := new_adj_old hq hadj
    obtain ⟨n, hn, hget⟩ := hq
    have hqOld : q ∈ TwoColorComponent G phi gamma d.1 (Sum.inl v0) := by
      rw [← hsupport]
      rw [← hget]
      exact p.getVert_mem_support n.val
    have hrOld : r ∈ TwoColorComponent G phi gamma d.1 (Sum.inl v0) := by
      change H0.connectedComponentMk r = H0.connectedComponentMk (Sum.inl v0)
      change H0.connectedComponentMk q = H0.connectedComponentMk (Sum.inl v0) at hqOld
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        holdAdj.symm).trans hqOld
    have hrSupport : r ∈ p.support := by
      have : r ∈ {x | x ∈ p.support} := by
        rw [hsupport]
        exact hrOld
      exact this
    obtain ⟨m, hmget, hml⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hrSupport
    have hindices := old_adjacent_indices n.val m (Nat.le_of_lt_succ n.isLt) hml
      (by simpa [H0, hget, hmget] using holdAdj)
    rcases hindices with hforward | hback
    · refine ⟨⟨m, Nat.lt_succ_of_le hml⟩, ?_, hmget⟩
      have him : i.val ≤ m := hn.trans (by omega)
      exact him
    · by_cases hm : i.val ≤ m
      · exact ⟨⟨m, Nat.lt_succ_of_le hml⟩, hm, hmget⟩
      · have hnbase : n.val = i.val := by omega
        have hmbase : m + 1 = i.val := by omega
        have hqv : q = Sum.inl (R.v1) := by
          rw [← hget, hnbase, hv1At]
        cases hr : r with
        | inl w =>
          have hbad : H1.Adj (Sum.inl (R.v1)) (Sum.inl w) := by
            simpa [hqv, hr] using hadj
          simp [H1, TwoColorIncidenceGraph] at hbad
        | inr e =>
          have hbad : H1.Adj (Sum.inl (R.v1)) (Sum.inr e) := by
            simpa [hqv, hr] using hadj
          have hnew : Incident G (R.v1) e ∧
              (phi1 e = some gammaJ ∨ phi1 e = some d.1) := by
            simpa [H1, TwoColorIncidenceGraph] using hbad
          have heTree : TreeIncidentEdge T e :=
            ⟨R.v1, by simpa [X] using hv1X, hnew.1⟩
          have heOld : phi e = some d.1 := by
            rcases hnew.2 with hg | hd
            · have hgold : phi e = some gammaJ := (hfixed e heTree).symm.trans hg
              exact False.elim ((missing_no_incident
                (by simpa [gammaJ] using R.gammaJ_missing) hnew.1) hgold)
            · exact (hfixed e heTree).symm.trans hd
          have hef : e ≠ R.f1 := by
            intro hef
            have hnodes : p.getVert m = p.getVert (i.val + 1) := by
              rw [hmget, hr, hef, hf1At]
            have hidx := hpathIs.getVert_injOn hml (Nat.le_of_lt hiOneLt) hnodes
            omega
          exact False.elim ((hproper hef
            ⟨R.v1, hnew.1, by simp [Incident, R.f1_ends]⟩ heOld)
              (R.f1_color))

  have hcomponentTail : K ⊆ S := by
    intro q hq
    change H1.connectedComponentMk q =
      H1.connectedComponentMk (Sum.inl (R.v1)) at hq
    have hreach := SimpleGraph.ConnectedComponent.exact hq
    obtain ⟨walk⟩ := hreach
    have propagate : ∀ {a b : Sum V E}, H1.Walk a b → a ∈ S → b ∈ S := by
      intro a b walk ha
      induction walk with
      | nil => exact ha
      | @cons a c b hac rest ih => exact ih (S_closed ha hac)
    have hv1R : Sum.inl R.v1 ∈ S := by
      exact ⟨i, le_rfl, hv1At⟩
    exact propagate walk.reverse hv1R
  have htailComponent : S ⊆ K := by
    intro q hq
    obtain ⟨r, hir, hget⟩ := hq
    have go : ∀ t : ℕ, i.val + t ≤ p.length →
        H1.connectedComponentMk (p.getVert (i.val + t)) =
          H1.connectedComponentMk (Sum.inl (R.v1)) := by
      intro t ht
      induction t with
      | zero => simpa using congrArg H1.connectedComponentMk hv1At
      | succ t ih =>
        have hprev : i.val + t ≤ p.length := by omega
        have hadj := tail_step_new (i.val + t) (by omega) (by omega)
        have hcc := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
        exact hcc.symm.trans (ih hprev)
    change H1.connectedComponentMk q = H1.connectedComponentMk (Sum.inl (R.v1))
    rw [← hget]
    have heq : i.val + (r.val - i.val) = r.val := by omega
    rw [← heq]
    have hrle : r.val ≤ p.length := Nat.le_of_lt_succ r.isLt
    exact go (r.val - i.val) (by omega)
  have hRK : S = K := Set.Subset.antisymm htailComponent hcomponentTail

  have hf1K : Sum.inr (R.f1) ∈ K := by
    rw [← hRK]
    exact ⟨R.edgeIndex, by simp [i, hsucc.1], by simpa [p] using R.f1_at_index⟩
  have hKtree : ∀ v : V, v ∈ X →
      (Sum.inl v ∈ K ↔ v = R.v1) := by
    intro v hv
    constructor
    · intro hvK
      have hvR : Sum.inl v ∈ S := by rw [hRK]; exact hvK
      obtain ⟨r, hir, hget⟩ := hvR
      rcases tail_vertex hir hget with hbase | hout
      · exact hbase.2
      · exact False.elim (hout.2 hv)
    · rintro rfl
      rw [← hRK]
      exact ⟨i, le_rfl, hv1At⟩
  have htreeEdges : ∀ q : Fin T.length, Sum.inr (T.edge q) ∉ K := by
    intro q hedge
    have hreach : H1.Reachable (Sum.inl R.v1) (Sum.inr (T.edge q)) := by
      apply SimpleGraph.ConnectedComponent.eq.mp
      change H1.connectedComponentMk (Sum.inr (T.edge q)) =
        H1.connectedComponentMk (Sum.inl R.v1) at hedge
      exact hedge.symm
    have hne : Sum.inl R.v1 ≠ Sum.inr (T.edge q) := by
      intro h
      cases h
    have hsupp : Sum.inr (T.edge q) ∈ H1.support :=
      SimpleGraph.mem_support_of_reachable hne.symm hreach.symm
    obtain ⟨w, hw⟩ := H1.mem_support.mp hsupp
    have hcolor : phi1 (T.edge q) = some gammaJ ∨
        phi1 (T.edge q) = some d.1 := by
      cases w with
      | inl w => exact hw.2
      | inr w => simpa [H1, TwoColorIncidenceGraph] using hw
    obtain ⟨a, hends⟩ := T.attaches q
    let oldIndex : Fin (T.length + 1) :=
      Fin.castLT a (Nat.lt_trans a.isLt (Nat.succ_lt_succ q.isLt))
    let newVertex := T.vertex q.succ
    let oldVertex := T.vertex oldIndex
    have hnewIncident : Incident G newVertex (T.edge q) := by
      change newVertex ∈ G.ends (T.edge q)
      rw [hends]
      simp [newVertex, oldVertex, oldIndex]
    have holdIncident : Incident G oldVertex (T.edge q) := by
      change oldVertex ∈ G.ends (T.edge q)
      rw [hends]
      simp [newVertex, oldVertex, oldIndex]
    have hnewAdj : H1.Adj (Sum.inl newVertex) (Sum.inr (T.edge q)) := by
      simp [H1, TwoColorIncidenceGraph, hnewIncident, hcolor]
    have holdAdj : H1.Adj (Sum.inl oldVertex) (Sum.inr (T.edge q)) := by
      simp [H1, TwoColorIncidenceGraph, holdIncident, hcolor]
    have hnewK : Sum.inl newVertex ∈ K := by
      change H1.connectedComponentMk (Sum.inl newVertex) =
        H1.connectedComponentMk (Sum.inl R.v1)
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        hnewAdj).trans hedge
    have holdK : Sum.inl oldVertex ∈ K := by
      change H1.connectedComponentMk (Sum.inl oldVertex) =
        H1.connectedComponentMk (Sum.inl R.v1)
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        holdAdj).trans hedge
    have hnewX : newVertex ∈ X := by
      simp [X, TreeSequenceVertexSet, newVertex]
    have holdX : oldVertex ∈ X := by
      simp [X, TreeSequenceVertexSet, oldVertex]
    have hnewEq : newVertex = R.v1 := (hKtree newVertex hnewX).mp hnewK
    have holdEq : oldVertex = R.v1 := (hKtree oldVertex holdX).mp holdK
    apply G.loopless (T.edge q) R.v1
    simpa [newVertex, oldVertex, oldIndex, hnewEq, holdEq] using hends
  have hKcolors : ∀ f : E, Sum.inr f ∈ K →
      phi1 f = some gammaJ ∨ phi1 f = some d.1 := by
    intro f hfK
    have hfR : Sum.inr f ∈ S := by rw [hRK]; exact hfK
    obtain ⟨r, hir, hget⟩ := hfR
    have hstrict : i.val < r.val := by
      by_contra hn
      have hre : r.val = i.val := by omega
      have : Sum.inr f = Sum.inl (R.v1) := by
        rw [← hget, hre, hv1At]
      simp at this
    have hadj := tail_step_new (r.val - 1) (by omega) (by omega)
    have hidx : r.val - 1 + 1 = r.val := by omega
    rw [hidx, hget] at hadj
    cases hprev : p.getVert (r.val - 1) with
    | inr e =>
      rw [hprev] at hadj
      simp [H1, TwoColorIncidenceGraph] at hadj
    | inl w =>
      rw [hprev] at hadj
      simpa [H1, TwoColorIncidenceGraph] using hadj.2

  have hf1color : phi1 R.f1 = some d.1 := by
    apply (hfixed R.f1 ?_).trans R.f1_color
    exact ⟨R.v1, by simpa [X] using hv1X, by simp [Incident, R.f1_ends]⟩
  have hproper2 : IsProperEdgeColoring G psi2 := by
    simpa [psi2] using TwoColorComponentSwapProper G phi1 gammaJ d.1
      hgammaJDelta hproper1 (Sum.inl R.v1)
  have hone2 : IsOneEdgeUncolored psi2 e0 := by
    constructor
    · simp [psi2, TwoColorComponentSwap, hone1.1]
    · intro f hfe
      obtain ⟨c, hc⟩ := hone1.2 f hfe
      by_cases hfK : Sum.inr f ∈ K
      · by_cases hcg : phi1 f = some gammaJ
        · exact ⟨d.1, by simp [psi2, TwoColorComponentSwap, K, hfK, hcg]⟩
        · by_cases hcd : phi1 f = some d.1
          · exact ⟨gammaJ, by simp [psi2, TwoColorComponentSwap, K, hfK,
              hcg, hcd, hgammaJDelta]⟩
          · exact ⟨c, by simpa [psi2, TwoColorComponentSwap, K, hfK,
              hcg, hcd] using hc⟩
      · exact ⟨c, by simpa [psi2, TwoColorComponentSwap, K, hfK] using hc⟩
  have hbehavior := TwoColorComponentSwapMissingBehavior G phi1 gammaJ d.1
    hgammaJDelta hproper1 (Sum.inl R.v1)
  have hv1K : Sum.inl R.v1 ∈ K := by rfl
  have hgammaJMissing1 : gammaJ ∈ MissingColors G phi1 R.v1 := by
    rw [hstable1.2 R.v1 (by simpa [X] using hv1X)]
    simpa [gammaJ] using R.gammaJ_missing
  have hdeltaMissing2 : d.1 ∈ MissingColors G psi2 R.v1 := by
    simpa [psi2, K] using hbehavior.2.1 R.v1 hv1K hgammaJMissing1
  have hotherMissing : ∀ v ∈ X, v ≠ R.v1 →
      MissingColors G psi2 v = MissingColors G phi v := by
    intro v hv hvne
    have hvNotK : Sum.inl v ∉ K := by
      intro hvK
      exact hvne ((hKtree v hv).mp hvK)
    calc
      MissingColors G psi2 v = MissingColors G phi1 v := by
        simpa [psi2, K] using hbehavior.1 v hvNotK
      _ = MissingColors G phi v := hstable1.2 v (by simpa [X] using hv)
  have hf0color1 : phi1 (D.f0 d) = some d.1 := by
    apply (hfixed (D.f0 d) ?_).trans (D.f0_color d)
    exact ⟨v0, by simpa [X] using hv0X, by simp [v0, Incident, D.f0_ends d]⟩
  have hf0NotK : Sum.inr (D.f0 d) ∉ K := by
    intro hf0K
    have hv0Adj : H1.Adj (Sum.inl v0) (Sum.inr (D.f0 d)) := by
      simp [H1, TwoColorIncidenceGraph, v0, Incident, D.f0_ends d, hf0color1]
    have hv0K : Sum.inl v0 ∈ K := by
      change H1.connectedComponentMk (Sum.inl v0) =
        H1.connectedComponentMk (Sum.inl R.v1)
      change H1.connectedComponentMk (Sum.inr (D.f0 d)) =
        H1.connectedComponentMk (Sum.inl R.v1) at hf0K
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        hv0Adj).trans hf0K
    exact R.v1_ne_v0 ((hKtree v0 hv0X).mp hv0K).symm
  have hf0color2 : psi2 (D.f0 d) = some d.1 := by
    simp [psi2, TwoColorComponentSwap, K, hf0NotK, hf0color1]

  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [phi1, gamma, gammaJ] using hproper1
  · simpa [phi1, gamma, gammaJ] using hone1
  · simpa [phi1, gamma, gammaJ] using hstable1
  · intro f hf
    simpa [phi1, gamma, gammaJ] using hfixed f hf
  · simpa [S, K, p, i, phi1, gamma, gammaJ] using hRK
  · simpa [K, phi1, gamma, gammaJ] using hf1K
  · intro v hv
    simpa [K, X, phi1, gamma, gammaJ] using hKtree v (by simpa [X] using hv)
  · intro q
    simpa [K, phi1, gamma, gammaJ] using htreeEdges q
  · simpa [phi1, gamma, gammaJ] using hf1color
  · simpa [psi2, phi1, gamma, gammaJ] using hproper2
  · simpa [psi2, phi1, gamma, gammaJ] using hone2
  · simpa [psi2, phi1, gamma, gammaJ] using hdeltaMissing2
  · intro v hv hvne
    simpa [psi2, phi1, gamma, gammaJ] using
      hotherMissing v (by simpa [X] using hv) hvne
  · simpa [psi2, phi1, gamma, gammaJ] using hf0color2
