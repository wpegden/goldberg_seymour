import Tablet.AdjacentEdges
import Tablet.FixedPairMaximalTashkinovTree
import Tablet.GlobalMaximumTriple
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.NormalGlobalMaximumTriple
import Tablet.ScheideGraphHeight
import Tablet.ScheideKempePathHeightBound
import Tablet.ScheideMaximalKempePath
import Tablet.TashkinovOrder
import Tablet.TashkinovTree
import Tablet.TreeColorUnusedThrough
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph

open scoped Sym2

-- [TABLET NODE: ScheideHeightFiveOutsideLinks]
theorem ScheideHeightFiveOutsideLinks {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hNheight : N.height = 5) (hGheight : ScheideGraphHeight G = 5)
    (gamma : Fin k)
    (hgamma : gamma ∈ MissingColors G phi
      (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩))
    (f1 f2 : E) (v1 v2 : V)
    (hf1ends : G.ends f1 =
      s(T.vertex ⟨1, by have := N.height_upper; omega⟩, v1))
    (hf2ends : G.ends f2 =
      s(T.vertex ⟨4, by have := N.height_upper; omega⟩, v2))
    (hf1color : phi f1 = some gamma) (hf2color : phi f2 = some gamma)
    (hv1T : v1 ∈ TreeSequenceVertexSet T)
    (hv2T : v2 ∈ TreeSequenceVertexSet T)
    (hv10 : v1 ≠ T.vertex ⟨0, by have := N.height_upper; omega⟩)
    (hv11 : v1 ≠ T.vertex ⟨1, by have := N.height_upper; omega⟩)
    (hv12 : v1 ≠ T.vertex ⟨2, by have := N.height_upper; omega⟩)
    (hv13 : v1 ≠ T.vertex ⟨3, by have := N.height_upper; omega⟩)
    (hv14 : v1 ≠ T.vertex ⟨4, by have := N.height_upper; omega⟩)
    (hv20 : v2 ≠ T.vertex ⟨0, by have := N.height_upper; omega⟩)
    (hv21 : v2 ≠ T.vertex ⟨1, by have := N.height_upper; omega⟩)
    (hv22 : v2 ≠ T.vertex ⟨2, by have := N.height_upper; omega⟩)
    (hv23 : v2 ≠ T.vertex ⟨3, by have := N.height_upper; omega⟩)
    (hv24 : v2 ≠ T.vertex ⟨4, by have := N.height_upper; omega⟩) :
    ∃ alphaEdge betaEdge : E,
      G.ends alphaEdge = s(v1, v2) ∧ phi alphaEdge = some N.alpha ∧
      G.ends betaEdge = s(v1, v2) ∧ phi betaEdge = some N.beta ∧
      alphaEdge ≠ betaEdge := by
-- BODY
  classical
  let y0 : V := T.vertex ⟨0, by have := N.height_upper; omega⟩
  let y1 : V := T.vertex ⟨1, by have := N.height_upper; omega⟩
  let y2 : V := T.vertex ⟨2, by have := N.height_upper; omega⟩
  let y3 : V := T.vertex ⟨3, by have := N.height_upper; omega⟩
  let y4 : V := T.vertex ⟨4, by have := N.height_upper; omega⟩
  let r1 : Fin T.length := ⟨1, by have := N.height_upper; omega⟩
  let r2 : Fin T.length := ⟨2, by have := N.height_upper; omega⟩
  let r3 : Fin T.length := ⟨3, by have := N.height_upper; omega⟩
  let a1 : E := T.edge r1
  let a2 : E := T.edge r2
  let a3 : E := T.edge r3
  let q : E := N.closingEdge
  have hy01 : y0 ≠ y1 := by
    intro h
    have := T.vertex_injective h
    simp [y0, y1] at this
  have hy02 : y0 ≠ y2 := by
    intro h
    have := T.vertex_injective h
    simp [y0, y2] at this
  have hy03 : y0 ≠ y3 := by
    intro h
    have := T.vertex_injective h
    simp [y0, y3] at this
  have hy04 : y0 ≠ y4 := by
    intro h
    have := T.vertex_injective h
    simp [y0, y4] at this
  have hy12 : y1 ≠ y2 := by
    intro h
    have := T.vertex_injective h
    simp [y1, y2] at this
  have hy13 : y1 ≠ y3 := by
    intro h
    have := T.vertex_injective h
    simp [y1, y3] at this
  have hy14 : y1 ≠ y4 := by
    intro h
    have := T.vertex_injective h
    simp [y1, y4] at this
  have hy23 : y2 ≠ y3 := by
    intro h
    have := T.vertex_injective h
    simp [y2, y3] at this
  have hy24 : y2 ≠ y4 := by
    intro h
    have := T.vertex_injective h
    simp [y2, y4] at this
  have hy34 : y3 ≠ y4 := by
    intro h
    have := T.vertex_injective h
    simp [y3, y4] at this
  have ha1ends : G.ends a1 = s(y1, y2) := by
    simpa [a1, r1, y1, y2, hNheight] using N.trunk_edge_ends r1 (by simp [r1])
      (by simp [r1, hNheight])
  have ha2ends : G.ends a2 = s(y2, y3) := by
    simpa [a2, r2, y2, y3, hNheight] using N.trunk_edge_ends r2 (by simp [r2])
      (by simp [r2, hNheight])
  have ha3ends : G.ends a3 = s(y3, y4) := by
    simpa [a3, r3, y3, y4, hNheight] using N.trunk_edge_ends r3 (by simp [r3])
      (by simp [r3, hNheight])
  have hqends : G.ends q = s(y4, y0) := by
    have hlast : N.lastIndex = ⟨4, by have := N.height_upper; omega⟩ := by
      apply Fin.ext
      have := N.lastIndex_height
      simp
      rw [hNheight] at this
      omega
    simpa [q, y0, y4, hlast] using N.closing_ends
  have hproper : IsProperEdgeColoring G phi := N.global.1.2.2.2.1
  have missing_excludes {c : Fin k} {v : V} {f : E}
      (hc : c ∈ MissingColors G phi v) (hinc : Incident G v f) :
      phi f ≠ some c := by
    intro hfc
    have hp : c ∈ PresentColors G phi v := by
      simp [PresentColors]
      exact ⟨f, hinc, hfc⟩
    have hn : c ∉ PresentColors G phi v := by
      simpa [MissingColors] using hc
    exact hn hp
  have edge_color_of_closing_support (f : E)
      (hf : Sum.inr f ∈ N.closingPath.support) :
      phi f = some N.alpha ∨ phi f = some N.beta := by
    obtain ⟨i, hi, hile⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hf
    have hilt : i < N.closingPath.length := by
      by_contra hn
      have hil : N.closingPath.length ≤ i := by omega
      have hend := N.closingPath.getVert_of_length_le (i := i) hil
      rw [hi] at hend
      simp at hend
    have hadj := N.closingPath.adj_getVert_succ hilt
    rw [hi] at hadj
    cases hz : N.closingPath.getVert (i + 1) with
    | inl v =>
        rw [hz] at hadj
        have hdata : Incident G v f ∧
            (phi f = some N.alpha ∨ phi f = some N.beta) := by
          simpa [TwoColorIncidenceGraph] using hadj
        exact hdata.2
    | inr e =>
        rw [hz] at hadj
        simp [TwoColorIncidenceGraph] at hadj
  have ha1support : Sum.inr a1 ∈ N.closingPath.support := by
    apply (N.closingPath_edges a1).2
    exact Or.inr ⟨r1, by simp [r1], by simp [r1, hNheight], rfl⟩
  have ha2support : Sum.inr a2 ∈ N.closingPath.support := by
    apply (N.closingPath_edges a2).2
    exact Or.inr ⟨r2, by simp [r2], by simp [r2, hNheight], rfl⟩
  have ha3support : Sum.inr a3 ∈ N.closingPath.support := by
    apply (N.closingPath_edges a3).2
    exact Or.inr ⟨r3, by simp [r3], by simp [r3, hNheight], rfl⟩
  have hqsupport : Sum.inr q ∈ N.closingPath.support := by
    exact (N.closingPath_edges q).2 (Or.inl rfl)
  have ha1color : phi a1 = some N.alpha := by
    rcases edge_color_of_closing_support a1 ha1support with h | h
    · exact h
    · have hbmiss : N.beta ∈ MissingColors G phi y1 := by
        simpa [y1] using N.beta_missing
      have hinc : Incident G y1 a1 := by
        unfold Incident
        rw [ha1ends]
        simp [Sym2.mem_iff]
      exact False.elim ((missing_excludes hbmiss hinc) h)
  have ha1a2 : AdjacentEdges G a1 a2 := by
    refine ⟨y2, ?_, ?_⟩ <;> unfold Incident
    · rw [ha1ends]
      simp [Sym2.mem_iff]
    · rw [ha2ends]
      simp [Sym2.mem_iff]
  have ha12ne : a1 ≠ a2 := by
    intro h
    exact (show r1 ≠ r2 by simp [r1, r2]) (T.edge_injective (by simpa [a1, a2] using h))
  have ha2color : phi a2 = some N.beta := by
    rcases edge_color_of_closing_support a2 ha2support with h | h
    · exact False.elim ((hproper ha12ne ha1a2 ha1color) h)
    · exact h
  have ha2a3 : AdjacentEdges G a2 a3 := by
    refine ⟨y3, ?_, ?_⟩ <;> unfold Incident
    · rw [ha2ends]
      simp [Sym2.mem_iff]
    · rw [ha3ends]
      simp [Sym2.mem_iff]
  have ha23ne : a2 ≠ a3 := by
    intro h
    exact (show r2 ≠ r3 by simp [r2, r3]) (T.edge_injective (by simpa [a2, a3] using h))
  have ha3color : phi a3 = some N.alpha := by
    rcases edge_color_of_closing_support a3 ha3support with h | h
    · exact h
    · exact False.elim ((hproper ha23ne ha2a3 ha2color) h)
  have ha3q : AdjacentEdges G a3 q := by
    refine ⟨y4, ?_, ?_⟩ <;> unfold Incident
    · rw [ha3ends]
      simp [Sym2.mem_iff]
    · rw [hqends]
      simp [Sym2.mem_iff]
  have ha3qne : a3 ≠ q := by
    intro h
    have hpairs : s(y3, y4) = s(y4, y0) := by
      rw [← ha3ends, h, hqends]
    rcases Sym2.eq_iff.mp hpairs with hd | hs
    · exact hy34 hd.1
    · exact hy03 hs.1.symm
  have hqcolor : phi q = some N.beta := by
    rcases edge_color_of_closing_support q hqsupport with h | h
    · exact False.elim ((hproper ha3qne ha3q ha3color) h)
    · exact h
  have hgamma_beta : gamma ≠ N.beta := by
    intro h
    have hinc : Incident G y1 f1 := by
      unfold Incident
      rw [hf1ends]
      simp [y1, Sym2.mem_iff]
    exact (missing_excludes (by simpa [y1] using N.beta_missing) hinc)
      (by simpa [h] using hf1color)
  have hf1ends' : G.ends f1 = s(y1, v1) := by simpa [y1] using hf1ends
  have hf2ends' : G.ends f2 = s(y4, v2) := by simpa [y4] using hf2ends
  have hv10' : v1 ≠ y0 := by simpa [y0] using hv10
  have hv11' : v1 ≠ y1 := by simpa [y1] using hv11
  have hv12' : v1 ≠ y2 := by simpa [y2] using hv12
  have hv13' : v1 ≠ y3 := by simpa [y3] using hv13
  have hv14' : v1 ≠ y4 := by simpa [y4] using hv14
  have hv20' : v2 ≠ y0 := by simpa [y0] using hv20
  have hv21' : v2 ≠ y1 := by simpa [y1] using hv21
  have hv22' : v2 ≠ y2 := by simpa [y2] using hv22
  have hv23' : v2 ≠ y3 := by simpa [y3] using hv23
  have hv24' : v2 ≠ y4 := by simpa [y4] using hv24
  have hf12ne : f1 ≠ f2 := by
    intro h
    have hpairs : s(y1, v1) = s(y4, v2) := by
      rw [← hf1ends', h, hf2ends']
    rcases Sym2.eq_iff.mp hpairs with hd | hs
    · exact hy14 hd.1
    · exact hv21' hs.1.symm
  have hv12ne : v1 ≠ v2 := by
    intro h
    have hadj : AdjacentEdges G f1 f2 := by
      refine ⟨v1, ?_, ?_⟩ <;> unfold Incident
      · rw [hf1ends']
        simp [Sym2.mem_iff]
      · rw [hf2ends', ← h]
        simp [Sym2.mem_iff]
    exact (hproper hf12ne hadj hf1color) hf2color
  have hqf1 : q ≠ f1 := by
    intro h
    have hc : some N.beta = some gamma := by rw [← hqcolor, h, hf1color]
    exact hgamma_beta (Option.some.inj hc).symm
  have hqf2 : q ≠ f2 := by
    intro h
    have hc : some N.beta = some gamma := by rw [← hqcolor, h, hf2color]
    exact hgamma_beta (Option.some.inj hc).symm
  obtain ⟨p1, hp1, hp1support, hp1div, hp1vertices, hp1bound⟩ :=
    ScheideKempePathHeightBound G k e0 phi T N.global gamma N.beta
      hgamma N.beta_missing
  have hp1bound' : p1.length / 2 + 1 ≤ 5 := by
    simpa [hGheight] using hp1bound
  let H1 := TwoColorIncidenceGraph G phi gamma N.beta
  let C1 := TwoColorComponent G phi gamma N.beta (Sum.inl y0)
  have hp1support' : {z | z ∈ p1.support} = C1 := by
    simpa [C1, y0] using hp1support
  have hC1root : Sum.inl y0 ∈ C1 := by
    change Sum.inl y0 ∈ H1.connectedComponentMk (Sum.inl y0)
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
  have C1_of_adj {x z : Sum V E} (hx : x ∈ C1) (hxz : H1.Adj x z) : z ∈ C1 := by
    change H1.connectedComponentMk x = H1.connectedComponentMk (Sum.inl y0) at hx
    change H1.connectedComponentMk z = H1.connectedComponentMk (Sum.inl y0)
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxz).symm.trans hx
  have support_of_C1 {z : Sum V E} (hz : z ∈ C1) : z ∈ p1.support := by
    change z ∈ {w | w ∈ p1.support}
    rw [hp1support']
    exact hz
  have hy0p1 : Sum.inl y0 ∈ p1.support := support_of_C1 hC1root
  have hqadj0 : H1.Adj (Sum.inl y0) (Sum.inr q) := by
    simp [H1, TwoColorIncidenceGraph, Incident, hqends, hqcolor, Sym2.mem_iff]
  have hqC1 : Sum.inr q ∈ C1 := C1_of_adj hC1root hqadj0
  have hqp1 : Sum.inr q ∈ p1.support := support_of_C1 hqC1
  have hqadj4 : H1.Adj (Sum.inr q) (Sum.inl y4) := by
    simp [H1, TwoColorIncidenceGraph, Incident, hqends, hqcolor, Sym2.mem_iff]
  have hy4C1 : Sum.inl y4 ∈ C1 := C1_of_adj hqC1 hqadj4
  have hy4p1 : Sum.inl y4 ∈ p1.support := support_of_C1 hy4C1
  have hf2adj4 : H1.Adj (Sum.inl y4) (Sum.inr f2) := by
    simp [H1, TwoColorIncidenceGraph, Incident, hf2ends', hf2color, Sym2.mem_iff]
  have hf2C1 : Sum.inr f2 ∈ C1 := C1_of_adj hy4C1 hf2adj4
  have hf2p1 : Sum.inr f2 ∈ p1.support := support_of_C1 hf2C1
  have hf2adjv2 : H1.Adj (Sum.inr f2) (Sum.inl v2) := by
    simp [H1, TwoColorIncidenceGraph, Incident, hf2ends', hf2color, Sym2.mem_iff]
  have hv2C1 : Sum.inl v2 ∈ C1 := C1_of_adj hf2C1 hf2adjv2
  have hv2p1 : Sum.inl v2 ∈ p1.support := support_of_C1 hv2C1
  have hy1p1 : Sum.inl y1 ∈ p1.support := by
    simpa [y1] using p1.end_mem_support
  have hy1C1 : Sum.inl y1 ∈ C1 := by
    rw [← hp1support']
    exact hy1p1
  have hf1adj1 : H1.Adj (Sum.inl y1) (Sum.inr f1) := by
    simp [H1, TwoColorIncidenceGraph, Incident, hf1ends', hf1color, Sym2.mem_iff]
  have hf1C1 : Sum.inr f1 ∈ C1 := C1_of_adj hy1C1 hf1adj1
  have hf1p1 : Sum.inr f1 ∈ p1.support := support_of_C1 hf1C1
  have hf1adjv1 : H1.Adj (Sum.inr f1) (Sum.inl v1) := by
    simp [H1, TwoColorIncidenceGraph, Incident, hf1ends', hf1color, Sym2.mem_iff]
  have hv1C1 : Sum.inl v1 ∈ C1 := C1_of_adj hf1C1 hf1adjv1
  have hv1p1 : Sum.inl v1 ∈ p1.support := support_of_C1 hv1C1
  let K8 : Finset (Sum V E) :=
    {Sum.inl y0, Sum.inl y1, Sum.inl y4, Sum.inl v1, Sum.inl v2,
      Sum.inr q, Sum.inr f1, Sum.inr f2}
  have hK8card : K8.card = 8 := by
    simp [K8, hy01, hy04, hy14, hv10', hv11', hv14', hv20', hv21', hv24',
      hv12ne, hqf1, hqf2, hf12ne, Ne.symm hy01, Ne.symm hy04, Ne.symm hy14,
      Ne.symm hv10', Ne.symm hv11', Ne.symm hv14', Ne.symm hv20',
      Ne.symm hv21', Ne.symm hv24', Ne.symm hv12ne, Ne.symm hqf1,
      Ne.symm hqf2, Ne.symm hf12ne]
  have hK8sub : K8 ⊆ p1.support.toFinset := by
    intro z hz
    simp only [K8, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa using hy0p1
    · simpa using hy1p1
    · simpa using hy4p1
    · simpa using hv1p1
    · simpa using hv2p1
    · simpa using hqp1
    · simpa using hf1p1
    · simpa using hf2p1
  have hp1lower : 7 ≤ p1.length := by
    have hc := Finset.card_le_card hK8sub
    rw [hK8card, List.toFinset_card_of_nodup hp1.support_nodup,
      SimpleGraph.Walk.length_support] at hc
    omega
  have hp1length : p1.length = 8 := by
    rcases hp1div with ⟨d, hd⟩
    omega
  obtain ⟨iv2, hiv2, hiv2le⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hv2p1
  have hiv20 : iv2 ≠ 0 := by
    intro h
    have hv : (Sum.inl v2 : Sum V E) = Sum.inl y0 := by
      rw [← hiv2, h, p1.getVert_zero]
    exact hv20' (Sum.inl_injective hv)
  have hiv2lt : iv2 < p1.length := by
    by_contra h
    have hil : p1.length ≤ iv2 := by omega
    have hvend := p1.getVert_of_length_le hil
    have hv : (Sum.inl v2 : Sum V E) = Sum.inl y1 := by
      rw [hiv2] at hvend
      simpa [y1] using hvend
    exact hv21' (Sum.inl_injective hv)
  have hprevAdj : H1.Adj (Sum.inl v2) (p1.getVert (iv2 - 1)) := by
    have h := (p1.adj_getVert_succ (i := iv2 - 1) (by omega)).symm
    have heq : iv2 - 1 + 1 = iv2 := by omega
    rw [heq, hiv2] at h
    exact h
  have hnextAdj : H1.Adj (Sum.inl v2) (p1.getVert (iv2 + 1)) := by
    have h := p1.adj_getVert_succ hiv2lt
    rw [hiv2] at h
    exact h
  have hprevnext : p1.getVert (iv2 - 1) ≠ p1.getVert (iv2 + 1) := by
    intro h
    have hi := hp1.getVert_injOn
      (show iv2 - 1 ≤ p1.length by omega)
      (show iv2 + 1 ≤ p1.length by omega) h
    omega
  obtain ⟨b, hbAdj, hbp1, hbf2⟩ : ∃ b : E,
      H1.Adj (Sum.inl v2) (Sum.inr b) ∧ Sum.inr b ∈ p1.support ∧ b ≠ f2 := by
    by_cases hp : p1.getVert (iv2 - 1) = Sum.inr f2
    · cases hn : p1.getVert (iv2 + 1) with
      | inl w =>
          rw [hn] at hnextAdj
          simp [H1, TwoColorIncidenceGraph] at hnextAdj
      | inr b =>
          rw [hn] at hnextAdj
          refine ⟨b, hnextAdj, ?_, ?_⟩
          · rw [← hn]
            exact p1.getVert_mem_support (iv2 + 1)
          · intro h
            apply hprevnext
            rw [hp, hn, h]
    · cases hn : p1.getVert (iv2 - 1) with
      | inl w =>
          rw [hn] at hprevAdj
          simp [H1, TwoColorIncidenceGraph] at hprevAdj
      | inr b =>
          rw [hn] at hprevAdj
          refine ⟨b, hprevAdj, ?_, ?_⟩
          · rw [← hn]
            exact p1.getVert_mem_support (iv2 - 1)
          · intro h
            exact hp (by rw [hn, h])
  have hbinc : Incident G v2 b := by
    simpa [H1, TwoColorIncidenceGraph] using hbAdj |>.1
  have hf2inc : Incident G v2 f2 := by
    unfold Incident
    rw [hf2ends']
    simp [Sym2.mem_iff]
  have hfbadj : AdjacentEdges G f2 b := ⟨v2, hf2inc, hbinc⟩
  have hbcolor : phi b = some N.beta := by
    have hc : phi b = some gamma ∨ phi b = some N.beta := by
      simpa [H1, TwoColorIncidenceGraph] using hbAdj |>.2
    exact hc.resolve_left (hproper hbf2.symm hfbadj hf2color)
  obtain ⟨w, hbends⟩ := Sym2.mem_iff_exists.mp hbinc
  have hbq : b ≠ q := by
    intro h
    have hpairs : s(v2, w) = s(y4, y0) := by
      rw [← hbends, h, hqends]
    rcases Sym2.eq_iff.mp hpairs with hd | hs
    · exact hv24' hd.1
    · exact hv20' hs.1
  have hbf1 : b ≠ f1 := by
    intro h
    have hc : some N.beta = some gamma := by rw [← hbcolor, h, hf1color]
    exact hgamma_beta (Option.some.inj hc).symm
  let K9 : Finset (Sum V E) := insert (Sum.inr b) K8
  have hK9card : K9.card = 9 := by
    rw [Finset.card_insert_of_notMem]
    · rw [hK8card]
    · simp [K8, hbf2, hbf1, hbq]
  have hK9sub : K9 ⊆ p1.support.toFinset := by
    intro z hz
    simp only [K9, Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · simpa using hbp1
    · exact hK8sub hz
  have hp1card : p1.support.toFinset.card = 9 := by
    rw [List.toFinset_card_of_nodup hp1.support_nodup,
      SimpleGraph.Walk.length_support, hp1length]
  have hK9eq : K9 = p1.support.toFinset := by
    exact Finset.eq_of_subset_of_card_le hK9sub (by rw [hK9card, hp1card])
  have hbAdjw : H1.Adj (Sum.inr b) (Sum.inl w) := by
    simp [H1, TwoColorIncidenceGraph, Incident, hbends, hbcolor, Sym2.mem_iff]
  have hbC1 : Sum.inr b ∈ C1 := by
    rw [← hp1support']
    exact hbp1
  have hwC1 : Sum.inl w ∈ C1 := C1_of_adj hbC1 hbAdjw
  have hwp1 : Sum.inl w ∈ p1.support := support_of_C1 hwC1
  have hwcases : w = y0 ∨ w = y1 ∨ w = y4 ∨ w = v1 ∨ w = v2 := by
    have hwfin : Sum.inl w ∈ K9 := by
      rw [hK9eq]
      simpa using hwp1
    simpa [K9, K8] using hwfin
  have hwy0 : w ≠ y0 := by
    intro h
    have hadj : AdjacentEdges G b q := ⟨y0, by
      unfold Incident
      rw [hbends, h]
      simp [Sym2.mem_iff], by
      unfold Incident
      rw [hqends]
      simp [Sym2.mem_iff]⟩
    exact (hproper hbq hadj hbcolor) hqcolor
  have hwy1 : w ≠ y1 := by
    intro h
    have hinc : Incident G y1 b := by
      unfold Incident
      rw [hbends, h]
      simp [Sym2.mem_iff]
    exact (missing_excludes (by simpa [y1] using N.beta_missing) hinc) hbcolor
  have hwy4 : w ≠ y4 := by
    intro h
    have hadj : AdjacentEdges G b q := ⟨y4, by
      unfold Incident
      rw [hbends, h]
      simp [Sym2.mem_iff], by
      unfold Incident
      rw [hqends]
      simp [Sym2.mem_iff]⟩
    exact (hproper hbq hadj hbcolor) hqcolor
  have hwv2 : w ≠ v2 := by
    intro h
    exact G.loopless b v2 (by simpa [h] using hbends)
  have hwv1 : w = v1 := by
    rcases hwcases with h | h | h | h | h
    · exact False.elim (hwy0 h)
    · exact False.elim (hwy1 h)
    · exact False.elim (hwy4 h)
    · exact h
    · exact False.elim (hwv2 h)
  have hbends' : G.ends b = s(v1, v2) := by
    rw [hbends, hwv1, Sym2.eq_swap]
  have hfixed : FixedPairMaximalTashkinovTree G e0 phi T := by
    refine ⟨N.global.2.1, ?_⟩
    intro S hS hsub
    have hk : ChromaticIndex G - 1 = k := by
      have hchrom := N.global.1.2.1
      omega
    have hScard : (TreeSequenceVertexSet S).card ≤ TashkinovOrder G := by
      unfold TashkinovOrder
      dsimp only
      apply Finset.le_max'
      apply Finset.mem_insert_of_mem
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ _))
      · rw [hk]
        exact ⟨e0, phi, S, N.global.1, hS, rfl⟩
    have hcard : (TreeSequenceVertexSet S).card ≤
        (TreeSequenceVertexSet T).card := by
      rw [N.global.2.2]
      exact hScard
    have heq : TreeSequenceVertexSet T = TreeSequenceVertexSet S :=
      Finset.eq_of_subset_of_card_le hsub hcard
    exact heq.symm.subset
  let i0 : Fin (T.length + 1) := ⟨0, by omega⟩
  let i1 : Fin (T.length + 1) := ⟨1, by have := N.height_upper; omega⟩
  obtain ⟨hab, pmax, hpmax, hpmaxsupport, hpmaxdiv, hpmaxvertices, hchange⟩ :=
    ScheideMaximalKempePath G k e0 phi T T N.global.1 hfixed N.global.2.1
      i0 i1 (by simp [i0, i1]) N.alpha N.beta
      (by simpa [i0] using N.alpha_missing)
      (by simpa [i1] using N.beta_missing)
  have hunused : TreeColorUnusedThrough phi T N.alpha i1 := by
    intro r hr hrj
    simp [i1] at hrj
    omega
  have hchangedata := hchange hunused
  let C0 := TwoColorComponent G phi N.alpha N.beta (Sum.inl y0)
  let H0 := TwoColorIncidenceGraph G phi N.alpha N.beta
  have hpmaxsupport' : {z | z ∈ pmax.support} = C0 := by
    simpa [C0, i0, y0] using hpmaxsupport
  have hC0root : Sum.inl y0 ∈ C0 := by
    change Sum.inl y0 ∈ H0.connectedComponentMk (Sum.inl y0)
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
  have C0_of_adj {x z : Sum V E} (hx : x ∈ C0) (hxz : H0.Adj x z) : z ∈ C0 := by
    change H0.connectedComponentMk x = H0.connectedComponentMk (Sum.inl y0) at hx
    change H0.connectedComponentMk z = H0.connectedComponentMk (Sum.inl y0)
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxz).symm.trans hx
  obtain ⟨p0, hp0, hp0support, hp0div, hp0vertices, hp0bound⟩ :=
    ScheideKempePathHeightBound G k e0 phi T N.global N.alpha N.beta
      N.alpha_missing N.beta_missing
  have hp0support' : {z | z ∈ p0.support} = C0 := by
    simpa [C0, y0] using hp0support
  have support_of_C0 {z : Sum V E} (hz : z ∈ C0) : z ∈ p0.support := by
    change z ∈ {w | w ∈ p0.support}
    rw [hp0support']
    exact hz
  have hq0adj : H0.Adj (Sum.inl y0) (Sum.inr q) := by
    simp [H0, TwoColorIncidenceGraph, Incident, hqends, hqcolor, Sym2.mem_iff]
  have hqC0 : Sum.inr q ∈ C0 := C0_of_adj hC0root hq0adj
  have hq4adj : H0.Adj (Sum.inr q) (Sum.inl y4) := by
    simp [H0, TwoColorIncidenceGraph, Incident, hqends, hqcolor, Sym2.mem_iff]
  have hy4C0 : Sum.inl y4 ∈ C0 := C0_of_adj hqC0 hq4adj
  have ha34adj : H0.Adj (Sum.inl y4) (Sum.inr a3) := by
    simp [H0, TwoColorIncidenceGraph, Incident, ha3ends, ha3color, Sym2.mem_iff]
  have ha3C0 : Sum.inr a3 ∈ C0 := C0_of_adj hy4C0 ha34adj
  have ha33adj : H0.Adj (Sum.inr a3) (Sum.inl y3) := by
    simp [H0, TwoColorIncidenceGraph, Incident, ha3ends, ha3color, Sym2.mem_iff]
  have hy3C0 : Sum.inl y3 ∈ C0 := C0_of_adj ha3C0 ha33adj
  have ha23adj : H0.Adj (Sum.inl y3) (Sum.inr a2) := by
    simp [H0, TwoColorIncidenceGraph, Incident, ha2ends, ha2color, Sym2.mem_iff]
  have ha2C0 : Sum.inr a2 ∈ C0 := C0_of_adj hy3C0 ha23adj
  have ha22adj : H0.Adj (Sum.inr a2) (Sum.inl y2) := by
    simp [H0, TwoColorIncidenceGraph, Incident, ha2ends, ha2color, Sym2.mem_iff]
  have hy2C0 : Sum.inl y2 ∈ C0 := C0_of_adj ha2C0 ha22adj
  have ha12adj : H0.Adj (Sum.inl y2) (Sum.inr a1) := by
    simp [H0, TwoColorIncidenceGraph, Incident, ha1ends, ha1color, Sym2.mem_iff]
  have ha1C0 : Sum.inr a1 ∈ C0 := C0_of_adj hy2C0 ha12adj
  have ha11adj : H0.Adj (Sum.inr a1) (Sum.inl y1) := by
    simp [H0, TwoColorIncidenceGraph, Incident, ha1ends, ha1color, Sym2.mem_iff]
  have hy1C0 : Sum.inl y1 ∈ C0 := C0_of_adj ha1C0 ha11adj
  have ha13ne : a1 ≠ a3 := by
    intro h
    exact (show r1 ≠ r3 by simp [r1, r3])
      (T.edge_injective (by simpa [a1, a3] using h))
  have hqa1 : q ≠ a1 := by
    intro h
    have hc : some N.beta = some N.alpha := by rw [← hqcolor, h, ha1color]
    exact hab (Option.some.inj hc).symm
  have hqa3 : q ≠ a3 := by
    intro h
    have hc : some N.beta = some N.alpha := by rw [← hqcolor, h, ha3color]
    exact hab (Option.some.inj hc).symm
  have hqa2 : q ≠ a2 := by
    intro h
    have hpairs : s(y4, y0) = s(y2, y3) := by
      rw [← hqends, h, ha2ends]
    rcases Sym2.eq_iff.mp hpairs with hd | hs
    · exact hy24 hd.1.symm
    · exact hy34 hs.1.symm
  let K0 : Finset (Sum V E) :=
    {Sum.inl y0, Sum.inl y1, Sum.inl y2, Sum.inl y3, Sum.inl y4,
      Sum.inr q, Sum.inr a1, Sum.inr a2, Sum.inr a3}
  have hK0card : K0.card = 9 := by
    simp [K0, hy01, hy02, hy03, hy04, hy12, hy13, hy14, hy23, hy24, hy34,
      ha12ne, ha13ne, ha23ne, hqa1, hqa2, hqa3, Ne.symm hy01, Ne.symm hy02,
      Ne.symm hy03, Ne.symm hy04, Ne.symm hy12, Ne.symm hy13, Ne.symm hy14,
      Ne.symm hy23, Ne.symm hy24, Ne.symm hy34, Ne.symm ha12ne,
      Ne.symm ha13ne, Ne.symm ha23ne, Ne.symm hqa1, Ne.symm hqa2,
      Ne.symm hqa3]
  have hK0sub : K0 ⊆ p0.support.toFinset := by
    intro z hz
    simp only [K0, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa using support_of_C0 hC0root
    · simpa using support_of_C0 hy1C0
    · simpa using support_of_C0 hy2C0
    · simpa using support_of_C0 hy3C0
    · simpa using support_of_C0 hy4C0
    · simpa using support_of_C0 hqC0
    · simpa using support_of_C0 ha1C0
    · simpa using support_of_C0 ha2C0
    · simpa using support_of_C0 ha3C0
  have hp0lower : 8 ≤ p0.length := by
    have hc := Finset.card_le_card hK0sub
    rw [hK0card, List.toFinset_card_of_nodup hp0.support_nodup,
      SimpleGraph.Walk.length_support] at hc
    omega
  have hp0bound' : p0.length / 2 + 1 ≤ 5 := by
    simpa [hGheight] using hp0bound
  have hp0length : p0.length = 8 := by
    rcases hp0div with ⟨d, hd⟩
    omega
  have hp0card : p0.support.toFinset.card = 9 := by
    rw [List.toFinset_card_of_nodup hp0.support_nodup,
      SimpleGraph.Walk.length_support, hp0length]
  have hK0eq : K0 = p0.support.toFinset :=
    Finset.eq_of_subset_of_card_le hK0sub (by rw [hK0card, hp0card])
  have hv1notC0 : Sum.inl v1 ∉ C0 := by
    intro hv
    have hvp := support_of_C0 hv
    have hvK : Sum.inl v1 ∈ K0 := by
      rw [hK0eq]
      simpa using hvp
    simp [K0, hv10', hv11', hv12', hv13', hv14'] at hvK
  have hv2notC0 : Sum.inl v2 ∉ C0 := by
    intro hv
    have hvp := support_of_C0 hv
    have hvK : Sum.inl v2 ∈ K0 := by
      rw [hK0eq]
      simpa using hvp
    simp [K0, hv20', hv21', hv22', hv23', hv24'] at hvK
  have hgamma_alpha : gamma ≠ N.alpha := by
    intro h
    have hf1adj : H0.Adj (Sum.inl y1) (Sum.inr f1) := by
      simp [H0, TwoColorIncidenceGraph, Incident, hf1ends', hf1color, h,
        Sym2.mem_iff]
    have hf1C : Sum.inr f1 ∈ C0 := C0_of_adj hy1C0 hf1adj
    have hv1adj : H0.Adj (Sum.inr f1) (Sum.inl v1) := by
      simp [H0, TwoColorIncidenceGraph, Incident, hf1ends', hf1color, h,
        Sym2.mem_iff]
    exact hv1notC0 (C0_of_adj hf1C hv1adj)
  let phi' := TwoColorComponentSwap G phi N.alpha N.beta (Sum.inl y0)
  have hproper' : IsProperEdgeColoring G phi' := by
    simpa [phi', y0, i0] using hchangedata.1
  have hone' : IsOneEdgeUncolored phi' e0 := by
    simpa [phi', y0, i0] using hchangedata.2.1
  have hTash' : TashkinovTree G e0 phi' T := by
    simpa [phi', y0, i0] using hchangedata.2.2
  have hglobal' : GlobalMaximumTriple G k e0 phi' T := by
    refine ⟨⟨N.global.1.1, N.global.1.2.1, N.global.1.2.2.1,
      hproper', hone'⟩, hTash', N.global.2.2⟩
  have hgamma_fixed (e : E) : phi' e = some gamma ↔ phi e = some gamma := by
    by_cases heC : Sum.inr e ∈ C0
    · by_cases hea : phi e = some N.alpha
      · simp [phi', TwoColorComponentSwap, C0, heC, hea, hgamma_alpha,
          hgamma_beta, Ne.symm hgamma_alpha, Ne.symm hgamma_beta]
      · by_cases heb : phi e = some N.beta
        · simp [phi', TwoColorComponentSwap, C0, heC, hea, heb,
            hab, Ne.symm hab, hgamma_alpha, hgamma_beta, Ne.symm hgamma_alpha,
            Ne.symm hgamma_beta]
        · simp [phi', TwoColorComponentSwap, C0, heC, hea, heb]
    · simp [phi', TwoColorComponentSwap, C0, heC]
  have hf1color' : phi' f1 = some gamma := (hgamma_fixed f1).2 hf1color
  have hf2color' : phi' f2 = some gamma := (hgamma_fixed f2).2 hf2color
  have hqcolor' : phi' q = some N.alpha := by
    simp [phi', TwoColorComponentSwap, C0, hqC0, hqcolor, hab]
  have hgamma' : gamma ∈ MissingColors G phi' y0 := by
    have hn : gamma ∉ PresentColors G phi' y0 := by
      intro hp
      simp [PresentColors] at hp
      obtain ⟨e, heinc, hecolor⟩ := hp
      have hpold : gamma ∈ PresentColors G phi y0 := by
        simp [PresentColors]
        exact ⟨e, heinc, (hgamma_fixed e).1 hecolor⟩
      have hnold : gamma ∉ PresentColors G phi y0 := by
        simpa [y0, MissingColors] using hgamma
      exact hnold hpold
    simpa [MissingColors] using hn
  have halpha' : N.alpha ∈ MissingColors G phi' y1 := by
    have hn : N.alpha ∉ PresentColors G phi' y1 := by
      intro hp
      simp [PresentColors] at hp
      obtain ⟨e, heinc, hecolor⟩ := hp
      by_cases heC : Sum.inr e ∈ C0
      · by_cases hea : phi e = some N.alpha
        · have : phi' e = some N.beta := by
            simp [phi', TwoColorComponentSwap, C0, heC, hea, hab]
          exact hab (Option.some.inj (this.symm.trans hecolor)).symm
        · by_cases heb : phi e = some N.beta
          · have hbmiss : N.beta ∈ MissingColors G phi y1 := by
              simpa [y1] using N.beta_missing
            exact (missing_excludes hbmiss heinc) heb
          · have hfix : phi' e = phi e := by
              simp [phi', TwoColorComponentSwap, C0, heC, hea, heb]
            exact hea (hfix.symm.trans hecolor)
      · have heold : phi e = some N.alpha := by
          simpa [phi', TwoColorComponentSwap, C0, heC] using hecolor
        have hadj : H0.Adj (Sum.inl y1) (Sum.inr e) := by
          simp [H0, TwoColorIncidenceGraph, heinc, heold]
        exact heC (C0_of_adj hy1C0 hadj)
    rw [MissingColors, Finset.mem_sdiff]
    exact ⟨Finset.mem_univ _, hn⟩
  have missing_excludes' {c : Fin k} {v : V} {f : E}
      (hc : c ∈ MissingColors G phi' v) (hinc : Incident G v f) :
      phi' f ≠ some c := by
    intro hfc
    have hp : c ∈ PresentColors G phi' v := by
      simp [PresentColors]
      exact ⟨f, hinc, hfc⟩
    have hn : c ∉ PresentColors G phi' v := by
      simpa [MissingColors] using hc
    exact hn hp
  obtain ⟨p2, hp2, hp2support, hp2div, hp2vertices, hp2bound⟩ :=
    ScheideKempePathHeightBound G k e0 phi' T hglobal' gamma N.alpha
      (by simpa [y0] using hgamma') (by simpa [y1] using halpha')
  have hp2bound' : p2.length / 2 + 1 ≤ 5 := by
    simpa [hGheight] using hp2bound
  let H2 := TwoColorIncidenceGraph G phi' gamma N.alpha
  let C2 := TwoColorComponent G phi' gamma N.alpha (Sum.inl y0)
  have hp2support' : {z | z ∈ p2.support} = C2 := by
    simpa [C2, y0] using hp2support
  have hC2root : Sum.inl y0 ∈ C2 := by
    change Sum.inl y0 ∈ H2.connectedComponentMk (Sum.inl y0)
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
  have C2_of_adj {x z : Sum V E} (hx : x ∈ C2) (hxz : H2.Adj x z) : z ∈ C2 := by
    change H2.connectedComponentMk x = H2.connectedComponentMk (Sum.inl y0) at hx
    change H2.connectedComponentMk z = H2.connectedComponentMk (Sum.inl y0)
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxz).symm.trans hx
  have support_of_C2 {z : Sum V E} (hz : z ∈ C2) : z ∈ p2.support := by
    change z ∈ {w | w ∈ p2.support}
    rw [hp2support']
    exact hz
  have hy0p2 : Sum.inl y0 ∈ p2.support := support_of_C2 hC2root
  have hqadj02 : H2.Adj (Sum.inl y0) (Sum.inr q) := by
    simp [H2, TwoColorIncidenceGraph, Incident, hqends, hqcolor', Sym2.mem_iff]
  have hqC2 : Sum.inr q ∈ C2 := C2_of_adj hC2root hqadj02
  have hqp2 : Sum.inr q ∈ p2.support := support_of_C2 hqC2
  have hqadj42 : H2.Adj (Sum.inr q) (Sum.inl y4) := by
    simp [H2, TwoColorIncidenceGraph, Incident, hqends, hqcolor', Sym2.mem_iff]
  have hy4C2 : Sum.inl y4 ∈ C2 := C2_of_adj hqC2 hqadj42
  have hy4p2 : Sum.inl y4 ∈ p2.support := support_of_C2 hy4C2
  have hf2adj42 : H2.Adj (Sum.inl y4) (Sum.inr f2) := by
    simp [H2, TwoColorIncidenceGraph, Incident, hf2ends', hf2color', Sym2.mem_iff]
  have hf2C2 : Sum.inr f2 ∈ C2 := C2_of_adj hy4C2 hf2adj42
  have hf2p2 : Sum.inr f2 ∈ p2.support := support_of_C2 hf2C2
  have hf2adjv22 : H2.Adj (Sum.inr f2) (Sum.inl v2) := by
    simp [H2, TwoColorIncidenceGraph, Incident, hf2ends', hf2color', Sym2.mem_iff]
  have hv2C2 : Sum.inl v2 ∈ C2 := C2_of_adj hf2C2 hf2adjv22
  have hv2p2 : Sum.inl v2 ∈ p2.support := support_of_C2 hv2C2
  have hy1p2 : Sum.inl y1 ∈ p2.support := by
    simpa [y1] using p2.end_mem_support
  have hy1C2 : Sum.inl y1 ∈ C2 := by
    rw [← hp2support']
    exact hy1p2
  have hf1adj12 : H2.Adj (Sum.inl y1) (Sum.inr f1) := by
    simp [H2, TwoColorIncidenceGraph, Incident, hf1ends', hf1color', Sym2.mem_iff]
  have hf1C2 : Sum.inr f1 ∈ C2 := C2_of_adj hy1C2 hf1adj12
  have hf1p2 : Sum.inr f1 ∈ p2.support := support_of_C2 hf1C2
  have hf1adjv12 : H2.Adj (Sum.inr f1) (Sum.inl v1) := by
    simp [H2, TwoColorIncidenceGraph, Incident, hf1ends', hf1color', Sym2.mem_iff]
  have hv1C2 : Sum.inl v1 ∈ C2 := C2_of_adj hf1C2 hf1adjv12
  have hv1p2 : Sum.inl v1 ∈ p2.support := support_of_C2 hv1C2
  have hK8sub2 : K8 ⊆ p2.support.toFinset := by
    intro z hz
    simp only [K8, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa using hy0p2
    · simpa using hy1p2
    · simpa using hy4p2
    · simpa using hv1p2
    · simpa using hv2p2
    · simpa using hqp2
    · simpa using hf1p2
    · simpa using hf2p2
  have hp2lower : 7 ≤ p2.length := by
    have hc := Finset.card_le_card hK8sub2
    rw [hK8card, List.toFinset_card_of_nodup hp2.support_nodup,
      SimpleGraph.Walk.length_support] at hc
    omega
  have hp2length : p2.length = 8 := by
    rcases hp2div with ⟨d, hd⟩
    omega
  obtain ⟨iv2', hiv2', hiv2le'⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hv2p2
  have hiv20' : iv2' ≠ 0 := by
    intro h
    have hv : (Sum.inl v2 : Sum V E) = Sum.inl y0 := by
      rw [← hiv2', h, p2.getVert_zero]
    exact hv20' (Sum.inl_injective hv)
  have hiv2lt' : iv2' < p2.length := by
    by_contra h
    have hil : p2.length ≤ iv2' := by omega
    have hvend := p2.getVert_of_length_le hil
    have hv : (Sum.inl v2 : Sum V E) = Sum.inl y1 := by
      rw [hiv2'] at hvend
      simpa [y1] using hvend
    exact hv21' (Sum.inl_injective hv)
  have hprevAdj2 : H2.Adj (Sum.inl v2) (p2.getVert (iv2' - 1)) := by
    have h := (p2.adj_getVert_succ (i := iv2' - 1) (by omega)).symm
    have heq : iv2' - 1 + 1 = iv2' := by omega
    rw [heq, hiv2'] at h
    exact h
  have hnextAdj2 : H2.Adj (Sum.inl v2) (p2.getVert (iv2' + 1)) := by
    have h := p2.adj_getVert_succ hiv2lt'
    rw [hiv2'] at h
    exact h
  have hprevnext2 : p2.getVert (iv2' - 1) ≠ p2.getVert (iv2' + 1) := by
    intro h
    have hi := hp2.getVert_injOn
      (show iv2' - 1 ≤ p2.length by omega)
      (show iv2' + 1 ≤ p2.length by omega) h
    omega
  obtain ⟨a, haAdj, hap2, haf2⟩ : ∃ a : E,
      H2.Adj (Sum.inl v2) (Sum.inr a) ∧ Sum.inr a ∈ p2.support ∧ a ≠ f2 := by
    by_cases hp : p2.getVert (iv2' - 1) = Sum.inr f2
    · cases hn : p2.getVert (iv2' + 1) with
      | inl w =>
          rw [hn] at hnextAdj2
          simp [H2, TwoColorIncidenceGraph] at hnextAdj2
      | inr a =>
          rw [hn] at hnextAdj2
          refine ⟨a, hnextAdj2, ?_, ?_⟩
          · rw [← hn]
            exact p2.getVert_mem_support (iv2' + 1)
          · intro h
            apply hprevnext2
            rw [hp, hn, h]
    · cases hn : p2.getVert (iv2' - 1) with
      | inl w =>
          rw [hn] at hprevAdj2
          simp [H2, TwoColorIncidenceGraph] at hprevAdj2
      | inr a =>
          rw [hn] at hprevAdj2
          refine ⟨a, hprevAdj2, ?_, ?_⟩
          · rw [← hn]
            exact p2.getVert_mem_support (iv2' - 1)
          · intro h
            exact hp (by rw [hn, h])
  have hainc : Incident G v2 a := by
    simpa [H2, TwoColorIncidenceGraph] using haAdj |>.1
  have hfaadj : AdjacentEdges G f2 a := ⟨v2, hf2inc, hainc⟩
  have hacolor' : phi' a = some N.alpha := by
    have hc : phi' a = some gamma ∨ phi' a = some N.alpha := by
      simpa [H2, TwoColorIncidenceGraph] using haAdj |>.2
    exact hc.resolve_left (hproper' haf2.symm hfaadj hf2color')
  obtain ⟨x, haends⟩ := Sym2.mem_iff_exists.mp hainc
  have haq : a ≠ q := by
    intro h
    have hpairs : s(v2, x) = s(y4, y0) := by
      rw [← haends, h, hqends]
    rcases Sym2.eq_iff.mp hpairs with hd | hs
    · exact hv24' hd.1
    · exact hv20' hs.1
  have haf1 : a ≠ f1 := by
    intro h
    have hc : some N.alpha = some gamma := by rw [← hacolor', h, hf1color']
    exact hgamma_alpha (Option.some.inj hc).symm
  let K9a : Finset (Sum V E) := insert (Sum.inr a) K8
  have hK9acard : K9a.card = 9 := by
    rw [Finset.card_insert_of_notMem]
    · rw [hK8card]
    · simp [K8, haf2, haf1, haq]
  have hK9asub : K9a ⊆ p2.support.toFinset := by
    intro z hz
    simp only [K9a, Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · simpa using hap2
    · exact hK8sub2 hz
  have hp2card : p2.support.toFinset.card = 9 := by
    rw [List.toFinset_card_of_nodup hp2.support_nodup,
      SimpleGraph.Walk.length_support, hp2length]
  have hK9aeq : K9a = p2.support.toFinset :=
    Finset.eq_of_subset_of_card_le hK9asub (by rw [hK9acard, hp2card])
  have haAdjx : H2.Adj (Sum.inr a) (Sum.inl x) := by
    simp [H2, TwoColorIncidenceGraph, Incident, haends, hacolor', Sym2.mem_iff]
  have haC2 : Sum.inr a ∈ C2 := by
    rw [← hp2support']
    exact hap2
  have hxC2 : Sum.inl x ∈ C2 := C2_of_adj haC2 haAdjx
  have hxp2 : Sum.inl x ∈ p2.support := support_of_C2 hxC2
  have hxcases : x = y0 ∨ x = y1 ∨ x = y4 ∨ x = v1 ∨ x = v2 := by
    have hxfin : Sum.inl x ∈ K9a := by
      rw [hK9aeq]
      simpa using hxp2
    simpa [K9a, K8] using hxfin
  have hxy0 : x ≠ y0 := by
    intro h
    have hadj : AdjacentEdges G a q := ⟨y0, by
      unfold Incident
      rw [haends, h]
      simp [Sym2.mem_iff], by
      unfold Incident
      rw [hqends]
      simp [Sym2.mem_iff]⟩
    exact (hproper' haq hadj hacolor') hqcolor'
  have hxy1 : x ≠ y1 := by
    intro h
    have hinc : Incident G y1 a := by
      unfold Incident
      rw [haends, h]
      simp [Sym2.mem_iff]
    exact (missing_excludes' halpha' hinc) hacolor'
  have hxy4 : x ≠ y4 := by
    intro h
    have hadj : AdjacentEdges G a q := ⟨y4, by
      unfold Incident
      rw [haends, h]
      simp [Sym2.mem_iff], by
      unfold Incident
      rw [hqends]
      simp [Sym2.mem_iff]⟩
    exact (hproper' haq hadj hacolor') hqcolor'
  have hxv2 : x ≠ v2 := by
    intro h
    exact G.loopless a v2 (by simpa [h] using haends)
  have hxv1 : x = v1 := by
    rcases hxcases with h | h | h | h | h
    · exact False.elim (hxy0 h)
    · exact False.elim (hxy1 h)
    · exact False.elim (hxy4 h)
    · exact h
    · exact False.elim (hxv2 h)
  have haends' : G.ends a = s(v1, v2) := by
    rw [haends, hxv1, Sym2.eq_swap]
  have haNotC0 : Sum.inr a ∉ C0 := by
    intro haC
    have habeta : phi a = some N.beta := by
      by_cases haa : phi a = some N.alpha
      · have hs : phi' a = some N.beta := by
          simp [phi', TwoColorComponentSwap, C0, haC, haa, hab]
        exact False.elim (hab (Option.some.inj (hacolor'.symm.trans hs)))
      · by_cases habeta : phi a = some N.beta
        · exact habeta
        · have hfix : phi' a = phi a := by
            simp [phi', TwoColorComponentSwap, C0, haC, haa, habeta]
          exact False.elim (haa (hfix.symm.trans hacolor'))
    have hadj : H0.Adj (Sum.inr a) (Sum.inl v1) := by
      simp [H0, TwoColorIncidenceGraph, Incident, haends', habeta, Sym2.mem_iff]
    exact hv1notC0 (C0_of_adj haC hadj)
  have hacolor : phi a = some N.alpha := by
    simpa [phi', TwoColorComponentSwap, C0, haNotC0] using hacolor'
  have habedge : a ≠ b := by
    intro h
    have hc : some N.alpha = some N.beta := by rw [← hacolor, h, hbcolor]
    exact hab (Option.some.inj hc)
  exact ⟨a, b, haends', hacolor, hbends', hbcolor, habedge⟩
