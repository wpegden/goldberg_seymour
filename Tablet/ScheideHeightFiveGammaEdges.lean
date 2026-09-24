import Tablet.AdjacentEdges
import Tablet.ColoredVertexSetElementary
import Tablet.FixedPairMaximalTashkinovTree
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.NormalGlobalMaximumTriple
import Tablet.PresentColors
import Tablet.ScheideGlobalMaximumFixedPairMaximal
import Tablet.ScheideGlobalMaximumOrder
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
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TwoColorIncidenceGraph

open scoped Sym2

-- [TABLET NODE: ScheideHeightFiveGammaEdges]
theorem ScheideHeightFiveGammaEdges {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hNheight : N.height = 5) (hGheight : ScheideGraphHeight G = 5)
    (gamma : Fin k)
    (hgamma : gamma ∈ MissingColors G phi
      (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩))
    (g : E) (v : V) (hgcolor : phi g = some gamma)
    (hgends :
      G.ends g = s(T.vertex ⟨0, by have := N.height_upper; omega⟩, v) ∨
      G.ends g = s(T.vertex ⟨1, by have := N.height_upper; omega⟩, v) ∨
      G.ends g = s(T.vertex ⟨2, by have := N.height_upper; omega⟩, v) ∨
      G.ends g = s(T.vertex ⟨3, by have := N.height_upper; omega⟩, v) ∨
      G.ends g = s(T.vertex ⟨4, by have := N.height_upper; omega⟩, v))
    (hvT : v ∈ TreeSequenceVertexSet T)
    (hv0 : v ≠ T.vertex ⟨0, by have := N.height_upper; omega⟩)
    (hv1 : v ≠ T.vertex ⟨1, by have := N.height_upper; omega⟩)
    (hv2 : v ≠ T.vertex ⟨2, by have := N.height_upper; omega⟩)
    (hv3 : v ≠ T.vertex ⟨3, by have := N.height_upper; omega⟩)
    (hv4 : v ≠ T.vertex ⟨4, by have := N.height_upper; omega⟩) :
    ∃ (f1 f2 f3 : E) (v1 v2 : V),
      G.ends f1 = s(T.vertex ⟨1, by have := N.height_upper; omega⟩, v1) ∧
      G.ends f2 = s(T.vertex ⟨4, by have := N.height_upper; omega⟩, v2) ∧
      G.ends f3 = s(T.vertex ⟨2, by have := N.height_upper; omega⟩,
        T.vertex ⟨3, by have := N.height_upper; omega⟩) ∧
      phi f1 = some gamma ∧ phi f2 = some gamma ∧
      phi f3 = some gamma ∧
      v1 ∈ TreeSequenceVertexSet T ∧ v2 ∈ TreeSequenceVertexSet T ∧
      v1 ≠ T.vertex ⟨0, by have := N.height_upper; omega⟩ ∧
      v1 ≠ T.vertex ⟨1, by have := N.height_upper; omega⟩ ∧
      v1 ≠ T.vertex ⟨2, by have := N.height_upper; omega⟩ ∧
      v1 ≠ T.vertex ⟨3, by have := N.height_upper; omega⟩ ∧
      v1 ≠ T.vertex ⟨4, by have := N.height_upper; omega⟩ ∧
      v2 ≠ T.vertex ⟨0, by have := N.height_upper; omega⟩ ∧
      v2 ≠ T.vertex ⟨1, by have := N.height_upper; omega⟩ ∧
      v2 ≠ T.vertex ⟨2, by have := N.height_upper; omega⟩ ∧
      v2 ≠ T.vertex ⟨3, by have := N.height_upper; omega⟩ ∧
      v2 ≠ T.vertex ⟨4, by have := N.height_upper; omega⟩ := by
-- BODY
  classical
  let y0 : V := T.vertex ⟨0, by have := N.height_upper; omega⟩
  let y1 : V := T.vertex ⟨1, by have := N.height_upper; omega⟩
  let y2 : V := T.vertex ⟨2, by have := N.height_upper; omega⟩
  let y3 : V := T.vertex ⟨3, by have := N.height_upper; omega⟩
  let y4 : V := T.vertex ⟨4, by have := N.height_upper; omega⟩
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
  have horder := ScheideGlobalMaximumOrder G k e0 phi T N.global
  have helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) :=
    horder.2.2.2.1
  have hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) :=
    horder.2.2.2.2
  have hy0T : y0 ∈ TreeSequenceVertexSet T := by
    simp [y0, TreeSequenceVertexSet]
  have hy1T : y1 ∈ TreeSequenceVertexSet T := by
    simp [y1, TreeSequenceVertexSet]
  have hy2T : y2 ∈ TreeSequenceVertexSet T := by
    simp [y2, TreeSequenceVertexSet]
  have hy3T : y3 ∈ TreeSequenceVertexSet T := by
    simp [y3, TreeSequenceVertexSet]
  have hy4T : y4 ∈ TreeSequenceVertexSet T := by
    simp [y4, TreeSequenceVertexSet]
  have hgamma0 : gamma ∈ MissingColors G phi y0 := by
    simpa [y0] using hgamma
  have gamma_present {x : V} (hxT : x ∈ TreeSequenceVertexSet T)
      (hx0 : x ≠ y0) : gamma ∈ PresentColors G phi x := by
    have hnot : gamma ∉ MissingColors G phi x := by
      intro hxmiss
      have hd := helem hxT hy0T hx0
      exact (Finset.disjoint_left.mp hd) hxmiss hgamma0
    simpa [MissingColors] using hnot
  obtain ⟨f1, hf1inc, hf1color⟩ : ∃ f1 : E,
      Incident G y1 f1 ∧ phi f1 = some gamma := by
    simpa [PresentColors] using gamma_present hy1T hy01.symm
  obtain ⟨f2, hf2inc, hf2color⟩ : ∃ f2 : E,
      Incident G y2 f2 ∧ phi f2 = some gamma := by
    simpa [PresentColors] using gamma_present hy2T hy02.symm
  obtain ⟨f3, hf3inc, hf3color⟩ : ∃ f3 : E,
      Incident G y3 f3 ∧ phi f3 = some gamma := by
    simpa [PresentColors] using gamma_present hy3T hy03.symm
  obtain ⟨f4, hf4inc, hf4color⟩ : ∃ f4 : E,
      Incident G y4 f4 ∧ phi f4 = some gamma := by
    simpa [PresentColors] using gamma_present hy4T hy04.symm
  obtain ⟨z1, hf1ends⟩ := Sym2.mem_iff_exists.mp hf1inc
  obtain ⟨z2, hf2ends⟩ := Sym2.mem_iff_exists.mp hf2inc
  obtain ⟨z3, hf3ends⟩ := Sym2.mem_iff_exists.mp hf3inc
  obtain ⟨z4, hf4ends⟩ := Sym2.mem_iff_exists.mp hf4inc
  have middle_no_escape (r : E) (w : V)
      (hrcolor : phi r = some gamma)
      (hrends :
        G.ends r = s(T.vertex ⟨2, by have := N.height_upper; omega⟩, w) ∨
        G.ends r = s(T.vertex ⟨3, by have := N.height_upper; omega⟩, w)) :
      w = T.vertex ⟨0, by have := N.height_upper; omega⟩ ∨
      w = T.vertex ⟨1, by have := N.height_upper; omega⟩ ∨
      w = T.vertex ⟨2, by have := N.height_upper; omega⟩ ∨
      w = T.vertex ⟨3, by have := N.height_upper; omega⟩ ∨
      w = T.vertex ⟨4, by have := N.height_upper; omega⟩ := by
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
    have missing_excludes {c : Fin k} {x : V} {f : E}
        (hc : c ∈ MissingColors G phi x) (hinc : Incident G x f) :
        phi f ≠ some c := by
      intro hfc
      have hp : c ∈ PresentColors G phi x := by
        simp [PresentColors]
        exact ⟨f, hinc, hfc⟩
      have hn : c ∉ PresentColors G phi x := by
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
      | inl x =>
          rw [hz] at hadj
          have hdata : Incident G x f ∧
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
          simp
        exact False.elim ((missing_excludes hbmiss hinc) h)
    have ha1a2 : AdjacentEdges G a1 a2 := by
      refine ⟨y2, ?_, ?_⟩ <;> unfold Incident
      · rw [ha1ends]
        simp
      · rw [ha2ends]
        simp
    have ha12ne : a1 ≠ a2 := by
      intro h
      exact (show r1 ≠ r2 by simp [r1, r2])
        (T.edge_injective (by simpa [a1, a2] using h))
    have ha2color : phi a2 = some N.beta := by
      rcases edge_color_of_closing_support a2 ha2support with h | h
      · exact False.elim ((hproper ha12ne ha1a2 ha1color) h)
      · exact h
    have ha2a3 : AdjacentEdges G a2 a3 := by
      refine ⟨y3, ?_, ?_⟩ <;> unfold Incident
      · rw [ha2ends]
        simp
      · rw [ha3ends]
        simp
    have ha23ne : a2 ≠ a3 := by
      intro h
      exact (show r2 ≠ r3 by simp [r2, r3])
        (T.edge_injective (by simpa [a2, a3] using h))
    have ha3color : phi a3 = some N.alpha := by
      rcases edge_color_of_closing_support a3 ha3support with h | h
      · exact h
      · exact False.elim ((hproper ha23ne ha2a3 ha2color) h)
    have ha3q : AdjacentEdges G a3 q := by
      refine ⟨y4, ?_, ?_⟩ <;> unfold Incident
      · rw [ha3ends]
        simp
      · rw [hqends]
        simp
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
    have halpha_beta : N.alpha ≠ N.beta := by
      intro h
      have hinc : Incident G y1 a1 := by
        unfold Incident
        rw [ha1ends]
        simp
      exact (missing_excludes (by simpa [y1] using N.beta_missing) hinc)
        (by simpa [h] using ha1color)
    have hv0' : v ≠ y0 := by simpa [y0] using hv0
    have hv1' : v ≠ y1 := by simpa [y1] using hv1
    have hv2' : v ≠ y2 := by simpa [y2] using hv2
    have hv3' : v ≠ y3 := by simpa [y3] using hv3
    have hv4' : v ≠ y4 := by simpa [y4] using hv4
    have hgends' : G.ends g = s(y0, v) ∨ G.ends g = s(y1, v) ∨
        G.ends g = s(y2, v) ∨ G.ends g = s(y3, v) ∨
        G.ends g = s(y4, v) := by
      simpa [y0, y1, y2, y3, y4] using hgends
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
      change H1.connectedComponentMk (Sum.inl y0) =
        H1.connectedComponentMk (Sum.inl y0)
      rfl
    have C1_of_adj {x z : Sum V E} (hx : x ∈ C1) (hxz : H1.Adj x z) : z ∈ C1 := by
      change H1.connectedComponentMk x = H1.connectedComponentMk (Sum.inl y0) at hx
      change H1.connectedComponentMk z = H1.connectedComponentMk (Sum.inl y0)
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxz).symm.trans hx
    have support_of_C1 {z : Sum V E} (hz : z ∈ C1) : z ∈ p1.support := by
      exact (Set.ext_iff.mp hp1support' z).mpr hz
    have edge_step_C1 {x : V} {f : E} (hx : Sum.inl x ∈ C1)
        (hxf : Incident G x f)
        (hfc : phi f = some gamma ∨ phi f = some N.beta) :
        Sum.inr f ∈ C1 := by
      apply C1_of_adj hx
      simpa [H1, TwoColorIncidenceGraph] using And.intro hxf hfc
    have vertex_step_C1 {f : E} {x : V} (hf : Sum.inr f ∈ C1)
        (hxf : Incident G x f)
        (hfc : phi f = some gamma ∨ phi f = some N.beta) :
        Sum.inl x ∈ C1 := by
      apply C1_of_adj hf
      simpa [H1, TwoColorIncidenceGraph] using And.intro hxf hfc
    have hqinc0 : Incident G y0 q := by unfold Incident; rw [hqends]; simp
    have hqinc4 : Incident G y4 q := by unfold Incident; rw [hqends]; simp
    have hqC1 : Sum.inr q ∈ C1 :=
      edge_step_C1 hC1root hqinc0 (Or.inr hqcolor)
    have hy4C1 : Sum.inl y4 ∈ C1 :=
      vertex_step_C1 hqC1 hqinc4 (Or.inr hqcolor)
    have hy1C1 : Sum.inl y1 ∈ C1 := by
      have hm := p1.getVert_mem_support p1.length
      rw [p1.getVert_length] at hm
      apply (Set.ext_iff.mp hp1support' _).mp
      simpa [y1] using hm
    have helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) :=
      (ScheideGlobalMaximumOrder G k e0 phi T N.global).2.2.2.1
    have hy0T : y0 ∈ TreeSequenceVertexSet T := by
      simp [y0, TreeSequenceVertexSet]
    have hy1T : y1 ∈ TreeSequenceVertexSet T := by
      simp [y1, TreeSequenceVertexSet]
    have hgamma_not_missing_y1 : gamma ∉ MissingColors G phi y1 := by
      intro hm
      have hd := helem hy0T hy1T hy01
      exact (Finset.disjoint_left.mp hd) (by simpa [y0] using hgamma) hm
    have hgamma_present_y1 : gamma ∈ PresentColors G phi y1 := by
      simpa [MissingColors] using hgamma_not_missing_y1
    obtain ⟨b, hbinc, hbcolor⟩ : ∃ b : E,
        Incident G y1 b ∧ phi b = some gamma := by
      simpa [PresentColors] using hgamma_present_y1
    have hbC1 : Sum.inr b ∈ C1 :=
      edge_step_C1 hy1C1 hbinc (Or.inl hbcolor)
    have hqa1 : q ≠ a1 := by
      intro h
      have hpairs : s(y4, y0) = s(y1, y2) := by
        rw [← hqends, h, ha1ends]
      rcases Sym2.eq_iff.mp hpairs with hd | hs
      · exact hy14 hd.1.symm
      · exact hy24 hs.1.symm
    have hqa2 : q ≠ a2 := by
      intro h
      have hpairs : s(y4, y0) = s(y2, y3) := by
        rw [← hqends, h, ha2ends]
      rcases Sym2.eq_iff.mp hpairs with hd | hs
      · exact hy24 hd.1.symm
      · exact hy34 hs.1.symm
    have hqa3 : q ≠ a3 := ha3qne.symm
    have ha13ne : a1 ≠ a3 := by
      intro h
      exact (show r1 ≠ r3 by simp [r1, r3])
        (T.edge_injective (by simpa [a1, a3] using h))
    have hgamma_alpha : gamma ≠ N.alpha := by
      intro hga
      have ha3C1 : Sum.inr a3 ∈ C1 := by
        apply edge_step_C1 hy4C1
        · unfold Incident
          rw [ha3ends]
          simp
        · left
          simpa [hga] using ha3color
      have hy3C1 : Sum.inl y3 ∈ C1 := by
        apply vertex_step_C1 ha3C1
        · unfold Incident
          rw [ha3ends]
          simp
        · left
          simpa [hga] using ha3color
      have ha2C1 : Sum.inr a2 ∈ C1 := by
        apply edge_step_C1 hy3C1
        · unfold Incident
          rw [ha2ends]
          simp
        · exact Or.inr ha2color
      have hy2C1 : Sum.inl y2 ∈ C1 := by
        apply vertex_step_C1 ha2C1
        · unfold Incident
          rw [ha2ends]
          simp
        · exact Or.inr ha2color
      have ha1C1 : Sum.inr a1 ∈ C1 := by
        apply edge_step_C1 hy2C1
        · unfold Incident
          rw [ha1ends]
          simp
        · left
          simpa [hga] using ha1color
      have hvC1 : Sum.inl v ∈ C1 := by
        rcases hgends' with hgv | hgv | hgv | hgv | hgv
        all_goals
          have hgi : Incident G v g := by unfold Incident; rw [hgv]; simp
        · have hgC := edge_step_C1 hC1root (by unfold Incident; rw [hgv]; simp)
              (Or.inl hgcolor)
          exact vertex_step_C1 hgC hgi (Or.inl hgcolor)
        · have hgC := edge_step_C1 hy1C1 (by unfold Incident; rw [hgv]; simp)
              (Or.inl hgcolor)
          exact vertex_step_C1 hgC hgi (Or.inl hgcolor)
        · have hgC := edge_step_C1 hy2C1 (by unfold Incident; rw [hgv]; simp)
              (Or.inl hgcolor)
          exact vertex_step_C1 hgC hgi (Or.inl hgcolor)
        · have hgC := edge_step_C1 hy3C1 (by unfold Incident; rw [hgv]; simp)
              (Or.inl hgcolor)
          exact vertex_step_C1 hgC hgi (Or.inl hgcolor)
        · have hgC := edge_step_C1 hy4C1 (by unfold Incident; rw [hgv]; simp)
              (Or.inl hgcolor)
          exact vertex_step_C1 hgC hgi (Or.inl hgcolor)
      let K10 : Finset (Sum V E) :=
        {Sum.inl y0, Sum.inl y1, Sum.inl y2, Sum.inl y3, Sum.inl y4,
          Sum.inl v, Sum.inr q, Sum.inr a1, Sum.inr a2, Sum.inr a3}
      have hK10card : K10.card = 10 := by
        simp [K10, hy01, hy02, hy03, hy04, hy12, hy13, hy14, hy23, hy24,
          hy34, hv0', hv1', hv2', hv3', hv4', hqa1, hqa2, hqa3,
          ha12ne, ha13ne, ha23ne, Ne.symm hy01, Ne.symm hy02, Ne.symm hy03,
          Ne.symm hy04, Ne.symm hy12, Ne.symm hy13, Ne.symm hy14,
          Ne.symm hy23, Ne.symm hy24, Ne.symm hy34, Ne.symm hv0',
          Ne.symm hv1', Ne.symm hv2', Ne.symm hv3', Ne.symm hv4',
          Ne.symm hqa1, Ne.symm hqa2, Ne.symm hqa3, Ne.symm ha12ne,
          Ne.symm ha13ne, Ne.symm ha23ne]
      have hK10sub : K10 ⊆ p1.support.toFinset := by
        intro z hz
        simp only [K10, Finset.mem_insert, Finset.mem_singleton] at hz
        simp only [List.mem_toFinset]
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact support_of_C1 hC1root
        · exact support_of_C1 hy1C1
        · exact support_of_C1 hy2C1
        · exact support_of_C1 hy3C1
        · exact support_of_C1 hy4C1
        · exact support_of_C1 hvC1
        · exact support_of_C1 hqC1
        · exact support_of_C1 ha1C1
        · exact support_of_C1 ha2C1
        · exact support_of_C1 ha3C1
      have hp1lower : 9 ≤ p1.length := by
        have hc := Finset.card_le_card hK10sub
        rw [hK10card, List.toFinset_card_of_nodup hp1.support_nodup,
          p1.length_support] at hc
        omega
      rcases hp1div with ⟨d, hd⟩
      omega
    have hgamma_beta : gamma ≠ N.beta := by
      intro h
      exact (missing_excludes (by simpa [y1] using N.beta_missing) hbinc)
        (by simpa [h] using hbcolor)
    have hrends' : G.ends r = s(y2, w) ∨ G.ends r = s(y3, w) := by
      simpa [y2, y3] using hrends
    change w = y0 ∨ w = y1 ∨ w = y2 ∨ w = y3 ∨ w = y4
    by_contra hwtrunk
    push_neg at hwtrunk
    rcases hwtrunk with ⟨hw0, hw1, hw2, hw3, hw4⟩
    have ha2inc2 : Incident G y2 a2 := by unfold Incident; rw [ha2ends]; simp
    have ha2inc3 : Incident G y3 a2 := by unfold Incident; rw [ha2ends]; simp
    have hrincw : Incident G w r := by
      rcases hrends' with h | h <;> unfold Incident <;> rw [h] <;> simp
    have hrmiddle : Incident G y2 r ∨ Incident G y3 r := by
      rcases hrends' with h | h
      · left
        unfold Incident
        rw [h]
        simp
      · right
        unfold Incident
        rw [h]
        simp
    have hbq : b ≠ q := by
      intro h
      rw [h, hqcolor] at hbcolor
      exact hgamma_beta (Option.some.inj hbcolor.symm)
    have hba2 : b ≠ a2 := by
      intro h
      rw [h, ha2color] at hbcolor
      exact hgamma_beta (Option.some.inj hbcolor.symm)
    have hrq : r ≠ q := by
      intro h
      rw [h, hqcolor] at hrcolor
      exact hgamma_beta (Option.some.inj hrcolor.symm)
    have hra2 : r ≠ a2 := by
      intro h
      rw [h, ha2color] at hrcolor
      exact hgamma_beta (Option.some.inj hrcolor.symm)
    have hbr : b ≠ r := by
      intro h
      have hinc : Incident G y1 r := by simpa [h] using hbinc
      rcases hrends' with hr | hr
      · unfold Incident at hinc
        rw [hr] at hinc
        simp [hy12] at hinc
        exact hw1 hinc.symm
      · unfold Incident at hinc
        rw [hr] at hinc
        simp [hy13] at hinc
        exact hw1 hinc.symm
    have middle_too_large
        (hy2C : Sum.inl y2 ∈ C1) (hy3C : Sum.inl y3 ∈ C1)
        (hwC : Sum.inl w ∈ C1) : False := by
      have ha2C : Sum.inr a2 ∈ C1 :=
        edge_step_C1 hy2C ha2inc2 (Or.inr ha2color)
      have hrC : Sum.inr r ∈ C1 := by
        rcases hrmiddle with h | h
        · exact edge_step_C1 hy2C h (Or.inl hrcolor)
        · exact edge_step_C1 hy3C h (Or.inl hrcolor)
      let L10 : Finset (Sum V E) :=
        {Sum.inl y0, Sum.inl y1, Sum.inl y2, Sum.inl y3, Sum.inl y4,
          Sum.inl w, Sum.inr q, Sum.inr a2, Sum.inr b, Sum.inr r}
      have hL10card : L10.card = 10 := by
        simp [L10, hy01, hy02, hy03, hy04, hy12, hy13, hy14, hy23, hy24,
          hy34, hw0, hw1, hw2, hw3, hw4, hqa2, hbq, hba2, hrq, hra2, hbr,
          Ne.symm hy01, Ne.symm hy02, Ne.symm hy03, Ne.symm hy04,
          Ne.symm hy12, Ne.symm hy13, Ne.symm hy14, Ne.symm hy23,
          Ne.symm hy24, Ne.symm hy34, Ne.symm hw0, Ne.symm hw1,
          Ne.symm hw2, Ne.symm hw3, Ne.symm hw4, Ne.symm hqa2,
          Ne.symm hbq, Ne.symm hba2, Ne.symm hrq, Ne.symm hra2, Ne.symm hbr]
      have hL10sub : L10 ⊆ p1.support.toFinset := by
        intro z hz
        simp only [L10, Finset.mem_insert, Finset.mem_singleton] at hz
        simp only [List.mem_toFinset]
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact support_of_C1 hC1root
        · exact support_of_C1 hy1C1
        · exact support_of_C1 hy2C
        · exact support_of_C1 hy3C
        · exact support_of_C1 hy4C1
        · exact support_of_C1 hwC
        · exact support_of_C1 hqC1
        · exact support_of_C1 ha2C
        · exact support_of_C1 hbC1
        · exact support_of_C1 hrC
      have hp1lower : 9 ≤ p1.length := by
        have hc := Finset.card_le_card hL10sub
        rw [hL10card, List.toFinset_card_of_nodup hp1.support_nodup,
          p1.length_support] at hc
        omega
      rcases hp1div with ⟨d, hd⟩
      omega
    have hy2notC1 : Sum.inl y2 ∉ C1 := by
      intro hy2C
      have ha2C := edge_step_C1 hy2C ha2inc2 (Or.inr ha2color)
      have hy3C := vertex_step_C1 ha2C ha2inc3 (Or.inr ha2color)
      have hrC : Sum.inr r ∈ C1 := by
        rcases hrmiddle with h | h
        · exact edge_step_C1 hy2C h (Or.inl hrcolor)
        · exact edge_step_C1 hy3C h (Or.inl hrcolor)
      have hwC := vertex_step_C1 hrC hrincw (Or.inl hrcolor)
      exact middle_too_large hy2C hy3C hwC
    have hy3notC1 : Sum.inl y3 ∉ C1 := by
      intro hy3C
      have ha2C := edge_step_C1 hy3C ha2inc3 (Or.inr ha2color)
      exact hy2notC1 (vertex_step_C1 ha2C ha2inc2 (Or.inr ha2color))
    have hwnotC1 : Sum.inl w ∉ C1 := by
      intro hwC
      have hrC := edge_step_C1 hwC hrincw (Or.inl hrcolor)
      rcases hrmiddle with h | h
      · exact hy2notC1 (vertex_step_C1 hrC h (Or.inl hrcolor))
      · exact hy3notC1 (vertex_step_C1 hrC h (Or.inl hrcolor))
    have hrnotC1 : Sum.inr r ∉ C1 := by
      intro hrC
      rcases hrmiddle with h | h
      · exact hy2notC1 (vertex_step_C1 hrC h (Or.inl hrcolor))
      · exact hy3notC1 (vertex_step_C1 hrC h (Or.inl hrcolor))
    have hfixed : FixedPairMaximalTashkinovTree G e0 phi T :=
      ScheideGlobalMaximumFixedPairMaximal G k e0 phi T N.global
    let i0 : Fin (T.length + 1) := ⟨0, by omega⟩
    let i1 : Fin (T.length + 1) := ⟨1, by have := N.height_upper; omega⟩
    obtain ⟨_, pmax, hpmax, hpmaxsupport, hpmaxdiv, hpmaxvertices, hchange⟩ :=
      ScheideMaximalKempePath G k e0 phi T T N.global.1 hfixed N.global.2.1
        i0 i1 (by simp [i0, i1]) gamma N.beta
        (by simpa [i0] using hgamma) (by simpa [i1] using N.beta_missing)
    have hunused : TreeColorUnusedThrough phi T gamma i1 := by
      intro j hjpos hjlt
      simp [i1] at hjlt
      omega
    have hchangedata := hchange hunused
    let phi' := TwoColorComponentSwap G phi gamma N.beta (Sum.inl y0)
    have hproper' : IsProperEdgeColoring G phi' := by
      simpa [phi', y0, i0] using hchangedata.1
    have hone' : IsOneEdgeUncolored phi' e0 := by
      simpa [phi', y0, i0] using hchangedata.2.1
    have hTash' : TashkinovTree G e0 phi' T := by
      simpa [phi', y0, i0] using hchangedata.2.2
    have hglobal' : GlobalMaximumTriple G k e0 phi' T := by
      exact ⟨⟨N.global.1.1, N.global.1.2.1, N.global.1.2.2.1,
        hproper', hone'⟩, hTash', N.global.2.2⟩
    have hbehavior := TwoColorComponentSwapMissingBehavior G phi gamma N.beta
      hgamma_beta hproper (Sum.inl y0)
    have hgamma' : gamma ∈ MissingColors G phi' y1 := by
      exact hbehavior.2.2.1 y1 hy1C1 (by simpa [y1] using N.beta_missing)
    have halpha' : N.alpha ∈ MissingColors G phi' y0 := by
      apply (hbehavior.2.2.2 y0 N.alpha hgamma_alpha.symm halpha_beta).2
      simpa [y0] using N.alpha_missing
    have hqcolor' : phi' q = some gamma := by
      simp [phi', TwoColorComponentSwap, C1, hqC1, hqcolor, hgamma_beta]
    have alpha_fixed (f : E) : phi' f = some N.alpha ↔ phi f = some N.alpha := by
      by_cases hfC : Sum.inr f ∈ C1
      · by_cases hfg : phi f = some gamma
        · simp [phi', TwoColorComponentSwap, C1, hfC, hfg, hgamma_alpha,
            halpha_beta, hgamma_beta, Ne.symm hgamma_alpha,
            Ne.symm halpha_beta, Ne.symm hgamma_beta]
        · by_cases hfb : phi f = some N.beta
          · simp [phi', TwoColorComponentSwap, C1, hfC, hfg, hfb,
              hgamma_alpha, halpha_beta, hgamma_beta, Ne.symm hgamma_alpha,
              Ne.symm halpha_beta, Ne.symm hgamma_beta]
          · simp [phi', TwoColorComponentSwap, C1, hfC, hfg, hfb]
      · simp [phi', TwoColorComponentSwap, C1, hfC]
    have ha1color' : phi' a1 = some N.alpha := (alpha_fixed a1).2 ha1color
    have ha3color' : phi' a3 = some N.alpha := (alpha_fixed a3).2 ha3color
    have hrcolor' : phi' r = some gamma := by
      simp [phi', TwoColorComponentSwap, C1, hrnotC1, hrcolor]
    obtain ⟨p2, hp2, hp2support, hp2div, hp2vertices, hp2bound⟩ :=
      ScheideKempePathHeightBound G k e0 phi' T hglobal' N.alpha gamma
        (by simpa [y0] using halpha') (by simpa [y1] using hgamma')
    have hp2bound' : p2.length / 2 + 1 ≤ 5 := by
      simpa [hGheight] using hp2bound
    let H2 := TwoColorIncidenceGraph G phi' N.alpha gamma
    let C2 := TwoColorComponent G phi' N.alpha gamma (Sum.inl y0)
    have hp2support' : {z | z ∈ p2.support} = C2 := by
      simpa [C2, y0] using hp2support
    have hC2root : Sum.inl y0 ∈ C2 := by
      change H2.connectedComponentMk (Sum.inl y0) =
        H2.connectedComponentMk (Sum.inl y0)
      rfl
    have C2_of_adj {x z : Sum V E} (hx : x ∈ C2) (hxz : H2.Adj x z) : z ∈ C2 := by
      change H2.connectedComponentMk x = H2.connectedComponentMk (Sum.inl y0) at hx
      change H2.connectedComponentMk z = H2.connectedComponentMk (Sum.inl y0)
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxz).symm.trans hx
    have support_of_C2 {z : Sum V E} (hz : z ∈ C2) : z ∈ p2.support := by
      exact (Set.ext_iff.mp hp2support' z).mpr hz
    have edge_step_C2 {x : V} {f : E} (hx : Sum.inl x ∈ C2)
        (hxf : Incident G x f)
        (hfc : phi' f = some N.alpha ∨ phi' f = some gamma) :
        Sum.inr f ∈ C2 := by
      apply C2_of_adj hx
      simpa [H2, TwoColorIncidenceGraph] using And.intro hxf hfc
    have vertex_step_C2 {f : E} {x : V} (hf : Sum.inr f ∈ C2)
        (hxf : Incident G x f)
        (hfc : phi' f = some N.alpha ∨ phi' f = some gamma) :
        Sum.inl x ∈ C2 := by
      apply C2_of_adj hf
      simpa [H2, TwoColorIncidenceGraph] using And.intro hxf hfc
    have hqC2 := edge_step_C2 hC2root hqinc0 (Or.inr hqcolor')
    have hy4C2 := vertex_step_C2 hqC2 hqinc4 (Or.inr hqcolor')
    have ha3inc4 : Incident G y4 a3 := by unfold Incident; rw [ha3ends]; simp
    have ha3inc3 : Incident G y3 a3 := by unfold Incident; rw [ha3ends]; simp
    have ha3C2 := edge_step_C2 hy4C2 ha3inc4 (Or.inl ha3color')
    have hy3C2 := vertex_step_C2 ha3C2 ha3inc3 (Or.inl ha3color')
    have hy1C2 : Sum.inl y1 ∈ C2 := by
      have hm := p2.getVert_mem_support p2.length
      rw [p2.getVert_length] at hm
      apply (Set.ext_iff.mp hp2support' _).mp
      simpa [y1] using hm
    have ha1inc1 : Incident G y1 a1 := by unfold Incident; rw [ha1ends]; simp
    have ha1inc2 : Incident G y2 a1 := by unfold Incident; rw [ha1ends]; simp
    have ha1C2 := edge_step_C2 hy1C2 ha1inc1 (Or.inl ha1color')
    have hy2C2 := vertex_step_C2 ha1C2 ha1inc2 (Or.inl ha1color')
    have hrC2 : Sum.inr r ∈ C2 := by
      rcases hrmiddle with h | h
      · exact edge_step_C2 hy2C2 h (Or.inr hrcolor')
      · exact edge_step_C2 hy3C2 h (Or.inr hrcolor')
    have hwC2 := vertex_step_C2 hrC2 hrincw (Or.inr hrcolor')
    have hra1 : r ≠ a1 := by
      intro h
      rw [h, ha1color] at hrcolor
      exact hgamma_alpha (Option.some.inj hrcolor.symm)
    have hra3 : r ≠ a3 := by
      intro h
      rw [h, ha3color] at hrcolor
      exact hgamma_alpha (Option.some.inj hrcolor.symm)
    let M10 : Finset (Sum V E) :=
      {Sum.inl y0, Sum.inl y1, Sum.inl y2, Sum.inl y3, Sum.inl y4,
        Sum.inl w, Sum.inr q, Sum.inr a1, Sum.inr a3, Sum.inr r}
    have hM10card : M10.card = 10 := by
      simp [M10, hy01, hy02, hy03, hy04, hy12, hy13, hy14, hy23, hy24,
        hy34, hw0, hw1, hw2, hw3, hw4, hqa1, hqa3, ha13ne, hrq, hra1,
        hra3, Ne.symm hy01, Ne.symm hy02, Ne.symm hy03, Ne.symm hy04,
        Ne.symm hy12, Ne.symm hy13, Ne.symm hy14, Ne.symm hy23,
        Ne.symm hy24, Ne.symm hy34, Ne.symm hw0, Ne.symm hw1,
        Ne.symm hw2, Ne.symm hw3, Ne.symm hw4, Ne.symm hqa1,
        Ne.symm hqa3, Ne.symm ha13ne, Ne.symm hrq, Ne.symm hra1,
        Ne.symm hra3]
    have hM10sub : M10 ⊆ p2.support.toFinset := by
      intro z hz
      simp only [M10, Finset.mem_insert, Finset.mem_singleton] at hz
      simp only [List.mem_toFinset]
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact support_of_C2 hC2root
      · exact support_of_C2 hy1C2
      · exact support_of_C2 hy2C2
      · exact support_of_C2 hy3C2
      · exact support_of_C2 hy4C2
      · exact support_of_C2 hwC2
      · exact support_of_C2 hqC2
      · exact support_of_C2 ha1C2
      · exact support_of_C2 ha3C2
      · exact support_of_C2 hrC2
    have hp2lower : 9 ≤ p2.length := by
      have hc := Finset.card_le_card hM10sub
      rw [hM10card, List.toFinset_card_of_nodup hp2.support_nodup,
        p2.length_support] at hc
      omega
    rcases hp2div with ⟨d, hd⟩
    omega
  have hz2trunk : z2 = y0 ∨ z2 = y1 ∨ z2 = y2 ∨ z2 = y3 ∨ z2 = y4 := by
    simpa [y0, y1, y2, y3, y4] using
      (middle_no_escape f2 z2 hf2color
        (Or.inl (by simpa [y2] using hf2ends)))
  have hz3trunk : z3 = y0 ∨ z3 = y1 ∨ z3 = y2 ∨ z3 = y3 ∨ z3 = y4 := by
    simpa [y0, y1, y2, y3, y4] using
      (middle_no_escape f3 z3 hf3color
        (Or.inr (by simpa [y3] using hf3ends)))
  have endpoint_in_tree {x z : V} {f : E}
      (hxT : x ∈ TreeSequenceVertexSet T)
      (hfends : G.ends f = s(x, z)) (hfcolor : phi f = some gamma) :
      z ∈ TreeSequenceVertexSet T := by
    by_contra hzT
    have hboundary : f ∈ BoundaryEdges G (TreeSequenceVertexSet T) := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x, hxT, z, hzT, hfends⟩
    exact (hclosed hboundary hy0T hfcolor) hgamma0
  have hz1T : z1 ∈ TreeSequenceVertexSet T :=
    endpoint_in_tree hy1T (by simpa [y1] using hf1ends) hf1color
  have hz4T : z4 ∈ TreeSequenceVertexSet T :=
    endpoint_in_tree hy4T (by simpa [y4] using hf4ends) hf4color
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
  have hproper : IsProperEdgeColoring G phi := N.global.1.2.2.2.1
  have missing_excludes {x : V} {f : E}
      (hm : gamma ∈ MissingColors G phi x) (hinc : Incident G x f) :
      phi f ≠ some gamma := by
    intro hfc
    have hp : gamma ∈ PresentColors G phi x := by
      simp [PresentColors]
      exact ⟨f, hinc, hfc⟩
    have hn : gamma ∉ PresentColors G phi x := by
      simpa [MissingColors] using hm
    exact hn hp
  have hz22 : z2 ≠ y2 := by
    intro h
    exact G.loopless f2 y2 (by simpa [h] using hf2ends)
  have hz33 : z3 ≠ y3 := by
    intro h
    exact G.loopless f3 y3 (by simpa [h] using hf3ends)
  have hz20 : z2 ≠ y0 := by
    intro h
    have hinc : Incident G y0 f2 := by
      unfold Incident
      rw [hf2ends, h]
      simp
    exact (missing_excludes hgamma0 hinc) hf2color
  have hz30 : z3 ≠ y0 := by
    intro h
    have hinc : Incident G y0 f3 := by
      unfold Incident
      rw [hf3ends, h]
      simp
    exact (missing_excludes hgamma0 hinc) hf3color
  have hgends' : G.ends g = s(y0, v) ∨ G.ends g = s(y1, v) ∨
      G.ends g = s(y2, v) ∨ G.ends g = s(y3, v) ∨
      G.ends g = s(y4, v) := by
    simpa [y0, y1, y2, y3, y4] using hgends
  have hv1' : v ≠ y1 := by simpa [y1] using hv1
  have hv2' : v ≠ y2 := by simpa [y2] using hv2
  have hv3' : v ≠ y3 := by simpa [y3] using hv3
  have hv4' : v ≠ y4 := by simpa [y4] using hv4
  have hgvinc : Incident G v g := by
    rcases hgends' with h | h | h | h | h <;>
      unfold Incident <;> rw [h] <;> simp
  have f2_eq_f3 : f2 = f3 := by
    by_contra hne
    have hz23 : z2 ≠ y3 := by
      intro h
      have hinc : Incident G y3 f2 := by
        unfold Incident
        rw [hf2ends, h]
        simp
      exact (hproper hne ⟨y3, hinc, hf3inc⟩ hf2color) hf3color
    have hz32 : z3 ≠ y2 := by
      intro h
      have hinc : Incident G y2 f3 := by
        unfold Incident
        rw [hf3ends, h]
        simp
      exact (hproper (Ne.symm hne) ⟨y2, hinc, hf2inc⟩ hf3color) hf2color
    have hz2cases : z2 = y1 ∨ z2 = y4 := by
      rcases hz2trunk with h | h | h | h | h
      · exact False.elim (hz20 h)
      · exact Or.inl h
      · exact False.elim (hz22 h)
      · exact False.elim (hz23 h)
      · exact Or.inr h
    have hz3cases : z3 = y1 ∨ z3 = y4 := by
      rcases hz3trunk with h | h | h | h | h
      · exact False.elim (hz30 h)
      · exact Or.inl h
      · exact False.elim (hz32 h)
      · exact False.elim (hz33 h)
      · exact Or.inr h
    have crossing_contra (hz2 : z2 = y1 ∨ z2 = y4)
        (hz3 : z3 = y1 ∨ z3 = y4) : False := by
      have hgf2 : g ≠ f2 := by
        intro h
        have hinc : Incident G v f2 := by simpa [h] using hgvinc
        unfold Incident at hinc
        rw [hf2ends] at hinc
        rcases hz2 with h2 | h2
        · rw [h2] at hinc
          simp only [Sym2.mem_iff] at hinc
          exact hinc.elim hv2' hv1'
        · rw [h2] at hinc
          simp only [Sym2.mem_iff] at hinc
          exact hinc.elim hv2' hv4'
      have hgf3 : g ≠ f3 := by
        intro h
        have hinc : Incident G v f3 := by simpa [h] using hgvinc
        unfold Incident at hinc
        rw [hf3ends] at hinc
        rcases hz3 with h3 | h3
        · rw [h3] at hinc
          simp only [Sym2.mem_iff] at hinc
          exact hinc.elim hv3' hv1'
        · rw [h3] at hinc
          simp only [Sym2.mem_iff] at hinc
          exact hinc.elim hv3' hv4'
      rcases hz2 with h2 | h2 <;> rcases hz3 with h3 | h3
      · have hi2 : Incident G y1 f2 := by
          unfold Incident
          rw [hf2ends, h2]
          simp
        have hi3 : Incident G y1 f3 := by
          unfold Incident
          rw [hf3ends, h3]
          simp
        exact (hproper hne ⟨y1, hi2, hi3⟩ hf2color) hf3color
      · rcases hgends' with h | h | h | h | h
        · have hinc : Incident G y0 g := by unfold Incident; rw [h]; simp
          exact (missing_excludes hgamma0 hinc) hgcolor
        · have hginc : Incident G y1 g := by unfold Incident; rw [h]; simp
          have hfinc : Incident G y1 f2 := by
            unfold Incident
            rw [hf2ends, h2]
            simp
          exact (hproper hgf2 ⟨y1, hginc, hfinc⟩ hgcolor) hf2color
        · have hginc : Incident G y2 g := by unfold Incident; rw [h]; simp
          exact (hproper hgf2 ⟨y2, hginc, hf2inc⟩ hgcolor) hf2color
        · have hginc : Incident G y3 g := by unfold Incident; rw [h]; simp
          exact (hproper hgf3 ⟨y3, hginc, hf3inc⟩ hgcolor) hf3color
        · have hginc : Incident G y4 g := by unfold Incident; rw [h]; simp
          have hfinc : Incident G y4 f3 := by
            unfold Incident
            rw [hf3ends, h3]
            simp
          exact (hproper hgf3 ⟨y4, hginc, hfinc⟩ hgcolor) hf3color
      · rcases hgends' with h | h | h | h | h
        · have hinc : Incident G y0 g := by unfold Incident; rw [h]; simp
          exact (missing_excludes hgamma0 hinc) hgcolor
        · have hginc : Incident G y1 g := by unfold Incident; rw [h]; simp
          have hfinc : Incident G y1 f3 := by
            unfold Incident
            rw [hf3ends, h3]
            simp
          exact (hproper hgf3 ⟨y1, hginc, hfinc⟩ hgcolor) hf3color
        · have hginc : Incident G y2 g := by unfold Incident; rw [h]; simp
          exact (hproper hgf2 ⟨y2, hginc, hf2inc⟩ hgcolor) hf2color
        · have hginc : Incident G y3 g := by unfold Incident; rw [h]; simp
          exact (hproper hgf3 ⟨y3, hginc, hf3inc⟩ hgcolor) hf3color
        · have hginc : Incident G y4 g := by unfold Incident; rw [h]; simp
          have hfinc : Incident G y4 f2 := by
            unfold Incident
            rw [hf2ends, h2]
            simp
          exact (hproper hgf2 ⟨y4, hginc, hfinc⟩ hgcolor) hf2color
      · have hi2 : Incident G y4 f2 := by
          unfold Incident
          rw [hf2ends, h2]
          simp
        have hi3 : Incident G y4 f3 := by
          unfold Incident
          rw [hf3ends, h3]
          simp
        exact (hproper hne ⟨y4, hi2, hi3⟩ hf2color) hf3color
    exact crossing_contra hz2cases hz3cases
  have hf23inc3 : Incident G y3 f2 := by
    rw [f2_eq_f3]
    exact hf3inc
  have hz2eq : z2 = y3 := by
    have hm : y3 ∈ s(y2, z2) := by
      rw [← hf2ends]
      exact hf23inc3
    simp only [Sym2.mem_iff] at hm
    rcases hm with h | h
    · exact False.elim (hy23 h.symm)
    · exact h.symm
  have hf23ends : G.ends f2 = s(y2, y3) := by simpa [hz2eq] using hf2ends
  have hf1ne2 : f1 ≠ f2 := by
    intro heq
    have hinc : Incident G y1 f2 := by
      rw [← heq]
      exact hf1inc
    unfold Incident at hinc
    rw [hf23ends] at hinc
    simp only [Sym2.mem_iff] at hinc
    exact hinc.elim hy12 hy13
  have hz11 : z1 ≠ y1 := by
    intro h
    exact G.loopless f1 y1 (by simpa [h] using hf1ends)
  have hz10 : z1 ≠ y0 := by
    intro h
    have hinc : Incident G y0 f1 := by unfold Incident; rw [hf1ends, h]; simp
    exact (missing_excludes hgamma0 hinc) hf1color
  have hz12 : z1 ≠ y2 := by
    intro h
    have hinc : Incident G y2 f1 := by unfold Incident; rw [hf1ends, h]; simp
    exact (hproper hf1ne2 ⟨y2, hinc, hf2inc⟩ hf1color) hf2color
  have hz13 : z1 ≠ y3 := by
    intro h
    have hinc : Incident G y3 f1 := by unfold Incident; rw [hf1ends, h]; simp
    exact (hproper hf1ne2 ⟨y3, hinc, hf23inc3⟩ hf1color) hf2color
  have hz14 : z1 ≠ y4 := by
    intro h14
    have hgf1 : g ≠ f1 := by
      intro h
      have hinc : Incident G v f1 := by simpa [h] using hgvinc
      unfold Incident at hinc
      rw [hf1ends, h14] at hinc
      simp only [Sym2.mem_iff] at hinc
      exact hinc.elim hv1' hv4'
    have hgf2 : g ≠ f2 := by
      intro h
      have hinc : Incident G v f2 := by simpa [h] using hgvinc
      unfold Incident at hinc
      rw [hf23ends] at hinc
      simp only [Sym2.mem_iff] at hinc
      exact hinc.elim hv2' hv3'
    rcases hgends' with h | h | h | h | h
    · have hginc : Incident G y0 g := by unfold Incident; rw [h]; simp
      exact (missing_excludes hgamma0 hginc) hgcolor
    · have hginc : Incident G y1 g := by unfold Incident; rw [h]; simp
      exact (hproper hgf1 ⟨y1, hginc, hf1inc⟩ hgcolor) hf1color
    · have hginc : Incident G y2 g := by unfold Incident; rw [h]; simp
      exact (hproper hgf2 ⟨y2, hginc, hf2inc⟩ hgcolor) hf2color
    · have hginc : Incident G y3 g := by unfold Incident; rw [h]; simp
      exact (hproper hgf2 ⟨y3, hginc, hf23inc3⟩ hgcolor) hf2color
    · have hginc : Incident G y4 g := by unfold Incident; rw [h]; simp
      have hfinc : Incident G y4 f1 := by
        unfold Incident
        rw [hf1ends, h14]
        simp
      exact (hproper hgf1 ⟨y4, hginc, hfinc⟩ hgcolor) hf1color
  have hz44 : z4 ≠ y4 := by
    intro h
    exact G.loopless f4 y4 (by simpa [h] using hf4ends)
  have hz40 : z4 ≠ y0 := by
    intro h
    have hinc : Incident G y0 f4 := by unfold Incident; rw [hf4ends, h]; simp
    exact (missing_excludes hgamma0 hinc) hf4color
  have hf4ne2 : f4 ≠ f2 := by
    intro heq
    have hinc : Incident G y4 f2 := by
      rw [← heq]
      exact hf4inc
    unfold Incident at hinc
    rw [hf23ends] at hinc
    simp only [Sym2.mem_iff] at hinc
    exact hinc.elim (Ne.symm hy24) (Ne.symm hy34)
  have hz42 : z4 ≠ y2 := by
    intro h
    have hinc : Incident G y2 f4 := by unfold Incident; rw [hf4ends, h]; simp
    exact (hproper hf4ne2 ⟨y2, hinc, hf2inc⟩ hf4color) hf2color
  have hz43 : z4 ≠ y3 := by
    intro h
    have hinc : Incident G y3 f4 := by unfold Incident; rw [hf4ends, h]; simp
    exact (hproper hf4ne2 ⟨y3, hinc, hf23inc3⟩ hf4color) hf2color
  have hz41 : z4 ≠ y1 := by
    intro h41
    have hf4inc1 : Incident G y1 f4 := by
      unfold Incident
      rw [hf4ends, h41]
      simp
    have heq : f4 = f1 := by
      by_contra hne
      exact (hproper hne ⟨y1, hf4inc1, hf1inc⟩ hf4color) hf1color
    have hpairs : s(y4, y1) = s(y1, z1) := by
      calc
        s(y4, y1) = G.ends f4 := by rw [hf4ends, h41]
        _ = G.ends f1 := congrArg G.ends heq
        _ = s(y1, z1) := hf1ends
    rcases Sym2.eq_iff.mp hpairs with hd | hs
    · exact hy14 hd.1.symm
    · exact hz14 hs.1.symm
  refine ⟨f1, f4, f2, z1, z4, ?_, ?_, ?_, hf1color, hf4color,
    hf2color, hz1T, hz4T, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [y1] using hf1ends
  · simpa [y4] using hf4ends
  · simpa [y2, y3] using hf23ends
  · simpa [y0] using hz10
  · simpa [y1] using hz11
  · simpa [y2] using hz12
  · simpa [y3] using hz13
  · simpa [y4] using hz14
  · simpa [y0] using hz40
  · simpa [y1] using hz41
  · simpa [y2] using hz42
  · simpa [y3] using hz43
  · simpa [y4] using hz44
