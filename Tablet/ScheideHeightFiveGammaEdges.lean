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
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideGraphHeight
import Tablet.ScheideKempePathHeightBound
import Tablet.ScheideMaximalKempePath
import Tablet.ScheideHeightFiveMiddleNoEscape
import Tablet.TashkinovOrder
import Tablet.TashkinovTree
import Tablet.TreeColorUnusedThrough
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
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
  have hz2trunk : z2 = y0 ∨ z2 = y1 ∨ z2 = y2 ∨ z2 = y3 ∨ z2 = y4 := by
    simpa [y0, y1, y2, y3, y4] using
      (ScheideHeightFiveMiddleNoEscape G k e0 phi T N hNheight hGheight
        gamma hgamma g v hgcolor hgends hvT hv0 hv1 hv2 hv3 hv4
        f2 z2 hf2color (Or.inl (by simpa [y2] using hf2ends)))
  have hz3trunk : z3 = y0 ∨ z3 = y1 ∨ z3 = y2 ∨ z3 = y3 ∨ z3 = y4 := by
    simpa [y0, y1, y2, y3, y4] using
      (ScheideHeightFiveMiddleNoEscape G k e0 phi T N hNheight hGheight
        gamma hgamma g v hgcolor hgends hvT hv0 hv1 hv2 hv3 hv4
        f3 z3 hf3color (Or.inr (by simpa [y3] using hf3ends)))
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
