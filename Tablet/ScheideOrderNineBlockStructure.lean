import Tablet.AdjacentEdges
import Tablet.BalancedGlobalMaximumTriple
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
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
import Tablet.ScheideHeightFiveGammaEdges
import Tablet.ScheideHeightFiveOutsideLinks
import Tablet.ScheideKempePathHeightBound
import Tablet.ScheideTrunkRotationColoring
import Tablet.ScheideTrunkRotationCycle
import Tablet.ScheideTrunkRotationNormal
import Tablet.ScheideTrunkRotationPreserves
import Tablet.ScheideTrunkRotationTree
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TrunkRotation
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Mathlib.Tactic.FinCases

open scoped Sym2

set_option maxHeartbeats 800000

-- [TABLET NODE: ScheideOrderNineBlockStructure]
theorem ScheideOrderNineBlockStructure {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hbalanced : BalancedGlobalMaximumTriple N)
    (horder : TashkinovOrder G = 9)
    (hgraphHeight : ScheideGraphHeight G = 5) :
    ∃ (e1 : E) (psi : PartialEdgeColoring E k) (S : TreeSequence G e1)
      (M : NormalGlobalMaximumTriple G k e1 psi S),
      ∃ (_ : BalancedGlobalMaximumTriple M) (_ : S.length = 8)
        (_ : M.height = 5) (gamma : Fin 2 → Fin k),
      Function.Injective gamma ∧
      (∀ (i : Fin 2) (j : Fin 2),
        ∃ q : Fin 5,
          G.ends (S.edge ⟨4 + 2 * i.val + j.val, by omega⟩) =
            s(S.vertex ⟨q.val, by omega⟩,
              S.vertex ⟨5 + 2 * i.val + j.val, by omega⟩)) ∧
      (∀ (i : Fin 2) (j : Fin 2),
        psi (S.edge ⟨4 + 2 * i.val + j.val, by omega⟩) =
          some (gamma i)) ∧
      (∀ i : Fin 2, ∃ q : Fin 5,
        gamma i ∈ MissingColors G psi (S.vertex ⟨q.val, by omega⟩)) ∧
      (∀ i : Fin 4, 1 ≤ i.val →
        ∀ c : Fin k, psi (S.edge ⟨i.val, by omega⟩) = some c →
          ∀ r : Fin 2, c ≠ gamma r) := by
-- BODY
  classical
  letI : DecidableEq V := Classical.decEq V
  have hNheight : N.height = 5 := hbalanced.1.trans hgraphHeight
  have hvertexCard : (TreeSequenceVertexSet T).card = T.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
      T.vertex_injective]
  have hlength : T.length = 8 := by
    have hcard := N.global.2.2
    rw [horder] at hcard
    omega
  let r4 : Fin T.length := ⟨4, by omega⟩
  let r5 : Fin T.length := ⟨5, by omega⟩
  let r6 : Fin T.length := ⟨6, by omega⟩
  let r7 : Fin T.length := ⟨7, by omega⟩
  obtain ⟨w0, gamma0, hr4color, hw0missing⟩ :=
    N.global.2.1 r4 (by simp [r4])
  have hr5color : phi (T.edge r5) = some gamma0 := by
    have hp := hbalanced.2 3 (by omega) (by omega)
    simpa [r4, r5] using hp.symm.trans hr4color
  obtain ⟨w1, gamma1, hr6color, hw1missing⟩ :=
    N.global.2.1 r6 (by simp [r6])
  have hr7color : phi (T.edge r7) = some gamma1 := by
    have hp := hbalanced.2 4 (by omega) (by omega)
    simpa [r6, r7] using hp.symm.trans hr6color
  let Good {e : E} (psi : PartialEdgeColoring E k)
      (S : TreeSequence G e)
      (M : NormalGlobalMaximumTriple G k e psi S) : Prop :=
    ∃ (_ : BalancedGlobalMaximumTriple M) (_ : S.length = 8)
      (_ : M.height = 5) (gamma : Fin 2 → Fin k),
      Function.Injective gamma ∧
      (∀ (i : Fin 2) (j : Fin 2),
        ∃ q : Fin 5,
          G.ends (S.edge ⟨4 + 2 * i.val + j.val, by omega⟩) =
            s(S.vertex ⟨q.val, by omega⟩,
              S.vertex ⟨5 + 2 * i.val + j.val, by omega⟩)) ∧
      (∀ (i : Fin 2) (j : Fin 2),
        psi (S.edge ⟨4 + 2 * i.val + j.val, by omega⟩) =
          some (gamma i)) ∧
      (∀ i : Fin 2, ∃ q : Fin 5,
        gamma i ∈ MissingColors G psi (S.vertex ⟨q.val, by omega⟩)) ∧
      (∀ i : Fin 4, 1 ≤ i.val →
        ∀ c : Fin k, psi (S.edge ⟨i.val, by omega⟩) = some c →
          ∀ r : Fin 2, c ≠ gamma r)
  have finish {e : E} (psi : PartialEdgeColoring E k)
      (S : TreeSequence G e)
      (M : NormalGlobalMaximumTriple G k e psi S)
      (hbal : BalancedGlobalMaximumTriple M)
      (hlen : S.length = 8) (hheight : M.height = 5)
      (g0 : Fin k)
      (h4 : psi (S.edge ⟨4, by omega⟩) = some g0)
      (h5 : psi (S.edge ⟨5, by omega⟩) = some g0)
      (hg0 : g0 ∈ MissingColors G psi
        (S.vertex ⟨0, Nat.zero_lt_succ S.length⟩)) :
      ∃ (e' : E) (psi' : PartialEdgeColoring E k) (S' : TreeSequence G e')
        (M' : NormalGlobalMaximumTriple G k e' psi' S'), Good psi' S' M' := by
    have hproper : IsProperEdgeColoring G psi := M.global.1.2.2.2.1
    have horderM := ScheideGlobalMaximumOrder G k e psi S M.global
    have helem : ColoredVertexSetElementary G psi
        (TreeSequenceVertexSet S) := horderM.2.2.2.1
    have hclosed : ColoredVertexSetClosed G psi
        (TreeSequenceVertexSet S) := horderM.2.2.2.2
    let y0 : V := S.vertex ⟨0, by omega⟩
    let y1 : V := S.vertex ⟨1, by omega⟩
    let y2 : V := S.vertex ⟨2, by omega⟩
    let y3 : V := S.vertex ⟨3, by omega⟩
    let y4 : V := S.vertex ⟨4, by omega⟩
    let y5 : V := S.vertex ⟨5, by omega⟩
    let y6 : V := S.vertex ⟨6, by omega⟩
    let y7 : V := S.vertex ⟨7, by omega⟩
    let y8 : V := S.vertex ⟨8, by omega⟩
    let a1 : E := S.edge ⟨1, by omega⟩
    let a2 : E := S.edge ⟨2, by omega⟩
    let a3 : E := S.edge ⟨3, by omega⟩
    let b0 : E := S.edge ⟨4, by omega⟩
    let b1 : E := S.edge ⟨5, by omega⟩
    let c0 : E := S.edge ⟨6, by omega⟩
    let c1 : E := S.edge ⟨7, by omega⟩
    have hvertex_ne {i j : Fin (S.length + 1)} (hij : i ≠ j) :
        S.vertex i ≠ S.vertex j := fun h => hij (S.vertex_injective h)
    have hedge_ne {i j : Fin S.length} (hij : i ≠ j) :
        S.edge i ≠ S.edge j := fun h => hij (S.edge_injective h)
    have hmem (i : Fin (S.length + 1)) :
        S.vertex i ∈ TreeSequenceVertexSet S := by
      simp [TreeSequenceVertexSet]
    have missing_excludes {c : Fin k} {v : V} {f : E}
        (hc : c ∈ MissingColors G psi v) (hinc : Incident G v f) :
        psi f ≠ some c := by
      intro hfc
      have hp : c ∈ PresentColors G psi v := by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨f, hinc, hfc⟩
      have hn : c ∉ PresentColors G psi v := by
        simpa [MissingColors] using hc
      exact hn hp
    have h4' : psi b0 = some g0 := by simpa [b0] using h4
    have h5' : psi b1 = some g0 := by simpa [b1] using h5
    have hg0' : g0 ∈ MissingColors G psi y0 := by simpa [y0] using hg0
    obtain ⟨p0, hp0⟩ := S.attaches (⟨4, by omega⟩ : Fin S.length)
    have hb0ends : G.ends b0 = s(y5,
        S.vertex (Fin.castLT p0
          (Nat.lt_trans p0.isLt
            (Nat.succ_lt_succ (⟨4, by omega⟩ : Fin S.length).isLt)))) := by
      simpa [b0, y5] using hp0
    obtain ⟨p1, hp1⟩ := S.attaches (⟨5, by omega⟩ : Fin S.length)
    have hb1ends : G.ends b1 = s(y6,
        S.vertex (Fin.castLT p1
          (Nat.lt_trans p1.isLt
            (Nat.succ_lt_succ (⟨5, by omega⟩ : Fin S.length).isLt)))) := by
      simpa [b1, y6] using hp1
    have hp1not5 : p1.val ≠ 5 := by
      intro hp15
      have hinc0 : Incident G y5 b0 := by
        rw [Incident, hb0ends]
        simp
      have hp1vertex : S.vertex (Fin.castLT p1
          (Nat.lt_trans p1.isLt
            (Nat.succ_lt_succ (⟨5, by omega⟩ : Fin S.length).isLt))) = y5 := by
        apply congrArg S.vertex
        apply Fin.ext
        simpa [y5] using hp15
      have hinc1 : Incident G y5 b1 := by
        rw [Incident, hb1ends, hp1vertex]
        simp
      have hbne : b0 ≠ b1 := by
        apply hedge_ne
        norm_num
      exact (hproper hbne ⟨y5, hinc0, hinc1⟩ h4') h5'
    have hfirstAttach : ∀ j : Fin 2, ∃ q : Fin 5,
        G.ends (S.edge ⟨4 + j.val, by omega⟩) =
          s(S.vertex ⟨q.val, by omega⟩,
            S.vertex ⟨5 + j.val, by omega⟩) := by
      intro j
      have hj : j.val = 0 ∨ j.val = 1 := by omega
      rcases hj with hj | hj
      · let q : Fin 5 := ⟨p0.val, by simpa using p0.isLt⟩
        refine ⟨q, ?_⟩
        have hv : S.vertex (Fin.castLT p0
            (Nat.lt_trans p0.isLt
              (Nat.succ_lt_succ (⟨4, by omega⟩ : Fin S.length).isLt))) =
            S.vertex ⟨q.val, by omega⟩ := by
          apply congrArg S.vertex
          apply Fin.ext
          rfl
        rw [show j = (0 : Fin 2) by apply Fin.ext; exact hj]
        simpa [b0, y5, hv] using hb0ends.trans Sym2.eq_swap
      · let q : Fin 5 := ⟨p1.val, by
            have hp := p1.isLt
            have hp' : p1.val < 6 := by simpa using hp
            omega⟩
        refine ⟨q, ?_⟩
        have hv : S.vertex (Fin.castLT p1
            (Nat.lt_trans p1.isLt
              (Nat.succ_lt_succ (⟨5, by omega⟩ : Fin S.length).isLt))) =
            S.vertex ⟨q.val, by omega⟩ := by
          apply congrArg S.vertex
          apply Fin.ext
          rfl
        rw [show j = (1 : Fin 2) by apply Fin.ext; exact hj]
        simpa [b1, y6, hv] using hb1ends.trans Sym2.eq_swap
    obtain ⟨q0, hq0ends⟩ := hfirstAttach (0 : Fin 2)
    have hq0cases :
        G.ends b0 = s(S.vertex ⟨0, by omega⟩, y5) ∨
        G.ends b0 = s(S.vertex ⟨1, by omega⟩, y5) ∨
        G.ends b0 = s(S.vertex ⟨2, by omega⟩, y5) ∨
        G.ends b0 = s(S.vertex ⟨3, by omega⟩, y5) ∨
        G.ends b0 = s(S.vertex ⟨4, by omega⟩, y5) := by
      have hcases : q0.val = 0 ∨ q0.val = 1 ∨ q0.val = 2 ∨
          q0.val = 3 ∨ q0.val = 4 := by omega
      rcases hcases with h | h | h | h | h
      · left; simpa [b0, y5, h] using hq0ends
      · right; left; simpa [b0, y5, h] using hq0ends
      · right; right; left; simpa [b0, y5, h] using hq0ends
      · right; right; right; left; simpa [b0, y5, h] using hq0ends
      · right; right; right; right; simpa [b0, y5, h] using hq0ends
    have hy5T : y5 ∈ TreeSequenceVertexSet S := by
      simpa [y5] using hmem (⟨5, by omega⟩ : Fin (S.length + 1))
    have hy50 : y5 ≠ y0 := by
      apply hvertex_ne
      norm_num
    have hy51 : y5 ≠ y1 := by
      apply hvertex_ne
      norm_num
    have hy52 : y5 ≠ y2 := by
      apply hvertex_ne
      norm_num
    have hy53 : y5 ≠ y3 := by
      apply hvertex_ne
      norm_num
    have hy54 : y5 ≠ y4 := by
      apply hvertex_ne
      norm_num
    obtain ⟨f1, f2, f3, v1, v2, hf1ends, hf2ends, hf3ends,
        hf1color, hf2color, hf3color, hv1T, hv2T, hv10, hv11, hv12,
        hv13, hv14, hv20, hv21, hv22, hv23, hv24⟩ :=
      ScheideHeightFiveGammaEdges G k e psi S M hheight hgraphHeight g0
        (by simpa [y0] using hg0') b0 y5 h4' hq0cases hy5T
        (by simpa [y0] using hy50) (by simpa [y1] using hy51)
        (by simpa [y2] using hy52) (by simpa [y3] using hy53)
        (by simpa [y4] using hy54)
    have hf1ends' : G.ends f1 = s(y1, v1) := by simpa [y1] using hf1ends
    have hf2ends' : G.ends f2 = s(y4, v2) := by simpa [y4] using hf2ends
    have hf3ends' : G.ends f3 = s(y2, y3) := by simpa [y2, y3] using hf3ends
    have classifyFirst : ∀ j : Fin 2,
        (S.edge ⟨4 + j.val, by omega⟩ = f1 ∧
          S.vertex ⟨5 + j.val, by omega⟩ = v1) ∨
        (S.edge ⟨4 + j.val, by omega⟩ = f2 ∧
          S.vertex ⟨5 + j.val, by omega⟩ = v2) := by
      intro j
      obtain ⟨q, hq⟩ := hfirstAttach j
      let bj : E := S.edge ⟨4 + j.val, by omega⟩
      let z : V := S.vertex ⟨5 + j.val, by omega⟩
      have hbjends : G.ends bj = s(S.vertex ⟨q.val, by omega⟩, z) := by
        simpa [bj, z] using hq
      have hbjcolor : psi bj = some g0 := by
        have hj : j.val = 0 ∨ j.val = 1 := by omega
        rcases hj with hj | hj
        · have : j = (0 : Fin 2) := Fin.ext hj
          subst j
          simpa [bj, b0] using h4'
        · have : j = (1 : Fin 2) := Fin.ext hj
          subst j
          simpa [bj, b1] using h5'
      have hz0 : z ≠ y0 := by
        apply hvertex_ne
        apply Fin.ne_of_val_ne
        change 5 + j.val ≠ 0
        omega
      have hz1 : z ≠ y1 := by
        apply hvertex_ne
        apply Fin.ne_of_val_ne
        change 5 + j.val ≠ 1
        omega
      have hz2 : z ≠ y2 := by
        apply hvertex_ne
        apply Fin.ne_of_val_ne
        change 5 + j.val ≠ 2
        omega
      have hz3 : z ≠ y3 := by
        apply hvertex_ne
        apply Fin.ne_of_val_ne
        change 5 + j.val ≠ 3
        omega
      have hz4 : z ≠ y4 := by
        apply hvertex_ne
        apply Fin.ne_of_val_ne
        change 5 + j.val ≠ 4
        omega
      have hq0 : q.val ≠ 0 := by
        intro hqv
        have hinc : Incident G y0 bj := by
          rw [Incident, hbjends]
          have hv : S.vertex ⟨q.val, by omega⟩ = y0 := by
            apply congrArg S.vertex
            apply Fin.ext
            simpa [y0] using hqv
          rw [hv]
          simp
        exact (missing_excludes hg0' hinc) hbjcolor
      have hbjf3 : bj ≠ f3 := by
        intro hEq
        have hpairs : s(S.vertex ⟨q.val, by omega⟩, z) = s(y2, y3) := by
          rw [← hbjends, hEq, hf3ends']
        rcases Sym2.eq_iff.mp hpairs with hd | hs
        · exact hz3 hd.2
        · exact hz2 hs.2
      have hq2 : q.val ≠ 2 := by
        intro hqv
        have hincb : Incident G y2 bj := by
          rw [Incident, hbjends]
          have hv : S.vertex ⟨q.val, by omega⟩ = y2 := by
            apply congrArg S.vertex
            apply Fin.ext
            simpa [y2] using hqv
          rw [hv]
          simp
        have hincf : Incident G y2 f3 := by
          rw [Incident, hf3ends']
          simp
        exact (hproper hbjf3 ⟨y2, hincb, hincf⟩ hbjcolor) hf3color
      have hq3 : q.val ≠ 3 := by
        intro hqv
        have hincb : Incident G y3 bj := by
          rw [Incident, hbjends]
          have hv : S.vertex ⟨q.val, by omega⟩ = y3 := by
            apply congrArg S.vertex
            apply Fin.ext
            simpa [y3] using hqv
          rw [hv]
          simp
        have hincf : Incident G y3 f3 := by
          rw [Incident, hf3ends']
          simp
        exact (hproper hbjf3 ⟨y3, hincb, hincf⟩ hbjcolor) hf3color
      have hqcases : q.val = 1 ∨ q.val = 4 := by omega
      rcases hqcases with hq1 | hq4
      · have hincb : Incident G y1 bj := by
          rw [Incident, hbjends]
          have hv : S.vertex ⟨q.val, by omega⟩ = y1 := by
            apply congrArg S.vertex
            apply Fin.ext
            simpa [y1] using hq1
          rw [hv]
          simp
        have hincf : Incident G y1 f1 := by
          rw [Incident, hf1ends']
          simp
        have hbf : bj = f1 := by
          by_contra hne
          exact (hproper hne ⟨y1, hincb, hincf⟩ hbjcolor) hf1color
        left
        refine ⟨by simpa [bj] using hbf, ?_⟩
        have hpairs : s(y1, z) = s(y1, v1) := by
          calc
            s(y1, z) = G.ends bj := by
              rw [hbjends]
              congr 1
              apply congrArg S.vertex
              apply Fin.ext
              simpa [y1] using hq1.symm
            _ = G.ends f1 := congrArg G.ends hbf
            _ = s(y1, v1) := hf1ends'
        rcases Sym2.eq_iff.mp hpairs with hd | hs
        · simpa [z] using hd.2
        · exact False.elim (hz1 hs.2)
      · have hincb : Incident G y4 bj := by
          rw [Incident, hbjends]
          have hv : S.vertex ⟨q.val, by omega⟩ = y4 := by
            apply congrArg S.vertex
            apply Fin.ext
            simpa [y4] using hq4
          rw [hv]
          simp
        have hincf : Incident G y4 f2 := by
          rw [Incident, hf2ends']
          simp
        have hbf : bj = f2 := by
          by_contra hne
          exact (hproper hne ⟨y4, hincb, hincf⟩ hbjcolor) hf2color
        right
        refine ⟨by simpa [bj] using hbf, ?_⟩
        have hpairs : s(y4, z) = s(y4, v2) := by
          calc
            s(y4, z) = G.ends bj := by
              rw [hbjends]
              congr 1
              apply congrArg S.vertex
              apply Fin.ext
              simpa [y4] using hq4.symm
            _ = G.ends f2 := congrArg G.ends hbf
            _ = s(y4, v2) := hf2ends'
        rcases Sym2.eq_iff.mp hpairs with hd | hs
        · simpa [z] using hd.2
        · exact False.elim (hz4 hs.2)
    have hb01ne : b0 ≠ b1 := by
      apply hedge_ne
      norm_num
    have horient :
        (b0 = f1 ∧ y5 = v1 ∧ b1 = f2 ∧ y6 = v2) ∨
        (b0 = f2 ∧ y5 = v2 ∧ b1 = f1 ∧ y6 = v1) := by
      have h0 := classifyFirst (0 : Fin 2)
      have h1 := classifyFirst (1 : Fin 2)
      rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
      · exact False.elim (hb01ne (by simpa [b0, b1] using h0.1.trans h1.1.symm))
      · left
        simpa [b0, b1, y5, y6] using ⟨h0.1, h0.2, h1.1, h1.2⟩
      · right
        simpa [b0, b1, y5, y6] using ⟨h0.1, h0.2, h1.1, h1.2⟩
      · exact False.elim (hb01ne (by simpa [b0, b1] using h0.1.trans h1.1.symm))
    obtain ⟨alpha56, beta56, halpha56ends, halpha56color,
        hbeta56ends, hbeta56color, hab56ne⟩ :=
      ScheideHeightFiveOutsideLinks G k e psi S M hheight hgraphHeight g0
        (by simpa [y0] using hg0') f1 f2 v1 v2 hf1ends hf2ends
        hf1color hf2color hv1T hv2T hv10 hv11 hv12 hv13 hv14 hv20 hv21
        hv22 hv23 hv24
    have halpha56ends' : G.ends alpha56 = s(y5, y6) := by
      rcases horient with h | h
      · simpa [h.2.1, h.2.2.2] using halpha56ends
      · simpa [h.2.1, h.2.2.2, Sym2.eq_swap] using halpha56ends
    have hbeta56ends' : G.ends beta56 = s(y5, y6) := by
      rcases horient with h | h
      · simpa [h.2.1, h.2.2.2] using hbeta56ends
      · simpa [h.2.1, h.2.2.2, Sym2.eq_swap] using hbeta56ends
    have ha1ends : G.ends a1 = s(y1, y2) := by
      let r : Fin S.length := ⟨1, by omega⟩
      have ht := M.trunk_edge_ends r (by simp [r]) (by simpa [hheight, r])
      have hs : r.succ = (⟨2, by omega⟩ : Fin (S.length + 1)) := Fin.ext rfl
      rw [hs] at ht
      simpa [a1, y1, y2, r] using ht
    have ha2ends : G.ends a2 = s(y2, y3) := by
      let r : Fin S.length := ⟨2, by omega⟩
      have ht := M.trunk_edge_ends r (by simp [r]) (by simpa [hheight, r])
      have hs : r.succ = (⟨3, by omega⟩ : Fin (S.length + 1)) := Fin.ext rfl
      rw [hs] at ht
      simpa [a2, y2, y3, r] using ht
    have ha3ends : G.ends a3 = s(y3, y4) := by
      let r : Fin S.length := ⟨3, by omega⟩
      have ht := M.trunk_edge_ends r (by simp [r]) (by simpa [hheight, r])
      have hs : r.succ = (⟨4, by omega⟩ : Fin (S.length + 1)) := Fin.ext rfl
      rw [hs] at ht
      simpa [a3, y3, y4, r] using ht
    have hlast : M.lastIndex = (⟨4, by omega⟩ : Fin (S.length + 1)) := by
      apply Fin.ext
      have hm := M.lastIndex_height
      rw [hheight] at hm
      simpa using hm
    have hclosingEnds : G.ends M.closingEdge = s(y4, y0) := by
      simpa [y4, y0, hlast] using M.closing_ends
    have hcycle := ScheideTrunkRotationCycle G k e psi S M hbal
    have ha1cycle : NormalCycleEdge M (⟨1, by omega⟩ : Fin M.height) = a1 := by
      simp [NormalCycleEdge, a1, hheight]
    have ha2cycle : NormalCycleEdge M (⟨2, by omega⟩ : Fin M.height) = a2 := by
      simp [NormalCycleEdge, a2, hheight]
    have ha3cycle : NormalCycleEdge M (⟨3, by omega⟩ : Fin M.height) = a3 := by
      simp [NormalCycleEdge, a3, hheight]
    have hcloseCycle : NormalCycleEdge M (⟨4, by omega⟩ : Fin M.height) =
        M.closingEdge := by
      simp [NormalCycleEdge, hheight]
    have ha1color : psi a1 = some M.alpha := by
      have hc := hcycle.2.2.2.2 (⟨1, by omega⟩ : Fin M.height) (by norm_num)
      simpa [ha1cycle] using hc
    have ha2color : psi a2 = some M.beta := by
      have hc := hcycle.2.2.2.2 (⟨2, by omega⟩ : Fin M.height) (by norm_num)
      have heven : ¬ Odd (2 : ℕ) := by decide
      simpa [ha2cycle, heven] using hc
    have ha3color : psi a3 = some M.alpha := by
      have hc := hcycle.2.2.2.2 (⟨3, by omega⟩ : Fin M.height) (by norm_num)
      have hodd : Odd (3 : ℕ) := by decide
      simpa [ha3cycle, hodd] using hc
    have hclosingColor : psi M.closingEdge = some M.beta := by
      have hc := hcycle.2.2.2.2 (⟨4, by omega⟩ : Fin M.height) (by norm_num)
      have heven : ¬ Odd (4 : ℕ) := by decide
      simpa [hcloseCycle, heven] using hc
    have hab : M.alpha ≠ M.beta := by
      intro hEq
      have hd := helem (hmem (⟨0, by omega⟩ : Fin (S.length + 1)))
        (hmem (⟨1, by omega⟩ : Fin (S.length + 1)))
        (by apply hvertex_ne; norm_num)
      exact (Finset.disjoint_left.mp hd) M.alpha_missing
        (by simpa [hEq] using M.beta_missing)
    have hg0alpha : g0 ≠ M.alpha := by
      intro hEq
      have hfne : f1 ≠ alpha56 := by
        intro heq
        have hpairs : s(y1, v1) = s(y5, y6) := by
          rw [← hf1ends', heq, halpha56ends']
        rcases Sym2.eq_iff.mp hpairs with hd | hs
        · exact (hvertex_ne (i := (⟨1, by omega⟩ : Fin (S.length + 1)))
            (j := (⟨5, by omega⟩ : Fin (S.length + 1))) (by norm_num))
            (by simpa [y1, y5] using hd.1)
        · exact (hvertex_ne (i := (⟨1, by omega⟩ : Fin (S.length + 1)))
            (j := (⟨6, by omega⟩ : Fin (S.length + 1))) (by norm_num))
            (by simpa [y1, y6] using hs.1)
      have hincf : Incident G v1 f1 := by
        rw [Incident, hf1ends']
        simp
      have hinca : Incident G v1 alpha56 := by
        rw [Incident, halpha56ends']
        rcases horient with h | h
        · simpa [h.2.1]
        · simpa [h.2.2.2]
      exact (hproper hfne ⟨v1, hincf, hinca⟩ hf1color)
        (by simpa [hEq] using halpha56color)
    have hg0beta : g0 ≠ M.beta := by
      intro hEq
      have hfne : f1 ≠ beta56 := by
        intro heq
        have hpairs : s(y1, v1) = s(y5, y6) := by
          rw [← hf1ends', heq, hbeta56ends']
        rcases Sym2.eq_iff.mp hpairs with hd | hs
        · exact (hvertex_ne (i := (⟨1, by omega⟩ : Fin (S.length + 1)))
            (j := (⟨5, by omega⟩ : Fin (S.length + 1))) (by norm_num))
            (by simpa [y1, y5] using hd.1)
        · exact (hvertex_ne (i := (⟨1, by omega⟩ : Fin (S.length + 1)))
            (j := (⟨6, by omega⟩ : Fin (S.length + 1))) (by norm_num))
            (by simpa [y1, y6] using hs.1)
      have hincf : Incident G v1 f1 := by
        rw [Incident, hf1ends']
        simp
      have hincb : Incident G v1 beta56 := by
        rw [Incident, hbeta56ends']
        rcases horient with h | h
        · simpa [h.2.1]
        · simpa [h.2.2.2]
      exact (hproper hfne ⟨v1, hincf, hincb⟩ hf1color)
        (by simpa [hEq] using hbeta56color)
    let r6' : Fin S.length := ⟨6, by omega⟩
    let r7' : Fin S.length := ⟨7, by omega⟩
    obtain ⟨w, g1, hc0color, hwmissing⟩ := M.global.2.1 r6' (by simp [r6'])
    have hc1color : psi c1 = some g1 := by
      have hp := hbal.2 4 (by omega) (by omega)
      have hc0' : psi c0 = some g1 := by simpa [c0, r6'] using hc0color
      simpa [c0, c1, r6', r7'] using hp.symm.trans hc0'
    have hc0color' : psi c0 = some g1 := by simpa [c0, r6'] using hc0color
    have hwmissing' : g1 ∈ MissingColors G psi
        (S.vertex ⟨w.val, by omega⟩) := by
      have hi : Fin.castLT w
          (Nat.lt_trans w.isLt (Nat.succ_lt_succ r6'.isLt)) =
          (⟨w.val, by omega⟩ : Fin (S.length + 1)) := Fin.ext rfl
      simpa [hi] using hwmissing
    obtain ⟨pc, hpc⟩ := S.attaches r6'
    let pc' : Fin 7 := ⟨pc.val, by simpa [r6'] using pc.isLt⟩
    have hc0ends : G.ends c0 = s(y7, S.vertex ⟨pc'.val, by omega⟩) := by
      have hi : Fin.castLT pc
          (Nat.lt_trans pc.isLt (Nat.succ_lt_succ r6'.isLt)) =
          (⟨pc'.val, by omega⟩ : Fin (S.length + 1)) := Fin.ext rfl
      simpa [c0, y7, r6', hi] using hpc
    have hc0_ne_f3 : c0 ≠ f3 := by
      intro hEq
      have hpairs : s(y7, S.vertex ⟨pc'.val, by omega⟩) = s(y2, y3) := by
        rw [← hc0ends, hEq, hf3ends']
      rcases Sym2.eq_iff.mp hpairs with hd | hs
      · exact (hvertex_ne (i := (⟨7, by omega⟩ : Fin (S.length + 1)))
          (j := (⟨2, by omega⟩ : Fin (S.length + 1))) (by norm_num))
          (by simpa [y7, y2] using hd.1)
      · exact (hvertex_ne (i := (⟨7, by omega⟩ : Fin (S.length + 1)))
          (j := (⟨3, by omega⟩ : Fin (S.length + 1))) (by norm_num))
          (by simpa [y7, y3] using hs.1)
    have hc0_ne_alpha56 : c0 ≠ alpha56 := by
      intro hEq
      have hpairs : s(y7, S.vertex ⟨pc'.val, by omega⟩) = s(y5, y6) := by
        rw [← hc0ends, hEq, halpha56ends']
      rcases Sym2.eq_iff.mp hpairs with hd | hs
      · exact (hvertex_ne (i := (⟨7, by omega⟩ : Fin (S.length + 1)))
          (j := (⟨5, by omega⟩ : Fin (S.length + 1))) (by norm_num))
          (by simpa [y7, y5] using hd.1)
      · exact (hvertex_ne (i := (⟨7, by omega⟩ : Fin (S.length + 1)))
          (j := (⟨6, by omega⟩ : Fin (S.length + 1))) (by norm_num))
          (by simpa [y7, y6] using hs.1)
    have hc0_ne_beta56 : c0 ≠ beta56 := by
      intro hEq
      have hpairs : s(y7, S.vertex ⟨pc'.val, by omega⟩) = s(y5, y6) := by
        rw [← hc0ends, hEq, hbeta56ends']
      rcases Sym2.eq_iff.mp hpairs with hd | hs
      · exact (hvertex_ne (i := (⟨7, by omega⟩ : Fin (S.length + 1)))
          (j := (⟨5, by omega⟩ : Fin (S.length + 1))) (by norm_num))
          (by simpa [y7, y5] using hd.1)
      · exact (hvertex_ne (i := (⟨7, by omega⟩ : Fin (S.length + 1)))
          (j := (⟨6, by omega⟩ : Fin (S.length + 1))) (by norm_num))
          (by simpa [y7, y6] using hs.1)
    have hc0_ne_closing : c0 ≠ M.closingEdge := by
      intro hEq
      have hpairs : s(y7, S.vertex ⟨pc'.val, by omega⟩) = s(y4, y0) := by
        rw [← hc0ends, hEq, hclosingEnds]
      rcases Sym2.eq_iff.mp hpairs with hd | hs
      · exact (hvertex_ne (i := (⟨7, by omega⟩ : Fin (S.length + 1)))
          (j := (⟨4, by omega⟩ : Fin (S.length + 1))) (by norm_num))
          (by simpa [y7, y4] using hd.1)
      · exact (hvertex_ne (i := (⟨7, by omega⟩ : Fin (S.length + 1)))
          (j := (⟨0, by omega⟩ : Fin (S.length + 1))) (by norm_num))
          (by simpa [y7, y0] using hs.1)
    have no_y7_of_ends {f : E} {u v : V} (hf : G.ends f = s(u, v))
        (hu : u ≠ y7) (hv : v ≠ y7) : ¬ Incident G y7 f := by
      intro hinc
      rw [Incident, hf] at hinc
      rcases Sym2.mem_iff.mp hinc with h | h
      · exact hu h.symm
      · exact hv h.symm
    have hy0_7 : y0 ≠ y7 := by apply hvertex_ne; norm_num
    have hy1_7 : y1 ≠ y7 := by apply hvertex_ne; norm_num
    have hy2_7 : y2 ≠ y7 := by apply hvertex_ne; norm_num
    have hy3_7 : y3 ≠ y7 := by apply hvertex_ne; norm_num
    have hy4_7 : y4 ≠ y7 := by apply hvertex_ne; norm_num
    have hy5_7 : y5 ≠ y7 := by apply hvertex_ne; norm_num
    have hy6_7 : y6 ≠ y7 := by apply hvertex_ne; norm_num
    have hv1_7 : v1 ≠ y7 := by
      rcases horient with h | h
      · exact h.2.1 ▸ hy5_7
      · exact h.2.2.2 ▸ hy6_7
    have hv2_7 : v2 ≠ y7 := by
      rcases horient with h | h
      · exact h.2.2.2 ▸ hy6_7
      · exact h.2.1 ▸ hy5_7
    have hno_f1 : ¬ Incident G y7 f1 :=
      no_y7_of_ends hf1ends' hy1_7 hv1_7
    have hno_f2 : ¬ Incident G y7 f2 :=
      no_y7_of_ends hf2ends' hy4_7 hv2_7
    have hno_f3 : ¬ Incident G y7 f3 :=
      no_y7_of_ends hf3ends' hy2_7 hy3_7
    have hno_a1 : ¬ Incident G y7 a1 :=
      no_y7_of_ends ha1ends hy1_7 hy2_7
    have hno_a2 : ¬ Incident G y7 a2 :=
      no_y7_of_ends ha2ends hy2_7 hy3_7
    have hno_a3 : ¬ Incident G y7 a3 :=
      no_y7_of_ends ha3ends hy3_7 hy4_7
    have hno_close : ¬ Incident G y7 M.closingEdge :=
      no_y7_of_ends hclosingEnds hy4_7 hy0_7
    have hno_alpha56 : ¬ Incident G y7 alpha56 :=
      no_y7_of_ends halpha56ends' hy5_7 hy6_7
    have hno_beta56 : ¬ Incident G y7 beta56 :=
      no_y7_of_ends hbeta56ends' hy5_7 hy6_7
    have hp0lt : p0.val < 5 := by simpa using p0.isLt
    have hp1lt : p1.val < 5 := by
      have hp : p1.val < 6 := by simpa using p1.isLt
      omega
    have hp0vertex_ne7 : S.vertex (Fin.castLT p0
        (Nat.lt_trans p0.isLt
          (Nat.succ_lt_succ (⟨4, by omega⟩ : Fin S.length).isLt))) ≠ y7 := by
      apply hvertex_ne
      apply Fin.ne_of_val_ne
      change p0.val ≠ 7
      omega
    have hp1vertex_ne7 : S.vertex (Fin.castLT p1
        (Nat.lt_trans p1.isLt
          (Nat.succ_lt_succ (⟨5, by omega⟩ : Fin S.length).isLt))) ≠ y7 := by
      apply hvertex_ne
      apply Fin.ne_of_val_ne
      change p1.val ≠ 7
      omega
    have hno_b0 : ¬ Incident G y7 b0 :=
      no_y7_of_ends hb0ends hy5_7 hp0vertex_ne7
    have hno_b1 : ¬ Incident G y7 b1 :=
      no_y7_of_ends hb1ends hy6_7 hp1vertex_ne7
    have second_ne_of_matching (c : Fin k) (m : Fin 7)
        (hcmiss : c ∈ MissingColors G psi
          (S.vertex ⟨m.val, by omega⟩))
        (hcover : ∀ q : Fin 7, q ≠ m →
          ∃ f : E, f ≠ c0 ∧ Incident G (S.vertex ⟨q.val, by omega⟩) f ∧
            psi f = some c ∧ ¬ Incident G y7 f) : g1 ≠ c := by
      intro hEq
      have hwEq : w.val = m.val := by
        by_contra hne
        have hvne : S.vertex ⟨w.val, by omega⟩ ≠
            S.vertex ⟨m.val, by omega⟩ := by
          apply hvertex_ne
          exact Fin.ne_of_val_ne hne
        have hd := helem (hmem (⟨w.val, by omega⟩ : Fin (S.length + 1)))
          (hmem (⟨m.val, by omega⟩ : Fin (S.length + 1))) hvne
        exact (Finset.disjoint_left.mp hd) hwmissing'
          (by simpa [hEq] using hcmiss)
      have hpcne : pc' ≠ m := by
        intro hpm
        have hinc : Incident G (S.vertex ⟨m.val, by omega⟩) c0 := by
          rw [Incident, hc0ends]
          have hv : S.vertex ⟨pc'.val, by omega⟩ =
              S.vertex ⟨m.val, by omega⟩ := by
            apply congrArg S.vertex
            apply Fin.ext
            simpa using congrArg Fin.val hpm
          rw [hv]
          simp
        exact (missing_excludes hcmiss hinc) (by simpa [hEq] using hc0color')
      obtain ⟨f, hfc0, hincf, hfcolor, _⟩ := hcover pc' hpcne
      have hincc : Incident G (S.vertex ⟨pc'.val, by omega⟩) c0 := by
        rw [Incident, hc0ends]
        simp
      exact (hproper hfc0.symm ⟨S.vertex ⟨pc'.val, by omega⟩, hincc,
        hincf⟩ (by simpa [hEq] using hc0color')) hfcolor
    have hcoverG0 : ∀ q : Fin 7, q ≠ (0 : Fin 7) →
        ∃ f : E, f ≠ c0 ∧ Incident G (S.vertex ⟨q.val, by omega⟩) f ∧
          psi f = some g0 ∧ ¬ Incident G y7 f := by
      intro q hq
      have hcases : q.val = 1 ∨ q.val = 2 ∨ q.val = 3 ∨
          q.val = 4 ∨ q.val = 5 ∨ q.val = 6 := by
        have hq0 : q.val ≠ 0 := by intro h; apply hq; apply Fin.ext; exact h
        omega
      rcases hcases with h | h | h | h | h | h
      · refine ⟨f1, ?_, ?_, hf1color, hno_f1⟩
        · rcases horient with ho | ho
          · rw [← ho.1]
            apply hedge_ne
            norm_num
          · rw [← ho.2.2.1]
            apply hedge_ne
            norm_num
        · rw [Incident, hf1ends']
          have hv : S.vertex ⟨q.val, by omega⟩ = y1 := by
            apply congrArg S.vertex; apply Fin.ext; simpa [y1] using h
          rw [hv]
          simp
      · refine ⟨f3, hc0_ne_f3.symm, ?_, hf3color, hno_f3⟩
        rw [Incident, hf3ends']
        have hv : S.vertex ⟨q.val, by omega⟩ = y2 := by
          apply congrArg S.vertex; apply Fin.ext; simpa [y2] using h
        rw [hv]
        simp
      · refine ⟨f3, hc0_ne_f3.symm, ?_, hf3color, hno_f3⟩
        rw [Incident, hf3ends']
        have hv : S.vertex ⟨q.val, by omega⟩ = y3 := by
          apply congrArg S.vertex; apply Fin.ext; simpa [y3] using h
        rw [hv]
        simp
      · refine ⟨f2, ?_, ?_, hf2color, hno_f2⟩
        · rcases horient with ho | ho
          · rw [← ho.2.2.1]
            apply hedge_ne
            norm_num
          · rw [← ho.1]
            apply hedge_ne
            norm_num
        · rw [Incident, hf2ends']
          have hv : S.vertex ⟨q.val, by omega⟩ = y4 := by
            apply congrArg S.vertex; apply Fin.ext; simpa [y4] using h
          rw [hv]
          simp
      · refine ⟨b0, ?_, ?_, h4', hno_b0⟩
        · apply hedge_ne
          norm_num
        · rw [Incident, hb0ends]
          have hv : S.vertex ⟨q.val, by omega⟩ = y5 := by
            apply congrArg S.vertex; apply Fin.ext; simpa [y5] using h
          rw [hv]
          simp
      · refine ⟨b1, ?_, ?_, h5', hno_b1⟩
        · apply hedge_ne
          norm_num
        · rw [Incident, hb1ends]
          have hv : S.vertex ⟨q.val, by omega⟩ = y6 := by
            apply congrArg S.vertex; apply Fin.ext; simpa [y6] using h
          rw [hv]
          simp
    have hcoverAlpha : ∀ q : Fin 7, q ≠ (0 : Fin 7) →
        ∃ f : E, f ≠ c0 ∧ Incident G (S.vertex ⟨q.val, by omega⟩) f ∧
          psi f = some M.alpha ∧ ¬ Incident G y7 f := by
      intro q hq
      have hcases : q.val = 1 ∨ q.val = 2 ∨ q.val = 3 ∨
          q.val = 4 ∨ q.val = 5 ∨ q.val = 6 := by
        have hq0 : q.val ≠ 0 := by intro h; apply hq; apply Fin.ext; exact h
        omega
      rcases hcases with h | h | h | h | h | h
      · refine ⟨a1, by apply hedge_ne; norm_num, ?_, ha1color, hno_a1⟩
        rw [Incident, ha1ends]
        have hv : S.vertex ⟨q.val, by omega⟩ = y1 := by
          apply congrArg S.vertex; apply Fin.ext; simpa [y1] using h
        rw [hv]; simp
      · refine ⟨a1, by apply hedge_ne; norm_num, ?_, ha1color, hno_a1⟩
        rw [Incident, ha1ends]
        have hv : S.vertex ⟨q.val, by omega⟩ = y2 := by
          apply congrArg S.vertex; apply Fin.ext; simpa [y2] using h
        rw [hv]; simp
      · refine ⟨a3, by apply hedge_ne; norm_num, ?_, ha3color, hno_a3⟩
        rw [Incident, ha3ends]
        have hv : S.vertex ⟨q.val, by omega⟩ = y3 := by
          apply congrArg S.vertex; apply Fin.ext; simpa [y3] using h
        rw [hv]; simp
      · refine ⟨a3, by apply hedge_ne; norm_num, ?_, ha3color, hno_a3⟩
        rw [Incident, ha3ends]
        have hv : S.vertex ⟨q.val, by omega⟩ = y4 := by
          apply congrArg S.vertex; apply Fin.ext; simpa [y4] using h
        rw [hv]; simp
      · refine ⟨alpha56, hc0_ne_alpha56.symm, ?_, halpha56color, hno_alpha56⟩
        rw [Incident, halpha56ends']
        have hv : S.vertex ⟨q.val, by omega⟩ = y5 := by
          apply congrArg S.vertex; apply Fin.ext; simpa [y5] using h
        rw [hv]; simp
      · refine ⟨alpha56, hc0_ne_alpha56.symm, ?_, halpha56color, hno_alpha56⟩
        rw [Incident, halpha56ends']
        have hv : S.vertex ⟨q.val, by omega⟩ = y6 := by
          apply congrArg S.vertex; apply Fin.ext; simpa [y6] using h
        rw [hv]; simp
    have hcoverBeta : ∀ q : Fin 7, q ≠ (1 : Fin 7) →
        ∃ f : E, f ≠ c0 ∧ Incident G (S.vertex ⟨q.val, by omega⟩) f ∧
          psi f = some M.beta ∧ ¬ Incident G y7 f := by
      intro q hq
      have hcases : q.val = 0 ∨ q.val = 2 ∨ q.val = 3 ∨
          q.val = 4 ∨ q.val = 5 ∨ q.val = 6 := by
        have hq1 : q.val ≠ 1 := by intro h; apply hq; apply Fin.ext; exact h
        omega
      rcases hcases with h | h | h | h | h | h
      · refine ⟨M.closingEdge, hc0_ne_closing.symm, ?_, hclosingColor, hno_close⟩
        rw [Incident, hclosingEnds]
        have hv : S.vertex ⟨q.val, by omega⟩ = y0 := by
          apply congrArg S.vertex; apply Fin.ext; simpa [y0] using h
        rw [hv]; simp
      · refine ⟨a2, by apply hedge_ne; norm_num, ?_, ha2color, hno_a2⟩
        rw [Incident, ha2ends]
        have hv : S.vertex ⟨q.val, by omega⟩ = y2 := by
          apply congrArg S.vertex; apply Fin.ext; simpa [y2] using h
        rw [hv]; simp
      · refine ⟨a2, by apply hedge_ne; norm_num, ?_, ha2color, hno_a2⟩
        rw [Incident, ha2ends]
        have hv : S.vertex ⟨q.val, by omega⟩ = y3 := by
          apply congrArg S.vertex; apply Fin.ext; simpa [y3] using h
        rw [hv]; simp
      · refine ⟨M.closingEdge, hc0_ne_closing.symm, ?_, hclosingColor, hno_close⟩
        rw [Incident, hclosingEnds]
        have hv : S.vertex ⟨q.val, by omega⟩ = y4 := by
          apply congrArg S.vertex; apply Fin.ext; simpa [y4] using h
        rw [hv]; simp
      · refine ⟨beta56, hc0_ne_beta56.symm, ?_, hbeta56color, hno_beta56⟩
        rw [Incident, hbeta56ends']
        have hv : S.vertex ⟨q.val, by omega⟩ = y5 := by
          apply congrArg S.vertex; apply Fin.ext; simpa [y5] using h
        rw [hv]; simp
      · refine ⟨beta56, hc0_ne_beta56.symm, ?_, hbeta56color, hno_beta56⟩
        rw [Incident, hbeta56ends']
        have hv : S.vertex ⟨q.val, by omega⟩ = y6 := by
          apply congrArg S.vertex; apply Fin.ext; simpa [y6] using h
        rw [hv]; simp
    have hg10 : g1 ≠ g0 :=
      second_ne_of_matching g0 (0 : Fin 7) (by simpa [y0] using hg0') hcoverG0
    have hg1alpha : g1 ≠ M.alpha :=
      second_ne_of_matching M.alpha (0 : Fin 7)
        (by simpa [y0] using M.alpha_missing) hcoverAlpha
    have hg1beta : g1 ≠ M.beta :=
      second_ne_of_matching M.beta (1 : Fin 7)
        (by simpa [y1] using M.beta_missing) hcoverBeta
    have last_pair_edge (c : Fin k) (m : Fin 7)
        (hcmiss : c ∈ MissingColors G psi
          (S.vertex ⟨m.val, by omega⟩))
        (hcover : ∀ q : Fin 7, q ≠ m →
          ∃ f : E, f ≠ c0 ∧ Incident G (S.vertex ⟨q.val, by omega⟩) f ∧
            psi f = some c ∧ ¬ Incident G y7 f) :
        ∃ f : E, G.ends f = s(y7, y8) ∧ psi f = some c := by
      have hmMem : S.vertex ⟨m.val, by omega⟩ ∈ TreeSequenceVertexSet S :=
        hmem (⟨m.val, by omega⟩ : Fin (S.length + 1))
      have hy7Mem : y7 ∈ TreeSequenceVertexSet S := by
        simpa [y7] using hmem (⟨7, by omega⟩ : Fin (S.length + 1))
      have hym7 : S.vertex ⟨m.val, by omega⟩ ≠ y7 := by
        apply hvertex_ne
        apply Fin.ne_of_val_ne
        change m.val ≠ 7
        omega
      have hcnotmissing : c ∉ MissingColors G psi y7 := by
        intro hc7
        have hd := helem hmMem hy7Mem hym7
        exact (Finset.disjoint_left.mp hd) hcmiss hc7
      have hcpresent : c ∈ PresentColors G psi y7 := by
        simpa [MissingColors] using hcnotmissing
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
        true_and] at hcpresent
      obtain ⟨f, hfinc, hfcolor⟩ := hcpresent
      obtain ⟨z, hfends⟩ := Sym2.mem_iff_exists.mp hfinc
      have hzT : z ∈ TreeSequenceVertexSet S := by
        by_contra hz
        have hfBoundary : f ∈ BoundaryEdges G (TreeSequenceVertexSet S) := by
          simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact ⟨y7, hy7Mem, z, hz, hfends⟩
        exact (hclosed hfBoundary hmMem hfcolor) hcmiss
      obtain ⟨q, -, hqz⟩ := Finset.mem_image.mp
        (show z ∈ Finset.image S.vertex Finset.univ from by
          simpa [TreeSequenceVertexSet] using hzT)
      have hq8 : q.val = 8 := by
        have hqbound : q.val < 9 := by
          calc
            q.val < S.length + 1 := q.isLt
            _ = 9 := by omega
        by_contra hne
        by_cases hq7 : q.val = 7
        · have hz7 : z = y7 := by
            rw [← hqz]
            apply congrArg S.vertex
            apply Fin.ext
            simpa [y7] using hq7
          exact G.loopless f y7 (by simpa [hz7] using hfends)
        · have hqlt : q.val < 7 := by omega
          let q7 : Fin 7 := ⟨q.val, hqlt⟩
          have hzq : z = S.vertex ⟨q7.val, by omega⟩ := by
            calc
              z = S.vertex q := hqz.symm
              _ = S.vertex ⟨q7.val, by omega⟩ := by
                apply congrArg S.vertex
                apply Fin.ext
                rfl
          by_cases hqm : q7 = m
          · have hincm : Incident G (S.vertex ⟨m.val, by omega⟩) f := by
              rw [Incident, hfends, hzq]
              have hv : S.vertex ⟨q7.val, by omega⟩ =
                  S.vertex ⟨m.val, by omega⟩ := by
                apply congrArg S.vertex
                apply Fin.ext
                simpa using congrArg Fin.val hqm
              rw [hv]
              simp
            exact (missing_excludes hcmiss hincm) hfcolor
          · obtain ⟨g, _, hginc, hgcolor, hgno7⟩ := hcover q7 hqm
            have hfne : f ≠ g := by
              intro heq
              exact hgno7 (heq ▸ hfinc)
            have hfincq : Incident G (S.vertex ⟨q7.val, by omega⟩) f := by
              rw [Incident, hfends, hzq]
              simp
            exact (hproper hfne ⟨S.vertex ⟨q7.val, by omega⟩,
              hfincq, hginc⟩ hfcolor) hgcolor
      have hzy8 : z = y8 := by
        rw [← hqz]
        apply congrArg S.vertex
        apply Fin.ext
        simpa [y8] using hq8
      exact ⟨f, by simpa [hzy8] using hfends, hfcolor⟩
    obtain ⟨g0last, hg0lastEnds, hg0lastColor⟩ :=
      last_pair_edge g0 (0 : Fin 7) (by simpa [y0] using hg0') hcoverG0
    obtain ⟨alphaLast, halphaLastEnds, halphaLastColor⟩ :=
      last_pair_edge M.alpha (0 : Fin 7)
        (by simpa [y0] using M.alpha_missing) hcoverAlpha
    obtain ⟨betaLast, hbetaLastEnds, hbetaLastColor⟩ :=
      last_pair_edge M.beta (1 : Fin 7)
        (by simpa [y1] using M.beta_missing) hcoverBeta
    have hg0AlphaLast : g0last ≠ alphaLast := by
      intro hEq
      have hc : some g0 = some M.alpha := by
        rw [← hg0lastColor, hEq, halphaLastColor]
      exact hg0alpha (Option.some.inj hc)
    have hg0BetaLast : g0last ≠ betaLast := by
      intro hEq
      have hc : some g0 = some M.beta := by
        rw [← hg0lastColor, hEq, hbetaLastColor]
      exact hg0beta (Option.some.inj hc)
    have hAlphaBetaLast : alphaLast ≠ betaLast := by
      intro hEq
      have hc : some M.alpha = some M.beta := by
        rw [← halphaLastColor, hEq, hbetaLastColor]
      exact hab (Option.some.inj hc)
    let a0 : E := S.edge ⟨0, by omega⟩
    have ha0eq : a0 = e := by simpa [a0] using S.first_edge
    have ha0color : psi a0 = none := by
      rw [ha0eq]
      exact M.global.1.2.2.2.2.1
    obtain ⟨pa0, hpa0⟩ := S.attaches (⟨0, by omega⟩ : Fin S.length)
    have hpa0zero : pa0 = 0 := Fin.eq_zero pa0
    have hpa0cast :
        (Fin.castLT pa0 (Nat.lt_trans pa0.isLt
          (Nat.succ_lt_succ (show 0 < S.length by omega))) :
            Fin (S.length + 1)) =
          (⟨0, Nat.zero_lt_succ S.length⟩ : Fin (S.length + 1)) := by
      apply Fin.ext
      simp [hpa0zero]
    have ha0ends : G.ends a0 = s(y1, y0) := by
      simpa [a0, y0, y1, hpa0cast] using hpa0
    have hbeta_a0 : beta56 ≠ a0 := by
      intro hEq
      rw [hEq, ha0color] at hbeta56color
      simp at hbeta56color
    have hbeta_f1 : beta56 ≠ f1 := by
      intro hEq
      have hc : some M.beta = some g0 := by
        rw [← hbeta56color, hEq, hf1color]
      exact hg0beta (Option.some.inj hc).symm
    have hbeta_f2 : beta56 ≠ f2 := by
      intro hEq
      have hc : some M.beta = some g0 := by
        rw [← hbeta56color, hEq, hf2color]
      exact hg0beta (Option.some.inj hc).symm
    have hbeta_a1 : beta56 ≠ a1 := by
      intro hEq
      have hc : some M.beta = some M.alpha := by
        rw [← hbeta56color, hEq, ha1color]
      exact hab (Option.some.inj hc).symm
    have hbeta_a3 : beta56 ≠ a3 := by
      intro hEq
      have hc : some M.beta = some M.alpha := by
        rw [← hbeta56color, hEq, ha3color]
      exact hab (Option.some.inj hc).symm
    have hbeta_c0 : beta56 ≠ c0 := by
      intro hEq
      have hc : some M.beta = some g1 := by
        rw [← hbeta56color, hEq, hc0color']
      exact hg1beta (Option.some.inj hc).symm
    have hbeta_c1 : beta56 ≠ c1 := by
      intro hEq
      have hc : some M.beta = some g1 := by
        rw [← hbeta56color, hEq, hc1color]
      exact hg1beta (Option.some.inj hc).symm
    have rebase (hwbase : 5 ≤ w.val) :
        ∃ (S' : TreeSequence G e)
          (M' : NormalGlobalMaximumTriple G k e psi S')
          (_ : S'.length = 8) (_ : M'.height = 5),
          BalancedGlobalMaximumTriple M' ∧
          S'.vertex ⟨0, by omega⟩ = y0 ∧
          S'.vertex ⟨1, by omega⟩ = y1 ∧
          S'.vertex ⟨2, by omega⟩ = v1 ∧
          S'.vertex ⟨3, by omega⟩ = v2 ∧
          S'.vertex ⟨4, by omega⟩ = y4 ∧
          S'.vertex ⟨5, by omega⟩ = y2 ∧
          S'.vertex ⟨6, by omega⟩ = y3 ∧
          S'.vertex ⟨7, by omega⟩ = y7 ∧
          S'.vertex ⟨8, by omega⟩ = y8 ∧
          S'.edge ⟨0, by omega⟩ = a0 ∧
          S'.edge ⟨1, by omega⟩ = f1 ∧
          S'.edge ⟨2, by omega⟩ = beta56 ∧
          S'.edge ⟨3, by omega⟩ = f2 ∧
          S'.edge ⟨4, by omega⟩ = a1 ∧
          S'.edge ⟨5, by omega⟩ = a3 ∧
          S'.edge ⟨6, by omega⟩ = c0 ∧
          S'.edge ⟨7, by omega⟩ = c1 ∧
          M'.alpha = g0 ∧ M'.beta = M.beta := by
      have hwcases : w.val = 5 ∨ w.val = 6 := by
        have hwlt : w.val < 7 := by simpa [r6'] using w.isLt
        omega
      let cast9 : Fin 9 ≃ Fin (S.length + 1) := finCongr (by omega)
      let permA : Equiv.Perm (Fin 9) :=
        (Equiv.swap 2 5).trans (Equiv.swap 3 6)
      let permB : Equiv.Perm (Fin 9) :=
        ((Equiv.swap 2 6).trans (Equiv.swap 2 3)).trans (Equiv.swap 2 5)
      let newVertex : Fin 9 → V := fun i ↦
        if b0 = f1 then S.vertex (cast9 (permA i))
        else S.vertex (cast9 (permB i))
      let edgeList : List E := [a0, f1, beta56, f2, a1, a3, c0, c1]
      have hedgeListLength : edgeList.length = 8 := by rfl
      let newEdge : Fin 8 → E := fun i ↦
        edgeList.get (Fin.cast hedgeListLength.symm i)
      have hselectA (hb : b0 = f1) :
          y5 = v1 ∧ b1 = f2 ∧ y6 = v2 := by
        rcases horient with ho | ho
        · exact ⟨ho.2.1, ho.2.2.1, ho.2.2.2⟩
        · exfalso
          apply hb01ne
          calc
            b0 = f1 := hb
            _ = b1 := ho.2.2.1.symm
      have hselectB (hb : b0 ≠ f1) :
          y5 = v2 ∧ b1 = f1 ∧ y6 = v1 := by
        rcases horient with ho | ho
        · exact (hb ho.1).elim
        · exact ⟨ho.2.1, ho.2.2.1, ho.2.2.2⟩
      have vertex_cast9 (i : Fin 9) (q : Fin (S.length + 1))
          (hv : i.val = q.val) : S.vertex (cast9 i) = S.vertex q := by
        apply congrArg S.vertex
        apply Fin.ext
        simpa [cast9] using hv
      have nv0 : newVertex 0 = y0 := by
        by_cases hb : b0 = f1
        · simp only [newVertex, if_pos hb, y0]
          apply vertex_cast9
          simp [permA, Equiv.swap_apply_def]
        · simp only [newVertex, if_neg hb, y0]
          apply vertex_cast9
          simp [permB, Equiv.swap_apply_def]
      have nv1 : newVertex 1 = y1 := by
        by_cases hb : b0 = f1
        · simp only [newVertex, if_pos hb, y1]
          apply vertex_cast9
          simp [permA, Equiv.swap_apply_def]
        · simp only [newVertex, if_neg hb, y1]
          apply vertex_cast9
          simp [permB, Equiv.swap_apply_def]
      have nv2 : newVertex 2 = v1 := by
        by_cases hb : b0 = f1
        · calc
            newVertex 2 = y5 := by
              simp only [newVertex, if_pos hb, y5]
              apply vertex_cast9
              simp [permA, Equiv.swap_apply_def]
            _ = v1 := (hselectA hb).1
        · calc
            newVertex 2 = y6 := by
              simp only [newVertex, if_neg hb, y6]
              apply vertex_cast9
              simp [permB, Equiv.swap_apply_def]
            _ = v1 := (hselectB hb).2.2
      have nv3 : newVertex 3 = v2 := by
        by_cases hb : b0 = f1
        · calc
            newVertex 3 = y6 := by
              simp only [newVertex, if_pos hb, y6]
              apply vertex_cast9
              simp [permA, Equiv.swap_apply_def]
            _ = v2 := (hselectA hb).2.2
        · calc
            newVertex 3 = y5 := by
              simp only [newVertex, if_neg hb, y5]
              apply vertex_cast9
              simp [permB, Equiv.swap_apply_def]
            _ = v2 := (hselectB hb).1
      have nv4 : newVertex 4 = y4 := by
        by_cases hb : b0 = f1
        · simp only [newVertex, if_pos hb, y4]
          apply vertex_cast9
          simp [permA, Equiv.swap_apply_def]
        · simp only [newVertex, if_neg hb, y4]
          apply vertex_cast9
          simp [permB, Equiv.swap_apply_def]
      have nv5 : newVertex 5 = y2 := by
        by_cases hb : b0 = f1
        · simp only [newVertex, if_pos hb, y2]
          apply vertex_cast9
          simp [permA, Equiv.swap_apply_def]
        · simp only [newVertex, if_neg hb, y2]
          apply vertex_cast9
          simp [permB, Equiv.swap_apply_def]
      have nv6 : newVertex 6 = y3 := by
        by_cases hb : b0 = f1
        · simp only [newVertex, if_pos hb, y3]
          apply vertex_cast9
          simp [permA, Equiv.swap_apply_def]
        · simp only [newVertex, if_neg hb, y3]
          apply vertex_cast9
          simp [permB, Equiv.swap_apply_def]
      have nv7 : newVertex 7 = y7 := by
        by_cases hb : b0 = f1
        · simp only [newVertex, if_pos hb, y7]
          apply vertex_cast9
          simp [permA, Equiv.swap_apply_def]
        · simp only [newVertex, if_neg hb, y7]
          apply vertex_cast9
          simp [permB, Equiv.swap_apply_def]
      have nv8 : newVertex 8 = y8 := by
        by_cases hb : b0 = f1
        · simp only [newVertex, if_pos hb, y8]
          apply vertex_cast9
          simp [permA, Equiv.swap_apply_def]
        · simp only [newVertex, if_neg hb, y8]
          apply vertex_cast9
          simp [permB, Equiv.swap_apply_def]
      have ne0 : newEdge 0 = a0 := rfl
      have ne1 : newEdge 1 = f1 := rfl
      have ne2 : newEdge 2 = beta56 := rfl
      have ne3 : newEdge 3 = f2 := rfl
      have ne4 : newEdge 4 = a1 := rfl
      have ne5 : newEdge 5 = a3 := rfl
      have ne6 : newEdge 6 = c0 := rfl
      have ne7 : newEdge 7 = c1 := rfl
      have hvertex_iff (i j : Fin (S.length + 1)) :
          S.vertex i = S.vertex j ↔ i = j := S.vertex_injective.eq_iff
      have hedge_iff (i j : Fin S.length) :
          S.edge i = S.edge j ↔ i = j := S.edge_injective.eq_iff
      have newVertex_injective : Function.Injective newVertex := by
        by_cases hb : b0 = f1
        · intro i j hij
          simp only [newVertex, if_pos hb] at hij
          exact permA.injective (cast9.injective (S.vertex_injective hij))
        · intro i j hij
          simp only [newVertex, if_neg hb] at hij
          exact permB.injective (cast9.injective (S.vertex_injective hij))
      have newEdge_injective : Function.Injective newEdge := by
        have hnodup : edgeList.Nodup := by
          rcases horient with ho | ho
          · have hb0beta : b0 ≠ beta56 := by
              intro hh
              exact hbeta_f1 (hh.symm.trans ho.1)
            have hbeta_b1 : beta56 ≠ b1 := by
              intro hh
              exact hbeta_f2 (hh.trans ho.2.2.1)
            simp [edgeList, ← ha0eq, ← ho.1, ← ho.2.2.1, a0, a1,
              a3, b0, b1, c0, c1, hedge_iff, hbeta_a0, hbeta_f1,
              hbeta_f2, hbeta_a1, hbeta_a3, hbeta_c0, hbeta_c1,
              Ne.symm hbeta_a0, Ne.symm hbeta_f1, Ne.symm hbeta_f2,
              Ne.symm hbeta_a1, Ne.symm hbeta_a3, Ne.symm hbeta_c0,
              Ne.symm hbeta_c1, hb0beta, hbeta_b1]
          · have hb1beta : b1 ≠ beta56 := by
              intro hh
              exact hbeta_f1 (hh.symm.trans ho.2.2.1)
            have hbeta_b0 : beta56 ≠ b0 := by
              intro hh
              exact hbeta_f2 (hh.trans ho.1)
            simp [edgeList, ← ha0eq, ← ho.2.2.1, ← ho.1, a0, a1,
              a3, b0, b1, c0, c1, hedge_iff, hbeta_a0, hbeta_f1,
              hbeta_f2, hbeta_a1, hbeta_a3, hbeta_c0, hbeta_c1,
              Ne.symm hbeta_a0, Ne.symm hbeta_f1, Ne.symm hbeta_f2,
              Ne.symm hbeta_a1, Ne.symm hbeta_a3, Ne.symm hbeta_c0,
              Ne.symm hbeta_c1, hb1beta, hbeta_b0]
        intro i j hij
        have hcast := hnodup.injective_get hij
        apply Fin.ext
        simpa using congrArg Fin.val hcast
      have firstSeven : ∀ q : Fin 7, ∃ t : Fin 7,
          newVertex (Fin.castLE (by norm_num : 7 ≤ 9) t) =
            S.vertex ⟨q.val, by omega⟩ := by
        intro q
        fin_cases q
        · exact ⟨0, by change newVertex 0 = y0; exact nv0⟩
        · exact ⟨1, by change newVertex 1 = y1; exact nv1⟩
        · exact ⟨5, by change newVertex 5 = y2; exact nv5⟩
        · exact ⟨6, by change newVertex 6 = y3; exact nv6⟩
        · exact ⟨4, by change newVertex 4 = y4; exact nv4⟩
        · rcases horient with ho | ho
          · exact ⟨2, by change newVertex 2 = y5; rw [nv2]; exact ho.2.1.symm⟩
          · exact ⟨3, by change newVertex 3 = y5; rw [nv3]; exact ho.2.1.symm⟩
        · rcases horient with ho | ho
          · exact ⟨3, by change newVertex 3 = y6; rw [nv3]; exact ho.2.2.2.symm⟩
          · exact ⟨2, by change newVertex 2 = y6; rw [nv2]; exact ho.2.2.2.symm⟩
      obtain ⟨pc1, hpc1⟩ := S.attaches r7'
      let pc1' : Fin 8 := ⟨pc1.val, by simpa [r7'] using pc1.isLt⟩
      have hpc1cast : Fin.castLT pc1
          (Nat.lt_trans pc1.isLt (Nat.succ_lt_succ r7'.isLt)) =
          (⟨pc1'.val, by omega⟩ : Fin (S.length + 1)) := by
        apply Fin.ext
        rfl
      have hc1ends : G.ends c1 = s(y8, S.vertex ⟨pc1'.val, by omega⟩) := by
        simpa [c1, r7', y8, hpc1cast] using hpc1
      have firstEight : ∀ q : Fin 8, ∃ t : Fin 8,
          newVertex (Fin.castLE (by norm_num : 8 ≤ 9) t) =
            S.vertex ⟨q.val, by omega⟩ := by
        intro q
        by_cases hq : q.val = 7
        · have hqeq : q = (7 : Fin 8) := Fin.ext hq
          subst q
          refine ⟨7, ?_⟩
          change newVertex 7 = y7
          exact nv7
        · let q' : Fin 7 := ⟨q.val, by omega⟩
          obtain ⟨t, ht⟩ := firstSeven q'
          refine ⟨Fin.castLE (by norm_num : 7 ≤ 8) t, ?_⟩
          simpa [q'] using ht
      obtain ⟨tc0, htc0⟩ := firstSeven pc'
      obtain ⟨tc1, htc1⟩ := firstEight pc1'
      obtain ⟨tw, htw⟩ := firstSeven w
      let S' : TreeSequence G e :=
        { length := 8
          positive := by omega
          vertex := newVertex
          edge := newEdge
          vertex_injective := newVertex_injective
          edge_injective := newEdge_injective
          first_edge := ne0.trans ha0eq
          attaches := by
            intro j
            fin_cases j
            · refine ⟨0, ?_⟩
              change G.ends (newEdge 0) = s(newVertex 1, newVertex 0)
              rw [ne0, nv0, nv1]
              exact ha0ends
            · refine ⟨1, ?_⟩
              change G.ends (newEdge 1) = s(newVertex 2, newVertex 1)
              rw [ne1, nv1, nv2]
              exact hf1ends'.trans Sym2.eq_swap
            · refine ⟨2, ?_⟩
              change G.ends (newEdge 2) = s(newVertex 3, newVertex 2)
              rw [ne2, nv2, nv3]
              exact hbeta56ends.trans Sym2.eq_swap
            · refine ⟨3, ?_⟩
              change G.ends (newEdge 3) = s(newVertex 4, newVertex 3)
              rw [ne3, nv3, nv4]
              exact hf2ends'
            · refine ⟨1, ?_⟩
              change G.ends (newEdge 4) = s(newVertex 5, newVertex 1)
              rw [ne4, nv1, nv5]
              exact ha1ends.trans Sym2.eq_swap
            · refine ⟨4, ?_⟩
              change G.ends (newEdge 5) = s(newVertex 6, newVertex 4)
              rw [ne5, nv4, nv6]
              exact ha3ends
            · refine ⟨tc0, ?_⟩
              change G.ends (newEdge 6) =
                s(newVertex 7, newVertex (Fin.castLE (by omega) tc0))
              rw [ne6, nv7]
              exact hc0ends.trans (congrArg (fun z ↦ s(y7, z)) htc0.symm)
            · refine ⟨tc1, ?_⟩
              change G.ends (newEdge 7) =
                s(newVertex 8, newVertex (Fin.castLE (by omega) tc1))
              rw [ne7, nv8]
              exact hc1ends.trans (congrArg (fun z ↦ s(y8, z)) htc1.symm) }
      have hS'length : S'.length = 8 := rfl
      have hS'vertex (i : Fin 9) : S'.vertex i = newVertex i := rfl
      have hS'edge (i : Fin 8) : S'.edge i = newEdge i := rfl
      have htwMissing : g1 ∈ MissingColors G psi
          (S'.vertex ⟨tw.val, by omega⟩) := by
        change g1 ∈ MissingColors G psi
          (newVertex (Fin.castLE (by omega) tw))
        rw [htw]
        exact hwmissing'
      have hS'tash : TashkinovTree G e psi S' := by
        intro j hj
        fin_cases j
        · simp at hj
        · refine ⟨0, g0, ?_, ?_⟩
          · change psi (newEdge 1) = some g0
            rw [ne1]
            exact hf1color
          · change g0 ∈ MissingColors G psi (newVertex 0)
            rw [nv0]
            exact hg0'
        · refine ⟨1, M.beta, ?_, ?_⟩
          · change psi (newEdge 2) = some M.beta
            rw [ne2]
            exact hbeta56color
          · change M.beta ∈ MissingColors G psi (newVertex 1)
            rw [nv1]
            simpa [y1] using M.beta_missing
        · refine ⟨0, g0, ?_, ?_⟩
          · change psi (newEdge 3) = some g0
            rw [ne3]
            exact hf2color
          · change g0 ∈ MissingColors G psi (newVertex 0)
            rw [nv0]
            exact hg0'
        · refine ⟨0, M.alpha, ?_, ?_⟩
          · change psi (newEdge 4) = some M.alpha
            rw [ne4]
            exact ha1color
          · change M.alpha ∈ MissingColors G psi (newVertex 0)
            rw [nv0]
            simpa [y0] using M.alpha_missing
        · refine ⟨0, M.alpha, ?_, ?_⟩
          · change psi (newEdge 5) = some M.alpha
            rw [ne5]
            exact ha3color
          · change M.alpha ∈ MissingColors G psi (newVertex 0)
            rw [nv0]
            simpa [y0] using M.alpha_missing
        · refine ⟨tw, g1, ?_, ?_⟩
          · change psi (newEdge 6) = some g1
            rw [ne6]
            exact hc0color'
          · have hv : S'.vertex (Fin.castLT tw (by omega)) =
                S'.vertex ⟨tw.val, by omega⟩ := by
                apply congrArg S'.vertex
                apply Fin.ext
                rfl
            rw [hv]
            exact htwMissing
        · refine ⟨Fin.castLE (by norm_num : 7 ≤ 8) tw, g1, ?_, ?_⟩
          · change psi (newEdge 7) = some g1
            rw [ne7]
            exact hc1color
          · have hv : S'.vertex
                (Fin.castLT (Fin.castLE (by norm_num : 7 ≤ 8) tw)
                  (lt_trans tw.isLt (by norm_num : 7 < 9))) =
                S'.vertex ⟨tw.val, by omega⟩ := by
                apply congrArg S'.vertex
                apply Fin.ext
                rfl
            rw [hv]
            exact htwMissing
      have horderNine : TashkinovOrder G = 9 := by
        calc
          TashkinovOrder G = (TreeSequenceVertexSet S).card := horderM.1
          _ = S.length + 1 := by
            simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
              S.vertex_injective]
          _ = 9 := by omega
      have hS'card : (TreeSequenceVertexSet S').card = 9 := by
        calc
          (TreeSequenceVertexSet S').card = S'.length + 1 := by
            simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
              S'.vertex_injective]
          _ = 9 := by rw [hS'length]
      have hS'global : GlobalMaximumTriple G k e psi S' := by
        refine ⟨M.global.1, hS'tash, ?_⟩
        rw [hS'card, horderNine]
      have hf1f2 : f1 ≠ f2 := by
        intro hh
        have he : newEdge 1 = newEdge 3 := by rw [ne1, ne3, hh]
        have hi := newEdge_injective he
        have hiv := congrArg Fin.val hi
        norm_num at hiv
      have hf1close : f1 ≠ M.closingEdge := by
        intro hh
        have hc : some g0 = some M.beta := by
          rw [← hf1color, hh, hclosingColor]
        exact hg0beta (Option.some.inj hc)
      have hf2close : f2 ≠ M.closingEdge := by
        intro hh
        have hc : some g0 = some M.beta := by
          rw [← hf2color, hh, hclosingColor]
        exact hg0beta (Option.some.inj hc)
      have hbetaClose : beta56 ≠ M.closingEdge := by
        intro hh
        have he : s(v1, v2) = s(y4, y0) := by
          rw [← hbeta56ends, hh]
          exact hclosingEnds
        rcases Sym2.eq_iff.mp he with hp | hp
        · exact hv14 hp.1
        · exact hv10 hp.1
      let H := TwoColorIncidenceGraph G psi g0 M.beta
      let pathNodes : List (Sum V E) :=
        [Sum.inl y1, Sum.inr f1, Sum.inl v1, Sum.inr beta56,
          Sum.inl v2, Sum.inr f2, Sum.inl y4,
          Sum.inr M.closingEdge, Sum.inl y0]
      have hy1f1 : Incident G y1 f1 := by
        rw [Incident, hf1ends']
        simp
      have hv1f1 : Incident G v1 f1 := by
        rw [Incident, hf1ends']
        simp
      have hv1beta : Incident G v1 beta56 := by
        rw [Incident, hbeta56ends]
        simp
      have hv2beta : Incident G v2 beta56 := by
        rw [Incident, hbeta56ends]
        simp
      have hv2f2 : Incident G v2 f2 := by
        rw [Incident, hf2ends']
        simp
      have hy4f2 : Incident G y4 f2 := by
        rw [Incident, hf2ends']
        simp
      have hy4close : Incident G y4 M.closingEdge := by
        rw [Incident, hclosingEnds]
        simp
      have hy0close : Incident G y0 M.closingEdge := by
        rw [Incident, hclosingEnds]
        simp
      have hpathChain : pathNodes.IsChain H.Adj := by
        simp [pathNodes, H, TwoColorIncidenceGraph, hy1f1, hv1f1,
          hv1beta, hv2beta, hv2f2, hy4f2, hy4close, hy0close,
          hf1color, hf2color, hbeta56color, hclosingColor]
      have hpathNodesNonempty : pathNodes ≠ [] := by simp [pathNodes]
      let rawPath := SimpleGraph.Walk.ofSupport pathNodes
        hpathNodesNonempty hpathChain
      have hpathStart : pathNodes.head hpathNodesNonempty =
          Sum.inl (S'.vertex ⟨1, by omega⟩) := by
        change Sum.inl y1 = Sum.inl (newVertex 1)
        rw [nv1]
      have hpathEnd : pathNodes.getLast hpathNodesNonempty =
          Sum.inl (S'.vertex ⟨0, by omega⟩) := by
        change Sum.inl y0 = Sum.inl (newVertex 0)
        rw [nv0]
      let closingPath : H.Walk
          (Sum.inl (S'.vertex ⟨1, by omega⟩))
          (Sum.inl (S'.vertex ⟨0, by omega⟩)) :=
        rawPath.copy hpathStart hpathEnd
      have hpathSupport : closingPath.support = pathNodes := by
        calc
          closingPath.support = rawPath.support := by
            simpa only [closingPath] using
              SimpleGraph.Walk.support_copy rawPath hpathStart hpathEnd
          _ = pathNodes := by
            simpa only [rawPath] using
              SimpleGraph.Walk.support_ofSupport hpathNodesNonempty hpathChain
      have hpathLength : closingPath.length = 8 := by
        calc
          closingPath.length = rawPath.length := by
            simpa only [closingPath] using
              SimpleGraph.Walk.length_copy rawPath hpathStart hpathEnd
          _ = pathNodes.length - 1 := by
            simpa only [rawPath] using
              SimpleGraph.Walk.length_ofSupport hpathNodesNonempty hpathChain
          _ = 8 := by simp [pathNodes]
      have hpathNodesNodup : pathNodes.Nodup := by
        simp [pathNodes, ← nv0, ← nv1, ← nv2, ← nv3, ← nv4,
          newVertex_injective.eq_iff, hf1f2, hf1close, hf2close,
          hbeta_f1, hbeta_f2, hbetaClose, Ne.symm hbeta_f1,
          Ne.symm hbeta_f2, Ne.symm hbetaClose]
      have hpathIsPath : closingPath.IsPath := by
        rw [SimpleGraph.Walk.isPath_def, hpathSupport]
        exact hpathNodesNodup
      have hpathVertexSupport : ∀ v : V,
          Sum.inl v ∈ closingPath.support ↔
            ∃ i : Fin 5, v = S'.vertex (Fin.castLE (by norm_num : 5 ≤ 9) i) := by
        intro v
        rw [hpathSupport]
        have nv0' : newVertex (Fin.castLE (by norm_num : 5 ≤ 9) (0 : Fin 5)) = y0 := by
          rw [show Fin.castLE (by norm_num : 5 ≤ 9) (0 : Fin 5) =
            (0 : Fin 9) by apply Fin.ext; rfl]
          exact nv0
        have nv1' : newVertex (Fin.castLE (by norm_num : 5 ≤ 9) (1 : Fin 5)) = y1 := by
          rw [show Fin.castLE (by norm_num : 5 ≤ 9) (1 : Fin 5) =
            (1 : Fin 9) by apply Fin.ext; rfl]
          exact nv1
        have nv2' : newVertex (Fin.castLE (by norm_num : 5 ≤ 9) (2 : Fin 5)) = v1 := by
          rw [show Fin.castLE (by norm_num : 5 ≤ 9) (2 : Fin 5) =
            (2 : Fin 9) by apply Fin.ext; rfl]
          exact nv2
        have nv3' : newVertex (Fin.castLE (by norm_num : 5 ≤ 9) (3 : Fin 5)) = v2 := by
          rw [show Fin.castLE (by norm_num : 5 ≤ 9) (3 : Fin 5) =
            (3 : Fin 9) by apply Fin.ext; rfl]
          exact nv3
        have nv4' : newVertex (Fin.castLE (by norm_num : 5 ≤ 9) (4 : Fin 5)) = y4 := by
          rw [show Fin.castLE (by norm_num : 5 ≤ 9) (4 : Fin 5) =
            (4 : Fin 9) by apply Fin.ext; rfl]
          exact nv4
        constructor
        · intro hv
          simp [pathNodes] at hv
          rcases hv with hv | hv | hv | hv | hv
          · refine ⟨1, ?_⟩
            exact hv.trans nv1'.symm
          · refine ⟨2, ?_⟩
            exact hv.trans nv2'.symm
          · refine ⟨3, ?_⟩
            exact hv.trans nv3'.symm
          · refine ⟨4, ?_⟩
            exact hv.trans nv4'.symm
          · refine ⟨0, ?_⟩
            exact hv.trans nv0'.symm
        · rintro ⟨i, rfl⟩
          fin_cases i
          · change Sum.inl (newVertex 0) ∈ pathNodes
            rw [nv0]
            simp [pathNodes]
          · change Sum.inl (newVertex 1) ∈ pathNodes
            rw [nv1]
            simp [pathNodes]
          · change Sum.inl (newVertex 2) ∈ pathNodes
            rw [nv2]
            simp [pathNodes]
          · change Sum.inl (newVertex 3) ∈ pathNodes
            rw [nv3]
            simp [pathNodes]
          · change Sum.inl (newVertex 4) ∈ pathNodes
            rw [nv4]
            simp [pathNodes]
      have hpathEdgeSupport : ∀ f : E,
          Sum.inr f ∈ closingPath.support ↔
            f = M.closingEdge ∨
              ∃ j : Fin S'.length,
                1 ≤ j.val ∧ j.val + 2 ≤ 5 ∧ f = S'.edge j := by
        intro f
        rw [hpathSupport]
        have se1 : S'.edge ⟨1, by rw [hS'length]; norm_num⟩ = f1 := by
          change newEdge ⟨1, by norm_num⟩ = f1
          rw [show (⟨1, by norm_num⟩ : Fin 8) = (1 : Fin 8) by
            apply Fin.ext; rfl, ne1]
        have se2 : S'.edge ⟨2, by rw [hS'length]; norm_num⟩ = beta56 := by
          change newEdge ⟨2, by norm_num⟩ = beta56
          rw [show (⟨2, by norm_num⟩ : Fin 8) = (2 : Fin 8) by
            apply Fin.ext; rfl, ne2]
        have se3 : S'.edge ⟨3, by rw [hS'length]; norm_num⟩ = f2 := by
          change newEdge ⟨3, by norm_num⟩ = f2
          rw [show (⟨3, by norm_num⟩ : Fin 8) = (3 : Fin 8) by
            apply Fin.ext; rfl, ne3]
        constructor
        · intro hf
          simp [pathNodes] at hf
          rcases hf with hf | hf | hf | hf
          · right
            refine ⟨⟨1, by rw [hS'length]; norm_num⟩, by norm_num,
              by norm_num, hf.trans se1.symm⟩
          · right
            refine ⟨⟨2, by rw [hS'length]; norm_num⟩, by norm_num,
              by norm_num, hf.trans se2.symm⟩
          · right
            refine ⟨⟨3, by rw [hS'length]; norm_num⟩, by norm_num,
              by norm_num, hf.trans se3.symm⟩
          · exact Or.inl hf
        · rintro (rfl | ⟨j, hj, hjbound, rfl⟩)
          · simp [pathNodes]
          · fin_cases j <;> simp at hj hjbound
            · change Sum.inr (newEdge 1) ∈ pathNodes
              rw [ne1]
              simp [pathNodes]
            · change Sum.inr (newEdge 2) ∈ pathNodes
              rw [ne2]
              simp [pathNodes]
            · change Sum.inr (newEdge 3) ∈ pathNodes
              rw [ne3]
              simp [pathNodes]
      have htrunkEnds : ∀ j : Fin S'.length,
          1 ≤ j.val → j.val + 2 ≤ 5 →
            G.ends (S'.edge j) =
              s(S'.vertex ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩,
                S'.vertex j.succ) := by
        intro j hj hjbound
        fin_cases j <;> simp at hj hjbound
        · change G.ends (newEdge 1) = s(newVertex 1, newVertex 2)
          rw [ne1, nv1, nv2]
          exact hf1ends'
        · change G.ends (newEdge 2) = s(newVertex 2, newVertex 3)
          rw [ne2, nv2, nv3]
          exact hbeta56ends
        · change G.ends (newEdge 3) = s(newVertex 3, newVertex 4)
          rw [ne3, nv3, nv4]
          exact hf2ends'.trans Sym2.eq_swap
      let M' : NormalGlobalMaximumTriple G k e psi S' :=
        { global := hS'global
          height := 5
          height_lower := by omega
          height_upper := by rw [hS'length]; omega
          alpha := g0
          beta := M.beta
          alpha_missing := by
            change g0 ∈ MissingColors G psi (newVertex 0)
            rw [nv0]
            exact hg0'
          beta_missing := by
            change M.beta ∈ MissingColors G psi (newVertex 1)
            rw [nv1]
            simpa [y1] using M.beta_missing
          closingEdge := M.closingEdge
          lastIndex := ⟨4, by rw [hS'length]; omega⟩
          lastIndex_height := by norm_num
          closing_ends := by
            change G.ends M.closingEdge = s(newVertex 4, newVertex 0)
            rw [nv4, nv0]
            exact hclosingEnds
          closingPath := by simpa only [H] using closingPath
          closingPath_isPath := by simpa only [H] using hpathIsPath
          closingPath_length := by simpa using hpathLength
          closingPath_vertices := hpathVertexSupport
          closingPath_edges := hpathEdgeSupport
          trunk_edge_ends := htrunkEnds }
      have hM'height : M'.height = 5 := rfl
      have hM'bal : BalancedGlobalMaximumTriple M' := by
        constructor
        · change 5 = ScheideGraphHeight G
          exact hgraphHeight.symm
        · intro q hlow hupp
          have hq : q = 3 ∨ q = 4 := by
            change 5 < 2 * q at hlow
            change 2 * q < 8 + 1 at hupp
            omega
          rcases hq with rfl | rfl
          · change psi (newEdge 4) = psi (newEdge 5)
            rw [ne4, ne5, ha1color, ha3color]
          · change psi (newEdge 6) = psi (newEdge 7)
            rw [ne6, ne7, hc0color', hc1color]
      refine ⟨S', M', hS'length, hM'height, hM'bal, ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_⟩
      · change newVertex 0 = y0
        exact nv0
      · change newVertex 1 = y1
        exact nv1
      · change newVertex 2 = v1
        exact nv2
      · change newVertex 3 = v2
        exact nv3
      · change newVertex 4 = y4
        exact nv4
      · change newVertex 5 = y2
        exact nv5
      · change newVertex 6 = y3
        exact nv6
      · change newVertex 7 = y7
        exact nv7
      · change newVertex 8 = y8
        exact nv8
      · change newEdge 0 = a0
        exact ne0
      · change newEdge 1 = f1
        exact ne1
      · change newEdge 2 = beta56
        exact ne2
      · change newEdge 3 = f2
        exact ne3
      · change newEdge 4 = a1
        exact ne4
      · change newEdge 5 = a3
        exact ne5
      · change newEdge 6 = c0
        exact ne6
      · change newEdge 7 = c1
        exact ne7
      · exact ⟨rfl, rfl⟩
    have complete {eX : E} (X : TreeSequence G eX)
        (Q : NormalGlobalMaximumTriple G k eX psi X)
        (hbalX : BalancedGlobalMaximumTriple Q)
        (hlenX : X.length = 8) (hheightX : Q.height = 5)
        (d0 d1 : Fin k)
        (hd0missing : d0 ∈ MissingColors G psi
          (X.vertex ⟨0, by omega⟩))
        (m : Fin 5) (hd1missing : d1 ∈ MissingColors G psi
          (X.vertex ⟨m.val, by omega⟩))
        (hd0alpha : d0 ≠ Q.alpha) (hd0beta : d0 ≠ Q.beta)
        (hd1alpha : d1 ≠ Q.alpha) (hd1beta : d1 ≠ Q.beta)
        (hd10 : d1 ≠ d0)
        (x1 x2 linkB last0 lastA lastB : E) (z1 z2 : V)
        (hx1ends : G.ends x1 = s(X.vertex ⟨1, by omega⟩, z1))
        (hx2ends : G.ends x2 = s(X.vertex ⟨4, by omega⟩, z2))
        (hx1color : psi x1 = some d0) (hx2color : psi x2 = some d0)
        (hlinkBends : G.ends linkB = s(z1, z2))
        (hlinkBcolor : psi linkB = some Q.beta)
        (hlast0ends : G.ends last0 =
          s(X.vertex ⟨7, by omega⟩, X.vertex ⟨8, by omega⟩))
        (hlast0color : psi last0 = some d0)
        (hlastAends : G.ends lastA =
          s(X.vertex ⟨7, by omega⟩, X.vertex ⟨8, by omega⟩))
        (hlastAcolor : psi lastA = some Q.alpha)
        (hlastBends : G.ends lastB =
          s(X.vertex ⟨7, by omega⟩, X.vertex ⟨8, by omega⟩))
        (hlastBcolor : psi lastB = some Q.beta)
        (hfirstOrient :
          (X.edge ⟨4, by omega⟩ = x1 ∧ X.vertex ⟨5, by omega⟩ = z1 ∧
            X.edge ⟨5, by omega⟩ = x2 ∧ X.vertex ⟨6, by omega⟩ = z2) ∨
          (X.edge ⟨4, by omega⟩ = x2 ∧ X.vertex ⟨5, by omega⟩ = z2 ∧
            X.edge ⟨5, by omega⟩ = x1 ∧ X.vertex ⟨6, by omega⟩ = z1))
        (hsecondColor : ∀ j : Fin 2,
          psi (X.edge ⟨6 + j.val, by omega⟩) = some d1) :
        Good psi X Q := by as_aux_lemma =>
      let Y (i : Fin 9) : V := X.vertex ⟨i.val, by omega⟩
      let C (j : Fin 2) : E := X.edge ⟨6 + j.val, by omega⟩
      have hYne {i j : Fin 9} (hij : i ≠ j) : Y i ≠ Y j := by
        intro h
        apply hij
        apply Fin.ext
        have heq : (⟨i.val, by omega⟩ : Fin (X.length + 1)) =
            ⟨j.val, by omega⟩ := X.vertex_injective h
        exact congrArg (fun r : Fin (X.length + 1) => r.val) heq
      have hCne : C 0 ≠ C 1 := by
        intro h
        have hi := X.edge_injective h
        norm_num [C] at hi
      have hCcolor (j : Fin 2) : psi (C j) = some d1 := by
        simpa [C] using hsecondColor j
      have hlink56 : G.ends linkB = s(Y 5, Y 6) := by
        rcases hfirstOrient with ho | ho
        · simpa [Y, ho.2.1, ho.2.2.2] using hlinkBends
        · simpa [Y, ho.2.1, ho.2.2.2, Sym2.eq_swap] using hlinkBends
      have hlast0 : G.ends last0 = s(Y 7, Y 8) := by
        simpa [Y] using hlast0ends
      have hlastA : G.ends lastA = s(Y 7, Y 8) := by
        simpa [Y] using hlastAends
      have hlastB : G.ends lastB = s(Y 7, Y 8) := by
        simpa [Y] using hlastBends
      have hproperX : IsProperEdgeColoring G psi := Q.global.1.2.2.2.1
      have hcross : ∃ j : Fin 2, ∃ q : Fin 5,
          G.ends (C j) =
            s(Y ⟨q.val, by omega⟩, Y ⟨7 + j.val, by omega⟩) := by
        by_contra hn
        push_neg at hn
        obtain ⟨p0, hp0⟩ := X.attaches (⟨6, by omega⟩ : Fin X.length)
        obtain ⟨p1, hp1⟩ := X.attaches (⟨7, by omega⟩ : Fin X.length)
        have hp0lt7 : p0.val < 7 := by simpa using p0.isLt
        have hp1lt8 : p1.val < 8 := by simpa using p1.isLt
        have hp0v : X.vertex (Fin.castLT p0
              (Nat.lt_trans p0.isLt
                (Nat.succ_lt_succ (⟨6, by omega⟩ : Fin X.length).isLt))) =
            Y ⟨p0.val, by omega⟩ := by
          apply congrArg X.vertex
          apply Fin.ext
          rfl
        have hp1v : X.vertex (Fin.castLT p1
              (Nat.lt_trans p1.isLt
                (Nat.succ_lt_succ (⟨7, by omega⟩ : Fin X.length).isLt))) =
            Y ⟨p1.val, by omega⟩ := by
          apply congrArg X.vertex
          apply Fin.ext
          rfl
        have hp0' : G.ends (C 0) =
            s(Y 7, Y ⟨p0.val, by omega⟩) := by
          simpa [C, Y, hp0v] using hp0
        have hp1' : G.ends (C 1) =
            s(Y 8, Y ⟨p1.val, by omega⟩) := by
          simpa [C, Y, hp1v] using hp1
        have hp0ge : 5 ≤ p0.val := by
          by_contra h
          have hp0lt : p0.val < 5 := by omega
          let q : Fin 5 := ⟨p0.val, hp0lt⟩
          exact hn 0 q (by simpa [q] using hp0'.trans Sym2.eq_swap)
        have hp1ge : 5 ≤ p1.val := by
          by_contra h
          have hp1lt : p1.val < 5 := by omega
          let q : Fin 5 := ⟨p1.val, hp1lt⟩
          exact hn 1 q (by simpa [q] using hp1'.trans Sym2.eq_swap)
        have hp1not7 : p1.val ≠ 7 := by
          intro hp17
          have hinc0 : Incident G (Y 7) (C 0) := by
            rw [Incident, hp0']
            simp
          have hinc1 : Incident G (Y 7) (C 1) := by
            rw [Incident, hp1']
            simp [hp17]
          exact (hproperX hCne ⟨Y 7, hinc0, hinc1⟩ (hCcolor 0))
            (hCcolor 1)
        have hp0cases : p0.val = 5 ∨ p0.val = 6 := by omega
        have hp1cases : p1.val = 5 ∨ p1.val = 6 := by omega
        have hpne : p0.val ≠ p1.val := by
          intro heq
          let u : Fin 9 := ⟨p0.val, by omega⟩
          have hinc0 : Incident G (Y u) (C 0) := by
            rw [Incident, hp0']
            simp [u]
          have hinc1 : Incident G (Y u) (C 1) := by
            rw [Incident, hp1']
            simp [u, heq]
          exact (hproperX hCne ⟨_, hinc0, hinc1⟩ (hCcolor 0))
            (hCcolor 1)
        have hmatch :
            (G.ends (C 0) = s(Y 7, Y 5) ∧
              G.ends (C 1) = s(Y 8, Y 6)) ∨
            (G.ends (C 0) = s(Y 7, Y 6) ∧
              G.ends (C 1) = s(Y 8, Y 5)) := by
          rcases hp0cases with h05 | h06 <;>
            rcases hp1cases with h15 | h16
          · exact False.elim (hpne (h05.trans h15.symm))
          · left
            constructor
            · simpa [h05] using hp0'
            · simpa [h16] using hp1'
          · right
            constructor
            · simpa [h06] using hp0'
            · simpa [h15] using hp1'
          · exact False.elim (hpne (h06.trans h16.symm))
        have cycleContradiction (a b : V) (r5 r6 : E)
            (ha7or8 : (a = Y 7 ∧ b = Y 8) ∨ (a = Y 8 ∧ b = Y 7))
            (hr5ends : G.ends r5 = s(z1, a))
            (hr6ends : G.ends r6 = s(z2, b))
            (hr5color : psi r5 = some d1)
            (hr6color : psi r6 = some d1)
            (hr5which : r5 = C 0 ∨ r5 = C 1)
            (hr6which : r6 = C 0 ∨ r6 = C 1)
            (hr56 : r5 ≠ r6) : False := by
          let H := TwoColorIncidenceGraph G psi d1 Q.beta
          let K := TwoColorComponent G psi d1 Q.beta (Sum.inl z1)
          let R : Set (Sum V E) := {q |
            q = Sum.inl z1 ∨ q = Sum.inr linkB ∨
            q = Sum.inl z2 ∨ q = Sum.inr r6 ∨
            q = Sum.inl b ∨ q = Sum.inr lastB ∨
            q = Sum.inl a ∨ q = Sum.inr r5}
          have hz12 : z1 ≠ z2 := by
            intro h
            subst z2
            exact G.loopless linkB z1 hlinkBends
          have habv : a ≠ b := by
            intro hab
            rcases ha7or8 with h | h
            · exact hYne (i := 7) (j := 8) (by decide)
                (h.1.symm.trans (hab.trans h.2))
            · exact hYne (i := 8) (j := 7) (by decide)
                (h.1.symm.trans (hab.trans h.2))
          have hlastab : G.ends lastB = s(a, b) := by
            rcases ha7or8 with h | h
            · simpa [h.1, h.2] using hlastB
            · simpa [h.1, h.2] using hlastB.trans Sym2.eq_swap
          have hlink_r5 : linkB ≠ r5 := by
            intro h
            subst r5
            rw [hlinkBcolor] at hr5color
            exact hd1beta (Option.some.inj hr5color.symm)
          have hlink_r6 : linkB ≠ r6 := by
            intro h
            subst r6
            rw [hlinkBcolor] at hr6color
            exact hd1beta (Option.some.inj hr6color.symm)
          have hlast_r5 : lastB ≠ r5 := by
            intro h
            subst r5
            rw [hlastBcolor] at hr5color
            exact hd1beta (Option.some.inj hr5color.symm)
          have hlast_r6 : lastB ≠ r6 := by
            intro h
            subst r6
            rw [hlastBcolor] at hr6color
            exact hd1beta (Option.some.inj hr6color.symm)
          have hz1a : z1 ≠ a := by
            intro h
            subst a
            exact G.loopless r5 z1 hr5ends
          have hz2b : z2 ≠ b := by
            intro h
            subst b
            exact G.loopless r6 z2 hr6ends
          have adjD {u v : V} {f : E} (hf : G.ends f = s(u, v))
              (hc : psi f = some d1) : H.Adj (Sum.inl u) (Sum.inr f) := by
            simp only [H, TwoColorIncidenceGraph]
            refine ⟨?_, Or.inl hc⟩
            rw [Incident, hf]
            simp
          have adjB {u v : V} {f : E} (hf : G.ends f = s(u, v))
              (hc : psi f = some Q.beta) :
              H.Adj (Sum.inl u) (Sum.inr f) := by
            simp only [H, TwoColorIncidenceGraph]
            refine ⟨?_, Or.inr hc⟩
            rw [Incident, hf]
            simp
          have hz1link := adjB hlinkBends hlinkBcolor
          have hz2link : H.Adj (Sum.inl z2) (Sum.inr linkB) :=
            adjB (hlinkBends.trans Sym2.eq_swap) hlinkBcolor
          have hz1r5 := adjD hr5ends hr5color
          have har5 : H.Adj (Sum.inl a) (Sum.inr r5) :=
            adjD (hr5ends.trans Sym2.eq_swap) hr5color
          have hz2r6 := adjD hr6ends hr6color
          have hbr6 : H.Adj (Sum.inl b) (Sum.inr r6) :=
            adjD (hr6ends.trans Sym2.eq_swap) hr6color
          have halast := adjB hlastab hlastBcolor
          have hblast : H.Adj (Sum.inl b) (Sum.inr lastB) :=
            adjB (hlastab.trans Sym2.eq_swap) hlastBcolor
          have neighbor_of_two {q r s t : Sum V E}
              (hr : H.Adj q r) (hs : H.Adj q s) (hrs : r ≠ s)
              (ht : H.Adj q t) : t = r ∨ t = s := by
            letI : Fintype (H.neighborSet q) := Fintype.ofFinite _
            by_contra hn
            push_neg at hn
            let three : Finset (Sum V E) := {r, s, t}
            have hsub : three ⊆ H.neighborFinset q := by
              intro x hx
              simp only [three, Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl | rfl
              · simpa [SimpleGraph.mem_neighborFinset] using hr
              · simpa [SimpleGraph.mem_neighborFinset] using hs
              · simpa [SimpleGraph.mem_neighborFinset] using ht
            have hthree : 3 ≤ (H.neighborFinset q).card := by
              have hc : three.card = 3 := by
                simp [three, hrs, hn.1, hn.2, Ne.symm]
              rw [← hc]
              exact Finset.card_le_card hsub
            have htwo : H.degree q ≤ 2 := by
              simpa [H] using
                TwoColorIncidenceDegreeAtMostTwo G psi d1 Q.beta hproperX q
            rw [SimpleGraph.card_neighborFinset_eq_degree] at hthree
            omega
          have R_closed : ∀ {q r : Sum V E}, q ∈ R → H.Adj q r → r ∈ R := by
            intro q r hq hr
            simp only [R] at hq ⊢
            rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · rcases neighbor_of_two hz1link hz1r5
                  (by simp [hlink_r5]) hr with h | h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inr h))))))
            · rcases neighbor_of_two hz1link.symm hz2link.symm
                  (by simp [hz12]) hr with h | h
              · exact Or.inl h
              · exact Or.inr (Or.inr (Or.inl h))
            · rcases neighbor_of_two hz2link hz2r6
                  (by simp [hlink_r6]) hr with h | h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
            · rcases neighbor_of_two hz2r6.symm hbr6.symm
                  (by simp [hz2b]) hr with h | h
              · exact Or.inr (Or.inr (Or.inl h))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
            · rcases neighbor_of_two hbr6 hblast
                  (by simp [hlast_r6, Ne.symm]) hr with h | h
              · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
              · exact Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inl h)))))
            · rcases neighbor_of_two hblast.symm halast.symm
                  (by simp [habv, Ne.symm]) hr with h | h
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inl h))))))
            · rcases neighbor_of_two halast har5
                  (by simp [hlast_r5]) hr with h | h
              · exact Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inl h)))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inr h))))))
            · rcases neighbor_of_two hz1r5.symm har5.symm
                  (by simp [hz1a]) hr with h | h
              · exact Or.inl h
              · exact Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr (Or.inl h))))))
          have hKR : K ⊆ R := by
            intro q hq
            change H.connectedComponentMk q =
              H.connectedComponentMk (Sum.inl z1) at hq
            obtain ⟨walk⟩ := SimpleGraph.ConnectedComponent.exact hq
            have propagate : ∀ {u v : Sum V E}, H.Walk u v → u ∈ R → v ∈ R := by
              intro u v walk hu
              induction walk with
              | nil => exact hu
              | @cons u t v hut rest ih => exact ih (R_closed hu hut)
            exact propagate walk.reverse (by simp [R])
          have hRK : R ⊆ K := by
            have mz1 : Sum.inl z1 ∈ K := rfl
            have mlink : Sum.inr linkB ∈ K :=
              (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                hz1link.symm).trans mz1
            have mz2 : Sum.inl z2 ∈ K :=
              (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                hz2link).trans mlink
            have mr6 : Sum.inr r6 ∈ K :=
              (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                hz2r6.symm).trans mz2
            have mb : Sum.inl b ∈ K :=
              (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                hbr6).trans mr6
            have mlast : Sum.inr lastB ∈ K :=
              (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                hblast.symm).trans mb
            have ma : Sum.inl a ∈ K :=
              (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                halast).trans mlast
            have mr5 : Sum.inr r5 ∈ K :=
              (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                har5.symm).trans ma
            intro q hq
            simp only [R] at hq
            rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact mz1
            · exact mlink
            · exact mz2
            · exact mr6
            · exact mb
            · exact mlast
            · exact ma
            · exact mr5
          have hKR_eq : K = R := Set.Subset.antisymm hKR hRK
          have hz1pos : z1 = Y 5 ∨ z1 = Y 6 := by
            rcases hfirstOrient with ho | ho
            · exact Or.inl (by simpa [Y] using ho.2.1.symm)
            · exact Or.inr (by simpa [Y] using ho.2.2.2.symm)
          have hz2pos : z2 = Y 5 ∨ z2 = Y 6 := by
            rcases hfirstOrient with ho | ho
            · exact Or.inr (by simpa [Y] using ho.2.2.2.symm)
            · exact Or.inl (by simpa [Y] using ho.2.1.symm)
          have trunk_tail_ne (q : Fin 5) (r : Fin 9) (hr : 5 ≤ r.val) :
              Y ⟨q.val, by omega⟩ ≠ Y r := by
            apply hYne
            intro h
            have hv := congrArg (fun i : Fin 9 => i.val) h
            exact (Nat.ne_of_lt (lt_of_lt_of_le q.isLt hr)) hv
          have htrunkNotK (q : Fin 5) :
              Sum.inl (Y ⟨q.val, by omega⟩) ∉ K := by
            rw [hKR_eq]
            simp only [R, Set.mem_setOf_eq, not_or, Sum.inl.injEq,
              Sum.inl_ne_inr, not_false_eq_true, true_and, and_true]
            refine ⟨?_, ?_, ?_, ?_⟩
            · rcases hz1pos with rfl | rfl
              · exact trunk_tail_ne q 5 (by norm_num)
              · exact trunk_tail_ne q 6 (by norm_num)
            · rcases hz2pos with rfl | rfl
              · exact trunk_tail_ne q 5 (by norm_num)
              · exact trunk_tail_ne q 6 (by norm_num)
            · rcases ha7or8 with h | h
              · rw [h.2]
                exact trunk_tail_ne q 8 (by norm_num)
              · rw [h.2]
                exact trunk_tail_ne q 7 (by norm_num)
            · rcases ha7or8 with h | h
              · rw [h.1]
                exact trunk_tail_ne q 7 (by norm_num)
              · rw [h.1]
                exact trunk_tail_ne q 8 (by norm_num)
          have beta_edge_not_K {f : E} {q : Fin 5}
              (hinc : Incident G (Y ⟨q.val, by omega⟩) f)
              (hfc : psi f = some Q.beta) : Sum.inr f ∉ K := by
            intro hfK
            have hadj : H.Adj (Sum.inl (Y ⟨q.val, by omega⟩))
                (Sum.inr f) := by
              simpa [H, TwoColorIncidenceGraph] using
                (show Incident G (Y ⟨q.val, by omega⟩) f ∧
                  (psi f = some d1 ∨ psi f = some Q.beta) from
                    ⟨hinc, Or.inr hfc⟩)
            apply htrunkNotK q
            change H.connectedComponentMk (Sum.inl (Y ⟨q.val, by omega⟩)) =
              H.connectedComponentMk (Sum.inl z1)
            change H.connectedComponentMk (Sum.inr f) =
              H.connectedComponentMk (Sum.inl z1) at hfK
            exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              hadj).trans hfK
          have hcycleX := ScheideTrunkRotationCycle G k eX psi X Q hbalX
          have he1cycle : NormalCycleEdge Q (⟨1, by omega⟩ : Fin Q.height) =
              X.edge ⟨1, by omega⟩ := by
            simp [NormalCycleEdge, hheightX]
          have he2cycle : NormalCycleEdge Q (⟨2, by omega⟩ : Fin Q.height) =
              X.edge ⟨2, by omega⟩ := by
            simp [NormalCycleEdge, hheightX]
          have he3cycle : NormalCycleEdge Q (⟨3, by omega⟩ : Fin Q.height) =
              X.edge ⟨3, by omega⟩ := by
            simp [NormalCycleEdge, hheightX]
          have hcloseCycleX : NormalCycleEdge Q
              (⟨4, by omega⟩ : Fin Q.height) = Q.closingEdge := by
            simp [NormalCycleEdge, hheightX]
          have he1color : psi (X.edge ⟨1, by omega⟩) = some Q.alpha := by
            have hc := hcycleX.2.2.2.2 (⟨1, by omega⟩ : Fin Q.height)
              (by norm_num)
            simpa [he1cycle] using hc
          have he2color : psi (X.edge ⟨2, by omega⟩) = some Q.beta := by
            have hc := hcycleX.2.2.2.2 (⟨2, by omega⟩ : Fin Q.height)
              (by norm_num)
            have heven : ¬ Odd (2 : ℕ) := by decide
            simpa [he2cycle, heven] using hc
          have he3color : psi (X.edge ⟨3, by omega⟩) = some Q.alpha := by
            have hc := hcycleX.2.2.2.2 (⟨3, by omega⟩ : Fin Q.height)
              (by norm_num)
            have hodd : Odd (3 : ℕ) := by decide
            simpa [he3cycle, hodd] using hc
          have hcloseColor : psi Q.closingEdge = some Q.beta := by
            have hc := hcycleX.2.2.2.2 (⟨4, by omega⟩ : Fin Q.height)
              (by norm_num)
            have heven : ¬ Odd (4 : ℕ) := by decide
            simpa [hcloseCycleX, heven] using hc
          have hAB : Q.alpha ≠ Q.beta := by
            intro h
            have hinc : Incident G (Y 1) (X.edge ⟨1, by omega⟩) := by
              have he := Q.trunk_edge_ends (⟨1, by omega⟩ : Fin X.length)
                (by norm_num) (by rw [hheightX]; norm_num)
              rw [Incident, he]
              simp [Y]
            have hnot := missing_excludes Q.beta_missing hinc
            exact hnot (by simpa [h] using he1color)
          have he2inc : Incident G (Y 2) (X.edge ⟨2, by omega⟩) := by
            have he := Q.trunk_edge_ends (⟨2, by omega⟩ : Fin X.length)
              (by norm_num) (by rw [hheightX]; norm_num)
            rw [Incident, he]
            simp [Y]
          have he2notK : Sum.inr (X.edge ⟨2, by omega⟩) ∉ K :=
            beta_edge_not_K (q := (2 : Fin 5)) he2inc he2color
          have hlastIndexX : Q.lastIndex =
              (⟨4, by omega⟩ : Fin (X.length + 1)) := by
            apply Fin.ext
            have h := Q.lastIndex_height
            rw [hheightX] at h
            simpa using h
          have hcloseEnds : G.ends Q.closingEdge = s(Y 4, Y 0) := by
            simpa [Y, hlastIndexX] using Q.closing_ends
          have hcloseInc : Incident G (Y 4) Q.closingEdge := by
            rw [Incident, hcloseEnds]
            simp
          have hcloseNotK : Sum.inr Q.closingEdge ∉ K :=
            beta_edge_not_K (q := (4 : Fin 5)) hcloseInc hcloseColor
          let chi := TwoColorComponentSwap G psi d1 Q.beta (Sum.inl z1)
          have hchiProper : IsProperEdgeColoring G chi := by
            simpa [chi] using TwoColorComponentSwapProper G psi d1 Q.beta
              hd1beta hproperX (Sum.inl z1)
          have unaffected {f : E} {c : Fin k} (hc : psi f = some c)
              (hcd : c ≠ d1) (hcb : c ≠ Q.beta) : chi f = some c := by
            by_cases hf : Sum.inr f ∈ K
            · simp [chi, TwoColorComponentSwap, K, hf, hc, hcd, hcb]
            · simp [chi, TwoColorComponentSwap, K, hf, hc]
          have beta_fixed {f : E} (hf : Sum.inr f ∉ K)
              (hc : psi f = some Q.beta) : chi f = some Q.beta := by
            simp [chi, TwoColorComponentSwap, K, hf, hc]
          have hr5K : Sum.inr r5 ∈ K := by
            rw [hKR_eq]
            simp [R]
          have hr6K : Sum.inr r6 ∈ K := by
            rw [hKR_eq]
            simp [R]
          have hchir5 : chi r5 = some Q.beta := by
            simp [chi, TwoColorComponentSwap, K, hr5K, hr5color, hd1beta]
          have hchir6 : chi r6 = some Q.beta := by
            simp [chi, TwoColorComponentSwap, K, hr6K, hr6color, hd1beta]
          have hchiC0 : chi (C 0) = some Q.beta := by
            rcases hr5which with h | h
            · simpa [h] using hchir5
            · rcases hr6which with h' | h'
              · simpa [h'] using hchir6
              · exact False.elim (hr56 (h.trans h'.symm))
          have hchiC1 : chi (C 1) = some Q.beta := by
            rcases hr5which with h | h
            · rcases hr6which with h' | h'
              · exact False.elim (hr56 (h.trans h'.symm))
              · simpa [h'] using hchir6
            · simpa [h] using hchir5
          have hchie1 : chi (X.edge ⟨1, by omega⟩) = some Q.alpha :=
            unaffected he1color hd1alpha.symm hAB
          have hchie2 : chi (X.edge ⟨2, by omega⟩) = some Q.beta :=
            beta_fixed he2notK he2color
          have hchie3 : chi (X.edge ⟨3, by omega⟩) = some Q.alpha :=
            unaffected he3color hd1alpha.symm hAB
          have hchix1 : chi x1 = some d0 :=
            unaffected hx1color hd10.symm hd0beta
          have hchix2 : chi x2 = some d0 :=
            unaffected hx2color hd10.symm hd0beta
          have hchilast0 : chi last0 = some d0 :=
            unaffected hlast0color hd10.symm hd0beta
          have hchiclose : chi Q.closingEdge = some Q.beta :=
            beta_fixed hcloseNotK hcloseColor
          have hbehavior := TwoColorComponentSwapMissingBehavior G psi d1
            Q.beta hd1beta hproperX (Sum.inl z1)
          have hmissD0 : d0 ∈ MissingColors G chi (Y 0) := by
            exact (hbehavior.2.2.2 (Y 0) d0 hd10.symm hd0beta).2
              (by simpa [Y] using hd0missing)
          have hmissA : Q.alpha ∈ MissingColors G chi (Y 0) := by
            exact (hbehavior.2.2.2 (Y 0) Q.alpha hd1alpha.symm hAB).2
              (by simpa [Y] using Q.alpha_missing)
          have hmissB : Q.beta ∈ MissingColors G chi (Y 1) := by
            have heq := hbehavior.1 (Y 1) (htrunkNotK 1)
            rw [heq]
            simpa [Y] using Q.beta_missing
          have he0notK : Sum.inr eX ∉ K := by
            intro he
            rw [hKR_eq] at he
            simp [R] at he
            rcases he with h | h | h | h
            · have hc := Q.global.1.2.2.2.2.1
              rw [h, hlinkBcolor] at hc
              simp at hc
            · have hc := Q.global.1.2.2.2.2.1
              rw [h, hr6color] at hc
              simp at hc
            · have hc := Q.global.1.2.2.2.2.1
              rw [h, hlastBcolor] at hc
              simp at hc
            · have hc := Q.global.1.2.2.2.2.1
              rw [h, hr5color] at hc
              simp at hc
          have honeChi : IsOneEdgeUncolored chi eX := by
            constructor
            · simpa [chi, TwoColorComponentSwap, K, he0notK] using
                Q.global.1.2.2.2.2.1
            · intro f hf
              obtain ⟨c, hc⟩ := Q.global.1.2.2.2.2.2 f hf
              by_cases hfk : Sum.inr f ∈ K
              · by_cases hcd : c = d1
                · refine ⟨Q.beta, ?_⟩
                  simp [chi, TwoColorComponentSwap, K, hfk, hc, hcd,
                    hd1beta]
                · by_cases hcb : c = Q.beta
                  · refine ⟨d1, ?_⟩
                    simp [chi, TwoColorComponentSwap, K, hfk, hc, hcd,
                      hcb, hd1beta]
                  · exact ⟨c, by
                      simp [chi, TwoColorComponentSwap, K, hfk, hc, hcd, hcb]⟩
              · exact ⟨c, by
                  simp [chi, TwoColorComponentSwap, K, hfk, hc]⟩
          have htashChi : TashkinovTree G eX chi X := by
            intro j hj
            have hjlt : j.val < 8 := by simpa [hlenX] using j.isLt
            have hjcases : j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨
                j.val = 4 ∨ j.val = 5 ∨ j.val = 6 ∨ j.val = 7 := by
              omega
            rcases hjcases with hjv | hjv | hjv | hjv | hjv | hjv | hjv
            · have hje : j = ⟨1, by omega⟩ := Fin.ext hjv
              rw [hje]
              refine ⟨0, Q.alpha, ?_, ?_⟩
              · exact hchie1
              · convert hmissA using 1
                congr 1
            · have hje : j = ⟨2, by omega⟩ := Fin.ext hjv
              rw [hje]
              refine ⟨1, Q.beta, ?_, ?_⟩
              · exact hchie2
              · convert hmissB using 1
                congr 1
            · have hje : j = ⟨3, by omega⟩ := Fin.ext hjv
              rw [hje]
              refine ⟨0, Q.alpha, ?_, ?_⟩
              · exact hchie3
              · convert hmissA using 1
                congr 1
            · have hje : j = ⟨4, by omega⟩ := Fin.ext hjv
              rw [hje]
              rcases hfirstOrient with ho | ho
              · refine ⟨0, d0, ?_, ?_⟩
                · simpa [ho.1] using hchix1
                · convert hmissD0 using 1
                  congr 1
              · refine ⟨0, d0, ?_, ?_⟩
                · simpa [ho.1] using hchix2
                · convert hmissD0 using 1
                  congr 1
            · have hje : j = ⟨5, by omega⟩ := Fin.ext hjv
              rw [hje]
              rcases hfirstOrient with ho | ho
              · refine ⟨0, d0, ?_, ?_⟩
                · simpa [ho.2.2.1] using hchix2
                · convert hmissD0 using 1
                  congr 1
              · refine ⟨0, d0, ?_, ?_⟩
                · simpa [ho.2.2.1] using hchix1
                · convert hmissD0 using 1
                  congr 1
            · have hje : j = ⟨6, by omega⟩ := Fin.ext hjv
              rw [hje]
              refine ⟨1, Q.beta, ?_, ?_⟩
              · simpa [C] using hchiC0
              · convert hmissB using 1
                congr 1
            · have hje : j = ⟨7, by omega⟩ := Fin.ext hjv
              rw [hje]
              refine ⟨1, Q.beta, ?_, ?_⟩
              · simpa [C] using hchiC1
              · convert hmissB using 1
                congr 1
          have hglobalChi : GlobalMaximumTriple G k eX chi X := by
            refine ⟨⟨Q.global.1.1, Q.global.1.2.1, Q.global.1.2.2.1,
              hchiProper, honeChi⟩, htashChi, Q.global.2.2⟩
          have hlast0ab : G.ends last0 = s(a, b) := by
            rcases ha7or8 with h | h
            · simpa [h.1, h.2] using hlast0
            · simpa [h.1, h.2] using hlast0.trans Sym2.eq_swap
          let H2 := TwoColorIncidenceGraph G chi d0 Q.beta
          let L := TwoColorComponent G chi d0 Q.beta (Sum.inl (Y 0))
          have adj0 {u v : V} {f : E} (hf : G.ends f = s(u, v))
              (hc : chi f = some d0) : H2.Adj (Sum.inl u) (Sum.inr f) := by
            simp only [H2, TwoColorIncidenceGraph]
            refine ⟨?_, Or.inl hc⟩
            rw [Incident, hf]
            simp
          have adj2B {u v : V} {f : E} (hf : G.ends f = s(u, v))
              (hc : chi f = some Q.beta) :
              H2.Adj (Sum.inl u) (Sum.inr f) := by
            simp only [H2, TwoColorIncidenceGraph]
            refine ⟨?_, Or.inr hc⟩
            rw [Incident, hf]
            simp
          have hY1x1 : H2.Adj (Sum.inl (Y 1)) (Sum.inr x1) :=
            adj0 (by simpa [Y] using hx1ends) hchix1
          have hz1x1 : H2.Adj (Sum.inl z1) (Sum.inr x1) :=
            adj0 (hx1ends.trans Sym2.eq_swap) hchix1
          have hz1r5' : H2.Adj (Sum.inl z1) (Sum.inr r5) :=
            adj2B hr5ends hchir5
          have har5' : H2.Adj (Sum.inl a) (Sum.inr r5) :=
            adj2B (hr5ends.trans Sym2.eq_swap) hchir5
          have halast0 : H2.Adj (Sum.inl a) (Sum.inr last0) :=
            adj0 hlast0ab hchilast0
          have hblast0 : H2.Adj (Sum.inl b) (Sum.inr last0) :=
            adj0 (hlast0ab.trans Sym2.eq_swap) hchilast0
          have hbr6' : H2.Adj (Sum.inl b) (Sum.inr r6) :=
            adj2B (hr6ends.trans Sym2.eq_swap) hchir6
          have hz2r6' : H2.Adj (Sum.inl z2) (Sum.inr r6) :=
            adj2B hr6ends hchir6
          have hz2x2 : H2.Adj (Sum.inl z2) (Sum.inr x2) :=
            adj0 (hx2ends.trans Sym2.eq_swap) hchix2
          have hY4x2 : H2.Adj (Sum.inl (Y 4)) (Sum.inr x2) :=
            adj0 (by simpa [Y] using hx2ends) hchix2
          have hY4close : H2.Adj (Sum.inl (Y 4))
              (Sum.inr Q.closingEdge) := adj2B hcloseEnds hchiclose
          have hY0close : H2.Adj (Sum.inl (Y 0))
              (Sum.inr Q.closingEdge) :=
            adj2B (hcloseEnds.trans Sym2.eq_swap) hchiclose
          have mY0 : Sum.inl (Y 0) ∈ L := rfl
          have mclose : Sum.inr Q.closingEdge ∈ L :=
            (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              hY0close.symm).trans mY0
          have mY4 : Sum.inl (Y 4) ∈ L :=
            (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              hY4close).trans mclose
          have mx2 : Sum.inr x2 ∈ L :=
            (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              hY4x2.symm).trans mY4
          have mz2 : Sum.inl z2 ∈ L :=
            (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              hz2x2).trans mx2
          have mr6 : Sum.inr r6 ∈ L :=
            (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              hz2r6'.symm).trans mz2
          have mb : Sum.inl b ∈ L :=
            (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              hbr6').trans mr6
          have mlast0 : Sum.inr last0 ∈ L :=
            (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              hblast0.symm).trans mb
          have ma : Sum.inl a ∈ L :=
            (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              halast0).trans mlast0
          have mr5 : Sum.inr r5 ∈ L :=
            (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              har5'.symm).trans ma
          have mz1 : Sum.inl z1 ∈ L :=
            (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              hz1r5').trans mr5
          have mx1 : Sum.inr x1 ∈ L :=
            (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              hz1x1.symm).trans mz1
          have mY1 : Sum.inl (Y 1) ∈ L :=
            (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              hY1x1).trans mx1
          obtain ⟨p, hp, hpsupport, hdiv, hvertices, hpbound⟩ :=
            ScheideKempePathHeightBound G k eX chi X hglobalChi d0 Q.beta
              (by simpa [Y] using hmissD0) (by simpa [Y] using hmissB)
          have in_support {u : Sum V E} (hu : u ∈ L) : u ∈ p.support := by
            have hu' : u ∈ {x | x ∈ p.support} := by
              rw [hpsupport]
              exact hu
            exact hu'
          have sx1 := in_support mx1
          have sx2 := in_support mx2
          have sr5 := in_support mr5
          have sr6 := in_support mr6
          have sY0 := in_support mY0
          have sY1 := in_support mY1
          have sY4 := in_support mY4
          have sz1 := in_support mz1
          have sz2 := in_support mz2
          have sa := in_support ma
          have sb := in_support mb
          have hx12 : x1 ≠ x2 := by
            intro h
            rcases hfirstOrient with ho | ho
            · have he : X.edge ⟨4, by omega⟩ = X.edge ⟨5, by omega⟩ :=
                ho.1.trans (h.trans ho.2.2.1.symm)
              have hi := X.edge_injective he
              norm_num at hi
            · have he : X.edge ⟨5, by omega⟩ = X.edge ⟨4, by omega⟩ :=
                ho.2.2.1.trans (h.trans ho.1.symm)
              have hi := X.edge_injective he
              norm_num at hi
          have x_d_ne {u v : E} (hu : psi u = some d0)
              (hv : psi v = some d1) : u ≠ v := by
            intro h
            subst v
            rw [hu] at hv
            exact hd10 (Option.some.inj hv.symm)
          have hx1r5 := x_d_ne hx1color hr5color
          have hx1r6 := x_d_ne hx1color hr6color
          have hx2r5 := x_d_ne hx2color hr5color
          have hx2r6 := x_d_ne hx2color hr6color
          let vs : List V := [Y 0, Y 1, Y 4, z1, z2, a, b]
          have hvs : vs.Nodup := by
            rcases hfirstOrient with ho | ho <;>
              rcases ha7or8 with ha | ha
            · have hz1 : z1 = Y 5 := by simpa [Y] using ho.2.1.symm
              have hz2 : z2 = Y 6 := by simpa [Y] using ho.2.2.2.symm
              simp [vs, hz1, hz2, ha.1, ha.2, hYne]
            · have hz1 : z1 = Y 5 := by simpa [Y] using ho.2.1.symm
              have hz2 : z2 = Y 6 := by simpa [Y] using ho.2.2.2.symm
              simp [vs, hz1, hz2, ha.1, ha.2, hYne]
            · have hz2 : z2 = Y 5 := by simpa [Y] using ho.2.1.symm
              have hz1 : z1 = Y 6 := by simpa [Y] using ho.2.2.2.symm
              simp [vs, hz1, hz2, ha.1, ha.2, hYne]
            · have hz2 : z2 = Y 5 := by simpa [Y] using ho.2.1.symm
              have hz1 : z1 = Y 6 := by simpa [Y] using ho.2.2.2.symm
              simp [vs, hz1, hz2, ha.1, ha.2, hYne]
          let es : List E := [x1, x2, r5, r6]
          have hes : es.Nodup := by
            simp [es, hx12, hx1r5, hx1r6, hx2r5, hx2r6, hr56, Ne.symm]
          let nodes : List (Sum V E) :=
            vs.map Sum.inl ++ es.map Sum.inr
          have hnodes : nodes.Nodup := by
            simp only [nodes, List.nodup_append]
            refine ⟨hvs.map Sum.inl_injective, hes.map Sum.inr_injective, ?_⟩
            intro u hu v hv huv
            obtain ⟨u, _, rfl⟩ := List.mem_map.mp hu
            obtain ⟨v, _, rfl⟩ := List.mem_map.mp hv
            exact Sum.inl_ne_inr huv
          have hnodesMem : ∀ u ∈ nodes, u ∈ p.support := by
            intro u hu
            simp only [nodes, vs, es, List.mem_append, List.mem_map,
              List.mem_cons, List.mem_singleton] at hu
            rcases hu with (⟨_, h, rfl⟩ | ⟨_, h, rfl⟩)
            all_goals simp only [List.mem_cons, List.mem_singleton,
              List.not_mem_nil, or_false] at h
            · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
              · exact sY0
              · exact sY1
              · exact sY4
              · exact sz1
              · exact sz2
              · exact sa
              · exact sb
            · rcases h with rfl | rfl | rfl | rfl
              · exact sx1
              · exact sx2
              · exact sr5
              · exact sr6
          have hsub : nodes.toFinset ⊆ p.support.toFinset := by
            intro u hu
            simp only [List.mem_toFinset] at hu ⊢
            exact hnodesMem u hu
          have hcard := Finset.card_le_card hsub
          have hpNodup : p.support.Nodup := by
            rwa [SimpleGraph.Walk.isPath_def] at hp
          rw [List.toFinset_card_of_nodup hnodes,
            List.toFinset_card_of_nodup hpNodup] at hcard
          have hnodesLength : nodes.length = 11 := by simp [nodes, vs, es]
          have hpSupportLength : p.support.length = p.length + 1 := by
            exact p.length_support
          rw [hnodesLength, hpSupportLength] at hcard
          rw [hgraphHeight] at hpbound
          omega
        rcases hmatch with hm | hm
        · rcases hfirstOrient with ho | ho
          · have hz1 : Y 5 = z1 := by simpa [Y] using ho.2.1
            have hz2 : Y 6 = z2 := by simpa [Y] using ho.2.2.2
            exact cycleContradiction (Y 7) (Y 8) (C 0) (C 1)
              (Or.inl ⟨rfl, rfl⟩)
              (by rw [← hz1]; exact hm.1.trans Sym2.eq_swap)
              (by rw [← hz2]; exact hm.2.trans Sym2.eq_swap)
              (hCcolor 0) (hCcolor 1) (Or.inl rfl) (Or.inr rfl) hCne
          · have hz2 : Y 5 = z2 := by simpa [Y] using ho.2.1
            have hz1 : Y 6 = z1 := by simpa [Y] using ho.2.2.2
            exact cycleContradiction (Y 8) (Y 7) (C 1) (C 0)
              (Or.inr ⟨rfl, rfl⟩)
              (by rw [← hz1]; exact hm.2.trans Sym2.eq_swap)
              (by rw [← hz2]; exact hm.1.trans Sym2.eq_swap)
              (hCcolor 1) (hCcolor 0) (Or.inr rfl) (Or.inl rfl) hCne.symm
        · rcases hfirstOrient with ho | ho
          · have hz1 : Y 5 = z1 := by simpa [Y] using ho.2.1
            have hz2 : Y 6 = z2 := by simpa [Y] using ho.2.2.2
            exact cycleContradiction (Y 8) (Y 7) (C 1) (C 0)
              (Or.inr ⟨rfl, rfl⟩)
              (by rw [← hz1]; exact hm.2.trans Sym2.eq_swap)
              (by rw [← hz2]; exact hm.1.trans Sym2.eq_swap)
              (hCcolor 1) (hCcolor 0) (Or.inr rfl) (Or.inl rfl) hCne.symm
          · have hz2 : Y 5 = z2 := by simpa [Y] using ho.2.1
            have hz1 : Y 6 = z1 := by simpa [Y] using ho.2.2.2
            exact cycleContradiction (Y 7) (Y 8) (C 0) (C 1)
              (Or.inl ⟨rfl, rfl⟩)
              (by rw [← hz1]; exact hm.1.trans Sym2.eq_swap)
              (by rw [← hz2]; exact hm.2.trans Sym2.eq_swap)
              (hCcolor 0) (hCcolor 1) (Or.inl rfl) (Or.inr rfl) hCne
      have localizeZero {eZ : E} (rho : PartialEdgeColoring E k)
          (Z : TreeSequence G eZ)
          (RZ : NormalGlobalMaximumTriple G k eZ rho Z)
          (hbalZ : BalancedGlobalMaximumTriple RZ)
          (hlenZ : Z.length = 8) (hheightZ : RZ.height = 5)
          (d : Fin k)
          (hdmissing : d ∈ MissingColors G rho
            (Z.vertex ⟨0, by omega⟩))
          (hdalpha : d ≠ RZ.alpha) (hdbeta : d ≠ RZ.beta)
          (lastAZ lastBZ : E)
          (hlastAZends : G.ends lastAZ =
            s(Z.vertex ⟨7, by omega⟩, Z.vertex ⟨8, by omega⟩))
          (hlastAZcolor : rho lastAZ = some RZ.alpha)
          (hlastBZends : G.ends lastBZ =
            s(Z.vertex ⟨7, by omega⟩, Z.vertex ⟨8, by omega⟩))
          (hlastBZcolor : rho lastBZ = some RZ.beta)
          (hcolors : ∀ j : Fin 2,
            rho (Z.edge ⟨6 + j.val, by omega⟩) = some d)
          (honeCross : ∃ j : Fin 2, ∃ q : Fin 5,
            G.ends (Z.edge ⟨6 + j.val, by omega⟩) =
              s(Z.vertex ⟨q.val, by omega⟩,
                Z.vertex ⟨7 + j.val, by omega⟩)) :
          ∀ j : Fin 2, ∃ q : Fin 5,
            G.ends (Z.edge ⟨6 + j.val, by omega⟩) =
              s(Z.vertex ⟨q.val, by omega⟩,
                Z.vertex ⟨7 + j.val, by omega⟩) := by
        let ZY (i : Fin 9) : V := Z.vertex ⟨i.val, by omega⟩
        let ZE (j : Fin 2) : E := Z.edge ⟨6 + j.val, by omega⟩
        have hproperZ : IsProperEdgeColoring G rho := RZ.global.1.2.2.2.1
        have hZYne {i j : Fin 9} (hij : i ≠ j) : ZY i ≠ ZY j := by
          intro h
          apply hij
          apply Fin.ext
          have heq : (⟨i.val, by omega⟩ : Fin (Z.length + 1)) =
              ⟨j.val, by omega⟩ := Z.vertex_injective h
          exact congrArg (fun r : Fin (Z.length + 1) => r.val) heq
        have missing_no_edge {v : V} {f : E}
            (hm : d ∈ MissingColors G rho v) (hi : Incident G v f) :
            rho f ≠ some d := by
          intro hf
          have hp : d ∈ PresentColors G rho v := by
            simp [PresentColors]
            exact ⟨f, hi, hf⟩
          have hn : d ∉ PresentColors G rho v := by
            simpa [MissingColors] using hm
          exact hn hp
        obtain ⟨j0, q0, hcross0⟩ := honeCross
        have hlastMem : ZY ⟨7 + j0.val, by omega⟩ ∈
            TreeSequenceVertexSet Z := by
          simp [ZY, TreeSequenceVertexSet]
        have hlastNe (r : Fin 5) :
            ZY ⟨7 + j0.val, by omega⟩ ≠ ZY ⟨r.val, by omega⟩ := by
          apply hZYne
          apply Fin.ne_of_val_ne
          apply Nat.ne_of_gt
          change r.val < 7 + j0.val
          omega
        obtain ⟨f1, f2, f3, u1, u2, hf1ends, hf2ends, hf3ends,
            hf1color, hf2color, hf3color, hu1T, hu2T, hu10, hu11, hu12,
            hu13, hu14, hu20, hu21, hu22, hu23, hu24⟩ :=
          ScheideHeightFiveGammaEdges G k eZ rho Z RZ hheightZ hgraphHeight d
            hdmissing (ZE j0) (ZY ⟨7 + j0.val, by omega⟩)
            (by simpa [ZE] using hcolors j0) (by
              fin_cases q0
              · exact Or.inl (by simpa [ZE, ZY] using hcross0)
              · exact Or.inr (Or.inl (by simpa [ZE, ZY] using hcross0))
              · exact Or.inr (Or.inr (Or.inl
                  (by simpa [ZE, ZY] using hcross0)))
              · exact Or.inr (Or.inr (Or.inr (Or.inl
                  (by simpa [ZE, ZY] using hcross0))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr
                  (by simpa [ZE, ZY] using hcross0)))))
            hlastMem (hlastNe 0) (hlastNe 1) (hlastNe 2) (hlastNe 3)
            (hlastNe 4)
        have hcross0' : G.ends (ZE j0) =
            s(ZY ⟨q0.val, by omega⟩, ZY ⟨7 + j0.val, by omega⟩) := by
          simpa [ZE, ZY] using hcross0
        have hknown : ZY ⟨7 + j0.val, by omega⟩ = u1 ∨
            ZY ⟨7 + j0.val, by omega⟩ = u2 := by
          fin_cases q0
          · have hi : Incident G (ZY 0) (ZE j0) := by
              rw [Incident, hcross0']
              simp [ZY]
            exact False.elim ((missing_no_edge hdmissing hi)
              (by simpa [ZE] using hcolors j0))
          · left
            have heq : ZE j0 = f1 := by
              by_contra hne
              have hi0 : Incident G (ZY 1) (ZE j0) := by
                rw [Incident, hcross0']
                simp [ZY]
              have hi1 : Incident G (ZY 1) f1 := by
                rw [Incident, hf1ends]
                simp [ZY]
              exact (hproperZ hne ⟨ZY 1, hi0, hi1⟩
                (by simpa [ZE] using hcolors j0)) hf1color
            have hpairs : s(ZY 1, ZY ⟨7 + j0.val, by omega⟩) =
                s(ZY 1, u1) := by
              rw [heq] at hcross0'
              simpa [ZY] using hcross0'.symm.trans hf1ends
            rcases Sym2.eq_iff.mp hpairs with hp | hp
            · exact hp.2
            · exact False.elim (hu11 (by simpa [ZY] using hp.1.symm))
          · have heq : ZE j0 = f3 := by
              by_contra hne
              have hi0 : Incident G (ZY 2) (ZE j0) := by
                rw [Incident, hcross0']
                simp [ZY]
              have hi3 : Incident G (ZY 2) f3 := by
                rw [Incident, hf3ends]
                simp [ZY]
              exact (hproperZ hne ⟨ZY 2, hi0, hi3⟩
                (by simpa [ZE] using hcolors j0)) hf3color
            have hpairs : s(ZY 2, ZY ⟨7 + j0.val, by omega⟩) =
                s(ZY 2, ZY 3) := by
              rw [heq] at hcross0'
              simpa [ZY] using hcross0'.symm.trans hf3ends
            rcases Sym2.eq_iff.mp hpairs with hp | hp
            · exact False.elim ((hlastNe 3) hp.2)
            · exact False.elim (hZYne (i := 2) (j := 3) (by decide) hp.1)
          · have heq : ZE j0 = f3 := by
              by_contra hne
              have hi0 : Incident G (ZY 3) (ZE j0) := by
                rw [Incident, hcross0']
                simp [ZY]
              have hi3 : Incident G (ZY 3) f3 := by
                rw [Incident, hf3ends]
                simp [ZY]
              exact (hproperZ hne ⟨ZY 3, hi0, hi3⟩
                (by simpa [ZE] using hcolors j0)) hf3color
            have hpairs : s(ZY 3, ZY ⟨7 + j0.val, by omega⟩) =
                s(ZY 2, ZY 3) := by
              rw [heq] at hcross0'
              simpa [ZY] using hcross0'.symm.trans hf3ends
            rcases Sym2.eq_iff.mp hpairs with hp | hp
            · exact False.elim (hZYne (i := 3) (j := 2) (by decide) hp.1)
            · exact False.elim ((hlastNe 2) hp.2)
          · right
            have heq : ZE j0 = f2 := by
              by_contra hne
              have hi0 : Incident G (ZY 4) (ZE j0) := by
                rw [Incident, hcross0']
                simp [ZY]
              have hi2 : Incident G (ZY 4) f2 := by
                rw [Incident, hf2ends]
                simp [ZY]
              exact (hproperZ hne ⟨ZY 4, hi0, hi2⟩
                (by simpa [ZE] using hcolors j0)) hf2color
            have hpairs : s(ZY 4, ZY ⟨7 + j0.val, by omega⟩) =
                s(ZY 4, u2) := by
              rw [heq] at hcross0'
              simpa [ZY] using hcross0'.symm.trans hf2ends
            rcases Sym2.eq_iff.mp hpairs with hp | hp
            · exact hp.2
            · exact False.elim (hu24 (by simpa [ZY] using hp.1.symm))
        obtain ⟨alphaEdge, betaEdge, halphaEnds, halphaColor, hbetaEnds,
            hbetaColor, habEdges⟩ :=
          ScheideHeightFiveOutsideLinks G k eZ rho Z RZ hheightZ
            hgraphHeight d hdmissing f1 f2 u1 u2 hf1ends hf2ends hf1color
            hf2color hu1T hu2T hu10 hu11 hu12 hu13 hu14 hu20 hu21 hu22
            hu23 hu24
        have hfinal : ZY ⟨7 + j0.val, by omega⟩ = ZY 7 ∨
            ZY ⟨7 + j0.val, by omega⟩ = ZY 8 := by
          fin_cases j0
          · exact Or.inl rfl
          · exact Or.inr rfl
        have hAlphaEq : alphaEdge = lastAZ := by
          by_contra hne
          rcases hknown with hu | hu <;> rcases hfinal with hy | hy
          · have hi1 : Incident G (ZY 7) alphaEdge := by
              rw [Incident, halphaEnds]
              simp [← hy, hu]
            have hi2 : Incident G (ZY 7) lastAZ := by
              rw [Incident, hlastAZends]
              simp [ZY]
            exact (hproperZ hne ⟨ZY 7, hi1, hi2⟩ halphaColor)
              hlastAZcolor
          · have hi1 : Incident G (ZY 8) alphaEdge := by
              rw [Incident, halphaEnds]
              simp [← hy, hu]
            have hi2 : Incident G (ZY 8) lastAZ := by
              rw [Incident, hlastAZends]
              simp [ZY]
            exact (hproperZ hne ⟨ZY 8, hi1, hi2⟩ halphaColor)
              hlastAZcolor
          · have hi1 : Incident G (ZY 7) alphaEdge := by
              rw [Incident, halphaEnds]
              simp [← hy, hu]
            have hi2 : Incident G (ZY 7) lastAZ := by
              rw [Incident, hlastAZends]
              simp [ZY]
            exact (hproperZ hne ⟨ZY 7, hi1, hi2⟩ halphaColor)
              hlastAZcolor
          · have hi1 : Incident G (ZY 8) alphaEdge := by
              rw [Incident, halphaEnds]
              simp [← hy, hu]
            have hi2 : Incident G (ZY 8) lastAZ := by
              rw [Incident, hlastAZends]
              simp [ZY]
            exact (hproperZ hne ⟨ZY 8, hi1, hi2⟩ halphaColor)
              hlastAZcolor
        have houtside : s(u1, u2) = s(ZY 7, ZY 8) := by
          rw [hAlphaEq] at halphaEnds
          simpa [ZY] using halphaEnds.symm.trans hlastAZends
        intro j
        obtain ⟨pj, hpj⟩ := Z.attaches (⟨6 + j.val, by omega⟩ : Fin Z.length)
        have hincC : Incident G (ZY ⟨7 + j.val, by omega⟩) (ZE j) := by
          rw [Incident, hpj]
          rw [Sym2.mem_iff]
          left
          apply congrArg Z.vertex
          apply Fin.ext
          change 7 + j.val = 6 + j.val + 1
          omega
        rcases Sym2.eq_iff.mp houtside with hout | hout
        · fin_cases j
          · have heq : ZE 0 = f1 := by
              by_contra hne
              have hi : Incident G (ZY 7) f1 := by
                rw [Incident, hf1ends]
                simp [ZY, hout.1]
              exact (hproperZ hne ⟨ZY 7, hincC, hi⟩ (hcolors 0)) hf1color
            refine ⟨1, ?_⟩
            change G.ends (ZE 0) = s(ZY 1, ZY 7)
            rw [heq]
            simpa [ZY, hout.1] using hf1ends
          · have heq : ZE 1 = f2 := by
              by_contra hne
              have hi : Incident G (ZY 8) f2 := by
                rw [Incident, hf2ends]
                simp [ZY, hout.2]
              exact (hproperZ hne ⟨ZY 8, hincC, hi⟩ (hcolors 1)) hf2color
            refine ⟨4, ?_⟩
            change G.ends (ZE 1) = s(ZY 4, ZY 8)
            rw [heq]
            simpa [ZY, hout.2] using hf2ends
        · fin_cases j
          · have heq : ZE 0 = f2 := by
              by_contra hne
              have hi : Incident G (ZY 7) f2 := by
                rw [Incident, hf2ends]
                simp [ZY, hout.2]
              exact (hproperZ hne ⟨ZY 7, hincC, hi⟩ (hcolors 0)) hf2color
            refine ⟨4, ?_⟩
            change G.ends (ZE 0) = s(ZY 4, ZY 7)
            rw [heq]
            simpa [ZY, hout.2] using hf2ends
          · have heq : ZE 1 = f1 := by
              by_contra hne
              have hi : Incident G (ZY 8) f1 := by
                rw [Incident, hf1ends]
                simp [ZY, hout.1]
              exact (hproperZ hne ⟨ZY 8, hincC, hi⟩ (hcolors 1)) hf1color
            refine ⟨1, ?_⟩
            change G.ends (ZE 1) = s(ZY 1, ZY 8)
            rw [heq]
            simpa [ZY, hout.1] using hf1ends
      have hsecondAttach : ∀ j : Fin 2, ∃ q : Fin 5,
          G.ends (X.edge ⟨6 + j.val, by omega⟩) =
            s(X.vertex ⟨q.val, by omega⟩,
              X.vertex ⟨7 + j.val, by omega⟩) := by
        by_cases hmzero : m.val = 0
        · have hm : m = 0 := Fin.ext hmzero
          exact localizeZero psi X Q hbalX hlenX hheightX d1
            (by simpa [hm] using hd1missing) hd1alpha hd1beta lastA lastB
            hlastAends hlastAcolor hlastBends hlastBcolor hsecondColor
            (by simpa [C, Y] using hcross)
        · let jQ : Fin Q.height := ⟨m.val, by
              rw [hheightX]
              exact m.isLt⟩
          have hjQ : 1 ≤ jQ.val := by
            simp [jQ]
            omega
          obtain ⟨rho, A, B, hAB, hA, hB, hproperR, honeR, hmissA,
              hmissB, hshiftR, hfixedR, htailColorR⟩ :=
            ScheideTrunkRotationColoring G k eX psi X Q hbalX jQ hjQ
          obtain ⟨Z, hglobalZ, hlengthZ, hverticesZ, htrunkVerticesZ,
              htailVerticesZ, htrunkEdgesZ, htailEdgesZ⟩ :=
            ScheideTrunkRotationTree G k eX psi rho X Q hbalX jQ hjQ A B
              hAB hA hB hproperR honeR hmissA hmissB hshiftR hfixedR
          obtain ⟨R, hheightR, halphaR, hbetaR, predR, hpredR,
              hclosingR⟩ :=
            ScheideTrunkRotationNormal G k eX psi rho X Q hbalX jQ hjQ A B
              hAB hA hB hshiftR hfixedR Z hglobalZ hmissA hmissB hlengthZ
              htrunkVerticesZ htrunkEdgesZ
          have hbalR : BalancedGlobalMaximumTriple R := by
            constructor
            · rw [hheightR]
              exact hbalX.1
            · intro q hlow hupp
              have hlow' : Q.height < 2 * q := by
                rw [hheightR] at hlow
                exact hlow
              have hupp' : 2 * q < X.length + 1 := by
                rw [hlengthZ] at hupp
                exact hupp
              have hqbound : 6 ≤ 2 * q := by
                rw [hheightX] at hlow'
                omega
              let z4 : Fin Z.length := ⟨2 * q - 2, by omega⟩
              let z5 : Fin Z.length := ⟨2 * q - 1, by omega⟩
              obtain ⟨x4, hx4val, hx4edge⟩ := htailEdgesZ z4 (by
                dsimp [z4]
                rw [hheightX]
                omega)
              obtain ⟨x5, hx5val, hx5edge⟩ := htailEdgesZ z5 (by
                dsimp [z5]
                rw [hheightX]
                omega)
              have hx4 : x4 = (⟨2 * q - 2, by omega⟩ : Fin X.length) := by
                apply Fin.ext
                simpa [z4] using hx4val
              have hx5 : x5 = (⟨2 * q - 1, by omega⟩ : Fin X.length) := by
                apply Fin.ext
                simpa [z5] using hx5val
              have hx4tail : Q.height - 1 ≤ x4.val := by
                rw [hheightX, hx4]
                change 4 ≤ 2 * q - 2
                omega
              have hx5tail : Q.height - 1 ≤ x5.val := by
                rw [hheightX, hx5]
                change 4 ≤ 2 * q - 1
                omega
              change rho (Z.edge z4) = rho (Z.edge z5)
              calc
                rho (Z.edge z4) = rho (X.edge x4) := congrArg rho hx4edge
                _ = psi (X.edge x4) := htailColorR x4 hx4tail
                _ = psi (X.edge x5) := by
                  rw [hx4, hx5]
                  exact hbalX.2 q hlow' hupp'
                _ = rho (X.edge x5) := (htailColorR x5 hx5tail).symm
                _ = rho (Z.edge z5) := congrArg rho hx5edge.symm
          have hlengthR : Z.length = 8 := hlengthZ.trans hlenX
          have hheightR5 : R.height = 5 := hheightR.trans hheightX
          have hnewZero : Z.vertex ⟨0, Nat.zero_lt_succ Z.length⟩ =
              X.vertex (Fin.castLE Q.height_upper jQ) := by
            obtain ⟨i, hi, hv⟩ := htrunkVerticesZ
              (⟨0, Nat.zero_lt_succ Z.length⟩ : Fin (Z.length + 1))
              (by simpa [hheightX])
            have hij : i = jQ := by
              apply Fin.ext
              simpa [jQ, Nat.mod_eq_of_lt jQ.isLt] using hi
            simpa [hij] using hv
          have holdMissing : d1 ∈ MissingColors G psi
              (X.vertex (Fin.castLE Q.height_upper jQ)) := by
            have hidx : (⟨m.val, by omega⟩ : Fin (X.length + 1)) =
                Fin.castLE Q.height_upper jQ := by
              apply Fin.ext
              rfl
            simpa [hidx] using hd1missing
          have hmissingR : d1 ∈ MissingColors G rho
              (Z.vertex ⟨0, Nat.zero_lt_succ Z.length⟩) := by
            rw [hnewZero, MissingColors, Finset.mem_sdiff]
            refine ⟨Finset.mem_univ _, ?_⟩
            intro hpresent
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
              true_and] at hpresent
            obtain ⟨f, hfinc, hfcolor⟩ := hpresent
            by_cases haffected : ∃ i : Fin (jQ.val + 1),
                f = NormalCycleEdge Q
                  (Fin.castLE (Nat.succ_le_iff.mpr jQ.isLt) i)
            · obtain ⟨i, rfl⟩ := haffected
              by_cases hilast : i.val = jQ.val
              · have hieq : Fin.castLE (Nat.succ_le_iff.mpr jQ.isLt) i =
                    jQ := by
                  apply Fin.ext
                  simpa using hilast
                have hu := honeR.1
                rw [hieq] at hfcolor
                rw [hfcolor] at hu
                simp at hu
              · let t : Fin jQ.val := ⟨i.val, by omega⟩
                have hcast : Fin.castLE (Nat.le_of_lt jQ.isLt) t =
                    Fin.castLE (Nat.succ_le_iff.mpr jQ.isLt) i := by
                  apply Fin.ext
                  rfl
                have hs := hshiftR t
                rw [hcast, hfcolor] at hs
                have hcycleColor :=
                  (ScheideTrunkRotationCycle G k eX psi X Q hbalX).2.2.2.2
                    (⟨t.val + 1, by omega⟩ : Fin Q.height)
                    (Nat.succ_le_succ (Nat.zero_le _))
                by_cases ho : Odd (t.val + 1)
                · rw [if_pos ho] at hcycleColor
                  exact hd1alpha (Option.some.inj (hs.trans hcycleColor))
                · rw [if_neg ho] at hcycleColor
                  exact hd1beta (Option.some.inj (hs.trans hcycleColor))
            · have hfix := hfixedR f (by
                intro i hi
                exact haffected ⟨i, hi⟩)
              have holdColor : psi f = some d1 := hfix.symm.trans hfcolor
              have hnotPresent : d1 ∉ PresentColors G psi
                  (X.vertex (Fin.castLE Q.height_upper jQ)) := by
                simpa [MissingColors] using holdMissing
              exact hnotPresent (by
                simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
                  true_and]
                exact ⟨f, hfinc, holdColor⟩)
          have htailVertexR (r : Fin 9) (hr : 5 ≤ r.val) :
              Z.vertex ⟨r.val, by omega⟩ = X.vertex ⟨r.val, by omega⟩ := by
            obtain ⟨s, hsval, hsv⟩ := htailVerticesZ
              (⟨r.val, by omega⟩ : Fin (Z.length + 1)) (by
                rw [hheightX]
                exact hr)
            have hs : s = (⟨r.val, by omega⟩ : Fin (X.length + 1)) := by
              apply Fin.ext
              simpa using hsval
            simpa [hs] using hsv
          have htailEdgeR (r : Fin 2) :
              Z.edge ⟨6 + r.val, by omega⟩ =
                X.edge ⟨6 + r.val, by omega⟩ := by
            obtain ⟨s, hsval, hse⟩ := htailEdgesZ
              (⟨6 + r.val, by omega⟩ : Fin Z.length) (by
                rw [hheightX]
                change 4 ≤ 6 + r.val
                omega)
            have hs : s = (⟨6 + r.val, by omega⟩ : Fin X.length) := by
              apply Fin.ext
              simpa using hsval
            simpa [hs] using hse
          have hcolorsR : ∀ r : Fin 2,
              rho (Z.edge ⟨6 + r.val, by omega⟩) = some d1 := by
            intro r
            calc
              rho (Z.edge ⟨6 + r.val, by omega⟩) =
                  rho (X.edge ⟨6 + r.val, by omega⟩) :=
                congrArg rho (htailEdgeR r)
              _ = psi (X.edge ⟨6 + r.val, by omega⟩) :=
                htailColorR (⟨6 + r.val, by omega⟩ : Fin X.length) (by
                  rw [hheightX]
                  change 4 ≤ 6 + r.val
                  omega)
              _ = some d1 := hsecondColor r
          have hz7 : Z.vertex ⟨7, by omega⟩ = X.vertex ⟨7, by omega⟩ :=
            htailVertexR 7 (by norm_num)
          have hz8 : Z.vertex ⟨8, by omega⟩ = X.vertex ⟨8, by omega⟩ :=
            htailVertexR 8 (by norm_num)
          have htrunkNeTail (i : Fin Q.height) (r : Fin 9)
              (hr : 5 ≤ r.val) :
              X.vertex (Fin.castLE Q.height_upper i) ≠
                X.vertex ⟨r.val, by omega⟩ := by
            intro hv
            have hi := X.vertex_injective hv
            have hiv := congrArg (fun q : Fin (X.length + 1) => q.val) hi
            have hilt : i.val < 5 := by simpa [hheightX] using i.isLt
            have heq : i.val = r.val := by simpa using hiv
            omega
          have hcycleEndsR :=
            (ScheideTrunkRotationCycle G k eX psi X Q hbalX).2.2.2.1
          have lastFixed (f : E)
              (hfends : G.ends f =
                s(X.vertex ⟨7, by omega⟩, X.vertex ⟨8, by omega⟩)) :
              rho f = psi f := by
            apply hfixedR f
            intro i hfi
            let ci : Fin Q.height :=
              Fin.castLE (Nat.succ_le_iff.mpr jQ.isLt) i
            let ni : Fin Q.height :=
              ⟨(ci.val + 1) % Q.height, Nat.mod_lt _ (by omega)⟩
            have hpairs :
                s(X.vertex ⟨7, by omega⟩, X.vertex ⟨8, by omega⟩) =
                  s(X.vertex (Fin.castLE Q.height_upper ci),
                    X.vertex (Fin.castLE Q.height_upper ni)) := by
              calc
                s(X.vertex ⟨7, by omega⟩, X.vertex ⟨8, by omega⟩) =
                    G.ends f := hfends.symm
                _ = G.ends (NormalCycleEdge Q ci) := congrArg G.ends hfi
                _ = s(X.vertex (Fin.castLE Q.height_upper ci),
                    X.vertex (Fin.castLE Q.height_upper ni)) := by
                  simpa [ci, ni] using hcycleEndsR ci
            rcases Sym2.eq_iff.mp hpairs with hp | hp
            · exact (htrunkNeTail ci 7 (by norm_num)) hp.1.symm
            · exact (htrunkNeTail ni 7 (by norm_num)) hp.1.symm
          have hlastAFixed : rho lastA = psi lastA :=
            lastFixed lastA hlastAends
          have hlastBFixed : rho lastB = psi lastB :=
            lastFixed lastB hlastBends
          have hlastAREnds : G.ends lastA =
              s(Z.vertex ⟨7, by omega⟩, Z.vertex ⟨8, by omega⟩) := by
            simpa [hz7, hz8] using hlastAends
          have hlastBREnds : G.ends lastB =
              s(Z.vertex ⟨7, by omega⟩, Z.vertex ⟨8, by omega⟩) := by
            simpa [hz7, hz8] using hlastBends
          have htrunkPreimage (q : Fin 5) : ∃ r : Fin 5,
              Z.vertex ⟨r.val, by omega⟩ = X.vertex ⟨q.val, by omega⟩ := by
            let qQ : Fin Q.height := ⟨q.val, by
              rw [hheightX]
              exact q.isLt⟩
            let r : Fin 5 :=
              ⟨(q.val + 5 - m.val) % 5, Nat.mod_lt _ (by norm_num)⟩
            obtain ⟨i, hi, hv⟩ := htrunkVerticesZ
              (⟨r.val, by omega⟩ : Fin (Z.length + 1)) (by
                rw [hheightX]
                exact r.isLt)
            have hiq : i = qQ := by
              apply Fin.ext
              rw [hi]
              change (jQ.val + r.val) % Q.height = qQ.val
              simpa [jQ, r, qQ, hheightX] using
                (show (m.val + ((q.val + 5 - m.val) % 5)) % 5 = q.val by
                  omega)
            refine ⟨r, ?_⟩
            simpa [hiq, qQ] using hv
          have hcrossR : ∃ r : Fin 2, ∃ q : Fin 5,
              G.ends (Z.edge ⟨6 + r.val, by omega⟩) =
                s(Z.vertex ⟨q.val, by omega⟩,
                  Z.vertex ⟨7 + r.val, by omega⟩) := by
            obtain ⟨r, q, hc⟩ := hcross
            obtain ⟨qR, hqR⟩ := htrunkPreimage q
            refine ⟨r, qR, ?_⟩
            have hc' : G.ends (X.edge ⟨6 + r.val, by omega⟩) =
                s(X.vertex ⟨q.val, by omega⟩,
                  X.vertex ⟨7 + r.val, by omega⟩) := by
              simpa [C, Y] using hc
            calc
              G.ends (Z.edge ⟨6 + r.val, by omega⟩) =
                  G.ends (X.edge ⟨6 + r.val, by omega⟩) :=
                congrArg G.ends (htailEdgeR r)
              _ = s(X.vertex ⟨q.val, by omega⟩,
                  X.vertex ⟨7 + r.val, by omega⟩) := hc'
              _ = s(Z.vertex ⟨qR.val, by omega⟩,
                  Z.vertex ⟨7 + r.val, by omega⟩) := by
                rw [hqR, htailVertexR ⟨7 + r.val, by omega⟩ (by
                  change 5 ≤ 7 + r.val
                  omega)]
          have hlocalized : ∀ r : Fin 2, ∃ q : Fin 5,
              G.ends (Z.edge ⟨6 + r.val, by omega⟩) =
                s(Z.vertex ⟨q.val, by omega⟩,
                  Z.vertex ⟨7 + r.val, by omega⟩) := by
            by_cases ho : Odd jQ.val
            · have hAe : A = Q.beta := by simpa [ho] using hA
              have hBe : B = Q.alpha := by simpa [ho] using hB
              have hdA : d1 ≠ R.alpha := by
                rw [halphaR, hAe]
                exact hd1beta
              have hdB : d1 ≠ R.beta := by
                rw [hbetaR, hBe]
                exact hd1alpha
              exact localizeZero rho Z R hbalR hlengthR hheightR5 d1
                hmissingR hdA hdB lastB lastA hlastBREnds
                (by rw [halphaR, hAe]; exact hlastBFixed.trans hlastBcolor)
                hlastAREnds
                (by rw [hbetaR, hBe]; exact hlastAFixed.trans hlastAcolor)
                hcolorsR hcrossR
            · have hAe : A = Q.alpha := by simpa [ho] using hA
              have hBe : B = Q.beta := by simpa [ho] using hB
              have hdA : d1 ≠ R.alpha := by
                rw [halphaR, hAe]
                exact hd1alpha
              have hdB : d1 ≠ R.beta := by
                rw [hbetaR, hBe]
                exact hd1beta
              exact localizeZero rho Z R hbalR hlengthR hheightR5 d1
                hmissingR hdA hdB lastA lastB hlastAREnds
                (by rw [halphaR, hAe]; exact hlastAFixed.trans hlastAcolor)
                hlastBREnds
                (by rw [hbetaR, hBe]; exact hlastBFixed.trans hlastBcolor)
                hcolorsR hcrossR
          intro r
          obtain ⟨q, hq⟩ := hlocalized r
          obtain ⟨i, hi, hvertex⟩ := htrunkVerticesZ
            (⟨q.val, by omega⟩ : Fin (Z.length + 1)) (by
              rw [hheightX]
              exact q.isLt)
          let i5 : Fin 5 := ⟨i.val, by
            rw [← hheightX]
            exact i.isLt⟩
          refine ⟨i5, ?_⟩
          calc
            G.ends (X.edge ⟨6 + r.val, by omega⟩) =
                G.ends (Z.edge ⟨6 + r.val, by omega⟩) :=
              congrArg G.ends (htailEdgeR r).symm
            _ = s(Z.vertex ⟨q.val, by omega⟩,
                Z.vertex ⟨7 + r.val, by omega⟩) := hq
            _ = s(X.vertex ⟨i5.val, by omega⟩,
                X.vertex ⟨7 + r.val, by omega⟩) := by
              rw [hvertex, htailVertexR ⟨7 + r.val, by omega⟩ (by
                change 5 ≤ 7 + r.val
                omega)]
              rfl
      have hfirstAttach : ∀ j : Fin 2, ∃ q : Fin 5,
          G.ends (X.edge ⟨4 + j.val, by omega⟩) =
            s(X.vertex ⟨q.val, by omega⟩,
              X.vertex ⟨5 + j.val, by omega⟩) := by
        intro j
        rcases hfirstOrient with ho | ho
        · fin_cases j
          · refine ⟨1, ?_⟩
            change G.ends (X.edge ⟨4, by omega⟩) =
              s(X.vertex ⟨1, by omega⟩, X.vertex ⟨5, by omega⟩)
            rw [ho.1]
            simpa [ho.2.1] using hx1ends
          · refine ⟨4, ?_⟩
            change G.ends (X.edge ⟨5, by omega⟩) =
              s(X.vertex ⟨4, by omega⟩, X.vertex ⟨6, by omega⟩)
            rw [ho.2.2.1]
            simpa [ho.2.2.2] using hx2ends
        · fin_cases j
          · refine ⟨4, ?_⟩
            change G.ends (X.edge ⟨4, by omega⟩) =
              s(X.vertex ⟨4, by omega⟩, X.vertex ⟨5, by omega⟩)
            rw [ho.1]
            simpa [ho.2.1] using hx2ends
          · refine ⟨1, ?_⟩
            change G.ends (X.edge ⟨5, by omega⟩) =
              s(X.vertex ⟨1, by omega⟩, X.vertex ⟨6, by omega⟩)
            rw [ho.2.2.1]
            simpa [ho.2.2.2] using hx1ends
      have hfirstColor : ∀ j : Fin 2,
          psi (X.edge ⟨4 + j.val, by omega⟩) = some d0 := by
        intro j
        rcases hfirstOrient with ho | ho
        · fin_cases j
          · simpa [ho.1] using hx1color
          · simpa [ho.2.2.1] using hx2color
        · fin_cases j
          · simpa [ho.1] using hx2color
          · simpa [ho.2.2.1] using hx1color
      obtain ⟨_, _, _, hcycleEnds, hcycleColors⟩ :=
        ScheideTrunkRotationCycle G k eX psi X Q hbalX
      have hbaseAlpha1 : psi (X.edge ⟨1, by omega⟩) = some Q.alpha := by
        simpa [NormalCycleEdge, hheightX] using hcycleColors
          (⟨1, by omega⟩ : Fin Q.height) (by norm_num)
      have hbaseBeta2 : psi (X.edge ⟨2, by omega⟩) = some Q.beta := by
        have hc := hcycleColors
          (⟨2, by omega⟩ : Fin Q.height) (by norm_num)
        have heven : ¬ Odd 2 := by
          intro ho
          obtain ⟨x, hx⟩ := ho
          omega
        rw [if_neg heven] at hc
        simpa [NormalCycleEdge, hheightX] using hc
      have hbaseAlpha3 : psi (X.edge ⟨3, by omega⟩) = some Q.alpha := by
        have hc := hcycleColors
          (⟨3, by omega⟩ : Fin Q.height) (by norm_num)
        have hodd : Odd 3 := ⟨1, by norm_num⟩
        rw [if_pos hodd] at hc
        simpa [NormalCycleEdge, hheightX] using hc
      let gamma : Fin 2 → Fin k := fun i => if i = 0 then d0 else d1
      refine ⟨hbalX, hlenX, hheightX, gamma, ?_, ?_, ?_, ?_, ?_⟩
      · intro a b hab
        fin_cases a <;> fin_cases b
        · rfl
        · simp [gamma] at hab
          exact False.elim (hd10 hab.symm)
        · simp [gamma] at hab
          exact False.elim (hd10 hab)
        · rfl
      · intro i j
        fin_cases i
        · simpa using hfirstAttach j
        · simpa using hsecondAttach j
      · intro i j
        fin_cases i
        · simpa [gamma] using hfirstColor j
        · simpa [gamma] using hsecondColor j
      · intro i
        fin_cases i
        · exact ⟨0, by simpa [gamma] using hd0missing⟩
        · exact ⟨m, by simpa [gamma] using hd1missing⟩
      · intro i hi c hc r
        fin_cases i
        · norm_num at hi
        · have hc' : c = Q.alpha := by
            exact Option.some.inj (hc.symm.trans hbaseAlpha1)
          fin_cases r
          · simpa [gamma, hc'] using hd0alpha.symm
          · simpa [gamma, hc'] using hd1alpha.symm
        · have hc' : c = Q.beta := by
            exact Option.some.inj (hc.symm.trans hbaseBeta2)
          fin_cases r
          · simpa [gamma, hc'] using hd0beta.symm
          · simpa [gamma, hc'] using hd1beta.symm
        · have hc' : c = Q.alpha := by
            exact Option.some.inj (hc.symm.trans hbaseAlpha3)
          fin_cases r
          · simpa [gamma, hc'] using hd0alpha.symm
          · simpa [gamma, hc'] using hd1alpha.symm
    by_cases hwbase : 5 ≤ w.val
    · obtain ⟨S', M', hlen', hheight', hbal', hv0', hv1', hv2', hv3',
          hv4', hv5', hv6', hv7', hv8', he0', he1', he2', he3', he4',
          he5', he6', he7', hMalpha, hMbeta⟩ := rebase hwbase
      have hwcases : w.val = 5 ∨ w.val = 6 := by
        have hwlt : w.val < 7 := by simpa [r6'] using w.isLt
        omega
      obtain ⟨m', hmvertex⟩ : ∃ m' : Fin 5,
          S'.vertex ⟨m'.val, by omega⟩ = S.vertex ⟨w.val, by omega⟩ := by
        rcases hwcases with hw5 | hw6
        · rcases horient with ho | ho
          · refine ⟨2, ?_⟩
            calc
              S'.vertex ⟨(2 : Fin 5).val, by omega⟩ =
                  S'.vertex ⟨2, by omega⟩ := by congr 1
              _ = v1 := hv2'
              _ = y5 := ho.2.1.symm
              _ = S.vertex ⟨w.val, by omega⟩ := by
                apply congrArg S.vertex
                apply Fin.ext
                simpa [y5] using hw5.symm
          · refine ⟨3, ?_⟩
            calc
              S'.vertex ⟨(3 : Fin 5).val, by omega⟩ =
                  S'.vertex ⟨3, by omega⟩ := by congr 1
              _ = v2 := hv3'
              _ = y5 := ho.2.1.symm
              _ = S.vertex ⟨w.val, by omega⟩ := by
                apply congrArg S.vertex
                apply Fin.ext
                simpa [y5] using hw5.symm
        · rcases horient with ho | ho
          · refine ⟨3, ?_⟩
            calc
              S'.vertex ⟨(3 : Fin 5).val, by omega⟩ =
                  S'.vertex ⟨3, by omega⟩ := by congr 1
              _ = v2 := hv3'
              _ = y6 := ho.2.2.2.symm
              _ = S.vertex ⟨w.val, by omega⟩ := by
                apply congrArg S.vertex
                apply Fin.ext
                simpa [y6] using hw6.symm
          · refine ⟨2, ?_⟩
            calc
              S'.vertex ⟨(2 : Fin 5).val, by omega⟩ =
                  S'.vertex ⟨2, by omega⟩ := by congr 1
              _ = v1 := hv2'
              _ = y6 := ho.2.2.2.symm
              _ = S.vertex ⟨w.val, by omega⟩ := by
                apply congrArg S.vertex
                apply Fin.ext
                simpa [y6] using hw6.symm
      refine ⟨e, psi, S', M', ?_⟩
      refine complete S' M' hbal' hlen' hheight' M.alpha g1
        (by rw [hv0']; simpa [y0] using M.alpha_missing) m'
        (by rw [hmvertex]; exact hwmissing')
        (by rw [hMalpha]; exact hg0alpha.symm)
        (by rw [hMbeta]; exact hab)
        (by rw [hMalpha]; exact hg10)
        (by rw [hMbeta]; exact hg1beta)
        hg1alpha a1 a3 a2 alphaLast g0last betaLast y2 y3
        (by simpa only [hv1'] using ha1ends)
        (by simpa only [hv4', Sym2.eq_swap] using ha3ends)
        ha1color ha3color ha2ends
        (by rw [hMbeta]; exact ha2color)
        (by simpa only [hv7', hv8'] using halphaLastEnds)
        halphaLastColor
        (by simpa only [hv7', hv8'] using hg0lastEnds)
        (by rw [hMalpha]; exact hg0lastColor)
        (by simpa only [hv7', hv8'] using hbetaLastEnds)
        (by rw [hMbeta]; exact hbetaLastColor)
        (Or.inl ⟨he4', hv5', he5', hv6'⟩) ?_
      intro j
      fin_cases j
      · simpa only using (he6' ▸ hc0color')
      · simpa only using (he7' ▸ hc1color)
    · have hwlt : w.val < 5 := by omega
      let m' : Fin 5 := ⟨w.val, hwlt⟩
      refine ⟨e, psi, S, M, ?_⟩
      refine complete S M hbal hlen hheight g0 g1 hg0' m'
        (by simpa [m'] using hwmissing') hg0alpha hg0beta hg1alpha hg1beta
        hg10 f1 f2 beta56 g0last alphaLast betaLast v1 v2 hf1ends' hf2ends'
        hf1color hf2color hbeta56ends hbeta56color hg0lastEnds hg0lastColor
        halphaLastEnds halphaLastColor
        hbetaLastEnds hbetaLastColor
        (by simpa [b0, b1, y5, y6] using horient) ?_
      intro j
      fin_cases j
      · simpa [c0] using hc0color'
      · simpa [c1] using hc1color
  by_cases hw0zero : w0.val = 0
  · have hw0vertex :
        T.vertex (Fin.castLT w0
          (Nat.lt_trans w0.isLt (Nat.succ_lt_succ r4.isLt))) =
          T.vertex ⟨0, Nat.zero_lt_succ T.length⟩ := by
      apply congrArg T.vertex
      apply Fin.ext
      simpa using hw0zero
    exact finish phi T N hbalanced hlength hNheight gamma0
      (by simpa [r4] using hr4color)
      (by simpa [r5] using hr5color)
      (by simpa [hw0vertex] using hw0missing)
  · let j : Fin N.height := ⟨w0.val, by
        have hw : w0.val < 5 := by simpa [r4] using w0.isLt
        rw [hNheight]
        exact hw⟩
    have hj : 1 ≤ j.val := by
      simp [j]
      omega
    obtain ⟨psi, A, B, hAB, hA, hB, hproper, hone, hmissA, hmissB,
        hshift, hfixed, htailColor⟩ :=
      ScheideTrunkRotationColoring G k e0 phi T N hbalanced j hj
    obtain ⟨S, hglobalS, hlengthS, hverticesS, htrunkVerticesS,
        htailVerticesS, htrunkEdgesS, htailEdgesS⟩ :=
      ScheideTrunkRotationTree G k e0 phi psi T N hbalanced j hj A B
        hAB hA hB hproper hone hmissA hmissB hshift hfixed
    obtain ⟨M, hheightM, halphaM, hbetaM, pred, hpred, hclosingM⟩ :=
      ScheideTrunkRotationNormal G k e0 phi psi T N hbalanced j hj A B
        hAB hA hB hshift hfixed S hglobalS hmissA hmissB hlengthS
        htrunkVerticesS htrunkEdgesS
    have hbalM : BalancedGlobalMaximumTriple M := by
      constructor
      · rw [hheightM]
        exact hbalanced.1
      · intro q hlow hupp
        have hlow' : N.height < 2 * q := by
          rw [hheightM] at hlow
          exact hlow
        have hupp' : 2 * q < T.length + 1 := by
          rw [hlengthS] at hupp
          exact hupp
        have hqbound : 6 ≤ 2 * q := by
          rw [hNheight] at hlow'
          omega
        let s4 : Fin S.length := ⟨2 * q - 2, by omega⟩
        let s5 : Fin S.length := ⟨2 * q - 1, by omega⟩
        obtain ⟨t4, ht4val, ht4edge⟩ := htailEdgesS s4 (by
          dsimp [s4]
          omega)
        obtain ⟨t5, ht5val, ht5edge⟩ := htailEdgesS s5 (by
          dsimp [s5]
          omega)
        have ht4 : t4 = (⟨2 * q - 2, by omega⟩ : Fin T.length) := by
          apply Fin.ext
          simpa [s4] using ht4val
        have ht5 : t5 = (⟨2 * q - 1, by omega⟩ : Fin T.length) := by
          apply Fin.ext
          simpa [s5] using ht5val
        change psi (S.edge s4) = psi (S.edge s5)
        calc
          psi (S.edge s4) = psi (T.edge t4) := congrArg psi ht4edge
          _ = phi (T.edge t4) := htailColor t4 (by
            rw [ht4, hNheight]
            change 4 ≤ 2 * q - 2
            omega)
          _ = phi (T.edge t5) := by
            rw [ht4, ht5]
            exact hbalanced.2 q hlow' hupp'
          _ = psi (T.edge t5) := (htailColor t5 (by
            rw [ht5, hNheight]
            change 4 ≤ 2 * q - 1
            omega)).symm
          _ = psi (S.edge s5) := congrArg psi ht5edge.symm
    have hnewZero : S.vertex ⟨0, Nat.zero_lt_succ S.length⟩ =
        T.vertex (Fin.castLE N.height_upper j) := by
      obtain ⟨i, hi, hv⟩ := htrunkVerticesS
        (⟨0, Nat.zero_lt_succ S.length⟩ : Fin (S.length + 1))
        (by simpa [hNheight])
      have hij : i = j := by
        apply Fin.ext
        simpa [j, Nat.mod_eq_of_lt j.isLt] using hi
      simpa [hij] using hv
    have holdMissing : gamma0 ∈ MissingColors G phi
        (T.vertex (Fin.castLE N.height_upper j)) := by
      have hidx : Fin.castLT w0
          (Nat.lt_trans w0.isLt (Nat.succ_lt_succ r4.isLt)) =
          Fin.castLE N.height_upper j := by
        apply Fin.ext
        rfl
      simpa [hidx] using hw0missing
    have horderData := ScheideGlobalMaximumOrder G k e0 phi T N.global
    have helem : ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet T) := horderData.2.2.2.1
    have hgammaAlpha : gamma0 ≠ N.alpha := by
      intro hga
      have hzeroMem : T.vertex ⟨0, Nat.zero_lt_succ T.length⟩ ∈
          TreeSequenceVertexSet T := by simp [TreeSequenceVertexSet]
      have hjMem : T.vertex (Fin.castLE N.height_upper j) ∈
          TreeSequenceVertexSet T := by simp [TreeSequenceVertexSet]
      have hne : T.vertex (Fin.castLE N.height_upper j) ≠
          T.vertex ⟨0, Nat.zero_lt_succ T.length⟩ := by
        intro hv
        have hi := T.vertex_injective hv
        have hiv := congrArg Fin.val hi
        have hz : j.val = 0 := by simpa using hiv
        exact (Nat.ne_of_gt hj) hz
      have hd := helem hjMem hzeroMem hne
      exact (Finset.disjoint_left.mp hd) holdMissing
        (by simpa [hga] using N.alpha_missing)
    have hgammaNew : gamma0 ∈ MissingColors G psi
        (S.vertex ⟨0, Nat.zero_lt_succ S.length⟩) := by
      rw [hnewZero]
      by_cases hgb : gamma0 = N.beta
      · have hjone : j.val = 1 := by
          by_contra hne
          have honeMem : T.vertex ⟨1, by omega⟩ ∈
              TreeSequenceVertexSet T := by simp [TreeSequenceVertexSet]
          have hjMem : T.vertex (Fin.castLE N.height_upper j) ∈
              TreeSequenceVertexSet T := by simp [TreeSequenceVertexSet]
          have hvne : T.vertex (Fin.castLE N.height_upper j) ≠
              T.vertex ⟨1, by omega⟩ := by
            intro hv
            have hi := T.vertex_injective hv
            exact hne (by simpa using congrArg Fin.val hi)
          have hd := helem hjMem honeMem hvne
          exact (Finset.disjoint_left.mp hd) holdMissing
            (by simpa [hgb] using N.beta_missing)
        have hjodd : Odd j.val := by
          rw [hjone]
          exact odd_one
        have hAeq : A = gamma0 := by simpa [hgb, hjodd] using hA
        simpa [hAeq] using hmissA
      · have hgammaBeta : gamma0 ≠ N.beta := hgb
        rw [MissingColors, Finset.mem_sdiff]
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hpresent
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and] at hpresent
        obtain ⟨f, hfinc, hfcolor⟩ := hpresent
        by_cases haffected : ∃ i : Fin (j.val + 1),
            f = NormalCycleEdge N
              (Fin.castLE (Nat.succ_le_iff.mpr j.isLt) i)
        · obtain ⟨i, rfl⟩ := haffected
          by_cases hilast : i.val = j.val
          · have hieq : Fin.castLE (Nat.succ_le_iff.mpr j.isLt) i = j := by
              apply Fin.ext
              simpa using hilast
            have hu := hone.1
            rw [hieq] at hfcolor
            rw [hfcolor] at hu
            simp at hu
          · let t : Fin j.val := ⟨i.val, by omega⟩
            have hcast : Fin.castLE (Nat.le_of_lt j.isLt) t =
                Fin.castLE (Nat.succ_le_iff.mpr j.isLt) i := by
              apply Fin.ext
              rfl
            have hs := hshift t
            rw [hcast, hfcolor] at hs
            have hcycle :=
              (ScheideTrunkRotationCycle G k e0 phi T N hbalanced).2.2.2.2
                (⟨t.val + 1, by
                  have htj := t.isLt
                  have hjN := j.isLt
                  omega⟩ : Fin N.height) (Nat.succ_le_succ (Nat.zero_le _))
            by_cases ho : Odd (t.val + 1)
            · rw [if_pos ho] at hcycle
              have : gamma0 = N.alpha := Option.some.inj (hs.trans hcycle)
              exact hgammaAlpha this
            · rw [if_neg ho] at hcycle
              have : gamma0 = N.beta := Option.some.inj (hs.trans hcycle)
              exact hgammaBeta this
        · have hfix := hfixed f (by
            intro i hi
            exact haffected ⟨i, hi⟩)
          have holdColor : phi f = some gamma0 := hfix.symm.trans hfcolor
          have hnotPresent : gamma0 ∉ PresentColors G phi
              (T.vertex (Fin.castLE N.height_upper j)) := by
            simpa [MissingColors] using holdMissing
          exact hnotPresent (by
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
              true_and]
            exact ⟨f, hfinc, holdColor⟩)
    have hS4 : psi (S.edge ⟨4, by omega⟩) = some gamma0 := by
      obtain ⟨t, htval, htedge⟩ := htailEdgesS
        (⟨4, by omega⟩ : Fin S.length) (by simpa [hNheight])
      have ht : t = r4 := by
        apply Fin.ext
        simpa [r4] using htval
      calc
        psi (S.edge ⟨4, by omega⟩) = psi (T.edge t) := congrArg psi htedge
        _ = psi (T.edge r4) := congrArg (fun f => psi (T.edge f)) ht
        _ = phi (T.edge r4) := htailColor r4 (by simpa [hNheight, r4])
        _ = some gamma0 := hr4color
    have hS5 : psi (S.edge ⟨5, by omega⟩) = some gamma0 := by
      obtain ⟨t, htval, htedge⟩ := htailEdgesS
        (⟨5, by omega⟩ : Fin S.length) (by simpa [hNheight])
      have ht : t = r5 := by
        apply Fin.ext
        simpa [r5] using htval
      calc
        psi (S.edge ⟨5, by omega⟩) = psi (T.edge t) := congrArg psi htedge
        _ = psi (T.edge r5) := congrArg (fun f => psi (T.edge f)) ht
        _ = phi (T.edge r5) := htailColor r5 (by simpa [hNheight, r5])
        _ = some gamma0 := hr5color
    exact finish psi S M hbalM
      (hlengthS.trans hlength) (hheightM.trans hNheight) gamma0 hS4 hS5
      hgammaNew
