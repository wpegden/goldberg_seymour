import Tablet.AdjacentEdges
import Tablet.BalancedGlobalMaximumTriple
import Tablet.ColoredVertexSetElementary
import Tablet.Critical
import Tablet.Elementary
import Tablet.FixedPairMaximalTashkinovTree
import Tablet.GlobalMaximumTriple
import Tablet.GlobalMaximumTripleExists
import Tablet.Incident
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MaximumDegree
import Tablet.MissingColors
import Tablet.NormalGlobalMaximumTriple
import Tablet.PresentColors
import Tablet.ScheideBalancedExists
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideGraphHeight
import Tablet.ScheideGraphHeightOdd
import Tablet.ScheideKempePathHeightBound
import Tablet.ScheideLargeHeightElementary
import Tablet.ScheideMaximalKempePath
import Tablet.ScheideTrunkRotationPreserves
import Tablet.TashkinovOrder
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TrunkRotation
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideSmallHeightElementary]
theorem ScheideSmallHeightElementary {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ)
    (hcritical : Critical G) (hindex : ChromaticIndex G = k + 1)
    (hdegree : MaximumDegree G + 1 ≤ k)
    (hnoisolated : ∀ v : V, ∃ e : E, Incident G v e)
    (hsmall : ScheideGraphHeight G < 5) :
    Elementary G := by
-- BODY
  classical
  obtain ⟨e0, phi0, T0, hglobal0⟩ :=
    GlobalMaximumTripleExists G k hcritical hindex hdegree
  have hheight : ScheideGraphHeight G = 3 := by
    have hodd := ScheideGraphHeightOdd G k e0 phi0 T0 hglobal0
    rcases hodd.2 with ⟨m, hm⟩
    omega
  obtain ⟨e0, phi, T, N, hbalanced⟩ :=
    ScheideBalancedExists G k e0 phi0 T0 hglobal0
  have hNheight : N.height = 3 := hbalanced.1.trans hheight
  letI : DecidableEq V := Classical.decEq V
  by_contra hnon
  have horder : 7 ≤ TashkinovOrder G := by
    have hnlt : ¬ TashkinovOrder G - 4 < ScheideGraphHeight G := by
      intro hlt
      exact hnon (ScheideLargeHeightElementary G k hcritical hindex hdegree
        hnoisolated hlt)
    omega
  have hcard : (TreeSequenceVertexSet T).card = T.length + 1 := by
    unfold TreeSequenceVertexSet
    rw [Finset.card_image_of_injective Finset.univ T.vertex_injective]
    simp
  have hlength : 6 ≤ T.length := by
    have hmax := N.global.2.2
    omega
  let v0 : Fin (T.length + 1) := ⟨0, by omega⟩
  let v1 : Fin (T.length + 1) := ⟨1, by omega⟩
  let v2 : Fin (T.length + 1) := ⟨2, by omega⟩
  let v3 : Fin (T.length + 1) := ⟨3, by omega⟩
  let v4 : Fin (T.length + 1) := ⟨4, by omega⟩
  let r1 : Fin T.length := ⟨1, by omega⟩
  let r2 : Fin T.length := ⟨2, by omega⟩
  let r3 : Fin T.length := ⟨3, by omega⟩
  have htail : phi (T.edge r2) = phi (T.edge r3) := by
    simpa [r2, r3] using hbalanced.2 2 (by omega) (by omega)
  obtain ⟨w, gamma, he2gamma, hwgamma⟩ := N.global.2.1 r2 (by simp [r2])
  have hw_bound : w.val < 3 := w.isLt
  have hwgamma' : gamma ∈ MissingColors G phi
      (T.vertex ⟨w.val, by omega⟩) := by
    have hidx : Fin.castLT w
        (Nat.lt_trans w.isLt (Nat.succ_lt_succ r2.isLt)) =
        (⟨w.val, by omega⟩ : Fin (T.length + 1)) := Fin.ext rfl
    rw [← hidx]
    exact hwgamma
  have he3gamma : phi (T.edge r3) = some gamma := by
    rw [← htail]
    exact he2gamma
  have hcycle := ScheideTrunkRotationCycle G k e0 phi T N hbalanced
  have hcycle_ends := hcycle.2.2.2.1
  have hcycle_colors := hcycle.2.2.2.2
  let c1 : Fin N.height := ⟨1, by omega⟩
  let c2 : Fin N.height := ⟨2, by omega⟩
  have hc1color : phi (NormalCycleEdge N c1) = some N.alpha := by
    simpa [c1] using hcycle_colors c1 (by simp [c1])
  have hc2color : phi (NormalCycleEdge N c2) = some N.beta := by
    have hnotodd : ¬ Odd (2 : ℕ) := by
      rintro ⟨x, hx⟩
      omega
    simpa [c2, hnotodd] using hcycle_colors c2 (by simp [c2])
  have hc1ends : G.ends (NormalCycleEdge N c1) =
      s(T.vertex v1, T.vertex v2) := by
    simpa [c1, v1, v2, hNheight] using hcycle_ends c1
  have hc2ends : G.ends (NormalCycleEdge N c2) =
      s(T.vertex v2, T.vertex v0) := by
    simpa [c2, v2, v0, hNheight] using hcycle_ends c2
  have hproper : IsProperEdgeColoring G phi := N.global.1.2.2.2.1
  have helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) :=
    (ScheideGlobalMaximumOrder G k e0 phi T N.global).2.2.2.1
  have hvertex_mem (i : Fin (T.length + 1)) :
      T.vertex i ∈ TreeSequenceVertexSet T := by
    simp [TreeSequenceVertexSet]
  have hmissing_absent {c : Fin k} {i : Fin (T.length + 1)}
      (hm : c ∈ MissingColors G phi (T.vertex i)) {f : E}
      (hinc : Incident G (T.vertex i) f) : phi f ≠ some c := by
    intro hfc
    have hp : c ∈ PresentColors G phi (T.vertex i) := by
      simp [PresentColors]
      exact ⟨f, hinc, hfc⟩
    have hnp : c ∉ PresentColors G phi (T.vertex i) := by
      simpa [MissingColors] using hm
    exact hnp hp
  obtain ⟨a2, ha2ends⟩ := T.attaches r2
  let a2' : Fin (T.length + 1) :=
    Fin.castLT a2 (Nat.lt_trans a2.isLt (Nat.succ_lt_succ r2.isLt))
  have ha2val : a2'.val < 3 := by simpa [a2', r2] using a2.isLt
  have ha2ends' : G.ends (T.edge r2) = s(T.vertex v3, T.vertex a2') := by
    simpa [r2, v3, a2'] using ha2ends
  have he2inc_new : Incident G (T.vertex v3) (T.edge r2) := by
    rw [Incident, ha2ends']
    simp
  have he2inc_attach : Incident G (T.vertex a2') (T.edge r2) := by
    rw [Incident, ha2ends']
    simp
  have ha2_ne_w : a2'.val ≠ w.val := by
    intro haw
    have hv : T.vertex a2' = T.vertex ⟨w.val, by omega⟩ := by
      apply congrArg T.vertex
      apply Fin.ext
      exact haw
    exact hmissing_absent hwgamma' (hv ▸ he2inc_attach) he2gamma
  have hw_eq_zero_of_alpha (hga : gamma = N.alpha) : w.val = 0 := by
    by_contra hw0
    have hne : T.vertex ⟨w.val, by omega⟩ ≠ T.vertex v0 := by
      intro hv
      have hi := T.vertex_injective hv
      apply hw0
      simpa [v0] using congrArg Fin.val hi
    have hd := helem (hvertex_mem ⟨w.val, by omega⟩) (hvertex_mem v0) hne
    exact (Finset.disjoint_left.mp hd) hwgamma' (by simpa [hga, v0] using N.alpha_missing)
  have hw_eq_one_of_beta (hgb : gamma = N.beta) : w.val = 1 := by
    by_contra hw1
    have hne : T.vertex ⟨w.val, by omega⟩ ≠ T.vertex v1 := by
      intro hv
      have hi := T.vertex_injective hv
      apply hw1
      simpa [v1] using congrArg Fin.val hi
    have hd := helem (hvertex_mem ⟨w.val, by omega⟩) (hvertex_mem v1) hne
    exact (Finset.disjoint_left.mp hd) hwgamma' (by simpa [hgb, v1] using N.beta_missing)
  have he2_ne_c1 : T.edge r2 ≠ NormalCycleEdge N c1 := by
    intro heq
    have hpairs : s(T.vertex v3, T.vertex a2') = s(T.vertex v1, T.vertex v2) := by
      rw [← ha2ends', ← hc1ends, heq]
    rcases Sym2.eq_iff.mp hpairs with h | h
    · have hi := T.vertex_injective h.1
      have := congrArg Fin.val hi
      simp [v3, v1] at this
    · have hi := T.vertex_injective h.1
      have := congrArg Fin.val hi
      simp [v3, v2] at this
  have he2_ne_c2 : T.edge r2 ≠ NormalCycleEdge N c2 := by
    intro heq
    have hpairs : s(T.vertex v3, T.vertex a2') = s(T.vertex v2, T.vertex v0) := by
      rw [← ha2ends', ← hc2ends, heq]
    rcases Sym2.eq_iff.mp hpairs with h | h
    · have hi := T.vertex_injective h.1
      have := congrArg Fin.val hi
      simp [v3, v2] at this
    · have hi := T.vertex_injective h.1
      have := congrArg Fin.val hi
      simp [v3, v0] at this
  have hgamma_alpha : gamma ≠ N.alpha := by
    intro hga
    have hw0 := hw_eq_zero_of_alpha hga
    have ha : a2'.val = 1 ∨ a2'.val = 2 := by omega
    have hinc : Incident G (T.vertex a2') (NormalCycleEdge N c1) := by
      rw [Incident, hc1ends]
      rcases ha with ha | ha
      · have hv : T.vertex a2' = T.vertex v1 := by
          apply congrArg T.vertex
          apply Fin.ext
          simpa [v1] using ha
        rw [hv]
        simp
      · have hv : T.vertex a2' = T.vertex v2 := by
          apply congrArg T.vertex
          apply Fin.ext
          simpa [v2] using ha
        rw [hv]
        simp
    have hadj : AdjacentEdges G (T.edge r2) (NormalCycleEdge N c1) :=
      ⟨T.vertex a2', he2inc_attach, hinc⟩
    exact (hproper he2_ne_c1 hadj he2gamma) (by simpa [hga] using hc1color)
  have hgamma_beta : gamma ≠ N.beta := by
    intro hgb
    have hw1 := hw_eq_one_of_beta hgb
    have ha : a2'.val = 0 ∨ a2'.val = 2 := by omega
    have hinc : Incident G (T.vertex a2') (NormalCycleEdge N c2) := by
      rw [Incident, hc2ends]
      rcases ha with ha | ha
      · have hv : T.vertex a2' = T.vertex v0 := by
          apply congrArg T.vertex
          apply Fin.ext
          simpa [v0] using ha
        rw [hv]
        simp
      · have hv : T.vertex a2' = T.vertex v2 := by
          apply congrArg T.vertex
          apply Fin.ext
          simpa [v2] using ha
        rw [hv]
        simp
    have hadj : AdjacentEdges G (T.edge r2) (NormalCycleEdge N c2) :=
      ⟨T.vertex a2', he2inc_attach, hinc⟩
    exact (hproper he2_ne_c2 hadj he2gamma) (by simpa [hgb] using hc2color)
  obtain ⟨a3, ha3ends⟩ := T.attaches r3
  let a3' : Fin (T.length + 1) :=
    Fin.castLT a3 (Nat.lt_trans a3.isLt (Nat.succ_lt_succ r3.isLt))
  have ha3val : a3'.val < 4 := by simpa [a3', r3] using a3.isLt
  have ha3ends' : G.ends (T.edge r3) = s(T.vertex v4, T.vertex a3') := by
    simpa [r3, v4, a3'] using ha3ends
  have he3inc_new : Incident G (T.vertex v4) (T.edge r3) := by
    rw [Incident, ha3ends']
    simp
  have he3inc_attach : Incident G (T.vertex a3') (T.edge r3) := by
    rw [Incident, ha3ends']
    simp
  have he23_ne : T.edge r2 ≠ T.edge r3 := by
    intro heq
    have hi := T.edge_injective heq
    have := congrArg Fin.val hi
    simp [r2, r3] at this
  have ha3_ne_three : a3'.val ≠ 3 := by
    intro ha
    have hv : T.vertex a3' = T.vertex v3 := by
      apply congrArg T.vertex
      apply Fin.ext
      simpa [v3] using ha
    have hadj : AdjacentEdges G (T.edge r2) (T.edge r3) :=
      ⟨T.vertex v3, he2inc_new, hv ▸ he3inc_attach⟩
    exact (hproper he23_ne hadj he2gamma) he3gamma
  have ha3trunk : a3'.val < 3 := by omega
  have ha3_ne_w : a3'.val ≠ w.val := by
    intro haw
    have hv : T.vertex a3' = T.vertex ⟨w.val, by omega⟩ := by
      apply congrArg T.vertex
      apply Fin.ext
      exact haw
    exact hmissing_absent hwgamma' (hv ▸ he3inc_attach) he3gamma
  have ha23_ne : a2'.val ≠ a3'.val := by
    intro ha
    have hv : T.vertex a2' = T.vertex a3' := by
      apply congrArg T.vertex
      apply Fin.ext
      exact ha
    have hadj : AdjacentEdges G (T.edge r2) (T.edge r3) :=
      ⟨T.vertex a2', he2inc_attach, hv ▸ he3inc_attach⟩
    exact (hproper he23_ne hadj he2gamma) he3gamma
  obtain ⟨e, psi, S, M, hSlen, hbalM, hMheight, hgamma0,
      htail2, htail3, hout2, hout3, hattach⟩ :
      ∃ (e : E) (psi : PartialEdgeColoring E k) (S : TreeSequence G e)
        (M : NormalGlobalMaximumTriple G k e psi S) (hSlen : 6 ≤ S.length),
        BalancedGlobalMaximumTriple M ∧ M.height = 3 ∧
        gamma ∈ MissingColors G psi
          (S.vertex ⟨0, by omega⟩) ∧
        psi (S.edge ⟨2, by omega⟩) = some gamma ∧
        psi (S.edge ⟨3, by omega⟩) = some gamma ∧
        Incident G (S.vertex ⟨3, by omega⟩) (S.edge ⟨2, by omega⟩) ∧
        Incident G (S.vertex ⟨4, by omega⟩) (S.edge ⟨3, by omega⟩) ∧
        ((Incident G (S.vertex ⟨1, by omega⟩) (S.edge ⟨2, by omega⟩) ∧
            Incident G (S.vertex ⟨2, by omega⟩) (S.edge ⟨3, by omega⟩)) ∨
          (Incident G (S.vertex ⟨2, by omega⟩) (S.edge ⟨2, by omega⟩) ∧
            Incident G (S.vertex ⟨1, by omega⟩) (S.edge ⟨3, by omega⟩))) := by
    by_cases hw0 : w.val = 0
    · have hpairs : (a2'.val = 1 ∧ a3'.val = 2) ∨
          (a2'.val = 2 ∧ a3'.val = 1) := by omega
      refine ⟨e0, phi, T, N, hlength, hbalanced, hNheight, ?_,
        he2gamma, he3gamma, he2inc_new, he3inc_new, ?_⟩
      · have hv : T.vertex ⟨0, by omega⟩ = T.vertex ⟨w.val, by omega⟩ := by
          apply congrArg T.vertex
          apply Fin.ext
          simpa using hw0.symm
        rw [hv]
        exact hwgamma'
      · rcases hpairs with h | h
        · left
          constructor
          · have hv : T.vertex ⟨1, by omega⟩ = T.vertex a2' := by
              apply congrArg T.vertex
              apply Fin.ext
              simpa using h.1.symm
            simpa [hv] using he2inc_attach
          · have hv : T.vertex ⟨2, by omega⟩ = T.vertex a3' := by
              apply congrArg T.vertex
              apply Fin.ext
              simpa using h.2.symm
            simpa [hv] using he3inc_attach
        · right
          constructor
          · have hv : T.vertex ⟨2, by omega⟩ = T.vertex a2' := by
              apply congrArg T.vertex
              apply Fin.ext
              simpa using h.1.symm
            simpa [hv] using he2inc_attach
          · have hv : T.vertex ⟨1, by omega⟩ = T.vertex a3' := by
              apply congrArg T.vertex
              apply Fin.ext
              simpa using h.2.symm
            simpa [hv] using he3inc_attach
    · have hwpos : 1 ≤ w.val := by omega
      let j : Fin N.height := ⟨w.val, by omega⟩
      obtain ⟨e1, psi, S, M, hrot, hbalM⟩ :=
        ScheideTrunkRotationPreserves G k e0 phi T N hbalanced j (by
          simpa [j] using hwpos)
      rcases hrot with ⟨_, _, _, hshift, hfixed, hSlength, hMheight0,
        hvertexSet, htrunkVertices, htailVertices, htrunkEdges,
        htailEdges, hclosing⟩
      have hMheight : M.height = 3 := hMheight0.trans hNheight
      have hSlen : 6 ≤ S.length := by omega
      have hback : ∀ f : E, psi f = some gamma → phi f = some gamma := by
        intro f hf
        by_cases hfj : f = NormalCycleEdge N j
        · subst f
          simp_all
        by_cases hs : ∃ i : Fin j.val,
            f = NormalCycleEdge N (Fin.castLE (Nat.le_of_lt j.isLt) i)
        · obtain ⟨i, hi⟩ := hs
          have hqpos : 1 ≤ i.val + 1 := by omega
          let q : Fin N.height := ⟨i.val + 1, by
            have hi' := i.isLt
            have hj' := j.isLt
            omega⟩
          have hc := hcycle_colors q hqpos
          have hpsi : psi f = phi (NormalCycleEdge N q) := by
            rw [hi]
            simpa [q] using hshift i
          rw [hpsi] at hf
          by_cases hodd : Odd q.val
          · rw [if_pos hodd] at hc
            exact False.elim (hgamma_alpha
              (Option.some.inj (hc.symm.trans hf)).symm)
          · rw [if_neg hodd] at hc
            exact False.elim (hgamma_beta
              (Option.some.inj (hc.symm.trans hf)).symm)
        · have hfix : psi f = phi f := hfixed f (by
            intro i
            by_cases hilast : i.val = j.val
            · intro heq
              apply hfj
              rw [heq]
              apply congrArg (NormalCycleEdge N)
              apply Fin.ext
              simpa [j] using hilast
            · intro heq
              apply hs
              let t : Fin j.val := ⟨i.val, by omega⟩
              refine ⟨t, ?_⟩
              rw [heq]
              apply congrArg (NormalCycleEdge N)
              apply Fin.ext
              rfl)
          exact hfix ▸ hf
      have hgammaOldPsi : gamma ∈ MissingColors G psi
          (T.vertex ⟨w.val, by omega⟩) := by
        have hnot : gamma ∉ PresentColors G psi
            (T.vertex ⟨w.val, by omega⟩) := by
          intro hp
          obtain ⟨f, hinc, hf⟩ := by simpa [PresentColors] using hp
          have hpold : gamma ∈ PresentColors G phi
              (T.vertex ⟨w.val, by omega⟩) := by
            simp [PresentColors]
            exact ⟨f, hinc, hback f hf⟩
          have hnold : gamma ∉ PresentColors G phi
              (T.vertex ⟨w.val, by omega⟩) := by
            simpa [MissingColors] using hwgamma'
          exact hnold hpold
        simpa [MissingColors] using hnot
      let s0 : Fin (S.length + 1) := ⟨0, by omega⟩
      let s1 : Fin (S.length + 1) := ⟨1, by omega⟩
      let s2 : Fin (S.length + 1) := ⟨2, by omega⟩
      let s3 : Fin (S.length + 1) := ⟨3, by omega⟩
      let s4 : Fin (S.length + 1) := ⟨4, by omega⟩
      let t2 : Fin S.length := ⟨2, by omega⟩
      let t3 : Fin S.length := ⟨3, by omega⟩
      obtain ⟨iw0, hiw0, hs0⟩ := htrunkVertices s0 (by simp [s0, hNheight])
      obtain ⟨iw1, hiw1, hs1⟩ := htrunkVertices s1 (by simp [s1, hNheight])
      obtain ⟨iw2, hiw2, hs2⟩ := htrunkVertices s2 (by simp [s2, hNheight])
      obtain ⟨ov3, hov3, hs3⟩ := htailVertices s3 (by simp [s3, hNheight])
      obtain ⟨ov4, hov4, hs4⟩ := htailVertices s4 (by simp [s4, hNheight])
      obtain ⟨oe2, hoe2, ht2⟩ := htailEdges t2 (by simp [t2, hNheight])
      obtain ⟨oe3, hoe3, ht3⟩ := htailEdges t3 (by simp [t3, hNheight])
      have hs0old : S.vertex s0 = T.vertex ⟨w.val, by omega⟩ := by
        rw [hs0]
        apply congrArg T.vertex
        apply Fin.ext
        have hjval : j.val = w.val := rfl
        have : iw0.val = w.val := by
          have hi := hiw0
          simp [s0, j, hNheight, Nat.mod_eq_of_lt hw_bound] at hi
          exact hi
        exact this
      have hov3eq : ov3 = v3 := by apply Fin.ext; simpa [s3, v3] using hov3
      have hov4eq : ov4 = v4 := by apply Fin.ext; simpa [s4, v4] using hov4
      have hoe2eq : oe2 = r2 := by apply Fin.ext; simpa [t2, r2] using hoe2
      have hoe3eq : oe3 = r3 := by apply Fin.ext; simpa [t3, r3] using hoe3
      have ht2old : S.edge t2 = T.edge r2 := by simpa [hoe2eq] using ht2
      have ht3old : S.edge t3 = T.edge r3 := by simpa [hoe3eq] using ht3
      have hs3old : S.vertex s3 = T.vertex v3 := by simpa [hov3eq] using hs3
      have hs4old : S.vertex s4 = T.vertex v4 := by simpa [hov4eq] using hs4
      have htailFixed (f : E) (hf : phi f = some gamma) : psi f = phi f := by
        apply hfixed
        intro i heq
        have hi0 : i.val = 0 ∨ 1 ≤ i.val := by omega
        rcases hi0 with hi0 | hipos
        · have hzero : NormalCycleEdge N
              (Fin.castLE (Nat.succ_le_iff.mpr j.isLt) i) = e0 := by
            simp [NormalCycleEdge, hi0]
          have hnone : phi (NormalCycleEdge N
              (Fin.castLE (Nat.succ_le_iff.mpr j.isLt) i)) = none := by
            rw [hzero]
            exact N.global.1.2.2.2.2.1
          rw [heq] at hf
          rw [hnone] at hf
          simp at hf
        · let q : Fin N.height :=
            Fin.castLE (Nat.succ_le_iff.mpr j.isLt) i
          have hc := hcycle_colors q (by simpa [q] using hipos)
          rw [heq] at hf
          change phi (NormalCycleEdge N q) = some gamma at hf
          by_cases hodd : Odd q.val
          · rw [if_pos hodd] at hc
            exact hgamma_alpha (Option.some.inj (hc.symm.trans hf)).symm
          · rw [if_neg hodd] at hc
            exact hgamma_beta (Option.some.inj (hc.symm.trans hf)).symm
      have ht2color : psi (S.edge t2) = some gamma := by
        rw [ht2old, htailFixed (T.edge r2) he2gamma]
        exact he2gamma
      have ht3color : psi (S.edge t3) = some gamma := by
        rw [ht3old, htailFixed (T.edge r3) he3gamma]
        exact he3gamma
      have hwcases : w.val = 1 ∨ w.val = 2 := by omega
      have hpairs : (a2'.val = iw1.val ∧ a3'.val = iw2.val) ∨
          (a2'.val = iw2.val ∧ a3'.val = iw1.val) := by
        rcases hwcases with hw1 | hw2
        · have hi1 : iw1.val = 2 := by
            have hi := hiw1
            simp [s1, j, hNheight, hw1] at hi
            exact hi
          have hi2 : iw2.val = 0 := by
            have hi := hiw2
            simp [s2, j, hNheight, hw1] at hi
            exact hi
          omega
        · have hi1 : iw1.val = 0 := by
            have hi := hiw1
            simp [s1, j, hNheight, hw2] at hi
            exact hi
          have hi2 : iw2.val = 1 := by
            have hi := hiw2
            simp [s2, j, hNheight, hw2] at hi
            exact hi
          omega
      have hout2 : Incident G (S.vertex s3) (S.edge t2) := by
        rw [hs3old, ht2old]
        exact he2inc_new
      have hout3 : Incident G (S.vertex s4) (S.edge t3) := by
        rw [hs4old, ht3old]
        exact he3inc_new
      have hattach :
          (Incident G (S.vertex s1) (S.edge t2) ∧
              Incident G (S.vertex s2) (S.edge t3)) ∨
            (Incident G (S.vertex s2) (S.edge t2) ∧
              Incident G (S.vertex s1) (S.edge t3)) := by
        rcases hpairs with h | h
        · left
          constructor
          · rw [ht2old, hs1]
            have hv : T.vertex (Fin.castLE N.height_upper iw1) = T.vertex a2' := by
              apply congrArg T.vertex
              apply Fin.ext
              simpa using h.1.symm
            rw [hv]
            exact he2inc_attach
          · rw [ht3old, hs2]
            have hv : T.vertex (Fin.castLE N.height_upper iw2) = T.vertex a3' := by
              apply congrArg T.vertex
              apply Fin.ext
              simpa using h.2.symm
            rw [hv]
            exact he3inc_attach
        · right
          constructor
          · rw [ht2old, hs2]
            have hv : T.vertex (Fin.castLE N.height_upper iw2) = T.vertex a2' := by
              apply congrArg T.vertex
              apply Fin.ext
              simpa using h.1.symm
            rw [hv]
            exact he2inc_attach
          · rw [ht3old, hs1]
            have hv : T.vertex (Fin.castLE N.height_upper iw1) = T.vertex a3' := by
              apply congrArg T.vertex
              apply Fin.ext
              simpa using h.2.symm
            rw [hv]
            exact he3inc_attach
      refine ⟨e1, psi, S, M, hSlen, hbalM, hMheight, ?_,
        ht2color, ht3color, hout2, hout3, hattach⟩
      rw [hs0old]
      exact hgammaOldPsi
  let s0 : Fin (S.length + 1) := ⟨0, by omega⟩
  let s1 : Fin (S.length + 1) := ⟨1, by omega⟩
  let s2 : Fin (S.length + 1) := ⟨2, by omega⟩
  let s3 : Fin (S.length + 1) := ⟨3, by omega⟩
  let s4 : Fin (S.length + 1) := ⟨4, by omega⟩
  let t2 : Fin S.length := ⟨2, by omega⟩
  let t3 : Fin S.length := ⟨3, by omega⟩
  have hgamma0' : gamma ∈ MissingColors G psi (S.vertex s0) := by
    simpa [s0] using hgamma0
  have hbeta1 : M.beta ∈ MissingColors G psi (S.vertex s1) := by
    simpa [s1] using M.beta_missing
  have helemS : ColoredVertexSetElementary G psi (TreeSequenceVertexSet S) :=
    (ScheideGlobalMaximumOrder G k e psi S M.global).2.2.2.1
  have hmemS (i : Fin (S.length + 1)) :
      S.vertex i ∈ TreeSequenceVertexSet S := by
    simp [TreeSequenceVertexSet]
  have hgamma_betaM : gamma ≠ M.beta := by
    intro heq
    have hne : S.vertex s0 ≠ S.vertex s1 := by
      intro hv
      have hi := S.vertex_injective hv
      have := congrArg Fin.val hi
      simp [s0, s1] at this
    have hd := helemS (hmemS s0) (hmemS s1) hne
    exact (Finset.disjoint_left.mp hd) hgamma0' (by simpa [heq] using hbeta1)
  have hcycleM := ScheideTrunkRotationCycle G k e psi S M hbalM
  have hcycleMends := hcycleM.2.2.2.1
  have hcycleMcolors := hcycleM.2.2.2.2
  let d2 : Fin M.height := ⟨2, by omega⟩
  let q : E := NormalCycleEdge M d2
  have hqcolor : psi q = some M.beta := by
    have hnotodd : ¬ Odd (2 : ℕ) := by
      rintro ⟨x, hx⟩
      omega
    simpa [q, d2, hnotodd] using hcycleMcolors d2 (by simp [d2])
  have hqends : G.ends q = s(S.vertex s2, S.vertex s0) := by
    simpa [q, d2, s2, s0, hMheight] using hcycleMends d2
  have hqinc0 : Incident G (S.vertex s0) q := by
    rw [Incident, hqends]
    simp
  have hqinc2 : Incident G (S.vertex s2) q := by
    rw [Incident, hqends]
    simp
  have htail2' : psi (S.edge t2) = some gamma := by simpa [t2] using htail2
  have htail3' : psi (S.edge t3) = some gamma := by simpa [t3] using htail3
  have hout2' : Incident G (S.vertex s3) (S.edge t2) := by
    simpa [s3, t2] using hout2
  have hout3' : Incident G (S.vertex s4) (S.edge t3) := by
    simpa [s4, t3] using hout3
  have hattach' :
      (Incident G (S.vertex s1) (S.edge t2) ∧
          Incident G (S.vertex s2) (S.edge t3)) ∨
        (Incident G (S.vertex s2) (S.edge t2) ∧
          Incident G (S.vertex s1) (S.edge t3)) := by
    simpa [s1, s2, t2, t3] using hattach
  obtain ⟨p, hp, hsupport, hdiv, hvertices, hbound⟩ :=
    ScheideKempePathHeightBound G k e psi S M.global gamma M.beta
      hgamma0' hbeta1
  let H := TwoColorIncidenceGraph G psi gamma M.beta
  let C := TwoColorComponent G psi gamma M.beta (Sum.inl (S.vertex s0))
  have hrootC : Sum.inl (S.vertex s0) ∈ C := by
    change H.connectedComponentMk (Sum.inl (S.vertex s0)) =
      H.connectedComponentMk (Sum.inl (S.vertex s0))
    rfl
  have hcomp_step {x y : Sum V E} (hx : x ∈ C) (hxy : H.Adj x y) : y ∈ C := by
    change H.connectedComponentMk x = H.connectedComponentMk (Sum.inl (S.vertex s0)) at hx
    change H.connectedComponentMk y = H.connectedComponentMk (Sum.inl (S.vertex s0))
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm.trans hx
  have hadj0q : H.Adj (Sum.inl (S.vertex s0)) (Sum.inr q) := by
    simpa [H, TwoColorIncidenceGraph] using
      (show Incident G (S.vertex s0) q ∧
          (psi q = some gamma ∨ psi q = some M.beta) from
        ⟨hqinc0, Or.inr hqcolor⟩)
  have hqC : Sum.inr q ∈ C := hcomp_step hrootC hadj0q
  have hadjq2 : H.Adj (Sum.inr q) (Sum.inl (S.vertex s2)) := by
    simpa [H, TwoColorIncidenceGraph] using
      (show Incident G (S.vertex s2) q ∧
          (psi q = some gamma ∨ psi q = some M.beta) from
        ⟨hqinc2, Or.inr hqcolor⟩)
  have hs2C : Sum.inl (S.vertex s2) ∈ C := hcomp_step hqC hadjq2
  have hs1C : Sum.inl (S.vertex s1) ∈ C := by
    have hsupp : Sum.inl (S.vertex s1) ∈ p.support := by
      have hm := p.getVert_mem_support p.length
      rw [p.getVert_length] at hm
      simpa [s1] using hm
    have hc : Sum.inl (S.vertex s1) ∈
        TwoColorComponent G psi gamma M.beta
          (Sum.inl (S.vertex ⟨0, by omega⟩)) := by
      rw [← hsupport]
      exact hsupp
    simpa [C, s0] using hc
  have hedge2_from (i : Fin (S.length + 1))
      (hi : Sum.inl (S.vertex i) ∈ C)
      (hinc : Incident G (S.vertex i) (S.edge t2)) :
      Sum.inr (S.edge t2) ∈ C := by
    apply hcomp_step hi
    simpa [H, TwoColorIncidenceGraph] using
      (show Incident G (S.vertex i) (S.edge t2) ∧
          (psi (S.edge t2) = some gamma ∨ psi (S.edge t2) = some M.beta) from
        ⟨hinc, Or.inl htail2'⟩)
  have hedge3_from (i : Fin (S.length + 1))
      (hi : Sum.inl (S.vertex i) ∈ C)
      (hinc : Incident G (S.vertex i) (S.edge t3)) :
      Sum.inr (S.edge t3) ∈ C := by
    apply hcomp_step hi
    simpa [H, TwoColorIncidenceGraph] using
      (show Incident G (S.vertex i) (S.edge t3) ∧
          (psi (S.edge t3) = some gamma ∨ psi (S.edge t3) = some M.beta) from
        ⟨hinc, Or.inl htail3'⟩)
  have he2C : Sum.inr (S.edge t2) ∈ C := by
    rcases hattach' with h | h
    · exact hedge2_from s1 hs1C h.1
    · exact hedge2_from s2 hs2C h.1
  have he3C : Sum.inr (S.edge t3) ∈ C := by
    rcases hattach' with h | h
    · exact hedge3_from s2 hs2C h.2
    · exact hedge3_from s1 hs1C h.2
  have hadje23 : H.Adj (Sum.inr (S.edge t2)) (Sum.inl (S.vertex s3)) := by
    simpa [H, TwoColorIncidenceGraph] using
      (show Incident G (S.vertex s3) (S.edge t2) ∧
          (psi (S.edge t2) = some gamma ∨ psi (S.edge t2) = some M.beta) from
        ⟨hout2', Or.inl htail2'⟩)
  have hadje34 : H.Adj (Sum.inr (S.edge t3)) (Sum.inl (S.vertex s4)) := by
    simpa [H, TwoColorIncidenceGraph] using
      (show Incident G (S.vertex s4) (S.edge t3) ∧
          (psi (S.edge t3) = some gamma ∨ psi (S.edge t3) = some M.beta) from
        ⟨hout3', Or.inl htail3'⟩)
  have hs3C : Sum.inl (S.vertex s3) ∈ C := hcomp_step he2C hadje23
  have hs4C : Sum.inl (S.vertex s4) ∈ C := hcomp_step he3C hadje34
  have hC_support {z : Sum V E} (hz : z ∈ C) : z ∈ p.support := by
    have hc : z ∈ TwoColorComponent G psi gamma M.beta
        (Sum.inl (S.vertex ⟨0, by omega⟩)) := by
      simpa [C, s0] using hz
    exact (Set.ext_iff.mp hsupport z).mpr hc
  have hs0support : Sum.inl (S.vertex s0) ∈ p.support := hC_support hrootC
  have hs1support : Sum.inl (S.vertex s1) ∈ p.support := hC_support hs1C
  have hs2support : Sum.inl (S.vertex s2) ∈ p.support := hC_support hs2C
  have hs3support : Sum.inl (S.vertex s3) ∈ p.support := hC_support hs3C
  have hs4support : Sum.inl (S.vertex s4) ∈ p.support := hC_support hs4C
  have hqsupport : Sum.inr q ∈ p.support := hC_support hqC
  have he2support : Sum.inr (S.edge t2) ∈ p.support := hC_support he2C
  have he3support : Sum.inr (S.edge t3) ∈ p.support := hC_support he3C
  have hq_ne_e2 : q ≠ S.edge t2 := by
    intro heq
    rw [heq, htail2'] at hqcolor
    exact hgamma_betaM (Option.some.inj hqcolor)
  have hq_ne_e3 : q ≠ S.edge t3 := by
    intro heq
    rw [heq, htail3'] at hqcolor
    exact hgamma_betaM (Option.some.inj hqcolor)
  have he23 : S.edge t2 ≠ S.edge t3 := by
    intro heq
    have hi := S.edge_injective heq
    have := congrArg Fin.val hi
    simp [t2, t3] at this
  let Z : Finset (Sum V E) :=
    {Sum.inl (S.vertex s0), Sum.inl (S.vertex s1),
      Sum.inl (S.vertex s2), Sum.inl (S.vertex s3),
      Sum.inl (S.vertex s4), Sum.inr q,
      Sum.inr (S.edge t2), Sum.inr (S.edge t3)}
  have hZcard : Z.card = 8 := by
    simp [Z, S.vertex_injective.eq_iff, hq_ne_e2, hq_ne_e3, he23,
      s0, s1, s2, s3, s4, t2, t3]
  have hZsub : Z ⊆ p.support.toFinset := by
    intro z hz
    simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [List.mem_toFinset]
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hs0support
    · exact hs1support
    · exact hs2support
    · exact hs3support
    · exact hs4support
    · exact hqsupport
    · exact he2support
    · exact he3support
  have hseven : 7 ≤ p.length := by
    have hc := Finset.card_le_card hZsub
    rw [hZcard, List.toFinset_card_of_nodup hp.support_nodup,
      p.length_support] at hc
    omega
  have height : 8 ≤ p.length := by
    rcases hdiv with ⟨d, hd⟩
    omega
  have hfive : 5 ≤ p.length / 2 + 1 := by omega
  omega
