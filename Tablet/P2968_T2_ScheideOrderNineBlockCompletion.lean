import Mathlib.Tactic.FinCases
import Tablet.BalancedGlobalMaximumTriple
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.NormalGlobalMaximumTriple
import Tablet.PresentColors
import Tablet.ScheideGraphHeight
import Tablet.ScheideHeightFiveGammaEdges
import Tablet.ScheideHeightFiveOutsideLinks
import Tablet.ScheideKempePathHeightBound
import Tablet.ScheideTrunkRotationColoring
import Tablet.ScheideTrunkRotationCycle
import Tablet.ScheideTrunkRotationNormal
import Tablet.ScheideTrunkRotationTree
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph

open scoped Sym2

set_option maxHeartbeats 800000

-- [TABLET NODE: P2968_T2_ScheideOrderNineBlockCompletion]
theorem P2968_T2_ScheideOrderNineBlockCompletion {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) {eX : E}
    (psi : PartialEdgeColoring E k) (X : TreeSequence G eX)
    (Q : NormalGlobalMaximumTriple G k eX psi X)
    (hbalX : BalancedGlobalMaximumTriple Q)
    (hgraphHeight : ScheideGraphHeight G = 5)
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
    ∃ (_ : BalancedGlobalMaximumTriple Q) (_ : X.length = 8)
      (_ : Q.height = 5) (gamma : Fin 2 → Fin k),
      Function.Injective gamma ∧
      (∀ (i : Fin 2) (j : Fin 2),
        ∃ q : Fin 5,
          G.ends (X.edge ⟨4 + 2 * i.val + j.val, by omega⟩) =
            s(X.vertex ⟨q.val, by omega⟩,
              X.vertex ⟨5 + 2 * i.val + j.val, by omega⟩)) ∧
      (∀ (i : Fin 2) (j : Fin 2),
        psi (X.edge ⟨4 + 2 * i.val + j.val, by omega⟩) =
          some (gamma i)) ∧
      (∀ i : Fin 2, ∃ q : Fin 5,
        gamma i ∈ MissingColors G psi (X.vertex ⟨q.val, by omega⟩)) ∧
      (∀ i : Fin 4, 1 ≤ i.val →
        ∀ c : Fin k, psi (X.edge ⟨i.val, by omega⟩) = some c →
          ∀ r : Fin 2, c ≠ gamma r) := by
-- BODY
  classical
  letI : DecidableEq V := Classical.decEq V
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
        have hnot : Q.beta ∉ PresentColors G psi (Y 1) := by
          simpa [MissingColors, Y] using Q.beta_missing
        apply hnot
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨X.edge ⟨1, by omega⟩, hinc, by simpa [h] using he1color⟩
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
