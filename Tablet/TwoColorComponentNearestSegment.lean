import Tablet.Incident
import Tablet.IsProperEdgeColoring
import Tablet.LooplessMultigraph
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorIncidenceGraph

open scoped Sym2

-- [TABLET NODE: TwoColorComponentNearestSegment]
theorem TwoColorComponentNearestSegment
    {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) {k : Nat} {e0 : E}
    (phi : PartialEdgeColoring E k) (S : TreeSequence G e0)
    (alpha beta : Fin k) (y : V)
    (hproper : IsProperEdgeColoring G phi)
    (hne : alpha ≠ beta)
    (hy : y ∉ TreeSequenceVertexSet S)
    (hmeets : ∃ u ∈ TreeSequenceVertexSet S,
      Sum.inl u ∈ TwoColorComponent G phi alpha beta (Sum.inl y)) :
    ∃ (m : Nat) (_ : 1 ≤ m)
      (pathVertex : Fin (m + 1) → V) (pathEdge : Fin m → E),
      Function.Injective pathVertex ∧
        Function.Injective pathEdge ∧
        pathVertex 0 ∈ TreeSequenceVertexSet S ∧
        pathVertex (Fin.last m) = y ∧
        (∀ i : Fin m,
          pathVertex i.succ ∉ TreeSequenceVertexSet S) ∧
        (∀ i : Fin (m + 1),
          Sum.inl (pathVertex i) ∈
            TwoColorComponent G phi alpha beta (Sum.inl y)) ∧
        (∀ i : Fin m,
          Sum.inr (pathEdge i) ∈
            TwoColorComponent G phi alpha beta (Sum.inl y)) ∧
        (∀ i : Fin m,
          phi (pathEdge i) = some alpha ∨
            phi (pathEdge i) = some beta) ∧
        (∀ i : Fin m,
          G.ends (pathEdge i) =
            s(pathVertex i.castSucc, pathVertex i.succ)) ∧
        ∀ i : Fin m, ∀ j : Fin S.length,
          pathEdge i ≠ S.edge j := by
-- BODY
  classical
  let H := TwoColorIncidenceGraph G phi alpha beta
  let C := TwoColorComponent G phi alpha beta (Sum.inl y)
  obtain ⟨a, b, p, hp, hsupp⟩ :=
    TwoColorComponentSpanningPath G phi alpha beta hproper (Sum.inl y)
  obtain ⟨u, huS, huC⟩ := hmeets
  have huP : Sum.inl u ∈ p.support := by
    change Sum.inl u ∈ {x | x ∈ p.support}
    rw [hsupp]
    exact huC
  have hyC : Sum.inl y ∈ C := by
    change H.connectedComponentMk (Sum.inl y) = H.connectedComponentMk (Sum.inl y)
    rfl
  have hyP : Sum.inl y ∈ p.support := by
    change Sum.inl y ∈ {x | x ∈ p.support}
    rw [hsupp]
    exact hyC
  obtain ⟨iu, hpu, hiu⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp huP
  obtain ⟨iy, hpy, hiy⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hyP
  have oriented : ∀ {a' b' : Sum V E}
      (q : H.Walk a' b') (hq : q.IsPath)
      (hqsupp : {x | x ∈ q.support} = C)
      (iu iy : Nat) (hiu : iu ≤ q.length) (hiy : iy ≤ q.length)
      (hiule : iu ≤ iy)
      (hqu : q.getVert iu = Sum.inl u)
      (hqy : q.getVert iy = Sum.inl y),
      ∃ (m : Nat) (_ : 1 ≤ m)
        (pathVertex : Fin (m + 1) → V) (pathEdge : Fin m → E),
        Function.Injective pathVertex ∧
          Function.Injective pathEdge ∧
          pathVertex 0 ∈ TreeSequenceVertexSet S ∧
          pathVertex (Fin.last m) = y ∧
          (∀ i : Fin m,
            pathVertex i.succ ∉ TreeSequenceVertexSet S) ∧
          (∀ i : Fin (m + 1),
            Sum.inl (pathVertex i) ∈ C) ∧
          (∀ i : Fin m, Sum.inr (pathEdge i) ∈ C) ∧
          (∀ i : Fin m,
            phi (pathEdge i) = some alpha ∨
              phi (pathEdge i) = some beta) ∧
          (∀ i : Fin m,
            G.ends (pathEdge i) =
              s(pathVertex i.castSucc, pathVertex i.succ)) ∧
          ∀ i : Fin m, ∀ j : Fin S.length,
            pathEdge i ≠ S.edge j := by
    intro a' b' q hq hqsupp iu iy hiu hiy hiule hqu hqy
    let P : Nat → Prop := fun d =>
      d ≤ iy ∧ ∃ v : V,
        q.getVert (iy - d) = Sum.inl v ∧ v ∈ TreeSequenceVertexSet S
    have hex : ∃ d, P d := by
      refine ⟨iy - iu, by omega, u, ?_, huS⟩
      have hidx : iy - (iy - iu) = iu := by omega
      rw [hidx]
      exact hqu
    let d := Nat.find hex
    have hdP : P d := Nat.find_spec hex
    obtain ⟨hdle, v0, hv0, hv0S⟩ := hdP
    have hdpos : 0 < d := by
      by_contra hn
      have hd0 : d = 0 := by omega
      have hv0y : v0 = y := by
        have hv0' := hv0
        rw [hd0] at hv0'
        have heq : (Sum.inl v0 : Sum V E) = Sum.inl y := by
          simpa using hv0'.symm.trans hqy
        exact Sum.inl.inj heq
      apply hy
      rw [← hv0y]
      exact hv0S
    let start := iy - d
    let r := (q.drop start).take d
    have hrlen : r.length = d := by
      simp only [r, SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length]
      rw [Nat.min_eq_left]
      omega
    have hrget : ∀ n ≤ d, r.getVert n = q.getVert (start + n) := by
      intro n hn
      simp only [r, SimpleGraph.Walk.take_getVert, SimpleGraph.Walk.drop_getVert]
      rw [Nat.min_eq_right hn]
    have hrstart : r.getVert 0 = Sum.inl v0 := by
      rw [hrget 0 (by omega)]
      simpa [start] using hv0
    have hrend : r.getVert d = Sum.inl y := by
      rw [hrget d (by omega)]
      have hidx : start + d = iy := by simp [start]; omega
      rw [hidx]
      exact hqy
    have hrpath : r.IsPath := (hq.drop start).take d
    have hrout : ∀ n, 0 < n → n ≤ d → ∀ v : V,
        r.getVert n = Sum.inl v → v ∉ TreeSequenceVertexSet S := by
      intro n hnpos hnle v hrv hvS
      have hsmall : d - n < d := by omega
      have hnotP := Nat.find_min hex hsmall
      apply hnotP
      refine ⟨by omega, v, ?_, hvS⟩
      have hidx : iy - (d - n) = start + n := by simp [start]; omega
      rw [hidx, ← hrget n hnle]
      exact hrv
    have hshape : ∀ n ≤ d,
        (n % 2 = 0 → ∃ v : V, r.getVert n = Sum.inl v) ∧
        (n % 2 = 1 → ∃ e : E, r.getVert n = Sum.inr e) := by
      intro n
      induction n with
      | zero =>
          intro hn
          constructor
          · intro _
            exact ⟨v0, hrstart⟩
          · omega
      | succ n ih =>
          intro hn
          have hnlt : n < r.length := by rw [hrlen]; omega
          have hadj := r.adj_getVert_succ hnlt
          have hprev := ih (by omega)
          constructor
          · intro heven
            obtain ⟨e, he⟩ := hprev.2 (by omega)
            cases hnext : r.getVert (n + 1) with
            | inl v => exact ⟨v, rfl⟩
            | inr e' =>
                rw [he, hnext] at hadj
                simp [H, TwoColorIncidenceGraph] at hadj
          · intro hodd
            obtain ⟨v, hv⟩ := hprev.1 (by omega)
            cases hnext : r.getVert (n + 1) with
            | inl v' =>
                rw [hv, hnext] at hadj
                simp [H, TwoColorIncidenceGraph] at hadj
            | inr e => exact ⟨e, rfl⟩
    have hdeven : d % 2 = 0 := by
      by_contra hnot
      have hodd : d % 2 = 1 := by omega
      obtain ⟨e, he⟩ := (hshape d (by omega)).2 hodd
      rw [hrend] at he
      cases he
    obtain ⟨m, hdm⟩ : ∃ m : Nat, d = 2 * m :=
      even_iff_exists_two_mul.mp (Nat.even_iff.mpr hdeven)
    have hm : 1 ≤ m := by omega
    have hvAt : ∀ i : Fin (m + 1), ∃ v : V,
        r.getVert (2 * i.val) = Sum.inl v := by
      intro i
      apply (hshape (2 * i.val) (by omega)).1
      omega
    have heAt : ∀ i : Fin m, ∃ e : E,
        r.getVert (2 * i.val + 1) = Sum.inr e := by
      intro i
      apply (hshape (2 * i.val + 1) (by omega)).2
      omega
    let pathVertex : Fin (m + 1) → V := fun i => (hvAt i).choose
    let pathEdge : Fin m → E := fun i => (heAt i).choose
    have hvSpec (i : Fin (m + 1)) :
        r.getVert (2 * i.val) = Sum.inl (pathVertex i) :=
      (hvAt i).choose_spec
    have heSpec (i : Fin m) :
        r.getVert (2 * i.val + 1) = Sum.inr (pathEdge i) :=
      (heAt i).choose_spec
    have hvertexInjective : Function.Injective pathVertex := by
      intro i j hij
      have hget : r.getVert (2 * i.val) = r.getVert (2 * j.val) := by
        rw [hvSpec i, hvSpec j, hij]
      have hibound : 2 * i.val ≤ r.length := by
        rw [hrlen, hdm]
        exact Nat.mul_le_mul_left 2 (Nat.lt_succ_iff.mp i.isLt)
      have hjbound : 2 * j.val ≤ r.length := by
        rw [hrlen, hdm]
        exact Nat.mul_le_mul_left 2 (Nat.lt_succ_iff.mp j.isLt)
      have hidx := hrpath.getVert_injOn hibound hjbound hget
      apply Fin.ext
      omega
    have hedgeInjective : Function.Injective pathEdge := by
      intro i j hij
      have hget : r.getVert (2 * i.val + 1) = r.getVert (2 * j.val + 1) := by
        rw [heSpec i, heSpec j, hij]
      have hibound : 2 * i.val + 1 ≤ r.length := by
        rw [hrlen, hdm]
        omega
      have hjbound : 2 * j.val + 1 ≤ r.length := by
        rw [hrlen, hdm]
        omega
      have hidx := hrpath.getVert_injOn hibound hjbound hget
      apply Fin.ext
      omega
    have hstart : pathVertex 0 ∈ TreeSequenceVertexSet S := by
      have hs : pathVertex 0 = v0 := by
        apply Sum.inl.inj
        rw [← hvSpec 0]
        simpa using hrstart
      rw [hs]
      exact hv0S
    have hlast : pathVertex (Fin.last m) = y := by
      apply Sum.inl.inj
      rw [← hvSpec (Fin.last m)]
      simpa [hdm] using hrend
    have houtside : ∀ i : Fin m,
        pathVertex i.succ ∉ TreeSequenceVertexSet S := by
      intro i
      have hibound : 2 * i.succ.val ≤ d := by
        rw [hdm]
        exact Nat.mul_le_mul_left 2 (Nat.lt_succ_iff.mp i.succ.isLt)
      apply hrout (2 * i.succ.val) (by simp only [Fin.val_succ]; omega) hibound
        (pathVertex i.succ)
      exact hvSpec i.succ
    have hrComponent : ∀ n ≤ d, r.getVert n ∈ C := by
      intro n hn
      rw [← hqsupp]
      rw [hrget n hn]
      exact q.getVert_mem_support _
    have hvertexComponent : ∀ i : Fin (m + 1),
        Sum.inl (pathVertex i) ∈ C := by
      intro i
      rw [← hvSpec i]
      exact hrComponent _ (by rw [hdm]; omega)
    have hedgeComponent : ∀ i : Fin m, Sum.inr (pathEdge i) ∈ C := by
      intro i
      rw [← heSpec i]
      exact hrComponent _ (by rw [hdm]; omega)
    have hstep : ∀ i : Fin m,
        Incident G (pathVertex i.castSucc) (pathEdge i) ∧
          Incident G (pathVertex i.succ) (pathEdge i) ∧
          (phi (pathEdge i) = some alpha ∨
            phi (pathEdge i) = some beta) := by
      intro i
      have hleft := r.adj_getVert_succ
        (i := 2 * i.val) (by rw [hrlen, hdm]; omega)
      have hright := r.adj_getVert_succ
        (i := 2 * i.val + 1) (by rw [hrlen, hdm]; omega)
      have hleft' : H.Adj (Sum.inl (pathVertex i.castSucc))
          (Sum.inr (pathEdge i)) := by
        rw [← hvSpec i.castSucc, ← heSpec i]
        simpa using hleft
      have hnext : 2 * i.val + 1 + 1 = 2 * i.succ.val := by simp; omega
      have hright' : H.Adj (Sum.inr (pathEdge i))
          (Sum.inl (pathVertex i.succ)) := by
        rw [← heSpec i, ← hvSpec i.succ]
        simpa [hnext]
      simp only [H, TwoColorIncidenceGraph] at hleft' hright'
      exact ⟨hleft'.1, hright'.1, hleft'.2⟩
    have hends : ∀ i : Fin m,
        G.ends (pathEdge i) =
          s(pathVertex i.castSucc, pathVertex i.succ) := by
      intro i
      have hneVertices : pathVertex i.castSucc ≠ pathVertex i.succ := by
        intro heq
        have := hvertexInjective heq
        have hv := congrArg Fin.val this
        simp at hv
      have ends_eq_of_mem : ∀ {z : Sym2 V} {x y : V},
          x ∈ z → y ∈ z → x ≠ y → z = s(x, y) := by
        intro z x y hx hy hxy
        induction z using Sym2.inductionOn with
        | _ a b =>
          simp only [Sym2.mem_iff] at hx hy
          rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
            simp_all [Sym2.eq_iff]
      exact ends_eq_of_mem (hstep i).1 (hstep i).2.1 hneVertices
    have hedgeFresh : ∀ i : Fin m, ∀ j : Fin S.length,
        pathEdge i ≠ S.edge j := by
      intro i j heq
      rcases S.attaches j with ⟨t, ht⟩
      have hinc : pathVertex i.succ ∈ G.ends (S.edge j) := by
        rw [← heq, hends i]
        simp [Sym2.mem_iff]
      rw [ht] at hinc
      simp only [Sym2.mem_iff] at hinc
      apply houtside i
      rcases hinc with hnew | hold
      · rw [hnew]
        simp [TreeSequenceVertexSet]
      · rw [hold]
        simp [TreeSequenceVertexSet]
    exact ⟨m, hm, pathVertex, pathEdge, hvertexInjective,
      hedgeInjective, hstart, hlast, houtside, hvertexComponent,
      hedgeComponent, fun i => (hstep i).2.2, hends, hedgeFresh⟩
  by_cases horder : iu ≤ iy
  · exact oriented p hp hsupp iu iy hiu hiy horder hpu hpy
  · have hrevSupp : {x | x ∈ p.reverse.support} = C := by
      ext x
      simp only [Set.mem_setOf_eq, SimpleGraph.Walk.support_reverse, List.mem_reverse]
      exact Set.ext_iff.mp hsupp x
    apply oriented p.reverse hp.reverse hrevSupp (p.length - iu) (p.length - iy)
    · simp
    · simp
    · omega
    · rw [SimpleGraph.Walk.getVert_reverse]
      have hidx : p.length - (p.length - iu) = iu := by omega
      rw [hidx]
      exact hpu
    · rw [SimpleGraph.Walk.getVert_reverse]
      have hidx : p.length - (p.length - iy) = iy := by omega
      rw [hidx]
      exact hpy
