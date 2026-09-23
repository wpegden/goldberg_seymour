import Tablet.BalancedGlobalMaximumTriple
import Tablet.GlobalMaximumTriple
import Tablet.MissingColors
import Tablet.NormalCycleEdge
import Tablet.NormalGlobalMaximumTriple
import Tablet.ScheideTrunkRotationCycle
import Tablet.ScheideTrunkRotationTree
import Tablet.TreeSequenceVertexSet
import Tablet.TreeSequence
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideTrunkRotationNormal]
theorem ScheideTrunkRotationNormal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi psi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hbalanced : BalancedGlobalMaximumTriple N)
    (j : Fin N.height) (hj : 1 ≤ j.val) (A B : Fin k)
    (hAB : A ≠ B)
    (hA : A = (if Odd j.val then N.beta else N.alpha))
    (hB : B = (if Odd j.val then N.alpha else N.beta))
    (hshift : ∀ i : Fin j.val,
      psi (NormalCycleEdge N
          (Fin.castLE (Nat.le_of_lt j.isLt) i)) =
        phi (NormalCycleEdge N
          ⟨i.val + 1, by
            have hi := i.isLt
            have hjlt := j.isLt
            omega⟩))
    (hfixed : ∀ f : E,
      (∀ i : Fin (j.val + 1),
        f ≠ NormalCycleEdge N
          (Fin.castLE (Nat.succ_le_iff.mpr j.isLt) i)) →
      psi f = phi f)
    (T' : TreeSequence G (NormalCycleEdge N j))
    (hglobal : GlobalMaximumTriple G k (NormalCycleEdge N j) psi T')
    (hmissA : A ∈ MissingColors G psi
      (T.vertex (Fin.castLE N.height_upper j)))
    (hmissB : B ∈ MissingColors G psi
      (T.vertex (Fin.castLE N.height_upper
        ⟨(j.val + 1) % N.height, by
          exact Nat.mod_lt _ (by
            have hp := N.height_lower
            omega)⟩)))
    (hlength : T'.length = T.length)
    (hvertex : ∀ r : Fin (T'.length + 1), r.val < N.height →
      ∃ i : Fin N.height,
        i.val = (j.val + r.val) % N.height ∧
          T'.vertex r = T.vertex (Fin.castLE N.height_upper i))
    (hedge : ∀ r : Fin T'.length, r.val + 1 < N.height →
      ∃ i : Fin N.height,
        i.val = (j.val + r.val) % N.height ∧
          T'.edge r = NormalCycleEdge N i) :
    ∃ N' : NormalGlobalMaximumTriple G k (NormalCycleEdge N j) psi T',
      N'.height = N.height ∧
      N'.alpha = A ∧ N'.beta = B ∧
      ∃ pred : Fin N.height,
        pred.val = (j.val + N.height - 1) % N.height ∧
          N'.closingEdge = NormalCycleEdge N pred := by
-- BODY
  classical
  obtain ⟨hp3, _hpodd, hcycle_injective, hcycle_ends, hcycle_colors⟩ :=
    ScheideTrunkRotationCycle G k e0 phi T N hbalanced
  have hnew_upper : N.height ≤ T'.length + 1 := by
    rw [hlength]
    exact N.height_upper
  let rho : Fin N.height → Fin N.height := fun r => j + r
  have hrho_val (r : Fin N.height) :
      (rho r).val = (j.val + r.val) % N.height := by
    rfl
  have hrho_injective : Function.Injective rho := by
    intro a b hab
    have hmod (r : Fin N.height) :
        (j.val + r.val) % N.height =
          if j.val + r.val < N.height then
            j.val + r.val
          else
            j.val + r.val - N.height := by
      by_cases hr : j.val + r.val < N.height
      · simp [hr, Nat.mod_eq_of_lt hr]
      · rw [if_neg hr, Nat.mod_eq_sub_mod (by omega)]
        rw [Nat.mod_eq_of_lt]
        omega
    have hv := congrArg Fin.val hab
    change (j.val + a.val) % N.height =
      (j.val + b.val) % N.height at hv
    rw [hmod a, hmod b] at hv
    by_cases ha : j.val + a.val < N.height <;>
      by_cases hb : j.val + b.val < N.height <;>
      simp [ha, hb] at hv <;>
      apply Fin.ext <;> omega
  have hrho_zero : rho ⟨0, by omega⟩ = j := by
    apply Fin.ext
    change (j.val + 0) % N.height = j.val
    simpa using Nat.mod_eq_of_lt j.isLt
  have hrho_succ (r : Fin N.height) :
      rho ⟨(r.val + 1) % N.height, Nat.mod_lt _ (by omega)⟩ =
        ⟨((rho r).val + 1) % N.height, Nat.mod_lt _ (by omega)⟩ := by
    apply Fin.ext
    change (j.val + ((r.val + 1) % N.height)) % N.height =
      (((j.val + r.val) % N.height) + 1) % N.height
    calc
      (j.val + ((r.val + 1) % N.height)) % N.height =
          ((j.val % N.height) + (((r.val + 1) % N.height) % N.height)) %
            N.height := Nat.add_mod _ _ _
      _ = ((j.val % N.height) + ((r.val + 1) % N.height)) %
          N.height := by
        rw [Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))]
      _ = (j.val + (r.val + 1)) % N.height :=
        (Nat.add_mod _ _ _).symm
      _ = ((j.val + r.val) + 1) % N.height := by congr 1 <;> omega
      _ = (((j.val + r.val) % N.height) + (1 % N.height)) %
          N.height := Nat.add_mod (j.val + r.val) 1 N.height
      _ = (((j.val + r.val) % N.height) + 1) % N.height := by
        rw [Nat.mod_eq_of_lt (by omega : 1 < N.height)]
  have hrot_vertex (r : Fin N.height) :
      T'.vertex (Fin.castLE hnew_upper r) =
        T.vertex (Fin.castLE N.height_upper (rho r)) := by
    obtain ⟨i, hi, hv⟩ := hvertex (Fin.castLE hnew_upper r) (by
      simpa using r.isLt)
    rw [hv]
    apply congrArg T.vertex
    apply congrArg (Fin.castLE N.height_upper)
    apply Fin.ext
    change i.val = (j.val + r.val) % N.height
    simpa using hi
  have hrot_ends (r : Fin N.height) :
      G.ends (NormalCycleEdge N (rho r)) =
        s(T'.vertex (Fin.castLE hnew_upper r),
          T'.vertex (Fin.castLE hnew_upper
            ⟨(r.val + 1) % N.height, Nat.mod_lt _ (by omega)⟩)) := by
    rw [hcycle_ends, hrot_vertex, hrot_vertex, hrho_succ]
  have hpair_colors (q : Fin N.height) (hq : 1 ≤ q.val) :
      phi (NormalCycleEdge N q) = some A ∨
        phi (NormalCycleEdge N q) = some B := by
    have hc := hcycle_colors q hq
    by_cases ho : Odd j.val
    · have hAe : A = N.beta := by simpa [ho] using hA
      have hBe : B = N.alpha := by simpa [ho] using hB
      by_cases hqo : Odd q.val
      · right
        rw [hBe]
        simpa [hqo] using hc
      · left
        rw [hAe]
        simpa [hqo] using hc
    · have hAe : A = N.alpha := by simpa [ho] using hA
      have hBe : B = N.beta := by simpa [ho] using hB
      by_cases hqo : Odd q.val
      · left
        rw [hAe]
        simpa [hqo] using hc
      · right
        rw [hBe]
        simpa [hqo] using hc
  have hrot_color (r : Fin N.height) (hr : 1 ≤ r.val) :
      psi (NormalCycleEdge N (rho r)) = some A ∨
        psi (NormalCycleEdge N (rho r)) = some B := by
    have hne : rho r ≠ j := by
      intro heq
      have hz := hrho_injective (heq.trans hrho_zero.symm)
      have hv := congrArg Fin.val hz
      simp at hv
      omega
    by_cases hq : (rho r).val < j.val
    · let a : Fin j.val := ⟨(rho r).val, hq⟩
      have hs := hshift a
      have hc := hpair_colors
        ⟨a.val + 1, by
          have hjlt := j.isLt
          simp [a] at *
          omega⟩ (by simp [a])
      have ha : Fin.castLE (Nat.le_of_lt j.isLt) a = rho r := by
        apply Fin.ext
        rfl
      rw [ha] at hs
      rw [hs]
      simpa [a] using hc
    · have hgt : j.val < (rho r).val := by
        have hn : (rho r).val ≠ j.val := by
          intro hn
          apply hne
          apply Fin.ext
          exact hn
        omega
      have hf : psi (NormalCycleEdge N (rho r)) =
          phi (NormalCycleEdge N (rho r)) := by
        apply hfixed
        intro a heq
        have hi := hcycle_injective heq
        have hv := congrArg Fin.val hi
        simp at hv
        omega
      rw [hf]
      exact hpair_colors (rho r) (by omega)
  have htrunk_edge_eq (r : Fin T'.length)
      (hr : r.val + 1 < N.height) :
      T'.edge r = NormalCycleEdge N
        (rho ⟨r.val, by omega⟩) := by
    obtain ⟨i, hi, he⟩ := hedge r hr
    rw [he]
    apply congrArg (NormalCycleEdge N)
    apply Fin.ext
    change i.val = (j.val + r.val) % N.height
    exact hi
  let last : Fin N.height := ⟨N.height - 1, by omega⟩
  let pred : Fin N.height := rho last
  have hpred_val : pred.val =
      (j.val + N.height - 1) % N.height := by
    change (j.val + (N.height - 1)) % N.height = _
    congr 1
    omega
  have hpred_before : pred.val = j.val - 1 := by
    rw [hpred_val]
    have heq : j.val + N.height - 1 = (j.val - 1) + N.height := by
      omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt]
    omega
  let H := TwoColorIncidenceGraph G psi A B
  let pathNode : Fin (2 * (N.height - 1) + 1) → Sum V E := fun n =>
    if he : n.val % 2 = 0 then
      Sum.inl (T'.vertex (Fin.castLE hnew_upper
        ⟨(n.val / 2 + 1) % N.height, Nat.mod_lt _ (by omega)⟩))
    else
      Sum.inr (NormalCycleEdge N
        (rho ⟨(n.val + 1) / 2, by omega⟩))
  have hnode_even (n : Fin (2 * (N.height - 1) + 1))
      (hn : n.val % 2 = 0) :
      pathNode n = Sum.inl (T'.vertex (Fin.castLE hnew_upper
        ⟨(n.val / 2 + 1) % N.height, Nat.mod_lt _ (by omega)⟩)) := by
    simp [pathNode, hn]
  have hnode_odd (n : Fin (2 * (N.height - 1) + 1))
      (hn : n.val % 2 ≠ 0) :
      pathNode n = Sum.inr (NormalCycleEdge N
        (rho ⟨(n.val + 1) / 2, by omega⟩)) := by
    simp [pathNode, hn]
  let nodes : List (Sum V E) := List.ofFn pathNode
  have hchain : nodes.IsChain H.Adj := by
    rw [List.isChain_iff_getElem]
    intro i hi
    rw [List.length_ofFn] at hi
    rw [List.getElem_ofFn, List.getElem_ofFn]
    by_cases he : i % 2 = 0
    · have ho : (i + 1) % 2 ≠ 0 := by omega
      rw [hnode_even _ he, hnode_odd _ ho]
      let r : Fin N.height := ⟨i / 2 + 1, by omega⟩
      have hidx : (i / 2 + 1) % N.height = r.val :=
        Nat.mod_eq_of_lt r.isLt
      have hedgeidx : (i + 1 + 1) / 2 = r.val := by
        dsimp [r]
        omega
      change H.Adj
        (Sum.inl (T'.vertex (Fin.castLE hnew_upper
          ⟨(i / 2 + 1) % N.height, _⟩)))
        (Sum.inr (NormalCycleEdge N
          (rho ⟨(i + 1 + 1) / 2, _⟩)))
      rw [show (⟨(i / 2 + 1) % N.height, _⟩ : Fin N.height) = r by
          apply Fin.ext
          exact hidx,
        show (⟨(i + 1 + 1) / 2, _⟩ : Fin N.height) = r by
          apply Fin.ext
          exact hedgeidx]
      change Incident G (T'.vertex (Fin.castLE hnew_upper r))
          (NormalCycleEdge N (rho r)) ∧
        (psi (NormalCycleEdge N (rho r)) = some A ∨
          psi (NormalCycleEdge N (rho r)) = some B)
      constructor
      · rw [Incident, hrot_ends]
        simp
      · exact hrot_color r (by simp [r])
    · have ho : i % 2 = 1 := by omega
      have he' : (i + 1) % 2 = 0 := by omega
      rw [hnode_odd _ he, hnode_even _ he']
      let r : Fin N.height := ⟨(i + 1) / 2, by omega⟩
      have hedgeidx : (i + 1) / 2 = r.val := rfl
      have hvertexidx : ((i + 1) / 2 + 1) % N.height =
          (r.val + 1) % N.height := by rfl
      change H.Adj
        (Sum.inr (NormalCycleEdge N
          (rho ⟨(i + 1) / 2, _⟩)))
        (Sum.inl (T'.vertex (Fin.castLE hnew_upper
          ⟨((i + 1) / 2 + 1) % N.height, _⟩)))
      rw [show (⟨(i + 1) / 2, _⟩ : Fin N.height) = r by
          apply Fin.ext
          exact hedgeidx,
        show (⟨((i + 1) / 2 + 1) % N.height, _⟩ : Fin N.height) =
            ⟨(r.val + 1) % N.height, Nat.mod_lt _ (by omega)⟩ by
          apply Fin.ext
          exact hvertexidx]
      change Incident G
          (T'.vertex (Fin.castLE hnew_upper
            ⟨(r.val + 1) % N.height, Nat.mod_lt _ (by omega)⟩))
          (NormalCycleEdge N (rho r)) ∧
        (psi (NormalCycleEdge N (rho r)) = some A ∨
          psi (NormalCycleEdge N (rho r)) = some B)
      constructor
      · rw [Incident, hrot_ends]
        simp
      · exact hrot_color r (by simp [r]; omega)
  have hnodes_nonempty : nodes ≠ [] := by
    simp [nodes]
  let rawPath := SimpleGraph.Walk.ofSupport nodes hnodes_nonempty hchain
  have hstart : nodes.head hnodes_nonempty =
      Sum.inl (T'.vertex ⟨1, Nat.succ_lt_succ T'.positive⟩) := by
    change (List.ofFn pathNode).head _ = _
    rw [List.head_ofFn, hnode_even]
    · congr 2
      apply Fin.ext
      simpa using (Nat.mod_eq_of_lt (by omega : 1 < N.height))
    · simp
  have hend : nodes.getLast hnodes_nonempty =
      Sum.inl (T'.vertex ⟨0, Nat.zero_lt_succ T'.length⟩) := by
    change (List.ofFn pathNode).getLast _ = _
    rw [List.getLast_ofFn_succ, hnode_even]
    · congr 2
      apply Fin.ext
      change ((2 * (N.height - 1)) / 2 + 1) % N.height = 0
      have hh : N.height - 1 + 1 = N.height := by omega
      rw [Nat.mul_div_right (N.height - 1) (by omega : 0 < 2), hh,
        Nat.mod_self]
    · change (2 * (N.height - 1)) % 2 = 0
      omega
  let closingPath : H.Walk
      (Sum.inl (T'.vertex ⟨1, Nat.succ_lt_succ T'.positive⟩))
      (Sum.inl (T'.vertex ⟨0, Nat.zero_lt_succ T'.length⟩)) :=
    rawPath.copy hstart hend
  have hpath_support : closingPath.support = nodes := by
    calc
      closingPath.support = rawPath.support := by
        simpa only [closingPath] using
          SimpleGraph.Walk.support_copy rawPath hstart hend
      _ = nodes := by
        simpa only [rawPath] using
          SimpleGraph.Walk.support_ofSupport hnodes_nonempty hchain
  have hpath_length : closingPath.length = 2 * (N.height - 1) := by
    calc
      closingPath.length = rawPath.length := by
        simpa only [closingPath] using
          SimpleGraph.Walk.length_copy rawPath hstart hend
      _ = nodes.length - 1 := by
        simpa only [rawPath] using
          SimpleGraph.Walk.length_ofSupport hnodes_nonempty hchain
      _ = 2 * (N.height - 1) := by
        simp [nodes]
  have hnode_injective : Function.Injective pathNode := by
    intro a b hab
    by_cases ha : a.val % 2 = 0
    · by_cases hb : b.val % 2 = 0
      · rw [hnode_even a ha, hnode_even b hb] at hab
        have hv := T'.vertex_injective (Sum.inl.inj hab)
        have hvv := congrArg Fin.val
          (Fin.castLE_injective hnew_upper hv)
        change (a.val / 2 + 1) % N.height =
          (b.val / 2 + 1) % N.height at hvv
        have hdiv : a.val / 2 = b.val / 2 := by
          by_cases hal : a.val / 2 + 1 < N.height
          · by_cases hbl : b.val / 2 + 1 < N.height
            · rw [Nat.mod_eq_of_lt hal, Nat.mod_eq_of_lt hbl] at hvv
              omega
            · have hbeq : b.val / 2 + 1 = N.height := by omega
              rw [hbeq, Nat.mod_self, Nat.mod_eq_of_lt hal] at hvv
              omega
          · by_cases hbl : b.val / 2 + 1 < N.height
            · have haeq : a.val / 2 + 1 = N.height := by omega
              rw [haeq, Nat.mod_self, Nat.mod_eq_of_lt hbl] at hvv
              omega
            · have haeq : a.val / 2 + 1 = N.height := by omega
              have hbeq : b.val / 2 + 1 = N.height := by omega
              omega
        apply Fin.ext
        omega
      · rw [hnode_even a ha, hnode_odd b hb] at hab
        simp at hab
    · by_cases hb : b.val % 2 = 0
      · rw [hnode_odd a ha, hnode_even b hb] at hab
        simp at hab
      · rw [hnode_odd a ha, hnode_odd b hb] at hab
        have hc := hcycle_injective (Sum.inr.inj hab)
        have hr := hrho_injective hc
        have hv := congrArg Fin.val hr
        simp at hv
        apply Fin.ext
        omega
  have hpath_isPath : closingPath.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hpath_support]
    exact List.nodup_ofFn.mpr hnode_injective
  have hvertex_support : ∀ v : V,
      Sum.inl v ∈ closingPath.support ↔
        ∃ i : Fin N.height,
          v = T'.vertex (Fin.castLE hnew_upper i) := by
    intro v
    rw [hpath_support]
    change Sum.inl v ∈ List.ofFn pathNode ↔ _
    rw [List.mem_ofFn]
    constructor
    · rintro ⟨n, hn⟩
      by_cases he : n.val % 2 = 0
      · rw [hnode_even n he] at hn
        exact ⟨⟨(n.val / 2 + 1) % N.height,
          Nat.mod_lt _ (by omega)⟩, (Sum.inl.inj hn).symm⟩
      · rw [hnode_odd n he] at hn
        simp at hn
    · rintro ⟨i, rfl⟩
      by_cases hi : i.val = 0
      · let n : Fin (2 * (N.height - 1) + 1) :=
          ⟨2 * (N.height - 1), by omega⟩
        refine ⟨n, ?_⟩
        rw [hnode_even n (by simp [n])]
        congr 2
        apply Fin.ext
        simp [n, hi]
        have hh : N.height - 1 + 1 = N.height := by omega
        rw [hh, Nat.mod_self]
      · let n : Fin (2 * (N.height - 1) + 1) :=
          ⟨2 * (i.val - 1), by omega⟩
        refine ⟨n, ?_⟩
        rw [hnode_even n (by simp [n])]
        congr 2
        apply Fin.ext
        simp [n]
        have hieq : i.val - 1 + 1 = i.val := by omega
        rw [hieq, Nat.mod_eq_of_lt i.isLt]
  have hedge_support : ∀ f : E,
      Sum.inr f ∈ closingPath.support ↔
        f = NormalCycleEdge N pred ∨
          ∃ r : Fin T'.length,
            1 ≤ r.val ∧ r.val + 2 ≤ N.height ∧ f = T'.edge r := by
    intro f
    rw [hpath_support]
    change Sum.inr f ∈ List.ofFn pathNode ↔ _
    rw [List.mem_ofFn]
    constructor
    · rintro ⟨n, hn⟩
      by_cases he : n.val % 2 = 0
      · rw [hnode_even n he] at hn
        simp at hn
      · rw [hnode_odd n he] at hn
        let r : Fin N.height := ⟨(n.val + 1) / 2, by omega⟩
        have hrpos : 1 ≤ r.val := by
          dsimp [r]
          omega
        by_cases hlast : r.val + 1 = N.height
        · left
          have hr : r = last := by
            apply Fin.ext
            simp [last]
            omega
          simpa [pred, r, hr] using (Sum.inr.inj hn).symm
        · right
          have hrbefore : r.val + 1 < N.height := by omega
          let rt : Fin T'.length := ⟨r.val, by
            have hu := hnew_upper
            omega⟩
          refine ⟨rt, by simpa [rt] using hrpos, by simp [rt]; omega, ?_⟩
          have heq := htrunk_edge_eq rt (by simp [rt]; omega)
          have hrr : (⟨rt.val, by
              simpa [rt] using Nat.lt_of_succ_lt hrbefore⟩ : Fin N.height) = r := by
            apply Fin.ext
            rfl
          rw [heq, hrr]
          exact (Sum.inr.inj hn).symm
    · rintro (hclose | ⟨r, hrpos, hrbound, rfl⟩)
      · let n : Fin (2 * (N.height - 1) + 1) :=
          ⟨2 * (N.height - 1) - 1, by omega⟩
        refine ⟨n, ?_⟩
        rw [hnode_odd n (by simp [n]; omega)]
        rw [hclose]
        congr 2
        apply congrArg rho
        apply Fin.ext
        simp [n, pred, last]
        omega
      · let n : Fin (2 * (N.height - 1) + 1) :=
          ⟨2 * r.val - 1, by omega⟩
        refine ⟨n, ?_⟩
        rw [hnode_odd n (by simp [n]; omega)]
        have heq := htrunk_edge_eq r (by omega)
        rw [heq]
        congr 2
        apply congrArg rho
        apply Fin.ext
        simp [n]
        omega
  let lastIndex : Fin (T'.length + 1) := Fin.castLE hnew_upper last
  have hclosing_ends : G.ends (NormalCycleEdge N pred) =
      s(T'.vertex lastIndex,
        T'.vertex ⟨0, Nat.zero_lt_succ T'.length⟩) := by
    rw [show pred = rho last by rfl, hrot_ends]
    apply Sym2.eq_iff.mpr
    left
    constructor
    · rfl
    · apply congrArg T'.vertex
      apply Fin.ext
      change (N.height - 1 + 1) % N.height = 0
      have hh : N.height - 1 + 1 = N.height := by omega
      rw [hh, Nat.mod_self]
  have htrunk_ends : ∀ r : Fin T'.length,
      1 ≤ r.val → r.val + 2 ≤ N.height →
        G.ends (T'.edge r) =
          s(T'.vertex ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩,
            T'.vertex r.succ) := by
    intro r hrpos hrbound
    have hrbefore : r.val + 1 < N.height := by omega
    rw [htrunk_edge_eq r hrbefore,
      hrot_ends ⟨r.val, by omega⟩]
    apply Sym2.eq_iff.mpr
    left
    constructor
    · apply congrArg T'.vertex
      apply Fin.ext
      rfl
    · apply congrArg T'.vertex
      apply Fin.ext
      change (r.val + 1) % N.height = r.val + 1
      exact Nat.mod_eq_of_lt (by omega)
  have hnew_zero : T'.vertex ⟨0, Nat.zero_lt_succ T'.length⟩ =
      T.vertex (Fin.castLE N.height_upper j) := by
    rw [show (⟨0, Nat.zero_lt_succ T'.length⟩ : Fin (T'.length + 1)) =
        Fin.castLE hnew_upper (⟨0, by omega⟩ : Fin N.height) by rfl,
      hrot_vertex, hrho_zero]
  have hnew_one : T'.vertex ⟨1, Nat.succ_lt_succ T'.positive⟩ =
      T.vertex (Fin.castLE N.height_upper
        ⟨(j.val + 1) % N.height, Nat.mod_lt _ (by omega)⟩) := by
    rw [show (⟨1, Nat.succ_lt_succ T'.positive⟩ : Fin (T'.length + 1)) =
        Fin.castLE hnew_upper (⟨1, by omega⟩ : Fin N.height) by rfl,
      hrot_vertex]
    apply congrArg T.vertex
    apply congrArg (Fin.castLE N.height_upper)
    apply Fin.ext
    rfl
  let N' : NormalGlobalMaximumTriple G k (NormalCycleEdge N j) psi T' :=
    { global := hglobal
      height := N.height
      height_lower := by omega
      height_upper := hnew_upper
      alpha := A
      beta := B
      alpha_missing := by
        rw [hnew_zero]
        exact hmissA
      beta_missing := by
        rw [hnew_one]
        exact hmissB
      closingEdge := NormalCycleEdge N pred
      lastIndex := lastIndex
      lastIndex_height := by
        change (N.height - 1) + 1 = N.height
        omega
      closing_ends := hclosing_ends
      closingPath := closingPath
      closingPath_isPath := hpath_isPath
      closingPath_length := hpath_length
      closingPath_vertices := hvertex_support
      closingPath_edges := hedge_support
      trunk_edge_ends := htrunk_ends }
  refine ⟨N', rfl, rfl, rfl, pred, hpred_val, rfl⟩
