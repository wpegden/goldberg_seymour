import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.Incident
import Tablet.LooplessMultigraph
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ExtensionBaseCaseTwoObservation21]
theorem ExtensionBaseCaseTwoObservation21 {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (Tn TjPrime : TreeSequence G e0)
    (rho1 : PartialEdgeColoring E k) (gammaN deltaN : Fin k)
    (fN : E) (terminalSupport x : V)
    (p : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk
      (Sum.inl terminalSupport) (Sum.inl x))
    (hpath : p.IsPath)
    (hcomponent : {y : Sum V E | y ∈ p.support} =
      TwoColorComponent G rho1 gammaN deltaN (Sum.inl terminalSupport))
    (hterminalN : terminalSupport ∈ TreeSequenceVertexSet Tn)
    (hterminalPrime : terminalSupport ∈ TreeSequenceVertexSet TjPrime)
    (hxOutside : x ∉
      TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime)
    (htwoN : ∃ w ∈ TreeSequenceVertexSet Tn,
      w ≠ terminalSupport ∧ Sum.inl w ∈ p.support)
    (hgammaBoundary : BoundaryColorEdges G rho1
      (TreeSequenceVertexSet Tn) gammaN = {fN})
    (hdeltaBoundary : BoundaryColorEdges G rho1
      (TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime) deltaN = ∅)
    (hfNterminal : Incident G terminalSupport fN) :
    ∃ (u : V)
      (exitPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk
        (Sum.inl x) (Sum.inl u)),
      u ∈ TreeSequenceVertexSet TjPrime \ TreeSequenceVertexSet Tn ∧
        exitPath.IsPath ∧ 2 ≤ exitPath.length ∧
        (∀ y : Sum V E, y ∈ exitPath.support → y ∈ p.support) ∧
        (∀ w : V,
          w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime →
          (Sum.inl w ∈ exitPath.support ↔ w = u)) ∧
        (∃ g ∈ BoundaryColorEdges G rho1
            (TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime) gammaN,
          Incident G u g ∧ Sum.inr g ∈ exitPath.support) ∧
        ¬ Incident G u fN := by
-- BODY
  classical
  letI : BEq (Sum V E) := instBEqOfDecidableEq
  let vertexSet := TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime
  let eligible : List (Sum V E) := p.support.filter (fun z =>
    match z with
    | Sum.inl v => decide (v ∈ vertexSet)
    | Sum.inr _ => false)
  have eligible_nonempty : eligible ≠ [] := by
    apply List.ne_nil_of_mem
    apply List.mem_filter.mpr
    refine ⟨p.start_mem_support, ?_⟩
    simp [vertexSet, hterminalN, hterminalPrime]
  let chosen : Sum V E := eligible.getLast eligible_nonempty
  have chosen_mem : chosen ∈ eligible := List.getLast_mem eligible_nonempty
  have chosen_pred := (List.mem_filter.mp chosen_mem).2
  have chosen_support : chosen ∈ p.support := List.mem_of_mem_filter chosen_mem
  obtain ⟨u, chosen_eq⟩ : ∃ u : V, chosen = Sum.inl u := by
    by_cases h : ∃ v : V, chosen = Sum.inl v
    · exact h
    · exfalso
      obtain ⟨e, he⟩ : ∃ e : E, chosen = Sum.inr e := by
        cases hc : chosen with
        | inl v => exact False.elim (h ⟨v, hc⟩)
        | inr e => exact ⟨e, rfl⟩
      rw [he] at chosen_pred
      exact False.elim (by simpa using chosen_pred)
  let uSupport : Sum V E := Sum.inl u
  have huSupport : uSupport ∈ p.support := by simpa [uSupport, chosen_eq] using chosen_support
  have huVertex : u ∈ vertexSet := by
    rw [chosen_eq] at chosen_pred
    simpa [vertexSet] using chosen_pred
  have singleton_of_head_last : ∀ (l : List (Sum V E)) (a : Sum V E),
      l.Nodup → l.head? = some a → l.getLast? = some a → l = [a] := by
    intro l
    induction l with
    | nil => simp
    | cons b t ih =>
      intro a hn hh hl
      simp only [List.head?_cons] at hh
      have hba : b = a := Option.some.inj hh
      subst b
      by_cases ht : t = []
      · simp [ht]
      · have hlast : t.getLast? = some a := by
          cases t with
          | nil => contradiction
          | cons c r => simpa using hl
        obtain ⟨ys, hys⟩ := (List.getLast?_eq_some_iff.mp hlast)
        have hmem : a ∈ t := by
          rw [hys]
          simp
        exact False.elim ((List.nodup_cons.mp hn).1 hmem)
  let suffix := p.dropUntil uSupport huSupport
  let exitPath := suffix.reverse
  have suffix_path : suffix.IsPath := hpath.dropUntil huSupport
  have exit_path : exitPath.IsPath := suffix_path.reverse
  have exit_support : exitPath.support = suffix.support.reverse := by
    simp [exitPath, SimpleGraph.Walk.support_reverse]
  have suffix_eligible_nonempty :
      (suffix.support.filter (fun z => match z with
        | Sum.inl v => decide (v ∈ vertexSet)
        | Sum.inr _ => false)) ≠ [] := by
    apply List.ne_nil_of_mem (a := uSupport)
    exact List.mem_filter.mpr ⟨suffix.start_mem_support, by simp [uSupport, huVertex]⟩
  have suffix_filter_last :
      (suffix.support.filter (fun z => match z with
        | Sum.inl v => decide (v ∈ vertexSet)
        | Sum.inr _ => false)).getLast suffix_eligible_nonempty = uSupport := by
    have hsuf : suffix.support <:+ p.support := by
      simpa [suffix] using p.support_dropUntil_suffix_support huSupport
    have hfiltered := hsuf.filter (fun z => match z with
      | Sum.inl v => decide (v ∈ vertexSet)
      | Sum.inr _ => false)
    have heq := hfiltered.getLast suffix_eligible_nonempty
    convert heq using 1 <;> simp [eligible, chosen, chosen_eq, uSupport]
  have suffix_filter_singleton :
      suffix.support.filter (fun z => match z with
        | Sum.inl v => decide (v ∈ vertexSet)
        | Sum.inr _ => false) = [uSupport] := by
    refine singleton_of_head_last
      (suffix.support.filter (fun z : Sum V E => match z with
        | Sum.inl v => decide (v ∈ vertexSet)
        | Sum.inr _ => false)) uSupport ?_ ?_ ?_
    · exact (suffix_path.support_nodup).filter _
    · rw [← suffix.cons_tail_support]
      rw [List.filter_cons]
      simp [uSupport, huVertex]
    · change (suffix.support.filter (fun z : Sum V E => match z with
          | Sum.inl v => decide (v ∈ vertexSet)
          | Sum.inr _ => false)).getLast? = some uSupport
      cases hlist : suffix.support.filter (fun z : Sum V E => match z with
          | Sum.inl v => decide (v ∈ vertexSet)
          | Sum.inr _ => false) with
      | nil => exact False.elim (suffix_eligible_nonempty hlist)
      | cons a t =>
          have hlast := suffix_filter_last
          have hlast' : (a :: t).getLast (by simp) = uSupport := by
            simpa [hlist] using hlast
          simpa [List.getLast?, hlist] using congrArg some hlast'
  have hu_terminal : u ≠ terminalSupport := by
    intro heq
    subst u
    have hs : suffix = p := by
      simpa [suffix, uSupport, chosen_eq] using p.dropUntil_first p.start_mem_support
    obtain ⟨w, hw, hwu, hwm⟩ := htwoN
    have hwm' : Sum.inl w ∈ suffix.support := by rw [hs]; exact hwm
    have hwf : Sum.inl w ∈ suffix.support.filter (fun z => match z with
        | Sum.inl v => decide (v ∈ vertexSet)
        | Sum.inr _ => false) := by
      apply List.mem_filter.mpr
      exact ⟨hwm', by simp [vertexSet, hw]⟩
    rw [suffix_filter_singleton] at hwf
    apply hwu
    simpa [uSupport] using hwf
  have suffix_positive : 0 < suffix.length := by
    by_contra hz
    have hz0 : suffix.length = 0 := by omega
    have hux := SimpleGraph.Walk.eq_of_length_eq_zero hz0
    have : x = u := by simpa [uSupport] using hux.symm
    apply hxOutside
    rw [this]
    exact huVertex
  have suffix_not_one : suffix.length ≠ 1 := by
    intro hone
    have ha := suffix.adj_getVert_succ (i := 0) (by omega)
    have hzero : suffix.getVert 0 = Sum.inl u := by simp [uSupport]
    rw [hzero] at ha
    rw [show suffix.getVert 1 = suffix.getVert suffix.length by simp [hone]] at ha
    rw [suffix.getVert_length] at ha
    simpa [TwoColorIncidenceGraph] using ha
  have suffix_length_two : 2 ≤ suffix.length := by omega
  have first_edge : ∃ g : E, suffix.getVert 1 = Sum.inr g := by
    have ha := suffix.adj_getVert_succ (i := 0) (by omega)
    cases hcase : suffix.getVert 1 with
    | inl v => exfalso; rw [suffix.getVert_zero, hcase] at ha; simp [uSupport, TwoColorIncidenceGraph] at ha
    | inr g => exact ⟨g, rfl⟩
  obtain ⟨g, hg⟩ := first_edge
  have next_vertex : ∃ v : V, suffix.getVert 2 = Sum.inl v := by
    have ha := suffix.adj_getVert_succ (i := 1) (by omega)
    cases hcase : suffix.getVert 2 with
    | inl v => exact ⟨v, rfl⟩
    | inr e => exfalso; rw [hg, hcase] at ha; simp [TwoColorIncidenceGraph] at ha
  obtain ⟨v, hv⟩ := next_vertex
  have hv_outside : v ∉ vertexSet := by
    intro hvin
    have hvm : Sum.inl v ∈ suffix.support := by
      apply SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
      exact ⟨2, hv, by omega⟩
    have hvf : Sum.inl v ∈ suffix.support.filter (fun z => match z with
        | Sum.inl z => decide (z ∈ vertexSet)
        | Sum.inr _ => false) := by
      exact List.mem_filter.mpr ⟨hvm, by simp [hvin]⟩
    rw [suffix_filter_singleton] at hvf
    have hvu : v = u := by simpa [uSupport] using hvf
    have hinj := suffix_path.getVert_injOn (by omega : 0 ≤ suffix.length)
      (by omega : 2 ≤ suffix.length)
      (show suffix.getVert 0 = suffix.getVert 2 by
        rw [suffix.getVert_zero, hv]
        exact congrArg Sum.inl hvu.symm)
    omega
  have hgu : Incident G u g := by
    have ha := suffix.adj_getVert_succ (i := 0) (by omega)
    rw [suffix.getVert_zero, hg] at ha
    simpa [uSupport, TwoColorIncidenceGraph] using ha.1
  have hgv : Incident G v g := by
    have ha := suffix.adj_getVert_succ (i := 1) (by omega)
    rw [hg, hv] at ha
    simpa [TwoColorIncidenceGraph] using ha.1
  have huv : u ≠ v := by
    intro huv
    have hinj := suffix_path.getVert_injOn (by omega : 0 ≤ suffix.length)
      (by omega : 2 ≤ suffix.length)
      (show suffix.getVert 0 = suffix.getVert 2 by
        rw [suffix.getVert_zero, hv]
        exact congrArg Sum.inl huv)
    omega
  have hends : G.ends g = s(u, v) := by
    have ends_eq_of_mem : ∀ {z : Sym2 V} {a b : V}, a ∈ z → b ∈ z → a ≠ b → z = s(a,b) := by
      intro z a b ha hb hab
      induction z using Sym2.inductionOn with
      | _ c d =>
        simp only [Sym2.mem_iff] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all [Sym2.eq_iff]
    exact ends_eq_of_mem hgu hgv huv
  have hg_boundary : g ∈ BoundaryEdges G vertexSet := by
    unfold BoundaryEdges
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨u, huVertex, v, hv_outside, hends⟩
  have hg_color : rho1 g = some gammaN ∨ rho1 g = some deltaN := by
    have ha := suffix.adj_getVert_succ (i := 0) (by omega)
    rw [suffix.getVert_zero, hg] at ha
    simpa [TwoColorIncidenceGraph] using ha.2
  have hg_gamma : rho1 g = some gammaN := by
    rcases hg_color with hg' | hg'
    · exact hg'
    · exfalso
      have hmem : g ∈ BoundaryColorEdges G rho1 vertexSet deltaN := by
        unfold BoundaryColorEdges
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hg_boundary, hg'⟩
      simpa [vertexSet, hdeltaBoundary] using hmem
  have hg_colored_boundary : g ∈ BoundaryColorEdges G rho1 vertexSet gammaN := by
    unfold BoundaryColorEdges
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hg_boundary, hg_gamma⟩
  have hu_not_Tn : u ∉ TreeSequenceVertexSet Tn := by
    intro huT
    have hgt : g ∈ BoundaryColorEdges G rho1 (TreeSequenceVertexSet Tn) gammaN := by
      unfold BoundaryColorEdges
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, hg_gamma⟩
      unfold BoundaryEdges
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hvTn : v ∉ TreeSequenceVertexSet Tn := by
        intro hvT
        exact hv_outside (Finset.mem_union.mpr (Or.inl hvT))
      exact ⟨u, huT, v, hvTn, hends⟩
    rw [hgammaBoundary] at hgt
    have hgf : g = fN := by simpa using hgt
    subst g
    have heq : u = terminalSupport := by
      have ht : terminalSupport ∈ s(u, v) := by
        rw [← hends]
        exact hfNterminal
      simp only [Sym2.mem_iff] at ht
      rcases ht with rfl | rfl
      · rfl
      · exfalso
        apply hv_outside
        exact Finset.mem_union.mpr (Or.inl hterminalN)
    exact hu_terminal heq
  refine ⟨u, exitPath, ?_, exit_path, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Finset.mem_sdiff]
    constructor
    · rcases Finset.mem_union.mp huVertex with h | h
      · exact False.elim (hu_not_Tn h)
      · exact h
    · exact hu_not_Tn
  · simpa [exitPath] using suffix_length_two
  · intro y hy
    have hy' : y ∈ suffix.support := by
      rw [exit_support] at hy
      exact List.mem_reverse.mp hy
    have hsuf : suffix.support <:+ p.support := by
      simpa [suffix] using p.support_dropUntil_suffix_support huSupport
    exact hsuf.subset hy'
  · intro w hw
    constructor
    · intro hwm
      have hwm' : Sum.inl w ∈ suffix.support := by
        rw [exit_support] at hwm
        exact List.mem_reverse.mp hwm
      have hwf : Sum.inl w ∈ suffix.support.filter (fun z => match z with
          | Sum.inl z => decide (z ∈ vertexSet)
          | Sum.inr _ => false) :=
        List.mem_filter.mpr ⟨hwm', by simp [vertexSet, hw]⟩
      rw [suffix_filter_singleton] at hwf
      simpa [uSupport] using hwf
    · intro hwu
      subst w
      rw [exit_support]
      apply List.mem_reverse.mpr
      have huf : Sum.inl u ∈ suffix.support.filter (fun z => match z with
          | Sum.inl z => decide (z ∈ vertexSet)
          | Sum.inr _ => false) := by
        rw [suffix_filter_singleton]
        simp [uSupport]
      exact (List.mem_filter.mp huf).1
  · refine ⟨g, ?_, hgu, ?_⟩
    · simpa [vertexSet] using hg_colored_boundary
    · rw [exit_support]
      apply List.mem_reverse.mpr
      apply SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
      exact ⟨1, hg, by omega⟩
  have hf_boundary : fN ∈ BoundaryColorEdges G rho1
      (TreeSequenceVertexSet Tn) gammaN := by
    rw [hgammaBoundary]
    simp
  have hf_color : rho1 fN = some gammaN := by
    have hh := hf_boundary
    unfold BoundaryColorEdges at hh
    exact (Finset.mem_filter.mp hh).2
  have hf_adj : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Adj
      (Sum.inl terminalSupport) (Sum.inr fN) :=
    ⟨hfNterminal, Or.inl hf_color⟩
  have hf_support : Sum.inr fN ∈ p.support := by
    change Sum.inr fN ∈ {y : Sum V E | y ∈ p.support}
    rw [hcomponent]
    apply (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hf_adj).symm
  · intro huf
    obtain ⟨w, hw, hwu, hwm⟩ := htwoN
    have hut : u ≠ terminalSupport := hu_terminal
    have hfend : G.ends fN = s(terminalSupport, u) := by
      have hend_of_mem : ∀ {z : Sym2 V} {a b : V}, a ∈ z → b ∈ z → a ≠ b →
          z = s(a,b) := by
        intro z a b ha hb hab
        induction z using Sym2.inductionOn with
        | _ c d =>
          simp only [Sym2.mem_iff] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
            simp_all [Sym2.eq_iff]
      exact hend_of_mem hfNterminal huf hut.symm
    obtain ⟨j, hj, hjle⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hf_support
    have hjf : p.getVert j = Sum.inr fN := hj
    have hjnotzero : j ≠ 0 := by
      intro hz
      have : (Sum.inl terminalSupport : Sum V E) = Sum.inr fN := by
        simpa [hz] using hjf.symm
      cases this
    have hjlt : j < p.length := by
      by_contra hn
      have he : j = p.length := by omega
      subst j
      have : (Sum.inl x : Sum V E) = Sum.inr fN := by
        simpa using hjf.symm
      cases this
    have hprev := p.adj_getVert_succ (i := j - 1) (by omega)
    have hnext := p.adj_getVert_succ (i := j) hjlt
    have hprev' : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Adj
        (p.getVert (j - 1)) (Sum.inr fN) := by
      rw [← hjf]
      simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hjnotzero)] using hprev
    have hprev_vertex : ∃ a : V, p.getVert (j - 1) = Sum.inl a := by
      cases hc : p.getVert (j - 1) with
      | inl a =>
          exact ⟨a, rfl⟩
      | inr e =>
          have ha := hprev'
          rw [hc] at ha
          exact False.elim (by simpa [TwoColorIncidenceGraph] using ha)
    have hnext_vertex : ∃ b : V, p.getVert (j + 1) = Sum.inl b := by
      have ha := hnext
      rw [hjf] at ha
      cases hc : p.getVert (j + 1) with
      | inl a =>
          exact ⟨a, rfl⟩
      | inr e =>
          rw [hc] at ha
          exact False.elim (by simpa [TwoColorIncidenceGraph] using ha)
    obtain ⟨a, ha⟩ := hprev_vertex
    obtain ⟨b, hb⟩ := hnext_vertex
    have hab : a ≠ b := by
      intro he
      have hi := hpath.getVert_injOn (by omega : j - 1 ≤ p.length)
        (by omega : j + 1 ≤ p.length)
        (by rw [ha, hb]; exact congrArg Sum.inl he)
      omega
    have hma : a ∈ G.ends fN := by
      have hh := hprev'
      rw [ha] at hh
      simpa [Incident, TwoColorIncidenceGraph] using hh.1
    have hmb : b ∈ G.ends fN := by
      have hh := hnext
      rw [hjf, hb] at hh
      simpa [Incident, TwoColorIncidenceGraph] using hh.1
    have edge_identity : ∀ {z : Sym2 V} {c d : V}, c ∈ z → d ∈ z → c ≠ d →
        z = s(c,d) := by
      intro z c d hc hd hcd
      induction z using Sym2.inductionOn with
      | _ r t =>
        simp only [Sym2.mem_iff] at hc hd
        rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> simp_all
    have hfends : G.ends fN = s(a,b) := edge_identity hma hmb hab
    have hterm_endpoint : terminalSupport ∈ s(a,b) := by
      rw [← hfends]
      exact hfNterminal
    have hendpoint : a = terminalSupport ∨ b = terminalSupport := by
      simp only [Sym2.mem_iff] at hterm_endpoint
      rcases hterm_endpoint with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    have hterm_prev : p.getVert (j - 1) = Sum.inl terminalSupport := by
      rcases hendpoint with h | h
      · simpa [ha, h]
      · exfalso
        have hi : j + 1 = 0 := by
          apply hpath.getVert_injOn
            (show j + 1 ≤ p.length from Nat.succ_le_of_lt hjlt)
            (show 0 ≤ p.length from Nat.zero_le _)
          simpa [hb, h] using p.getVert_zero.symm
        omega
    have hjone : j = 1 := by
      have hi : j - 1 = 0 := by
        apply hpath.getVert_injOn (by omega : j - 1 ≤ p.length)
            (show 0 ≤ p.length from Nat.zero_le _)
        exact hterm_prev.trans p.getVert_zero.symm
      have hjpos : 0 < j := Nat.pos_of_ne_zero hjnotzero
      omega
    have hu_at_two : p.getVert 2 = Sum.inl u := by
      have hjtwo : j + 1 = 2 := by omega
      have hbu : b = u := by
        have hm : b ∈ G.ends fN := hmb
        have : b = terminalSupport ∨ b = u := by
          rw [hfend] at hm
          simpa only [Sym2.mem_iff] using hm
        rcases this with h | h
        · exfalso
          have hi : 2 = 0 := by
            apply hpath.getVert_injOn (by omega : 2 ≤ p.length)
              (show 0 ≤ p.length from Nat.zero_le _)
            have htwo : p.getVert 2 = Sum.inl terminalSupport := by
              calc
                p.getVert 2 = p.getVert (j + 1) := congrArg p.getVert hjtwo.symm
                _ = Sum.inl b := hb
                _ = Sum.inl terminalSupport := by rw [h]
            exact htwo.trans p.getVert_zero.symm
          omega
        · exact h
      calc
        p.getVert 2 = p.getVert (j + 1) := congrArg p.getVert hjtwo.symm
        _ = Sum.inl b := hb
        _ = Sum.inl u := by rw [hbu]
    obtain ⟨iw, hiw, hiwle⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (by
        exact hwm)
    have hiwval : p.getVert iw = Sum.inl w := hiw
    have hiwgt : 2 < iw := by
      have hiwnzero : iw ≠ 0 := by
        intro hz
        have : w = terminalSupport := by
          subst iw
          exact Sum.inl.inj (hiwval.symm.trans p.getVert_zero)
        exact hwu this
      have hiwneone : iw ≠ 1 := by
        intro hz
        have : (Sum.inl w : Sum V E) = Sum.inr fN := by
          subst iw
          rw [hjone] at hjf
          exact hiwval.symm.trans hjf
        cases this
      have hiwneu : iw ≠ 2 := by
        intro hz
        have : w = u := by
          subst iw
          exact Sum.inl.inj (hiwval.symm.trans hu_at_two)
        exact hu_not_Tn (this ▸ hw)
      omega
    have hidx : p.support.idxOf uSupport = 2 := by
      apply hpath.getVert_injOn
        (by
          have hh := List.idxOf_lt_length_of_mem huSupport
          simp only [SimpleGraph.Walk.length_support] at hh
          exact Nat.le_of_lt_succ hh)
        (by omega : 2 ≤ p.length)
      calc
        p.getVert (p.support.idxOf uSupport) = uSupport :=
          p.getVert_support_idxOf huSupport
        _ = p.getVert 2 := by simpa [uSupport] using hu_at_two.symm
    have hsuffix : suffix.support = (p.drop 2).support := by
      change (p.dropUntil uSupport huSupport).support = (p.drop 2).support
      rw [SimpleGraph.Walk.dropUntil_eq_drop]
      simp [hidx]
    have hw_suffix : Sum.inl w ∈ suffix.support := by
      rw [hsuffix]
      have hdrop : (p.drop 2).support = p.support.drop 2 := by
        simpa [Nat.min_eq_left (by omega : 2 ≤ p.length)] using
          p.drop_support_eq_support_drop_min 2
      apply List.mem_iff_getElem.mpr
      refine ⟨iw - 2, ?_, ?_⟩
      · have hp : iw - 2 < p.length + 1 - 2 := by omega
        rw [hdrop]
        simp only [List.length_drop, SimpleGraph.Walk.length_support]
        omega
      ·
        have hvalid : iw - 2 < (p.support.drop 2).length := by
          simp [List.length_drop, SimpleGraph.Walk.length_support] <;> omega
        have helem : (p.support.drop 2)[iw - 2]'hvalid = Sum.inl w := by
          simp only [List.getElem_drop]
          have hsum : 2 + (iw - 2) = iw := by omega
          have hiwlt : iw < p.support.length := by
            simpa [SimpleGraph.Walk.length_support] using Nat.lt_succ_of_le hiwle
          have hh := p.support_getElem_eq_getVert (n := iw) hiwlt
          simpa [hsum] using hh.trans hiwval
        simpa [hdrop] using helem
    have hwf : Sum.inl w ∈ suffix.support.filter (fun z : Sum V E => match z with
        | Sum.inl v => decide (v ∈ vertexSet)
        | Sum.inr _ => false) := by
      apply List.mem_filter.mpr
      exact ⟨hw_suffix, by simp [vertexSet, hw]⟩
    rw [suffix_filter_singleton] at hwf
    have : w = u := by simpa [uSupport] using hwf
    exact hu_not_Tn (this ▸ hw)
