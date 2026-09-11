import Tablet.IsProperEdgeColoring
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.TreeExit
import Tablet.TreeExitPath
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: TreeExitComponentMeetsTreeOnlyAtExit]
theorem TreeExitComponentMeetsTreeOnlyAtExit
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) (v : V)
    (hproper : IsProperEdgeColoring G phi)
    (hmissing : alpha ∈ MissingColors G phi v)
    (hexit : TreeExit T phi alpha beta v) :
    ∀ w, w ∈ TreeSequenceVertexSet T →
      (Sum.inl w ∈ TwoColorComponent G phi alpha beta (Sum.inl v) ↔ w = v) := by
-- BODY
  classical
  have hdegree : ∀ w, alpha ∈ MissingColors G phi w ∨
      beta ∈ MissingColors G phi w →
      (TwoColorIncidenceGraph G phi alpha beta).degree (Sum.inl w) ≤ 1 := by
    intro w hw
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_one.mpr
    intro y hy z hz
    simp only [SimpleGraph.mem_neighborFinset] at hy hz
    cases y with
    | inl y => simp [TwoColorIncidenceGraph] at hy
    | inr e =>
      cases z with
      | inl z => simp [TwoColorIncidenceGraph] at hz
      | inr f =>
        simp only [TwoColorIncidenceGraph] at hy hz
        rcases hw with hw | hw
        · have he : phi e = some beta := hy.2.resolve_left (by
            intro he
            apply (by simpa [MissingColors] using hw)
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨e, hy.1, he⟩)
          have hf : phi f = some beta := hz.2.resolve_left (by
            intro hf
            apply (by simpa [MissingColors] using hw)
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨f, hz.1, hf⟩)
          by_cases h : e = f
          · exact congrArg Sum.inr h
          · exact (hproper h ⟨w, hy.1, hz.1⟩ he hf).elim
        · have he : phi e = some alpha := hy.2.resolve_right (by
            intro he
            apply (by simpa [MissingColors] using hw)
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨e, hy.1, he⟩)
          have hf : phi f = some alpha := hz.2.resolve_right (by
            intro hf
            apply (by simpa [MissingColors] using hw)
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨f, hz.1, hf⟩)
          by_cases h : e = f
          · exact congrArg Sum.inr h
          · exact (hproper h ⟨w, hy.1, hz.1⟩ he hf).elim
  rcases hexit with ⟨u, path, pathData⟩
  rcases pathData with ⟨pathIs, pathLen, uOut, endTree, endOnly⟩
  have hdegreeBound : ∀ x, @SimpleGraph.degree _
      (TwoColorIncidenceGraph G phi alpha beta) x
      (Fintype.ofFinite _) ≤ 2 := by
    intro x
    exact TwoColorIncidenceDegreeAtMostTwo G phi alpha beta hproper x
  have huDegree := hdegree u endOnly.1
  have hclosed : ∀ x, x ∈ path.support → ∀ y,
      (TwoColorIncidenceGraph G phi alpha beta).Adj x y →
      y ∈ path.support := by
    intro x hx y hxy
    obtain ⟨n, hn, hnle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
    by_cases hn0 : n = 0
    · subst n
      have hx0 : x = Sum.inl u := by simpa using hn.symm
      let graph := TwoColorIncidenceGraph G phi alpha beta
      letI : Fintype (graph.neighborSet x) := Fintype.ofFinite _
      have card : Fintype.card (graph.neighborSet x) ≤ 1 := by
        rw [SimpleGraph.card_neighborSet_eq_degree]
        convert huDegree using 1
        cases hx0
        exact congrArg (fun z => @SimpleGraph.degree _ graph (Sum.inl u) z)
          (Subsingleton.elim _ _)
      have hy' : y ∈ graph.neighborSet x := by
        simpa [graph, SimpleGraph.mem_neighborSet] using hxy
      have hn' : path.getVert 1 ∈ graph.neighborSet x := by
        simpa [graph, hx0, SimpleGraph.mem_neighborSet] using
          path.adj_getVert_succ (show 0 < path.length by omega)
      have heq := Fintype.card_le_one_iff.mp card
        ⟨y, hy'⟩ ⟨path.getVert 1, hn'⟩
      have hey : y = path.getVert 1 := congrArg Subtype.val heq
      rw [hey]
      exact path.getVert_mem_support 1
    by_cases hlast : n = path.length
    · have hx1 : x = Sum.inl v := by
        rw [← hn, pathIs.getVert_eq_end_iff hnle]
        exact hlast
      let graph := TwoColorIncidenceGraph G phi alpha beta
      letI : Fintype (graph.neighborSet x) := Fintype.ofFinite _
      have card : Fintype.card (graph.neighborSet x) ≤ 1 := by
        rw [SimpleGraph.card_neighborSet_eq_degree]
        convert hdegree v (Or.inl hmissing) using 1
        cases hx1
        exact congrArg (fun z => @SimpleGraph.degree _ graph (Sum.inl v) z)
          (Subsingleton.elim _ _)
      have hy' : y ∈ graph.neighborSet x := by
        simpa [graph, SimpleGraph.mem_neighborSet] using hxy
      have hp : path.getVert (path.length - 1) ∈ graph.neighborSet x := by
        have ha : graph.Adj (Sum.inl v) (path.getVert (path.length - 1)) := by
          simpa [graph, show path.length - 1 + 1 = path.length by omega] using
            (path.adj_getVert_succ
              (show path.length - 1 < path.length by omega)).symm
        simpa [hx1, SimpleGraph.mem_neighborSet] using ha
      have heq := Fintype.card_le_one_iff.mp card
        ⟨y, hy'⟩ ⟨path.getVert (path.length - 1), hp⟩
      have hey : y = path.getVert (path.length - 1) := congrArg Subtype.val heq
      rw [hey]
      exact path.getVert_mem_support _
    have hl : (TwoColorIncidenceGraph G phi alpha beta).Adj
        (path.getVert n) (path.getVert (n - 1)) := by
      rw [← show n - 1 + 1 = n by omega]
      exact (path.adj_getVert_succ (by omega)).symm
    have hnlt : n < path.length := lt_of_le_of_ne hnle hlast
    have hr := path.adj_getVert_succ hnlt
    by_contra hyout
    rw [← hn] at hxy
    have hnl : path.getVert (n - 1) ≠ y := by
      intro h
      apply hyout
      rw [← h]
      exact path.getVert_mem_support _
    have hnr : path.getVert (n + 1) ≠ y := by
      intro h
      apply hyout
      rw [← h]
      exact path.getVert_mem_support _
    have hnp : path.getVert (n - 1) ≠ path.getVert (n + 1) := by
      intro h
      have hi := pathIs.getVert_injOn
        (show n - 1 ≤ path.length by omega)
        (show n + 1 ≤ path.length by omega) h
      omega
    let graph := TwoColorIncidenceGraph G phi alpha beta
    letI : Fintype (graph.neighborSet (path.getVert n)) := Fintype.ofFinite _
    have three : 3 ≤ graph.degree (path.getVert n) := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      let s : Finset _ := {y, path.getVert (n - 1), path.getVert (n + 1)}
      have hs : s ⊆ graph.neighborFinset (path.getVert n) := by
        intro t ht
        simp only [s, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · simpa [graph, SimpleGraph.mem_neighborFinset] using hxy
        · simpa [graph, SimpleGraph.mem_neighborFinset] using hl
        · simpa [graph, SimpleGraph.mem_neighborFinset] using hr
      have hc : 3 ≤ s.card := by
        simp [s, hnl, hnr, hnp, hnl.symm, hnr.symm, hnp.symm]
      exact hc.trans (Finset.card_le_card hs)
    have upper : graph.degree (path.getVert n) ≤ 2 :=
      hdegreeBound (path.getVert n)
    omega
  intro w hw
  constructor
  · intro hwC
    let graph := TwoColorIncidenceGraph G phi alpha beta
    have reach : graph.Reachable (Sum.inl v) (Sum.inl w) := by
      change graph.connectedComponentMk (Sum.inl w) =
        graph.connectedComponentMk (Sum.inl v) at hwC
      exact SimpleGraph.ConnectedComponent.eq.mp hwC |>.symm
    have ws : Sum.inl w ∈ path.support := by
      apply reach.mem_subgraphVerts
        (H := (⊤ : graph.Subgraph).induce {x | x ∈ path.support})
        (fun x hx y hadj =>
          ⟨by simpa using hx, hclosed x (by simpa using hx) y hadj, hadj⟩)
        (by simpa using path.getVert_mem_support path.length)
    exact (endOnly.2 w hw).mp ws
  · rintro rfl
    change (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk
      (Sum.inl w) = (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk
        (Sum.inl w)
    rfl
