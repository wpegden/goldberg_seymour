import Tablet.ColoredVertexSetElementary
import Tablet.IsProperEdgeColoring
import Tablet.MissingColorIncidenceEndpoint
import Tablet.MissingColors
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: TwoColorComponentSwapNonElementary]
theorem TwoColorComponentSwapNonElementary {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (hproper : IsProperEdgeColoring G phi) (z : Sum V E)
    (X : Finset V) (u v : V) (huX : u ∈ X) (hvX : v ∈ X)
    (huv : u ≠ v)
    (huC : Sum.inl u ∈ TwoColorComponent G phi alpha beta z)
    (hvC : Sum.inl v ∈ TwoColorComponent G phi alpha beta z)
    (hua : alpha ∈ MissingColors G phi u)
    (hvb : beta ∈ MissingColors G phi v)
    (hnot : ¬ ColoredVertexSetElementary G phi X) :
    ¬ ColoredVertexSetElementary G
      (TwoColorComponentSwap G phi alpha beta z) X := by
-- BODY
  classical
  let H := TwoColorIncidenceGraph G phi alpha beta
  let C := TwoColorComponent G phi alpha beta z
  let phi' := TwoColorComponentSwap G phi alpha beta z
  obtain ⟨a, b, p, hp, hsupport⟩ :=
    TwoColorComponentSpanningPath G phi alpha beta hproper z
  have support_of_component {w : V} (hwC : Sum.inl w ∈ C) :
      Sum.inl w ∈ p.support := by
    change Sum.inl w ∈ {x | x ∈ p.support}
    rw [hsupport]
    exact hwC
  have hpu : Sum.inl u ∈ p.support := support_of_component huC
  have hpv : Sum.inl v ∈ p.support := support_of_component hvC
  have endpoint_of_missing_alpha {w : V} (hwC : Sum.inl w ∈ C)
      (hw : alpha ∈ MissingColors G phi w) : Sum.inl w = a ∨ Sum.inl w = b := by
    have hdegree : @SimpleGraph.degree _ H (Sum.inl w) (Fintype.ofFinite _) ≤ 1 := by
      simpa [H] using
        MissingColorIncidenceEndpoint G phi alpha beta hne hproper w hw
    have hleaf : (H.neighborSet (Sum.inl w)).Subsingleton := by
      letI : Fintype (H.neighborSet (Sum.inl w)) := Fintype.ofFinite _
      intro x hx y hy
      have hcard : Fintype.card (H.neighborSet (Sum.inl w)) ≤ 1 := by
        rw [SimpleGraph.card_neighborSet_eq_degree]
        exact hdegree
      exact congrArg Subtype.val
        (Fintype.card_le_one_iff.mp hcard ⟨x, hx⟩ ⟨y, hy⟩)
    by_contra hend
    push_neg at hend
    exact (hp.isTrail.not_mem_support_of_subsingleton_neighborSet
      hend.1 hend.2 hleaf) (support_of_component hwC)
  have endpoint_of_missing_beta {w : V} (hwC : Sum.inl w ∈ C)
      (hw : beta ∈ MissingColors G phi w) : Sum.inl w = a ∨ Sum.inl w = b := by
    have hgraph : TwoColorIncidenceGraph G phi beta alpha = H := by
      ext x y
      cases x <;> cases y <;> simp [H, TwoColorIncidenceGraph, or_comm]
    have hdegree : @SimpleGraph.degree _ H (Sum.inl w) (Fintype.ofFinite _) ≤ 1 := by
      rw [← hgraph]
      exact MissingColorIncidenceEndpoint G phi beta alpha hne.symm hproper w hw
    have hleaf : (H.neighborSet (Sum.inl w)).Subsingleton := by
      letI : Fintype (H.neighborSet (Sum.inl w)) := Fintype.ofFinite _
      intro x hx y hy
      have hcard : Fintype.card (H.neighborSet (Sum.inl w)) ≤ 1 := by
        rw [SimpleGraph.card_neighborSet_eq_degree]
        exact hdegree
      exact congrArg Subtype.val
        (Fintype.card_le_one_iff.mp hcard ⟨x, hx⟩ ⟨y, hy⟩)
    by_contra hend
    push_neg at hend
    exact (hp.isTrail.not_mem_support_of_subsingleton_neighborSet
      hend.1 hend.2 hleaf) (support_of_component hwC)
  have hu_end : Sum.inl u = a ∨ Sum.inl u = b :=
    endpoint_of_missing_alpha huC hua
  have hv_end : Sum.inl v = a ∨ Sum.inl v = b :=
    endpoint_of_missing_beta hvC hvb
  have hab : a ≠ b := by
    intro hab
    rcases hu_end with hua' | hub'
    · rcases hv_end with hva' | hvb'
      · exact huv (Sum.inl.inj (hua'.trans hva'.symm))
      · exact huv (Sum.inl.inj (hua'.trans (hab.trans hvb'.symm)))
    · rcases hv_end with hva' | hvb'
      · exact huv (Sum.inl.inj (hub'.trans (hab.symm.trans hva'.symm)))
      · exact huv (Sum.inl.inj (hub'.trans hvb'.symm))
  have hp_nontrivial : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hab
  have affected_edge_of_endpoint {w : V}
      (hw : Sum.inl w = a ∨ Sum.inl w = b) :
      ∃ e : E, Incident G w e ∧ (phi e = some alpha ∨ phi e = some beta) := by
    rcases hw with hwa | hwb
    · have hadj := p.adj_snd hp_nontrivial
      have hadj' : H.Adj (Sum.inl w) p.snd := by
        simpa only [H, hwa] using hadj
      cases hsnd : p.snd with
      | inl x =>
          rw [hsnd] at hadj'
          simp [H, TwoColorIncidenceGraph] at hadj'
      | inr e =>
          rw [hsnd] at hadj'
          refine ⟨e, ?_⟩
          simpa [H, TwoColorIncidenceGraph] using hadj'
    · have hrev : ¬ p.reverse.Nil := by simpa using hp_nontrivial
      have hadj := p.reverse.adj_snd hrev
      have hadj' : H.Adj (Sum.inl w) p.reverse.snd := by
        simpa only [H, hwb] using hadj
      cases hsnd : p.reverse.snd with
      | inl x =>
          rw [hsnd] at hadj'
          simp [H, TwoColorIncidenceGraph] at hadj'
      | inr e =>
          rw [hsnd] at hadj'
          refine ⟨e, ?_⟩
          simpa [H, TwoColorIncidenceGraph] using hadj'
  obtain ⟨eu, heu_incident, heu_color⟩ := affected_edge_of_endpoint hu_end
  obtain ⟨ev, hev_incident, hev_color⟩ := affected_edge_of_endpoint hv_end
  have alpha_not_present_u : alpha ∉ PresentColors G phi u := by
    simpa [MissingColors] using hua
  have beta_not_present_v : beta ∉ PresentColors G phi v := by
    simpa [MissingColors] using hvb
  have heu_beta : phi eu = some beta := by
    rcases heu_color with heu_alpha | heu_beta
    · exact False.elim (alpha_not_present_u (by
        simp [PresentColors]
        exact ⟨eu, heu_incident, heu_alpha⟩))
    · exact heu_beta
  have hev_alpha : phi ev = some alpha := by
    rcases hev_color with hev_alpha | hev_beta
    · exact hev_alpha
    · exact False.elim (beta_not_present_v (by
        simp [PresentColors]
        exact ⟨ev, hev_incident, hev_beta⟩))
  have beta_not_missing_u : beta ∉ MissingColors G phi u := by
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
    simp [PresentColors]
    exact ⟨eu, heu_incident, heu_beta⟩
  have alpha_not_missing_v : alpha ∉ MissingColors G phi v := by
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
    simp [PresentColors]
    exact ⟨ev, hev_incident, hev_alpha⟩
  have endpoint_is_u_or_v {w : V}
      (hw : Sum.inl w = a ∨ Sum.inl w = b) : w = u ∨ w = v := by
    rcases hu_end with hua' | hub'
    · rcases hv_end with hva' | hvb'
      · exact False.elim (huv (Sum.inl.inj (hua'.trans hva'.symm)))
      · rcases hw with hwa' | hwb'
        · exact Or.inl (Sum.inl.inj (hwa'.trans hua'.symm))
        · exact Or.inr (Sum.inl.inj (hwb'.trans hvb'.symm))
    · rcases hv_end with hva' | hvb'
      · rcases hw with hwa' | hwb'
        · exact Or.inr (Sum.inl.inj (hwa'.trans hva'.symm))
        · exact Or.inl (Sum.inl.inj (hwb'.trans hub'.symm))
      · exact False.elim (huv (Sum.inl.inj (hub'.trans hvb'.symm)))
  have unique_alpha {w : V} (hwC : Sum.inl w ∈ C)
      (hw : alpha ∈ MissingColors G phi w) : w = u := by
    rcases endpoint_is_u_or_v (endpoint_of_missing_alpha hwC hw) with rfl | rfl
    · rfl
    · exact False.elim (alpha_not_missing_v hw)
  have unique_beta {w : V} (hwC : Sum.inl w ∈ C)
      (hw : beta ∈ MissingColors G phi w) : w = v := by
    rcases endpoint_is_u_or_v (endpoint_of_missing_beta hwC hw) with rfl | rfl
    · exact False.elim (beta_not_missing_u hw)
    · rfl
  have edge_of_vertex {w : V} {e : E} (hwC : Sum.inl w ∈ C)
      (hwe : Incident G w e)
      (hecolor : phi e = some alpha ∨ phi e = some beta) : Sum.inr e ∈ C := by
    change H.connectedComponentMk (Sum.inl w) = H.connectedComponentMk z at hwC
    change H.connectedComponentMk (Sum.inr e) = H.connectedComponentMk z
    have hadj : H.Adj (Sum.inr e) (Sum.inl w) := by
      simpa [H, TwoColorIncidenceGraph] using And.intro hwe hecolor
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hwC
  have heuC : Sum.inr eu ∈ C :=
    edge_of_vertex huC heu_incident (Or.inr heu_beta)
  have hevC : Sum.inr ev ∈ C :=
    edge_of_vertex hvC hev_incident (Or.inl hev_alpha)
  have heu_new : phi' eu = some alpha := by
    simp [phi', TwoColorComponentSwap, C, heuC, heu_beta, hne]
  have hev_new : phi' ev = some beta := by
    simp [phi', TwoColorComponentSwap, C, hevC, hev_alpha, hne]
  have alpha_not_missing_new_u : alpha ∉ MissingColors G phi' u := by
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
    simp [PresentColors]
    exact ⟨eu, heu_incident, heu_new⟩
  have beta_not_missing_new_v : beta ∉ MissingColors G phi' v := by
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
    simp [PresentColors]
    exact ⟨ev, hev_incident, hev_new⟩
  obtain ⟨outside_fixed, alpha_to_beta, beta_to_alpha, unaffected⟩ :=
    TwoColorComponentSwapMissingBehavior G phi alpha beta hne hproper z
  have hu_beta_new : beta ∈ MissingColors G phi' u := alpha_to_beta u huC hua
  have hv_alpha_new : alpha ∈ MissingColors G phi' v := beta_to_alpha v hvC hvb
  intro helementary
  rw [ColoredVertexSetElementary] at hnot helementary
  push_neg at hnot
  obtain ⟨x, hxX, y, hyX, hxy, hxy_not_disjoint⟩ := hnot
  rw [Finset.not_disjoint_iff] at hxy_not_disjoint
  obtain ⟨c, hcx, hcy⟩ := hxy_not_disjoint
  by_cases hca : c = alpha
  · subst c
    by_cases hxC : Sum.inl x ∈ C
    · have hxu : x = u := unique_alpha hxC hcx
      subst x
      by_cases hyC : Sum.inl y ∈ C
      · have hyu : y = u := unique_alpha hyC hcy
        exact hxy hyu.symm
      · have hy_new : alpha ∈ MissingColors G phi' y := by
          rw [outside_fixed y hyC]
          exact hcy
        exact (Finset.disjoint_left.mp
          (helementary hvX hyX (by
            intro hvy
            subst y
            exact hyC hvC))) hv_alpha_new hy_new
    · have hx_new : alpha ∈ MissingColors G phi' x := by
        rw [outside_fixed x hxC]
        exact hcx
      by_cases hyC : Sum.inl y ∈ C
      · have hyu : y = u := unique_alpha hyC hcy
        subst y
        exact (Finset.disjoint_left.mp
          (helementary hxX hvX (by
            intro hxv
            subst x
            exact hxC hvC))) hx_new hv_alpha_new
      · have hy_new : alpha ∈ MissingColors G phi' y := by
          rw [outside_fixed y hyC]
          exact hcy
        exact (Finset.disjoint_left.mp (helementary hxX hyX hxy)) hx_new hy_new
  · by_cases hcb : c = beta
    · subst c
      by_cases hxC : Sum.inl x ∈ C
      · have hxv : x = v := unique_beta hxC hcx
        subst x
        by_cases hyC : Sum.inl y ∈ C
        · have hyv : y = v := unique_beta hyC hcy
          exact hxy hyv.symm
        · have hy_new : beta ∈ MissingColors G phi' y := by
            rw [outside_fixed y hyC]
            exact hcy
          exact (Finset.disjoint_left.mp
            (helementary huX hyX (by
              intro huy
              subst y
              exact hyC huC))) hu_beta_new hy_new
      · have hx_new : beta ∈ MissingColors G phi' x := by
          rw [outside_fixed x hxC]
          exact hcx
        by_cases hyC : Sum.inl y ∈ C
        · have hyv : y = v := unique_beta hyC hcy
          subst y
          exact (Finset.disjoint_left.mp
            (helementary hxX huX (by
              intro hxu
              subst x
              exact hxC huC))) hx_new hu_beta_new
        · have hy_new : beta ∈ MissingColors G phi' y := by
            rw [outside_fixed y hyC]
            exact hcy
          exact (Finset.disjoint_left.mp (helementary hxX hyX hxy)) hx_new hy_new
    · have hcx_new : c ∈ MissingColors G phi' x :=
        (unaffected x c hca hcb).mpr hcx
      have hcy_new : c ∈ MissingColors G phi' y :=
        (unaffected y c hca hcb).mpr hcy
      exact (Finset.disjoint_left.mp (helementary hxX hyX hxy)) hcx_new hcy_new
