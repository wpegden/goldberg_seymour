import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.ScheideDefectiveChainPath
import Tablet.ScheideGlobalMaximumBoundaryFacts
import Tablet.ScheideGlobalMaximumOrder
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: P2968_T1_DefectiveColorComponentPath]
theorem P2968_T1_DefectiveColorComponentPath {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T)
    (alpha gamma : Fin k)
    (halpha : alpha ∈ DefectiveColors G phi (TreeSequenceVertexSet T))
    (u : V) (hu : u ∈ TreeSequenceVertexSet T)
    (hgamma : gamma ∈ MissingColors G phi u) :
    ∃ (z : V)
      (p : (TwoColorIncidenceGraph G phi alpha gamma).Walk
        (Sum.inl u) (Sum.inl z)),
      ScheideDefectiveChainPath T phi alpha gamma u z p := by
-- BODY
  classical
  let X := TreeSequenceVertexSet T
  have hproper : IsProperEdgeColoring G phi := hglobal.1.2.2.2.1
  have horder := ScheideGlobalMaximumOrder G k e0 phi T hglobal
  have helem : ColoredVertexSetElementary G phi X := horder.2.2.2.1
  have hclosed : ColoredVertexSetClosed G phi X := horder.2.2.2.2
  have hfacts := ScheideGlobalMaximumBoundaryFacts G k e0 phi T hglobal
  have hcard : 3 ≤ (BoundaryColorEdges G phi X alpha).card :=
    (hfacts.2.2 alpha halpha).2
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < (BoundaryColorEdges G phi X alpha).card)
  have hb' : b ∈ BoundaryEdges G X ∧ phi b = some alpha := by
    simpa [BoundaryColorEdges] using (Finset.mem_filter.mp hb)
  have halpha_present : ∀ x ∈ X, alpha ∈ PresentColors G phi x := by
    intro x hx
    have hn : alpha ∉ MissingColors G phi x := by
      intro hm
      exact (hclosed hb'.1 hx hb'.2) hm
    simpa [MissingColors] using hn
  have hne : alpha ≠ gamma := by
    intro heq
    have hp := halpha_present u hu
    subst gamma
    have hm : alpha ∉ PresentColors G phi u := by simpa [MissingColors] using hgamma
    exact hm hp
  have huniq : ∀ {v : V} {e f : E}, Incident G v e → Incident G v f →
      phi e = some alpha → phi f = some alpha → e = f := by
    intro v e f he hf hce hcf
    by_contra hne
    exact hproper hne ⟨v, he, hf⟩ hce (by simpa [hcf])
  have ha_u : ∃ e, Incident G u e ∧ phi e = some alpha := by
    simpa [PresentColors] using halpha_present u hu
  obtain ⟨ea, hea, hca⟩ := ha_u
  have hdeg_u : @SimpleGraph.degree _ (TwoColorIncidenceGraph G phi alpha gamma)
      (Sum.inl u) (Fintype.ofFinite _) = 1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have heq : @SimpleGraph.neighborFinset (Sum V E)
        (TwoColorIncidenceGraph G phi alpha gamma) (Sum.inl u) (Fintype.ofFinite _) =
        ({Sum.inr ea} : Finset (Sum V E)) := by
      ext y
      cases y with
      | inl v =>
        simp only [SimpleGraph.mem_neighborFinset]
        simp [TwoColorIncidenceGraph]
      | inr e =>
        simp only [SimpleGraph.mem_neighborFinset]
        constructor
        · intro hy
          have hy' : Incident G u e ∧ (phi e = some alpha ∨ phi e = some gamma) := by
            simpa [TwoColorIncidenceGraph] using hy
          rcases hy'.2 with hα | hγ
          · have : e = ea := huniq hy'.1 hea hα hca
            simp [this]
          · exfalso
            have hm : gamma ∉ PresentColors G phi u := by simpa [MissingColors] using hgamma
            exact hm (by simpa [PresentColors] using ⟨e, hy'.1, hγ⟩)
        · intro hy
          simp only [Finset.mem_singleton] at hy
          injection hy with h
          subst e
          simpa [TwoColorIncidenceGraph] using (show
            Incident G u ea ∧ (phi ea = some alpha ∨ phi ea = some gamma) from
              ⟨hea, Or.inl hca⟩)
    calc
      _ = ({Sum.inr ea} : Finset (Sum V E)).card := congrArg Finset.card heq
      _ = 1 := by simp
  have huniqColor : ∀ (c : Fin k) {v : V} {e f : E}, Incident G v e →
      Incident G v f → phi e = some c → phi f = some c → e = f := by
    intro c v e f he hf hce hcf
    by_contra hne
    exact hproper hne ⟨v, he, hf⟩ hce hcf
  have hdeg_X : ∀ {x : V}, x ∈ X → x ≠ u →
      @SimpleGraph.degree _ (TwoColorIncidenceGraph G phi alpha gamma)
        (Sum.inl x) (Fintype.ofFinite _) = 2 := by
    intro x hx hxu
    have hdis := helem hu hx hxu.symm
    have hgam : gamma ∈ PresentColors G phi x := by
      have hng : gamma ∉ MissingColors G phi x := by
        intro hmx
        exact Finset.disjoint_left.1 hdis hgamma hmx
      simpa [MissingColors] using hng
    obtain ⟨eaX, heaX, hcaX⟩ :=
      (by simpa [PresentColors] using (halpha_present x hx))
    obtain ⟨eg, heg, hcg⟩ := (by simpa [PresentColors] using hgam)
    have hne_edges : eaX ≠ eg := by
      intro heq
      have : phi eaX = some gamma := heq ▸ hcg
      exact hne (Option.some.inj (hcaX.symm.trans this))
    have heq : @SimpleGraph.neighborFinset (Sum V E)
        (TwoColorIncidenceGraph G phi alpha gamma) (Sum.inl x) (Fintype.ofFinite _) =
        ({Sum.inr eaX, Sum.inr eg} : Finset (Sum V E)) := by
      ext y
      cases y with
      | inl v =>
        simp only [SimpleGraph.mem_neighborFinset]
        simp [TwoColorIncidenceGraph]
      | inr e =>
        simp only [SimpleGraph.mem_neighborFinset]
        constructor
        · intro hy
          have hy' : Incident G x e ∧ (phi e = some alpha ∨ phi e = some gamma) := by
            simpa [TwoColorIncidenceGraph] using hy
          rcases hy'.2 with hα | hγ
          · have hh : e = eaX := huniqColor alpha hy'.1 heaX hα hcaX
            simp [hh]
          · have hh : e = eg := huniqColor gamma hy'.1 heg hγ hcg
            simp [hh]
        · intro hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with h | h
          · injection h with h
            subst e
            simpa [TwoColorIncidenceGraph] using
              (show Incident G x eaX ∧ (phi eaX = some alpha ∨ phi eaX = some gamma) from
                ⟨by exact heaX, Or.inl hcaX⟩)
          · injection h with h
            subst e
            simpa [TwoColorIncidenceGraph] using
              (show Incident G x eg ∧ (phi eg = some alpha ∨ phi eg = some gamma) from
                ⟨by exact heg, Or.inr hcg⟩)
    calc
      _ = ({Sum.inr eaX, Sum.inr eg} : Finset (Sum V E)).card := congrArg Finset.card heq
      _ = 2 := by simp [hne_edges]
  obtain ⟨a, b', q, hq, hqs⟩ :=
    TwoColorComponentSpanningPath G phi alpha gamma hproper (Sum.inl u)
  have hcu : Sum.inl u ∈ TwoColorComponent G phi alpha gamma (Sum.inl u) := by
    change Sum.inl u ∈ (TwoColorIncidenceGraph G phi alpha gamma).connectedComponentMk (Sum.inl u)
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr (by rfl)
  have huq : Sum.inl u ∈ q.support := by
    have hh : Sum.inl u ∈ {x | x ∈ q.support} := hqs.symm ▸ hcu
    exact hh
  obtain ⟨i, hiq, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp huq
  have hi_le : i ≤ q.length := hi
  have huvert : q.getVert i = Sum.inl u := hiq
  have hi_end : i = 0 ∨ i = q.length := by
    by_contra hn
    have hi0 : 0 < i := Nat.pos_of_ne_zero (fun h => hn (Or.inl h))
    have hil : i < q.length := by
      exact Nat.lt_of_le_of_ne hi_le (fun h => hn (Or.inr h))
    have hleft : (TwoColorIncidenceGraph G phi alpha gamma).Adj
        (Sum.inl u) (q.getVert (i - 1)) := by
      rw [← huvert]
      have hh := q.adj_getVert_succ (show i - 1 < q.length by omega)
      rw [show i - 1 + 1 = i by omega] at hh
      exact hh.symm
    have hright : (TwoColorIncidenceGraph G phi alpha gamma).Adj
        (Sum.inl u) (q.getVert (i + 1)) := by
      rw [← huvert]
      exact q.adj_getVert_succ hil
    have hne_lr : q.getVert (i - 1) ≠ q.getVert (i + 1) := by
      intro heq
      have := hq.getVert_injOn (show i - 1 ≤ q.length by omega)
        (show i + 1 ≤ q.length by omega) heq
      omega
    have htwo : 2 ≤ @SimpleGraph.degree _
        (TwoColorIncidenceGraph G phi alpha gamma) (Sum.inl u) (Fintype.ofFinite _) := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      let s : Finset (Sum V E) := {q.getVert (i - 1), q.getVert (i + 1)}
      have hs : s ⊆ @SimpleGraph.neighborFinset (Sum V E)
          (TwoColorIncidenceGraph G phi alpha gamma) (Sum.inl u) (Fintype.ofFinite _) := by
        intro y hy
        simp only [s, Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · simpa [SimpleGraph.mem_neighborFinset] using hleft
        · simpa [SimpleGraph.mem_neighborFinset] using hright
      have hc : 2 ≤ s.card := by simp [s, hne_lr]
      exact hc.trans (Finset.card_le_card hs)
    omega
  have hstart : ∃ w, ∃ r : (TwoColorIncidenceGraph G phi alpha gamma).Walk
      (Sum.inl u) w, r.IsPath ∧ {x | x ∈ r.support} =
        TwoColorComponent G phi alpha gamma (Sum.inl u) := by
    rcases hi_end with hi0 | hil
    · have hu0 : q.getVert 0 = Sum.inl u := hi0 ▸ huvert
      have haeq : a = Sum.inl u := q.getVert_zero.symm.trans hu0
      subst a
      exact ⟨b', q, hq, hqs⟩
    · have hb_eq : b' = Sum.inl u := by
        have hh : q.getVert q.length = Sum.inl u := hil ▸ huvert
        exact (q.getVert_length.symm.trans hh)
      subst b'
      refine ⟨a, q.reverse, hq.reverse, ?_⟩
      ext x
      rw [SimpleGraph.Walk.support_reverse]
      simpa [hqs]
  obtain ⟨w, qnew, hqnew, hqsnew⟩ := hstart
  let b' := w
  let q := qnew
  have hq : q.IsPath := hqnew
  have hqs : {x | x ∈ q.support} = TwoColorComponent G phi alpha gamma (Sum.inl u) := hqsnew
  have hfinal : ∃ z p, ScheideDefectiveChainPath T phi alpha gamma u z p := by
    have hadj : (TwoColorIncidenceGraph G phi alpha gamma).Adj (Sum.inl u) (Sum.inr ea) := by
      simpa [TwoColorIncidenceGraph] using (show
        Incident G u ea ∧ (phi ea = some alpha ∨ phi ea = some gamma) from
          ⟨hea, Or.inl hca⟩)
    have hcea : Sum.inr ea ∈ TwoColorComponent G phi alpha gamma (Sum.inl u) := by
      apply (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm
    have hpos : 0 < q.length := by
      by_contra hz
      have : q.length = 0 := Nat.eq_zero_of_not_pos hz
      have hm : Sum.inr ea ∈ {x | x ∈ q.support} := hqs.symm ▸ hcea
      change Sum.inr ea ∈ q.support at hm
      obtain ⟨j, hjget, hjle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hm
      have hjzero : j = 0 := Nat.eq_zero_of_le_zero (this ▸ hjle)
      have heq : Sum.inr ea = Sum.inl u := by
        rw [← hjget, hjzero, q.getVert_zero]
      exact (Sum.inr_ne_inl heq).elim
    have hbne : b' ≠ Sum.inl u := by
      intro he
      have hl : q.getVert q.length = b' := q.getVert_length
      have hz : q.getVert 0 = Sum.inl u := q.getVert_zero
      have hi : q.getVert 0 = q.getVert q.length := hz.trans (he ▸ hl).symm
      have hh := hq.getVert_injOn (show 0 ≤ q.length by omega)
        (show q.length ≤ q.length by rfl) hi
      omega
    have huq' : q.IsPath := hq
    have hfirst : q.getVert 0 = Sum.inl u := q.getVert_zero
    have hlast : q.getVert q.length = b' := q.getVert_length
    have hnotedge : ∀ y, (TwoColorIncidenceGraph G phi alpha gamma).Adj b' y →
        y = q.getVert (q.length - 1) := by
      intro y hy
      have hcb : b' ∈ TwoColorComponent G phi alpha gamma (Sum.inl u) := by
        have hm : b' ∈ {x | x ∈ q.support} := by
          simpa [b'] using q.getVert_mem_support q.length
        exact hqs ▸ hm
      have hcy : y ∈ TwoColorComponent G phi alpha gamma (Sum.inl u) := by
        have heq := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hcb
        apply (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2
        exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hy).symm.trans heq
      have hyset : y ∈ {x | x ∈ q.support} := hqs.symm ▸ hcy
      have hyq : y ∈ q.support := hyset
      obtain ⟨j, hjget, hjle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hyq
      have hjq : q.getVert j = y := hjget
      have hjne : j ≠ q.length := by
        intro he
        have : y = b' := hjq ▸ he ▸ hlast
        exact (by simpa [this] using hy.ne)
      have hjlt : j < q.length := Nat.lt_of_le_of_ne hjle hjne
      by_cases hjend : j + 1 = q.length
      · calc
          y = q.getVert j := hjq.symm
          _ = q.getVert (q.length - 1) := by congr 1; omega
      by_cases hj0 : j = 0
      · by_cases hn1 : q.length = 1
        · have heq : j = q.length - 1 := by omega
          rw [← hjq, heq, hn1]
        · have hq1 : (TwoColorIncidenceGraph G phi alpha gamma).Adj
              (Sum.inl u) (q.getVert 1) := by
            simpa [hfirst] using q.adj_getVert_succ (show 0 < q.length by omega)
          have huunique := (@SimpleGraph.degree_eq_one_iff_existsUnique_adj _
            (TwoColorIncidenceGraph G phi alpha gamma) (Sum.inl u)
            (Fintype.ofFinite _)).mp hdeg_u
          have hyu : (TwoColorIncidenceGraph G phi alpha gamma).Adj
              (Sum.inl u) b' := by
            have hh := hy.symm
            rw [← hjq, hj0, hfirst] at hh
            exact hh
          have heq := huunique.unique hq1 hyu
          have hiq1 : q.getVert 1 ≠ b' := by
            intro hh
            have hxx := hq.getVert_injOn (show 1 ≤ q.length by omega)
              (show q.length ≤ q.length by rfl) (hh.trans hlast.symm)
            omega
          exact (hiq1 heq).elim
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
        have hleft := q.adj_getVert_succ (show j - 1 < q.length by omega)
        rw [show j - 1 + 1 = j by omega] at hleft
        have hright := q.adj_getVert_succ hjlt
        have hthree : 3 ≤ @SimpleGraph.degree _
            (TwoColorIncidenceGraph G phi alpha gamma) (q.getVert j) (Fintype.ofFinite _) := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          let s : Finset (Sum V E) :=
            {b', q.getVert (j - 1), q.getVert (j + 1)}
          have hs : s ⊆ @SimpleGraph.neighborFinset (Sum V E)
              (TwoColorIncidenceGraph G phi alpha gamma) (q.getVert j) (Fintype.ofFinite _) := by
            intro t ht
            simp only [s, Finset.mem_insert, Finset.mem_singleton] at ht
            rcases ht with rfl | rfl | rfl
            · have hh := hy.symm
              rw [← hjq] at hh
              simpa [SimpleGraph.mem_neighborFinset] using hh
            · simpa [SimpleGraph.mem_neighborFinset] using hleft.symm
            · simpa [SimpleGraph.mem_neighborFinset] using hright
          have hdistinct : s.card = 3 := by
            have hbnot : b' ∉ ({q.getVert (j - 1), q.getVert (j + 1)} : Finset (Sum V E)) := by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              intro hh
              rcases hh with hh | hh
              ·
                have heq := hh.symm.trans hlast.symm
                have hidx := hq.getVert_injOn (show j - 1 ≤ q.length by omega)
                  (show q.length ≤ q.length by rfl) heq
                have hidx' : j - 1 = q.length := hidx
                have hbad : q.length ≤ j := by
                  omega
                exact (Nat.not_le_of_gt hjlt) hbad
              ·
                have heq := hh.symm.trans hlast.symm
                have hidx := hq.getVert_injOn (show j + 1 ≤ q.length by omega)
                  (show q.length ≤ q.length by rfl) heq
                have hidx' : j + 1 = q.length := hidx
                exact (hjend hidx').elim
            have hlr : q.getVert (j - 1) ≠ q.getVert (j + 1) := by
              intro hh
              have := hq.getVert_injOn (show j - 1 ≤ q.length by omega)
                (show j + 1 ≤ q.length by omega) hh
              omega
            simp [s, hbnot, hlr]
          calc
            3 = s.card := hdistinct.symm
          _ ≤ _ := Finset.card_le_card hs
        have hup := TwoColorIncidenceDegreeAtMostTwo G phi alpha gamma hproper (q.getVert j)
        omega
    have hlastadj : (TwoColorIncidenceGraph G phi alpha gamma).Adj
          b' (q.getVert (q.length - 1)) := by
      have hh := q.adj_getVert_succ (show q.length - 1 < q.length by omega)
      rw [show q.length - 1 + 1 = q.length by omega, hlast] at hh
      exact hh.symm
    have hend : @SimpleGraph.degree _ (TwoColorIncidenceGraph G phi alpha gamma)
        b' (Fintype.ofFinite _) = 1 := by
      apply (@SimpleGraph.degree_eq_one_iff_existsUnique_adj _
        (TwoColorIncidenceGraph G phi alpha gamma) b' (Fintype.ofFinite _)).mpr
      refine ⟨q.getVert (q.length - 1), hlastadj, ?_⟩
      intro y hy
      exact hnotedge y hy
    have hbvertex : ∃ z : V, b' = Sum.inl z := by
      dsimp [b'] at *
      cases hw : w with
      | inl z => exact ⟨z, rfl⟩
      | inr e =>
        have htwo := TwoColorIncidenceDegreeAtMostTwo G phi alpha gamma hproper (Sum.inr e)
        have hcq : b' ∈ q.support := by
          change w ∈ q.support
          simpa only [hlast] using q.getVert_mem_support q.length
        obtain ⟨j, hsj, hj⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hcq
        have hjpos : 0 < j := by
          by_contra hjz
          have hjzero : j = 0 := Nat.eq_zero_of_not_pos hjz
          have hh := hsj
          rw [hjzero, hfirst] at hh
          exact Sum.inl_ne_inr (hh.trans hw)
        have hprev := q.adj_getVert_succ (show j - 1 < q.length by omega)
        rw [show j - 1 + 1 = j by omega] at hprev
        have hprev2 : (TwoColorIncidenceGraph G phi alpha gamma).Adj
            (q.getVert (j - 1)) (Sum.inr e) := by
          simpa [b', hsj, hw] using hprev
        have hinc : ∃ z, Incident G z e ∧
            (phi e = some alpha ∨ phi e = some gamma) := by
          cases hp : q.getVert (j - 1) with
          | inl z =>
            have htemp := hprev2
            rw [hp] at htemp
            exact ⟨z, by simpa [TwoColorIncidenceGraph] using htemp⟩
          | inr f =>
            have htemp := hprev2
            rw [hp] at htemp
            simp [TwoColorIncidenceGraph] at htemp
        obtain ⟨z₁, hz₁, hcol⟩ := hinc
        let p₁ := (Quot.out (G.ends e)).1
        let p₂ := (Quot.out (G.ends e)).2
        have heends : s(p₁, p₂) = G.ends e := Quot.out_eq _
        have hp₁ : Incident G p₁ e := by
          change p₁ ∈ G.ends e
          rw [← heends]
          simpa [p₁, p₂] using Sym2.out_fst_mem (G.ends e)
        have hp₂ : Incident G p₂ e := by
          change p₂ ∈ G.ends e
          rw [← heends]
          simpa [p₁, p₂] using Sym2.out_snd_mem (G.ends e)
        have hpne : p₁ ≠ p₂ := by
          intro he
          apply G.loopless e p₁
          rw [← heends, he]
        have ha₁ : (TwoColorIncidenceGraph G phi alpha gamma).Adj
            (Sum.inr e) (Sum.inl p₁) := by
          simpa [TwoColorIncidenceGraph] using (show
            Incident G p₁ e ∧ (phi e = some alpha ∨ phi e = some gamma) from
              ⟨hp₁, hcol⟩)
        have ha₂ : (TwoColorIncidenceGraph G phi alpha gamma).Adj
            (Sum.inr e) (Sum.inl p₂) := by
          simpa [TwoColorIncidenceGraph] using (show
            Incident G p₂ e ∧ (phi e = some alpha ∨ phi e = some gamma) from
              ⟨hp₂, hcol⟩)
        have hlow : 2 ≤ @SimpleGraph.degree _
            (TwoColorIncidenceGraph G phi alpha gamma) (Sum.inr e) (Fintype.ofFinite _) := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          let s : Finset (Sum V E) := {Sum.inl p₁, Sum.inl p₂}
          have hs : s ⊆ @SimpleGraph.neighborFinset (Sum V E)
              (TwoColorIncidenceGraph G phi alpha gamma) (Sum.inr e) (Fintype.ofFinite _) := by
            intro t ht
            simp only [s, Finset.mem_insert, Finset.mem_singleton] at ht
            rcases ht with rfl | rfl
            · simpa [SimpleGraph.mem_neighborFinset] using ha₁
            · simpa [SimpleGraph.mem_neighborFinset] using ha₂
          have hsiz : 2 ≤ s.card := by simp [s, hpne]
          exact hsiz.trans (Finset.card_le_card hs)
        have hone : @SimpleGraph.degree _
            (TwoColorIncidenceGraph G phi alpha gamma) (Sum.inr e) (Fintype.ofFinite _) = 1 := by
          subst w
          exact hend
        omega
    obtain ⟨z, hz⟩ := hbvertex
    have hzout : z ∉ X := by
      intro hzX
      by_cases hzu : z = u
      · exact hbne (by simpa [hz, hzu])
      · have := hdeg_X hzX hzu
        have hone : @SimpleGraph.degree _
            (TwoColorIncidenceGraph G phi alpha gamma) (Sum.inl z) (Fintype.ofFinite _) = 1 := by
          have hh := hend
          rw [hz] at hh
          exact hh
        omega
    have hzq : w = Sum.inl z := hz
    subst w
    exact ⟨z, q, ⟨hu, hq, hzout, by
      ext x
      exact Set.ext_iff.mp hqs x⟩⟩
  exact hfinal
