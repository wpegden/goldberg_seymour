import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.ScheideDefectiveChainPath
import Tablet.ScheideDefectiveChainPathExists
import Tablet.ScheideGlobalMaximumBoundaryFacts
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideGlobalMaximumUnused
import Tablet.TashkinovOrder
import Tablet.TashkinovTree
import Tablet.TreeFreeColors
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TreeUsedColors
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceGraph

-- [TABLET NODE: ScheideDefectiveChainBoundaryEdges]
theorem ScheideDefectiveChainBoundaryEdges {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T)
    (alpha gamma : Fin k)
    (halpha : alpha ∈ DefectiveColors G phi (TreeSequenceVertexSet T))
    (hgammaFree : gamma ∈ TreeFreeColors phi T)
    (u : V) (hu : u ∈ TreeSequenceVertexSet T)
    (hgamma : gamma ∈ MissingColors G phi u)
    (z : V)
    (p : (TwoColorIncidenceGraph G phi alpha gamma).Walk
      (Sum.inl u) (Sum.inl z))
    (hp : ScheideDefectiveChainPath T phi alpha gamma u z p) :
    ∀ f : E,
      f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) alpha ↔
        f ∈ BoundaryEdges G (TreeSequenceVertexSet T) ∧
          Sum.inr f ∈ p.support := by
-- BODY
  set_option maxHeartbeats 800000 in
    classical
    have horder := ScheideGlobalMaximumOrder G k e0 phi T hglobal
    have hfacts := ScheideGlobalMaximumBoundaryFacts G k e0 phi T hglobal
    have hunused := ScheideGlobalMaximumUnused G k e0 phi T hglobal
    intro f
    simp only [BoundaryColorEdges, Finset.mem_filter]
    constructor
    · intro h
      refine ⟨h.1, ?_⟩
      by_contra hnot
      have htreegamma : gamma ∈ TreeMissingColors phi T := by
        simp [TreeMissingColors]
        exact ⟨u, hu, hgamma⟩
      have hgammaempty := hfacts.2.1 gamma htreegamma
      have hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) :=
        horder.2.2.2.2
      have hne : alpha ≠ gamma := by
        intro heq
        have ha : alpha ∉ MissingColors G phi u := by
          exact hclosed h.1 hu h.2
        exact ha (heq ▸ hgamma)
      let Q := TwoColorComponent G phi alpha gamma (Sum.inr f)
      let psi := TwoColorComponentSwap G phi alpha gamma (Sum.inr f)
      have hfQ : Sum.inr f ∈ Q := by
        change (TwoColorIncidenceGraph G phi alpha gamma).connectedComponentMk
          (Sum.inr f) = (TwoColorIncidenceGraph G phi alpha gamma).connectedComponentMk
          (Sum.inr f)
        rfl
      have huQ : Sum.inl u ∉ Q := by
        intro huq
        have huf : Sum.inl u ∈ TwoColorComponent G phi alpha gamma (Sum.inr f) := huq
        have huf' : Sum.inr f ∈ TwoColorComponent G phi alpha gamma (Sum.inl u) := by
          change (TwoColorIncidenceGraph G phi alpha gamma).connectedComponentMk
              (Sum.inr f) = (TwoColorIncidenceGraph G phi alpha gamma).connectedComponentMk
              (Sum.inl u)
          exact huf.symm
        have hps : Sum.inr f ∈ p.support := by
          have hh : Sum.inr f ∈ {x | x ∈ p.support} := by
            rw [hp.2.2.2]
            exact huf'
          exact hh
        exact hnot hps
      have qcolor : ∀ e, Sum.inr e ∈ Q →
          phi e = some alpha ∨ phi e = some gamma := by
        intro e he
        by_cases hef : e = f
        · exact Or.inl (by simpa [hef] using h.2)
        · have hs : Sum.inr e ∈
              (TwoColorIncidenceGraph G phi alpha gamma).support := by
            apply SimpleGraph.mem_support_of_reachable
            · intro hh
              apply hef
              exact Sum.inr.inj hh
            · change (TwoColorIncidenceGraph G phi alpha gamma).connectedComponentMk
                (Sum.inr e) = (TwoColorIncidenceGraph G phi alpha gamma).connectedComponentMk
                (Sum.inr f) at he
              exact SimpleGraph.ConnectedComponent.eq.mp he
          obtain ⟨w, hw⟩ := (TwoColorIncidenceGraph G phi alpha gamma).mem_support.mp hs
          cases w with
          | inl v => exact hw.2
          | inr e' => simpa [TwoColorIncidenceGraph] using hw
      have qvertex : ∀ v e, Incident G v e → Sum.inr e ∈ Q →
          Sum.inl v ∈ Q := by
        intro v e hev he
        have hc := qcolor e he
        have hadj : (TwoColorIncidenceGraph G phi alpha gamma).Adj
            (Sum.inl v) (Sum.inr e) := by
          simp [TwoColorIncidenceGraph, hev, hc]
        change (TwoColorIncidenceGraph G phi alpha gamma).connectedComponentMk
            (Sum.inl v) = (TwoColorIncidenceGraph G phi alpha gamma).connectedComponentMk
            (Sum.inr f)
        exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans he
      have qedge_not : ∀ v e, Incident G v e → Sum.inl v ∉ Q →
          Sum.inr e ∉ Q := by
        intro v e hev hv he
        exact hv (qvertex v e hev he)
      have halpha_present : ∀ v, v ∈ TreeSequenceVertexSet T →
          alpha ∈ PresentColors G phi v := by
        intro v hv
        have hn : alpha ∉ MissingColors G phi v := by
          exact hclosed h.1 hv h.2
        simpa [MissingColors] using hn
      have hgamma_present : ∀ v, v ∈ TreeSequenceVertexSet T → v ≠ u →
          gamma ∈ PresentColors G phi v := by
        intro v hv hnevu
        have helem := horder.2.2.2.1 hu hv hnevu.symm
        have hn : gamma ∉ MissingColors G phi v := by
          intro hm
          exact Finset.disjoint_left.mp helem hgamma hm
        simpa [MissingColors] using hn
      have qedge_of_vertex : ∀ v e, Sum.inl v ∈ Q → Incident G v e →
          (phi e = some alpha ∨ phi e = some gamma) → Sum.inr e ∈ Q := by
        intro v e hv hev hc
        change (TwoColorIncidenceGraph G phi alpha gamma).connectedComponentMk
            (Sum.inr e) = (TwoColorIncidenceGraph G phi alpha gamma).connectedComponentMk
            (Sum.inr f)
        apply (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj ?_).trans hv
        simp [TwoColorIncidenceGraph, hev, hc]
      have present_eq : ∀ v, v ∈ TreeSequenceVertexSet T →
          PresentColors G psi v = PresentColors G phi v := by
        intro v hv
        have vnot : Sum.inl v ∉ Q ∨ v ≠ u := by
          by_cases hvq : Sum.inl v ∈ Q
          · right
            intro hvu
            exact huQ (hvu ▸ hvq)
          · exact Or.inl hvq
        ext c
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨e, hev, hec⟩
          by_cases heq : Sum.inr e ∈ Q
          · have hce : phi e = some alpha ∨ phi e = some gamma := qcolor e heq
            rcases hce with hca | hcg
            · have hvne : v ≠ u := by
                intro hvu
                exact huQ (hvu ▸ qvertex v e hev heq)
              have hgp : gamma ∈ PresentColors G phi v :=
                hgamma_present v hv hvne
              obtain ⟨g, hgv, hgc⟩ := by simpa [PresentColors] using hgp
              have hc : c = gamma := by
                apply Option.some.inj
                simpa [psi, Q, TwoColorComponentSwap, heq, hca, hne, hne.symm] using hec.symm
              subst c
              refine ⟨g, hgv, ?_⟩
              have hgq := qedge_of_vertex v g (qvertex v e hev heq) hgv (Or.inr hgc)
              simpa [hgq, psi, Q, TwoColorComponentSwap, hgc, hne] using hgc
            · have hap := halpha_present v hv
              obtain ⟨a, hav, hac⟩ := by simpa [PresentColors] using hap
              have hc : c = alpha := by
                apply Option.some.inj
                simpa [psi, Q, TwoColorComponentSwap, heq, hcg, hne, hne.symm] using hec.symm
              subst c
              refine ⟨a, hav, ?_⟩
              have haq := qedge_of_vertex v a (qvertex v e hev heq) hav (Or.inl hac)
              simpa [haq, psi, Q, TwoColorComponentSwap, hac, hne, hne.symm] using hac
          · refine ⟨e, hev, ?_⟩
            simpa [psi, Q, TwoColorComponentSwap, heq] using hec
        · rintro ⟨e, hev, hec⟩
          by_cases heq : Sum.inr e ∈ Q
          · have hce : phi e = some alpha ∨ phi e = some gamma := qcolor e heq
            rcases hce with hca | hcg
            · have hvne : v ≠ u := by
                intro hvu
                exact huQ (hvu ▸ qvertex v e hev heq)
              have hgp := hgamma_present v hv hvne
              obtain ⟨g, hgv, hgc⟩ := by simpa [PresentColors] using hgp
              have hc : c = alpha := Option.some.inj (hec.symm.trans hca)
              subst c
              refine ⟨g, hgv, ?_⟩
              have hgq : Sum.inr g ∈ Q :=
                qedge_of_vertex v g (qvertex v e hev heq) hgv (Or.inr hgc)
              simpa [hgq, psi, Q, TwoColorComponentSwap, hgc, hne] using hgc
            · have hap := halpha_present v hv
              obtain ⟨a, hav, hac⟩ := by simpa [PresentColors] using hap
              have hc : c = gamma := Option.some.inj (hec.symm.trans hcg)
              subst c
              refine ⟨a, hav, ?_⟩
              have haq := qedge_of_vertex v a (qvertex v e hev heq) hav (Or.inl hac)
              simpa [haq, psi, Q, TwoColorComponentSwap, hac, hne, hne.symm] using hac
          · refine ⟨e, hev, ?_⟩
            simpa [psi, Q, TwoColorComponentSwap, heq] using hec
      have missing_eq : ∀ v, v ∈ TreeSequenceVertexSet T →
          MissingColors G psi v = MissingColors G phi v := by
        intro v hv
        simp [MissingColors, present_eq v hv]
      have proper_psi : IsProperEdgeColoring G psi := by
        exact TwoColorComponentSwapProper G phi alpha gamma hne
          hglobal.1.2.2.2.1 (Sum.inr f)
      have one : IsOneEdgeUncolored phi e0 := hglobal.1.2.2.2.2
      have e0not : Sum.inr e0 ∉ Q := by
        intro he
        rcases qcolor e0 he with hc | hc <;> simp [one.1] at hc
      have one_psi : IsOneEdgeUncolored psi e0 := by
        refine ⟨?_, ?_⟩
        · simpa [psi, Q, TwoColorComponentSwap, e0not] using one.1
        · intro e he
          obtain ⟨c, hc⟩ := one.2 e he
          by_cases hqe : Sum.inr e ∈ Q
          · rcases qcolor e hqe with hα | hγ
            · refine ⟨gamma, ?_⟩
              simp [psi, Q, TwoColorComponentSwap, hqe, hα, hne]
            · refine ⟨alpha, ?_⟩
              simp [psi, Q, TwoColorComponentSwap, hqe, hγ, hne, hne.symm]
          · refine ⟨c, ?_⟩
            simpa [psi, Q, TwoColorComponentSwap, hqe] using hc
      have tree_fixed : ∀ j : Fin T.length, psi (T.edge j) = phi (T.edge j) := by
        intro j
        by_cases hj : j.val = 0
        · have hje : j = ⟨0, T.positive⟩ := by apply Fin.ext; exact hj
          subst j
          rw [T.first_edge]
          simp [one.1, e0not, psi, Q, TwoColorComponentSwap]
        · by_cases hqe : Sum.inr (T.edge j) ∈ Q
          · rcases qcolor (T.edge j) hqe with hα | hγ
            · have hused : alpha ∈ TreeUsedColors phi T := by
                simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨j, by omega, hα⟩
              exact False.elim ((Finset.disjoint_left.mp hunused.1 halpha) hused)
            · have hused : gamma ∈ TreeUsedColors phi T := by
                simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨j, by omega, hγ⟩
              exact False.elim ((Finset.disjoint_left.mp hunused.2 hgammaFree) hused)
          · simpa [psi, Q, TwoColorComponentSwap, hqe]
      obtain ⟨x, hx, y, hy, hends⟩ := by
        simpa [BoundaryEdges] using h.1
      have vertex_mem : ∀ i : Fin (T.length + 1),
          T.vertex i ∈ TreeSequenceVertexSet T := by
        intro i
        simp [TreeSequenceVertexSet]
      have fnew : ∀ j : Fin T.length, f ≠ T.edge j := by
        intro j heq
        obtain ⟨i, hi⟩ := T.attaches j
        have hyend : y ∈ G.ends (T.edge j) := by
          rw [← heq, hends]
          exact Sym2.mem_iff.mpr (Or.inr rfl)
        rw [hi] at hyend
        rcases Sym2.mem_iff.mp hyend with hvv | hvv
        · exact hy (hvv ▸ vertex_mem j.succ)
        · exact hy (hvv ▸ vertex_mem (Fin.castLT i (by omega)))
      let Tplus : TreeSequence G e0 :=
        { length := T.length + 1
          positive := by omega
          vertex := Fin.lastCases y (fun i => T.vertex i)
          edge := Fin.lastCases f (fun i => T.edge i)
          vertex_injective := by
            intro i j
            revert j
            refine Fin.lastCases ?_ (fun i => ?_) i
            · intro j
              refine Fin.lastCases ?_ (fun j => ?_) j
              · intro hij; rfl
              · intro hij
                dsimp only [Fin.lastCases] at hij
                rw [Fin.reverseInduction_last, Fin.reverseInduction_castSucc] at hij
                exact (hy (hij ▸ vertex_mem j)).elim
            · intro j
              refine Fin.lastCases ?_ (fun j => ?_) j
              · intro hij
                dsimp only [Fin.lastCases] at hij
                rw [Fin.reverseInduction_castSucc, Fin.reverseInduction_last] at hij
                exact (hy (hij ▸ vertex_mem i)).elim
              · intro hij
                dsimp only [Fin.lastCases] at hij
                rw [Fin.reverseInduction_castSucc, Fin.reverseInduction_castSucc] at hij
                exact congrArg Fin.castSucc (T.vertex_injective hij)
          edge_injective := by
            intro i j
            revert j
            refine Fin.lastCases ?_ (fun i => ?_) i
            · intro j
              refine Fin.lastCases ?_ (fun j => ?_) j
              · intro hij; rfl
              · intro hij
                dsimp only [Fin.lastCases] at hij
                rw [Fin.reverseInduction_last, Fin.reverseInduction_castSucc] at hij
                exact (fnew j hij).elim
            · intro j
              refine Fin.lastCases ?_ (fun j => ?_) j
              · intro hij
                dsimp only [Fin.lastCases] at hij
                rw [Fin.reverseInduction_castSucc, Fin.reverseInduction_last] at hij
                exact (fnew i hij.symm).elim
              · intro hij
                dsimp only [Fin.lastCases] at hij
                rw [Fin.reverseInduction_castSucc, Fin.reverseInduction_castSucc] at hij
                exact congrArg Fin.castSucc (T.edge_injective hij)
          first_edge := by
            have hz : (⟨0, Nat.succ_pos _⟩ : Fin (T.length + 1)) =
                (⟨0, T.positive⟩ : Fin T.length).castSucc := by rfl
            rw [hz]
            simp only [Fin.lastCases, Fin.reverseInduction_castSucc]
            exact T.first_edge
          attaches := by
            intro j
            by_cases hj : j = Fin.last T.length
            · subst j
              obtain ⟨i, hi⟩ := by simpa [TreeSequenceVertexSet] using hx
              refine ⟨i, ?_⟩
              have hc : (Fin.castLT i (by omega) : Fin (T.length + 1 + 1)) = i.castSucc := by
                apply Fin.ext; rfl
              rw [hc]
              simp [Fin.lastCases, Fin.reverseInduction_last, Fin.reverseInduction_castSucc]
              rw [hends, ← hi]
              exact (Sym2.eq_iff).2 (Or.inr ⟨rfl, rfl⟩)
            · have hjle : j.val ≤ T.length := Nat.lt_succ_iff.mp j.isLt
              have hjne : j.val ≠ T.length := by
                intro heq; apply hj; apply Fin.ext; simpa using heq
              have hj' : j.val < T.length := Nat.lt_of_le_of_ne hjle hjne
              obtain ⟨i, hi⟩ := T.attaches (j.castPred hj)
              have hjform : j = (j.castPred hj).castSucc := by apply Fin.ext; rfl
              have hji : (j.castPred hj).val + 1 ≤ j.val + 1 := by
                rw [show (j.castPred hj).val = j.val by rfl]
              refine ⟨Fin.castLE hji i, ?_⟩
              convert hi using 1
              · apply congrArg G.ends
                conv_lhs => rw [hjform]
                simp only [Fin.lastCases, Fin.reverseInduction_castSucc]
              · apply (Sym2.eq_iff).2
                left
                constructor
                · have hjs : j.succ = (j.castPred hj).succ.castSucc := by apply Fin.ext; rfl
                  rw [hjs]
                  simp only [Fin.lastCases, Fin.reverseInduction_castSucc]
                · have hi' : i.val < T.length + 1 := by omega
                  have hq : (Fin.castLE hji i).castLT (by omega) =
                      (i.castLT hi').castSucc := by apply Fin.ext; rfl
                  rw [hq]
                  simp only [Fin.lastCases, Fin.reverseInduction_castSucc] }
      have hTash : TashkinovTree G e0 psi Tplus := by
        intro j
        revert j
        refine Fin.lastCases ?_ (fun q => ?_)
        · intro hj
          obtain ⟨i, hi⟩ := by simpa [TreeSequenceVertexSet] using hu
          have hi_lt := i.isLt
          refine ⟨i, ?_⟩
          refine ⟨gamma, ?_, ?_⟩
          · simp [Tplus, psi, Q, TwoColorComponentSwap, hfQ, h.2, hne]
          · have hiold : i.val < T.length + 1 := by omega
            have hb : i.val < T.length + 1 + 1 := by omega
            have hii : Tplus.vertex (Fin.castLT i hb) =
                T.vertex (i.castLT hiold) := by
              have heq : (Fin.castLT i hb : Fin (T.length + 1 + 1)) =
                  (i.castLT hiold).castSucc := by apply Fin.ext; rfl
              rw [heq]
              simp [Tplus]
            have hmu : MissingColors G psi
                (Tplus.vertex (Fin.castLT i hb)) =
                MissingColors G phi u := by
              rw [hii]
              rw [missing_eq _ (by simpa [TreeSequenceVertexSet] using hu)]
              exact congrArg (MissingColors G phi) hi
            exact hmu.symm ▸ hgamma
        · intro hj
          have hqbound : q.val < T.length := by simpa [Tplus] using q.isLt
          have hq : 1 ≤ q.val := by
            simpa [Fin.lastCases] using hj
          obtain ⟨i, c, hc, hcm⟩ := hglobal.2.1 q hq
          refine ⟨i, c, ?_, ?_⟩
          · simpa [Tplus, Fin.lastCases, Fin.reverseInduction_castSucc] using
              (tree_fixed q ▸ hc)
          · have hiX : T.vertex (i.castLT (by omega)) ∈ TreeSequenceVertexSet T := by
              have hi_lt := i.isLt
              simp [TreeSequenceVertexSet]
            have hmi := missing_eq _ hiX
            have hiold : i.val < T.length + 1 := by omega
            have hb : i.val < T.length + 1 + 1 := by omega
            have hiv : Tplus.vertex (Fin.castLT i hb) =
                T.vertex (i.castLT hiold) := by
              have heq : (Fin.castLT i hb : Fin (T.length + 1 + 1)) =
                  (i.castLT hiold).castSucc := by apply Fin.ext; rfl
              rw [heq]
              simp [Tplus]
            rw [hiv, hmi]
            exact hcm
      have hK : KTriple G k e0 psi := by
        refine ⟨hglobal.1.1, hglobal.1.2.1, hglobal.1.2.2.1, proper_psi, one_psi⟩
      have hsizeplus : (TreeSequenceVertexSet Tplus).card = Tplus.length + 1 := by
        simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
          Tplus.vertex_injective]
      have hchi : ChromaticIndex G = k + 1 := hglobal.1.2.1
      have hk : ChromaticIndex G - 1 = k := by omega
      have hk0 : k = ChromaticIndex G - 1 := hk.symm
      subst k
      have hmemorder : Tplus.length + 1 ∈
          (Finset.range (Fintype.card V + 1)).filter (fun n =>
            ∃ (e0' : E) (phi' : PartialEdgeColoring E (ChromaticIndex G - 1))
              (S : TreeSequence G e0'),
              KTriple G (ChromaticIndex G - 1) e0' phi' ∧
                TashkinovTree G e0' phi' S ∧
                (TreeSequenceVertexSet S).card = n) := by
        apply Finset.mem_filter.mpr
        constructor
        · have hh := Fintype.card_le_of_injective Tplus.vertex Tplus.vertex_injective
          have hh' : Tplus.length + 1 ≤ Fintype.card V := by simpa using hh
          have hlen : Tplus.length = T.length + 1 := rfl
          have hfin : Fintype.card (Fin (Tplus.length + 1)) = Tplus.length + 1 :=
            Fintype.card_fin _
          simpa using Nat.lt_succ_of_le hh'
        · refine ⟨e0, psi, Tplus, ?_⟩
          simpa using ⟨hK, hTash, hsizeplus⟩
      have hle := Finset.le_max' (insert 0
          ((Finset.range (Fintype.card V + 1)).filter (fun n =>
            ∃ (e0' : E) (phi' : PartialEdgeColoring E (ChromaticIndex G - 1))
              (S : TreeSequence G e0'),
              KTriple G (ChromaticIndex G - 1) e0' phi' ∧
                TashkinovTree G e0' phi' S ∧
                (TreeSequenceVertexSet S).card = n)))
          (Tplus.length + 1) (Finset.mem_insert_of_mem hmemorder)
      change Tplus.length + 1 ≤ TashkinovOrder G at hle
      rw [horder.1] at hle
      have hsizeold : (TreeSequenceVertexSet T).card = T.length + 1 := by
        simp [TreeSequenceVertexSet, Finset.card_image_of_injective, T.vertex_injective]
      have hlen : Tplus.length = T.length + 1 := rfl
      exact False.elim (by omega)
    · intro h
      have left_7 : f ∈ BoundaryEdges G (TreeSequenceVertexSet T) := h.1
      have right_3 : Sum.inr f ∈ p.support := h.2
      have htreegamma : gamma ∈ TreeMissingColors phi T := by
        simp [TreeMissingColors]
        exact ⟨u, hu, hgamma⟩
      have hgammaempty := hfacts.2.1 gamma htreegamma
      have hnalpha : phi f = some alpha ∨ phi f = some gamma := by
        obtain ⟨n, hn, hnl⟩ :=
          SimpleGraph.Walk.mem_support_iff_exists_getVert.mp right_3
        have hn0 : 0 < n := by
          by_contra hh
          have he : n = 0 := by omega
          subst he
          simp at hn
        have hnlast : n < p.length := by
          by_contra hh
          have he := p.getVert_of_length_le (i := n) (by omega)
          rw [hn] at he
          simp at he
        have hadj := p.adj_getVert_succ (i := n - 1) (by omega)
        have hidx : n - 1 + 1 = n := by omega
        rw [hidx, hn] at hadj
        cases hprev : p.getVert (n - 1) with
        | inl v =>
            rw [hprev] at hadj
            simp [TwoColorIncidenceGraph] at hadj
            exact hadj.2
        | inr e =>
            rw [hprev] at hadj
            simp [TwoColorIncidenceGraph] at hadj
      rcases hnalpha with hfa | hfg
      · exact ⟨left_7, hfa⟩
      · exfalso
        have hbad : f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) gamma := by
          simpa [BoundaryColorEdges] using (show
            f ∈ BoundaryEdges G (TreeSequenceVertexSet T) ∧ phi f = some gamma
            from ⟨left_7, hfg⟩)
        rw [hgammaempty] at hbad
        simpa using hbad
