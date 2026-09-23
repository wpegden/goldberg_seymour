import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetElementary
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.NormalGlobalMaximumTriple
import Tablet.NormalTripleTrunk
import Tablet.PresentColors
import Tablet.ScheideBalancedCandidate
import Tablet.TashTree
import Tablet.TashkinovOrder
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceBoundaryEdgeAppendExists
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet
import Tablet.TreeUsedColors

set_option maxHeartbeats 400000

-- [TABLET NODE: ScheideBalancedCandidateMaximumOrder]
theorem ScheideBalancedCandidateMaximumOrder {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T S : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hS : ScheideBalancedCandidate N S)
    (hmax : ∀ R : TreeSequence G e0, ScheideBalancedCandidate N R →
      (TreeSequenceVertexSet R).card ≤
        (TreeSequenceVertexSet S).card) :
    (TreeSequenceVertexSet S).card = TashkinovOrder G := by
-- BODY
  classical
  have htriple : KTriple G k e0 phi := N.global.1
  have hk : ChromaticIndex G - 1 = k := by
    have hchrom := htriple.2.1
    omega
  have hSle : (TreeSequenceVertexSet S).card ≤ TashkinovOrder G := by
    unfold TashkinovOrder
    dsimp only
    apply Finset.le_max'
    apply Finset.mem_insert_of_mem
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ _))
    · rw [hk]
      exact ⟨e0, phi, S, htriple, hS.tashkinov, rfl⟩
  apply Nat.le_antisymm hSle
  by_contra hnot
  have hltOrder : (TreeSequenceVertexSet S).card < TashkinovOrder G :=
    Nat.lt_of_not_ge hnot
  have hlt : (TreeSequenceVertexSet S).card <
      (TreeSequenceVertexSet T).card := by
    simpa [N.global.2.2] using hltOrder
  let X := TreeSequenceVertexSet S
  have firstVertices : ∀ j : Fin 2,
      T.vertex (Fin.castLE (Nat.succ_le_succ T.positive) j) ∈ X := by
    intro j
    obtain ⟨it, ht⟩ := T.attaches ⟨0, T.positive⟩
    obtain ⟨is, hs⟩ := S.attaches ⟨0, S.positive⟩
    have itzero : it = 0 := Fin.eq_zero it
    have iszero : is = 0 := Fin.eq_zero is
    subst it
    subst is
    rw [T.first_edge] at ht
    rw [S.first_edge] at hs
    have hm : T.vertex (Fin.castLE (Nat.succ_le_succ T.positive) j) ∈
        G.ends e0 := by
      have cases : j.val = 0 ∨ j.val = 1 := by omega
      rcases cases with hzero | hone
      · have hj : j = 0 := Fin.ext hzero
        subst j
        rw [ht]
        exact Sym2.mem_iff.mpr (Or.inr rfl)
      · have hj : j = 1 := Fin.ext hone
        subst j
        rw [ht]
        exact Sym2.mem_iff.mpr (Or.inl rfl)
    rw [hs] at hm
    rcases Sym2.mem_iff.mp hm with hm | hm
    · simpa [X, TreeSequenceVertexSet] using
        (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, hm.symm⟩)
    · simpa [X, TreeSequenceVertexSet] using
        (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, hm.symm⟩)
  have omitted : ∃ n : ℕ, ∃ hn : n < T.length + 1,
      T.vertex ⟨n, hn⟩ ∉ X := by
    by_contra hn
    push_neg at hn
    have hsub : TreeSequenceVertexSet T ⊆ X := by
      intro v hv
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp
        (show v ∈ Finset.image T.vertex Finset.univ from by
          simpa [TreeSequenceVertexSet] using hv)
      exact hn j.val j.isLt
    have hcard := Finset.card_le_card hsub
    exact (Nat.not_le_of_gt hlt) (by simpa [X] using hcard)
  let n : ℕ := Nat.find omitted
  have hnlt : n < T.length + 1 := (Nat.find_spec omitted).1
  have hnout : T.vertex ⟨n, hnlt⟩ ∉ X := (Nat.find_spec omitted).2
  have hnlarge : 2 ≤ n := by
    by_contra hh
    have hcases : n = 0 ∨ n = 1 := by omega
    rcases hcases with hzero | hone
    · apply hnout
      simpa [hzero] using firstVertices ⟨0, by omega⟩
    · apply hnout
      have hv := firstVertices ⟨1, by omega⟩
      have hi : (⟨n, hnlt⟩ : Fin (T.length + 1)) =
          Fin.castLE (Nat.succ_le_succ T.positive) ⟨1, by omega⟩ := by
        apply Fin.ext
        simp [hone]
      rw [hi]
      exact hv
  let q : Fin T.length := ⟨n - 1, by omega⟩
  have hqrel : q.val + 1 = n := by
    simp [q, Nat.sub_add_cancel (by omega : 1 ≤ n)]
  have hqout : T.vertex q.succ ∉ X := by
    have hidx : q.succ = ⟨n, hnlt⟩ := Fin.ext (by simp [hqrel])
    rw [hidx]
    exact hnout
  have prior : ∀ (i : Fin (q.val + 1)),
      T.vertex (Fin.castLT i
        (Nat.lt_trans i.isLt (Nat.succ_lt_succ q.isLt))) ∈ X := by
    intro i
    by_contra hout
    have hprop : ∃ hi : i.val < T.length + 1,
        T.vertex ⟨i.val, hi⟩ ∉ X :=
      ⟨by omega, by
        intro hm
        apply hout
        convert hm using 1
        apply congrArg T.vertex
        apply Fin.ext
        rfl⟩
    have hmin : n ≤ i.val := Nat.find_min' omitted hprop
    omega
  obtain ⟨a, gamma, hqcolor, hagamma⟩ :=
    N.global.2.1 q (by simp [q]; omega)
  have haX := prior a
  obtain ⟨s, -, hsa⟩ := Finset.mem_image.mp
    (show T.vertex (Fin.castLT a
        (Nat.lt_trans a.isLt (Nat.succ_lt_succ q.isLt))) ∈
        Finset.image S.vertex Finset.univ from by
      simpa [X, TreeSequenceVertexSet] using haX)
  obtain ⟨b, hqb⟩ := T.attaches q
  have hbX := prior b
  have hboundary : T.edge q ∈ BoundaryEdges G X := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨T.vertex (Fin.castLT b
        (Nat.lt_trans b.isLt (Nat.succ_lt_succ q.isLt))), hbX,
      T.vertex q.succ, hqout, ?_⟩
    rw [hqb]
    exact Sym2.eq_swap
  obtain ⟨Splus, hAdjoinPlus⟩ :=
    TreeSequenceBoundaryEdgeAppendExists S (T.edge q) hboundary
  rcases hAdjoinPlus with ⟨hPlusLen, hSPlusInit, hPlusLast⟩
  have hPlusVertex (i : Fin (S.length + 1)) :
      Splus.vertex (Fin.castLE (Nat.succ_le_succ hSPlusInit.1) i) =
        S.vertex i := hSPlusInit.2.1 i
  have hPlusEdge (j : Fin S.length) :
      Splus.edge (Fin.castLE hSPlusInit.1 j) = S.edge j :=
    hSPlusInit.2.2 j
  have hPlusTash : TashkinovTree G e0 phi Splus := by
    intro j hj
    by_cases hlast : j.val = S.length
    · have hjlast : j = Fin.cast hPlusLen.symm (Fin.last S.length) := by
        apply Fin.ext
        simpa [hlast]
      let ss : Fin (j.val + 1) := ⟨s.val, by simpa [hlast] using s.isLt⟩
      refine ⟨ss, gamma, ?_, ?_⟩
      · rw [hjlast, hPlusLast, hqcolor]
      · have hcast : Fin.castLT ss
          (Nat.lt_trans ss.isLt (Nat.succ_lt_succ j.isLt)) =
          Fin.castLE (Nat.succ_le_succ hSPlusInit.1) s := by
          apply Fin.ext
          simp [ss]
        rw [hcast, hPlusVertex, hsa]
        exact hagamma
    · have hjlt : j.val < S.length := by
        rw [hPlusLen] at j
        omega
      let jS : Fin S.length := ⟨j.val, hjlt⟩
      obtain ⟨i, c, hcolor, hmissing⟩ := hS.tashkinov jS (by simpa [jS] using hj)
      let ii : Fin (j.val + 1) := ⟨i.val, by simpa [jS] using i.isLt⟩
      refine ⟨ii, c, ?_, ?_⟩
      · have hindex : j = Fin.castLE hSPlusInit.1 jS := by
          apply Fin.ext
          rfl
        rw [hindex, hPlusEdge]
        exact hcolor
      · have hidx : Fin.castLT ii
            (Nat.lt_trans ii.isLt (Nat.succ_lt_succ j.isLt)) =
            Fin.castLE (Nat.succ_le_succ hSPlusInit.1)
              (Fin.castLT i
                (Nat.lt_trans i.isLt (Nat.succ_lt_succ jS.isLt))) := by
          apply Fin.ext
          rfl
        rw [hidx, hPlusVertex]
        exact hmissing
  have hgammaUsedT : gamma ∈ TreeUsedColors phi T := by
    simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨q, by simp [q]; omega, hqcolor⟩
  have hSCard : (TreeSequenceVertexSet S).card = S.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
      S.vertex_injective]
  have hPlusCard : (TreeSequenceVertexSet Splus).card = S.length + 2 := by
    rw [show (TreeSequenceVertexSet Splus).card = Splus.length + 1 by
      simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
        Splus.vertex_injective]]
    omega
  have hsGamma : gamma ∈ MissingColors G phi
      (Splus.vertex (Fin.castLE (Nat.succ_le_succ hSPlusInit.1) s)) := by
    rw [hPlusVertex, hsa]
    exact hagamma
  have hElem : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet Splus) :=
    TashTree G k e0 phi Splus htriple hPlusTash
  let U := TreeSequenceVertexSet Splus
  let z := Splus.vertex (Fin.castLE (Nat.succ_le_succ hSPlusInit.1) s)
  have hzU : z ∈ U := by
    simp [z, U, TreeSequenceVertexSet]
  have hzMissing : gamma ∈ MissingColors G phi z := by
    simpa [z] using hsGamma
  have hzNotPresent : gamma ∉ PresentColors G phi z := by
    simpa [MissingColors] using hzMissing
  have hproper : IsProperEdgeColoring G phi := htriple.2.2.2.1
  have hpresent : ∀ v, v ∈ U → v ≠ z →
      gamma ∈ PresentColors G phi v := by
    intro v hv hvz
    have hnmissing : gamma ∉ MissingColors G phi v := by
      intro hm
      have hd : Disjoint (MissingColors G phi v) (MissingColors G phi z) :=
        hElem (by simpa [U] using hv) (by simpa [U] using hzU) hvz
      exact (Finset.disjoint_left.mp hd) hm hzMissing
    simpa [MissingColors] using hnmissing
  let B := BoundaryColorEdges G phi U gamma
  let edges := (Finset.univ : Finset E).filter (fun e => phi e = some gamma)
  let good := edges.filter (fun e => ∀ v, Incident G v e → v ∈ U)
  let Y := U.erase z
  have hedgeMem : ∀ e, e ∈ edges ↔ phi e = some gamma := by
    intro e
    simp [edges]
  have hgood : ∀ e, e ∈ good ↔
      e ∈ edges ∧ ∀ v, Incident G v e → v ∈ U := by
    intro e
    simp [good]
  have hendcard : ∀ e : E, (G.ends e).toFinset.card = 2 := by
    intro e
    apply Sym2.card_toFinset_of_not_isDiag
    intro hd
    exact G.loopless e ((G.ends e).diagElem hd) (Sym2.diag_diagElem hd).symm
  have hgoodDisjoint : ∀ ⦃e⦄, e ∈ good → ∀ ⦃f⦄, f ∈ good →
      e ≠ f → Disjoint (G.ends e).toFinset (G.ends f).toFinset := by
    intro e he f hf hef
    rw [Finset.disjoint_left]
    intro v hev hvf
    exact (hproper hef
      ⟨v, Sym2.mem_toFinset.mp hev, Sym2.mem_toFinset.mp hvf⟩
      (hedgeMem e |>.mp (hgood e |>.mp he).1))
      (hedgeMem f |>.mp (hgood f |>.mp hf).1)
  have hgoodUnion :
      (good.biUnion fun e => (G.ends e).toFinset).card = 2 * good.card := by
    have aux : ∀ A : Finset E, A ⊆ good →
        (A.biUnion fun e => (G.ends e).toFinset).card = 2 * A.card := by
      intro A hA
      induction A using Finset.induction_on with
      | empty => simp
      | @insert e A heA ih =>
        rw [Finset.biUnion_insert]
        have hd : Disjoint (G.ends e).toFinset
            (A.biUnion fun f => (G.ends f).toFinset) := by
          rw [Finset.disjoint_left]
          intro v hev hvA
          obtain ⟨f, hf, hvf⟩ := Finset.mem_biUnion.mp hvA
          have hh := hgoodDisjoint (hA (Finset.mem_insert_self e A))
            (hA (Finset.mem_insert_of_mem hf)) (by
              intro hef
              exact heA (by simpa [hef] using hf))
          exact (Finset.disjoint_left.mp hh) hev hvf
        rw [Finset.card_union_of_disjoint hd, hendcard]
        rw [ih (fun x hx => hA (Finset.mem_insert_of_mem hx))]
        rw [Finset.card_insert_of_notMem heA]
        omega
    exact aux good (by intro e he; exact he)
  have hcover : ∀ v, v ∈ Y →
      v ∈ good.biUnion (fun e => (G.ends e).toFinset) ∨
        v ∈ B.biUnion (fun e => U.filter (fun v => Incident G v e)) := by
    intro v hvY
    have hvU : v ∈ U := Finset.mem_of_mem_erase hvY
    have hvz : v ≠ z := (Finset.mem_erase.mp hvY).1
    obtain ⟨e, hve, hecolor⟩ := by
      simpa [PresentColors] using hpresent v hvU hvz
    by_cases hall : ∀ w, Incident G w e → w ∈ U
    · left
      exact Finset.mem_biUnion.mpr
        ⟨e, (hgood e).mpr ⟨(hedgeMem e).mpr hecolor, hall⟩,
          Sym2.mem_toFinset.mpr hve⟩
    · right
      push_neg at hall
      obtain ⟨w, hw, hwo⟩ := hall
      obtain ⟨x, hx⟩ := Sym2.mem_iff_exists.mp hw
      have heq : G.ends e = s(w, x) := hx
      have hxU : x ∈ U := by
        have hvends : v = w ∨ v = x := by
          have : v ∈ s(w, x) := by rw [← heq]; exact hve
          simpa using this
        rcases hvends with rfl | rfl
        · exact False.elim (hwo hvU)
        · exact hvU
      have hbound : e ∈ BoundaryEdges G U := by
        simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨x, hxU, w, hwo, heq.trans Sym2.eq_swap⟩
      exact Finset.mem_biUnion.mpr
        ⟨e, (Finset.mem_filter.mpr ⟨hbound, hecolor⟩),
          Finset.mem_filter.mpr ⟨hvU, hve⟩⟩
  have hbFiber : ∀ e, e ∈ B →
      (U.filter (fun v => Incident G v e)).card = 1 := by
    intro e he
    obtain ⟨u, hu, v, hv, huv⟩ := by
      simpa [B, BoundaryColorEdges, BoundaryEdges] using
        (Finset.mem_filter.mp he).1
    have hs : U.filter (fun x => Incident G x e) = {u} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton, Incident,
        huv, Sym2.mem_iff]
      constructor
      · rintro ⟨hxU, rfl | hxe⟩
        · exact rfl
        · exact False.elim (hv (hxe ▸ hxU))
      · intro hxu
        subst hxu
        exact ⟨hu, Or.inl rfl⟩
    rw [hs]
    simp
  have hbDisjoint : ∀ ⦃e⦄, e ∈ B → ∀ ⦃f⦄, f ∈ B → e ≠ f →
      Disjoint (U.filter (fun v => Incident G v e))
        (U.filter (fun v => Incident G v f)) := by
    intro e he f hf hef
    rw [Finset.disjoint_left]
    intro v hev hvf
    exact (hproper hef
      ⟨v, (Finset.mem_filter.mp hev).2, (Finset.mem_filter.mp hvf).2⟩
      (Finset.mem_filter.mp he).2) (Finset.mem_filter.mp hf).2
  have hbUnion :
      (B.biUnion fun e => U.filter (fun v => Incident G v e)).card = B.card := by
    have aux : ∀ A : Finset E, A ⊆ B →
        (A.biUnion fun e => U.filter (fun v => Incident G v e)).card =
          A.card := by
      intro A hA
      induction A using Finset.induction_on with
      | empty => simp
      | @insert e A heA ih =>
        rw [Finset.biUnion_insert]
        have hd : Disjoint (U.filter (fun v => Incident G v e))
            (A.biUnion fun f => U.filter (fun v => Incident G v f)) := by
          rw [Finset.disjoint_left]
          intro v hev hvA
          obtain ⟨f, hf, hvf⟩ := Finset.mem_biUnion.mp hvA
          exact (Finset.disjoint_left.mp
            (hbDisjoint (hA (Finset.mem_insert_self e A))
              (hA (Finset.mem_insert_of_mem hf)) (by
                intro hef
                exact heA (by simpa [hef] using hf)))) hev hvf
        rw [Finset.card_union_of_disjoint hd,
          hbFiber e (hA (Finset.mem_insert_self e A))]
        rw [ih (fun x hx => hA (Finset.mem_insert_of_mem hx))]
        rw [Finset.card_insert_of_notMem heA]
        omega
    exact aux B (by intro e he; exact he)
  let I := good.biUnion (fun e => (G.ends e).toFinset)
  let W := B.biUnion (fun e => U.filter (fun v => Incident G v e))
  have hIY : I ⊆ Y := by
    intro v hv
    obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
    have hvU : v ∈ U := (hgood e).mp he |>.2 v
      (Sym2.mem_toFinset.mp hve)
    have hvz : v ≠ z := by
      intro hvz
      subst v
      apply hzNotPresent
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e, Sym2.mem_toFinset.mp hve,
        hedgeMem e |>.mp (hgood e |>.mp he).1⟩
    exact Finset.mem_erase.mpr ⟨hvz, hvU⟩
  have hWY : W ⊆ Y := by
    intro v hv
    obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
    have hvU := (Finset.mem_filter.mp hve).1
    have hvz : v ≠ z := by
      intro hvz
      subst v
      apply hzNotPresent
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e, (Finset.mem_filter.mp hve).2,
        (Finset.mem_filter.mp he).2⟩
    exact Finset.mem_erase.mpr ⟨hvz, hvU⟩
  have hIW : Disjoint I W := by
    rw [Finset.disjoint_left]
    intro v hvI hvW
    obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hvI
    obtain ⟨f, hf, hvf⟩ := Finset.mem_biUnion.mp hvW
    have hef : e ≠ f := by
      intro hef
      subst f
      obtain ⟨u, hu, w, hw, huw⟩ := by
        simpa [B, BoundaryColorEdges, BoundaryEdges] using
          (Finset.mem_filter.mp hf).1
      have hwU : w ∈ U := (hgood e).mp he |>.2 w
        (by change w ∈ G.ends e; rw [huw]; exact Sym2.mem_mk_right u w)
      exact hw hwU
    exact (hproper hef
      ⟨v, Sym2.mem_toFinset.mp hve, (Finset.mem_filter.mp hvf).2⟩
      (hedgeMem e |>.mp (hgood e |>.mp he).1))
      (Finset.mem_filter.mp hf).2
  have hIYunion : I ∪ W = Y := by
    apply Finset.Subset.antisymm
    · exact Finset.union_subset hIY hWY
    · intro v hv
      rcases hcover v hv with hvI | hvW
      · exact Finset.mem_union.mpr (Or.inl hvI)
      · exact Finset.mem_union.mpr (Or.inr hvW)
  have hYCardEq : Y.card = 2 * good.card + B.card := by
    rw [← hIYunion, Finset.card_union_of_disjoint hIW]
    simpa [I, W] using congrArg₂ (· + ·) hgoodUnion hbUnion
  have hUCard : U.card = S.length + 2 := by
    simpa [U] using hPlusCard
  have hYCard : Y.card = S.length + 1 := by
    have herase := Finset.card_erase_add_one hzU
    change Y.card + 1 = U.card at herase
    omega
  have hYOdd : Odd Y.card := by
    rw [hYCard, ← hSCard]
    exact hS.oddOrder
  have hBOdd : Odd B.card := by
    rcases hYOdd with ⟨m, hm⟩
    have hgoodle : good.card ≤ m := by omega
    refine ⟨m - good.card, ?_⟩
    omega
  have hBpos : 0 < B.card := by
    rcases hBOdd with ⟨m, hm⟩
    omega
  obtain ⟨f, hfB⟩ := Finset.card_pos.mp hBpos
  have hfBoundary : f ∈ BoundaryEdges G U :=
    (Finset.mem_filter.mp hfB).1
  have hfColor : phi f = some gamma :=
    (Finset.mem_filter.mp hfB).2
  obtain ⟨Splusplus, hAdjoinPlusPlus⟩ :=
    TreeSequenceBoundaryEdgeAppendExists Splus f hfBoundary
  rcases hAdjoinPlusPlus with
    ⟨hPlusPlusLen, hPlusPlusInit, hPlusPlusLast⟩
  have hPlusPlusVertex (i : Fin (Splus.length + 1)) :
      Splusplus.vertex
          (Fin.castLE (Nat.succ_le_succ hPlusPlusInit.1) i) =
        Splus.vertex i := hPlusPlusInit.2.1 i
  have hPlusPlusEdge (j : Fin Splus.length) :
      Splusplus.edge (Fin.castLE hPlusPlusInit.1 j) = Splus.edge j :=
    hPlusPlusInit.2.2 j
  let zIndex : Fin (Splus.length + 1) :=
    Fin.castLE (Nat.succ_le_succ hSPlusInit.1) s
  have hzIndexMissing : gamma ∈ MissingColors G phi (Splus.vertex zIndex) := by
    simpa [zIndex] using hsGamma
  have hPlusPlusTash : TashkinovTree G e0 phi Splusplus := by
    intro j hj
    by_cases hlast : j.val = Splus.length
    · have hjlast : j = Fin.cast hPlusPlusLen.symm (Fin.last Splus.length) := by
        apply Fin.ext
        simpa [hlast]
      let zz : Fin (j.val + 1) :=
        ⟨zIndex.val, by simpa [hlast] using zIndex.isLt⟩
      refine ⟨zz, gamma, ?_, ?_⟩
      · rw [hjlast, hPlusPlusLast, hfColor]
      · have hcast : Fin.castLT zz
            (Nat.lt_trans zz.isLt (Nat.succ_lt_succ j.isLt)) =
            Fin.castLE (Nat.succ_le_succ hPlusPlusInit.1) zIndex := by
          apply Fin.ext
          simp [zz]
        rw [hcast, hPlusPlusVertex]
        exact hzIndexMissing
    · have hjlt : j.val < Splus.length := by
        rw [hPlusPlusLen] at j
        omega
      let jPlus : Fin Splus.length := ⟨j.val, hjlt⟩
      obtain ⟨i, c, hcolor, hmissing⟩ :=
        hPlusTash jPlus (by simpa [jPlus] using hj)
      let ii : Fin (j.val + 1) :=
        ⟨i.val, by simpa [jPlus] using i.isLt⟩
      refine ⟨ii, c, ?_, ?_⟩
      · have hindex : j = Fin.castLE hPlusPlusInit.1 jPlus := by
          apply Fin.ext
          rfl
        rw [hindex, hPlusPlusEdge]
        exact hcolor
      · have hidx : Fin.castLT ii
            (Nat.lt_trans ii.isLt (Nat.succ_lt_succ j.isLt)) =
            Fin.castLE (Nat.succ_le_succ hPlusPlusInit.1)
              (Fin.castLT i
                (Nat.lt_trans i.isLt (Nat.succ_lt_succ jPlus.isLt))) := by
          apply Fin.ext
          rfl
        rw [hidx, hPlusPlusVertex]
        exact hmissing
  have hSPlusPlusInit : TreeSequenceInitialSegment S Splusplus := by
    rcases hSPlusInit with ⟨hSP, hvSP, heSP⟩
    rcases hPlusPlusInit with ⟨hPP, hvPP, hePP⟩
    refine ⟨le_trans hSP hPP, ?_, ?_⟩
    · intro i
      have hi : Fin.castLE (Nat.succ_le_succ (le_trans hSP hPP)) i =
          Fin.castLE (Nat.succ_le_succ hPP)
            (Fin.castLE (Nat.succ_le_succ hSP) i) := by
        apply Fin.ext
        rfl
      rw [hi, hvPP]
      exact hvSP i
    · intro j
      have hj : Fin.castLE (le_trans hSP hPP) j =
          Fin.castLE hPP (Fin.castLE hSP j) := by
        apply Fin.ext
        rfl
      rw [hj, hePP]
      exact heSP j
  have hTrunkInit :
      TreeSequenceInitialSegment (NormalTripleTrunk N) Splusplus := by
    rcases hS.exactTrunk with ⟨hTS, hvTS, heTS⟩
    rcases hSPlusPlusInit with ⟨hSS, hvSS, heSS⟩
    refine ⟨le_trans hTS hSS, ?_, ?_⟩
    · intro i
      have hi : Fin.castLE (Nat.succ_le_succ (le_trans hTS hSS)) i =
          Fin.castLE (Nat.succ_le_succ hSS)
            (Fin.castLE (Nat.succ_le_succ hTS) i) := by
        apply Fin.ext
        rfl
      rw [hi, hvSS]
      exact hvTS i
    · intro j
      have hj : Fin.castLE (le_trans hTS hSS) j =
          Fin.castLE hSS (Fin.castLE hTS j) := by
        apply Fin.ext
        rfl
      rw [hj, heSS]
      exact heTS j
  let firstNewPlus : Fin Splus.length :=
    Fin.cast hPlusLen.symm (Fin.last S.length)
  let firstNew : Fin Splusplus.length :=
    Fin.castLE hPlusPlusInit.1 firstNewPlus
  let secondNew : Fin Splusplus.length :=
    Fin.cast hPlusPlusLen.symm (Fin.last Splus.length)
  have hFirstNewVal : firstNew.val = S.length := by
    simp [firstNew, firstNewPlus]
  have hSecondNewVal : secondNew.val = S.length + 1 := by
    simp [secondNew, hPlusLen]
  have hFirstNewColor : phi (Splusplus.edge firstNew) = some gamma := by
    rw [show Splusplus.edge firstNew = Splus.edge firstNewPlus by
      exact hPlusPlusEdge firstNewPlus]
    rw [show Splus.edge firstNewPlus = T.edge q by
      exact hPlusLast]
    exact hqcolor
  have hSecondNewColor : phi (Splusplus.edge secondNew) = some gamma := by
    rw [show Splusplus.edge secondNew = f by exact hPlusPlusLast]
    exact hfColor
  have hPlusPlusCard :
      (TreeSequenceVertexSet Splusplus).card = S.length + 3 := by
    rw [show (TreeSequenceVertexSet Splusplus).card =
        Splusplus.length + 1 by
      simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
        Splusplus.vertex_injective]]
    omega
  have hUsed : TreeUsedColors phi Splusplus ⊆ TreeUsedColors phi T := by
    intro c hc
    simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ,
      true_and] at hc ⊢
    obtain ⟨j, hj, hjcolor⟩ := hc
    by_cases hold : j.val < S.length
    · let jS : Fin S.length := ⟨j.val, hold⟩
      have hjEq : j = Fin.castLE hPlusPlusInit.1
          (Fin.castLE hSPlusInit.1 jS) := by
        apply Fin.ext
        rfl
      have hOldColor : phi (S.edge jS) = some c := by
        rw [hjEq, hPlusPlusEdge, hPlusEdge] at hjcolor
        exact hjcolor
      have hcS : c ∈ TreeUsedColors phi S := by
        simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨jS, by simpa [jS] using hj, hOldColor⟩
      simpa [TreeUsedColors] using hS.usedColors hcS
    · have hjcases : j.val = S.length ∨ j.val = S.length + 1 := by
        rw [hPlusPlusLen, hPlusLen] at j
        omega
      have hcgamma : c = gamma := by
        rcases hjcases with hfirst | hsecond
        · have hjeq : j = firstNew := by
            apply Fin.ext
            simpa [hFirstNewVal] using hfirst
          rw [hjeq, hFirstNewColor] at hjcolor
          exact (Option.some.inj hjcolor).symm
        · have hjeq : j = secondNew := by
            apply Fin.ext
            simpa [hSecondNewVal] using hsecond
          rw [hjeq, hSecondNewColor] at hjcolor
          exact (Option.some.inj hjcolor).symm
      simpa [hcgamma, TreeUsedColors] using hgammaUsedT
  have hPlusPlusOdd : Odd (TreeSequenceVertexSet Splusplus).card := by
    rcases hS.oddOrder with ⟨m, hm⟩
    refine ⟨m + 1, ?_⟩
    rw [hPlusPlusCard]
    rw [hSCard] at hm
    omega
  have hCandidate : ScheideBalancedCandidate N Splusplus := by
    refine
      { tashkinov := hPlusPlusTash
        oddOrder := hPlusPlusOdd
        exactTrunk := hTrunkInit
        usedColors := hUsed
        paired := ?_ }
    intro r hlow hupp
    by_cases hold : 2 * r < S.length + 1
    · have hOld := hS.paired r hlow hold
      have hidxOne :
          (⟨2 * r - 2, by omega⟩ : Fin Splusplus.length) =
            Fin.castLE hPlusPlusInit.1
              (Fin.castLE hSPlusInit.1
                (⟨2 * r - 2, by omega⟩ : Fin S.length)) := by
        apply Fin.ext
        rfl
      have hidxTwo :
          (⟨2 * r - 1, by omega⟩ : Fin Splusplus.length) =
            Fin.castLE hPlusPlusInit.1
              (Fin.castLE hSPlusInit.1
                (⟨2 * r - 1, by omega⟩ : Fin S.length)) := by
        apply Fin.ext
        rfl
      rw [hidxOne, hidxTwo, hPlusPlusEdge, hPlusEdge,
        hPlusPlusEdge, hPlusEdge]
      exact hOld
    · have hoddLength : Odd (S.length + 1) := by
        rw [← hSCard]
        exact hS.oddOrder
      have hne : 2 * r ≠ S.length + 1 := by
        intro heq
        rcases hoddLength with ⟨m, hm⟩
        omega
      have heq : 2 * r = S.length + 2 := by
        rw [hPlusPlusLen, hPlusLen] at hupp
        omega
      have hidxOne :
          (⟨2 * r - 2, by omega⟩ : Fin Splusplus.length) = firstNew := by
        apply Fin.ext
        simp [hFirstNewVal, heq]
      have hidxTwo :
          (⟨2 * r - 1, by omega⟩ : Fin Splusplus.length) = secondNew := by
        apply Fin.ext
        simp [hSecondNewVal, heq]
      rw [hidxOne, hidxTwo, hFirstNewColor, hSecondNewColor]
  have hmaxPlusPlus := hmax Splusplus hCandidate
  rw [hPlusPlusCard, hSCard] at hmaxPlusPlus
  omega
