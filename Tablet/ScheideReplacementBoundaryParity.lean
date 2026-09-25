import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.GlobalMaximumTriple
import Tablet.Incident
import Tablet.InternalEdges
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.ScheideDefectiveNoCross
import Tablet.ScheideDefectiveSetup
import Tablet.ScheideGlobalMaximumBoundaryFacts
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideReducedConfiguration
import Tablet.ScheideStructuralConfiguration
import Tablet.ScheideExitVertex
import Tablet.ScheideExitVertices
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: ScheideReplacementBoundaryParity]
theorem ScheideReplacementBoundaryParity {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C) :
    ∀ d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)},
      let X := TreeSequenceVertexSet T
      let Z := X \ {C.blockVertex (D.gammaIndex d) 0,
        C.blockVertex (D.gammaIndex d) 1}
      let B := @Finset.filter E (fun f => ∃ w, w ∉ X ∧ Incident G w f)
        (fun _ => Classical.propDecidable _) (BoundaryColorEdges G phi Z d.1)
      D.v0 d ∈ Z ∧
        C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ ∈ Z ∧
        (∀ z ∈ Z, ∃! f : E, Incident G z f ∧ phi f = some d.1) ∧
        D.f0 d ∈ B ∧ Odd B.card := by
-- BODY
  classical
  intro d
  dsimp only
  let X := TreeSequenceVertexSet T
  let i := D.gammaIndex d
  let U := ({C.blockVertex i 0, C.blockVertex i 1} : Finset V)
  let Z := X \ U
  let B := (BoundaryColorEdges G phi Z d.1).filter
    (fun f => ∃ w, w ∉ X ∧ Incident G w f)

  have hproper : IsProperEdgeColoring G phi :=
    C.globally_maximum.1.2.2.2.1
  have horder := ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum
  have helementary : ColoredVertexSetElementary G phi X := by
    exact horder.2.2.2.1
  have hclosed : ColoredVertexSetClosed G phi X := by
    exact horder.2.2.2.2
  have hlength := C.length_eq

  have base_mem_X (a : Fin C.p) : C.y a ∈ X := by
    rw [← C.base_vertex_position a]
    simp [X, TreeSequenceVertexSet]
  have block_mem_X (b : Fin 2) : C.blockVertex i b ∈ X := by
    rw [← C.block_vertex_position i b]
    simp [X, TreeSequenceVertexSet]
  have hv0X : D.v0 d ∈ X := by
    have hv0exit : ScheideExitVertex T phi (D.v0 d) := by
      simpa [ScheideExitVertices] using D.v0_is_exit d
    rcases hv0exit with
      ⟨u, gamma, delta, hu, hgamma, hdelta, z, path, hpath,
        q, hq, hv0X, hafter⟩
    exact hv0X
  have hv0_base : ∃ a : Fin C.p, D.v0 d = C.y a := by
    obtain ⟨r, hr0⟩ := C.exit_covered (D.v0 d) (D.v0_is_exit d)
    obtain ⟨a, hra⟩ := C.block_color_missing_on_base r
    refine ⟨a, ?_⟩
    by_contra hne
    have hdisjoint := helementary hv0X (base_mem_X a) hne
    exact (Finset.disjoint_left.mp hdisjoint) hr0 hra
  have base_ne_block (a : Fin C.p) (b : Fin 2) :
      C.y a ≠ C.blockVertex i b := by
    intro h
    let qa : Fin (T.length + 1) := ⟨a.val, by
      have ha := a.isLt
      have hi := i.isLt
      have hb := b.isLt
      omega⟩
    let qb : Fin (T.length + 1) :=
      ⟨C.p + 2 * i.val + b.val, by
        have hi := i.isLt
        have hb := b.isLt
        omega⟩
    have hv : T.vertex qa = T.vertex qb := by
      rw [show T.vertex qa = C.y a by
        simpa [qa] using C.base_vertex_position a]
      rw [show T.vertex qb = C.blockVertex i b by
        simpa [qb] using C.block_vertex_position i b]
      exact h
    have hq := congrArg Fin.val (T.vertex_injective hv)
    have ha := a.isLt
    dsimp [qa, qb] at hq
    omega
  have base_mem_Z (a : Fin C.p) : C.y a ∈ Z := by
    apply Finset.mem_sdiff.mpr
    refine ⟨base_mem_X a, ?_⟩
    simp [U, base_ne_block]
  have hv0Z : D.v0 d ∈ Z := by
    obtain ⟨a, ha⟩ := hv0_base
    rw [ha]
    exact base_mem_Z a
  let y0 := C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
  have hy0Z : y0 ∈ Z := by
    exact base_mem_Z ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩

  have hpair_ne : C.blockVertex i 0 ≠ C.blockVertex i 1 := by
    intro h
    let q0 : Fin (T.length + 1) :=
      ⟨C.p + 2 * i.val, by
        have hi := i.isLt
        omega⟩
    let q1 : Fin (T.length + 1) :=
      ⟨C.p + 2 * i.val + 1, by
        have hi := i.isLt
        omega⟩
    have hv : T.vertex q0 = T.vertex q1 := by
      rw [show T.vertex q0 = C.blockVertex i 0 by
        simpa [q0] using C.block_vertex_position i (0 : Fin 2)]
      rw [show T.vertex q1 = C.blockVertex i 1 by
        simpa [q1] using C.block_vertex_position i (1 : Fin 2)]
      exact h
    have hq := congrArg Fin.val (T.vertex_injective hv)
    simp [q0, q1] at hq
  have hUcard : U.card = 2 := by
    simp [U, hpair_ne]
  have hUsub : U ⊆ X := by
    intro v hv
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact block_mem_X 0
    · exact block_mem_X 1
  have hZcard : Z.card = X.card - 2 := by
    change (X \ U).card = X.card - 2
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hUsub, hUcard]
  have hZodd : Odd Z.card := by
    rcases horder.2.2.1 with ⟨q, hq⟩
    have htwo : 2 ≤ X.card := by
      rw [← hUcard]
      exact Finset.card_le_card hUsub
    refine ⟨q - 1, ?_⟩
    rw [hZcard]
    have hq' : X.card = 2 * q + 1 := by simpa [X] using hq
    omega

  have hboundary_nonempty :
      0 < (BoundaryColorEdges G phi X d.1).card := by
    have hthree :=
      (ScheideGlobalMaximumBoundaryFacts G k e0 phi T C.globally_maximum).2.2
        d.1 d.2 |>.2
    simpa [X] using (lt_of_lt_of_le (by omega : 0 < 3) hthree)
  obtain ⟨boundaryEdge, hboundaryEdge⟩ :=
    Finset.card_pos.mp hboundary_nonempty
  have hboundary : boundaryEdge ∈ BoundaryEdges G X :=
    (Finset.mem_filter.mp hboundaryEdge).1
  have hboundary_color : phi boundaryEdge = some d.1 :=
    (Finset.mem_filter.mp hboundaryEdge).2
  have hpresent : ∀ v, v ∈ Z → d.1 ∈ PresentColors G phi v := by
    intro v hvZ
    have hnotmissing : d.1 ∉ MissingColors G phi v := by
      exact hclosed hboundary (Finset.mem_sdiff.mp hvZ).1 hboundary_color
    simpa [MissingColors] using hnotmissing
  have hunique : ∀ v, v ∈ Z →
      ∃! f : E, Incident G v f ∧ phi f = some d.1 := by
    intro v hvZ
    obtain ⟨f, hvf, hfc⟩ := by
      simpa [PresentColors] using hpresent v hvZ
    refine ⟨f, ⟨hvf, hfc⟩, ?_⟩
    intro g hg
    by_contra hgf
    exact (hproper hgf ⟨v, hg.1, hvf⟩ hg.2) hfc

  have hf0B : D.f0 d ∈ B := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, D.u0 d, D.u0_outside d, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨?_, D.f0_color d⟩
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨D.v0 d, hv0Z, D.u0 d,
        fun huZ => D.u0_outside d (Finset.mem_sdiff.mp huZ).1,
        D.f0_ends d⟩
    · simp [Incident, D.f0_ends d]

  let internal := (InternalEdges G Z).filter (fun e => phi e = some d.1)
  have hinternal : ∀ e, e ∈ internal ↔
      phi e = some d.1 ∧ ∀ v, Incident G v e → v ∈ Z := by
    intro e
    simp [internal, InternalEdges, and_comm]
  have hendcard : ∀ e : E, (G.ends e).toFinset.card = 2 := by
    intro e
    apply Sym2.card_toFinset_of_not_isDiag
    intro hd
    exact G.loopless e ((G.ends e).diagElem hd)
      (Sym2.diag_diagElem hd).symm
  have hinternal_disjoint : ∀ ⦃e⦄, e ∈ internal → ∀ ⦃f⦄, f ∈ internal →
      e ≠ f → Disjoint (G.ends e).toFinset (G.ends f).toFinset := by
    intro e he f hf hef
    rw [Finset.disjoint_left]
    intro v hev hvf
    exact (hproper hef
      ⟨v, Sym2.mem_toFinset.mp hev, Sym2.mem_toFinset.mp hvf⟩
      ((hinternal e).mp he).1) ((hinternal f).mp hf).1
  have hinternal_union :
      (internal.biUnion fun e => (G.ends e).toFinset).card =
        2 * internal.card := by
    as_aux_lemma =>
    have aux : ∀ s : Finset E, s ⊆ internal →
        (s.biUnion fun e => (G.ends e).toFinset).card = 2 * s.card := by
      intro s hs
      induction s using Finset.induction_on with
      | empty => simp
      | @insert e s hes ih =>
        rw [Finset.biUnion_insert]
        have hd : Disjoint (G.ends e).toFinset
            (s.biUnion fun f => (G.ends f).toFinset) := by
          rw [Finset.disjoint_left]
          intro v hev hvs
          obtain ⟨f, hf, hvf⟩ := Finset.mem_biUnion.mp hvs
          have hh := hinternal_disjoint
            (hs (Finset.mem_insert_self e s))
            (hs (Finset.mem_insert_of_mem hf)) (by
              intro heq
              exact hes (by simpa [heq] using hf))
          exact (Finset.disjoint_left.mp hh) hev hvf
        rw [Finset.card_union_of_disjoint hd, hendcard]
        rw [ih (fun x hx => hs (Finset.mem_insert_of_mem hx))]
        rw [Finset.card_insert_of_notMem hes]
        omega
    exact aux internal (by intro e he; exact he)

  have hcover : ∀ v, v ∈ Z →
      v ∈ internal.biUnion (fun e => (G.ends e).toFinset) ∨
        v ∈ B.biUnion (fun e => Z.filter (fun w => Incident G w e)) := by
    as_aux_lemma =>
    intro v hvZ
    obtain ⟨e, hve, hecolor⟩ := by
      simpa [PresentColors] using hpresent v hvZ
    by_cases hall : ∀ w, Incident G w e → w ∈ Z
    · left
      exact Finset.mem_biUnion.mpr
        ⟨e, (hinternal e).mpr ⟨hecolor, hall⟩,
          Sym2.mem_toFinset.mpr hve⟩
    · right
      push Not at hall
      obtain ⟨w, hwe, hwZ⟩ := hall
      have hwX : w ∉ X := by
        intro hwX
        have hwU : w ∈ U := by
          by_contra hwU
          exact hwZ (Finset.mem_sdiff.mpr ⟨hwX, hwU⟩)
        have hno := ScheideDefectiveNoCross G k e0 phi T C D d e hecolor
        exact hno ⟨w, by simpa [U, i] using hwU, hwe,
          v, by simpa [X, U, Z, i] using hvZ, hve⟩
      obtain ⟨z, hze⟩ := Sym2.mem_iff_exists.mp hwe
      have heq : G.ends e = s(w, z) := hze
      have hzv : z = v := by
        have hvEnds : v = w ∨ v = z := by
          have : v ∈ s(w, z) := by rw [← heq]; exact hve
          simpa using this
        rcases hvEnds with hvw | hvz
        · exact False.elim (hwZ (hvw ▸ hvZ))
        · exact hvz.symm
      have heboundary : e ∈ BoundaryEdges G Z := by
        simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨v, hvZ, w, hwZ, by simpa [hzv] using heq.trans Sym2.eq_swap⟩
      have heB : e ∈ B := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_filter.mpr ⟨heboundary, hecolor⟩, w, hwX, hwe⟩
      exact Finset.mem_biUnion.mpr ⟨e, heB,
        Finset.mem_filter.mpr ⟨hvZ, hve⟩⟩

  have hBfiber : ∀ e, e ∈ B →
      (Z.filter (fun v => Incident G v e)).card = 1 := by
    as_aux_lemma =>
    intro e he
    have heboundary : e ∈ BoundaryEdges G Z :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1
    obtain ⟨u, hu, v, hv, huv⟩ := by
      simpa [BoundaryEdges] using heboundary
    have hs : Z.filter (fun x => Incident G x e) = {u} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton, Incident,
        huv, Sym2.mem_iff]
      constructor
      · rintro ⟨hx, rfl | hxe⟩
        · exact rfl
        · exact False.elim (hv (hxe ▸ hx))
      · intro hxu
        subst hxu
        exact ⟨hu, Or.inl rfl⟩
    rw [hs]
    simp
  have hBcolor : ∀ e, e ∈ B → phi e = some d.1 := by
    intro e he
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
  have hBdisjoint : ∀ ⦃e⦄, e ∈ B → ∀ ⦃f⦄, f ∈ B → e ≠ f →
      Disjoint (Z.filter (fun v => Incident G v e))
        (Z.filter (fun v => Incident G v f)) := by
    intro e he f hf hef
    rw [Finset.disjoint_left]
    intro v hev hvf
    exact (hproper hef ⟨v, (Finset.mem_filter.mp hev).2,
      (Finset.mem_filter.mp hvf).2⟩ (hBcolor e he)) (hBcolor f hf)
  have hBunion :
      (B.biUnion fun e => Z.filter (fun v => Incident G v e)).card =
        B.card := by
    as_aux_lemma =>
    have aux : ∀ s : Finset E, s ⊆ B →
        (s.biUnion fun e => Z.filter (fun v => Incident G v e)).card =
          s.card := by
      intro s hs
      induction s using Finset.induction_on with
      | empty => simp
      | @insert e s hes ih =>
        rw [Finset.biUnion_insert]
        have hd : Disjoint (Z.filter (fun v => Incident G v e))
            (s.biUnion fun f => Z.filter (fun v => Incident G v f)) := by
          rw [Finset.disjoint_left]
          intro v hev hvs
          obtain ⟨f, hf, hvf⟩ := Finset.mem_biUnion.mp hvs
          exact (Finset.disjoint_left.mp
            (hBdisjoint (hs (Finset.mem_insert_self e s))
              (hs (Finset.mem_insert_of_mem hf)) (by
                intro heq
                exact hes (by simpa [heq] using hf)))) hev hvf
        rw [Finset.card_union_of_disjoint hd,
          hBfiber e (hs (Finset.mem_insert_self e s))]
        rw [ih (fun x hx => hs (Finset.mem_insert_of_mem hx))]
        rw [Finset.card_insert_of_notMem hes]
        exact Nat.add_comm 1 s.card
    exact aux B (by intro e he; exact he)

  let A := internal.biUnion (fun e => (G.ends e).toFinset)
  let W := B.biUnion (fun e => Z.filter (fun v => Incident G v e))
  have hA : A ⊆ Z := by
    intro v hv
    obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
    exact ((hinternal e).mp he).2 v (Sym2.mem_toFinset.mp hve)
  have hW : W ⊆ Z := by
    intro v hv
    obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
    exact (Finset.mem_filter.mp hve).1
  have hAW : Disjoint A W := by
    as_aux_lemma =>
    rw [Finset.disjoint_left]
    intro v hvA hvW
    obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hvA
    obtain ⟨f, hf, hvf⟩ := Finset.mem_biUnion.mp hvW
    have hef : e ≠ f := by
      intro hef
      have hfboundary : f ∈ BoundaryEdges G Z :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).1
      obtain ⟨u, hu, w, hw, huw⟩ := by
        simpa [BoundaryEdges] using hfboundary
      have : w ∈ Z := ((hinternal e).mp he).2 w (by
        change w ∈ G.ends e
        rw [hef, huw]
        simp)
      exact hw this
    exact (hproper hef ⟨v, Sym2.mem_toFinset.mp hve,
      (Finset.mem_filter.mp hvf).2⟩ ((hinternal e).mp he).1)
      (hBcolor f hf)
  have hAZ : A ∪ W = Z := by
    apply Finset.Subset.antisymm
    · exact Finset.union_subset hA hW
    · intro v hv
      rcases hcover v hv with hvA | hvW
      · exact Finset.mem_union.mpr (Or.inl hvA)
      · exact Finset.mem_union.mpr (Or.inr hvW)
  have hcardeq : Z.card = 2 * internal.card + B.card := by
    rw [← hAZ, Finset.card_union_of_disjoint hAW,
      hinternal_union, hBunion]
  have hBodd : Odd B.card := by
    rcases hZodd with ⟨q, hq⟩
    have hq' : Z.card = 2 * q + 1 := hq
    have hintle : internal.card ≤ q := by omega
    refine ⟨q - internal.card, ?_⟩
    omega
  let statementB :=
    @Finset.filter E (fun f => ∃ w, w ∉ X ∧ Incident G w f)
      (fun _ => Classical.propDecidable _) (BoundaryColorEdges G phi Z d.1)
  have hBstatement : B = statementB := by
    ext e
    simp [B, statementB]
  have hstatementOdd : Odd statementB.card := by
    rw [← hBstatement]
    exact hBodd

  exact ⟨by simpa [X, i, U, Z] using hv0Z,
    by simpa [X, i, U, Z, y0] using hy0Z,
    by simpa [X, i, U, Z] using hunique,
    by simpa [X, i, U, Z, B] using hf0B,
    by
      have heq : statementB =
          @Finset.filter E
            (fun f => ∃ w, w ∉ TreeSequenceVertexSet T ∧ Incident G w f)
            (fun _ => Classical.propDecidable _)
            (BoundaryColorEdges G phi
              (TreeSequenceVertexSet T \
                {C.blockVertex (D.gammaIndex d) 0,
                  C.blockVertex (D.gammaIndex d) 1}) d.1) := by
        ext e
        simp [statementB, X, i, U, Z]
      rw [← heq]
      exact hstatementOdd⟩
