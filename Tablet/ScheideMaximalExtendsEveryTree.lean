import Tablet.FixedPairMaximalTashkinovTree
import Tablet.ScheideMaximalContainsEveryTree
import Tablet.TashkinovTree
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: ScheideMaximalExtendsEveryTree]
theorem ScheideMaximalExtendsEveryTree {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T S : TreeSequence G e0)
    (htriple : KTriple G k e0 phi)
    (hmax : FixedPairMaximalTashkinovTree G e0 phi T)
    (hS : TashkinovTree G e0 phi S) :
    ∃ T' : TreeSequence G e0,
      TashkinovTree G e0 phi T' ∧
        TreeSequenceVertexSet T' = TreeSequenceVertexSet T ∧
        TreeSequenceInitialSegment S T' := by
-- BODY
  classical
  let X := TreeSequenceVertexSet T
  have hsub : TreeSequenceVertexSet S ⊆ X :=
    ScheideMaximalContainsEveryTree G k e0 phi T S htriple hmax hS
  have hTash : TashkinovTree G e0 phi T := hmax.1
  have first_vertices : ∀ (C : TreeSequence G e0) (j : Fin 2),
      T.vertex (Fin.castLE (Nat.succ_le_succ T.positive) j) ∈
        TreeSequenceVertexSet C := by
    intro C j
    obtain ⟨it, ht⟩ := T.attaches ⟨0, T.positive⟩
    obtain ⟨ic, hc⟩ := C.attaches ⟨0, C.positive⟩
    have itzero : it = 0 := Fin.eq_zero it
    have iczero : ic = 0 := Fin.eq_zero ic
    subst it
    subst ic
    rw [T.first_edge] at ht
    rw [C.first_edge] at hc
    have hm : T.vertex (Fin.castLE (Nat.succ_le_succ T.positive) j) ∈ G.ends e0 := by
      have cases : j.val = 0 ∨ j.val = 1 := by omega
      rcases cases with hzero | hone
      · have hj : j = 0 := Fin.ext hzero
        subst j
        rw [ht]
        apply Sym2.mem_iff.mpr
        right
        rfl
      · have hj : j = 1 := Fin.ext hone
        subst j
        rw [ht]
        apply Sym2.mem_iff.mpr
        left
        rfl
    rw [hc] at hm
    rcases Sym2.mem_iff.mp hm with hm | hm
    · change T.vertex (Fin.castLE (Nat.succ_le_succ T.positive) j) ∈
        Finset.image C.vertex Finset.univ
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, hm.symm⟩
    · change T.vertex (Fin.castLE (Nat.succ_le_succ T.positive) j) ∈
        Finset.image C.vertex Finset.univ
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, hm.symm⟩
  have extend : ∀ (C : TreeSequence G e0),
      TashkinovTree G e0 phi C → TreeSequenceVertexSet C ⊆ X →
      ∃ D : TreeSequence G e0, TashkinovTree G e0 phi D ∧
        TreeSequenceInitialSegment C D ∧ TreeSequenceVertexSet D ⊆ X ∧
        (D.length = C.length + 1 ∨ TreeSequenceVertexSet C = X) := by
    intro C hC hCX
    by_cases heq : TreeSequenceVertexSet C = X
    · exact ⟨C, hC, by
        refine ⟨le_rfl, ?_, ?_⟩
        · intro i; rfl
        · intro j; rfl, by simpa [heq] using hCX, Or.inr heq⟩
    · have hex : ∃ n : ℕ, ∃ hn : n < T.length + 1,
          T.vertex ⟨n, hn⟩ ∉ TreeSequenceVertexSet C := by
        obtain ⟨v, hv, hvc⟩ : ∃ v, v ∈ X ∧ v ∉ TreeSequenceVertexSet C := by
          by_contra hn
          apply heq
          apply Finset.Subset.antisymm hCX
          intro v hv
          by_contra hvo
          exact hn ⟨v, hv, hvo⟩
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp
          (show v ∈ Finset.image T.vertex Finset.univ from
            by simpa [X, TreeSequenceVertexSet] using hv)
        exact ⟨j.val, j.isLt, by simpa using hvc⟩
      let n : ℕ := Nat.find hex
      have hnlt : n < T.length + 1 := (Nat.find_spec hex).1
      have hnout : T.vertex ⟨n, hnlt⟩ ∉ TreeSequenceVertexSet C :=
        (Nat.find_spec hex).2
      have hnle : n ≤ T.length := by omega
      have hnpos : 1 ≤ n := by
        by_contra hp
        have hnzero : n = 0 := by omega
        apply hnout
        simpa [hnzero] using first_vertices C ⟨0, by omega⟩
      have hnlarge : 2 ≤ n := by
        by_contra hh
        have hcases : n = 0 ∨ n = 1 := by omega
        rcases hcases with hzero | hone
        · apply hnout
          simpa [hzero] using first_vertices C ⟨0, by omega⟩
        · apply hnout
          have hv := first_vertices C ⟨1, by omega⟩
          have hi : (⟨n, hnlt⟩ : Fin (T.length + 1)) =
              Fin.castLE (Nat.succ_le_succ T.positive) ⟨1, by omega⟩ := by
            apply Fin.ext
            simp [hone]
          rw [hi]
          exact hv
      let j : Fin T.length := ⟨n - 1, by omega⟩
      have hjrel : j.val + 1 = n := by
        simp [j, Nat.sub_add_cancel hnpos]
      have hjout : T.vertex j.succ ∉ TreeSequenceVertexSet C := by
        have hidx : j.succ = ⟨n, hnlt⟩ := Fin.ext (by simp [j, hjrel])
        rw [hidx]
        exact hnout
      have prior : ∀ (i : Fin (j.val + 1)), i.val ≤ j.val →
          T.vertex (Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))) ∈
            TreeSequenceVertexSet C := by
        intro i hil
        by_contra hout
        have hprop : ∃ hn : i.val < T.length + 1,
            T.vertex ⟨i.val, hn⟩ ∉ TreeSequenceVertexSet C :=
          ⟨by omega, by
            intro hm
            apply hout
            congr 1⟩
        have hmin : n ≤ i.val := Nat.find_min' hex hprop
        exact (not_le_of_gt (by omega : i.val < n)) hmin
      obtain ⟨i, hiatt⟩ := T.attaches j
      have hprior := prior i (by omega)
      obtain ⟨r, hrC, hri⟩ := Finset.mem_image.mp
        (show T.vertex (Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))) ∈
          Finset.image C.vertex Finset.univ from by
            simpa [TreeSequenceVertexSet] using hprior)
      have hedgenew : T.edge j ∉ Finset.image C.edge Finset.univ := by
        intro hedge
        obtain ⟨l, -, hle⟩ := Finset.mem_image.mp hedge
        obtain ⟨lc, hlc⟩ := C.attaches l
        have hends : G.ends (C.edge l) =
            Sym2.mk (C.vertex l.succ) (C.vertex (Fin.castLT lc
              (Nat.lt_trans lc.isLt (Nat.succ_lt_succ l.isLt)))) := hlc
        have hnew : T.vertex j.succ =
            C.vertex l.succ ∨ T.vertex j.succ =
              C.vertex (Fin.castLT lc (Nat.lt_trans lc.isLt (Nat.succ_lt_succ l.isLt))) := by
          have hm : T.vertex j.succ ∈
              Sym2.mk (C.vertex l.succ) (C.vertex (Fin.castLT lc
                (Nat.lt_trans lc.isLt (Nat.succ_lt_succ l.isLt)))) := by
            rw [← hends, hle, hiatt]
            exact Sym2.mem_iff.mpr (by exact Or.inl rfl)
          exact Sym2.mem_iff.mp hm
        rcases hnew with hnew | hnew
        · have hmem : T.vertex j.succ ∈
              Finset.image C.vertex Finset.univ := by
            exact Finset.mem_image.mpr ⟨l.succ, Finset.mem_univ _, hnew.symm⟩
          exact hjout hmem
        · have hmem : T.vertex j.succ ∈
              Finset.image C.vertex Finset.univ := by
            exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, hnew.symm⟩
          exact hjout hmem
      let D : TreeSequence G e0 :=
        { length := C.length + 1
          positive := by omega
          vertex := Fin.lastCases (T.vertex j.succ) C.vertex
          edge := Fin.lastCases (T.edge j) C.edge
          vertex_injective := by
            intro a b
            revert b
            refine Fin.lastCases ?_ (fun a => ?_) a
            · intro b
              refine Fin.lastCases ?_ (fun b => ?_) b
              · intro h; rfl
              · intro h
                dsimp only [Fin.lastCases] at h
                rw [Fin.reverseInduction_last, Fin.reverseInduction_castSucc] at h
                exact (hjout (by
                  apply Finset.mem_image.mpr
                  exact ⟨b, Finset.mem_univ _, h.symm⟩)).elim
            · intro b
              refine Fin.lastCases ?_ (fun b => ?_) b
              · intro h
                dsimp only [Fin.lastCases] at h
                rw [Fin.reverseInduction_last, Fin.reverseInduction_castSucc] at h
                exact (hjout (by
                  apply Finset.mem_image.mpr
                  exact ⟨a, Finset.mem_univ _, h⟩)).elim
              · intro h
                exact congrArg Fin.castSucc (C.vertex_injective (by
                  simpa only [Fin.lastCases_castSucc] using h))
          edge_injective := by
            intro a b
            revert b
            refine Fin.lastCases ?_ (fun a => ?_) a
            · intro b
              refine Fin.lastCases ?_ (fun b => ?_) b
              · intro h; rfl
              · intro h
                dsimp only [Fin.lastCases] at h
                rw [Fin.reverseInduction_last, Fin.reverseInduction_castSucc] at h
                exact (hedgenew (by
                  apply Finset.mem_image.mpr
                  exact ⟨b, Finset.mem_univ _, h.symm⟩)).elim
            · intro b
              refine Fin.lastCases ?_ (fun b => ?_) b
              · intro h
                dsimp only [Fin.lastCases] at h
                rw [Fin.reverseInduction_last, Fin.reverseInduction_castSucc] at h
                exact (hedgenew (by
                  apply Finset.mem_image.mpr
                  exact ⟨a, Finset.mem_univ _, h⟩)).elim
              · intro h
                exact congrArg Fin.castSucc (C.edge_injective (by
                  simpa only [Fin.lastCases_castSucc] using h))
          first_edge := by
            have hzero : (⟨0, Nat.succ_pos C.length⟩ : Fin (C.length + 1)) =
                (⟨0, C.positive⟩ : Fin C.length).castSucc := by rfl
            rw [hzero]
            simp only [Fin.lastCases_castSucc]
            exact C.first_edge
          attaches := by
            intro q
            refine Fin.lastCases ?_ (fun q => ?_) q
            · refine ⟨r, ?_⟩
              have hqidx : ((Fin.last C.length).succ : Fin (C.length + 2)) =
                  Fin.last (C.length + 1) := by
                apply Fin.ext
                simp
              rw [hqidx]
              simp only [Fin.lastCases_last]
              have hridx : (Fin.castLT r (by omega) : Fin (C.length + 2)) =
                  r.castSucc := by
                apply Fin.ext
                rfl
              rw [hridx]
              simp only [Fin.lastCases_castSucc]
              rw [hiatt]
              congr 1
              exact hri.symm
            · obtain ⟨a, ha⟩ := C.attaches q
              refine ⟨a, ?_⟩
              simp only [Fin.lastCases_castSucc]
              have hqidx : (q.castSucc.succ : Fin (C.length + 2)) =
                  (q.succ : Fin (C.length + 1)).castSucc := by
                apply Fin.ext
                rfl
              let aa : Fin (C.length + 1) := ⟨a.val, by omega⟩
              have haidx : (Fin.castLT a (by omega) : Fin (C.length + 2)) =
                  aa.castSucc := by
                apply Fin.ext
                rfl
              have haold : (Fin.castLT a (by omega) : Fin (C.length + 1)) = aa := by
                apply Fin.ext
                rfl
              rw [hqidx, haidx]
              simp only [Fin.lastCases_castSucc]
              simpa [haold] using ha
        }
      refine ⟨D, ?_, ?_, ?_, Or.inl rfl⟩
      · intro q
        refine Fin.lastCases ?_ (fun q => ?_) q
        · intro hq
          obtain ⟨a, c, hcolor, hmissing⟩ := hTash j (by omega)
          have hav : T.vertex (Fin.castLT a
              (Nat.lt_trans a.isLt (Nat.succ_lt_succ j.isLt))) ∈
              TreeSequenceVertexSet C := prior a (by omega)
          obtain ⟨s, hsC, hsa⟩ := Finset.mem_image.mp
            (show T.vertex (Fin.castLT a
                (Nat.lt_trans a.isLt (Nat.succ_lt_succ j.isLt))) ∈
              Finset.image C.vertex Finset.univ from by
                simpa [TreeSequenceVertexSet] using hav)
          refine ⟨s, c, ?_, ?_⟩
          · simpa [D, Fin.lastCases] using hcolor
          · have hsidx : (Fin.castLT s (by omega) : Fin (C.length + 2)) =
                s.castSucc := by
              apply Fin.ext
              rfl
            simpa [D, Fin.lastCases, hsidx, hsa] using hmissing
        · intro hq
          have hqold : 1 ≤ q.val := by exact hq
          obtain ⟨a, c, hcolor, hmissing⟩ := hC q hqold
          refine ⟨a, c, ?_, ?_⟩
          · simpa [D, Fin.lastCases] using hcolor
          · have hqidx : (q.castSucc.succ : Fin (C.length + 2)) =
                (q.succ : Fin (C.length + 1)).castSucc := by
              apply Fin.ext
              rfl
            let aa : Fin (C.length + 1) := ⟨a.val, by omega⟩
            have haidx : (Fin.castLT a (by omega) : Fin (C.length + 2)) =
                aa.castSucc := by
              apply Fin.ext
              rfl
            have haold : (Fin.castLT a (by omega) : Fin (C.length + 1)) = aa := by
              apply Fin.ext
              rfl
            simpa [D, Fin.lastCases, hqidx, haidx, haold] using hmissing
      · change ∃ hlen : C.length ≤ D.length,
          (∀ i : Fin (C.length + 1),
            D.vertex (Fin.castLE (Nat.succ_le_succ hlen) i) = C.vertex i) ∧
          ∀ jx : Fin C.length, D.edge (Fin.castLE hlen jx) = C.edge jx
        refine ⟨by dsimp [D]; omega, ?_, ?_⟩
        · intro i
          have hi : Fin.castLE (Nat.succ_le_succ (Nat.le_succ C.length)) i =
              i.castSucc := by
            apply Fin.ext
            rfl
          rw [hi]
          simp [D, Fin.lastCases_castSucc]
        · intro jx
          have hjx : Fin.castLE (Nat.le_succ C.length) jx =
              jx.castSucc := by
            apply Fin.ext
            rfl
          rw [hjx]
          simp [D, Fin.lastCases_castSucc]
      · intro v hv
        change v ∈ Finset.univ.image D.vertex at hv
        obtain ⟨a, -, haeq⟩ := Finset.mem_image.mp hv
        rw [← haeq]
        by_cases ha : a.val ≤ C.length
        · let b : Fin (C.length + 1) := ⟨a.val, by omega⟩
          have haidx : a = b.castSucc := by
            apply Fin.ext
            rfl
          have hb : C.vertex b ∈ TreeSequenceVertexSet C := by
            change C.vertex b ∈ Finset.univ.image C.vertex
            exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
          have hc : C.vertex b ∈ X := hCX hb
          simpa [D, Fin.lastCases, haidx] using hc
        · have halt : a.val < C.length + 2 := by simpa [D] using a.isLt
          have haeq : a = Fin.last (C.length + 1) := by
            apply Fin.ext
            simp
            omega
          have hnew : T.vertex j.succ ∈ X := by
            change T.vertex j.succ ∈ Finset.univ.image T.vertex
            exact Finset.mem_image.mpr ⟨j.succ, Finset.mem_univ _, rfl⟩
          simpa [D, Fin.lastCases, haeq] using hnew
  have initial_trans : ∀ (A B C : TreeSequence G e0),
      TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B C →
      TreeSequenceInitialSegment A C := by
    intro A B C hab hbc
    rcases hab with ⟨hab, hvab, heab⟩
    rcases hbc with ⟨hbc, hvbc, hebc⟩
    refine ⟨le_trans hab hbc, ?_, ?_⟩
    · intro i
      have hi : Fin.castLE (Nat.succ_le_succ (le_trans hab hbc)) i =
          Fin.castLE (Nat.succ_le_succ hbc)
            (Fin.castLE (Nat.succ_le_succ hab) i) := by
        apply Fin.ext
        rfl
      rw [hi, hvbc]
      exact hvab i
    · intro j
      have hj : Fin.castLE (le_trans hab hbc) j =
          Fin.castLE hbc (Fin.castLE hab j) := by
        apply Fin.ext
        rfl
      rw [hj, hebc]
      exact heab j
  have vertex_card : ∀ U : TreeSequence G e0,
      (TreeSequenceVertexSet U).card = U.length + 1 := by
    intro U
    rw [TreeSequenceVertexSet,
      Finset.card_image_of_injective Finset.univ U.vertex_injective,
      Finset.card_univ, Fintype.card_fin]
  let measure : TreeSequence G e0 → ℕ := fun U =>
    X.card - (TreeSequenceVertexSet U).card
  have finish : ∀ m : ℕ, ∀ C : TreeSequence G e0,
      measure C = m → TashkinovTree G e0 phi C →
      TreeSequenceVertexSet C ⊆ X → TreeSequenceInitialSegment S C →
      ∃ R : TreeSequence G e0, TashkinovTree G e0 phi R ∧
        TreeSequenceVertexSet R = X ∧ TreeSequenceInitialSegment S R := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro C hm hC hCX hSC
      by_cases heq : TreeSequenceVertexSet C = X
      · exact ⟨C, hC, heq, hSC⟩
      · obtain ⟨D, hD, hCD, hDX, hlenOr⟩ := extend C hC hCX
        have hcardC : (TreeSequenceVertexSet C).card = C.length + 1 :=
          vertex_card C
        have hcardD : (TreeSequenceVertexSet D).card = D.length + 1 :=
          vertex_card D
        have hlen : C.length + 1 = D.length := by
          rcases hlenOr with hlen | heqC
          · exact hlen.symm
          · exact (heq heqC).elim
        have hmeasure : measure D < m := by
          have hX : (TreeSequenceVertexSet D).card ≤ X.card :=
            Finset.card_le_card hDX
          have hpos : 1 ≤ C.length + 1 := by omega
          simp [measure, hcardC, hcardD, hlen] at hm ⊢
          omega
        obtain ⟨R, hR, hRX, hSR⟩ := ih _ hmeasure D rfl hD hDX
          (initial_trans S C D hSC hCD)
        exact ⟨R, hR, hRX, hSR⟩
  obtain ⟨R, hR, hRX, hSR⟩ := finish (measure S) S rfl hS hsub
    ⟨le_rfl, (by intro i; rfl), (by intro j; rfl)⟩
  exact ⟨R, hR, hRX, hSR⟩
