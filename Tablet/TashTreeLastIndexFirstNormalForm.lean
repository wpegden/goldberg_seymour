import Tablet.ColoredVertexSetElementary
import Tablet.KTriple
import Tablet.MissingColorIncidenceEndpoint
import Tablet.MissingColors
import Tablet.TashTreeBadPair
import Tablet.TashTreeControlledInterchange
import Tablet.TashTreeDisjointComponentNormalization
import Tablet.TashTreeFourUnusedColors
import Tablet.TashTreeLastIndexIntersectionShortening
import Tablet.TashTreeMinimumBadPair
import Tablet.TashTreePathIndex
import Tablet.TashTreeProperPrefixElementary
import Tablet.TashTreeSuffixPath
import Tablet.TashkinovTree
import Tablet.TreeFreeColors
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequencePrefix
import Tablet.TreeUsedColors
import Tablet.TwoColorComponent
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapMissingBehavior

-- [TABLET NODE: TashTreeLastIndexFirstNormalForm]
theorem TashTreeLastIndexFirstNormalForm {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hlast : TashTreePathIndex G T = T.length) :
    ∃ (phi₁ : PartialEdgeColoring E k) (beta : Fin k)
        (j : Fin (T.length + 1)),
      TashTreeMinimumBadPair G k e0 phi₁ T ∧
        j.val + 2 ≤ T.length ∧
        beta ∈ MissingColors G phi₁ (T.vertex j) ∧
        beta ∈ MissingColors G phi₁ (T.vertex (Fin.last T.length)) ∧
        beta ∉ TreeUsedColors phi₁ T := by
-- BODY
  classical
  have hlen : 3 ≤ T.length := by
    have hi : TashTreePathIndex G T ≤ T.length := by
      rw [hlast]
    omega
  let P : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - 2) (by omega) (by omega)
  have hPlen : P.length = T.length - 2 := rfl
  have hPelem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet P) := by
    apply TashTreeProperPrefixElementary G k e0 phi T P hmin
    · refine ⟨by rw [hPlen]; omega, ?_, ?_⟩
      · intro i
        rfl
      · intro i
        rfl
    · rw [hPlen]
      omega
  have hfour : 4 ≤ (TreeFreeColors phi P).card := by
    simpa [P] using TashTreeFourUnusedColors G k e0 phi T hmin
      (T.length - 2) (by omega) (by omega)
  let P1 : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - 1) (by omega) (by omega)
  have hP1len : P1.length = T.length - 1 := rfl
  have hP1elem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet P1) := by
    apply TashTreeProperPrefixElementary G k e0 phi T P1 hmin
    · refine ⟨by rw [hP1len]; omega, ?_, ?_⟩
      · intro i
        rfl
      · intro i
        rfl
    · rw [hP1len]
      omega
  have hbad : ¬ ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) := hmin.1.2.2
  have hcommon : ∃ u ∈ TreeSequenceVertexSet T, ∃ v ∈ TreeSequenceVertexSet T,
      u ≠ v ∧ ∃ c, c ∈ MissingColors G phi u ∧ c ∈ MissingColors G phi v := by
    by_contra hneg
    push_neg at hneg
    apply hbad
    intro u hu v hv huv
    rw [Finset.disjoint_left]
    intro c hcu hcv
    exact hneg u hu v hv huv c hcu hcv
  rcases hcommon with ⟨u, hu, v, hv, huv, beta, hbu, hbv⟩
  have huindex : ∃ i : Fin (T.length + 1), T.vertex i = u := by
    simpa [TreeSequenceVertexSet] using hu
  have hvindex : ∃ i : Fin (T.length + 1), T.vertex i = v := by
    simpa [TreeSequenceVertexSet] using hv
  rcases huindex with ⟨i, rfl⟩
  rcases hvindex with ⟨j, rfl⟩
  have hbetaLast : beta ∈ MissingColors G phi (T.vertex (Fin.last T.length)) := by
    have hil : i.val ≤ T.length := Nat.le_of_lt_succ i.isLt
    have hjl : j.val ≤ T.length := Nat.le_of_lt_succ j.isLt
    by_cases hi : i.val = T.length
    · have hi' : i = Fin.last T.length := Fin.ext (by simpa using hi)
      simpa [hi'] using hbu
    · by_cases hj : j.val = T.length
      · have hj' : j = Fin.last T.length := Fin.ext (by simpa using hj)
        simpa [hj'] using hbv
      · exfalso
        have hiP1 : T.vertex i ∈ TreeSequenceVertexSet P1 := by
          rw [TreeSequenceVertexSet]
          let ip : Fin (P1.length + 1) := ⟨i.val, by rw [hP1len]; omega⟩
          refine Finset.mem_image.mpr ⟨ip, Finset.mem_univ _, ?_⟩
          rfl
        have hjP1 : T.vertex j ∈ TreeSequenceVertexSet P1 := by
          rw [TreeSequenceVertexSet]
          let jp : Fin (P1.length + 1) := ⟨j.val, by rw [hP1len]; omega⟩
          refine Finset.mem_image.mpr ⟨jp, Finset.mem_univ _, ?_⟩
          rfl
        have hd := hP1elem hiP1 hjP1 huv
        exact (Finset.disjoint_left.mp hd) hbu hbv
  have hbetaIndex : ∃ j : Fin (T.length + 1), j.val < T.length ∧
      beta ∈ MissingColors G phi (T.vertex j) := by
    by_cases hi : i.val < T.length
    · exact ⟨i, hi, hbu⟩
    · have hjlt : j.val < T.length := by
        have hjle : j.val ≤ T.length := Nat.le_of_lt_succ j.isLt
        have hjne : j.val ≠ T.length := by
          intro hjlast
          have hiLast : i.val = T.length := by omega
          have hij : i = j := Fin.ext (by simpa [hjlast, hiLast])
          exact huv (congrArg T.vertex hij)
        exact Nat.lt_of_le_of_ne hjle hjne
      exact ⟨j, hjlt, hbv⟩
  rcases hbetaIndex with ⟨j, hj, hbj⟩
  let r₁ : Fin T.length := ⟨T.length - 2, by omega⟩
  let r₂ : Fin T.length := ⟨T.length - 1, by omega⟩
  let d₁ : Fin k := (phi (T.edge r₁)).getD beta
  let d₂ : Fin k := (phi (T.edge r₂)).getD beta
  have hfree : ∃ alpha : Fin k, alpha ∈ TreeFreeColors phi P ∧
      alpha ≠ beta ∧ alpha ≠ d₁ ∧ alpha ≠ d₂ := by
    by_contra! hn
    have hs : TreeFreeColors phi P ⊆ ({beta, d₁, d₂} : Finset (Fin k)) := by
      intro c hc
      by_cases hcb : c = beta
      · simp [hcb]
      by_cases hd1 : c = d₁
      · simp [hd1]
      simp [hn c hc hcb hd1]
    have hc : (TreeFreeColors phi P).card ≤ 3 := by
      have hh := Finset.card_le_card hs
      calc
        _ ≤ ({beta, d₁, d₂} : Finset (Fin k)).card := hh
        _ ≤ 3 := Finset.card_le_three
    omega
  rcases hfree with ⟨alpha, halphaFree, hab, had₁, had₂⟩
  have halphaMissing : ∃ m : Fin (T.length + 1), m.val ≤ T.length - 2 ∧
      alpha ∈ MissingColors G phi (T.vertex m) := by
    rw [TreeFreeColors] at halphaFree
    have hm : alpha ∈ TreeMissingColors phi P := (Finset.mem_sdiff.mp halphaFree).1
    rw [TreeMissingColors] at hm
    rcases Finset.mem_biUnion.mp hm with ⟨x, hx, hxm⟩
    rw [TreeSequenceVertexSet] at hx
    rcases Finset.mem_image.mp hx with ⟨m, -, rfl⟩
    let mt : Fin (T.length + 1) :=
      Fin.castLE (by rw [hPlen]; omega) m
    refine ⟨mt, ?_, ?_⟩
    · dsimp [mt]
      rw [hPlen] at m
      omega
    · simpa [mt, P, TreeSequencePrefix] using hxm
  rcases halphaMissing with ⟨m, hm, ham⟩
  by_cases hj2 : j.val + 2 ≤ T.length
  · have hbetaTree : beta ∈ TreeMissingColors phi P := by
      rw [TreeMissingColors]
      apply Finset.mem_biUnion.mpr
      refine ⟨T.vertex j, ?_, hbj⟩
      rw [TreeSequenceVertexSet]
      let jp : Fin (P.length + 1) := ⟨j.val, by rw [hPlen]; omega⟩
      exact Finset.mem_image.mpr ⟨jp, Finset.mem_univ _, rfl⟩
    have hprefix : TreeSequenceInitialSegment P T := by
      refine ⟨by rw [hPlen]; omega, ?_, ?_⟩
      · intro x
        rfl
      · intro x
        rfl
    have hlastOutside : T.vertex (Fin.last T.length) ∉ TreeSequenceVertexSet P := by
      rw [TreeSequenceVertexSet]
      intro hh
      rcases Finset.mem_image.mp hh with ⟨x, -, hx⟩
      have hxv : x.val ≤ T.length - 2 := by rw [hPlen] at x; omega
      have heq : x.val = T.length := by
        apply T.vertex_injective at hx
        simpa [Fin.castLE] using congrArg Fin.val hx
      omega
    let C := TwoColorComponent G phi alpha beta
      (Sum.inl (T.vertex (Fin.last T.length)))
    have hvertices : ∀ q : Fin (T.length + 1), q.val ≤ T.length - 2 →
        Sum.inl (T.vertex q) ∉ C := by
      intro q hqv hqC
      have hmeet : ∃ u ∈ TreeSequenceVertexSet P,
          Sum.inl u ∈ TwoColorComponent G phi alpha beta
            (Sum.inl (T.vertex (Fin.last T.length))) := by
        refine ⟨T.vertex q, ?_, ?_⟩
        · rw [TreeSequenceVertexSet]
          let qq : Fin (P.length + 1) := ⟨q.val, by rw [hPlen]; omega⟩
          exact Finset.mem_image.mpr ⟨qq, Finset.mem_univ _, rfl⟩
        · exact hqC
      have hAlphaTree : alpha ∈ TreeMissingColors phi P := by
        rw [TreeFreeColors] at halphaFree
        exact (Finset.mem_sdiff.mp halphaFree).1
      have hfalse := TashTreeLastIndexIntersectionShortening G k e0 phi T P
        hmin hlast hprefix (by rw [hPlen]; omega) alpha beta hab
        hAlphaTree hbetaTree hbetaLast
        hlastOutside hmeet
      exact hfalse.elim
    have hedges : ∀ r : Fin T.length, r.val < T.length - 2 →
        Sum.inr (T.edge r) ∉ C := by
      intro r hr heC
      rcases T.attaches r with ⟨i, hi⟩
      let q : Fin (T.length + 1) := ⟨i.val, by omega⟩
      have hinc : Incident G (T.vertex q) (T.edge r) := by
        have hqeq : q = Fin.castLT i (Nat.lt_trans i.isLt
            (Nat.succ_lt_succ r.isLt)) := Fin.ext (by rfl)
        rw [hqeq]
        rw [Incident, hi]
        simp
      by_cases hcol : phi (T.edge r) = some alpha ∨
          phi (T.edge r) = some beta
      · have hvC : Sum.inl (T.vertex q) ∈ C := by
          change Sum.inl (T.vertex q) ∈
            ((TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk
              (Sum.inl (T.vertex (Fin.last T.length)))).supp
          rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
          have hadj : (TwoColorIncidenceGraph G phi alpha beta).Adj
              (Sum.inl (T.vertex q)) (Sum.inr (T.edge r)) := by
            simpa [TwoColorIncidenceGraph, hinc, hcol, q]
          exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            hadj).trans heC
        exact hvertices q (by dsimp [q]; omega) hvC
      · let H := TwoColorIncidenceGraph G phi alpha beta
        have hno : ∀ x, H.Reachable (Sum.inr (T.edge r)) x →
            x = Sum.inr (T.edge r) := by
          intro x hx
          rw [H.reachable_iff_reflTransGen] at hx
          induction hx with
          | refl => rfl
          | tail h ha ih =>
            subst ih
            rename_i c
            cases c <;> simp [H, TwoColorIncidenceGraph, hcol] at ha
        have hrch : H.Reachable (Sum.inr (T.edge r))
            (Sum.inl (T.vertex (Fin.last T.length))) := by
          apply SimpleGraph.ConnectedComponent.eq.mp
          exact heC
        have heq := hno _ hrch
        cases heq
    let p : Fin (T.length + 1) := ⟨T.length - 2, by omega⟩
    have hnorm := TashTreeDisjointComponentNormalization G k e0 phi T hmin
      p m j (by dsimp [p]; omega) (by dsimp [p]; exact hm)
      (by dsimp [p]; omega) alpha beta hab ham hbj hbetaLast hvertices hedges
    dsimp only at hnorm
    refine ⟨TwoColorComponentSwap G phi alpha beta
      (Sum.inl (T.vertex (Fin.last T.length))), alpha, m, ?_, ?_, ?_, ?_, ?_⟩
    · exact hnorm.1
    · omega
    · exact hnorm.2.2.1
    · exact hnorm.2.2.2
    · intro hused
      rw [TreeUsedColors] at hused
      rcases Finset.mem_filter.mp hused with ⟨-, ⟨r, hr, he⟩⟩
      by_cases hsmall : r.val < T.length - 2
      · have hfix := hnorm.2.1 r hsmall
        have hnot : phi (T.edge r) ≠ some alpha := by
          intro heq
          have hnotP : alpha ∉ TreeUsedColors phi P :=
            (Finset.mem_sdiff.mp (by simpa [TreeFreeColors] using halphaFree)).2
          apply hnotP
          rw [TreeUsedColors]
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          refine ⟨⟨r.val, by rw [hPlen]; omega⟩, ?_, ?_⟩
          · omega
          · change phi (T.edge r) = some alpha
            exact heq
        exact hnot (hfix ▸ he)
      · have hrlarge : T.length - 2 ≤ r.val := by omega
        by_cases hrone : r.val = T.length - 2
        · have hre : r = r₁ := Fin.ext (by simpa [r₁] using hrone)
          subst r
          have hphiAlpha : phi (T.edge r₁) ≠ some alpha := by
            intro hh
            apply had₁
            simp [d₁, hh]
          have hout : Sum.inr (T.edge r₁) ∉ C := by
            rcases T.attaches r₁ with ⟨i, hi⟩
            let q : Fin (T.length + 1) := ⟨i.val, by omega⟩
            have hinc : Incident G (T.vertex q) (T.edge r₁) := by
              have hqeq : q = Fin.castLT i (Nat.lt_trans i.isLt
                  (Nat.succ_lt_succ r₁.isLt)) := Fin.ext (by rfl)
              rw [hqeq, Incident, hi]
              simp
            by_cases hcol : phi (T.edge r₁) = some alpha ∨
                phi (T.edge r₁) = some beta
            · intro hec
              have hvC : Sum.inl (T.vertex q) ∈ C := by
                change Sum.inl (T.vertex q) ∈
                  ((TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk
                    (Sum.inl (T.vertex (Fin.last T.length)))).supp
                rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
                have hadj : (TwoColorIncidenceGraph G phi alpha beta).Adj
                    (Sum.inl (T.vertex q)) (Sum.inr (T.edge r₁)) := by
                  simpa [TwoColorIncidenceGraph, hinc, hcol, q]
                exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                  hadj).trans hec
              exact hvertices q (by dsimp [q]; omega) hvC
            · intro hec
              let H := TwoColorIncidenceGraph G phi alpha beta
              have hno : ∀ x, H.Reachable (Sum.inr (T.edge r₁)) x →
                  x = Sum.inr (T.edge r₁) := by
                intro x hx
                rw [H.reachable_iff_reflTransGen] at hx
                induction hx with
                | refl => rfl
                | tail h ha ih =>
                  subst ih
                  rename_i c
                  cases c <;> simp [H, TwoColorIncidenceGraph, hcol] at ha
              have hrch : H.Reachable (Sum.inr (T.edge r₁))
                  (Sum.inl (T.vertex (Fin.last T.length))) := by
                apply SimpleGraph.ConnectedComponent.eq.mp
                exact hec
              have heq := hno _ hrch
              cases heq
          by_cases hc : Sum.inr (T.edge r₁) ∈ C
          · exact hout hc
          · simp [C, TwoColorComponentSwap, hc] at he
            exact hphiAlpha he
        · have hrlt : r.val < T.length := r.isLt
          have hre : r = r₂ := by
            apply Fin.ext
            have hrge : T.length - 2 ≤ r.val := hrlarge
            have hrstrict : T.length - 2 < r.val :=
              Nat.lt_of_le_of_ne hrge (Ne.symm hrone)
            dsimp [r₂]
            omega
          subst r
          have hphiAlpha : phi (T.edge r₂) ≠ some alpha := by
            intro hh
            apply had₂
            simp [d₂, hh]
          have hphiBeta : phi (T.edge r₂) ≠ some beta := by
            intro hh
            rcases T.attaches r₂ with ⟨i, hi⟩
            have hs : r₂.succ = Fin.last T.length := by
              apply Fin.ext
              dsimp [r₂]
              omega
            have hinc : Incident G (T.vertex (Fin.last T.length)) (T.edge r₂) := by
              rw [Incident, hi]
              simp [hs]
            have hp : beta ∉ PresentColors G phi (T.vertex (Fin.last T.length)) := by
              simpa [MissingColors] using hbetaLast
            apply hp
            rw [PresentColors]
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, T.edge r₂, hinc, hh⟩
          by_cases hc : Sum.inr (T.edge r₂) ∈ C
          · simp [C, TwoColorComponentSwap, hc, hphiAlpha, hphiBeta] at he
          · simp [C, TwoColorComponentSwap, hc] at he
            exact hphiAlpha he
  · have hjlast : j.val = T.length - 1 := by omega
    let pen : Fin (T.length + 1) := ⟨T.length - 1, by omega⟩
    have hbjpen : beta ∈ MissingColors G phi (T.vertex pen) := by
      have hjEq : j = pen := by
        apply Fin.ext
        dsimp [pen]
        exact hjlast
      rw [← hjEq]
      exact hbj
    have hbetaUnused : TreeColorUnusedThrough phi T beta pen := by
      intro s hs1 hslt hcolor
      rcases hmin.1.2.1 s hs1 with ⟨i, c, hc, hmiss⟩
      have hcb : beta = c := by simpa [hcolor] using hc
      subst c
      have hsmem : T.vertex (Fin.castLT i
          (Nat.lt_trans i.isLt (Nat.succ_lt_succ s.isLt))) ∈
          TreeSequenceVertexSet P1 := by
        rw [TreeSequenceVertexSet]
        refine Finset.mem_image.mpr ⟨⟨i.val, by rw [hP1len]; omega⟩,
          Finset.mem_univ _, ?_⟩
        rfl
      have hpmem : T.vertex pen ∈ TreeSequenceVertexSet P1 := by
        rw [TreeSequenceVertexSet]
        refine Finset.mem_image.mpr ⟨⟨T.length - 1, by rw [hP1len]; omega⟩,
          Finset.mem_univ _, rfl⟩
      have hne : T.vertex (Fin.castLT i
          (Nat.lt_trans i.isLt (Nat.succ_lt_succ s.isLt))) ≠ T.vertex pen := by
        intro heq
        have hv := T.vertex_injective heq
        have hvv := congrArg Fin.val hv
        dsimp [pen] at hvv
        have his : i.val ≤ s.val := Nat.le_of_lt_succ i.isLt
        have hiVal : (Fin.castLT i
            (Nat.lt_trans i.isLt (Nat.succ_lt_succ s.isLt))).val = i.val := rfl
        omega
      exact (Finset.disjoint_left.mp (hP1elem hsmem hpmem hne)) hmiss hbjpen
    have halphaUnused : TreeColorUnusedThrough phi T alpha pen := by
      intro s hs1 hslt hcolor
      have hslt' : s.val < T.length - 1 := by simpa [pen] using hslt
      by_cases hs : s.val = T.length - 2
      · have heq : s = r₁ := by
          apply Fin.ext
          dsimp [r₁]
          exact hs
        rw [heq] at hcolor
        exact had₁ (by simpa [d₁, hcolor])
      · have hslt2 : s.val < T.length - 2 := by omega
        have hnotP : alpha ∉ TreeUsedColors phi P :=
          (Finset.mem_sdiff.mp (by simpa [TreeFreeColors] using halphaFree)).2
        apply hnotP
        rw [TreeUsedColors]
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ⟨⟨s.val, by rw [hPlen]; omega⟩, ?_, ?_⟩⟩
        · exact hs1
        · change phi (T.edge s) = some alpha
          exact hcolor
    have hm_lt_pen : m.val < pen.val := by
      dsimp [pen]
      omega
    have hswap := TashTreeControlledInterchange G k e0 phi T hmin
      ⟨m, by omega⟩ pen hm_lt_pen (by dsimp [pen]; omega)
      alpha beta hab ham hbjpen halphaUnused hbetaUnused
    dsimp only at hswap
    let phi' := TwoColorComponentSwap G phi alpha beta
      (Sum.inl (T.vertex pen))
    have hmin' : TashTreeMinimumBadPair G k e0 phi' T := hswap.2.2.2.2.2.2.2.2
    have hlastOutside : Sum.inl (T.vertex (Fin.last T.length)) ∉
        TwoColorComponent G phi alpha beta (Sum.inl (T.vertex pen)) := by
      intro hin
      obtain ⟨a, b, path, hpath, hsupport⟩ :=
        TwoColorComponentSpanningPath G phi alpha beta
          hmin.1.1.2.2.2.1 (Sum.inl (T.vertex pen))
      have hsupp {x : Sum V E} (hx : x ∈
          TwoColorComponent G phi alpha beta (Sum.inl (T.vertex pen))) :
          x ∈ path.support := by
        change x ∈ {y | y ∈ path.support}
        rw [hsupport]
        exact hx
      have hend {x : Sum V E} (hx : x ∈
          TwoColorComponent G phi alpha beta (Sum.inl (T.vertex pen)))
          (hd : Set.Subsingleton
            ((TwoColorIncidenceGraph G phi alpha beta).neighborSet x)) :
          x = a ∨ x = b := by
        by_contra hn
        push_neg at hn
        exact (hpath.isTrail.not_mem_support_of_subsingleton_neighborSet
          hn.1 hn.2 hd) (hsupp hx)
      have hdeg : Set.Subsingleton
          ((TwoColorIncidenceGraph G phi alpha beta).neighborSet
            (Sum.inl (T.vertex (Fin.last T.length)))) := by
        letI : Fintype ((TwoColorIncidenceGraph G phi beta alpha).neighborSet
            (Sum.inl (T.vertex (Fin.last T.length)))) := Fintype.ofFinite _
        have hd := MissingColorIncidenceEndpoint G phi beta alpha hab.symm
          hmin.1.1.2.2.2.1 (T.vertex (Fin.last T.length)) hbetaLast
        intro x hx y hy
        have hx' := (SimpleGraph.mem_neighborFinset
          (TwoColorIncidenceGraph G phi beta alpha)
          (Sum.inl (T.vertex (Fin.last T.length))) x).2
          (by cases x <;> simpa [TwoColorIncidenceGraph, or_comm] using hx)
        have hy' := (SimpleGraph.mem_neighborFinset
          (TwoColorIncidenceGraph G phi beta alpha)
          (Sum.inl (T.vertex (Fin.last T.length))) y).2
          (by cases y <;> simpa [TwoColorIncidenceGraph, or_comm] using hy)
        exact (Finset.card_le_one.mp (by
          rw [SimpleGraph.card_neighborFinset_eq_degree]
          exact hd)) x hx' y hy'
      have hmEnd := hend hswap.2.1 hswap.2.2.1
      have hpEnd := hend (by
        change Sum.inl (T.vertex pen) ∈
          ((TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk
            (Sum.inl (T.vertex pen))).supp
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff]) hswap.2.2.2.1
      have hmLast : (Sum.inl (T.vertex ⟨m.val, by omega⟩) : Sum V E) ≠
          Sum.inl (T.vertex (Fin.last T.length)) := by
        intro hh
        have hv : T.vertex ⟨m.val, by omega⟩ = T.vertex (Fin.last T.length) := by
          simpa using hh
        have hvv := congrArg Fin.val (T.vertex_injective hv)
        dsimp at hvv
        have hmval : m.val ≤ T.length - 2 := hm
        have hmindex : (⟨m.val, by omega⟩ : Fin (T.length + 1)).val = m.val := rfl
        have hmlast : (Fin.last T.length).val = T.length := rfl
        omega
      have hpLast : (Sum.inl (T.vertex pen) : Sum V E) ≠
          Sum.inl (T.vertex (Fin.last T.length)) := by
        intro hh
        have hv : T.vertex pen = T.vertex (Fin.last T.length) := by simpa using hh
        have hvv := congrArg Fin.val (T.vertex_injective hv)
        dsimp [pen] at hvv
        omega
      have hmPen : (Sum.inl (T.vertex ⟨m.val, by omega⟩) : Sum V E) ≠
          Sum.inl (T.vertex pen) := by
        intro hh
        have hv : T.vertex ⟨m.val, by omega⟩ = T.vertex pen := by simpa using hh
        have hvv := congrArg Fin.val (T.vertex_injective hv)
        dsimp [pen] at hvv
        omega
      have endpoint {x : Sum V E} (hx : x = a ∨ x = b) :
          x = Sum.inl (T.vertex ⟨m.val, by omega⟩) ∨
          x = Sum.inl (T.vertex pen) := by
        rcases hmEnd with hma | hmb <;> rcases hpEnd with hpa | hpb
        · exact False.elim (hmPen (hma.trans hpa.symm))
        · rcases hx with hxa | hxb
          · exact Or.inl (hxa.trans hma.symm)
          · exact Or.inr (hxb.trans hpb.symm)
        · rcases hx with hxa | hxb
          · exact Or.inr (hxa.trans hpa.symm)
          · exact Or.inl (hxb.trans hmb.symm)
        · exact False.elim (hmPen (hmb.trans hpb.symm))
      rcases endpoint (hend hin hdeg) with hml | hpl
      · exact hmLast hml.symm
      · exact hpLast hpl.symm
    have hbetaLast' : beta ∈ MissingColors G phi'
        (T.vertex (Fin.last T.length)) := by
      have hm := TwoColorComponentSwapMissingBehavior G phi alpha beta hab
        hmin.1.1.2.2.2.1 (Sum.inl (T.vertex pen))
      dsimp only at hm
      exact (hm.1 _ hlastOutside) ▸ hbetaLast
    have hpenAlpha : phi (T.edge r₂) ≠ some alpha := by
      intro hh
      apply had₂
      simp [d₂, hh]
    have hpenBeta : phi (T.edge r₂) ≠ some beta := by
      intro hh
      rcases T.attaches r₂ with ⟨i, hi⟩
      have hs : r₂.succ = Fin.last T.length := by
        apply Fin.ext
        dsimp [r₂]
        omega
      have hinc : Incident G (T.vertex (Fin.last T.length)) (T.edge r₂) := by
        rw [Incident, hi]
        simp [hs]
      have hp : beta ∉ PresentColors G phi (T.vertex (Fin.last T.length)) := by
        simpa [MissingColors] using hbetaLast
      apply hp
      rw [PresentColors]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, T.edge r₂, hinc, hh⟩
    refine ⟨phi', beta, m, hmin', by omega, hswap.2.2.2.2.1, hbetaLast', ?_⟩
    intro hused
    rw [TreeUsedColors] at hused
    rcases Finset.mem_filter.mp hused with ⟨-, ⟨s, hs1, he⟩⟩
    have hslt : s.val < T.length - 1 := by
      by_contra hn
      have hsval : s.val = T.length - 1 := by omega
      have hsEq : s = r₂ := by
        apply Fin.ext
        dsimp [r₂]
        exact hsval
      rw [hsEq] at he
      have hold : phi (T.edge r₂) = some beta := by
        simpa [phi', TwoColorComponentSwap, hpenAlpha, hpenBeta] using he
      exact hpenBeta hold
    have hfix := hswap.2.2.2.2.2.2.1 s hs1 hslt
    exact (by
      change TwoColorComponentSwap G phi alpha beta (Sum.inl (T.vertex pen))
        (T.edge s) = some beta at he
      rw [hfix] at he
      have : phi (T.edge s) = some beta := he
      exact hbetaUnused s hs1 hslt this)
