import Tablet.ColoredVertexSetElementary
import Tablet.KTriple
import Tablet.MissingColorIncidenceEndpoint
import Tablet.MissingColors
import Tablet.MissingColorsNonemptyOfMaximumDegree
import Tablet.PresentColors
import Tablet.TashTreeBadPair
import Tablet.TashTreeControlledInterchange
import Tablet.TashTreeMinimumBadPair
import Tablet.TashTreePathIndex
import Tablet.TashTreeProperPrefixElementary
import Tablet.TashTreeSuffixPath
import Tablet.TashkinovTree
import Tablet.TreeColorUnusedThrough
import Tablet.TreeSequence
import Tablet.TreeSequencePrefix
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwapMissingBehavior

-- [TABLET NODE: TashTreeSuffixAdvance]
theorem TashTreeSuffixAdvance {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (beta : Fin k) (i : Fin T.length)
    (hiSuffix : i.val = 0 ∨ TashTreePathIndex G T ≤ i.val)
    (hiNext : i.val + 1 < T.length)
    (hi : beta ∈ MissingColors G phi (T.vertex i.castSucc))
    (hlast : beta ∈ MissingColors G phi
      (T.vertex (Fin.last T.length))) :
    ∃ phi' : PartialEdgeColoring E k,
      TashTreeMinimumBadPair G k e0 phi' T ∧
      beta ∈ MissingColors G phi' (T.vertex i.succ) ∧
      beta ∈ MissingColors G phi'
        (T.vertex (Fin.last T.length)) := by
-- BODY
  classical
  have hdegree : MaximumDegree G + 1 ≤ k := hmin.1.1.2.2.1
  have hproper : IsProperEdgeColoring G phi := hmin.1.1.2.2.2.1
  have hTash : TashkinovTree G e0 phi T := hmin.1.2.1
  obtain ⟨gamma, hgamma⟩ :=
    MissingColorsNonemptyOfMaximumDegree G phi hdegree (T.vertex i.succ)

  have hprefixPositive : 1 ≤ i.val + 1 := by omega
  have hprefixLe : i.val + 1 ≤ T.length := Nat.le_of_lt hiNext
  let P := TreeSequencePrefix T (i.val + 1) hprefixPositive hprefixLe
  have hPprefix : TreeSequenceInitialSegment P T := by
    refine ⟨hprefixLe, ?_, ?_⟩
    · intro r
      rfl
    · intro r
      rfl
  have hPproper : P.length < T.length := by
    exact hiNext
  have hPelem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet P) :=
    TashTreeProperPrefixElementary G k e0 phi T P hmin hPprefix hPproper
  have hiP : T.vertex i.castSucc ∈ TreeSequenceVertexSet P := by
    rw [TreeSequenceVertexSet]
    apply Finset.mem_image.mpr
    let ip : Fin (P.length + 1) := ⟨i.val, by
      change i.val < i.val + 1 + 1
      omega⟩
    refine ⟨ip, Finset.mem_univ _, ?_⟩
    apply congrArg T.vertex
    apply Fin.ext
    rfl
  have hnextP : T.vertex i.succ ∈ TreeSequenceVertexSet P := by
    rw [TreeSequenceVertexSet]
    apply Finset.mem_image.mpr
    let jp : Fin (P.length + 1) := ⟨i.val + 1, by
      change i.val + 1 < i.val + 1 + 1
      omega⟩
    refine ⟨jp, Finset.mem_univ _, ?_⟩
    apply congrArg T.vertex
    apply Fin.ext
    rfl
  have hvertexNext : T.vertex i.castSucc ≠ T.vertex i.succ := by
    intro hv
    have hindex := congrArg Fin.val (T.vertex_injective hv)
    simp at hindex
  have hne : beta ≠ gamma := by
    intro hbg
    have hdisjoint := hPelem hiP hnextP hvertexNext
    exact (Finset.disjoint_left.mp hdisjoint) (by simpa [hbg] using hi) hgamma

  have hgammaUnused : TreeColorUnusedThrough phi T gamma i.succ := by
    intro r hrPositive hrBefore hrgamma
    have hrBefore' : r.val < i.val + 1 := by
      simpa only [Fin.val_succ] using hrBefore
    rcases hTash r hrPositive with ⟨w, c, hc, hw⟩
    have hcgamma : c = gamma := Option.some.inj (hc.symm.trans hrgamma)
    subst c
    let wt : Fin (T.length + 1) :=
      Fin.castLT w (Nat.lt_trans w.isLt (Nat.succ_lt_succ r.isLt))
    have hwP : T.vertex wt ∈ TreeSequenceVertexSet P := by
      rw [TreeSequenceVertexSet]
      apply Finset.mem_image.mpr
      let wp : Fin (P.length + 1) := ⟨w.val, by
        change w.val < i.val + 1 + 1
        omega⟩
      refine ⟨wp, Finset.mem_univ _, ?_⟩
      apply congrArg T.vertex
      apply Fin.ext
      rfl
    have hwne : T.vertex wt ≠ T.vertex i.succ := by
      intro hv
      have hwt_lt : wt < i.succ := by
        change w.val < i.val + 1
        omega
      exact (Fin.ne_of_lt hwt_lt) (T.vertex_injective hv)
    have hdisjoint := hPelem hwP hnextP hwne
    exact (Finset.disjoint_left.mp hdisjoint) hw hgamma

  have hbetaUnused : TreeColorUnusedThrough phi T beta i.succ := by
    by_cases hiZero : i.val = 0
    · intro r hrPositive hrBefore
      have hrBefore' : r.val < i.val + 1 := by
        simpa only [Fin.val_succ] using hrBefore
      omega
    · have hiPositive : 1 ≤ i.val := by omega
      have hiAtOrAfter : TashTreePathIndex G T ≤ i.val :=
        hiSuffix.resolve_left hiZero
      have hpathAtIndex :
          TashTreeSuffixPath G T (TashTreePathIndex G T) := by
        unfold TashTreePathIndex
        exact Nat.find_spec _
      intro r hrPositive hrBefore hrbeta
      have hrBefore' : r.val < i.val + 1 := by
        simpa only [Fin.val_succ] using hrBefore
      by_cases hrEarlier : r.val < i.val
      · rcases hTash r hrPositive with ⟨w, c, hc, hw⟩
        have hcbeta : c = beta := Option.some.inj (hc.symm.trans hrbeta)
        subst c
        let wt : Fin (T.length + 1) :=
          Fin.castLT w (Nat.lt_trans w.isLt (Nat.succ_lt_succ r.isLt))
        have hwP : T.vertex wt ∈ TreeSequenceVertexSet P := by
          rw [TreeSequenceVertexSet]
          apply Finset.mem_image.mpr
          let wp : Fin (P.length + 1) := ⟨w.val, by
            change w.val < i.val + 1 + 1
            omega⟩
          refine ⟨wp, Finset.mem_univ _, ?_⟩
          apply congrArg T.vertex
          apply Fin.ext
          rfl
        have hwne : T.vertex wt ≠ T.vertex i.castSucc := by
          intro hv
          have hwt_lt : wt < i.castSucc := by
            change w.val < i.val
            omega
          exact (Fin.ne_of_lt hwt_lt) (T.vertex_injective hv)
        have hdisjoint := hPelem hwP hiP hwne
        exact (Finset.disjoint_left.mp hdisjoint) hw hi
      · have hri : r = i := by
          apply Fin.ext
          omega
        subst r
        have hends := hpathAtIndex.2.2 i hiAtOrAfter
        have hincident : Incident G (T.vertex i.castSucc) (T.edge i) := by
          change T.vertex i.castSucc ∈ G.ends (T.edge i)
          rw [hends]
          exact Sym2.mem_mk_left _ _
        have hnotPresent : beta ∉ PresentColors G phi (T.vertex i.castSucc) := by
          simpa [MissingColors] using hi
        exact hnotPresent (by
          simp [PresentColors]
          exact ⟨T.edge i, hincident, hrbeta⟩)

  have hcontrolled := TashTreeControlledInterchange G k e0 phi T hmin
    i.castSucc i.succ (show i.castSucc < i.succ from Fin.castSucc_lt_succ)
    hiNext beta gamma hne hi hgamma hbetaUnused hgammaUnused
  dsimp only at hcontrolled
  rcases hcontrolled with
    ⟨hpath, hiComponent, hiSubsingleton, hnextSubsingleton,
      _hgammaAtI, hbetaAtNext, _hearly, _hlater, hminimum⟩
  let C := TwoColorComponent G phi beta gamma (Sum.inl (T.vertex i.succ))
  let phi' := TwoColorComponentSwap G phi beta gamma (Sum.inl (T.vertex i.succ))
  have hlastNeI : T.vertex (Fin.last T.length) ≠ T.vertex i.castSucc := by
    intro hv
    have hindex := congrArg Fin.val (T.vertex_injective hv)
    simp at hindex
    omega
  have hlastNeNext : T.vertex (Fin.last T.length) ≠ T.vertex i.succ := by
    intro hv
    have hindex := congrArg Fin.val (T.vertex_injective hv)
    simp at hindex
    omega
  have hlastSubsingleton : Set.Subsingleton
      ((TwoColorIncidenceGraph G phi beta gamma).neighborSet
        (Sum.inl (T.vertex (Fin.last T.length)))) := by
    letI : Fintype
        ((TwoColorIncidenceGraph G phi beta gamma).neighborSet
          (Sum.inl (T.vertex (Fin.last T.length)))) := Fintype.ofFinite _
    have hlastDegree := MissingColorIncidenceEndpoint G phi beta gamma hne
      hproper (T.vertex (Fin.last T.length)) hlast
    have hcard :
        ((TwoColorIncidenceGraph G phi beta gamma).neighborFinset
          (Sum.inl (T.vertex (Fin.last T.length)))).card ≤ 1 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      exact hlastDegree
    intro x hx y hy
    exact (Finset.card_le_one.mp hcard) x
      (by simpa [SimpleGraph.mem_neighborFinset] using hx) y
      (by simpa [SimpleGraph.mem_neighborFinset] using hy)
  obtain ⟨a, b, p, hp, hsupport⟩ :=
    TwoColorComponentSpanningPath G phi beta gamma hproper
      (Sum.inl (T.vertex i.succ))
  have support_of_component {x : Sum V E} (hx : x ∈ C) : x ∈ p.support := by
    change x ∈ {y | y ∈ p.support}
    rw [hsupport]
    exact hx
  have endpoint_of_subsingleton {x : Sum V E} (hxC : x ∈ C)
      (hxSub : Set.Subsingleton
        ((TwoColorIncidenceGraph G phi beta gamma).neighborSet x)) :
      x = a ∨ x = b := by
    by_contra hend
    push_neg at hend
    exact (hp.isTrail.not_mem_support_of_subsingleton_neighborSet
      hend.1 hend.2 hxSub) (support_of_component hxC)
  have hnextComponent : Sum.inl (T.vertex i.succ) ∈ C := by
    change Sum.inl (T.vertex i.succ) ∈
      ((TwoColorIncidenceGraph G phi beta gamma).connectedComponentMk
        (Sum.inl (T.vertex i.succ))).supp
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hiEnd := endpoint_of_subsingleton hiComponent hiSubsingleton
  have hnextEnd := endpoint_of_subsingleton hnextComponent hnextSubsingleton
  have endpoint_is_i_or_next {x : Sum V E} (hx : x = a ∨ x = b) :
      x = Sum.inl (T.vertex i.castSucc) ∨ x = Sum.inl (T.vertex i.succ) := by
    rcases hiEnd with hia | hib
    · rcases hnextEnd with hja | hjb
      · exact False.elim (hvertexNext (Sum.inl.inj (hia.trans hja.symm)))
      · rcases hx with hxa | hxb
        · exact Or.inl (hxa.trans hia.symm)
        · exact Or.inr (hxb.trans hjb.symm)
    · rcases hnextEnd with hja | hjb
      · rcases hx with hxa | hxb
        · exact Or.inr (hxa.trans hja.symm)
        · exact Or.inl (hxb.trans hib.symm)
      · exact False.elim (hvertexNext (Sum.inl.inj (hib.trans hjb.symm)))
  have hlastOutside : Sum.inl (T.vertex (Fin.last T.length)) ∉ C := by
    intro hlastComponent
    have hlastEnd := endpoint_of_subsingleton hlastComponent hlastSubsingleton
    rcases endpoint_is_i_or_next hlastEnd with hli | hln
    · exact hlastNeI (Sum.inl.inj hli)
    · exact hlastNeNext (Sum.inl.inj hln)
  have hbehavior := TwoColorComponentSwapMissingBehavior G phi beta gamma hne
    hproper (Sum.inl (T.vertex i.succ))
  dsimp only at hbehavior
  have hbetaAtLast : beta ∈ MissingColors G phi'
      (T.vertex (Fin.last T.length)) := by
    rw [hbehavior.1 _ hlastOutside]
    exact hlast
  exact ⟨phi', hminimum, hbetaAtNext, hbetaAtLast⟩

