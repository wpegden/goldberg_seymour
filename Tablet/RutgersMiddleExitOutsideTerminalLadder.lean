import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.CertifiedETTPredecessor
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.HkuMissingStoredMonotone
import Tablet.HkuParallelBoundaryStructure
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.LooplessMultigraph
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumDegree
import Tablet.MaximumProperty
import Tablet.MissingColors
import Tablet.OutsideTreeColorSwap
import Tablet.OutsideTreeColorSwapStable
import Tablet.ParallelExtensionColor
import Tablet.ParallelExtensionUndoStable
import Tablet.PresentColors
import Tablet.RutgersClosedPresentation
import Tablet.RutgersCounterexample
import Tablet.StableColoring
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TechnicalTheoremBase
import Tablet.TreeExitPath
import Tablet.TreeIncidentEdge
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeMissingColorsCardLowerBound
import Tablet.TreeSequence
import Tablet.TreeSequenceAdjoinEdge
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapDisjointPairGraph
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorPathComponent
import Tablet.sc2

-- [TABLET NODE: RutgersMiddleExitOutsideTerminalLadder]
theorem RutgersMiddleExitOutsideTerminalLadder
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (original : ExtendedTashkinovTree G k e0 input T generating)
    (hdegree : MaximumDegree G + 1 <= k)
    (hcurrentFour : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (current : ExtendedTashkinovTree G k e0 input' T' generating'),
      current.rounds = original.rounds -> MaximumProperty current ->
      let terminal : Fin (current.rounds + 1) := Fin.last current.rounds
      let Tterminal : TreeSequence G e0 :=
        current.series.data.tree terminal.castSucc
      forall (v : V) (gamma delta : Fin k),
        current.series.data.kind terminal = some TashkinovExtensionKind.PE ->
        current.series.data.chosenVertex terminal = some v ->
        current.series.data.gamma terminal = some gamma ->
        current.series.data.delta terminal = some delta ->
        forall sigma : PartialEdgeColoring E k,
          IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
          StableColoring Tterminal
            (TashkinovStoredColors current.series.data terminal)
            (current.series.data.coloring terminal) sigma ->
          forall w, w ∈ TreeSequenceVertexSet Tterminal ->
            (Sum.inl w ∈ TwoColorComponent G sigma gamma delta
                (Sum.inl v) <-> w = v))
    (hlowerTwo : forall {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0} {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input' T' generating'),
      0 < lower.rounds -> lower.rounds < original.rounds ->
      MaximumProperty lower ->
      let terminal : Fin (lower.rounds + 1) := Fin.last lower.rounds
      let Tnext : TreeSequence G e0 :=
        lower.series.data.tree (Fin.last (lower.rounds + 1))
      forall sigma : PartialEdgeColoring E k,
        IsProperEdgeColoring G sigma -> IsOneEdgeUncolored sigma e0 ->
        StableColoring Tnext
          (TashkinovStoredColors lower.series.data terminal)
          (lower.series.data.coloring terminal) sigma ->
        forall alpha beta : Fin k,
          (alpha ∈ TreeMissingColors sigma Tnext ∨
            beta ∈ TreeMissingColors sigma Tnext) ->
          TreeInterchangeable G Tnext sigma alpha beta)
    (presentation : RutgersClosedPresentation G k e0 original)
    (counterexample : RutgersCounterexample G k e0 original presentation)
    (helementary : ColoredVertexSetElementary G presentation.sigma
      (TreeSequenceVertexSet presentation.U)) :
    let replacement := presentation.corresponding.replacementETT
    let terminal : Fin (replacement.rounds + 1) := Fin.last replacement.rounds
    counterexample.b2 ∉
      TreeSequenceVertexSet (replacement.series.data.tree terminal.castSucc) := by
-- BODY
  classical
  let R := presentation.corresponding.replacementETT
  let q : Fin R.rounds := ⟨R.rounds - 1, by have := R.roundsPositive; omega⟩
  have hq : q.succ = Fin.last R.rounds := by
    apply Fin.ext
    simp [q]
    have := R.roundsPositive
    omega
  let N := R.series.data.tree q.succ.castSucc
  let sigma := presentation.sigma
  let U := presentation.U
  let alpha := counterexample.alpha
  let beta := counterexample.beta
  have hcolor : R.series.data.coloring q.succ = sigma := by
    rw [hq]
    exact R.generatingColoring.symm
  have hproper : IsProperEdgeColoring G sigma := by
    dsimp [sigma]
    rw [presentation.corresponding.finalGeneratingColoring]
    exact presentation.corresponding.replacementProper _
  have hone : IsOneEdgeUncolored sigma e0 := by
    dsimp [sigma]
    rw [presentation.corresponding.finalGeneratingColoring]
    exact presentation.corresponding.replacementOneUncolored _
  dsimp only
  change counterexample.b2 ∉ TreeSequenceVertexSet (R.series.data.tree (Fin.last R.rounds).castSucc)
  rw [← hq]
  change counterexample.b2 ∉ TreeSequenceVertexSet N
  intro hb2
  have hprefix : TreeSequenceInitialSegment N U ∧
      ColoredVertexSetClosed G sigma (TreeSequenceVertexSet U) := by
    have hr := presentation.terminalRoute
    change (R.series.data.kind (Fin.last R.rounds) = some TashkinovExtensionKind.PE ∧
        TashkinovClosure sigma (R.series.data.tree (Fin.last R.rounds).castSucc) U) ∨
      ((R.series.data.kind (Fin.last R.rounds) = some TashkinovExtensionKind.SE ∨
        R.series.data.kind (Fin.last R.rounds) = some TashkinovExtensionKind.RE) ∧
        ∃ f seed, R.series.data.connectingEdges (Fin.last R.rounds) = {f} ∧
          TreeSequenceAdjoinEdge (R.series.data.tree (Fin.last R.rounds).castSucc)
            f seed ∧ TashkinovClosure sigma seed U) at hr
    rw [← hq] at hr
    rcases hr with ⟨_, hc⟩ | ⟨_, f, seed, _, ha, hc⟩
    · exact ⟨TashkinovAugmentationSequenceInitialSegment sigma N U hc.1, hc.2⟩
    · obtain ⟨_, ⟨hlen1, hv1, he1⟩, _⟩ := ha
      obtain ⟨hlen2, hv2, he2⟩ :=
        TashkinovAugmentationSequenceInitialSegment sigma seed U hc.1
      refine ⟨⟨hlen1.trans hlen2, ?_, ?_⟩, hc.2⟩
      · intro i
        exact (hv2 (Fin.castLE (Nat.succ_le_succ hlen1) i)).trans (hv1 i)
      · intro i
        exact (he2 (Fin.castLE hlen1 i)).trans (he1 i)
  have hsub : TreeSequenceVertexSet N ⊆ TreeSequenceVertexSet U :=
    TreeSequenceInitialSegmentVertexSetSubset hprefix.1
  have hb1 : counterexample.b1 ∈ TreeSequenceVertexSet N := by
    obtain ⟨hlen, hv, _⟩ := hprefix.1
    obtain ⟨i, j, hi, hj, hij⟩ := counterexample.insideOrder12
    obtain ⟨t, ht⟩ : ∃ t, N.vertex t = counterexample.b2 := by
      simpa [TreeSequenceVertexSet] using hb2
    have hjt : j = Fin.castLE (Nat.succ_le_succ hlen) t :=
      U.vertex_injective (hj.trans ((hv t).trans ht).symm)
    have hil : i.val < N.length + 1 := by
      have htlt := t.isLt
      rw [hjt] at hij
      simp only [Fin.val_castLE] at hij
      omega
    let r : Fin (N.length + 1) := ⟨i.val, hil⟩
    have hir : Fin.castLE (Nat.succ_le_succ hlen) r = i := by
      apply Fin.ext
      rfl
    have hr : N.vertex r = counterexample.b1 := by
      rw [← hv r, hir]
      exact hi
    simpa [TreeSequenceVertexSet] using (show ∃ r, N.vertex r = counterexample.b1 from ⟨r, hr⟩)
  have helemN : ColoredVertexSetElementary G sigma (TreeSequenceVertexSet N) := by
    intro x hx y hy hxy
    exact helementary (hsub hx) (hsub hy) hxy
  have hcard := TreeMissingColorsCardLowerBound G k e0 sigma N hone.1 hdegree helemN
  -- Choose outside both terminal option slots, uniformly over the three kinds.
  let forbidden : Finset (Fin k) :=
    (R.series.data.gamma q.succ).toFinset ∪ (R.series.data.delta q.succ).toFinset
  have hforbidden : forbidden.card ≤ 2 := by
    have ho (a : Option (Fin k)) : a.toFinset.card ≤ 1 := by
      cases a <;> simp
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add (ho _) (ho _))
  have hnonempty : (TreeMissingColors sigma N \ forbidden).Nonempty := by
    apply Finset.card_pos.mp
    have hn : 0 < (TreeSequenceVertexSet N).card :=
      Finset.card_pos.mpr ⟨counterexample.b2, hb2⟩
    have hle := Finset.card_le_card (Finset.inter_subset_right :
      TreeMissingColors sigma N ∩ forbidden ⊆ forbidden)
    have heq := Finset.card_sdiff_add_card_inter (TreeMissingColors sigma N) forbidden
    omega
  obtain ⟨c, hc⟩ := hnonempty
  obtain ⟨hcN, hcAvoid⟩ := Finset.mem_sdiff.mp hc
  have hcU : c ∈ TreeMissingColors sigma U := by
    obtain ⟨x, hx, hm⟩ : ∃ x ∈ TreeSequenceVertexSet N, c ∈ MissingColors G sigma x := by
      simpa [TreeMissingColors] using hcN
    exact Finset.mem_biUnion.mpr ⟨x, hsub hx, hm⟩
  have hcb : c ≠ beta := by
    intro heq
    apply counterexample.betaPresent
    change beta ∈ TreeMissingColors sigma U
    rw [← heq]
    exact hcU
  have hab : alpha ≠ beta := counterexample.colorsDistinct
  -- Rung one uses the certified initial series, not a zero-rung ETT.
  have lowerInterchangeable : ∀ rho : PartialEdgeColoring E k,
      IsProperEdgeColoring G rho → IsOneEdgeUncolored rho e0 →
      StableColoring N (TashkinovStoredColors R.series.data q.castSucc)
        (R.series.data.coloring q.castSucc) rho →
      c ∈ TreeMissingColors rho N → TreeInterchangeable G N rho c beta := by
    intro rho hp ho hs hc
    by_cases hn : R.rounds = 1
    · have hi : q.succ.castSucc = (⟨1, by omega⟩ : Fin (R.rounds + 2)) := by
        apply Fin.ext
        simp [q, hn]
      have hz : q.castSucc = (0 : Fin (R.rounds + 1)) := by
        apply Fin.ext
        simp [q, hn]
      have hb := (TechnicalTheoremBase G k R.rounds e0
        presentation.corresponding.replacementInput R.series).2
      dsimp only at hb
      have hs' : StableColoring (R.series.data.tree ⟨1, by omega⟩)
          (TashkinovStoredColors R.series.data 0) (R.series.data.coloring 0) rho := by
        simpa only [N, hi, hz] using hs
      have ht := hb rho hp ho hs' c beta
        (Or.inl (by simpa only [N, hi] using hc))
      simpa only [N, hi] using ht
    · have hn' : 1 < R.rounds := by have := R.roundsPositive; omega
      obtain ⟨lower, hr, hmp, htrees, hdata⟩ :=
        CertifiedETTPredecessor G k e0 presentation.corresponding.replacementInput
          U sigma R presentation.maximum hn'
      let lt : Fin (lower.rounds + 1) := Fin.last lower.rounds
      have hcast : Fin.castLE (by omega) lt = q.castSucc := by
        apply Fin.ext
        simp [lt, q, hr]
      have ht : lower.series.data.tree (Fin.last (lower.rounds + 1)) = N := by
        rw [htrees]
        congr 1
        apply Fin.ext
        simp [N, hr, q]
      obtain ⟨hco, _, _, _, _, _, _, _, hst, _⟩ := hdata lt
      have hs' : StableColoring
          (lower.series.data.tree (Fin.last (lower.rounds + 1)))
          (TashkinovStoredColors lower.series.data lt)
          (lower.series.data.coloring lt) rho := by
        rw [ht, hco, hst, hcast]
        exact hs
      have hh := hlowerTwo lower (by omega)
        (by have := presentation.corresponding.rungAgreement; change R.rounds = original.rounds at this; omega) hmp
      dsimp only at hh
      have hi := hh rho hp ho hs' c beta (Or.inl (by simpa only [ht] using hc))
      simpa only [ht] using hi
  -- Subsingleton neighbor sets also cover isolated path components.
  have noninterchangeable : ∀ (rho : PartialEdgeColoring E k),
      IsProperEdgeColoring G rho → c ∈ TreeMissingColors rho N →
      ∀ (P1 : (TwoColorIncidenceGraph G rho c beta).Walk
          (Sum.inl counterexample.a1) (Sum.inl counterexample.b1))
        (P2 : (TwoColorIncidenceGraph G rho c beta).Walk
          (Sum.inl counterexample.a2) (Sum.inl counterexample.b2)),
        TreeExitPath N rho c beta counterexample.a1 counterexample.b1 P1 →
        TreeExitPath N rho c beta counterexample.a2 counterexample.b2 P2 →
        ¬ TreeInterchangeable G N rho c beta := by
    intro rho hp hc P1 P2 he1 he2 hinter
    let H := TwoColorIncidenceGraph G rho c beta
    have leaf (x : V) (hm : c ∈ MissingColors G rho x ∨ beta ∈ MissingColors G rho x) :
        Set.Subsingleton (H.neighborSet (Sum.inl x)) := by
      intro z hz w hw
      cases z with
      | inl y => simp [H, SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hz
      | inr e =>
        cases w with
        | inl y => simp [H, SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hw
        | inr f =>
          have he : Incident G x e ∧ (rho e = some c ∨ rho e = some beta) := by
            simpa [H, SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] using hz
          have hf : Incident G x f ∧ (rho f = some c ∨ rho f = some beta) := by
            simpa [H, SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] using hw
          apply congrArg Sum.inr
          by_contra hef
          have absent (d : Fin k) (hd : d ∈ MissingColors G rho x) :
              ∀ e, Incident G x e → rho e ≠ some d := by
            intro e he hco
            have hn : d ∉ PresentColors G rho x := by simpa [MissingColors] using hd
            exact hn (by simpa [PresentColors] using
              (show ∃ f, Incident G x f ∧ rho f = some d from ⟨e, he, hco⟩))
          rcases hm with hm | hm
          · exact (hp hef ⟨x, he.1, hf.1⟩
              (he.2.resolve_left (absent c hm e he.1)))
              (hf.2.resolve_left (absent c hm f hf.1))
          · exact (hp hef ⟨x, he.1, hf.1⟩
              (he.2.resolve_right (absent beta hm e he.1)))
              (hf.2.resolve_right (absent beta hm f hf.1))
    obtain ⟨x, hx, hcx⟩ : ∃ x ∈ TreeSequenceVertexSet N, c ∈ MissingColors G rho x := by
      simpa [TreeMissingColors] using hc
    have self (v : V) : Sum.inl v ∈ TwoColorComponent G rho c beta (Sum.inl v) :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
    have lx := leaf x (Or.inl hcx)
    have l1 := leaf counterexample.a1 he1.2.2.2.2.1
    have l2 := leaf counterexample.a2 he2.2.2.2.2.1
    have px : TwoColorPathComponent G rho c beta (Sum.inl x) :=
      ⟨hcb, Sum.inl x, self x, lx⟩
    have p1 : TwoColorPathComponent G rho c beta (Sum.inl counterexample.a1) :=
      ⟨hcb, Sum.inl counterexample.a1, self _, l1⟩
    have p2 : TwoColorPathComponent G rho c beta (Sum.inl counterexample.a2) :=
      ⟨hcb, Sum.inl counterexample.a2, self _, l2⟩
    have meet1 : Sum.inl counterexample.b1 ∈
        TwoColorComponent G rho c beta (Sum.inl counterexample.a1) := by
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr
        (SimpleGraph.ConnectedComponent.eq.mpr P1.reachable.symm)
    have meet2 : Sum.inl counterexample.b2 ∈
        TwoColorComponent G rho c beta (Sum.inl counterexample.a2) := by
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr
        (SimpleGraph.ConnectedComponent.eq.mpr P2.reachable.symm)
    have eq1 := hinter (Sum.inl x) (Sum.inl counterexample.a1) px p1
      ⟨x, hx, self x⟩ ⟨counterexample.b1, hb1, meet1⟩
    have eq2 := hinter (Sum.inl x) (Sum.inl counterexample.a2) px p2
      ⟨x, hx, self x⟩ ⟨counterexample.b2, hb2, meet2⟩
    obtain ⟨u, v, p, hp, hsupport⟩ :=
      TwoColorComponentSpanningPath G rho c beta hp (Sum.inl x)
    have endpoint (w : V) (hw : Sum.inl w ∈ TwoColorComponent G rho c beta (Sum.inl x))
        (hl : Set.Subsingleton (H.neighborSet (Sum.inl w))) :
        Sum.inl w = u ∨ Sum.inl w = v := by
      by_contra hn
      push Not at hn
      apply hp.isTrail.not_mem_support_of_subsingleton_neighborSet hn.1 hn.2 hl
      change Sum.inl w ∈ {z | z ∈ p.support}
      rw [hsupport]
      exact hw
    have ex := endpoint x (self x) lx
    have e1 := endpoint counterexample.a1 (by rw [eq1]; exact self _) l1
    have e2 := endpoint counterexample.a2 (by rw [eq2]; exact self _) l2
    have hx1 : (Sum.inl x : Sum V E) ≠ Sum.inl counterexample.a1 := by
      intro heq
      exact he1.2.2.1 ((Sum.inl.inj heq) ▸ hx)
    have hx2 : (Sum.inl x : Sum V E) ≠ Sum.inl counterexample.a2 := by
      intro heq
      exact he2.2.2.1 ((Sum.inl.inj heq) ▸ hx)
    have ha12 : (Sum.inl counterexample.a1 : Sum V E) ≠ Sum.inl counterexample.a2 := by
      simpa using counterexample.outsideDistinct12
    rcases ex with ex | ex
    · rcases e1 with e1 | e1
      · exact hx1 (ex.trans e1.symm)
      · rcases e2 with e2 | e2
        · exact hx2 (ex.trans e2.symm)
        · exact ha12 (e1.trans e2.symm)
    · rcases e1 with e1 | e1
      · rcases e2 with e2 | e2
        · exact ha12 (e1.trans e2.symm)
        · exact hx2 (ex.trans e2.symm)
      · exact hx1 (ex.trans e1.symm)
  let mu := OutsideTreeColorSwap U sigma alpha c
  have hswap : IsProperEdgeColoring G mu ∧ IsOneEdgeUncolored mu e0 ∧
      StableColoring U (TashkinovStoredColors R.series.data q.succ) sigma mu ∧
      ∀ f, TreeIncidentEdge U f → mu f = sigma f := by
    by_cases hac : alpha = c
    · have hm : mu = sigma := by
        funext f
        dsimp [mu]
        by_cases hf : TreeIncidentEdge U f
        · simp [OutsideTreeColorSwap, hf]
        · by_cases hc : sigma f = some c <;>
            simp [OutsideTreeColorSwap, hf, hac, hc]
      rw [hm]
      exact ⟨hproper, hone, ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩, fun _ _ => rfl⟩
    · exact OutsideTreeColorSwapStable U _ sigma alpha c hproper hone hprefix.2
        counterexample.alphaMissing hcU hac
  obtain ⟨hmuProper, hmuOne, hmuStable, hfixed⟩ := hswap
  have hstableN : StableColoring N (TashkinovStoredColors R.series.data q.succ)
      (R.series.data.coloring q.succ) mu := by
    rw [hcolor]
    refine ⟨?_, fun v hv => hmuStable.2 v (hsub hv)⟩
    intro f hf _
    obtain ⟨v, hv, hinc⟩ := hf
    exact hfixed f ⟨v, hsub hv, hinc⟩
  have hcMu : c ∈ TreeMissingColors mu N := by
    obtain ⟨v, hv, hm⟩ : ∃ v ∈ TreeSequenceVertexSet N, c ∈ MissingColors G sigma v := by
      simpa [TreeMissingColors] using hcN
    exact Finset.mem_biUnion.mpr ⟨v, hv, by rw [hmuStable.2 v (hsub hv)]; exact hm⟩
  have ends_eq_of_mem : ∀ {z : Sym2 V} {x y : V}, x ∈ z → y ∈ z → x ≠ y →
      z = Sym2.mk x y := by
    intro z x y hx hy hxy
    induction z using Sym2.inductionOn with
    | _ a b =>
      simp only [Sym2.mem_iff] at hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact (hxy (hx.trans hy.symm)).elim
      · rw [hx, hy]
      · rw [hx, hy]
        exact Sym2.eq_swap ..
      · exact (hxy (hx.trans hy.symm)).elim
  have closed_color (d : Fin k) (hd : d ∈ TreeMissingColors sigma U) :
      ∀ {f}, f ∈ BoundaryEdges G (TreeSequenceVertexSet U) → sigma f ≠ some d := by
    intro f hf hfd
    obtain ⟨v, hv, hm⟩ : ∃ v ∈ TreeSequenceVertexSet U, d ∈ MissingColors G sigma v := by
      simpa [TreeMissingColors] using hd
    exact (hprefix.2 hf hv hfd) hm
  have path_boundary : ∀ {a b : V}
      (P : (TwoColorIncidenceGraph G sigma alpha beta).Walk (Sum.inl a) (Sum.inl b)),
      TreeExitPath U sigma alpha beta a b P →
      ∀ {f}, Sum.inr f ∈ P.support → TreeIncidentEdge U f →
        f ∈ BoundaryEdges G (TreeSequenceVertexSet U) := by
    intro a b P hexit f hf hftree
    obtain ⟨n, hn, hnle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hf
    have hnpos : 0 < n := by
      by_contra h
      have hz : n = 0 := by omega
      rw [hz] at hn
      simp at hn
    have hnlt : n < P.length := by
      by_contra h
      have hz : n = P.length := by omega
      rw [hz] at hn
      simp at hn
    have hprev := P.adj_getVert_succ (i := n - 1) (by omega)
    have hnext := P.adj_getVert_succ (i := n) hnlt
    have hnsub : n - 1 + 1 = n := by omega
    rw [hnsub, hn] at hprev
    rw [hn] at hnext
    cases hy : P.getVert (n - 1) with
    | inr g =>
      rw [hy] at hprev
      simp [TwoColorIncidenceGraph] at hprev
    | inl y =>
      rw [hy] at hprev
      cases hz : P.getVert (n + 1) with
      | inr g =>
        rw [hz] at hnext
        simp [TwoColorIncidenceGraph] at hnext
      | inl z =>
        rw [hz] at hnext
        have hyf : Incident G y f := hprev.1
        have hzf : Incident G z f := hnext.1
        have hyz : y ≠ z := by
          intro hyz
          have heq : P.getVert (n - 1) = P.getVert (n + 1) := by rw [hy, hz, hyz]
          have hleft : n - 1 ≤ P.length := by omega
          have hright : n + 1 ≤ P.length := by omega
          have hi := hexit.1.getVert_injOn hleft hright heq
          omega
        have hySupport : Sum.inl y ∈ P.support := by rw [← hy]; exact P.getVert_mem_support _
        have hzSupport : Sum.inl z ∈ P.support := by rw [← hz]; exact P.getVert_mem_support _
        have he : G.ends f = Sym2.mk y z := ends_eq_of_mem hyf hzf hyz
        obtain ⟨x, hx, hxf⟩ := hftree
        have hxy : x = y ∨ x = z := by simpa [Incident, he] using hxf
        simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hxy with hxy | hxz
        · subst x
          refine ⟨y, hx, z, ?_, he⟩
          intro hzT
          exact hyz ((hexit.2.2.2.2.2 y hx).mp hySupport |>.trans
            ((hexit.2.2.2.2.2 z hzT).mp hzSupport).symm)
        · subst x
          refine ⟨z, hx, y, ?_, ?_⟩
          · intro hyT
            exact hyz ((hexit.2.2.2.2.2 y hyT).mp hySupport |>.trans
              ((hexit.2.2.2.2.2 z hx).mp hzSupport).symm)
          · exact he.trans (Sym2.eq_swap ..)
  have outside_color (f : E) (hf : ¬ TreeIncidentEdge U f) :
      (mu f = some c → sigma f = some alpha) ∧
      (mu f = some beta ↔ sigma f = some beta) := by
    constructor
    · intro hmc
      by_cases ha : sigma f = some alpha
      · exact ha
      · by_cases hc : sigma f = some c
        · have hca : c ≠ alpha := by
            intro heq
            exact ha (hc.trans (congrArg some heq))
          have hac : alpha = c := by
            apply Option.some.inj
            simpa [mu, OutsideTreeColorSwap, hf, ha, hc, hca] using hmc
          exact hc.trans (congrArg some hac.symm)
        · have hc' : sigma f = some c := by
            simpa [mu, OutsideTreeColorSwap, hf, ha, hc] using hmc
          exact (hc hc').elim
    · by_cases ha : sigma f = some alpha
      · simp [mu, OutsideTreeColorSwap, hf, ha, hab, hcb]
      · by_cases hc : sigma f = some c
        · have hca : c ≠ alpha := by
            intro heq
            exact ha (hc.trans (congrArg some heq))
          simp [mu, OutsideTreeColorSwap, hf, ha, hc, hca, hab, hcb]
        · simp [mu, OutsideTreeColorSwap, hf, ha, hc]
  have remote_missing : ∀ {v : V}, v ∉ TreeSequenceVertexSet U →
      (alpha ∈ MissingColors G sigma v ∨ beta ∈ MissingColors G sigma v) →
      c ∈ MissingColors G mu v ∨ beta ∈ MissingColors G mu v := by
    intro v hv hm
    have outside_boundary {f : E} (hinc : Incident G v f) (hf : TreeIncidentEdge U f) :
        f ∈ BoundaryEdges G (TreeSequenceVertexSet U) := by
      obtain ⟨w, hw, hwf⟩ := hf
      have hwv : w ≠ v := by intro heq; exact hv (heq ▸ hw)
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨w, hw, v, hv, ends_eq_of_mem hwf hinc hwv⟩
    rcases hm with ha | hb
    · left
      have hnot : alpha ∉ PresentColors G sigma v := by simpa [MissingColors] using ha
      change c ∈ Finset.univ \ PresentColors G mu v
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hpres
      obtain ⟨f, hinc, hfc⟩ : ∃ f, Incident G v f ∧ mu f = some c := by
        simpa [PresentColors] using hpres
      by_cases hf : TreeIncidentEdge U f
      -- A fixed edge at an outside endpoint is a boundary edge of U.
      · exact closed_color c hcU (outside_boundary hinc hf) ((hfixed f hf).symm.trans hfc)
      · apply hnot
        simpa [PresentColors] using
          (show ∃ f, Incident G v f ∧ sigma f = some alpha from
            ⟨f, hinc, (outside_color f hf).1 hfc⟩)
    · right
      have hnot : beta ∉ PresentColors G sigma v := by simpa [MissingColors] using hb
      change beta ∈ Finset.univ \ PresentColors G mu v
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hpres
      obtain ⟨f, hinc, hfb⟩ : ∃ f, Incident G v f ∧ mu f = some beta := by
        simpa [PresentColors] using hpres
      have hfb' : sigma f = some beta := by
        by_cases hf : TreeIncidentEdge U f
        · exact (hfixed f hf).symm.trans hfb
        · exact (outside_color f hf).2.mp hfb
      apply hnot
      simpa [PresentColors] using
        (show ∃ f, Incident G v f ∧ sigma f = some beta from ⟨f, hinc, hfb'⟩)
  have transfer_exit : ∀ {a b : V}
      (P : (TwoColorIncidenceGraph G sigma alpha beta).Walk (Sum.inl a) (Sum.inl b)),
      TreeExitPath U sigma alpha beta a b P → b ∈ TreeSequenceVertexSet N →
      ∃ Q : (TwoColorIncidenceGraph G mu c beta).Walk (Sum.inl a) (Sum.inl b),
        TreeExitPath N mu c beta a b Q := by
    intro a b P hexit hb
    have preserve : ∀ {v : V} {f : E}, Sum.inr f ∈ P.support →
        (TwoColorIncidenceGraph G sigma alpha beta).Adj (Sum.inl v) (Sum.inr f) →
        (TwoColorIncidenceGraph G mu c beta).Adj (Sum.inl v) (Sum.inr f) := by
      intro v f hf hadj
      have hold : Incident G v f ∧ (sigma f = some alpha ∨ sigma f = some beta) := hadj
      refine ⟨hold.1, ?_⟩
      by_cases ht : TreeIncidentEdge U f
      · have hfb : sigma f = some beta := hold.2.resolve_left
          (closed_color alpha counterexample.alphaMissing (path_boundary P hexit hf ht))
        exact Or.inr ((hfixed f ht).trans hfb)
      · rcases hold.2 with ha | hb
        · exact Or.inl (by simp [mu, OutsideTreeColorSwap, ht, ha])
        · exact Or.inr ((outside_color f ht).2.mpr hb)
    have hedges : ∀ z, z ∈ P.edges → z ∈ (TwoColorIncidenceGraph G mu c beta).edgeSet := by
      intro z hz
      induction z using Sym2.inductionOn with
      | _ x y =>
        have hadj := (SimpleGraph.mem_edgeSet _).mp (P.edges_subset_edgeSet hz)
        have hx := P.fst_mem_support_of_mem_edges hz
        have hy := P.snd_mem_support_of_mem_edges hz
        apply (SimpleGraph.mem_edgeSet _).mpr
        cases x with
        | inl v =>
          cases y with
          | inl w => simpa [TwoColorIncidenceGraph] using hadj
          | inr f => exact preserve hy hadj
        | inr f =>
          cases y with
          | inl v => exact (preserve hx hadj.symm).symm
          | inr g => simpa [TwoColorIncidenceGraph] using hadj
    let Q := P.transfer (TwoColorIncidenceGraph G mu c beta) hedges
    refine ⟨Q, hexit.1.transfer hedges, ?_, ?_, hb, ?_, ?_⟩
    · simpa [Q] using hexit.2.1
    · exact fun ha => hexit.2.2.1 (hsub ha)
    · exact remote_missing hexit.2.2.1 hexit.2.2.2.2.1
    · intro w hw
      simpa [Q] using hexit.2.2.2.2.2 w (hsub hw)
  obtain ⟨P1, he1⟩ := transfer_exit counterexample.Q1 counterexample.exit1 hb1
  obtain ⟨P2, he2⟩ := transfer_exit counterexample.Q2 counterexample.exit2 hb2
  have hnot := noninterchangeable mu hmuProper hcMu P1 P2 he1 he2
  -- The swap fixes all tree-incident identities, stronger than stable control.
  have stableAfter (phi : PartialEdgeColoring E k) (D : Finset (Fin k))
      (hs : StableColoring N D phi sigma) : StableColoring N D phi mu := by
    refine ⟨?_, ?_⟩
    · intro f hf hc
      obtain ⟨v, hv, hinc⟩ := hf
      exact (hfixed f ⟨v, hsub hv, hinc⟩).trans (hs.1 f ⟨v, hv, hinc⟩ hc)
    · intro v hv
      exact (hmuStable.2 v (hsub hv)).trans (hs.2 v hv)
  have boundary_restrict (f : E) (b : V)
      (hf : f ∈ BoundaryColorEdges G sigma (TreeSequenceVertexSet U) beta)
      (hb : b ∈ TreeSequenceVertexSet N) (hinc : Incident G b f) :
      f ∈ BoundaryColorEdges G sigma (TreeSequenceVertexSet N) beta := by
    obtain ⟨hboundary, hfc⟩ := Finset.mem_filter.mp hf
    obtain ⟨x, hx, y, hy, he⟩ : ∃ x ∈ TreeSequenceVertexSet U,
        ∃ y ∉ TreeSequenceVertexSet U, G.ends f = Sym2.mk x y := by
      simpa [BoundaryEdges] using hboundary
    have hbx : b = x := by
      have hbends : b = x ∨ b = y := by simpa [Incident, he] using hinc
      exact hbends.resolve_right (by intro heq; exact hy (heq ▸ hsub hb))
    refine Finset.mem_filter.mpr ⟨?_, hfc⟩
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨b, hb, y, fun h => hy (hsub h), by rw [hbx]; exact he⟩
  have hf1 := boundary_restrict counterexample.f1 counterexample.b1
    counterexample.boundary1 hb1 counterexample.incident1
  have hf2 := boundary_restrict counterexample.f2 counterexample.b2
    counterexample.boundary2 hb2 counterexample.incident2
  have hfne : counterexample.f1 ≠ counterexample.f2 := by
    intro heq
    exact counterexample.supportDisjoint12 (Sum.inr counterexample.f1)
      counterexample.edgeOnWalk1 (by rw [heq]; exact counterexample.edgeOnWalk2)
  have cert := R.series.certified q.succ
  generalize hslot : q.succ = slot at cert
  cases cert with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
    exact (Fin.succ_ne_zero q hslot).elim
  | SE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternative currentColoring currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma adjoined
      adjoinedExactly closedExtension orderedExtension strictExtension =>
    have hi : i = q := by
      apply Fin.ext
      have h := congrArg Fin.val hslot
      simp only [Fin.val_succ] at h
      omega
    subst i
    have hselected : choice.selected = sigma := currentColoring.symm.trans hcolor
    have hs : StableColoring N (TashkinovStoredColors R.series.data q.castSucc)
        (R.series.data.coloring q.castSucc) sigma := by
      rw [← hselected]
      exact choice.selectedStable
    exact hnot (lowerInterchangeable mu hmuProper hmuOne (stableAfter _ _ hs) hcMu)
  | RE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      available currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly closedExtension
      orderedExtension strictExtension =>
    have hi : i = q := by
      apply Fin.ext
      have h := congrArg Fin.val hslot
      simp only [Fin.val_succ] at h
      omega
    subst i
    have hprevious : R.series.data.coloring q.castSucc = sigma :=
      currentColoring.symm.trans hcolor
    have hs : StableColoring N (TashkinovStoredColors R.series.data q.castSucc)
        (R.series.data.coloring q.castSucc) sigma := by
      rw [hprevious]
      exact ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩
    exact hnot (lowerInterchangeable mu hmuProper hmuOne (stableAfter _ _ hs) hcMu)
  | PE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternativeFails gamma gammaRule secondStable
      secondStableProper secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
      orderedExtension strictExtension =>
    have hi : i = q := by
      apply Fin.ext
      have h := congrArg Fin.val hslot
      simp only [Fin.val_succ] at h
      omega
    subst i
    have hv : choice.vertex ∈ TreeSequenceVertexSet N := choice.vertexDefective.1
    have hgSecond : gamma ∈ MissingColors G secondStable choice.vertex := by
      rw [secondStableRelation.2 choice.vertex hv]
      exact gammaRule.1
    have hfSecond : secondStable choice.edge = some choice.color := by
      exact (secondStableRelation.1 choice.edge
        ⟨choice.vertex, hv, choice.edgeIncident⟩
        ⟨choice.color, Finset.mem_union_right _ (Finset.mem_insert_self _ _),
          choice.edgeColor⟩).trans choice.edgeColor
    have hgd : gamma ≠ choice.color := by
      intro heq
      have hn : gamma ∉ PresentColors G secondStable choice.vertex := by
        simpa [MissingColors] using hgSecond
      apply hn
      simpa [PresentColors] using
        (show ∃ f, Incident G choice.vertex f ∧ secondStable f = some gamma from
          ⟨choice.edge, choice.edgeIncident, by rw [heq]; exact hfSecond⟩)
    have hdMissing : choice.color ∈ MissingColors G sigma choice.vertex := by
      rw [← hcolor, currentColoring]
      exact (TwoColorComponentSwapMissingBehavior G secondStable gamma choice.color
        hgd secondStableProper (Sum.inl choice.vertex)).2.1 choice.vertex
          ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl) hgSecond
    have hbd : beta ≠ choice.color := by
      intro heq
      apply counterexample.betaPresent
      change beta ∈ TreeMissingColors sigma U
      apply Finset.mem_biUnion.mpr
      exact ⟨choice.vertex, hsub hv, by rw [heq]; exact hdMissing⟩
    have hboundary := (HkuParallelBoundaryStructure G k R.rounds e0
      presentation.corresponding.replacementInput R.series q choice.edge choice.color gamma
      choice.vertex currentKind currentEdges currentDelta currentGamma currentVertex).1
    rw [hcolor] at hboundary
    have hbg : beta ≠ gamma := by
      intro heq
      have h1 := hf1
      have h2 := hf2
      change counterexample.f1 ∈ BoundaryColorEdges G sigma
        (TreeSequenceVertexSet (R.series.data.tree q.succ.castSucc)) beta at h1
      change counterexample.f2 ∈ BoundaryColorEdges G sigma
        (TreeSequenceVertexSet (R.series.data.tree q.succ.castSucc)) beta at h2
      rw [heq, hboundary] at h1 h2
      exact hfne ((Finset.mem_singleton.mp h1).trans (Finset.mem_singleton.mp h2).symm)
    have hcg : c ≠ gamma := by
      intro heq
      apply hcAvoid
      simp [forbidden, currentGamma, heq]
    have hcd : c ≠ choice.color := by
      intro heq
      apply hcAvoid
      simp [forbidden, currentDelta, heq]
    have hcomponent : ∀ w, w ∈ TreeSequenceVertexSet N →
        (Sum.inl w ∈ TwoColorComponent G mu gamma choice.color (Sum.inl choice.vertex) ↔
          w = choice.vertex) := by
      have hfour := hcurrentFour R presentation.corresponding.rungAgreement presentation.maximum
      dsimp only at hfour
      rw [← hq] at hfour
      exact hfour choice.vertex gamma choice.color currentKind currentVertex currentGamma
        currentDelta mu hmuProper hmuOne hstableN
    obtain ⟨selected, recovered, _, _, _, _, _, _, _, _, _, hundone⟩ :=
      ParallelExtensionUndoStable G k R.rounds e0 presentation.corresponding.replacementInput
        R.series q choice.vertex gamma choice.color currentKind currentVertex currentGamma
        currentDelta mu hmuProper hmuOne hstableN hv hcomponent
    let tau := TwoColorComponentSwap G mu gamma choice.color (Sum.inl choice.vertex)
    have htProper : IsProperEdgeColoring G tau :=
      TwoColorComponentSwapProper G mu gamma choice.color hgd hmuProper (Sum.inl choice.vertex)
    have htOne : IsOneEdgeUncolored tau e0 := by
      constructor
      · by_cases he : Sum.inr e0 ∈ TwoColorComponent G mu gamma choice.color (Sum.inl choice.vertex)
        · simp [tau, TwoColorComponentSwap, he, hmuOne.1]
        · simp [tau, TwoColorComponentSwap, he, hmuOne.1]
      · intro e he0
        obtain ⟨d, hd⟩ := hmuOne.2 e he0
        by_cases he : Sum.inr e ∈ TwoColorComponent G mu gamma choice.color (Sum.inl choice.vertex)
        · by_cases hdg : d = gamma
          · exact ⟨choice.color, by simp [tau, TwoColorComponentSwap, he, hd, hdg]⟩
          · by_cases hdd : d = choice.color
            · exact ⟨gamma, by simp [tau, TwoColorComponentSwap, he, hd, hdd, hgd.symm]⟩
            · exact ⟨d, by simp [tau, TwoColorComponentSwap, he, hd, hdg, hdd]⟩
        · exact ⟨d, by simp [tau, TwoColorComponentSwap, he, hd]⟩
    have hcTau : c ∈ TreeMissingColors tau N := by
      obtain ⟨v, hv, hm⟩ : ∃ v ∈ TreeSequenceVertexSet N, c ∈ MissingColors G mu v := by
        simpa [TreeMissingColors] using hcMu
      apply Finset.mem_biUnion.mpr
      exact ⟨v, hv, (TwoColorComponentSwapMissingBehavior G mu gamma choice.color hgd
        hmuProper (Sum.inl choice.vertex)).2.2.2 v c hcg hcd |>.mpr hm⟩
    have hdisjoint : Disjoint ({c, beta} : Finset (Fin k)) {gamma, choice.color} := by
      rw [Finset.disjoint_left]
      intro d hd hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd hs
      rcases hd with rfl | rfl <;> rcases hs with hs | hs
      · exact hcg hs
      · exact hcd hs
      · exact hbg hs
      · exact hbd hs
    have hgraph : TwoColorIncidenceGraph G tau c beta = TwoColorIncidenceGraph G mu c beta :=
      TwoColorComponentSwapDisjointPairGraph G mu c beta gamma choice.color
        (Sum.inl choice.vertex) hdisjoint
    have transferTau : ∀ {a b : V}
        (P : (TwoColorIncidenceGraph G mu c beta).Walk (Sum.inl a) (Sum.inl b)),
        TreeExitPath N mu c beta a b P →
        ∃ Q : (TwoColorIncidenceGraph G tau c beta).Walk (Sum.inl a) (Sum.inl b),
          TreeExitPath N tau c beta a b Q := by
      intro a b P he
      have hedges : ∀ z, z ∈ P.edges → z ∈ (TwoColorIncidenceGraph G tau c beta).edgeSet := by
        intro z hz
        rw [hgraph]
        exact P.edges_subset_edgeSet hz
      let Q := P.transfer (TwoColorIncidenceGraph G tau c beta) hedges
      refine ⟨Q, he.1.transfer hedges, ?_, he.2.2.1, he.2.2.2.1, ?_, ?_⟩
      · simpa [Q] using he.2.1
      · have hm := (TwoColorComponentSwapMissingBehavior G mu gamma choice.color hgd
          hmuProper (Sum.inl choice.vertex)).2.2.2
        rcases he.2.2.2.2.1 with hc | hb
        · exact Or.inl ((hm a c hcg hcd).mpr hc)
        · exact Or.inr ((hm a beta hbg hbd).mpr hb)
      · intro w hw
        simpa [Q] using he.2.2.2.2.2 w hw
    obtain ⟨Q1, hQ1⟩ := transferTau P1 he1
    obtain ⟨Q2, hQ2⟩ := transferTau P2 he2
    exact noninterchangeable tau htProper hcTau Q1 Q2 hQ1 hQ2
      (lowerInterchangeable tau htProper htOne hundone hcTau)
