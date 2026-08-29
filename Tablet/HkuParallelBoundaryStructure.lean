import Tablet.AdjacentEdges
import Tablet.BoundaryColorEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.DefectiveEdge
import Tablet.DefectiveVertex
import Tablet.Incident
import Tablet.IsProperEdgeColoring
import Tablet.MaximumDefectiveChoice
import Tablet.MissingColors
import Tablet.ParallelExtensionColor
import Tablet.PresentColors
import Tablet.StableColoring
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeExit
import Tablet.TreeExitPath
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeVertexOrder
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.sc2

-- [TABLET NODE: HkuParallelBoundaryStructure]
theorem HkuParallelBoundaryStructure {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input) (q : Fin rounds)
    (f : E) (delta gamma : Fin k) (v : V)
    (hkind : series.data.kind q.succ = some TashkinovExtensionKind.PE)
    (hedge : series.data.connectingEdges q.succ = {f})
    (hdelta : series.data.delta q.succ = some delta)
    (hgamma : series.data.gamma q.succ = some gamma)
    (hvertex : series.data.chosenVertex q.succ = some v) :
    BoundaryColorEdges G (series.data.coloring q.succ)
        (TreeSequenceVertexSet (series.data.tree q.succ.castSucc)) gamma = {f} ∧
    (∀ g ∈ BoundaryColorEdges G (series.data.coloring q.succ)
        (TreeSequenceVertexSet (series.data.tree q.succ.castSucc)) delta,
      ∃ w : V, TreeVertexOrder (series.data.tree q.succ.castSucc) w v ∧
        Incident G w g) ∧
    (ColoredVertexSetElementary G (series.data.coloring q.castSucc)
        (TreeSequenceVertexSet (series.data.tree q.succ.castSucc)) →
      ∀ alpha ∈ TreeMissingColors (series.data.coloring q.succ)
          (series.data.tree q.succ.castSucc), alpha ≠ delta →
        BoundaryColorEdges G (series.data.coloring q.succ)
          (TreeSequenceVertexSet (series.data.tree q.succ.castSucc)) alpha = ∅) := by
-- BODY
  classical
  generalize target_eq : q.succ = target
  cases series.certified target with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    exact (Fin.succ_ne_zero q target_eq).elim
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have value := congrArg Fin.val target_eq
    simp at value
    have ci_eq : ci = q := by apply Fin.ext; omega
    subst ci
    rw [currentKind] at hkind
    simp at hkind
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have value := congrArg Fin.val target_eq
    simp at value
    have ci_eq : ci = q := by apply Fin.ext; omega
    subst ci
    rw [currentKind] at hkind
    simp at hkind
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      chosenGamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
    have value := congrArg Fin.val target_eq
    simp at value
    have ci_eq : ci = q := by apply Fin.ext; omega
    subst ci
    rw [currentKind] at hkind
    have delta_eq : delta = choice.color := Option.some.inj (hdelta.symm.trans currentDelta)
    have gamma_eq : gamma = chosenGamma := Option.some.inj (hgamma.symm.trans currentGamma)
    have vertex_eq : v = choice.vertex := Option.some.inj (hvertex.symm.trans currentVertex)
    subst delta
    subst gamma
    subst v
    let tree := series.data.tree q.succ.castSucc
    let vertices := TreeSequenceVertexSet tree
    have hmissing : chosenGamma ∈ MissingColors G secondStable choice.vertex := by
      exact (secondStableRelation.2 choice.vertex choice.vertexDefective.1).symm ▸ gammaRule.1
    have hdegree : ∀ w, chosenGamma ∈ MissingColors G secondStable w ∨
        choice.color ∈ MissingColors G secondStable w →
        (TwoColorIncidenceGraph G secondStable chosenGamma choice.color).degree
          (Sum.inl w) ≤ 1 := by
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
          · have he : secondStable e = some choice.color :=
              hy.2.resolve_left (by
                intro he
                have hn : chosenGamma ∉ PresentColors G secondStable w := by
                  simpa [MissingColors] using hw
                apply hn
                simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨_, hy.1, he⟩)
            have hf : secondStable f = some choice.color :=
              hz.2.resolve_left (by
                intro hf
                have hn : chosenGamma ∉ PresentColors G secondStable w := by
                  simpa [MissingColors] using hw
                apply hn
                simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨_, hz.1, hf⟩)
            by_cases h : e = f
            · exact congrArg Sum.inr h
            · exact (secondStableProper h ⟨w, hy.1, hz.1⟩ he hf).elim
          · have he : secondStable e = some chosenGamma :=
              hy.2.resolve_right (by
                intro he
                have hn : choice.color ∉ PresentColors G secondStable w := by
                  simpa [MissingColors] using hw
                apply hn
                simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨_, hy.1, he⟩)
            have hf : secondStable f = some chosenGamma :=
              hz.2.resolve_right (by
                intro hf
                have hn : choice.color ∉ PresentColors G secondStable w := by
                  simpa [MissingColors] using hw
                apply hn
                simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨_, hz.1, hf⟩)
            by_cases h : e = f
            · exact congrArg Sum.inr h
            · exact (secondStableProper h ⟨w, hy.1, hz.1⟩ he hf).elim
    have hcomponent : ∀ w, w ∈ vertices →
        Sum.inl w ∈ TwoColorComponent G secondStable chosenGamma choice.color
          (Sum.inl choice.vertex) → w = choice.vertex := by
      intro w hwT hwC
      rcases exitWitness with ⟨u, path, pathData⟩
      rcases pathData with ⟨pathIs, pathLen, uOut, endTree, endOnly⟩
      have hne : ¬ path.Nil := by
        intro hn
        have hl : path.length = 0 := by simpa [SimpleGraph.Walk.nil_iff_support_eq] using hn
        omega
      have huDegree := hdegree u endOnly.1
      let graph := TwoColorIncidenceGraph G secondStable chosenGamma choice.color
      have hbound : ∀ x, @SimpleGraph.degree _ graph x (Fintype.ofFinite _) ≤ 2 := by
        intro x
        exact TwoColorIncidenceDegreeAtMostTwo G secondStable chosenGamma choice.color
          secondStableProper x
      have closed : ∀ x, x ∈ path.support → ∀ y, graph.Adj x y → y ∈ path.support := by
        intro x hx y hxy
        obtain ⟨n, hn, hnle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
        by_cases hn0 : n = 0
        · subst n
          have hx0 : x = Sum.inl u := by simpa using hn.symm
          letI : Fintype (graph.neighborSet x) := Fintype.ofFinite _
          have card : Fintype.card (graph.neighborSet x) ≤ 1 := by
            rw [SimpleGraph.card_neighborSet_eq_degree]
            convert huDegree using 1
            cases hx0
            exact congrArg (fun z => @SimpleGraph.degree _ graph (Sum.inl u) z) (Subsingleton.elim _ _)
          have hy' : y ∈ graph.neighborSet x := by simpa [SimpleGraph.mem_neighborSet] using hxy
          have hn' : path.getVert 1 ∈ graph.neighborSet x := by
            simpa [hx0, SimpleGraph.mem_neighborSet] using path.adj_getVert_succ (show 0 < path.length by omega)
          have heq := Fintype.card_le_one_iff.mp card ⟨y, hy'⟩ ⟨path.getVert 1, hn'⟩
          have hey : y = path.getVert 1 := congrArg Subtype.val heq
          rw [hey]
          exact path.getVert_mem_support 1
        by_cases hlast : n = path.length
        · have hx1 : x = Sum.inl choice.vertex := by
            rw [← hn, pathIs.getVert_eq_end_iff hnle]
            exact hlast
          letI : Fintype (graph.neighborSet x) := Fintype.ofFinite _
          have card : Fintype.card (graph.neighborSet x) ≤ 1 := by
            rw [SimpleGraph.card_neighborSet_eq_degree]
            convert hdegree choice.vertex (Or.inl hmissing) using 1
            cases hx1
            exact congrArg (fun z => @SimpleGraph.degree _ graph (Sum.inl choice.vertex) z) (Subsingleton.elim _ _)
          have hy' : y ∈ graph.neighborSet x := by simpa [SimpleGraph.mem_neighborSet] using hxy
          have hp : path.getVert (path.length - 1) ∈ graph.neighborSet x := by
            have ha : graph.Adj (Sum.inl choice.vertex) (path.getVert (path.length - 1)) := by
              simpa [graph, show path.length - 1 + 1 = path.length by omega] using
                (path.adj_getVert_succ (show path.length - 1 < path.length by omega)).symm
            simpa [hx1, SimpleGraph.mem_neighborSet] using ha
          have heq := Fintype.card_le_one_iff.mp card ⟨y, hy'⟩ ⟨path.getVert (path.length - 1), hp⟩
          have hey : y = path.getVert (path.length - 1) := congrArg Subtype.val heq
          rw [hey]
          exact path.getVert_mem_support _
        have hl : graph.Adj (path.getVert n) (path.getVert (n - 1)) := by
          rw [← show n - 1 + 1 = n by omega]
          exact (path.adj_getVert_succ (by omega)).symm
        have hr : graph.Adj (path.getVert n) (path.getVert (n + 1)) := path.adj_getVert_succ (by omega)
        by_contra hyout
        have hyout' := hxy
        rw [← hn] at hyout'
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
          have hi := pathIs.getVert_injOn (show n - 1 ≤ path.length by omega)
            (show n + 1 ≤ path.length by omega) h
          omega
        letI : Fintype (graph.neighborSet (path.getVert n)) := Fintype.ofFinite _
        have three : 3 ≤ graph.degree (path.getVert n) := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          let s : Finset _ := {y, path.getVert (n - 1), path.getVert (n + 1)}
          have hs : s ⊆ graph.neighborFinset (path.getVert n) := by
            intro t ht
            simp only [s, Finset.mem_insert, Finset.mem_singleton] at ht
            rcases ht with rfl | rfl | rfl
            · simpa [SimpleGraph.mem_neighborFinset] using hyout'
            · simpa [SimpleGraph.mem_neighborFinset] using hl
            · simpa [SimpleGraph.mem_neighborFinset] using hr
          have hc : 3 ≤ s.card := by simp [s, hnl, hnr, hnp, hnl.symm, hnr.symm, hnp.symm]
          exact hc.trans (Finset.card_le_card hs)
        have upper : @SimpleGraph.degree _ graph (path.getVert n) (Fintype.ofFinite _) ≤ 2 :=
          hbound (path.getVert n)
        omega
      have reach : graph.Reachable (Sum.inl choice.vertex) (Sum.inl w) := by
        change graph.connectedComponentMk (Sum.inl w) = graph.connectedComponentMk (Sum.inl choice.vertex) at hwC
        exact SimpleGraph.ConnectedComponent.eq.mp hwC |>.symm
      have ws : Sum.inl w ∈ path.support := by
        apply reach.mem_subgraphVerts (H := (⊤ : graph.Subgraph).induce {x | x ∈ path.support})
          (fun x hx y hadj => ⟨by simpa using hx, closed x (by simpa using hx) y hadj, hadj⟩)
          (by simpa using path.getVert_mem_support path.length)
      exact (endOnly.2 w hwT).mp ws
    have hboundary : ∀ {e : E}, e ∈ BoundaryEdges G vertices →
        TreeIncidentEdge tree e := by
      intro e he
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
      rcases he with ⟨x, hx, y, hy, hexy⟩
      exact ⟨x, hx, by simpa [Incident, hexy]⟩
    have hreverseEdge : ∀ e, TreeIncidentEdge tree e →
        ((∃ c ∈ TreeMissingColors choice.selected tree ∪
          insert choice.color (TashkinovStoredColors series.data q.castSucc),
          choice.selected e = some c) ∨
        (∃ c ∈ TreeMissingColors choice.selected tree ∪
          insert choice.color (TashkinovStoredColors series.data q.castSucc),
          secondStable e = some c)) →
        secondStable e = choice.selected e := by
      intro e he h
      exact (sc1 G e0 tree (insert choice.color
        (TashkinovStoredColors series.data q.castSucc)) choice.selected secondStable
        choice.selectedProper choice.selectedOneUncolored
        secondStableProper secondStableOneUncolored).mp secondStableRelation e he h
    have hclosedSelected : ColoredVertexSetClosed G choice.selected vertices := by
      intro e c x he hx hec hmiss
      have hmissOld : c ∈ MissingColors G (series.data.coloring q.castSucc) x := by
        rw [← choice.selectedStable.2 x hx]
        exact hmiss
      have htreeOld : c ∈ TreeMissingColors
          (series.data.coloring q.castSucc) tree := by
        unfold TreeMissingColors
        simp only [Finset.mem_biUnion]
        exact ⟨x, hx, hmissOld⟩
      have hstable := (sc1 G e0 tree (TashkinovStoredColors series.data q.castSucc)
          (series.data.coloring q.castSucc) choice.selected previousProper
          previousOneUncolored choice.selectedProper choice.selectedOneUncolored).mp
        choice.selectedStable e (hboundary he)
        (Or.inr ⟨c, Finset.mem_union.mpr (Or.inl htreeOld), hec⟩)
      have heold : series.data.coloring q.castSucc e = some c := by
        exact hstable.symm ▸ hec
      exact previousClosed he hx heold hmissOld
    have htree : TreeMissingColors secondStable tree =
        TreeMissingColors choice.selected tree := by
      ext a
      simp only [TreeMissingColors, Finset.mem_biUnion]
      constructor <;> rintro ⟨x, hx, ha⟩ <;> refine ⟨x, hx, ?_⟩
      · rw [(secondStableRelation.2 x hx)] at ha
        exact ha
      · rw [← (secondStableRelation.2 x hx)] at ha
        exact ha
    have hclosedSecond : ColoredVertexSetClosed G secondStable vertices := by
      intro e c x he hx hec hmiss
      have hmissSel : c ∈ MissingColors G choice.selected x :=
        (secondStableRelation.2 x hx).symm ▸ hmiss
      have htreeSel : c ∈ TreeMissingColors choice.selected tree := by
        unfold TreeMissingColors
        simp only [Finset.mem_biUnion]
        exact ⟨x, hx, hmissSel⟩
      have hstable := hreverseEdge e (hboundary he)
        (Or.inr ⟨c, Finset.mem_union.mpr (Or.inl htreeSel), hec⟩)
      exact (hclosedSelected he hx (hstable ▸ hec)
          hmissSel).elim
    have hchoiceBoundary : choice.edge ∈ BoundaryEdges G vertices := by
      rcases choice.edgeDefective with ⟨c, hc, he⟩
      exact (Finset.mem_filter.mp he).1
    have hchoiceTree : TreeIncidentEdge tree choice.edge := hboundary hchoiceBoundary
    have hchoiceStable : secondStable choice.edge = choice.selected choice.edge := by
      exact secondStableRelation.1 choice.edge hchoiceTree
        ⟨choice.color, Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self _ _)),
          choice.edgeColor⟩
    have hchoiceSecond : secondStable choice.edge = some choice.color :=
      hchoiceStable.trans choice.edgeColor
    have hneq : choice.color ≠ chosenGamma := by
      intro heq
      have hp : chosenGamma ∈ PresentColors G secondStable choice.vertex := by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨choice.edge, choice.edgeIncident, heq ▸ hchoiceSecond⟩
      have hpnot : chosenGamma ∉ PresentColors G secondStable choice.vertex := by
        simpa [MissingColors] using hmissing
      exact hpnot hp
    have hgammaSelected : chosenGamma ∈
        TreeMissingColors choice.selected tree := by
      unfold TreeMissingColors
      simp only [Finset.mem_biUnion]
      exact ⟨choice.vertex, choice.vertexDefective.1,
        (secondStableRelation.2 choice.vertex choice.vertexDefective.1).symm ▸ hmissing⟩
    have hboundaryColor : ∀ {e : E} (c : Fin k),
        c ∈ TreeMissingColors choice.selected tree ∪
          insert choice.color (TashkinovStoredColors series.data q.castSucc) →
        (e ∈ BoundaryColorEdges G secondStable vertices c ↔
        e ∈ BoundaryColorEdges G choice.selected vertices c) := by
      intro e c hcset
      constructor <;> intro he
      · have hb : e ∈ BoundaryEdges G vertices := (Finset.mem_filter.mp he).1
        have hc : secondStable e = some c := (Finset.mem_filter.mp he).2
        have hs : secondStable e = choice.selected e := by
          apply hreverseEdge e (hboundary hb)
          exact Or.inr ⟨c, hcset, hc⟩
        apply Finset.mem_filter.mpr
        exact ⟨hb, hs.symm ▸ hc⟩
      · have hb : e ∈ BoundaryEdges G vertices := (Finset.mem_filter.mp he).1
        have hc : choice.selected e = some c := (Finset.mem_filter.mp he).2
        have hs : secondStable e = choice.selected e := by
          apply hreverseEdge e (hboundary hb)
          exact Or.inl ⟨c, hcset, hc⟩
        apply Finset.mem_filter.mpr
        exact ⟨hb, hs.trans hc⟩
    have hrhoGammaEmpty : BoundaryColorEdges G secondStable vertices chosenGamma = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro ⟨e, he⟩
      simp only [BoundaryColorEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
      have hb : e ∈ BoundaryEdges G vertices := he.1
      have hc : secondStable e = some chosenGamma := he.2
      have hn : chosenGamma ∉ MissingColors G secondStable choice.vertex := by
        intro hm
        exact (hclosedSecond hb
          (show choice.vertex ∈ vertices from choice.vertexDefective.1) hc) hm
      exact (hn hmissing).elim
    have hfGamma : Sum.inr choice.edge ∈
        TwoColorComponent G secondStable chosenGamma choice.color
          (Sum.inl choice.vertex) := by
      apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      simp [TwoColorIncidenceGraph, choice.edgeIncident, hchoiceSecond]
    have hcomponentEdge : ∀ e,
        Sum.inr e ∈ TwoColorComponent G secondStable chosenGamma choice.color
          (Sum.inl choice.vertex) →
        secondStable e = some chosenGamma ∨ secondStable e = some choice.color := by
      intro e he
      have hs : Sum.inr e ∈
          (TwoColorIncidenceGraph G secondStable chosenGamma choice.color).support := by
        apply SimpleGraph.mem_support_of_reachable
          (G := TwoColorIncidenceGraph G secondStable chosenGamma choice.color)
          (u := Sum.inr e) (v := Sum.inl choice.vertex) (by simp)
        exact SimpleGraph.ConnectedComponent.eq.mp he
      obtain ⟨r, hr⟩ :=
        (TwoColorIncidenceGraph G secondStable chosenGamma choice.color).mem_support.mp hs
      cases r with
      | inl x => exact hr.2
      | inr x => simpa [TwoColorIncidenceGraph] using hr
    have hcurrentOutside : ∀ e, Sum.inr e ∉
        TwoColorComponent G secondStable chosenGamma choice.color
          (Sum.inl choice.vertex) →
        series.data.coloring q.succ e = secondStable e := by
      intro e he
      rw [congrFun currentColoring e]
      simp [TwoColorComponentSwap, he]
    have hcurrentF : series.data.coloring q.succ choice.edge = some chosenGamma := by
      rw [congrFun currentColoring choice.edge]
      simp [TwoColorComponentSwap, hfGamma, hchoiceSecond]
    have f_eq : f = choice.edge := by
      rw [currentEdges] at hedge
      exact Finset.singleton_inj.mp hedge |>.symm
    have hcurrentGamma : ∀ e,
        e ∈ BoundaryColorEdges G (series.data.coloring q.succ) vertices chosenGamma ↔
          e = choice.edge := by
      intro e
      constructor
      · intro he
        simp only [BoundaryColorEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
        have hb0 : e ∈ BoundaryEdges G vertices := he.1
        have hb := hb0
        simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hb
        have hc : series.data.coloring q.succ e = some chosenGamma := he.2
        by_cases hcomp : Sum.inr e ∈
            TwoColorComponent G secondStable chosenGamma choice.color
              (Sum.inl choice.vertex)
        · have hce := hcomponentEdge e hcomp
          have hcol : secondStable e = some choice.color := by
            rcases hce with hce | hce
            · have hn : secondStable e ≠ some chosenGamma := by
                intro heq
                have hp : chosenGamma ∈ PresentColors G secondStable choice.vertex := by
                  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
                  rcases hb with ⟨x, hx, y, hy, hexy⟩
                  have hxe : Incident G x e := by simpa [Incident, hexy]
                  have hxcomp : Sum.inl x ∈
                      TwoColorComponent G secondStable chosenGamma choice.color
                        (Sum.inl choice.vertex) := by
                    change (TwoColorIncidenceGraph G secondStable chosenGamma choice.color).connectedComponentMk
                      (Sum.inl x) = _
                    have hadj : (TwoColorIncidenceGraph G secondStable chosenGamma choice.color).Adj
                        (Sum.inl x) (Sum.inr e) := by
                      simp [TwoColorIncidenceGraph, hxe, hce]
                    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hcomp
                  have hxv : x = choice.vertex := hcomponent x hx hxcomp
                  subst x
                  exact ⟨e, hxe, heq⟩
                have hpnot : chosenGamma ∉ PresentColors G secondStable choice.vertex := by
                  simpa [MissingColors] using hmissing
                exact hpnot hp
              exact (hn hce).elim
            · exact hce
          have hceq : e = choice.edge := by
            by_contra hne
            have hx : ∃ x, x ∈ vertices ∧ Incident G x e := by
              rcases hb with ⟨x, hx, y, hy, hexy⟩
              exact ⟨x, hx, by simpa [Incident, hexy]⟩
            rcases hx with ⟨x, hx, hxe⟩
            have hxcomp : Sum.inl x ∈
                TwoColorComponent G secondStable chosenGamma choice.color
                  (Sum.inl choice.vertex) := by
              change (TwoColorIncidenceGraph G secondStable chosenGamma choice.color).connectedComponentMk
                (Sum.inl x) = _
              have hadj : (TwoColorIncidenceGraph G secondStable chosenGamma choice.color).Adj
                  (Sum.inl x) (Sum.inr e) := by
                simp [TwoColorIncidenceGraph, hxe, hcol]
              exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hcomp
            have hxv : x = choice.vertex := hcomponent x hx hxcomp
            subst x
            exact (secondStableProper hne
              ⟨choice.vertex, hxe, choice.edgeIncident⟩ hcol hchoiceSecond).elim
          exact hceq
        · have heq := hcurrentOutside e hcomp
          have hbad : e ∈ BoundaryColorEdges G secondStable vertices chosenGamma := by
            apply Finset.mem_filter.mpr
            exact ⟨hb0, heq.symm.trans hc⟩
          rw [hrhoGammaEmpty] at hbad
          simpa using hbad
      · intro he
        subst e
        apply Finset.mem_filter.mpr
        exact ⟨hchoiceBoundary, hcurrentF⟩
    refine ⟨?_, ?_, ?_⟩
    · ext e
      change e ∈ BoundaryColorEdges G (series.data.coloring q.succ) vertices chosenGamma ↔ e ∈ ({f} : Finset E)
      simpa [f_eq] using hcurrentGamma e
    · intro g hg
      simp only [BoundaryColorEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hg
      have hb0 : g ∈ BoundaryEdges G vertices := hg.1
      have hb := hb0
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      have hc : series.data.coloring q.succ g = some choice.color := hg.2
      have hcomp : Sum.inr g ∉
          TwoColorComponent G secondStable chosenGamma choice.color
            (Sum.inl choice.vertex) := by
        intro hm
        have hce := hcomponentEdge g hm
        have hinside : ∃ x, x ∈ vertices ∧ Incident G x g := by
          rcases hb with ⟨x, hx, y, hy, hexy⟩
          exact ⟨x, hx, by simpa [Incident, hexy]⟩
        rcases hinside with ⟨x, hx, hxe⟩
        have hxcomp : Sum.inl x ∈
            TwoColorComponent G secondStable chosenGamma choice.color
              (Sum.inl choice.vertex) := by
          change (TwoColorIncidenceGraph G secondStable chosenGamma choice.color).connectedComponentMk
            (Sum.inl x) = _
          have hadj : (TwoColorIncidenceGraph G secondStable chosenGamma choice.color).Adj
              (Sum.inl x) (Sum.inr g) := by
            simp [TwoColorIncidenceGraph, hxe, hce]
          exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hm
        have hxv : x = choice.vertex := hcomponent x hx hxcomp
        subst x
        rcases hce with hce | hce
        · have hp : chosenGamma ∈ PresentColors G secondStable choice.vertex := by
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨g, hxe, hce⟩
          have hpnot : chosenGamma ∉ PresentColors G secondStable choice.vertex := by
            simpa [MissingColors] using hmissing
          exact hpnot hp
        · rw [congrFun currentColoring g] at hc
          simp [TwoColorComponentSwap, hm, hce, hneq, hneq.symm] at hc
      have hs : secondStable g = series.data.coloring q.succ g :=
        (hcurrentOutside g hcomp).symm
      have hsc : secondStable g = some choice.color := by
        rw [hs]
        exact hc
      have hgsel : g ∈ BoundaryColorEdges G choice.selected vertices choice.color := by
        apply (hboundaryColor choice.color
          (Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self _ _)))).1
        apply Finset.mem_filter.mpr
        exact ⟨hb0, hsc⟩
      have hdef : DefectiveColor G choice.selected vertices choice.color := by
        have hfmem : choice.edge ∈ BoundaryColorEdges G choice.selected vertices choice.color := by
          apply Finset.mem_filter.mpr
          exact ⟨hchoiceBoundary, choice.edgeColor⟩
        unfold DefectiveColor
        have hne : g ≠ choice.edge := by
          intro heq
          subst g
          exact hcomp hfGamma
        have hsset : ({choice.edge, g} : Finset E) ⊆
            BoundaryColorEdges G choice.selected vertices choice.color := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        have : 2 ≤ ({choice.edge, g} : Finset E).card := by simp [hne, hne.symm]
        exact this.trans (Finset.card_le_card hsset)
      rcases hb with ⟨x, hx, y, hy, hexy⟩
      have hdefv : DefectiveVertex G choice.selected vertices x :=
        ⟨hx, ⟨g, ⟨choice.color, hdef, hgsel⟩, by simpa [Incident, hexy]⟩⟩
      rcases choice.maximal choice.selected x choice.selectedProper
        choice.selectedOneUncolored choice.selectedStable hdefv with hxv | horder
      · subst x
        exfalso
        apply hcomp
        change (TwoColorIncidenceGraph G secondStable chosenGamma choice.color).connectedComponentMk
            (Sum.inr g) = (TwoColorIncidenceGraph G secondStable chosenGamma choice.color).connectedComponentMk
            (Sum.inl choice.vertex)
        apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        simp [TwoColorIncidenceGraph, Incident, hexy, hsc]
      · exact ⟨x, horder, by simpa [Incident, hexy]⟩
    · intro helem
      intro alpha halpha hne
      have hsecondElementary : ColoredVertexSetElementary G secondStable vertices := by
        intro x hx y hy hxy
        have hd := helem hx hy hxy
        simpa only [← secondStableRelation.2 x hx, ← secondStableRelation.2 y hy,
          ← choice.selectedStable.2 x hx, ← choice.selectedStable.2 y hy] using hd
      have hgammaNoOther : ∀ x, x ∈ vertices → x ≠ choice.vertex →
          chosenGamma ∉ MissingColors G secondStable x := by
        intro x hx hneX hm
        have hd := hsecondElementary hx choice.vertexDefective.1 hneX
        exact (Finset.disjoint_left.mp hd) hm hmissing
      have hgammaCurrent : chosenGamma ∉
          TreeMissingColors (series.data.coloring q.succ) tree := by
        intro hm
        rcases (show chosenGamma ∈ TreeMissingColors
            (series.data.coloring q.succ) tree from hm) with hm
        simp only [TreeMissingColors, Finset.mem_biUnion] at hm
        rcases hm with ⟨x, hx, hmx⟩
        by_cases hxeq : x = choice.vertex
        · subst x
          have hp : chosenGamma ∈ PresentColors G (series.data.coloring q.succ) choice.vertex := by
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨choice.edge, choice.edgeIncident, hcurrentF⟩
          have hpnot : chosenGamma ∉ PresentColors G (series.data.coloring q.succ) choice.vertex := by
            simpa [MissingColors] using hmx
          exact hpnot hp
        · have hnot := hgammaNoOther x hx hxeq
          by_cases hp : chosenGamma ∈ MissingColors G secondStable x
          · exact (hnot hp).elim
          · have hp' : chosenGamma ∈ PresentColors G secondStable x := by
              simpa [MissingColors] using hp
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hp'
            rcases hp' with ⟨e, hex, hec⟩
            have heout : Sum.inr e ∉
              TwoColorComponent G secondStable chosenGamma choice.color
                (Sum.inl choice.vertex) := by
              intro hein
              have hecomp := hcomponentEdge e hein
              have hxcomp : Sum.inl x ∈
                  TwoColorComponent G secondStable chosenGamma choice.color
                    (Sum.inl choice.vertex) := by
                change (TwoColorIncidenceGraph G secondStable chosenGamma choice.color).connectedComponentMk
                  (Sum.inl x) = _
                apply (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                  (by simp [TwoColorIncidenceGraph, hex, hecomp])).trans hein
              exact hxeq (hcomponent x hx hxcomp)
            have heeq := hcurrentOutside e heout
            have hpCurrent : chosenGamma ∈ PresentColors G (series.data.coloring q.succ) x := by
              simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨e, hex, heeq.trans hec⟩
            have hpnot : chosenGamma ∉ PresentColors G (series.data.coloring q.succ) x := by
              simpa [MissingColors] using hmx
            exact hpnot hpCurrent
      have halphaGamma : alpha ≠ chosenGamma := by
        intro heq
        subst alpha
        exact hgammaCurrent halpha
      have halphaSecond : ∃ x, x ∈ vertices ∧
          alpha ∈ MissingColors G secondStable x := by
        unfold TreeMissingColors at halpha
        simp only [Finset.mem_biUnion] at halpha
        rcases halpha with ⟨x, hx, hmx⟩
        refine ⟨x, hx, ?_⟩
        by_contra hp
        have hp' : alpha ∈ PresentColors G secondStable x := by
          simpa [MissingColors] using hp
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hp'
        rcases hp' with ⟨e, hex, hec⟩
        have hsame : series.data.coloring q.succ e = some alpha ↔
            secondStable e = some alpha := by
          rw [congrFun currentColoring e]
          by_cases hm : Sum.inr e ∈
              TwoColorComponent G secondStable chosenGamma choice.color
                (Sum.inl choice.vertex)
          · have hce := hcomponentEdge e hm
            rcases hce with hce | hce
            · simp [TwoColorComponentSwap, hm, hce, halphaGamma, hne, hneq]
              constructor
              · intro h
                exact (hne h.symm).elim
              · intro h
                exact (halphaGamma h.symm).elim
            · simp [TwoColorComponentSwap, hm, hce, halphaGamma, hne, hneq]
              constructor
              · intro h
                exact (halphaGamma h.symm).elim
              · intro h
                exact (hne h.symm).elim
          · simp [TwoColorComponentSwap, hm]
        have hpCurrent : alpha ∈ PresentColors G (series.data.coloring q.succ) x := by
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨e, hex, (hsame.mpr hec)⟩
        have hpnot : alpha ∉ PresentColors G (series.data.coloring q.succ) x := by
          simpa [MissingColors] using hmx
        exact hpnot hpCurrent
      rcases halphaSecond with ⟨alphaVertex, halphaVertexIn, halphaVertexMissing⟩
      have hsecondEmpty : BoundaryColorEdges G secondStable vertices alpha = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro hn
        rcases hn with ⟨e, he⟩
        simp only [BoundaryColorEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
        have hb : e ∈ BoundaryEdges G vertices := he.1
        exact (hclosedSecond (f := e) (c := alpha) (v := alphaVertex)
          he.1 halphaVertexIn he.2) halphaVertexMissing
      have hsameAlpha : ∀ e, series.data.coloring q.succ e = some alpha ↔
          secondStable e = some alpha := by
        intro e
        rw [congrFun currentColoring e]
        by_cases hm : Sum.inr e ∈
            TwoColorComponent G secondStable chosenGamma choice.color
              (Sum.inl choice.vertex)
        · have hce := hcomponentEdge e hm
          rcases hce with hce | hce
          · simp [TwoColorComponentSwap, hm, hce, hne, halphaGamma, hneq]
            constructor
            · intro h
              exact (hne h.symm).elim
            · intro h
              exact (halphaGamma h.symm).elim
          · simp [TwoColorComponentSwap, hm, hce, hne, halphaGamma, hneq]
            constructor
            · intro h
              exact (halphaGamma h.symm).elim
            · intro h
              exact (hne h.symm).elim
        · simp [TwoColorComponentSwap, hm]
      ext e
      constructor
      · intro he
        have hs : e ∈ BoundaryColorEdges G secondStable vertices alpha := by
          apply Finset.mem_filter.mpr
          exact ⟨(Finset.mem_filter.mp he).1,
            (hsameAlpha e).mp (Finset.mem_filter.mp he).2⟩
        rw [hsecondEmpty] at hs
        exact False.elim (by simpa using hs)
      · intro he
        exact False.elim (by simpa using he)
