import Tablet.AdjacentEdges
import Tablet.BoundaryColorVertex
import Tablet.ColoredVertexSetElementary
import Tablet.CombinedStableClosurePreserved
import Tablet.CombinedStableColoring
import Tablet.DefectiveColor
import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtendedTashkinovTree
import Tablet.HierarchyBase
import Tablet.Incident
import Tablet.InterchangePEClosedCore
import Tablet.InterchangePEClosureConstituent
import Tablet.InterchangePECommonMissingClosed
import Tablet.InterchangePETreeConstituent
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.LooplessMultigraph
import Tablet.MaximumProperty
import Tablet.MissingColors
import Tablet.ModColoring
import Tablet.OrderedTreeUnion
import Tablet.OrderedTreeUnionExists
import Tablet.OutsideKempeRecoloring
import Tablet.OutsideKempeRecoloringStable
import Tablet.P2634_T1_PETerminalFacts
import Tablet.P2668_T2_CopyAugmentationPrefix
import Tablet.P2668_T2_OppositeRootComponents
import Tablet.ParallelClosureUnionElementary
import Tablet.PartialEdgeColoring
import Tablet.PresentColors
import Tablet.StableColoring
import Tablet.StableColoringBeforeVertex
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.TashkinovAugmentationSequenceRestrict
import Tablet.TashkinovClosure
import Tablet.TashkinovClosureExists
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceInitialSegmentVertexSetSubset
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder
import Tablet.TwoColorComponent
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapMissingBehavior
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorIncidenceGraph
import Tablet.TwoColorNontrivialPathComponent
import Tablet.TwoColorPathComponent
import Tablet.sc2

-- [TABLET NODE: InterchangePEMixedCore]
theorem InterchangePEMixedCore {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hlower : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input' T' generating'),
      0 < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
      ColoredVertexSetElementary G generating'
          (TreeSequenceVertexSet T') ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tnext : TreeSequence G e0 :=
           lower.series.data.tree (Fin.last (lower.rounds + 1))
         ∀ sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
           StableColoring Tnext
             (TashkinovStoredColors lower.series.data n)
             (lower.series.data.coloring n) sigma →
           ∀ alpha beta : Fin k,
             (alpha ∈ TreeMissingColors sigma Tnext ∨
               beta ∈ TreeMissingColors sigma Tnext) →
             TreeInterchangeable G Tnext sigma alpha beta) ∧
        ((∀ (q : Fin lower.rounds) (v : V),
          lower.series.data.kind q.succ =
              some TashkinovExtensionKind.PE →
          lower.series.data.chosenVertex q.succ = some v →
          ∀ hvFinal : v ∈ TreeSequenceVertexSet T',
          ∀ j : Fin (lower.rounds + 1),
            ETTFirstAppearanceIndex lower v hvFinal = j.val + 1 →
            ∀ sigma : PartialEdgeColoring E k,
              IsProperEdgeColoring G sigma →
              IsOneEdgeUncolored sigma e0 →
              StableColoring
                (lower.series.data.tree q.succ.castSucc)
                (TashkinovStoredColors lower.series.data q.succ)
                (lower.series.data.coloring q.succ) sigma →
              StableColoringBeforeVertex T' v hvFinal
                  (TashkinovStoredColors lower.series.data j)
                  (lower.series.data.coloring j) sigma ∧
                (0 < j.val →
                  StableColoring (lower.series.data.tree j.castSucc)
                    (TashkinovStoredColors lower.series.data j)
                    (lower.series.data.coloring j) sigma)) ∧
          ∀ (q r : Fin lower.rounds) (vq vr : V),
            q ≠ r → vq ≠ vr →
            lower.series.data.kind q.succ =
                some TashkinovExtensionKind.PE →
            lower.series.data.kind r.succ =
                some TashkinovExtensionKind.PE →
            lower.series.data.chosenVertex q.succ = some vq →
            lower.series.data.chosenVertex r.succ = some vr →
            ∀ (hvq : vq ∈ TreeSequenceVertexSet T')
              (hvr : vr ∈ TreeSequenceVertexSet T'),
              ETTFirstAppearanceIndex lower vq hvq =
                  ETTFirstAppearanceIndex lower vr hvr →
              Disjoint (lower.series.data.stored q.succ)
                (lower.series.data.stored r.succ)) ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tn : TreeSequence G e0 :=
           lower.series.data.tree n.castSucc
         ∀ (v : V) (gamma delta : Fin k),
           lower.series.data.kind n = some TashkinovExtensionKind.PE →
           lower.series.data.chosenVertex n = some v →
           lower.series.data.gamma n = some gamma →
           lower.series.data.delta n = some delta →
           ∀ sigma : PartialEdgeColoring E k,
             IsProperEdgeColoring G sigma →
             IsOneEdgeUncolored sigma e0 →
             StableColoring Tn
               (TashkinovStoredColors lower.series.data n)
               (lower.series.data.coloring n) sigma →
             ∀ w, w ∈ TreeSequenceVertexSet Tn →
               (Sum.inl w ∈ TwoColorComponent G sigma gamma delta
                   (Sum.inl v) ↔ w = v)) ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tn : TreeSequence G e0 :=
           lower.series.data.tree n.castSucc
         ∀ sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
           StableColoring Tn
             (TashkinovStoredColors lower.series.data n)
             (lower.series.data.coloring n) sigma →
           ∀ (delta : Fin k),
             DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta →
             ∀ (v : V),
               BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn)
                   delta v →
               (∃ w, BoundaryColorVertex G sigma
                   (TreeSequenceVertexSet Tn) delta w ∧
                 TreeVertexOrder Tn w v) →
               ∀ (hvFinal : v ∈ TreeSequenceVertexSet T')
                 (q : Fin lower.rounds) (vi : V),
                 (lower.series.data.kind q.succ =
                      some TashkinovExtensionKind.PE ∨
                    lower.series.data.kind q.succ =
                      some TashkinovExtensionKind.SE) →
                 lower.series.data.chosenVertex q.succ = some vi →
                 ETTFirstAppearanceIndex lower v hvFinal ≤ q.val + 1 →
                 v = vi ∨ TreeVertexOrder T' v vi) ∧
        (let n : Fin (lower.rounds + 1) := Fin.last lower.rounds
         let Tn : TreeSequence G e0 :=
           lower.series.data.tree n.castSucc
         ∀ sigma : PartialEdgeColoring E k,
           IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
           StableColoring Tn
             (TashkinovStoredColors lower.series.data n)
             (lower.series.data.coloring n) sigma →
           ModColoring lower sigma))
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (base : HierarchyBase ett generating)
    (hproper : IsProperEdgeColoring G sigma)
    (hone : IsOneEdgeUncolored sigma e0)
    (hstable : CombinedStableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      base.closure
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      generating sigma)
    (alpha beta : Fin k) :
    let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
    alpha ∈ TreeMissingColors sigma Tn →
      beta ∈ TreeMissingColors sigma base.closure →
      TreeInterchangeable G base.core sigma alpha beta := by
-- BODY
  classical
  dsimp
  intro halpha hbeta
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let S := TreeSequencePrefix Tn base.supportPosition.val
    base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt)
  have hSTn : TreeSequenceInitialSegment S Tn :=
    ⟨Nat.le_of_lt_succ base.supportPosition.isLt,
      (fun _ => rfl), (fun _ => rfl)⟩
  obtain ⟨hchosen, _, ⟨ord⟩⟩ := base.parallel hPE
  obtain ⟨hproperGen, honeGen, _⟩ := P2634_T1_PETerminalFacts ett hPE
  have hpreserved := CombinedStableClosurePreserved G k e0 input T
    generating generating sigma ett hpositive base ett.generatingColoring hPE
    hproperGen honeGen hproper hone hstable
  have hclosure : TashkinovClosure sigma S base.closure := hpreserved.2.2
  let baseSigma : HierarchyBase ett sigma := {
    core := base.core
    closure := base.closure
    supportPosition := base.supportPosition
    supportPositive := base.supportPositive
    terminalMissingColors := by
      dsimp
      ext c
      simp only [TreeMissingColors, Finset.mem_biUnion]
      constructor
      · rintro ⟨v, hv, hc⟩
        exact ⟨v, hv, by rw [← hstable.1.2 v hv]; exact hc⟩
      · rintro ⟨v, hv, hc⟩
        exact ⟨v, hv, by rw [hstable.1.2 v hv]; exact hc⟩
    parallel := fun hp => ⟨(base.parallel hp).1,
      hclosure, (base.parallel hp).2.2⟩
    nonparallel := base.nonparallel }
  have helem : ColoredVertexSetElementary G sigma
      (TreeSequenceVertexSet base.core) :=
    ParallelClosureUnionElementary G k e0 input T generating ett hMP
      hpositive hlower hPE sigma hproper hone hstable.1 baseSigma
  have hX : TreeInterchangeable G Tn sigma alpha beta :=
    InterchangePETreeConstituent G k e0 input T generating sigma ett hMP
      hpositive hlower hPE base hproper hone hstable alpha beta halpha
  have hgraph : TwoColorIncidenceGraph G sigma beta alpha =
      TwoColorIncidenceGraph G sigma alpha beta := by
    ext a b
    cases a <;> cases b <;> simp [TwoColorIncidenceGraph, or_comm]
  have hY : TreeInterchangeable G base.closure sigma alpha beta := by
    have hcomp : ∀ z, TwoColorComponent G sigma beta alpha z =
        TwoColorComponent G sigma alpha beta z := by
      intro z
      unfold TwoColorComponent
      rw [hgraph]
    have hrev := InterchangePEClosureConstituent G k e0 input T
      generating sigma ett hMP hpositive hlower hPE base hproper hone
      hstable beta alpha hbeta
    simpa only [TreeInterchangeable, TwoColorPathComponent,
      hcomp, hgraph, ne_comm] using hrev
  by_contra hnot
  obtain ⟨u, hu, hua⟩ := Finset.mem_biUnion.mp halpha
  obtain ⟨v, hv, hvb⟩ := Finset.mem_biUnion.mp hbeta
  obtain ⟨hab, huR, hvTn, avoidTn, _⟩ :=
    P2668_T2_OppositeRootComponents sigma alpha beta Tn base.closure
      base.core ⟨ord⟩ hproper hX hY u v hu hv hua hvb hnot
  let psi := TwoColorComponentSwap G sigma alpha beta (Sum.inl v)
  have hrecolor : OutsideKempeRecoloring Tn sigma psi alpha beta := by
    refine ⟨hab, {Sum.inl v}, ?_, ?_⟩
    · intro z hz x hxc hx
      have hzv : z = Sum.inl v := Finset.mem_singleton.mp hz
      subst z
      exact avoidTn x hx hxc
    · intro f
      simp [psi, TwoColorComponentSwap]
  obtain ⟨hproperPsi, honePsi, hchange, _, _⟩ :=
    OutsideKempeRecoloringStable G e0 Tn
      (TashkinovStoredColors ett.series.data n)
      sigma psi alpha beta hproper hone hrecolor
  have hterminal : StableColoring Tn
      (TashkinovStoredColors ett.series.data n) generating psi := by
    let a : {chi : PartialEdgeColoring E k //
        IsProperEdgeColoring G chi ∧ IsOneEdgeUncolored chi e0} :=
      ⟨generating, hproperGen, honeGen⟩
    let b : {chi : PartialEdgeColoring E k //
        IsProperEdgeColoring G chi ∧ IsOneEdgeUncolored chi e0} :=
      ⟨sigma, hproper, hone⟩
    let c : {chi : PartialEdgeColoring E k //
        IsProperEdgeColoring G chi ∧ IsOneEdgeUncolored chi e0} :=
      ⟨psi, hproperPsi, honePsi⟩
    have hab' : StableColoring Tn
        (TashkinovStoredColors ett.series.data n) a.1 b.1 := hstable.1
    have hbc' : StableColoring Tn
        (TashkinovStoredColors ett.series.data n) b.1 c.1 := hchange
    exact (sc2 G e0 Tn (TashkinovStoredColors ett.series.data n)).trans
      (x := a) (y := b) (z := c) hab' hbc'
  have huCore : u ∈ TreeSequenceVertexSet base.core := by
    rw [ord.vertexSet]
    exact Finset.mem_union_left _ hu
  have hRCore : TreeSequenceVertexSet base.closure ⊆
      TreeSequenceVertexSet base.core := by
    intro x hx
    rw [ord.vertexSet]
    exact Finset.mem_union_right _ hx
  have hvS : v ∉ TreeSequenceVertexSet S := by
    intro h
    exact hvTn (TreeSequenceInitialSegmentVertexSetSubset hSTn h)
  obtain ⟨B, _, hlast, hcopied⟩ :=
    P2668_T2_CopyAugmentationPrefix sigma alpha beta hab hproper
      (Sum.inl v) S base.closure (TreeSequenceVertexSet base.core)
      helem hRCore u v huCore huR hv hvS hua hvb hclosure.1
  obtain ⟨R', hR'⟩ := TashkinovClosureExists psi B
  have hnewClosure : TashkinovClosure psi S R' :=
    ⟨hcopied.trans hR'.1, hR'.2⟩
  obtain ⟨U', hU'⟩ := OrderedTreeUnionExists Tn R'
  let newBase : HierarchyBase ett psi := {
    core := U'
    closure := R'
    supportPosition := base.supportPosition
    supportPositive := base.supportPositive
    terminalMissingColors := by
      dsimp
      ext c
      simp only [TreeMissingColors, Finset.mem_biUnion]
      constructor
      · rintro ⟨x, hx, hc⟩
        exact ⟨x, hx, by rw [← hterminal.2 x hx]; exact hc⟩
      · rintro ⟨x, hx, hc⟩
        exact ⟨x, hx, by rw [hterminal.2 x hx]; exact hc⟩
    parallel := fun hp => ⟨(base.parallel hp).1, hnewClosure, hU'⟩
    nonparallel := by dsimp only; intro hn; exact (hn hPE).elim }
  have hnewElementary : ColoredVertexSetElementary G psi
      (TreeSequenceVertexSet U') :=
    ParallelClosureUnionElementary G k e0 input T generating ett hMP
      hpositive hlower hPE psi hproperPsi honePsi hterminal newBase
  obtain ⟨newOrd⟩ := hU'
  have hvB : v ∈ TreeSequenceVertexSet B := by
    rw [← hlast]
    simp [TreeSequenceVertexSet]
  have hvR' : v ∈ TreeSequenceVertexSet R' :=
    TreeSequenceInitialSegmentVertexSetSubset
      (TashkinovAugmentationSequenceInitialSegment psi B R' hR'.1) hvB
  have huU' : u ∈ TreeSequenceVertexSet U' := by
    rw [newOrd.vertexSet]
    exact Finset.mem_union_left _ hu
  have hvU' : v ∈ TreeSequenceVertexSet U' := by
    rw [newOrd.vertexSet]
    exact Finset.mem_union_right _ hvR'
  have huv : u ≠ v := by intro h; exact hvTn (h ▸ hu)
  have huaPsi : alpha ∈ MissingColors G psi u := by
    rw [hchange.2 u hu]
    exact hua
  have selfv : Sum.inl v ∈ TwoColorComponent G sigma alpha beta (Sum.inl v) :=
    SimpleGraph.ConnectedComponent.eq.mpr (SimpleGraph.Reachable.refl _)
  have hvaPsi : alpha ∈ MissingColors G psi v :=
    (TwoColorComponentSwapMissingBehavior G sigma alpha beta hab hproper
      (Sum.inl v)).2.2.1 v selfv hvb
  exact (Finset.disjoint_left.mp (hnewElementary huU' hvU' huv)) huaPsi hvaPsi
