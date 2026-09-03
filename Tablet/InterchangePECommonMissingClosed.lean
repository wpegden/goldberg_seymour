import Tablet.BoundaryColorEdges
import Tablet.BoundaryColorVertex
import Tablet.BoundaryEdges
import Tablet.CertifiedETTPredecessor
import Tablet.ColoredVertexSetElementary
import Tablet.CombinedStableClosurePreserved
import Tablet.CombinedStableColoring
import Tablet.DefectiveColor
import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtendedTashkinovTree
import Tablet.HierarchyBase
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.LooplessMultigraph
import Tablet.MaximumProperty
import Tablet.ModColoring
import Tablet.OrderedTreeUnion
import Tablet.ParallelClosureUnionElementary
import Tablet.ParallelCommonMissingClosed
import Tablet.PartialEdgeColoring
import Tablet.StableColoring
import Tablet.StableColoringBeforeVertex
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TechnicalTheoremBase
import Tablet.TreeColorSetClosed
import Tablet.TreeIncidentEdge
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder
import Tablet.TwoColorComponent
import Tablet.sc2

-- [TABLET NODE: InterchangePECommonMissingClosed]
theorem InterchangePECommonMissingClosed {V E : Type*}
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
                StableColoring (lower.series.data.tree j.castSucc)
                  (TashkinovStoredColors lower.series.data j)
                  (lower.series.data.coloring j) sigma) ∧
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
    (color : Fin k) :
    let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
    color ∈ TreeMissingColors sigma Tn →
      color ∈ TreeMissingColors sigma base.closure →
      TreeColorSetClosed G sigma base.core {color} := by
-- BODY
  classical
  dsimp
  intro hcolorT hcolorR
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
  have hgen : generating = ett.series.data.coloring (Fin.last ett.rounds) :=
    ett.generatingColoring
  have hstableTree : StableColoring Tn
      (TashkinovStoredColors ett.series.data n) generating sigma := by
    simpa [Tn, n] using hstable.1
  have hproperGen : IsProperEdgeColoring G generating := by
    have hstep := ett.series.certified n
    generalize targetEq : n = target at hstep
    cases hstep with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
      have hn : n ≠ 0 := by simp [n]; omega
      exact (hn targetEq).elim
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma closedExtension orderedExtension
        strictExtension =>
      have hi : i.succ = n := by
        apply Fin.ext
        have hv := congrArg Fin.val targetEq
        simp at hv
        omega
      simpa [hgen, n, hi] using currentProper
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      have hlast : ett.series.data.kind n =
          some TashkinovExtensionKind.PE := by simpa [n] using hPE
      rw [targetEq, currentKind] at hlast
      contradiction
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      have hlast : ett.series.data.kind n =
          some TashkinovExtensionKind.PE := by simpa [n] using hPE
      rw [targetEq, currentKind] at hlast
      contradiction
  have honeGen : IsOneEdgeUncolored generating e0 := by
    have hstep := ett.series.certified n
    generalize targetEq : n = target at hstep
    cases hstep with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
      have hn : n ≠ 0 := by simp [n]; omega
      exact (hn targetEq).elim
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma closedExtension orderedExtension
        strictExtension =>
      have hi : i.succ = n := by
        apply Fin.ext
        have hv := congrArg Fin.val targetEq
        simp at hv
        omega
      simpa [hgen, n, hi] using currentOneUncolored
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      have hlast : ett.series.data.kind n =
          some TashkinovExtensionKind.PE := by simpa [n] using hPE
      rw [targetEq, currentKind] at hlast
      contradiction
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      have hlast : ett.series.data.kind n =
          some TashkinovExtensionKind.PE := by simpa [n] using hPE
      rw [targetEq, currentKind] at hlast
      contradiction
  have hlowerElem : ColoredVertexSetElementary G
      (ett.series.data.coloring ⟨ett.rounds - 1, by omega⟩)
      (TreeSequenceVertexSet Tn) := by
    set_option maxHeartbeats 800000 in
      by_cases honeRound : ett.rounds = 1
    · have htech := TechnicalTheoremBase G k ett.rounds e0 input ett.series
      have hn : n = (⟨1, by omega⟩ : Fin (ett.rounds + 1)) := by
        apply Fin.ext
        simp [n, honeRound]
      have hTn : Tn = ett.series.data.tree ⟨1, by omega⟩ := by
        apply congrArg (fun i : Fin (ett.rounds + 2) => ett.series.data.tree i)
        apply Fin.ext
        simp [Tn, n, honeRound]
      have hcol : (⟨ett.rounds - 1, by omega⟩ : Fin (ett.rounds + 1)) = 0 := by
        apply Fin.ext
        simp [honeRound]
      rw [hTn, hcol]
      exact htech.1
    · have hgt : 1 < ett.rounds := by omega
      obtain ⟨pred, hpredRound, hpredMP, htrees, hdata⟩ :=
        CertifiedETTPredecessor G k e0 input T generating ett hMP hgt
      have hpredElem := hlower pred (by omega) (by omega) hpredMP
      have htree : ColoredVertexSetElementary G
          (ett.series.data.coloring ⟨ett.rounds - 1, by omega⟩)
          (TreeSequenceVertexSet
            (ett.series.data.tree ⟨ett.rounds, by omega⟩)) := hpredElem.1
      have hidx : (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) =
          (Fin.last ett.rounds).castSucc := by
        apply Fin.ext
        rfl
      rw [hidx] at htree
      exact htree
  have hcommon := ParallelCommonMissingClosed G k e0 input T generating
      generating ett hpositive base hgen hPE hlowerElem
  have hgenCommon : color ∈ TreeMissingColors generating Tn := by
    have hs := hstable.1.2
    unfold TreeMissingColors at *
    rcases Finset.mem_biUnion.mp (show color ∈
      TreeMissingColors sigma Tn from hcolorT) with ⟨v, hv, hc⟩
    refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
    rw [← hs v hv]
    exact hc
  have hgenClosure : color ∈ TreeMissingColors generating base.closure := by
    have hs := hstable.2.2
    unfold TreeMissingColors at *
    rcases Finset.mem_biUnion.mp (show color ∈
      TreeMissingColors sigma base.closure from hcolorR) with ⟨v, hv, hc⟩
    refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
    rw [← hs v hv]
    exact hc
  have hstableRevTree : StableColoring Tn
        (TashkinovStoredColors ett.series.data n) sigma generating := by
    let a : {psi : PartialEdgeColoring E k //
        IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
      ⟨generating, hproperGen, honeGen⟩
    let b : {psi : PartialEdgeColoring E k //
        IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
      ⟨sigma, hproper, hone⟩
    have hab : StableColoring Tn
        (TashkinovStoredColors ett.series.data n) a.1 b.1 := by
      simpa [a, b] using hstableTree
    have hba := (sc2 G e0 Tn
      (TashkinovStoredColors ett.series.data n)).symm hab
    simpa [a, b] using hba
  have hstableRevClosure : StableColoring base.closure ∅ sigma generating := by
    let a : {psi : PartialEdgeColoring E k //
        IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
      ⟨generating, hproperGen, honeGen⟩
    let b : {psi : PartialEdgeColoring E k //
        IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
      ⟨sigma, hproper, hone⟩
    have hab : StableColoring base.closure ∅ a.1 b.1 := by
      simpa [a, b] using hstable.2
    have hba := (sc2 G e0 base.closure ∅).symm hab
    simpa [a, b] using hba
  obtain ⟨orderedUnion⟩ := (base.parallel hPE).2.2
  have coreVertices : TreeSequenceVertexSet base.core =
      TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet base.closure := by
    rw [← orderedUnion.vertexSet]
  unfold TreeColorSetClosed
  intro c hc
  have hcEq : c = color := by simpa using hc
  subst c
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro g hg
  have hgParts : g ∈ BoundaryEdges G (TreeSequenceVertexSet base.core) ∧
      sigma g = some color := by
    simpa [BoundaryColorEdges] using hg
  obtain ⟨hb, hcolorSigma⟩ := hgParts
  have hbParts : ∃ p ∈ TreeSequenceVertexSet base.core, ∃ r ∉
      TreeSequenceVertexSet base.core, G.ends g = s(p, r) := by
    simpa [BoundaryEdges] using hb
  obtain ⟨p, hp, r, hr, hends⟩ := hbParts
  have hxCore : TreeSequenceVertexSet Tn ⊆
      TreeSequenceVertexSet base.core := by
    rw [coreVertices]
    exact Finset.subset_union_left
  have hyCore : TreeSequenceVertexSet base.closure ⊆
      TreeSequenceVertexSet base.core := by
    rw [coreVertices]
    exact Finset.subset_union_right
  have incidentAt : Incident G p g := by
    change p ∈ G.ends g
    rw [hends]
    exact Sym2.mem_mk_left _ _
  have hgenBoundary : g ∈ BoundaryColorEdges G generating
      (TreeSequenceVertexSet base.core) color := by
    have hbgen : g ∈ BoundaryEdges G (TreeSequenceVertexSet base.core) := hb
    have hcoreColor : generating g = some color := by
      by_cases hpX : p ∈ TreeSequenceVertexSet Tn
      · have hinc : TreeIncidentEdge Tn g := ⟨p, hpX, incidentAt⟩
        have hmiss : color ∈ TreeMissingColors sigma Tn := by
          simpa [Tn, n] using hcolorT
        have heq := hstableRevTree.1 g hinc
          ⟨color, Finset.mem_union_left _ hmiss, hcolorSigma⟩
        exact heq.trans hcolorSigma
      · have hpY : p ∈ TreeSequenceVertexSet base.closure := by
          have hu : p ∈ TreeSequenceVertexSet Tn ∪
              TreeSequenceVertexSet base.closure := by
            rw [← coreVertices]
            exact hp
          exact (Finset.mem_union.mp hu).resolve_left hpX
        have hinc : TreeIncidentEdge base.closure g :=
          ⟨p, hpY, incidentAt⟩
        have hmiss : color ∈ TreeMissingColors sigma base.closure := hcolorR
        have heq := hstableRevClosure.1 g hinc
          ⟨color, Finset.mem_union_left _ hmiss, hcolorSigma⟩
        exact heq.trans hcolorSigma
    simp [BoundaryColorEdges, hbgen, hcoreColor]
  have hgenEmpty := hcommon color
    (Finset.mem_inter.mpr ⟨hgenCommon, hgenClosure⟩)
  rw [hgenEmpty] at hgenBoundary
  simpa using hgenBoundary
