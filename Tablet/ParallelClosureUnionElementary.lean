import Tablet.Basic2
import Tablet.CertifiedETTRestriction
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetElementary
import Tablet.CorrespondingExtendedTashkinovTree
import Tablet.DefectiveColor
import Tablet.DefectiveEdge
import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtendedTashkinovTree
import Tablet.ExtensionBase
import Tablet.ExtensionRules
import Tablet.HierarchyBase
import Tablet.HkuParallelBoundaryStructure
import Tablet.HkuTreeColorsControlled
import Tablet.InternalEdges
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.KTriple
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumDegree
import Tablet.MaximumProperty
import Tablet.MaximumPropertyTransport
import Tablet.MissingColors
import Tablet.ModColoring
import Tablet.OrderedTreeUnion
import Tablet.ParallelExtensionColor
import Tablet.ParallelExtensionUndoStable
import Tablet.ParallelSupportClosureProperties
import Tablet.ParallelTerminalAwayInterchangeable
import Tablet.ParallelTerminalPEPreprocessing
import Tablet.ParallelTwoConstituentPathContradiction
import Tablet.PresentColors
import Tablet.SameColorSeriesPreserved
import Tablet.StableColoring
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovClosure
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.Td
import Tablet.TechnicalTheoremBase
import Tablet.TechnicalInductionContext
import Tablet.TreeIncidentEdge
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix
import Tablet.TreeSequenceVertexSet
import Tablet.TwoColorComponentSwap
import Tablet.TwoColorComponentSwapProper
import Tablet.TwoColorComponentSpanningPath
import Tablet.TwoColorComponentsDisjoint
import Tablet.TwoColorIncidenceDegreeAtMostTwo
import Tablet.TwoColorIncidenceGraph
import Tablet.sc1
import Tablet.sc2

-- [TABLET NODE: ParallelClosureUnionElementary]
theorem ParallelClosureUnionElementary {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
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
    (sigma : PartialEdgeColoring E k)
    (hproper : IsProperEdgeColoring G sigma)
    (hone : IsOneEdgeUncolored sigma e0)
    (hstable : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      phi sigma)
    (baseSigma : HierarchyBase ett sigma) :
    ColoredVertexSetElementary G sigma
      (TreeSequenceVertexSet baseSigma.core) := by
-- BODY
  classical
  have ctx : TechnicalInductionContext G k e0 ett.rounds := by
    refine {
      lowerOne := ?_
      lowerTwo := ?_
      lowerThree := ?_
      lowerFour := ?_
      lowerFive := ?_
      lowerSix := ?_
      currentThree := ?_
      currentFour := ?_
      currentFive := ?_
      currentSix := ?_ }
    · intro input' T' generating' lower hp hlt hmax
      exact (hlower lower hp hlt hmax).1
    · intro input' T' generating' lower hp hlt hmax
      exact (hlower lower hp hlt hmax).2.1
    · intro input' T' generating' lower hp hlt hmax
      exact (hlower lower hp hlt hmax).2.2.1
    · intro input' T' generating' lower hp hlt hmax
      exact (hlower lower hp hlt hmax).2.2.2.1
    · intro input' T' generating' lower hp hlt hmax
      exact (hlower lower hp hlt hmax).2.2.2.2.1
    · intro input' T' generating' lower hp hlt hmax
      exact (hlower lower hp hlt hmax).2.2.2.2.2
    · intro input' T' generating' current hround hmax
      apply ExtensionRules G k e0 input' T' generating' current hmax
        current.roundsPositive
      intro lowerT lowerGenerating lower hp hlt lowerMax
      apply hlower lower hp (by omega) lowerMax
    · intro input' T' generating' current hround hmax
      apply ExtensionBase G k e0 input' T' generating' current hmax
        current.roundsPositive
      intro lowerInput lowerT lowerGenerating lower hp hlt lowerMax
      apply hlower lower hp (by omega) lowerMax
    · intro input' T' generating' current hround hmax
      apply Basic2 G k e0 input' T' generating' current hmax
        current.roundsPositive
      intro lowerInput lowerT lowerGenerating lower hp hlt lowerMax
      apply hlower lower hp (by omega) lowerMax
    · intro input' T' generating' current hround hmax
      apply Td G k e0 input' T' generating' current hmax
        current.roundsPositive
      intro lowerInput lowerT lowerGenerating lower hp hlt lowerMax
      apply hlower lower hp (by omega) lowerMax
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
  have hpre := ParallelTerminalPEPreprocessing G k e0 input T phi ett ctx
    hMP hpositive hPE sigma hproper hone hstable baseSigma
  dsimp at hpre
  rcases hpre with
    ⟨support, common, gamma, delta, hsupport, hgamma, hdelta,
      hsupportT, hsupportJ, hcommonT, hcommonJ, hcommonNe,
      hdeltaMissing, hgammaNotMissing, hcommonMissing, hTElementary⟩
  have hclosure := ParallelSupportClosureProperties G k e0 input T phi ett
    ctx hMP hpositive hPE sigma hproper hone hstable baseSigma
  rcases hclosure with ⟨hJElementary, hJClosed, hJInterchangeable⟩
  have hTInterchangeable :=
    ParallelTerminalAwayInterchangeable G k e0 input T phi ett ctx hMP
      hpositive hPE sigma hproper hone hstable support gamma delta
      hsupport hgamma hdelta
  dsimp at hTInterchangeable
  have hunion : Nonempty (OrderedTreeUnion Tn baseSigma.closure baseSigma.core) := by
    simpa [n, Tn] using (baseSigma.parallel hPE).2.2
  apply ParallelTwoConstituentPathContradiction G k e0 sigma Tn
    baseSigma.closure baseSigma.core hunion hproper hTElementary
    hJElementary hJClosed support common gamma delta hsupportT hsupportJ
    hcommonT hcommonJ hcommonNe hdeltaMissing hgammaNotMissing
    hcommonMissing
  · intro alpha beta halpha hbeta halphaGamma halphaDelta hbetaGamma
      hbetaDelta
    exact hTInterchangeable alpha beta halpha hbeta halphaGamma halphaDelta
      hbetaGamma hbetaDelta
  · exact hJInterchangeable
