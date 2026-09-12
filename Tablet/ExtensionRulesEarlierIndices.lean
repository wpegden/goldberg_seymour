import Tablet.ColoredVertexSetElementary
import Tablet.CertifiedETTRestriction
import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtendedTashkinovTree
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.MaximumProperty
import Tablet.StableColoring
import Tablet.StableColoringBeforeVertex
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TashkinovStoredColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: ExtensionRulesEarlierIndices]
theorem ExtensionRulesEarlierIndices {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E)
    (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hLowerThree : ∀ {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input T' generating'),
      0 < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
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
              (lower.series.data.stored r.succ))) :
    ((∀ (q : Fin ett.rounds) (v : V),
        q.succ ≠ Fin.last ett.rounds →
        ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex q.succ = some v →
        ∀ hvFinal : v ∈ TreeSequenceVertexSet T,
        ∀ j : Fin (ett.rounds + 1),
          ETTFirstAppearanceIndex ett v hvFinal = j.val + 1 →
          ∀ sigma : PartialEdgeColoring E k,
            IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
            StableColoring (ett.series.data.tree q.succ.castSucc)
              (TashkinovStoredColors ett.series.data q.succ)
              (ett.series.data.coloring q.succ) sigma →
            StableColoringBeforeVertex T v hvFinal
                (TashkinovStoredColors ett.series.data j)
                (ett.series.data.coloring j) sigma ∧
              (0 < j.val →
                StableColoring (ett.series.data.tree j.castSucc)
                  (TashkinovStoredColors ett.series.data j)
                  (ett.series.data.coloring j) sigma)) ∧
      ∀ (q r : Fin ett.rounds) (vq vr : V),
        q.succ ≠ Fin.last ett.rounds →
        r.succ ≠ Fin.last ett.rounds →
        q ≠ r → vq ≠ vr →
        ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
        ett.series.data.kind r.succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex q.succ = some vq →
        ett.series.data.chosenVertex r.succ = some vr →
        ∀ (hvq : vq ∈ TreeSequenceVertexSet T)
          (hvr : vr ∈ TreeSequenceVertexSet T),
          ETTFirstAppearanceIndex ett vq hvq =
              ETTFirstAppearanceIndex ett vr hvr →
          Disjoint (ett.series.data.stored q.succ)
            (ett.series.data.stored r.succ)) := by
-- BODY
  sorry
