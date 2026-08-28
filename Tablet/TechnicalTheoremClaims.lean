import Tablet.BoundaryColorVertex
import Tablet.ColoredVertexSetElementary
import Tablet.DefectiveColor
import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtendedTashkinovTree
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.ModColoring
import Tablet.StableColoring
import Tablet.StableColoringBeforeVertex
import Tablet.TashkinovExtensionKind
import Tablet.TashkinovStoredColors
import Tablet.TreeInterchangeable
import Tablet.TreeMissingColors
import Tablet.TreeSequenceVertexSet
import Tablet.TreeVertexOrder
import Tablet.TwoColorComponent

-- [TABLET NODE: TechnicalTheoremClaims]
structure TechnicalTheoremClaims {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating) : Prop where
-- BODY
  displayedElementary :
    ColoredVertexSetElementary G generating (TreeSequenceVertexSet T)
  finalStageInterchangeability :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tnext : TreeSequence G e0 :=
      ett.series.data.tree (Fin.last (ett.rounds + 1))
    ∀ sigma : PartialEdgeColoring E k,
      IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
      StableColoring Tnext (TashkinovStoredColors ett.series.data n)
        (ett.series.data.coloring n) sigma →
      ∀ alpha beta : Fin k,
        (alpha ∈ TreeMissingColors sigma Tnext ∨
          beta ∈ TreeMissingColors sigma Tnext) →
        TreeInterchangeable G Tnext sigma alpha beta
  supportingVertexRules :
    (∀ (q : Fin ett.rounds) (v : V),
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
          StableColoringBeforeVertex T v
              (TashkinovStoredColors ett.series.data j)
              (ett.series.data.coloring j) sigma ∧
            StableColoring (ett.series.data.tree j.castSucc)
              (TashkinovStoredColors ett.series.data j)
              (ett.series.data.coloring j) sigma) ∧
    ∀ (q r : Fin ett.rounds) (vq vr : V),
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
          (ett.series.data.stored r.succ)
  terminalParallelPath :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
    ∀ (v : V) (gamma delta : Fin k),
      ett.series.data.kind n = some TashkinovExtensionKind.PE →
      ett.series.data.chosenVertex n = some v →
      ett.series.data.gamma n = some gamma →
      ett.series.data.delta n = some delta →
      ∀ sigma : PartialEdgeColoring E k,
        IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
        StableColoring Tn (TashkinovStoredColors ett.series.data n)
          (ett.series.data.coloring n) sigma →
        ∀ w, w ∈ TreeSequenceVertexSet Tn →
          (Sum.inl w ∈ TwoColorComponent G sigma gamma delta (Sum.inl v) ↔
            w = v)
  defectiveBoundaryOrder :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
    ∀ sigma : PartialEdgeColoring E k,
      IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
      StableColoring Tn (TashkinovStoredColors ett.series.data n)
        (ett.series.data.coloring n) sigma →
      ∀ (delta : Fin k),
        DefectiveColor G sigma (TreeSequenceVertexSet Tn) delta →
        ∀ (v : V),
          BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta v →
          (∃ w, BoundaryColorVertex G sigma (TreeSequenceVertexSet Tn) delta w ∧
            TreeVertexOrder Tn w v) →
          ∀ (hvFinal : v ∈ TreeSequenceVertexSet T)
            (q : Fin ett.rounds) (vi : V),
            (ett.series.data.kind q.succ = some TashkinovExtensionKind.PE ∨
              ett.series.data.kind q.succ = some TashkinovExtensionKind.SE) →
            ett.series.data.chosenVertex q.succ = some vi →
            ETTFirstAppearanceIndex ett v hvFinal ≤ q.val + 1 →
            v = vi ∨ TreeVertexOrder T v vi
  everyStableColoringIsMod :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
    ∀ sigma : PartialEdgeColoring E k,
      IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
      StableColoring Tn (TashkinovStoredColors ett.series.data n)
        (ett.series.data.coloring n) sigma →
      ModColoring ett sigma
