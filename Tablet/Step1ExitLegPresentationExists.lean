import Tablet.ElementaryClosedNoninterchangeableExitPair
import Tablet.GoodHierarchyPrefixRepackage
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyTerminalStoredColors
import Tablet.Step1ExitLegPresentation
import Tablet.TreeSequence
import Tablet.TreeVertexOrder

-- [TABLET NODE: Step1ExitLegPresentationExists]
theorem Step1ExitLegPresentationExists {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base) (good : GoodHierarchy H)
    (hfewer : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (other : ExtendedTashkinovTree G k e0 input' T' generating'),
      other.rounds = ett.rounds → MaximumProperty other →
      ∀ (base' : HierarchyBase other generating')
        (K : TashkinovHierarchy other base'),
        GoodHierarchy K → K.dividerCount < H.dividerCount →
        ColoredVertexSetElementary G generating'
          (TreeSequenceVertexSet T'))
    (hlarge : 2 * ett.rounds + 11 ≤
      (TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card)
    (i : Fin H.dividerCount) (alpha beta : Fin k)
    (halpha : alpha ∈ TreeMissingColors phi (H.stage i.succ.castSucc))
    (hne : alpha ≠ beta)
    (hclosed : TreeColorSetClosed G phi
      (H.stage i.succ.castSucc) {alpha})
    (hnot : ¬ TreeInterchangeable G
      (H.stage i.succ.castSucc) phi alpha beta) :
    Nonempty (Step1ExitLegPresentation G k e0 ett.rounds H.dividerCount) := by
-- BODY
  sorry
