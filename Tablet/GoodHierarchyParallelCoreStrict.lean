import Tablet.GoodHierarchy
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.TashkinovHierarchy
import Tablet.TreeColorSetClosed
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeMissingColors

-- [TABLET NODE: GoodHierarchyParallelCoreStrict]
theorem GoodHierarchyParallelCoreStrict {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T phi}
    {base : HierarchyBase ett phi} {H : TashkinovHierarchy ett base}
    (good : GoodHierarchy H)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (hclosed : TreeColorSetClosed G phi T (TreeMissingColors phi T)) :
    H.stage ⟨1, by omega⟩ ≠ base.core := by
-- BODY
  classical
  intro equality
  have notClosed := good.parallelBase
  dsimp at notClosed
  have notClosedCore :
      ¬ TreeColorSetMinusClosed G phi base.core
          ((HierarchyStoredColorsAt H 0).biUnion (good.gamma 0)) := by
    apply (notClosed hPE).1
  by_cases divider : H.dividerCount = 0
  · have terminal : H.stage ⟨1, by omega⟩ = T := by
      have index : (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) =
          Fin.last (H.dividerCount + 1) := by
        apply Fin.ext
        simp [divider]
      rw [index]
      exact H.terminalStage
    have coreTree : base.core = T := by
      exact equality.symm.trans terminal
    apply notClosedCore
    rw [coreTree]
    unfold TreeColorSetMinusClosed
    intro alpha alphaMem
    apply hclosed alpha
    exact (Finset.mem_sdiff.mp alphaMem).1
  · have positive : 0 < H.dividerCount := Nat.pos_of_ne_zero divider
    let dividerIndex : Fin H.dividerCount := ⟨0, positive⟩
    have refresh := good.uniqueRefresh dividerIndex
    obtain ⟨eta, properties, uniqueness⟩ := refresh
    obtain ⟨etaMem, etaSmall, uniqueness⟩ := properties
    have firstIndex : dividerIndex.succ.castSucc =
        (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) := by
      ext
      simp [dividerIndex]
    have zeroIndex : dividerIndex.castSucc = (0 : Fin (H.dividerCount + 1)) := by
      ext
      simp [dividerIndex]
    have emptyDifference :
        (TreeSequenceVertexSet (H.stage dividerIndex.succ.castSucc) \
          TreeSequenceVertexSet (HierarchyStarredStage H dividerIndex.castSucc)).biUnion
            (fun v => MissingColors G phi v) = ∅ := by
      rw [firstIndex, equality]
      rw [zeroIndex]
      simp [HierarchyStarredStage]
    have smallEmpty : good.gamma dividerIndex.succ eta ⊆ (∅ : Finset (Fin k)) := by
      rw [firstIndex, equality, zeroIndex] at etaSmall
      simpa [HierarchyStarredStage] using etaSmall
    have gammaEmpty : good.gamma dividerIndex.succ eta = ∅ :=
      Finset.subset_empty.mp smallEmpty
    have cardZero : (good.gamma dividerIndex.succ eta).card = 0 := by
      simp [gammaEmpty]
    have cardTwo := good.twoColors dividerIndex.succ eta etaMem
    omega
