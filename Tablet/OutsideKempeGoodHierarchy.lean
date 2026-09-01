import Tablet.OutsideKempeRecoloringStable
import Tablet.OrderedTreeUnion
import Tablet.SameGoodHierarchy

-- [TABLET NODE: OutsideKempeGoodHierarchy]
theorem OutsideKempeGoodHierarchy {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    {input₁ input₂ : PartialEdgeColoring E k} (T : TreeSequence G e0)
    (phi sigma : PartialEdgeColoring E k)
    (ett₁ : ExtendedTashkinovTree G k e0 input₁ T phi)
    (ett₂ : ExtendedTashkinovTree G k e0 input₂ T sigma)
    (base₁ : HierarchyBase ett₁ phi) (base₂ : HierarchyBase ett₂ sigma)
    (H₁ : TashkinovHierarchy ett₁ base₁)
    (H₂ : TashkinovHierarchy ett₂ base₂)
    (hsame : SameHierarchyStages H₁ H₂)
    (good₁ : GoodHierarchy H₁)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (alpha beta : Fin k)
    (hrecolor : OutsideKempeRecoloring T phi sigma alpha beta)
    (hrung : ett₁.rounds = ett₂.rounds)
    (hseries :
      ∀ i : Fin (ett₁.rounds + 1),
        ett₁.series.data.stored i = ett₂.series.data.stored
          (Fin.cast (congrArg (fun r => r + 1) hrung) i)) :
    ∃ good₂ : GoodHierarchy H₂, SameGoodHierarchy good₁ good₂ := by
-- BODY
  classical
  have stable := OutsideKempeRecoloringStable G e0 T ∅ phi sigma alpha beta
    hproper hone hrecolor
  have hmissing : ∀ v ∈ TreeSequenceVertexSet T,
      MissingColors G phi v = MissingColors G sigma v := fun v hv =>
    (stable.2.2.1.2 v hv).symm
  have hfixed : ∀ f, TreeIncidentEdge T f → sigma f = phi f := stable.2.2.2.2
  rcases hsame with ⟨hcore, hcount, hstage, hposition, hpe⟩
  have hsame' : SameHierarchyStages H₁ H₂ :=
    ⟨hcore, hcount, hstage, hposition, hpe⟩
  let stageTypes : ℕ → Sort _ := fun q => Fin (q + 2) → TreeSequence G e0
  let positionTypes : ℕ → Sort _ := fun q => Fin q → Fin (T.length + 1)
  have transportStage : ∀ {n m : ℕ} (h : n = m)
      (f : Fin (n + 2) → TreeSequence G e0)
      (g : Fin (m + 2) → TreeSequence G e0), HEq f g →
      f = cast (congrArg (fun q => Fin (q + 2) → TreeSequence G e0) h).symm g := by
    intro n m h f g hg
    cases h
    exact eq_of_heq hg
  have transportPosition : ∀ {n m : ℕ} (h : n = m)
      (f : Fin n → Fin (T.length + 1))
      (g : Fin m → Fin (T.length + 1)), HEq f g →
      f = cast (congrArg (fun q => Fin q → Fin (T.length + 1)) h).symm g := by
    intro n m h f g hg
    cases h
    exact eq_of_heq hg
  have transportStageAt : ∀ {n m : ℕ} (h : n = m)
      (f : Fin (n + 2) → TreeSequence G e0)
      (g : Fin (m + 2) → TreeSequence G e0), HEq f g →
      ∀ j : Fin (m + 2), f (Fin.cast (congrArg (fun q : ℕ => q + 2) h).symm j) = g j := by
    intro n m h f g hg j
    cases h
    simpa using congrFun (eq_of_heq hg) j
  have transportPositionAt : ∀ {n m : ℕ} (h : n = m)
      (f : Fin n → Fin (T.length + 1))
      (g : Fin m → Fin (T.length + 1)), HEq f g →
      ∀ j : Fin m, f (Fin.cast h.symm j) = g j := by
    intro n m h f g hg j
    cases h
    simpa using congrFun (eq_of_heq hg) j
  have hstageEq : H₁.stage = cast (congrArg stageTypes hcount).symm H₂.stage := by
    exact transportStage hcount H₁.stage H₂.stage hstage
  have hpositionEq : H₁.dividerPosition =
      cast (congrArg positionTypes hcount).symm H₂.dividerPosition := by
    exact transportPosition hcount H₁.dividerPosition H₂.dividerPosition hposition
  have stageAt : ∀ j : Fin (H₂.dividerCount + 2),
      H₁.stage (Fin.cast (congrArg (fun q => q + 2) hcount).symm j) = H₂.stage j := by
    intro j
    exact transportStageAt hcount H₁.stage H₂.stage hstage j
  have positionAt : ∀ j : Fin H₂.dividerCount,
      H₁.dividerPosition (Fin.cast hcount.symm j) = H₂.dividerPosition j := by
    intro j
    exact transportPositionAt hcount H₁.dividerPosition H₂.dividerPosition hposition j
  have starredAt : ∀ j : Fin (H₂.dividerCount + 1),
      HierarchyStarredStage H₁ (Fin.cast (congrArg (fun q => q + 1) hcount).symm j) =
        HierarchyStarredStage H₂ j := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa [HierarchyStarredStage] using hcore
    · have hs := stageAt i.succ.castSucc
      simpa [HierarchyStarredStage] using hs
  have storedTransport : ∀ {n m : ℕ}
      (h : n = m) (d₁ : TashkinovSeriesData G k n e0)
      (d₂ : TashkinovSeriesData G k m e0),
      (∀ i : Fin (n + 1), d₁.stored i = d₂.stored
        (Fin.cast (congrArg (fun q : ℕ => q + 1) h) i)) →
      TreeMissingColors (d₁.coloring (Fin.last n)) (d₁.tree (Fin.last n).castSucc) =
        TreeMissingColors (d₂.coloring (Fin.last m)) (d₂.tree (Fin.last m).castSucc) →
      TashkinovStoredColors d₁ (Fin.last n) = TashkinovStoredColors d₂ (Fin.last m) := by
    intro n m h d₁ d₂ hs hm
    cases h
    simp [TashkinovStoredColors, hs, hm]
  let gamma : Fin (H₂.dividerCount + 1) → Fin k → Finset (Fin k) :=
    fun j eta => good₁.gamma (Fin.cast (congrArg (fun q => q + 1) hcount).symm j) eta
  have initialSubset : ∀ {A B : TreeSequence G e0},
      TreeSequenceInitialSegment A B →
        TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro A B hab v hv
    simp only [TreeSequenceVertexSet, Finset.mem_image] at hv ⊢
    obtain ⟨i, hi, hvi⟩ := hv
    obtain ⟨hlen, hvertices, hedges⟩ := hab
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i, Finset.mem_univ _,
      (hvertices i).trans hvi⟩
  have stageSubset₁ : ∀ j : Fin (H₁.dividerCount + 2),
      TreeSequenceVertexSet (H₁.stage j) ⊆ TreeSequenceVertexSet T := by
    intro j
    exact Fin.reverseInduction (motive := fun q =>
      TreeSequenceVertexSet (H₁.stage q) ⊆ TreeSequenceVertexSet T) (by
      simpa [H₁.terminalStage]) (by
      intro i hi
      exact (initialSubset (H₁.nested i)).trans hi) j
  have stageSubset₂ : ∀ j : Fin (H₂.dividerCount + 2),
      TreeSequenceVertexSet (H₂.stage j) ⊆ TreeSequenceVertexSet T := by
    intro j
    exact Fin.reverseInduction (motive := fun q =>
      TreeSequenceVertexSet (H₂.stage q) ⊆ TreeSequenceVertexSet T) (by
      simpa [H₂.terminalStage]) (by
      intro i hi
      exact (initialSubset (H₂.nested i)).trans hi) j
  have missingTree : ∀ {A : TreeSequence G e0},
      TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet T →
      TreeMissingColors phi A = TreeMissingColors sigma A := by
    intro A hA
    ext c
    simp only [TreeMissingColors, Finset.mem_biUnion]
    constructor <;> intro hc
    · obtain ⟨v, hv, hvc⟩ := hc
      exact ⟨v, hv, (Finset.ext_iff.mp (hmissing v (hA hv)) c).mp hvc⟩
    · obtain ⟨v, hv, hvc⟩ := hc
      exact ⟨v, hv, (Finset.ext_iff.mp (hmissing v (hA hv)) c).mpr hvc⟩
  have finalTreeEq :
      ett₁.series.data.tree (Fin.last ett₁.rounds).castSucc =
        ett₂.series.data.tree (Fin.last ett₂.rounds).castSucc := by
    calc
      _ = H₁.stage 0 := H₁.baseStage.symm
      _ = H₂.stage 0 := by
        have hh := transportStageAt hcount H₁.stage H₂.stage hstage 0
        have hz : Fin.cast (congrArg (fun q : ℕ => q + 2) hcount).symm
            (0 : Fin (H₂.dividerCount + 2)) = 0 := by
          apply Fin.ext
          rfl
        rw [hz] at hh
        exact hh
      _ = _ := H₂.baseStage
  have finalMissingEq :
      TreeMissingColors phi (ett₁.series.data.tree (Fin.last ett₁.rounds).castSucc) =
        TreeMissingColors sigma (ett₂.series.data.tree (Fin.last ett₂.rounds).castSucc) := by
    rw [← finalTreeEq]
    apply missingTree
    simpa [H₁.baseStage] using stageSubset₁ 0
  have storedBaseEq :
      TashkinovStoredColors ett₁.series.data (Fin.last ett₁.rounds) =
        TashkinovStoredColors ett₂.series.data (Fin.last ett₂.rounds) := by
    have finalColorMissingEq :
        TreeMissingColors (ett₁.series.data.coloring (Fin.last ett₁.rounds))
            (ett₁.series.data.tree (Fin.last ett₁.rounds).castSucc) =
          TreeMissingColors (ett₂.series.data.coloring (Fin.last ett₂.rounds))
            (ett₂.series.data.tree (Fin.last ett₂.rounds).castSucc) := by
      simpa [← ett₁.generatingColoring, ← ett₂.generatingColoring] using finalMissingEq
    exact storedTransport hrung ett₁.series.data ett₂.series.data hseries
      finalColorMissingEq
  have starredSubset₁ : ∀ j : Fin (H₁.dividerCount + 1),
      TreeSequenceVertexSet (HierarchyStarredStage H₁ j) ⊆ TreeSequenceVertexSet T := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact (initialSubset H₁.coreInsideFirst).trans (stageSubset₁ ⟨1, by omega⟩)
    · exact stageSubset₁ i.succ.castSucc
  have starredSubset₂ : ∀ j : Fin (H₂.dividerCount + 1),
      TreeSequenceVertexSet (HierarchyStarredStage H₂ j) ⊆ TreeSequenceVertexSet T := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact (initialSubset H₂.coreInsideFirst).trans (stageSubset₂ ⟨1, by omega⟩)
    · exact stageSubset₂ i.succ.castSucc
  have starredMissingAt : ∀ j : Fin (H₂.dividerCount + 1),
      TreeMissingColors phi (HierarchyStarredStage H₁
        (Fin.cast (congrArg (fun q => q + 1) hcount).symm j)) =
      TreeMissingColors sigma (HierarchyStarredStage H₂ j) := by
    intro j
    rw [starredAt j]
    apply missingTree
    exact starredSubset₂ _
  have stageMissingAt : ∀ j : Fin (H₂.dividerCount + 2),
      TreeMissingColors phi (H₁.stage (Fin.cast (congrArg (fun q : ℕ => q + 2) hcount).symm j)) =
        TreeMissingColors sigma (H₂.stage j) := by
    intro j
    rw [stageAt j]
    apply missingTree
    exact stageSubset₂ j
  have firstMissingAt : ∀ eta : Fin k,
      HierarchyFirstMissingPosition phi T eta = HierarchyFirstMissingPosition sigma T eta := by
    intro eta
    unfold HierarchyFirstMissingPosition
    have candidatesEq :
        (Finset.univ.filter fun i => eta ∈ MissingColors G phi (T.vertex i)) =
        (Finset.univ.filter fun i => eta ∈ MissingColors G sigma (T.vertex i)) := by
      ext i
      have hv := hmissing (T.vertex i) (by simp [TreeSequenceVertexSet])
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
        (show (eta ∈ MissingColors G phi (T.vertex i)) ↔
          eta ∈ MissingColors G sigma (T.vertex i) from by rw [hv])
    rw [candidatesEq]
  have edgeFixed : ∀ {A : TreeSequence G e0},
      TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet T →
      ∀ r : Fin A.length, sigma (A.edge r) = phi (A.edge r) := by
    intro A hA r
    rcases A.attaches r with ⟨i, hi⟩
    apply hfixed
    refine ⟨A.vertex r.succ, ?_, ?_⟩
    · apply hA
      simp [TreeSequenceVertexSet]
    · simp [Incident, hi]
  have stageSuccAt : ∀ (j : Fin (H₂.dividerCount + 1)),
      H₁.stage ((Fin.cast (congrArg (fun q : ℕ => q + 1) hcount).symm j).succ) =
        H₂.stage j.succ := by
    intro j
    have hi : (Fin.cast (congrArg (fun q : ℕ => q + 1) hcount).symm j).succ =
        Fin.cast (congrArg (fun q : ℕ => q + 2) hcount).symm j.succ := by
      apply Fin.ext
      rfl
    rw [hi]
    exact stageAt j.succ
  have segmentAt : ∀ (j : Fin (H₂.dividerCount + 1)) (eta : Fin k),
      HierarchySegmentColors H₁
          (Fin.cast (congrArg (fun q => q + 1) hcount).symm j) eta =
        HierarchySegmentColors H₂ j eta := by
    intro j eta
    simp [HierarchySegmentColors, starredAt, stageAt, stageSuccAt, firstMissingAt,
      edgeFixed (stageSubset₂ _), and_assoc] <;> rw [stageSuccAt j] <;>
      ext x <;> simp [and_assoc]
  have boundaryAt : ∀ {A : TreeSequence G e0},
      TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet T → ∀ c,
      BoundaryColorEdges G phi (TreeSequenceVertexSet A) c =
        BoundaryColorEdges G sigma (TreeSequenceVertexSet A) c := by
    intro A hA c
    ext f
    simp only [BoundaryColorEdges, BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor <;> intro hf
    · obtain ⟨hboundary, hfc⟩ := hf
      obtain ⟨u, hu, v, hv, he⟩ := hboundary
      refine ⟨⟨u, hu, v, hv, he⟩, ?_⟩
      exact (hfixed f ⟨u, hA hu,
        by simpa [Incident, he]⟩).trans hfc
    · obtain ⟨hboundary, hfc⟩ := hf
      obtain ⟨u, hu, v, hv, he⟩ := hboundary
      refine ⟨⟨u, hu, v, hv, he⟩, ?_⟩
      exact (hfixed f ⟨u, hA hu,
        by simpa [Incident, he]⟩).symm.trans hfc
  have closedAt : ∀ {A : TreeSequence G e0},
      TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet T → ∀ C,
      TreeColorSetClosed G phi A C ↔ TreeColorSetClosed G sigma A C := by
    intro A hA C
    unfold TreeColorSetClosed
    constructor <;> intro h c hc
    · exact (boundaryAt hA c).symm ▸ h c hc
    · exact (boundaryAt hA c) ▸ h c hc
  have coreSubset₁ : TreeSequenceVertexSet base₁.core ⊆ TreeSequenceVertexSet T :=
    (initialSubset H₁.coreInsideFirst).trans (stageSubset₁ ⟨1, by omega⟩)
  have coreSubset₂ : TreeSequenceVertexSet base₂.core ⊆ TreeSequenceVertexSet T := by
    rw [← hcore]
    exact coreSubset₁
  have minusAt : ∀ {A : TreeSequence G e0},
      TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet T → ∀ C,
      TreeColorSetMinusClosed G phi A C ↔ TreeColorSetMinusClosed G sigma A C := by
    intro A hA C
    unfold TreeColorSetMinusClosed
    rw [missingTree hA]
    exact closedAt hA _
  have storedEq : ∀ j : Fin (H₂.dividerCount + 1),
      HierarchyStoredColorsAt H₁ (Fin.cast (congrArg (fun q => q + 1) hcount).symm j) =
        HierarchyStoredColorsAt H₂ j := by
    intro j
    dsimp [HierarchyStoredColorsAt]
    rw [storedBaseEq, starredMissingAt]
  have stageTreeAt : ∀ i : Fin H₂.dividerCount,
      H₁.stage (Fin.cast hcount.symm i).castSucc.succ =
        H₂.stage i.castSucc.succ := by
    intro i
    have hs := stageSuccAt i.castSucc
    simpa using hs
  have stageMissingSucc : ∀ i : Fin H₂.dividerCount,
      TreeMissingColors phi (H₁.stage (Fin.cast hcount.symm i).castSucc.succ) =
        TreeMissingColors sigma (H₂.stage i.castSucc.succ) := by
    intro i
    rw [stageTreeAt i]
    exact missingTree (stageSubset₂ _)
  have refreshMissingAt : ∀ i : Fin H₂.dividerCount,
      (TreeSequenceVertexSet (H₂.stage i.succ.castSucc) \
        TreeSequenceVertexSet (HierarchyStarredStage H₂ i.castSucc)).biUnion
          (fun v => MissingColors G phi v) =
      (TreeSequenceVertexSet (H₂.stage i.succ.castSucc) \
        TreeSequenceVertexSet (HierarchyStarredStage H₂ i.castSucc)).biUnion
          (fun v => MissingColors G sigma v) := by
    intro i
    ext c
    simp only [Finset.mem_biUnion]
    constructor <;> intro hc
    · obtain ⟨v, hv, hvc⟩ := hc
      exact ⟨v, hv, (Finset.ext_iff.mp (hmissing v
        (stageSubset₂ _ (Finset.mem_sdiff.mp hv).1)) c).mp hvc⟩
    · obtain ⟨v, hv, hvc⟩ := hc
      exact ⟨v, hv, (Finset.ext_iff.mp (hmissing v
        (stageSubset₂ _ (Finset.mem_sdiff.mp hv).1)) c).mpr hvc⟩
  refine ⟨⟨gamma, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j eta heta
    apply good₁.twoColors
      (Fin.cast (congrArg (fun q => q + 1) hcount).symm j) eta
    rw [storedEq]
    exact heta
  · intro j eta heta
    have h := good₁.avoidance
      (Fin.cast (congrArg (fun q => q + 1) hcount).symm j) eta
      (by simpa [storedEq j] using heta)
    rw [← segmentAt j]
    have stageMissingEq :
        HierarchyStageMissingColors H₁
            (Fin.cast (congrArg (fun q => q + 1) hcount).symm j) =
          HierarchyStageMissingColors H₂ j := by
      unfold HierarchyStageMissingColors
      refine Fin.cases ?_ (fun i => ?_) j
      · have hz : Fin.cast (congrArg (fun q => q + 1) hcount).symm
            (0 : Fin (H₂.dividerCount + 1)) = 0 := by
          apply Fin.ext
          rfl
        rw [hz]
        exact finalMissingEq
      · have hi : Fin.cast (congrArg (fun q => q + 1) hcount).symm i.succ =
            (Fin.cast hcount.symm i).succ := by
          apply Fin.ext
          rfl
        rw [hi]
        have hs := stageMissingAt i.succ.castSucc
        simpa using hs
    rw [← stageMissingEq]
    simpa [gamma] using h
  · intro j eta theta heta htheta hne
    apply good₁.disjointPairs
      (Fin.cast (congrArg (fun q => q + 1) hcount).symm j) eta theta
    · simpa [storedEq j] using heta
    · simpa [storedEq j] using htheta
    · exact hne
  · intro i
    rw [← storedEq i.succ]
    rw [← refreshMissingAt i]
    rw [← starredAt i.castSucc]
    simpa [gamma, HierarchyStageMissingColors, HierarchySegmentColors,
      stageAt, stageSuccAt, starredAt, stageMissingAt,
      firstMissingAt, segmentAt, storedEq, hmissing, hfixed, hcore,
      stageTreeAt, stageMissingSucc] using
      good₁.uniqueRefresh (Fin.cast hcount.symm i)
  · change (ett₂.series.data.kind (Fin.last ett₂.rounds) =
      some TashkinovExtensionKind.PE) → _
    intro hkind
    have hkind₁ : ett₁.series.data.kind (Fin.last ett₁.rounds) =
        some TashkinovExtensionKind.PE := hpe.1.mpr hkind
    have hclosure := hpe.2 hkind₁
    have closureSubset₂ : TreeSequenceVertexSet base₂.closure ⊆
        TreeSequenceVertexSet T := by
      intro v hv
      apply coreSubset₂
      obtain ⟨_, _, ⟨ordered⟩⟩ := base₂.parallel hkind
      rw [ordered.vertexSet]
      exact Finset.mem_union_right _ hv
    have closureMissingEq :
        TreeMissingColors phi base₂.closure =
          TreeMissingColors sigma base₂.closure :=
      missingTree closureSubset₂
    rw [← storedEq 0]
    simpa [gamma, HierarchyStageMissingColors, HierarchySegmentColors,
      HierarchyStarredStage, stageAt, stageSuccAt, starredAt, stageMissingAt,
      firstMissingAt, segmentAt, storedEq, hmissing, hfixed, hcore,
      finalMissingEq, hclosure, closureMissingEq, minusAt coreSubset₁,
      minusAt coreSubset₂] using
      good₁.parallelBase hkind₁
  · intro i
    rw [← storedEq i.succ]
    simpa [gamma, HierarchyStageMissingColors, HierarchySegmentColors,
      HierarchyStarredStage, stageAt, stageSuccAt, starredAt, stageMissingAt,
      firstMissingAt, segmentAt, storedEq, hmissing, hfixed, hcore,
      minusAt (stageSubset₂ _), stageTreeAt, stageMissingSucc] using
      good₁.minusClosed (Fin.cast hcount.symm i)
  · change SameHierarchyStages H₁ H₂ ∧ _
    refine ⟨hsame', hcount, ?_⟩
    intro j
    constructor
    · exact storedEq (Fin.cast (congrArg (fun q => q + 1) hcount) j)
    · intro eta heta
      dsimp [gamma]
