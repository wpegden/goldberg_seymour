import Tablet.GoodHierarchy
import Tablet.HierarchyFirstMissingPosition
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.TashkinovAugmentation
import Tablet.TashkinovAugmentationSequence
import Tablet.TashkinovHierarchy
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: GoodHierarchyRestrictedMaximalChain]
theorem GoodHierarchyRestrictedMaximalChain {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (J : TreeSequence G e0)
    (sigma : PartialEdgeColoring E k)
    {generating : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input J generating}
    (baseJ : HierarchyBase ett sigma)
    (KJ : TashkinovHierarchy ett baseJ) (goodJ : GoodHierarchy KJ) :
    let lastJ : Fin (KJ.dividerCount + 1) := Fin.last KJ.dividerCount
    let A : TreeSequence G e0 := HierarchyStarredStage KJ lastJ
    let restrictedColors : TreeSequence G e0 → Fin k → Finset (Fin k) :=
      fun W eta => Finset.univ.filter fun c =>
        ∃ r : Fin W.length, A.length ≤ r.val ∧
          r.val < min (HierarchyFirstMissingPosition sigma W eta).val W.length ∧
          sigma (W.edge r) = some c
    ∃ (m : ℕ) (chain : Fin (m + 1) → TreeSequence G e0)
        (U : TreeSequence G e0),
      chain 0 = J ∧ chain (Fin.last m) = U ∧
      (∀ r : Fin m,
        TashkinovAugmentation sigma (chain r.castSucc) (chain r.succ) ∧
          ∀ eta : Fin k, eta ∈ HierarchyStoredColorsAt KJ lastJ →
            Disjoint (goodJ.gamma lastJ eta)
              (restrictedColors (chain r.succ) eta)) ∧
      (∀ r : Fin (m + 1), (chain r).length = J.length + r.val) ∧
      (∀ r s : Fin (m + 1), r.val ≤ s.val →
        TreeSequenceInitialSegment (chain r) (chain s)) ∧
      (∀ r : Fin m,
        TreeSequenceVertexSet (chain r.castSucc) ⊂
          TreeSequenceVertexSet (chain r.succ)) ∧
      TashkinovAugmentationSequence sigma J U ∧
      (∀ eta : Fin k, eta ∈ HierarchyStoredColorsAt KJ lastJ →
        Disjoint (goodJ.gamma lastJ eta) (restrictedColors U eta)) ∧
      (∀ W : TreeSequence G e0,
        TashkinovAugmentation sigma U W →
        (∀ eta : Fin k, eta ∈ HierarchyStoredColorsAt KJ lastJ →
          Disjoint (goodJ.gamma lastJ eta) (restrictedColors W eta)) →
        False) := by
-- BODY
  let vertexDecidable : DecidableEq V := inferInstance
  classical
  dsimp
  let lastJ : Fin (KJ.dividerCount + 1) := Fin.last KJ.dividerCount
  let A : TreeSequence G e0 := HierarchyStarredStage KJ lastJ
  let colors : TreeSequence G e0 → Fin k → Finset (Fin k) :=
    fun W eta => Finset.univ.filter fun c =>
      ∃ r : Fin W.length, A.length ≤ r.val ∧
        r.val < min (HierarchyFirstMissingPosition sigma W eta).val W.length ∧
        sigma (W.edge r) = some c
  let avoids (W : TreeSequence G e0) : Prop :=
    ∀ eta : Fin k, eta ∈ HierarchyStoredColorsAt KJ lastJ →
      Disjoint (goodJ.gamma lastJ eta) (colors W eta)
  have initialAvoid : avoids J := by
    intro eta heta
    have hgood := goodJ.avoidance lastJ eta heta
    have hterminal : KJ.stage lastJ.succ = J := by
      simpa [lastJ] using KJ.terminalStage
    have hlen : J.length = (KJ.stage lastJ.succ).length :=
      congrArg TreeSequence.length hterminal.symm
    change Disjoint (goodJ.gamma lastJ eta) (colors J eta)
    have hsub : colors J eta ⊆ HierarchySegmentColors KJ lastJ eta := by
      intro c hc
      rcases Finset.mem_filter.mp hc with ⟨_, r, hra, hrb, hcol⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hterminal]
      exact ⟨r, hra, hrb, hcol⟩
    refine Finset.disjoint_left.2 ?_
    intro c hgc hcc
    exact (Finset.mem_sdiff.mp (hgood hgc)).2 (hsub hcc)
  have segmentTrans {X Y Z : TreeSequence G e0}
      (hXY : TreeSequenceInitialSegment X Y)
      (hYZ : TreeSequenceInitialSegment Y Z) :
      TreeSequenceInitialSegment X Z := by
    rcases hXY with ⟨hxy, vxy, exy⟩
    rcases hYZ with ⟨hyz, vyz, eyz⟩
    refine ⟨hxy.trans hyz, ?_, ?_⟩
    · intro i
      calc
        Z.vertex (Fin.castLE (Nat.succ_le_succ (hxy.trans hyz)) i) =
            Z.vertex (Fin.castLE (Nat.succ_le_succ hyz)
              (Fin.castLE (Nat.succ_le_succ hxy) i)) := by congr 1
        _ = Y.vertex (Fin.castLE (Nat.succ_le_succ hxy) i) := vyz _
        _ = X.vertex i := vxy _
    · intro i
      calc
        Z.edge (Fin.castLE (hxy.trans hyz) i) =
            Z.edge (Fin.castLE hyz (Fin.castLE hxy i)) := by congr 1
        _ = Y.edge (Fin.castLE hxy i) := eyz _
        _ = X.edge i := exy _
  have strictOfAug {X Y : TreeSequence G e0}
      (h : TashkinovAugmentation sigma X Y) :
      TreeSequenceVertexSet X ⊂ TreeSequenceVertexSet Y := by
    rcases h with ⟨hlen, hseg, hc⟩
    rcases hseg with ⟨hle, hv, he⟩
    letI : DecidableEq V := Classical.decEq V
    rw [TreeSequenceVertexSet, TreeSequenceVertexSet]
    constructor
    · intro v hvx
      rcases Finset.mem_image.mp hvx with ⟨i, _, hi⟩
      apply Finset.mem_image.mpr
      refine ⟨Fin.castLE (Nat.succ_le_succ hle) i, Finset.mem_univ _, ?_⟩
      exact (hv i).trans hi
    · intro heq
      have hlast : Y.vertex (Fin.last Y.length) ∈
          Finset.univ.image Y.vertex := Finset.mem_image.mpr ⟨Fin.last Y.length,
            Finset.mem_univ _, rfl⟩
      have hback := heq hlast
      rcases Finset.mem_image.mp hback with ⟨i, _, hi⟩
      have hvi : Y.vertex (Fin.last Y.length) =
          Y.vertex (Fin.castLE (Nat.succ_le_succ hle) i) :=
        hi.symm.trans (hv i).symm
      have hind := Y.vertex_injective hvi
      have hval : Y.length = (Fin.castLE (Nat.succ_le_succ hle) i).val :=
        congrArg Fin.val hind
      have hile : (Fin.castLE (Nat.succ_le_succ hle) i).val ≤ X.length := by
        have hi0 : i.val ≤ X.length := by omega
        simpa using hi0
      have : (Fin.castLE (Nat.succ_le_succ hle) i).val < Y.length := by
        omega
      omega
  let Path (n : ℕ) (q : Fin (n + 1) → TreeSequence G e0) : Prop :=
    q 0 = J ∧
    (∀ r : Fin n,
      TashkinovAugmentation sigma (q r.castSucc) (q r.succ) ∧
        avoids (q r.succ)) ∧
    (∀ r : Fin (n + 1), (q r).length = J.length + r.val) ∧
    (∀ r s : Fin (n + 1), r.val ≤ s.val →
      TreeSequenceInitialSegment (q r) (q s))
  have zeroPath : Path 0 (fun _ => J) := by
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro r
      exact Fin.elim0 r
    · intro r
      simp
    · intro r s h
      exact ⟨le_rfl, (fun _ => rfl), (fun _ => rfl)⟩
  have pathBound {n : ℕ} {q : Fin (n + 1) → TreeSequence G e0}
      (hq : Path n q) : n ≤ Fintype.card V := by
    have hc := Fintype.card_le_of_injective (q (Fin.last n)).vertex
      (q (Fin.last n)).vertex_injective
    have hl := hq.2.2.1 (Fin.last n)
    have hcard : J.length + n + 1 ≤ Fintype.card V := by
      simpa [Fintype.card_fin, hl] using hc
    omega
  let attainable : Finset ℕ :=
    (Finset.range (Fintype.card V + 1)).filter
      (fun n => ∃ q : Fin (n + 1) → TreeSequence G e0, Path n q)
  have attainableNonempty : attainable.Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _),
      ⟨fun _ => J, zeroPath⟩⟩⟩
  let m := attainable.max' attainableNonempty
  have hm : m ∈ attainable := Finset.max'_mem attainable attainableNonempty
  rcases Finset.mem_filter.mp hm with ⟨hmrange, ⟨chain, hchain⟩⟩
  have extendPath {n : ℕ} {q : Fin (n + 1) → TreeSequence G e0}
      (hq : Path n q) {W : TreeSequence G e0}
      (haug : TashkinovAugmentation sigma (q (Fin.last n)) W)
      (haw : avoids W) :
      Path (n + 1) (Fin.lastCases W (fun i => q i)) := by
    rcases haug with ⟨hlen, hseg, hc⟩
    let qnew : Fin (n + 2) → TreeSequence G e0 :=
      Fin.lastCases W (fun i => q i)
    have haug' : TashkinovAugmentation sigma (q (Fin.last n)) W :=
      ⟨hlen, hseg, hc⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc by rfl]
      simp only [Fin.lastCases_castSucc]
      exact hq.1
    · intro r
      refine Fin.lastCases ?_ (fun i => ?_) r
      · simpa [qnew, Fin.lastCases_castSucc, Fin.lastCases_last] using ⟨haug', haw⟩
      · simpa only [Fin.lastCases_castSucc, Fin.succ_castSucc] using hq.2.1 i
    · intro r
      refine Fin.lastCases ?_ (fun i => ?_) r
      · simpa [qnew, Fin.lastCases_castSucc, Fin.lastCases_last, Nat.add_assoc,
          hq.2.2.1 (Fin.last n)] using hlen
      · simpa using hq.2.2.1 i
    · intro r s hrs
      revert r
      refine Fin.lastCases ?_ (fun s0 => ?_) s
      · intro r hrs
        revert hrs
        refine Fin.lastCases ?_ (fun r0 => ?_) r
        · intro hrs
          exact ⟨le_rfl, (fun _ => rfl), (fun _ => rfl)⟩
        · intro hrs
          have hbound : r0.val ≤ n := Nat.le_of_lt_succ r0.isLt
          simpa [qnew, Fin.succ_castSucc, Fin.lastCases_last] using
            segmentTrans (hq.2.2.2 r0 (Fin.last n) hbound) hseg
      · intro r hrs
        revert hrs
        refine Fin.lastCases ?_ (fun s1 => ?_) s0
        · intro hrs
          revert hrs
          refine Fin.lastCases ?_ (fun r0 => ?_) r
          · intro hrs
            have hle : (Fin.last (n + 1)).val ≤ (Fin.last n).castSucc.val := by
              simpa using hrs
            have hlt : (Fin.last n).castSucc.val < (Fin.last (n + 1)).val := by
              simp
            exfalso
            exact (Nat.not_le_of_gt hlt) hle
          · intro hrs
            simpa [qnew, Fin.succ_castSucc, Fin.lastCases_last] using
              hq.2.2.2 r0 (Fin.last n) (Nat.le_of_lt_succ r0.isLt)
        · intro hrs
          revert hrs
          refine Fin.lastCases ?_ (fun r1 => ?_) r
          · intro hrs
            have hle : (Fin.last (n + 1)).val ≤ s1.castSucc.castSucc.val := by
              simpa using hrs
            have hlt : s1.castSucc.castSucc.val < (Fin.last (n + 1)).val := by
              have hs : s1.val < n := s1.isLt
              have hs' : s1.val < n + 1 := Nat.lt_succ_of_lt hs
              simpa using hs'
            exfalso
            exact (Nat.not_le_of_gt hlt) hle
          · intro hrs
            simpa [qnew, Fin.succ_castSucc] using
              hq.2.2.2 r1 s1.castSucc (by simpa using hrs)
  have terminal : ∀ W : TreeSequence G e0,
      TashkinovAugmentation sigma (chain (Fin.last m)) W → avoids W → False := by
    intro W hW havoid
    have hp := extendPath hchain hW havoid
    have hnext : m + 1 ≤ Fintype.card V := pathBound hp
    have hmem : m + 1 ∈ attainable := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, ⟨Fin.lastCases W (fun i => chain i), hp⟩⟩
      omega
    have hle := Finset.le_max' attainable (m + 1) hmem
    omega
  let U : TreeSequence G e0 := chain (Fin.last m)
  refine ⟨m, chain, U, hchain.1, rfl, ?_, hchain.2.2.1, hchain.2.2.2, ?_, ?_, ?_, ?_⟩
  · intro r
    exact hchain.2.1 r
  · intro r
    exact strictOfAug (hchain.2.1 r).1
  · have pathSequence : ∀ n (q : Fin (n + 1) → TreeSequence G e0),
        Path n q → TashkinovAugmentationSequence sigma (q 0) (q (Fin.last n)) := by
      intro n
      induction n with
      | zero =>
          intro q hq
          exact Relation.ReflTransGen.refl
      | succ n ih =>
          intro q hq
          let qold : Fin (n + 1) → TreeSequence G e0 := fun i => q i.castSucc
          have hold : Path n qold := by
            refine ⟨?_, ?_, ?_, ?_⟩
            · simpa [qold] using hq.1
            · intro r
              simpa [qold] using hq.2.1 r.castSucc
            · intro r
              simpa [qold] using hq.2.2.1 r.castSucc
            · intro r s hrs
              simpa [qold] using hq.2.2.2 r.castSucc s.castSucc (by simpa using hrs)
          exact Relation.ReflTransGen.tail (ih qold hold) (hq.2.1 (Fin.last n)).1
    simpa [U, hchain.1] using pathSequence m chain hchain
  · intro eta heta
    by_cases hz : m = 0
    · have hidx : Fin.last m = (0 : Fin (m + 1)) := by
        apply Fin.ext
        simpa [hz]
      have hU : U = J := by
        dsimp [U]
        rw [hidx]
        exact hchain.1
      rw [hU]
      exact initialAvoid eta heta
    · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hz
      let r : Fin m := ⟨n, by omega⟩
      have hi : r.succ = Fin.last m := by
        apply Fin.ext
        simp [r, hn]
      have hU : chain r.succ = U := by
        dsimp [U]
        rw [hi]
      rw [← hU]
      simpa [avoids, colors, lastJ] using (hchain.2.1 r).2 eta heta
  · intro W hW havoid
    exact terminal W hW havoid
