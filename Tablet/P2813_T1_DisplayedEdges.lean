import Tablet.P2813_T1_BaseControl
import Tablet.P2813_T1_BaseDisplayedEdges
import Tablet.P2813_T1_TerminalRoute
import Tablet.TashkinovAugmentationSequencePosition
import Tablet.TashkinovAugmentationSequenceInitialSegment
import Tablet.OutsideKempeRecoloringStable

-- [TABLET NODE: P2813_T1_DisplayedEdges]
theorem P2813_T1_DisplayedEdges {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (hprefixElementary :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      let ell := T.length - A.length
      let Ty := TreeSequencePrefix T
        (min (A.length + (ell - 1)) T.length)
        (by have hA := A.positive; have hT := T.positive; omega)
        (Nat.min_le_right _ _)
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet Ty))
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (hmissingPrefix :
      let H := C.hierarchy
      let A := HierarchyStarredStage H (Fin.last H.dividerCount)
      let ell := T.length - A.length
      let Ty := TreeSequencePrefix T
        (min (A.length + (ell - 1)) T.length)
        (by have hA := A.positive; have hT := T.positive; omega)
        (Nat.min_le_right _ _)
      alpha ∈ TreeMissingColors phi Ty ∧
        beta ∈ TreeMissingColors phi Ty)
    (z : Sum V E) (hpath : TwoColorPathComponent G phi alpha beta z)
    (sigma : PartialEdgeColoring E k)
    (hsigma : sigma = TwoColorComponentSwap G phi alpha beta z)
    (hcase :
      let H := C.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
      let A := HierarchyStarredStage H q
      let Tnq := H.stage ⟨H.dividerCount, by omega⟩
      let Tn := ett.series.data.tree n.castSucc
      let Dn := TashkinovStoredColors ett.series.data n
      (0 < H.dividerCount ∧ alpha ∈ TreeMissingColors phi Tnq) ∨
        (H.dividerCount = 0 ∧
          (alpha ∈ TreeMissingColors phi Tn ∨
            (alpha ∈ TreeMissingColors phi A ∧
              alpha ∉ Dn ∧ beta ∉ Dn))))
    (hdisjoint :
      let va := T.vertex (HierarchyFirstMissingPosition phi T alpha)
      Disjoint (TwoColorComponent G phi alpha beta z)
        (TwoColorComponent G phi alpha beta (Sum.inl va))) :
    let A := HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)
    ∀ t : Fin A.length, sigma (A.edge t) = phi (A.edge t) := by
-- BODY
  classical
  have controls := P2813_T1_BaseControl G k e0 input T phi ett base C ctx
    hprefixElementary alpha beta hne hmissingPrefix z hpath sigma hsigma hcase hdisjoint
  rcases controls with ⟨hbase, hmissing, hsproper, hsone, houtside⟩
  have coreFixed := P2813_T1_BaseDisplayedEdges G k e0 input T phi ett base
    sigma ctx.oneEdgeUncolored hsone hbase
  rcases ctx with ⟨hproper, hone, hlower, hfewer, hminimal, hlarge⟩
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let a := T.vertex (HierarchyFirstMissingPosition phi T alpha)
  let b := T.vertex (HierarchyFirstMissingPosition phi T beta)
  let Ty := TreeSequencePrefix T
    (min (A.length + ((T.length - A.length) - 1)) T.length)
    (by have hA := A.positive; have hT := T.positive; omega)
    (Nat.min_le_right _ _)
  have trans {U W Z : TreeSequence G e0}
      (hUW : TreeSequenceInitialSegment U W)
      (hWZ : TreeSequenceInitialSegment W Z) :
      TreeSequenceInitialSegment U Z := by
    clear * - hUW hWZ
    refine ⟨hUW.1.trans hWZ.1, ?_, ?_⟩
    · intro j
      exact (hWZ.2.1 (Fin.castLE (Nat.succ_le_succ hUW.1) j)).trans
        (hUW.2.1 j)
    · intro j
      exact (hWZ.2.2 (Fin.castLE hUW.1 j)).trans (hUW.2.2 j)
  have stageChain : ∀ (j : ℕ) (hj : j < H.dividerCount + 2)
      (i : Fin (H.dividerCount + 2)), i.val ≤ j →
      TreeSequenceInitialSegment (H.stage i) (H.stage ⟨j, hj⟩) := by
    clear * - H trans
    intro j
    induction j with
    | zero =>
        intro hj i hi
        have hi0 : i = 0 := Fin.ext (Nat.eq_zero_of_le_zero hi)
        subst i
        exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    | succ j ih =>
        intro hj i hi
        by_cases heq : i.val = j + 1
        · have heq' : i = ⟨j + 1, hj⟩ := Fin.ext heq
          subst i
          exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
        · exact trans (ih (by omega) i (by omega))
            (H.nested ⟨j, by omega⟩)
  have starStage (r : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage H r)
        (H.stage r.succ) := by
    clear * - H r
    refine Fin.cases ?_ (fun i => ?_) r
    · exact H.coreInsideFirst
    · exact H.nested i.succ
  have starChain (r s : Fin (H.dividerCount + 1)) (hrs : r ≤ s) :
      TreeSequenceInitialSegment (HierarchyStarredStage H r)
        (HierarchyStarredStage H s) := by
    clear * - H r s hrs stageChain starStage trans
    by_cases heq : r = s
    · subst s
      exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    · have hrlt : r.val < s.val := by
        have := Fin.le_iff_val_le_val.mp hrs
        have : r.val ≠ s.val := fun h => heq (Fin.ext h)
        omega
      have hs : s ≠ 0 := by intro hs; subst s; simp at hrlt
      have hstar : HierarchyStarredStage H s = H.stage s.castSucc := by
        rw [← Fin.succ_pred s hs]
        rfl
      rw [hstar]
      exact trans (starStage r)
        (stageChain s.val (by omega) r.succ (by simp; omega))
  have hAT : TreeSequenceInitialSegment A T := by
    have hh := starStage q
    have hlast : q.succ = Fin.last (H.dividerCount + 1) := Fin.ext rfl
    simpa [hlast, H.terminalStage] using hh
  have hATy : TreeSequenceInitialSegment A Ty := by
    clear * - hAT A Ty
    have hlen : A.length ≤ Ty.length := by
      change A.length ≤ min (A.length + ((T.length - A.length) - 1)) T.length
      exact Nat.le_min.mpr ⟨Nat.le_add_right _ _, hAT.1⟩
    refine ⟨hlen, ?_, ?_⟩
    · intro j
      change T.vertex _ = A.vertex j
      exact hAT.2.1 j
    · intro j
      change T.edge _ = A.edge j
      exact hAT.2.2 j
  have hTyT : TreeSequenceInitialSegment Ty T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have helemA : ColoredVertexSetElementary G phi (TreeSequenceVertexSet A) := by
    intro u hu v hv hne'
    exact hprefixElementary
      (TreeSequenceInitialSegmentVertexSetSubset hATy hu)
      (TreeSequenceInitialSegmentVertexSetSubset hATy hv) hne'
  have helemStar (r : Fin (H.dividerCount + 1)) :
      ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet (HierarchyStarredStage H r)) := by
    have hsub := TreeSequenceInitialSegmentVertexSetSubset
      (starChain r q (Fin.le_last r))
    intro u hu v hv hne'
    exact helemA (hsub hu) (hsub hv) hne'
  have missingSubset {B S : TreeSequence G e0} (hBS : TreeSequenceInitialSegment B S) :
      TreeMissingColors phi B ⊆ TreeMissingColors phi S := by
    intro c hc
    obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr ⟨v, TreeSequenceInitialSegmentVertexSetSubset hBS hv, hvm⟩
  have maxClosed (c : Fin k)
      (hex : ∃ r, TreeColorSetClosed G phi (HierarchyStarredStage H r) {c}) :
      ∃ r : Fin (H.dividerCount + 1),
        TreeColorSetClosed G phi (HierarchyStarredStage H r) {c} ∧
        ∀ s : Fin (H.dividerCount + 1), r.val < s.val →
          ¬ TreeColorSetClosed G phi (HierarchyStarredStage H s) {c} := by
    let S := Finset.univ.filter fun r : Fin (H.dividerCount + 1) =>
      TreeColorSetClosed G phi (HierarchyStarredStage H r) {c}
    have hS : S.Nonempty := by
      obtain ⟨r, hr⟩ := hex
      exact ⟨r, by simp [S, hr]⟩
    refine ⟨S.max' hS, (Finset.mem_filter.mp (Finset.max'_mem S hS)).2, ?_⟩
    intro s hs hcl
    have hmem : s ∈ S := by simp [S, hcl]
    have hle := Finset.le_max' S s hmem
    change s.val ≤ (S.max' hS).val at hle
    omega
  have missingAtMax (c : Fin k) (hcA : c ∈ TreeMissingColors phi A)
      (r : Fin (H.dividerCount + 1))
      (hmax : ∀ s : Fin (H.dividerCount + 1), r.val < s.val →
        ¬ TreeColorSetClosed G phi (HierarchyStarredStage H s) {c}) :
      c ∈ TreeMissingColors phi (HierarchyStarredStage H r) := by
    let P (j : ℕ) := ∃ hj : j ≤ H.dividerCount,
      c ∈ TreeMissingColors phi (HierarchyStarredStage H ⟨j, by omega⟩)
    have hex : ∃ j, P j := ⟨H.dividerCount, le_rfl, hcA⟩
    let s := Nat.find hex
    obtain ⟨hs, hsm⟩ : P s := Nat.find_spec hex
    by_cases hsr : s ≤ r.val
    · exact missingSubset (starChain ⟨s, by omega⟩ r hsr) hsm
    · have hspos : 0 < s := by omega
      let i : Fin H.dividerCount := ⟨s - 1, by omega⟩
      have his : i.succ = (⟨s, by omega⟩ : Fin (H.dividerCount + 1)) :=
        Fin.ext (by simp [i]; omega)
      have hprev : c ∉ TreeMissingColors phi (HierarchyStarredStage H i.castSucc) := by
        intro hm
        have hh : P (s - 1) := ⟨by omega, hm⟩
        have hmin := Nat.find_min' hex hh
        change s ≤ s - 1 at hmin
        omega
      have hsm' : c ∈ TreeMissingColors phi (H.stage i.succ.castSucc) := by
        simpa only [← his, HierarchyStarredStage, Fin.cases_succ] using hsm
      obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hsm'
      have hvnew : v ∉ TreeSequenceVertexSet (HierarchyStarredStage H i.castSucc) := by
        intro hh
        exact hprev (Finset.mem_biUnion.mpr ⟨v, hh, hvm⟩)
      have hnew := GoodHierarchyNewMissingClosed C.good i (helemStar i.succ) c
        (Finset.mem_biUnion.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hv, hvnew⟩, hvm⟩)
      apply False.elim
      apply hmax i.succ (by simp [i]; omega)
      intro d hd
      have heq : d = c := Finset.mem_singleton.mp hd
      subst d
      exact hnew
  have preStepElementary :
      let i : Fin ett.rounds := ⟨ett.rounds - 1, by have := C.positive; omega⟩
      ColoredVertexSetElementary G (ett.series.data.coloring i.castSucc)
        (TreeSequenceVertexSet Tn) := by
    dsimp only
    by_cases hn : ett.rounds = 1
    · have hcolor : (⟨ett.rounds - 1, by have := C.positive; omega⟩ : Fin ett.rounds).castSucc = 0 :=
        Fin.ext (by simp [hn])
      have htree : n.castSucc = (⟨1, by omega⟩ : Fin (ett.rounds + 2)) :=
        Fin.ext (by simp [n, hn])
      dsimp only [Tn]
      rw [hcolor, htree]
      exact (TechnicalTheoremBase G k ett.rounds e0 input ett.series).1
    · have hmore : 1 < ett.rounds := by have := C.positive; omega
      obtain ⟨predecessor, hr, hmaximum, _, _⟩ :=
        CertifiedETTPredecessor G k e0 input T phi ett C.maximum hmore
      have htree : n.castSucc = (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) :=
        Fin.ext rfl
      dsimp only [Tn]
      rw [htree]
      exact (hlower predecessor (by omega) (by omega) hmaximum).1

  have coreChain : TreeSequenceInitialSegment Tn base.core := by
    by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
    · exact (base.parallel hp).2.2.some.leftSegment
    · rw [base.nonparallel hp]
      exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  have coreA : TreeSequenceInitialSegment base.core A := starChain 0 q (Fin.zero_le _)
  have TnA := trans coreChain coreA
  have hnStable : StableColoring Tn
      (TashkinovStoredColors ett.series.data n) phi sigma := by
    change (if ett.series.data.kind n = some TashkinovExtensionKind.PE then
      CombinedStableColoring Tn base.closure (TashkinovStoredColors ett.series.data n) phi sigma
      else StableColoring Tn (TashkinovStoredColors ett.series.data n) phi sigma) at hbase
    by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
    · exact (if_pos hp ▸ hbase).1
    · simpa only [hp, if_false] using hbase
  have fixedValue (f : E) (ha : phi f ≠ some alpha) (hb : phi f ≠ some beta) :
      sigma f = phi f := by
    rw [hsigma]
    simp only [TwoColorComponentSwap]
    split_ifs <;> simp_all
  have hqPositive (t : Fin A.length) (ht : base.core.length ≤ t.val) :
      0 < H.dividerCount := by
    by_contra hn
    have hz : q = 0 := Fin.ext (by dsimp [q]; omega)
    have he : A = base.core := by dsimp only [A]; rw [hz]; rfl
    have hlt := t.isLt
    have hlen := congrArg TreeSequence.length he
    omega
  have missingEdge (t : Fin A.length) (ht : base.core.length ≤ t.val)
      (c : Fin k) (hc : c = alpha ∨ c = beta)
      (hm : c ∈ TreeMissingColors phi A) (hcol : phi (A.edge t) = some c) :
      sigma (A.edge t) = phi (A.edge t) := by
    have hp := hqPositive t ht
    by_cases hex : ∃ r, TreeColorSetClosed G phi (HierarchyStarredStage H r) {c}
    · obtain ⟨r, hcl, hmax⟩ := maxClosed c hex
      have hmr := missingAtMax c hm r hmax
      have havoid := (rutcor G k e0 input T phi ett base H C.good hp
        hprefixElementary preStepElementary c hm).1 hex r hcl hmax
      by_cases htr : t.val < (HierarchyStarredStage H r).length
      · let u : Fin (HierarchyStarredStage H r).length := ⟨t.val, htr⟩
        have hseg := starChain r q (Fin.le_last r)
        have he : Fin.castLE hseg.1 u = t := Fin.ext rfl
        rw [← he, hseg.2.2 u]
        have hh := OutsideKempeRecoloringStable G e0 (HierarchyStarredStage H r)
          ∅ phi sigma alpha beta hproper hone (houtside r c hc hmr hcl)
        apply hh.2.2.2.2
        obtain ⟨i, hi⟩ := (HierarchyStarredStage H r).attaches u
        refine ⟨(HierarchyStarredStage H r).vertex u.succ, ?_, ?_⟩
        · simp only [TreeSequenceVertexSet, Finset.mem_image,
            Finset.mem_univ, true_and]
          exact ⟨u.succ, rfl⟩
        · simp [Incident, hi]
      · exact False.elim (havoid (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, t, by omega, hcol⟩))
    · have hnone : ∀ r, ¬ TreeColorSetClosed G phi (HierarchyStarredStage H r) {c} :=
        fun r hr => hex ⟨r, hr⟩
      have havoid := (rutcor G k e0 input T phi ett base H C.good hp
        hprefixElementary preStepElementary c hm).2 hnone
      exact False.elim (havoid.2.2.2 (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, t, le_trans coreChain.1 ht, hcol⟩))
  have route := P2813_T1_TerminalRoute G k e0 input T phi ett
  have augmentationMissing (S : TreeSequence G e0)
      (hseq : TashkinovAugmentationSequence phi S T)
      (t : Fin A.length) (ht : S.length ≤ t.val)
      (c : Fin k) (hcol : phi (A.edge t) = some c) :
      c ∈ TreeMissingColors phi A := by
    let tT := Fin.castLE hAT.1 t
    obtain ⟨hlen, hinit, d, hcolor, hdm⟩ :=
      (TashkinovAugmentationSequencePosition phi S T hseq tT ht).1
    have hdcol : phi (T.edge tT) = some d := by
      convert hcolor using 1
      congr 2
    have hdc : d = c := Option.some.inj
      (hdcol.symm.trans (by rw [hAT.2.2 t]; exact hcol))
    subst d
    obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hdm
    obtain ⟨i, hi⟩ : ∃ i, (TreeSequencePrefix T tT.val
        (le_trans S.positive ht) (Nat.le_of_lt tT.isLt)).vertex i = v := by
      simpa [TreeSequenceVertexSet] using hv
    let iA : Fin (A.length + 1) := ⟨i.val, by
      have hiBound : i.val < t.val + 1 := i.isLt
      have := t.isLt
      omega⟩
    have hvA : A.vertex iA = v := by
      have hh := hAT.2.1 iA
      exact hh.symm.trans hi
    exact Finset.mem_biUnion.mpr ⟨v, by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨iA, hvA⟩, hvm⟩
  change ∀ t : Fin A.length, sigma (A.edge t) = phi (A.edge t)
  intro t
  by_cases ht : t.val < base.core.length
  · let u : Fin base.core.length := ⟨t.val, ht⟩
    have he : Fin.castLE coreA.1 u = t := Fin.ext rfl
    rw [← he, coreA.2.2 u]
    exact coreFixed u
  · have htCore : base.core.length ≤ t.val := by omega
    by_cases ha : phi (A.edge t) = some alpha
    · by_cases hm : alpha ∈ TreeMissingColors phi A
      · exact missingEdge t htCore alpha (Or.inl rfl) hm ha
      · rcases route with ⟨hp, hseq⟩ | ⟨hp, f, seed, hedges, hseed, hincident, hcontrol, hseq⟩
        · exact (hm (augmentationMissing Tn hseq t (le_trans coreChain.1 htCore) alpha ha)).elim
        · by_cases hs : seed.length ≤ t.val
          · exact (hm (augmentationMissing seed hseq t hs alpha ha)).elim
          · have hseedT := TashkinovAugmentationSequenceInitialSegment phi seed T hseq
            have htSeed : t.val = Tn.length := by
              have hseedLen : seed.length = Tn.length + 1 := hseed.1
              have hcoreLen : Tn.length ≤ base.core.length := coreChain.1
              omega
            let u : Fin seed.length := ⟨t.val, by omega⟩
            have he : Fin.castLE hseedT.1 u = Fin.castLE hAT.1 t := Fin.ext rfl
            have hf : A.edge t = f := by
              rw [← hAT.2.2 t, ← he, hseedT.2.2 u]
              have hu : u = Fin.cast hseed.1.symm (Fin.last Tn.length) := Fin.ext htSeed
              rw [hu, hseed.2.2]
            rw [hf]
            exact hnStable.1 f hincident hcontrol
    · by_cases hb : phi (A.edge t) = some beta
      · by_cases hm : beta ∈ TreeMissingColors phi A
        · exact missingEdge t htCore beta (Or.inr rfl) hm hb
        · rcases route with ⟨hp, hseq⟩ | ⟨hp, f, seed, hedges, hseed, hincident, hcontrol, hseq⟩
          · exact (hm (augmentationMissing Tn hseq t (le_trans coreChain.1 htCore) beta hb)).elim
          · by_cases hs : seed.length ≤ t.val
            · exact (hm (augmentationMissing seed hseq t hs beta hb)).elim
            · have hseedT := TashkinovAugmentationSequenceInitialSegment phi seed T hseq
              have htSeed : t.val = Tn.length := by
                have hseedLen : seed.length = Tn.length + 1 := hseed.1
                have hcoreLen : Tn.length ≤ base.core.length := coreChain.1
                omega
              let u : Fin seed.length := ⟨t.val, by omega⟩
              have he : Fin.castLE hseedT.1 u = Fin.castLE hAT.1 t := Fin.ext rfl
              have hf : A.edge t = f := by
                rw [← hAT.2.2 t, ← he, hseedT.2.2 u]
                have hu : u = Fin.cast hseed.1.symm (Fin.last Tn.length) := Fin.ext htSeed
                rw [hu, hseed.2.2]
              rw [hf]
              exact hnStable.1 f hincident hcontrol
      · exact fixedValue _ ha hb
