import Tablet.GoodHierarchy
import Tablet.GoodHierarchyReservedDisjoint
import Tablet.HierarchyBase
import Tablet.HierarchyCounterexample
import Tablet.HierarchyCounterexamplePenultimateElementary
import Tablet.HierarchyFullTailLength
import Tablet.HierarchyFullTailPrefix
import Tablet.HierarchyMinimumCounterexampleContext
import Tablet.HierarchyReplacementPresentation
import Tablet.HierarchyStageMissingColors
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsAt
import Tablet.NineN
import Tablet.SameGoodHierarchy
import Tablet.SameHierarchyStages
import Tablet.TashkinovHierarchy
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequencePrefix

-- [TABLET NODE: HierarchySituationThreeColorChoice]
theorem HierarchySituationThreeColorChoice
    {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext
      G k e0 input T phi ett base C)
    (P : HierarchyReplacementPresentation
      G k e0 input T phi ett base C ctx)
    (alpha : Fin k)
    (hpathLower : 2 <= HierarchyPathNumber C.hierarchy)
    (hpathUpper :
      HierarchyPathNumber C.hierarchy < HierarchyFullTailLength C)
    (halpha :
      let H := P.counterexample.hierarchy
      let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
      let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
        Fin.last P.corresponding.replacementETT.rounds
      let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
      let j := HierarchyPathNumber C.hierarchy
      let B := HierarchyFullTailPrefix C (j - 2)
      let D := HierarchyStoredColorsAt H q
      let Gamma := D.biUnion (P.counterexample.good.gamma q)
      let baseExtraMissing :=
        ((TreeSequenceVertexSet P.replacementBase.core \
            TreeSequenceVertexSet Tn).biUnion
          fun v => MissingColors G P.coloring v)
      alpha ∈ MissingColors G P.coloring
          (T.vertex (Fin.last T.length)) /\
        alpha ∈ TreeMissingColors P.coloring B /\
        (alpha ∉ Gamma ∪ baseExtraMissing ∨
          exists eta : Fin k, eta ∈ D /\
            alpha ∈ P.counterexample.good.gamma q eta /\
            (HierarchyFirstMissingPosition P.coloring T eta).val <=
              B.length)) :
    let H := P.counterexample.hierarchy
    let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
    let j := HierarchyPathNumber C.hierarchy
    let A := HierarchyStarredStage H q
    let B := HierarchyFullTailPrefix C (j - 2)
    let D := HierarchyStoredColorsAt H q
    let Gamma := D.biUnion (P.counterexample.good.gamma q)
    let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
      Fin.last P.corresponding.replacementETT.rounds
    let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
    let baseExtraMissing :=
      ((TreeSequenceVertexSet P.replacementBase.core \
          TreeSequenceVertexSet Tn).biUnion
        fun v => MissingColors G P.coloring v)
    let tailUsedThroughJ :=
      (Finset.univ : Finset (Fin k)).filter fun c =>
        exists r : Fin T.length,
          A.length <= r.val /\ r.val < A.length + j /\
            P.coloring (T.edge r) = some c
    exists beta : Fin k,
      beta ≠ alpha /\
        beta ∈ TreeMissingColors P.coloring B /\
        beta ∉ Gamma /\ beta ∉ tailUsedThroughJ /\
        (beta ∉ baseExtraMissing ∪ D ∨
          beta ∈ D /\
            Disjoint (P.counterexample.good.gamma q beta ∪ {beta})
              tailUsedThroughJ) := by
-- BODY
  classical
  clear halpha
  let H := P.counterexample.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let j := HierarchyPathNumber C.hierarchy
  change 2 <= j at hpathLower
  let i := j - 2
  let B := HierarchyFullTailPrefix C i
  let D := HierarchyStoredColorsAt H q
  let Gamma := D.biUnion (P.counterexample.good.gamma q)
  let n : Fin (P.corresponding.replacementETT.rounds + 1) :=
    Fin.last P.corresponding.replacementETT.rounds
  let Tn := P.corresponding.replacementETT.series.data.tree n.castSucc
  let M := (TreeSequenceVertexSet P.replacementBase.core \
    TreeSequenceVertexSet Tn).biUnion fun v => MissingColors G P.coloring v
  let U := fun s : Nat => (Finset.univ : Finset (Fin k)).filter fun c =>
    exists r : Fin T.length,
      A.length <= r.val /\ r.val < A.length + s /\
        P.coloring (T.edge r) = some c
  change exists beta : Fin k,
    beta ≠ alpha /\ beta ∈ TreeMissingColors P.coloring B /\
      beta ∉ Gamma /\ beta ∉ U j /\
      (beta ∉ M ∪ D ∨ beta ∈ D /\
        Disjoint (P.counterexample.good.gamma q beta ∪ {beta}) (U j))
  have hpen : ColoredVertexSetElementary G P.coloring
      (TreeSequenceVertexSet (HierarchyFullTailPrefix P.counterexample
        (HierarchyFullTailLength P.counterexample - 1))) := by
    exact HierarchyCounterexamplePenultimateElementary
      G k e0 P.corresponding.replacementInput T P.coloring
      P.corresponding.replacementETT P.replacementBase P.counterexample
      P.minimumContext.proper P.minimumContext.oneEdgeUncolored
      P.minimumContext.lowerRung P.minimumContext.fewerDividers
      P.minimumContext.lexicographicMinimality P.minimumContext.largeMissingSet
  have hsame := P.sameGood
  unfold SameGoodHierarchy SameHierarchyStages at hsame
  obtain ⟨⟨hcore, hcount, hstage, -⟩, -⟩ := hsame
  have transport (m m' : Nat)
      (s : Fin (m + 2) → TreeSequence G e0)
      (s' : Fin (m' + 2) → TreeSequence G e0)
      (b b' : TreeSequence G e0)
      (hc : m = m') (hb : b = b') (hs : HEq s s') :
      Fin.cases (motive := fun _ => TreeSequence G e0)
          b (fun r : Fin m => s r.succ.castSucc) (Fin.last m) =
        Fin.cases (motive := fun _ => TreeSequence G e0)
          b' (fun r : Fin m' => s' r.succ.castSucc) (Fin.last m') := by
    subst m'
    have hs' : s = s' := eq_of_heq hs
    rw [← hs', ← hb]
  have hstar : HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount) = A := by
    exact transport _ _ _ _ _ _ hcount hcore hstage
  have hell : HierarchyFullTailLength C = T.length - A.length := by
    change T.length - (HierarchyStarredStage C.hierarchy
      (Fin.last C.hierarchy.dividerCount)).length = T.length - A.length
    rw [hstar]
  let Ty := fun s : Nat =>
    TreeSequencePrefix T (min (A.length + s) T.length)
      (by have hA := A.positive; have hT := T.positive; omega)
      (Nat.min_le_right _ _)
  have hB : B = Ty i := by
    dsimp [B, HierarchyFullTailPrefix, Ty]
    simp only [hstar]
  have hi : i < T.length - A.length := by
    rw [hell] at hpathUpper
    dsimp only [i]
    omega
  have hji : j = i + 2 := by
    dsimp only [i]
    omega
  have hj : j < T.length - A.length := by
    change j < HierarchyFullTailLength C at hpathUpper
    rwa [hell] at hpathUpper
  let X := (TreeMissingColors P.coloring B \ M) \ U i
  have hnine : (X \ (Gamma ∪ D)).card <= 4 →
      exists eta : Fin 7 → Fin k, Function.Injective eta ∧
        ∀ h : Fin 7, eta h ∈ D ∧ eta h ∈ TreeMissingColors P.coloring B ∧
          Disjoint (P.counterexample.good.gamma q (eta h) ∪ {eta h}) (U i) := by
    dsimp only [X]
    rw [hB]
    exact (NineN G k e0 P.corresponding.replacementInput T P.coloring
      P.corresponding.replacementETT P.counterexample.positive
      P.replacementBase H P.counterexample.good hpen
      P.minimumContext.largeMissingSet i hi).2
  clear hpen transport hcore hcount hstage hstar hB hell hi hpathUpper hpathLower
  let R := U j \ U i
  have hRcard : R.card <= 2 := by
    let r0 : Fin T.length := ⟨A.length + i, by omega⟩
    let r1 : Fin T.length := ⟨A.length + i + 1, by omega⟩
    have hsub : R.image some ⊆
        ({r0, r1} : Finset (Fin T.length)).image
          (fun r => P.coloring (T.edge r)) := by
      intro oc hoc
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hoc
      obtain ⟨hcj, hci⟩ := Finset.mem_sdiff.mp hc
      obtain ⟨r, hrA, hrj, hrc⟩ := (Finset.mem_filter.mp hcj).2
      have hri : A.length + i <= r.val := by
        by_contra hlt
        apply hci
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, r, hrA, by omega, hrc⟩
      have hr : r = r0 ∨ r = r1 := by
        have hv : r.val = A.length + i ∨ r.val = A.length + i + 1 := by omega
        rcases hv with hv | hv
        · left; apply Fin.ext; exact hv
        · right; apply Fin.ext; exact hv
      apply Finset.mem_image.mpr
      refine ⟨r, ?_, hrc⟩
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hr
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective R
      (by intro a b hab; exact Option.some.inj hab)] at hcard
    have hpair : ({r0, r1} : Finset (Fin T.length)).card <= 2 := by
      exact (Finset.card_insert_le _ _).trans (by simp)
    exact hcard.trans (Finset.card_image_le.trans hpair)
  have chooseColor (S M D Gamma : Finset (Fin k))
      (gamma : Fin k → Finset (Fin k)) (Ui Uj : Finset (Fin k))
      (hRcard : (Uj \ Ui).card <= 2) (hGD : Disjoint Gamma D)
      (hgamma : ∀ eta ∈ D, gamma eta ⊆ Gamma)
      (hpairs : ∀ eta theta, eta ∈ D → theta ∈ D → eta ≠ theta →
        Disjoint (gamma eta) (gamma theta))
      (hnine : ((((S \ M) \ Ui) \ (Gamma ∪ D)).card <= 4 →
        exists eta : Fin 7 → Fin k, Function.Injective eta ∧
          ∀ h : Fin 7, eta h ∈ D ∧ eta h ∈ S ∧
            Disjoint (gamma (eta h) ∪ {eta h}) Ui)) :
      exists beta : Fin k, beta ≠ alpha ∧ beta ∈ S ∧
        beta ∉ Gamma ∧ beta ∉ Uj ∧
        (beta ∉ M ∪ D ∨ beta ∈ D ∧ Disjoint (gamma beta ∪ {beta}) Uj) := by
    let R := Uj \ Ui
    let X := (S \ M) \ Ui
    change R.card <= 2 at hRcard
    let F := R ∪ {alpha}
    have hFcard : F.card <= 3 := by
      have hc := Finset.card_union_le R {alpha}
      simp only [Finset.card_singleton] at hc
      dsimp [F]
      omega
    have notUsed {c : Fin k} (hci : c ∉ Ui) (hcR : c ∉ R) : c ∉ Uj := by
      intro hcj
      exact hcR (Finset.mem_sdiff.mpr ⟨hcj, hci⟩)
    by_cases hsmall : (X \ (Gamma ∪ D)).card <= 4
    · obtain ⟨eta, hinj, heta⟩ := hnine hsmall
      let Q := fun h : Fin 7 => gamma (eta h) ∪ {eta h}
      have hQdisjoint : ∀ a b : Fin 7, a ≠ b → Disjoint (Q a) (Q b) := by
        intro a b hab
        have hne : eta a ≠ eta b := fun he => hab (hinj he)
        have hp := hpairs (eta a) (eta b)
          (heta a).1 (heta b).1 hne
        rw [Finset.disjoint_left]
        intro c hca hcb
        rcases Finset.mem_union.mp hca with hca | hca <;>
          rcases Finset.mem_union.mp hcb with hcb | hcb
        · exact Finset.disjoint_left.mp hp hca hcb
        · exact Finset.disjoint_left.mp hGD (hgamma (eta a) (heta a).1 hca)
            (by simpa only [Finset.mem_singleton.mp hcb] using (heta b).1)
        · exact Finset.disjoint_left.mp hGD (hgamma (eta b) (heta b).1 hcb)
            (by simpa only [Finset.mem_singleton.mp hca] using (heta a).1)
        · exact hne ((Finset.mem_singleton.mp hca).symm.trans
            (Finset.mem_singleton.mp hcb))
      let bad := (Finset.univ : Finset (Fin 7)).filter fun h =>
        exists c : Fin k, c ∈ Q h ∧ c ∈ F
      have badWitness (h : bad) : exists c : Fin k, c ∈ Q h.val ∧ c ∈ F :=
        (Finset.mem_filter.mp h.property).2
      let f : bad → F := fun h =>
        ⟨Classical.choose (badWitness h), (Classical.choose_spec (badWitness h)).2⟩
      have hf (h : bad) : (f h).val ∈ Q h.val :=
        (Classical.choose_spec (badWitness h)).1
      have hfinj : Function.Injective f := by
        intro a b hab
        apply Subtype.ext
        by_contra hne
        have hfb := hf b
        rw [← congrArg Subtype.val hab] at hfb
        exact Finset.disjoint_left.mp (hQdisjoint a.val b.val hne) (hf a) hfb
      have hbadcard : bad.card <= 3 :=
        (Finset.card_le_card_of_injective hfinj).trans hFcard
      have hnot : ¬ (Finset.univ : Finset (Fin 7)) ⊆ bad := by
        intro hs
        have hc := Finset.card_le_card hs
        simp only [Finset.card_univ, Fintype.card_fin] at hc
        omega
      obtain ⟨h, _, hh⟩ := Finset.not_subset.mp hnot
      have hQF : Disjoint (Q h) F := by
        rw [Finset.disjoint_left]
        intro c hc hF
        apply hh
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, c, hc, hF⟩
      have hself : eta h ∈ Q h := Finset.mem_union_right _ (Finset.mem_singleton_self _)
      have halpha' : eta h ≠ alpha := by
        intro he
        apply Finset.disjoint_left.mp hQF hself
        exact Finset.mem_union_right _ (Finset.mem_singleton.mpr he)
      have hQU : Disjoint (Q h) (Uj) := by
        rw [Finset.disjoint_left]
        intro c hc hcj
        have hci : c ∉ Ui := fun hu => Finset.disjoint_left.mp (heta h).2.2 hc hu
        have hcR : c ∉ R := fun hr =>
          Finset.disjoint_left.mp hQF hc (Finset.mem_union_left _ hr)
        exact notUsed hci hcR hcj
      refine ⟨eta h, halpha', (heta h).2.1, ?_, ?_, Or.inr ⟨(heta h).1, hQU⟩⟩
      · intro hc
        exact Finset.disjoint_left.mp hGD hc (heta h).1
      · intro hc
        exact Finset.disjoint_left.mp hQU hself hc
    · have hnot : ¬ X \ (Gamma ∪ D) ⊆ F := by
        intro hs
        have hc := Finset.card_le_card hs
        omega
      obtain ⟨beta, hb, hF⟩ := Finset.not_subset.mp hnot
      obtain ⟨hx, hGD⟩ := Finset.mem_sdiff.mp hb
      obtain ⟨hBM, hUi⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨hBmissing, hM⟩ := Finset.mem_sdiff.mp hBM
      have hGamma : beta ∉ Gamma := fun hc => hGD (Finset.mem_union_left _ hc)
      have hD : beta ∉ D := fun hc => hGD (Finset.mem_union_right _ hc)
      have hR : beta ∉ R := fun hc => hF (Finset.mem_union_left _ hc)
      have hne : beta ≠ alpha := by
        intro he
        exact hF (Finset.mem_union_right _ (Finset.mem_singleton.mpr he))
      refine ⟨beta, hne, hBmissing, hGamma, notUsed hUi hR, Or.inl ?_⟩
      intro hc
      rcases Finset.mem_union.mp hc with hc | hc
      · exact hM hc
      · exact hD hc
  exact chooseColor (TreeMissingColors P.coloring B) M D Gamma
    (P.counterexample.good.gamma q) (U i) (U j) hRcard
    (GoodHierarchyReservedDisjoint P.counterexample.good q).2
    (by
      intro eta heta c hc
      exact Finset.mem_biUnion.mpr ⟨eta, heta, hc⟩)
    (fun eta theta he ht hne =>
      P.counterexample.good.disjointPairs q eta theta he ht hne) hnine
