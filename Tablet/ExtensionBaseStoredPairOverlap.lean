import Tablet.DefectiveVertex
import Tablet.ETTFirstAppearanceIndex
import Tablet.ExtensionBaseActiveIndices
import Tablet.ExtensionBaseDeltaExclusion
import Tablet.ExtensionBaseSameSupportStoredPairOverlap
import Tablet.ExtensionBaseSupportClass
import Tablet.ExtensionBaseSupportClassEnumeration
import Tablet.ExtensionBaseSupportClassColors
import Tablet.ExtensionBaseSupportOrder
import Tablet.ExtensionRules
import Tablet.MaximumDefectiveChoice
import Tablet.MaximumProperty
import Tablet.ModColoring
import Tablet.TashkinovSeries
import Tablet.TashkinovSeriesStep
import Tablet.TreeInterchangeable
import Tablet.TreeSequenceInitialSegment
import Tablet.TreeSequenceVertexSet

-- [TABLET NODE: ExtensionBaseStoredPairOverlap]
theorem ExtensionBaseStoredPairOverlap {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (q : Fin ett.rounds) (hqTerminal : q.val + 1 = ett.rounds)
    (hqKind : ett.series.data.kind q.succ =
      some TashkinovExtensionKind.PE)
    (hqVertex : ett.series.data.chosenVertex q.succ = some terminalSupport)
    (jSlot : Fin ett.rounds)
    (hjSlot : jSlot.val + 1 =
      ETTFirstAppearanceIndex ett terminalSupport hterminalSupport)
    (hMP : MaximumProperty ett)
    (hpositive : 0 < ett.rounds)
    (hLowerElementary : ∀ r : Fin ett.rounds, r.val < q.val →
      ColoredVertexSetElementary G (ett.series.data.coloring r.castSucc)
        (TreeSequenceVertexSet
          (ett.series.data.tree r.succ.castSucc)))
    (hLowerPartV : ∀ (r a : Fin ett.rounds), a.val < r.val →
      ∀ sigma : PartialEdgeColoring E k,
        IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
        StableColoring (ett.series.data.tree r.succ.castSucc)
          (TashkinovStoredColors ett.series.data r.castSucc)
          (ett.series.data.coloring r.castSucc) sigma →
        ∀ delta : Fin k,
          DefectiveColor G sigma
            (TreeSequenceVertexSet
              (ett.series.data.tree r.succ.castSucc)) delta →
          ∀ v : V,
            BoundaryColorVertex G sigma
              (TreeSequenceVertexSet
                (ett.series.data.tree r.succ.castSucc)) delta v →
            (∃ w : V, BoundaryColorVertex G sigma
                (TreeSequenceVertexSet
                  (ett.series.data.tree r.succ.castSucc)) delta w ∧
              TreeVertexOrder (ett.series.data.tree r.succ.castSucc) w v) →
            ∀ hvFinal : v ∈ TreeSequenceVertexSet T,
              ETTFirstAppearanceIndex ett v hvFinal ≤ a.val + 1 →
              ∀ va : V,
                (ett.series.data.kind a.succ =
                    some TashkinovExtensionKind.PE ∨
                  ett.series.data.kind a.succ =
                    some TashkinovExtensionKind.SE) →
                ett.series.data.chosenVertex a.succ = some va →
                v = va ∨
                  TreeVertexOrder
                    (ett.series.data.tree r.succ.castSucc) v va)
    (hlower : ∀ {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input T' generating'),
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
           ModColoring lower sigma)) :
    ∀ (s t : Fin ett.rounds) (vs vt : V)
      (hvsFinal : vs ∈ TreeSequenceVertexSet T)
      (hvtFinal : vt ∈ TreeSequenceVertexSet T)
      (gammaS deltaS gammaT deltaT : Fin k),
      s ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      t ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      s.val < t.val →
      ett.series.data.chosenVertex s.succ = some vs →
      ett.series.data.chosenVertex t.succ = some vt →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      ett.series.data.gamma t.succ = some gammaT →
      ett.series.data.delta t.succ = some deltaT →
      ((ett.series.data.stored s.succ ∩
          ett.series.data.stored t.succ).Nonempty ↔
        vs = vt ∧
          ¬ ∃ r : Fin ett.rounds,
            r ∈ ExtensionBaseActiveIndices ett terminalSupport
              hterminalSupport ∧
            s.val < r.val ∧ r.val < t.val ∧
            ett.series.data.chosenVertex r.succ = some vs) ∧
      ((ett.series.data.stored s.succ ∩
          ett.series.data.stored t.succ).Nonempty →
        ett.series.data.stored s.succ ∩
            ett.series.data.stored t.succ = {gammaT} ∧
          ett.series.data.stored s.succ ∩
            ett.series.data.stored t.succ = {deltaS}) := by
-- BODY
  classical
  have supportOrder := ExtensionBaseSupportOrder ett terminalSupport
    hterminalSupport q hqTerminal hqKind hqVertex hLowerPartV
  have deltaExclusion := (ExtensionBaseDeltaExclusion ett terminalSupport
    hterminalSupport q hqTerminal hqKind hqVertex jSlot hjSlot
    hLowerElementary hLowerPartV).1
  have differentSupport := (ExtensionRules G k e0 input T generating ett
    hMP hpositive hlower).2
  intro s t vs vt hvsFinal hvtFinal gammaS deltaS gammaT deltaT
    hsActive htActive hst hsVertex htVertex hsGamma hsDelta htGamma htDelta
  have hsKind : ett.series.data.kind s.succ =
      some TashkinovExtensionKind.PE := by
    have hsData := hsActive
    simp [ExtensionBaseActiveIndices] at hsData
    exact hsData.2.1
  have htKind : ett.series.data.kind t.succ =
      some TashkinovExtensionKind.PE := by
    have htData := htActive
    simp [ExtensionBaseActiveIndices] at htData
    exact htData.2.1
  have sameSupport : vs = vt →
      (((ett.series.data.stored s.succ ∩
          ett.series.data.stored t.succ).Nonempty ↔
        ¬ ∃ r : Fin ett.rounds,
          r ∈ ExtensionBaseActiveIndices ett terminalSupport
            hterminalSupport ∧
          s.val < r.val ∧ r.val < t.val ∧
          ett.series.data.chosenVertex r.succ = some vs) ∧
      ((ett.series.data.stored s.succ ∩
          ett.series.data.stored t.succ).Nonempty →
        ett.series.data.stored s.succ ∩
            ett.series.data.stored t.succ = {gammaT} ∧
          ett.series.data.stored s.succ ∩
            ett.series.data.stored t.succ = {deltaS})) := by
    intro hvst
    subst vt
    have hsClass : s ∈ ExtensionBaseSupportClass ett terminalSupport
        hterminalSupport vs := by
      simp [ExtensionBaseSupportClass, hsActive, hsVertex]
    have htClass : t ∈ ExtensionBaseSupportClass ett terminalSupport
        hterminalSupport vs := by
      simp [ExtensionBaseSupportClass, htActive, htVertex]
    have hclassNonempty :
        (ExtensionBaseSupportClass ett terminalSupport
          hterminalSupport vs).Nonempty := ⟨s, hsClass⟩
    have hcommon : ∀ (r : Fin ett.rounds) (v : V)
        (hvFinal : v ∈ TreeSequenceVertexSet T),
        r ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
        ett.series.data.chosenVertex r.succ = some v →
        ETTFirstAppearanceIndex ett v hvFinal =
          ETTFirstAppearanceIndex ett terminalSupport hterminalSupport := by
      intro r v hvFinal hrActive hrVertex
      exact (supportOrder.2.1 r v hvFinal hrActive hrVertex).1
    obtain ⟨p, indices, hwCurrent, hincreasing, hclass, henumerates⟩ :=
      ExtensionBaseSupportClassEnumeration ett terminalSupport
        hterminalSupport q hqTerminal vs hcommon hclassNonempty
    have hdeltaIndexed : ∀ (a b : Fin (p + 1))
        (gammaA deltaB : Fin k), a.val ≤ b.val →
        ett.series.data.gamma (indices a).succ = some gammaA →
        ett.series.data.delta (indices b).succ = some deltaB →
        deltaB ≠ gammaA := by
      intro a b gammaA deltaB hab haGamma hbDelta
      have haClass := (hclass (indices a)).2 ⟨a, rfl⟩
      have hbClass := (hclass (indices b)).2 ⟨b, rfl⟩
      simp only [ExtensionBaseSupportClass, Finset.mem_filter] at haClass hbClass
      have habIndices : (indices a).val ≤ (indices b).val := by
        rcases lt_or_eq_of_le hab with hablt | habeq
        · exact (hincreasing a b hablt).le
        · have habFin : a = b := Fin.ext habeq
          subst b
          exact le_rfl
      exact (deltaExclusion (indices a) (indices b) vs vs hvsFinal
        hvsFinal deltaB gammaA haClass.1 hbClass.1 habIndices
        haClass.2 hbClass.2 hbDelta haGamma).2
    have hsame := ExtensionBaseSameSupportStoredPairOverlap ett
      terminalSupport hterminalSupport q hqTerminal vs hwCurrent p indices
      hincreasing hclass henumerates hdeltaIndexed s t hsClass htClass hst
      gammaS deltaS gammaT deltaT hsGamma hsDelta htGamma htDelta
    have hbetween :
        (∃ r : Fin ett.rounds,
          r ∈ ExtensionBaseSupportClass ett terminalSupport
            hterminalSupport vs ∧
          s.val < r.val ∧ r.val < t.val) ↔
        ∃ r : Fin ett.rounds,
          r ∈ ExtensionBaseActiveIndices ett terminalSupport
            hterminalSupport ∧
          s.val < r.val ∧ r.val < t.val ∧
          ett.series.data.chosenVertex r.succ = some vs := by
      constructor
      · rintro ⟨r, hrClass, hsr, hrt⟩
        simp only [ExtensionBaseSupportClass, Finset.mem_filter] at hrClass
        exact ⟨r, hrClass.1, hsr, hrt, hrClass.2⟩
      · rintro ⟨r, hrActive, hsr, hrt, hrVertex⟩
        refine ⟨r, ?_, hsr, hrt⟩
        simp [ExtensionBaseSupportClass, hrActive, hrVertex]
    constructor
    · constructor
      · intro hoverlap hbetweenActive
        exact (hsame.1.mp hoverlap) (hbetween.mpr hbetweenActive)
      · intro hnoClass
        apply hsame.1.mpr
        intro hbetweenClass
        exact hnoClass (hbetween.mp hbetweenClass)
    · exact hsame.2
  have hoverlapIff :
      ((ett.series.data.stored s.succ ∩
          ett.series.data.stored t.succ).Nonempty ↔
        vs = vt ∧
          ¬ ∃ r : Fin ett.rounds,
            r ∈ ExtensionBaseActiveIndices ett terminalSupport
              hterminalSupport ∧
            s.val < r.val ∧ r.val < t.val ∧
            ett.series.data.chosenVertex r.succ = some vs) := by
    constructor
    · intro hoverlap
      by_cases hvst : vs = vt
      · exact ⟨hvst, (sameSupport hvst).1.mp hoverlap⟩
      · have hstNe : s ≠ t := by
          intro heq
          subst t
          omega
        have hsFirst :=
          (supportOrder.2.1 s vs hvsFinal hsActive hsVertex).1
        have htFirst :=
          (supportOrder.2.1 t vt hvtFinal htActive htVertex).1
        have hdisjoint := differentSupport s t vs vt hstNe hvst hsKind
          htKind hsVertex htVertex hvsFinal hvtFinal
          (hsFirst.trans htFirst.symm)
        obtain ⟨c, hc⟩ := hoverlap
        have hcPairs := Finset.mem_inter.mp hc
        exact (Finset.disjoint_left.mp hdisjoint hcPairs.1 hcPairs.2).elim
    · rintro ⟨hvst, hnoBetween⟩
      exact (sameSupport hvst).1.mpr hnoBetween
  refine ⟨hoverlapIff, ?_⟩
  intro hoverlap
  have hvst := (hoverlapIff.mp hoverlap).1
  exact (sameSupport hvst).2 hoverlap
