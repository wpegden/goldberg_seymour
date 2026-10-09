import Tablet.BoundaryColorVertex
import Tablet.DefectiveColor
import Tablet.ETTFirstAppearanceIndex
import Tablet.GoodHierarchyRestrictedAugmentation
import Tablet.StableColoringBeforeVertex
import Tablet.TreeInterchangeable
import Tablet.TreeVertexOrder
import Tablet.P2716_T2_ElementaryEndpointExclusion
import Tablet.P2716_T2_FirstEntryClipping
import Tablet.TreeSequenceInitialSegmentVertexSetSubset

-- [TABLET NODE: Step1CaseTwoOutsideRestrictedAugmentation]
lemma Step1CaseTwoOutsideRestrictedAugmentation {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
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
        (((∀ (q : Fin lower.rounds) (v : V),
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
           ModColoring lower sigma)))
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base) (good : GoodHierarchy H)
    (q : ℕ) (hdivider : H.dividerCount < q)
    (hfewer : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (other : ExtendedTashkinovTree G k e0 input' T' generating'),
      other.rounds = ett.rounds → MaximumProperty other →
      ∀ (base' : HierarchyBase other generating')
        (K : TashkinovHierarchy other base'),
        GoodHierarchy K → K.dividerCount < q →
        ColoredVertexSetElementary G generating'
          (TreeSequenceVertexSet T'))
    (hlarge : 2 * ett.rounds + 11 ≤
      (TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card)
    (hterminal : TreeColorSetMinusClosed G phi T
      ((HierarchyTerminalStoredColors H).biUnion
        (good.gamma (Fin.last H.dividerCount))))
    (hElementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T))
    (alpha beta : Fin k) (halpha : alpha ∈ TreeMissingColors phi T)
    (hclosed : TreeColorSetClosed G phi T {alpha})
    (hne : alpha ≠ beta) (hbeta : beta ∉ TreeMissingColors phi T)
    (a₁ b₁ a₂ b₂ a₃ b₃ : V)
    (P₁ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₁) (Sum.inl b₁))
    (P₂ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₂) (Sum.inl b₂))
    (P₃ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₃) (Sum.inl b₃))
    (hP₁ : TreeExitPath T phi alpha beta a₁ b₁ P₁)
    (hP₂ : TreeExitPath T phi alpha beta a₂ b₂ P₂)
    (hP₃ : TreeExitPath T phi alpha beta a₃ b₃ P₃)
    (hpaths₁₂ : ∀ x, x ∈ P₁.support → x ∉ P₂.support)
    (hpaths₁₃ : ∀ x, x ∈ P₁.support → x ∉ P₃.support)
    (hpaths₂₃ : ∀ x, x ∈ P₂.support → x ∉ P₃.support)
    (ha₁₂ : a₁ ≠ a₂) (ha₁₃ : a₁ ≠ a₃) (ha₂₃ : a₂ ≠ a₃)
    (hb₁₂ : b₁ ≠ b₂) (hb₁₃ : b₁ ≠ b₃) (hb₂₃ : b₂ ≠ b₃)
    (horder₁₂ : TreeVertexOrder T b₁ b₂)
    (horder₂₃ : TreeVertexOrder T b₂ b₃)
    (f₁ f₂ f₃ : E)
    (hf₁ : f₁ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta)
    (hf₂ : f₂ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta)
    (hf₃ : f₃ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta)
    (hif₁ : Incident G b₁ f₁) (hif₂ : Incident G b₂ f₂)
    (hif₃ : Incident G b₃ f₃)
    (hPf₁ : Sum.inr f₁ ∈ P₁.support)
    (hPf₂ : Sum.inr f₂ ∈ P₂.support)
    (hPf₃ : Sum.inr f₃ ∈ P₃.support)
    (houtside : b₃ ∉ TreeSequenceVertexSet
      (HierarchyStarredStage H (Fin.last H.dividerCount)))
    (hnoBetter :
      ∀ (sigma : PartialEdgeColoring E k) (T' : TreeSequence G e0)
        (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T'),
        IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
        StableColoring
          (ett.series.data.tree (Fin.last ett.rounds).castSucc)
          (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
          phi sigma →
        MaximumProperty corr.replacementETT →
        ∀ (base' : HierarchyBase corr.replacementETT sigma)
          (K : TashkinovHierarchy corr.replacementETT base')
          (good' : GoodHierarchy K),
          K.dividerCount = H.dividerCount →
          2 * corr.replacementETT.rounds + 11 ≤
            (TreeMissingColors sigma
              (corr.replacementETT.series.data.tree
                (Fin.last corr.replacementETT.rounds).castSucc)).card →
          TreeColorSetMinusClosed G sigma T'
            ((HierarchyTerminalStoredColors K).biUnion
              (good'.gamma (Fin.last K.dividerCount))) →
          ∀ (a b : Fin k), a ≠ b →
            a ∈ TreeMissingColors sigma T' →
            TreeColorSetClosed G sigma T' {a} →
            ∀ (u₁ v₁ u₂ v₂ : V)
              (Q₁ : (TwoColorIncidenceGraph G sigma a b).Walk
                (Sum.inl u₁) (Sum.inl v₁))
              (Q₂ : (TwoColorIncidenceGraph G sigma a b).Walk
                (Sum.inl u₂) (Sum.inl v₂)),
              TreeExitPath T' sigma a b u₁ v₁ Q₁ →
              TreeExitPath T' sigma a b u₂ v₂ Q₂ →
              (∀ x, x ∈ Q₁.support → x ∉ Q₂.support) →
              u₁ ≠ u₂ →
              (b ∈ TreeMissingColors sigma T' ∨
                (b ∉ TreeMissingColors sigma T' ∧
                  ∃ (u₃ v₃ : V)
                    (Q₃ : (TwoColorIncidenceGraph G sigma a b).Walk
                      (Sum.inl u₃) (Sum.inl v₃)),
                    TreeExitPath T' sigma a b u₃ v₃ Q₃ ∧
                    (∀ x, x ∈ Q₁.support → x ∉ Q₃.support) ∧
                    (∀ x, x ∈ Q₂.support → x ∉ Q₃.support) ∧
                    u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧
                    Q₁.length + Q₂.length + Q₃.length <
                      P₁.length + P₂.length + P₃.length)) →
              False)
    (hseed :
      ∃ (gamma : Fin k) (mu : PartialEdgeColoring E k)
        (C J₁ J : TreeSequence G e0)
        (corrJ : CorrespondingExtendedTashkinovTree G k e0 ett mu J)
        (baseJ : HierarchyBase corrJ.replacementETT mu)
        (KJ : TashkinovHierarchy corrJ.replacementETT baseJ)
        (goodJ : GoodHierarchy KJ)
        (R₁ : (TwoColorIncidenceGraph G mu gamma beta).Walk
          (Sum.inl a₁) (Sum.inl b₁))
        (R₂ : (TwoColorIncidenceGraph G mu gamma beta).Walk
          (Sum.inl a₂) (Sum.inl b₂))
        (R₃ : (TwoColorIncidenceGraph G mu gamma beta).Walk
          (Sum.inl a₃) (Sum.inl b₃)),
        gamma ≠ beta ∧
        IsProperEdgeColoring G mu ∧ IsOneEdgeUncolored mu e0 ∧
        StableColoring
          (ett.series.data.tree (Fin.last ett.rounds).castSucc)
          (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
          phi mu ∧
        ModColoring ett mu ∧
        MaximumProperty corrJ.replacementETT ∧
        KJ.dividerCount = H.dividerCount ∧
        2 * corrJ.replacementETT.rounds + 11 ≤
          (TreeMissingColors mu
            (corrJ.replacementETT.series.data.tree
              (Fin.last corrJ.replacementETT.rounds).castSucc)).card ∧
        gamma ∉ (HierarchyStoredColorsAt KJ
          (Fin.last KJ.dividerCount)).biUnion
            (goodJ.gamma (Fin.last KJ.dividerCount)) ∧
        beta ∉ (HierarchyStoredColorsAt KJ
          (Fin.last KJ.dividerCount)).biUnion
            (goodJ.gamma (Fin.last KJ.dividerCount)) ∧
        beta ∈ MissingColors G mu b₃ ∧
        TreeExitPath T mu gamma beta a₁ b₁ R₁ ∧
        TreeExitPath T mu gamma beta a₂ b₂ R₂ ∧
        TreeExitPath T mu gamma beta a₃ b₃ R₃ ∧
        (∀ x, x ∈ R₁.support → x ∉ R₂.support) ∧
        (∀ x, x ∈ R₁.support → x ∉ R₃.support) ∧
        (∀ x, x ∈ R₂.support → x ∉ R₃.support) ∧
        R₁.support = P₁.support ∧ R₂.support = P₂.support ∧
        R₃.support = P₃.support ∧
        R₁.length = P₁.length ∧ R₂.length = P₂.length ∧
        R₃.length = P₃.length ∧
        TreeSequenceInitialSegment C T ∧
        C.vertex (Fin.last C.length) = b₃ ∧
        TreeSequenceAdjoinEdge C f₁ J₁ ∧
        TreeSequenceAdjoinEdge J₁ f₂ J ∧
        (∀ v, Incident G v f₁ → v ∈ TreeSequenceVertexSet J) ∧
        (∀ v, Incident G v f₂ → v ∈ TreeSequenceVertexSet J) ∧
        b₁ ∈ TreeSequenceVertexSet J ∧
        b₂ ∈ TreeSequenceVertexSet J ∧
        b₃ ∈ TreeSequenceVertexSet J) : False := by
-- BODY
  classical
  rcases hseed with ⟨gamma, mu, C, J₁, J, corrJ, baseJ, KJ, goodJ,
    R₁, R₂, R₃, hgammaBeta, hproperMu, honeMu, hstableMu, hmodMu,
    hMPJ, hcountJ, hlargeJ, hgammaAvoid, hbetaAvoid, hbetaB₃,
    hR₁, hR₂, hR₃, hdisR₁₂, hdisR₁₃, hdisR₂₃,
    hsuppR₁, hsuppR₂, hsuppR₃, hlenR₁, hlenR₂, hlenR₃,
    hCT, hlastC, hCedge₁, hJedge₂, hf₁ends, hf₂ends,
    hb₁J, hb₂J, hb₃J⟩
  obtain ⟨m, chain, U, hfirst, hlast, hsteps, hlengths, hsegments,
      hvertices, hsequence, havoid, hmaximal, corrU, hMPU, baseU,
      hcore, hclosure, hsupport, KU, hcount, hstages, hdividers,
      goodU, hgamma, hstored, hminus⟩ :=
    GoodHierarchyRestrictedAugmentation G k e0 input T phi mu ett hmodMu
      hMP J corrJ baseJ KJ goodJ
  have hJU : TreeSequenceInitialSegment J U := by
    rw [← hfirst, ← hlast]
    exact hsegments 0 (Fin.last m) (by simp)
  have hJUvertices := TreeSequenceInitialSegmentVertexSetSubset hJU
  have hb₁U := hJUvertices hb₁J
  have hb₂U := hJUvertices hb₂J
  have hb₃U := hJUvertices hb₃J
  have hbetaU : beta ∈ TreeMissingColors mu U :=
    Finset.mem_biUnion.mpr ⟨b₃, hb₃U, hbetaB₃⟩
  have hcountU : KU.dividerCount = H.dividerCount := hcount.trans hcountJ
  have hKUlt : KU.dividerCount < q := by rw [hcountU]; exact hdivider
  have hElementaryU : ColoredVertexSetElementary G mu
      (TreeSequenceVertexSet U) :=
    hfewer corrU.replacementETT corrU.rungAgreement hMPU baseU KU goodU hKUlt
  have hlastIndex : Fin.cast (congrArg (fun n : ℕ => n + 1) hcount)
      (Fin.last KU.dividerCount) = Fin.last KJ.dividerCount := by
    apply Fin.ext
    simp
  have avoidTransport (c : Fin k)
      (hc : c ∉ (HierarchyStoredColorsAt KJ (Fin.last KJ.dividerCount)).biUnion
        (goodJ.gamma (Fin.last KJ.dividerCount))) :
      c ∉ (HierarchyTerminalStoredColors KU).biUnion
        (goodU.gamma (Fin.last KU.dividerCount)) := by
    intro h
    obtain ⟨eta, heta, hcEta⟩ := Finset.mem_biUnion.mp h
    apply hc
    refine Finset.mem_biUnion.mpr ⟨eta, hstored heta, ?_⟩
    rw [hgamma (Fin.last KU.dividerCount) eta, hlastIndex] at hcEta
    exact hcEta
  have hgammaAvoidU := avoidTransport gamma hgammaAvoid
  have hbetaAvoidU := avoidTransport beta hbetaAvoid
  have closedColor (c : Fin k) (hc : c ∈ TreeMissingColors mu U)
      (havoidC : c ∉ (HierarchyTerminalStoredColors KU).biUnion
        (goodU.gamma (Fin.last KU.dividerCount))) :
      TreeColorSetClosed G mu U {c} := by
    intro d hd
    have hdc : d = c := by simpa using hd
    subst d
    exact hminus c (Finset.mem_sdiff.mpr ⟨hc, havoidC⟩)
  have hbetaClosedU := closedColor beta hbetaU hbetaAvoidU
  obtain ⟨ha₁U, ha₂U, ha₃U⟩ :=
    P2716_T2_ElementaryEndpointExclusion G mu T U gamma beta
      a₁ b₁ a₂ b₂ a₃ b₃ R₁ R₂ R₃ hR₁ hR₂ hR₃ ha₁₂
      hb₁U hb₂U hb₃U hElementaryU hbetaB₃ hbetaClosedU
      (fun hc => closedColor gamma hc hgammaAvoidU)
  obtain ⟨v₁, L₁, hL₁, hsL₁, hlL₁, hstrictL₁⟩ :=
    P2716_T2_FirstEntryClipping G mu U gamma beta a₁ b₁ R₁ hR₁.1
      hR₁.2.2.2.2.1 ha₁U hb₁U
  obtain ⟨v₂, L₂, hL₂, hsL₂, hlL₂, hstrictL₂⟩ :=
    P2716_T2_FirstEntryClipping G mu U gamma beta a₂ b₂ R₂ hR₂.1
      hR₂.2.2.2.2.1 ha₂U hb₂U
  obtain ⟨v₃, L₃, hL₃, hsL₃, hlL₃, hstrictL₃⟩ :=
    P2716_T2_FirstEntryClipping G mu U gamma beta a₃ b₃ R₃ hR₃.1
      hR₃.2.2.2.2.1 ha₃U hb₃U
  have hf₁R : Sum.inr f₁ ∈ R₁.support := by rw [hsuppR₁]; exact hPf₁
  have hl₁strict : L₁.length < R₁.length :=
    hstrictL₁ f₁ hf₁R (fun v hv => hJUvertices (hf₁ends v hv))
  have htotal : L₁.length + L₂.length + L₃.length <
      P₁.length + P₂.length + P₃.length := by omega
  -- Normalize the dependent presentation of the final ladder tree.
  have terminalTreeEq {W : TreeSequence G e0}
      (corr : CorrespondingExtendedTashkinovTree G k e0 ett mu W) :
      corr.replacementETT.series.data.tree
          (Fin.last corr.replacementETT.rounds).castSucc =
        ett.series.data.tree (Fin.last ett.rounds).castSucc := by
    let replacementSeries : TashkinovSeries G k corr.replacementETT.rounds e0
        corr.replacementInput :=
      cast (congrArg (fun n => TashkinovSeries G k n e0 corr.replacementInput)
        corr.rungAgreement.symm) corr.replacementSeries
    have castTree {a b : ℕ} (h : a = b)
        (s : TashkinovSeries G k a e0 corr.replacementInput)
        (i : Fin (b + 2)) :
        (cast (congrArg (fun n => TashkinovSeries G k n e0 corr.replacementInput) h)
          s).data.tree i = s.data.tree (Fin.cast (congrArg (fun n => n + 2) h.symm) i) := by
      cases h
      rfl
    have hseries : corr.replacementETT.series = replacementSeries := by
      exact ((cast_eq_iff_heq
        (e := congrArg (fun n => TashkinovSeries G k n e0 corr.replacementInput)
          corr.rungAgreement.symm)
        (a := corr.replacementSeries) (a' := corr.replacementETT.series)).2
        corr.seriesPresentation.symm).symm
    let terminalIndex : Fin corr.replacementETT.rounds :=
      Fin.cast corr.rungAgreement.symm
        ⟨ett.rounds - 1, by have hp := ett.roundsPositive; omega⟩
    have htree : corr.replacementETT.series.data.tree terminalIndex.succ.castSucc =
        ett.series.data.tree (Fin.last ett.rounds).castSucc := by
      rw [hseries]
      calc
        replacementSeries.data.tree terminalIndex.succ.castSucc =
            corr.replacementSeries.data.tree
              (Fin.cast (congrArg (fun n => n + 2) corr.rungAgreement)
                terminalIndex.succ.castSucc) := by
          simpa [replacementSeries] using
            (castTree corr.rungAgreement.symm corr.replacementSeries
              terminalIndex.succ.castSucc)
        _ = ett.series.data.tree (Fin.last ett.rounds).castSucc := by
          convert corr.ladderTreesAgree (Fin.cast corr.rungAgreement terminalIndex) using 1
          · congr 1
          · congr 1
            apply Fin.ext
            have hp := ett.roundsPositive
            simp [terminalIndex, Nat.sub_add_cancel hp]
    have hi : (Fin.last corr.replacementETT.rounds).castSucc =
        terminalIndex.succ.castSucc := by
      apply Fin.ext
      have hp := ett.roundsPositive
      simp [terminalIndex, Nat.sub_add_cancel hp]
      exact corr.rungAgreement
    rw [hi]
    exact htree
  have hlargeU : 2 * corrU.replacementETT.rounds + 11 ≤
      (TreeMissingColors mu (corrU.replacementETT.series.data.tree
        (Fin.last corrU.replacementETT.rounds).castSucc)).card := by
    rw [terminalTreeEq corrU, corrU.rungAgreement]
    rw [terminalTreeEq corrJ, corrJ.rungAgreement] at hlargeJ
    exact hlargeJ
  -- Reorder the colors without changing any exact support or walk length.
  have hflip : TwoColorIncidenceGraph G mu gamma beta ≤
      TwoColorIncidenceGraph G mu beta gamma := by
    intro x y hxy
    cases x <;> cases y <;> simpa only [TwoColorIncidenceGraph, or_comm] using hxy
  have flipExit {a v : V}
      (L : (TwoColorIncidenceGraph G mu gamma beta).Walk (Sum.inl a) (Sum.inl v))
      (hL : TreeExitPath U mu gamma beta a v L) :
      TreeExitPath U mu beta gamma a v (L.mapLe hflip) := by
    rcases hL with ⟨hpath, hlen, ha, hv, hmissing, honly⟩
    refine ⟨hpath.mapLe hflip, ?_, ha, hv, hmissing.symm, ?_⟩
    · simpa only [SimpleGraph.Walk.length_mapLe] using hlen
    · simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using honly
  let Q₁ := L₁.mapLe hflip
  let Q₂ := L₂.mapLe hflip
  let Q₃ := L₃.mapLe hflip
  have hQ₁ := flipExit L₁ hL₁
  have hQ₂ := flipExit L₂ hL₂
  have hQ₃ := flipExit L₃ hL₃
  have hdQ₁₂ : ∀ x, x ∈ Q₁.support → x ∉ Q₂.support := by
    simpa only [Q₁, Q₂, SimpleGraph.Walk.support_mapLe_eq_support] using
      (fun x hx hy => hdisR₁₂ x (hsL₁ x hx) (hsL₂ x hy))
  have hdQ₁₃ : ∀ x, x ∈ Q₁.support → x ∉ Q₃.support := by
    simpa only [Q₁, Q₃, SimpleGraph.Walk.support_mapLe_eq_support] using
      (fun x hx hy => hdisR₁₃ x (hsL₁ x hx) (hsL₃ x hy))
  have hdQ₂₃ : ∀ x, x ∈ Q₂.support → x ∉ Q₃.support := by
    simpa only [Q₂, Q₃, SimpleGraph.Walk.support_mapLe_eq_support] using
      (fun x hx hy => hdisR₂₃ x (hsL₂ x hx) (hsL₃ x hy))
  apply hnoBetter mu U corrU hproperMu honeMu hstableMu hMPU
    baseU KU goodU hcountU hlargeU hminus beta gamma hgammaBeta.symm
    hbetaU hbetaClosedU a₁ v₁ a₂ v₂ Q₁ Q₂ hQ₁ hQ₂ hdQ₁₂ ha₁₂
  by_cases hgammaU : gamma ∈ TreeMissingColors mu U
  · exact Or.inl hgammaU
  · right
    refine ⟨hgammaU, a₃, v₃, Q₃, hQ₃, hdQ₁₃, hdQ₂₃, ha₁₃, ha₂₃, ?_⟩
    simpa only [Q₁, Q₂, Q₃, SimpleGraph.Walk.length_mapLe] using htotal
