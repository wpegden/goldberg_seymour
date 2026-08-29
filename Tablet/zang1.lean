import Tablet.AdjacentEdges
import Tablet.BoundaryEdges
import Tablet.ColoredVertexSetClosed
import Tablet.ColoredVertexSetStronglyClosed
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.LooplessMultigraph
import Tablet.MissingColors
import Tablet.PartialEdgeColoring
import Tablet.PresentColors
import Tablet.StableColoring
import Tablet.TreeIncidentEdge
import Tablet.TreeMissingColors
import Tablet.TreeSequence
import Tablet.TreeSequenceVertexSet
import Tablet.sc1

-- [TABLET NODE: zang1]
theorem zang1 {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : LooplessMultigraph V E) {k : ℕ}
    (e0 : E) (T : TreeSequence G e0) (C : Finset (Fin k))
    (phi pi : PartialEdgeColoring E k)
    (hproperPhi : IsProperEdgeColoring G phi)
    (honePhi : IsOneEdgeUncolored phi e0)
    (hproperPi : IsProperEdgeColoring G pi)
    (honePi : IsOneEdgeUncolored pi e0)
    (hodd : Odd (TreeSequenceVertexSet T).card)
    (hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T))
    (hnotstrong : ¬ ColoredVertexSetStronglyClosed G phi (TreeSequenceVertexSet T))
    (hstable : StableColoring T C phi pi) :
    ColoredVertexSetClosed G pi (TreeSequenceVertexSet T) ∧
      ¬ ColoredVertexSetStronglyClosed G pi (TreeSequenceVertexSet T) := by
-- BODY
  classical
  let X := TreeSequenceVertexSet T
  let B := BoundaryEdges G X
  have hmiss : ∀ v ∈ X, MissingColors G pi v = MissingColors G phi v := by
    intro v hv
    exact hstable.2 v hv
  have htree : TreeMissingColors pi T = TreeMissingColors phi T := by
    unfold TreeMissingColors
    ext c
    simp only [Finset.mem_biUnion]
    constructor <;> rintro ⟨v, hv, hc⟩ <;> refine ⟨v, hv, ?_⟩
    · simpa [hmiss v hv] using hc
    · simpa [hmiss v hv] using hc
  have htreepi : TreeMissingColors pi T = TreeMissingColors phi T := htree
  have hincident_boundary : ∀ {f : E}, f ∈ B → TreeIncidentEdge T f := by
    intro f hf
    simp only [B, BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    obtain ⟨v, hv, w, hw, he⟩ := hf
    refine ⟨v, hv, ?_⟩
    change v ∈ G.ends f
    rw [he]
    exact Sym2.mem_mk_left _ _
  have hclosedPi : ColoredVertexSetClosed G pi X := by
    intro f c v hf hv hfc
    have htf := hincident_boundary hf
    have hstab := (sc1 G e0 T C phi pi hproperPhi honePhi hproperPi honePi).mp hstable
    intro hmpi
    have hmphi : c ∈ MissingColors G phi v := by
      simpa [hmiss v hv] using hmpi
    have hcmem : c ∈ TreeMissingColors phi T ∪ C := by
      apply Finset.mem_union_left
      simp only [TreeMissingColors, Finset.mem_biUnion]
      exact ⟨v, hv, hmphi⟩
    have heq : pi f = phi f := hstab f htf (Or.inr ⟨c, hcmem, hfc⟩)
    have hphi : phi f = some c := by simpa [heq] using hfc
    exact (hclosed hf hv hphi) hmphi
  have hXnonempty : X.Nonempty := by
    let z : Fin (T.length + 1) := ⟨0, Nat.succ_pos _⟩
    refine ⟨T.vertex z, ?_⟩
    simp only [X, TreeSequenceVertexSet, Finset.mem_image]
    exact ⟨z, Finset.mem_univ _, rfl⟩
  have hboundary_color : ∀ c : Fin k, c ∉ TreeMissingColors phi T →
      ∃ f ∈ B, phi f = some c := by
    intro c hc
    let edges := (Finset.univ : Finset E).filter (fun f => phi f = some c)
    let good := edges.filter (fun f => ∀ v, Incident G v f → v ∈ X)
    have hedge : ∀ f, f ∈ edges ↔ phi f = some c := by
      intro f
      simp [edges]
    have hpresent : ∀ v, v ∈ X → ∃ f, Incident G v f ∧ phi f = some c := by
      intro v hv
      have hcmiss : c ∉ MissingColors G phi v := by
        intro hm
        apply hc
        simp only [TreeMissingColors, Finset.mem_biUnion]
        exact ⟨v, hv, hm⟩
      have hcp : c ∈ PresentColors G phi v := by
        simpa [MissingColors] using hcmiss
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hcp
      obtain ⟨f, hfv, hfc⟩ := hcp
      exact ⟨f, hfv, hfc⟩
    have hgood_mem : ∀ f, f ∈ good ↔ f ∈ edges ∧ ∀ v, Incident G v f → v ∈ X := by
      intro f
      simp [good]
    by_contra hnone
    have hgood_all : ∀ f, f ∈ good → ∀ v, Incident G v f → v ∈ X := by
      intro f hf v hv
      exact (hgood_mem f).mp hf |>.2 v hv
    have hgood_disjoint : ∀ ⦃f g⦄, f ∈ good → g ∈ good → f ≠ g →
        Disjoint (G.ends f).toFinset (G.ends g).toFinset := by
      intro f g hf hg hfg
      rw [Finset.disjoint_left]
      intro v hfv hgv
      exact (hproperPhi hfg ⟨v, Sym2.mem_toFinset.mp hfv, Sym2.mem_toFinset.mp hgv⟩
        (hedge f |>.mp (hgood_mem f |>.mp hf).1))
        (hedge g |>.mp (hgood_mem g |>.mp hg).1)
    have hendcard : ∀ f : E, (G.ends f).toFinset.card = 2 := by
      intro f
      apply Sym2.card_toFinset_of_not_isDiag
      intro hd
      exact G.loopless f ((G.ends f).diagElem hd) (Sym2.diag_diagElem hd).symm
    have hunioncard : (good.biUnion fun f => (G.ends f).toFinset).card = 2 * good.card := by
      have aux : ∀ s : Finset E, s ⊆ good →
          (s.biUnion fun f => (G.ends f).toFinset).card = 2 * s.card := by
        intro s hs
        induction s using Finset.induction_on with
        | empty => simp
        | @insert f s hfs ih =>
          rw [Finset.biUnion_insert]
          have hd : Disjoint (G.ends f).toFinset
              (s.biUnion fun g => (G.ends g).toFinset) := by
            rw [Finset.disjoint_left]
            intro v hfv hvs
            obtain ⟨g, hg, hvg⟩ := Finset.mem_biUnion.mp hvs
            exact (Finset.disjoint_left.mp (hgood_disjoint
              (hs (Finset.mem_insert_self f s)) (hs (Finset.mem_insert_of_mem hg)) (by
                intro hfg
                exact hfs (by simpa [hfg] using hg)))) hfv hvg
          rw [Finset.card_union_of_disjoint hd, hendcard]
          rw [ih (fun g hg => hs (Finset.mem_insert_of_mem hg))]
          rw [Finset.card_insert_of_notMem hfs]
          omega
      exact aux good (by intro f hf; exact hf)
    have hunion_sub : good.biUnion (fun f => (G.ends f).toFinset) ⊆ X := by
      intro v hv
      obtain ⟨f, hf, hfv⟩ := Finset.mem_biUnion.mp hv
      exact hgood_all f hf v (Sym2.mem_toFinset.mp hfv)
    have hX_sub : X ⊆ good.biUnion (fun f => (G.ends f).toFinset) := by
      intro v hv
      obtain ⟨f, hfv, hfc⟩ := hpresent v hv
      have hfnot : f ∉ B := by
        intro hfb
        exact hnone ⟨f, hfb, hfc⟩
      have hall : ∀ w, Incident G w f → w ∈ X := by
        intro w hw
        by_cases hwX : w ∈ X
        · exact hwX
        · exfalso
          have hvw : v ≠ w := by
            intro hvw
            exact hwX (hvw ▸ hv)
          have heends : G.ends f = s(v, w) :=
            (Sym2.mem_and_mem_iff hvw).mp ⟨by simpa [Incident] using hfv,
              by simpa [Incident] using hw⟩
          apply hfnot
          simp only [B, BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨v, hv, w, hwX, heends⟩
      have hgoodf : f ∈ good := (hgood_mem f).mpr ⟨by simpa [edges] using hfc, hall⟩
      exact Finset.mem_biUnion.mpr ⟨f, hgoodf,
        Sym2.mem_toFinset.mpr (by simpa [Incident] using hfv)⟩
    have heq : good.biUnion (fun f => (G.ends f).toFinset) = X :=
      Finset.Subset.antisymm hunion_sub hX_sub
    have hcardeq : X.card = 2 * good.card := by
      rw [← hunioncard, heq]
    rcases hodd with ⟨q, hq⟩
    rw [hq] at hcardeq
    omega
  change ColoredVertexSetClosed G pi X ∧ _
  refine ⟨hclosedPi, ?_⟩
  intro hstrongPi
  have hrep : ∃ f ∈ B, ∃ g ∈ B, f ≠ g ∧ ∃ c, phi f = some c ∧ phi g = some c := by
    by_contra hn
    apply hnotstrong
    refine ⟨hclosed, ?_⟩
    intro f g c hf hg hfg hfc
    by_contra hgc
    apply hn
    exact ⟨f, hf, g, hg, hfg, c, hfc, hgc⟩
  obtain ⟨f, hf, g, hg, hfg, c, hfc, hgc⟩ := hrep
  have hc_out : c ∉ TreeMissingColors phi T := by
    intro hcm
    have hcmv : ∃ v ∈ X, c ∈ MissingColors G phi v := by
      simp only [TreeMissingColors, Finset.mem_biUnion] at hcm
      exact hcm
    obtain ⟨v, hv, hmv⟩ := hcmv
    exact (hclosed hf hv hfc) hmv
  let S := (Finset.univ : Finset (Fin k)) \ TreeMissingColors phi T
  let chooseBoundary : (c : Fin k) → c ∈ S → E := fun d hd =>
    Classical.choose (hboundary_color d (Finset.mem_sdiff.mp hd).2)
  have chooseBoundary_mem : ∀ d hd, chooseBoundary d hd ∈ B := by
    intro d hd
    exact (Classical.choose_spec (hboundary_color d (Finset.mem_sdiff.mp hd).2)).1
  have chooseBoundary_color : ∀ d hd,
      phi (chooseBoundary d hd) = some d := by
    intro d hd
    exact (Classical.choose_spec (hboundary_color d (Finset.mem_sdiff.mp hd).2)).2
  have chooseBoundary_inj : ∀ d₁ hd₁ d₂ hd₂,
      chooseBoundary d₁ hd₁ = chooseBoundary d₂ hd₂ → d₁ = d₂ := by
    intro d₁ hd₁ d₂ hd₂ heq
    have hh := chooseBoundary_color d₁ hd₁
    have hh' := chooseBoundary_color d₂ hd₂
    exact Option.some.inj (heq ▸ hh |>.symm.trans hh')
  have he0not : e0 ∉ B := by
    intro he0
    obtain ⟨i, hi⟩ := T.attaches ⟨0, T.positive⟩
    let z : Fin (T.length + 1) :=
      Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ T.positive))
    have hv1 : T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩ ∈ X := by
      simp [X, TreeSequenceVertexSet]
    have hv0 : T.vertex z ∈ X := by
      simp [X, TreeSequenceVertexSet]
    have heq : G.ends e0 = G.ends (T.edge ⟨0, T.positive⟩) := by
      rw [T.first_edge]
    simp only [B, BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he0
    obtain ⟨u, hu, w, hw, hend⟩ := he0
    have huend : u ∈ G.ends e0 := by
      rw [hend]
      exact Sym2.mem_mk_left _ _
    have hwend : w ∈ G.ends e0 := by
      rw [hend]
      exact Sym2.mem_mk_right _ _
    have huX : u ∈ X := by
      rw [heq, hi] at huend
      rcases (Sym2.mem_iff.mp huend) with h | h
      · simpa [h] using hv1
      · simpa [h, z] using hv0
    have hwX : w ∈ X := by
      rw [heq, hi] at hwend
      rcases (Sym2.mem_iff.mp hwend) with h | h
      · simpa [h] using hv1
      · simpa [h, z] using hv0
    exact hw hwX
  have hcoloredB : ∀ q, q ∈ B → ∃ d, pi q = some d := by
    intro q hq
    have hne : q ≠ e0 := by
      intro hqe
      exact he0not (hqe ▸ hq)
    exact honePi.2 q hne
  have hpi_out : ∀ (q : E) (hq : q ∈ B) (d : Fin k),
      pi q = some d → d ∈ S := by
    intro q hq d hqd
    have hv := hXnonempty
    obtain ⟨v, hv⟩ := hv
    have hdmiss : d ∉ MissingColors G pi v := by
      intro hd
      exact (hclosedPi hq hv hqd) hd
    have hdmissPhi : d ∉ MissingColors G phi v := by
      simpa [hmiss v hv] using hdmiss
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
      intro hdt
      simp only [TreeMissingColors, Finset.mem_biUnion] at hdt
      obtain ⟨w, hw, hdm⟩ := hdt
      have hbad : d ∈ MissingColors G pi w := by
        simpa [hmiss w hw] using hdm
      exact (hclosedPi hq hw hqd) hbad
      ⟩
  let choosePi : (q : E) → q ∈ B → Fin k := fun q hq =>
    Classical.choose (hcoloredB q hq)
  have choosePi_spec : ∀ q hq, pi q = some (choosePi q hq) := by
    intro q hq
    exact Classical.choose_spec (hcoloredB q hq)
  have choosePi_mem : ∀ q hq, choosePi q hq ∈ S := by
    intro q hq
    exact hpi_out q hq _ (choosePi_spec q hq)
  have choosePi_inj : ∀ q₁ hq₁ q₂ hq₂,
      choosePi q₁ hq₁ = choosePi q₂ hq₂ → q₁ = q₂ := by
    intro q₁ hq₁ q₂ hq₂ heq
    by_contra hn
    have hs := hstrongPi.2 hq₁ hq₂ hn (choosePi_spec q₁ hq₁)
    apply hs
    simpa [heq] using (choosePi_spec q₂ hq₂)
  let attachedPi := B.attach.image (fun q : {q // q ∈ B} => choosePi q.1 q.2)
  have happ : attachedPi.card = B.card := by
    dsimp [attachedPi]
    have hh : (B.attach.image (fun q : {q // q ∈ B} => choosePi q.1 q.2)).card =
        B.attach.card := Finset.card_image_iff.mpr (by
      intro q₁ hq₁ q₂ hq₂ heq
      exact Subtype.ext (choosePi_inj q₁.1 q₁.2 q₂.1 q₂.2 heq))
    calc
      _ = B.attach.card := hh
      _ = B.card := by simp
  have hB_le : B.card ≤ S.card := by
    rw [← happ]
    apply Finset.card_le_card
    intro d hd
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hd
    simpa [heq] using choosePi_mem q.1 q.2
  let imageBoundary := S.attach.image (fun d : {d // d ∈ S} => chooseBoundary d.1 d.2)
  have himage_sub : imageBoundary ⊆ B := by
    intro q hq
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hq
    exact chooseBoundary_mem d.1 d.2
  have himage_card : imageBoundary.card = S.card := by
    dsimp [imageBoundary]
    have hh : (S.attach.image (fun d : {d // d ∈ S} => chooseBoundary d.1 d.2)).card =
        S.attach.card := Finset.card_image_iff.mpr (by
      intro d₁ hd₁ d₂ hd₂ heq
      exact Subtype.ext (chooseBoundary_inj d₁.1 d₁.2 d₂.1 d₂.2 heq))
    simpa using hh
  have hcS : c ∈ S := by
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hc_out⟩
  let extra := if chooseBoundary c hcS = f then g else f
  have hextra : extra ∈ B := by
    dsimp [extra]
    split <;> assumption
  have hextra_ne : extra ≠ chooseBoundary c hcS := by
    dsimp [extra]
    split
    · intro heq
      exact hfg (heq.trans ‹chooseBoundary c hcS = f›).symm
    · exact (‹chooseBoundary c hcS ≠ f›).symm
  have hnotimage : extra ∉ imageBoundary := by
    intro hgi
    obtain ⟨d, hd, hgd⟩ := Finset.mem_image.mp hgi
    have hdcol := chooseBoundary_color d.1 d.2
    have hextracol : phi extra = some c := by
      dsimp [extra]
      split <;> assumption
    have hsame : d.1 = c := by
      apply Option.some.inj
      exact hdcol.symm.trans ((congrArg phi hgd).trans hextracol)
    have hedges : chooseBoundary c hcS = extra := by
      have heq : chooseBoundary c hcS = chooseBoundary d.1 d.2 := by
        simpa [hsame]
      exact heq.trans hgd
    exact hextra_ne hedges.symm
  have hlt : S.card < B.card := by
    rw [← himage_card]
    apply Finset.card_lt_card
    refine ⟨?_, ?_⟩
    · intro q hq
      exact himage_sub hq
    · intro hsub
      exact hnotimage (hsub hextra)
  omega
