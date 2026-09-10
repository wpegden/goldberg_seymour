import Tablet.AdjacentEdges
import Tablet.ColoredVertexSetElementary
import Tablet.Degree
import Tablet.Incident
import Tablet.IsOneEdgeUncolored
import Tablet.IsProperEdgeColoring
import Tablet.LooplessMultigraph
import Tablet.MaximumDegree
import Tablet.MissingColors
import Tablet.PresentColors
import Tablet.TreeMissingColors
import Tablet.TreeSequenceVertexSet

open scoped Sym2

-- [TABLET NODE: CommonMissingColorsAtUncoloredEndpoints]
theorem CommonMissingColorsAtUncoloredEndpoints
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (phi : PartialEdgeColoring E k) (A B : TreeSequence G e0)
    (x y : V) (hends : G.ends e0 = s(x, y))
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hdegree : MaximumDegree G + 1 <= k)
    (hxA : x ∈ TreeSequenceVertexSet A)
    (hyA : y ∈ TreeSequenceVertexSet A)
    (hxB : x ∈ TreeSequenceVertexSet B)
    (hyB : y ∈ TreeSequenceVertexSet B)
    (helem : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet A ∪ TreeSequenceVertexSet B)) :
    4 <= (TreeMissingColors phi A ∩ TreeMissingColors phi B).card := by
-- BODY
  classical
  have hxy : x ≠ y := by
    intro h
    subst y
    exact G.loopless e0 x hends
  have hx0 : Incident G x e0 := by
    simp [Incident, hends]
  have hy0 : Incident G y e0 := by
    simp [Incident, hends]
  have colored_iff : forall v e,
      (Incident G v e ∧ exists c, phi e = some c) ↔
        Incident G v e ∧ e ≠ e0 := by
    intro v e
    constructor
    · rintro ⟨hv, c, hc⟩
      refine ⟨hv, ?_⟩
      intro he
      subst e
      rw [hone.1] at hc
      simp at hc
    · rintro ⟨hv, he⟩
      obtain ⟨c, hc⟩ := hone.2 e he
      exact ⟨hv, c, hc⟩
  have present_card : forall v,
      (PresentColors G phi v).card =
        (Finset.univ.filter fun e =>
          Incident G v e ∧ exists c, phi e = some c).card := by
    intro v
    let colored := Finset.univ.filter fun e =>
      Incident G v e ∧ exists c, phi e = some c
    let chooseColor : (e : E) -> e ∈ colored -> Fin k :=
      fun e he => Classical.choose (Finset.mem_filter.mp he).2.2
    have choose_spec : forall (e : E) (he : e ∈ colored),
        phi e = some (chooseColor e he) := by
      intro e he
      exact Classical.choose_spec (Finset.mem_filter.mp he).2.2
    symm
    apply Finset.card_bij chooseColor
    · intro e he
      simp [PresentColors]
      exact ⟨e, (Finset.mem_filter.mp he).2.1, choose_spec e he⟩
    · intro e1 h1 e2 h2 heq
      by_contra hne
      have hi1 := (Finset.mem_filter.mp h1).2.1
      have hi2 := (Finset.mem_filter.mp h2).2.1
      have hadj : AdjacentEdges G e1 e2 := ⟨v, hi1, hi2⟩
      have hp := hproper hne hadj (choose_spec e1 h1)
      exact hp (by simpa [heq] using choose_spec e2 h2)
    · intro c hc
      simp [PresentColors] at hc
      obtain ⟨e, he, hce⟩ := hc
      have heColored : e ∈ colored := by
        simp [colored]
        exact ⟨he, c, hce⟩
      refine ⟨e, heColored, ?_⟩
      exact Option.some.inj ((choose_spec e heColored).symm.trans hce)
  have colored_card : forall v,
      (Finset.univ.filter fun e =>
        Incident G v e ∧ exists c, phi e = some c).card =
      if Incident G v e0 then Degree G v - 1 else Degree G v := by
    intro v
    have hset : (Finset.univ.filter fun e =>
        Incident G v e ∧ exists c, phi e = some c) =
        (Finset.univ.filter fun e => Incident G v e).filter
          (fun e => e ≠ e0) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [colored_iff v e]
    rw [hset]
    by_cases hv : Incident G v e0
    · have hmem : e0 ∈ Finset.univ.filter (fun e => Incident G v e) := by
        simp [hv]
      rw [Finset.filter_ne', Finset.card_erase_of_mem hmem]
      simp [Degree, hv]
    · have hnot : e0 ∉ Finset.univ.filter (fun e => Incident G v e) := by
        simp [hv]
      rw [Finset.filter_ne', Finset.erase_eq_self.mpr hnot]
      simp [Degree, hv]
  have missing_two : forall v, Incident G v e0 ->
      2 <= (MissingColors G phi v).card := by
    intro v hv0
    have hdeg : Degree G v <= MaximumDegree G := by
      change Degree G v <=
        (insert 0 (Finset.univ.image (fun w => Degree G w))).max' _
      exact Finset.le_max' _ _
        (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨v, by simp, rfl⟩))
    have hmissing : (MissingColors G phi v).card =
        k - (Degree G v - 1) := by
      calc
        (MissingColors G phi v).card =
            k - (PresentColors G phi v).card := by
              simp [MissingColors, Finset.card_sdiff]
        _ = k - (Degree G v - 1) := by
          rw [present_card v, colored_card v, if_pos hv0]
    have hdegpos : 0 < Degree G v := by
      unfold Degree
      exact Finset.card_pos.mpr ⟨e0, by simp [hv0]⟩
    rw [hmissing]
    omega
  have hxMissingA : MissingColors G phi x ⊆ TreeMissingColors phi A := by
    intro c hc
    rw [TreeMissingColors]
    exact Finset.mem_biUnion.mpr ⟨x, hxA, hc⟩
  have hxMissingB : MissingColors G phi x ⊆ TreeMissingColors phi B := by
    intro c hc
    rw [TreeMissingColors]
    exact Finset.mem_biUnion.mpr ⟨x, hxB, hc⟩
  have hyMissingA : MissingColors G phi y ⊆ TreeMissingColors phi A := by
    intro c hc
    rw [TreeMissingColors]
    exact Finset.mem_biUnion.mpr ⟨y, hyA, hc⟩
  have hyMissingB : MissingColors G phi y ⊆ TreeMissingColors phi B := by
    intro c hc
    rw [TreeMissingColors]
    exact Finset.mem_biUnion.mpr ⟨y, hyB, hc⟩
  have hxyDisjoint : Disjoint (MissingColors G phi x) (MissingColors G phi y) := by
    apply helem
    · exact Finset.mem_union_left _ hxA
    · exact Finset.mem_union_left _ hyA
    · exact hxy
  let C := MissingColors G phi x ∪ MissingColors G phi y
  have hCsubset : C ⊆ TreeMissingColors phi A ∩ TreeMissingColors phi B := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact Finset.mem_inter.mpr ⟨hxMissingA hc, hxMissingB hc⟩
    · exact Finset.mem_inter.mpr ⟨hyMissingA hc, hyMissingB hc⟩
  have hCcard : 4 <= C.card := by
    rw [Finset.card_union_of_disjoint hxyDisjoint]
    exact Nat.add_le_add (missing_two x hx0) (missing_two y hy0)
  exact hCcard.trans (Finset.card_le_card hCsubset)
