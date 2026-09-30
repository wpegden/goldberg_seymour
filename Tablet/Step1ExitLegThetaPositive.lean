import Tablet.ColoredVertexSetElementary
import Tablet.GoodHierarchy
import Tablet.HierarchyStarredStage
import Tablet.HierarchyStoredColorsCardinality
import Tablet.HierarchyStoredColorsAt
import Tablet.HierarchyTerminalStoredColors
import Tablet.OrderedTreeUnion
import Tablet.Step1ExitLegMinimum
import Tablet.Step1ExitLegPresentation
import Tablet.TashkinovHierarchy
import Tablet.TreeColorSetMinusClosed
import Tablet.TreeMissingColors
import Tablet.TreeSequenceInitialSegment

-- [TABLET NODE: Step1ExitLegThetaPositive]
lemma Step1ExitLegThetaPositive {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (n q : ℕ)
    (M : Step1ExitLegMinimum G k e0 n q)
    (hpositive : 0 < M.selected.hierarchy.dividerCount) :
    ∃ theta : Fin k,
      theta ≠ M.selected.a ∧ theta ≠ M.selected.b ∧
      theta ∈ TreeMissingColors M.selected.phi
        (HierarchyStarredStage M.selected.hierarchy
          (Fin.last M.selected.hierarchy.dividerCount)) ∧
      TreeColorSetClosed G M.selected.phi
        (HierarchyStarredStage M.selected.hierarchy
          (Fin.last M.selected.hierarchy.dividerCount)) {theta} ∧
      TreeColorSetClosed G M.selected.phi M.selected.T {theta} := by
-- BODY
  classical
  have missing_mono : ∀ (S R : TreeSequence G e0),
      TreeSequenceInitialSegment S R →
        TreeMissingColors M.selected.phi S ⊆
          TreeMissingColors M.selected.phi R := by
    intro S R h c hc
    simp only [TreeMissingColors, Finset.mem_biUnion] at hc ⊢
    rcases hc with ⟨v, hv, hcv⟩
    rcases h with ⟨hlen, heq, hedge⟩
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hv ⊢
    rcases hv with ⟨i, rfl⟩
    refine ⟨R.vertex (Fin.castLE (Nat.succ_le_succ hlen) i), ?_, ?_⟩
    · exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i, rfl⟩
    · simpa [heq i] using hcv
  let H := M.selected.hierarchy
  let d := H.dividerCount
  have hd : 1 ≤ d := by
    dsimp [d]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpositive)
  have segment_trans : ∀ {S R W : TreeSequence G e0},
      TreeSequenceInitialSegment S R → TreeSequenceInitialSegment R W →
        TreeSequenceInitialSegment S W := by
    intro S R W hSR hRW
    rcases hSR with ⟨u, hfirst⟩
    rcases hfirst with ⟨hu, he⟩
    rcases hRW with ⟨v, hsecond⟩
    rcases hsecond with ⟨hv, hw⟩
    have htotal : S.length ≤ W.length := by omega
    refine ⟨htotal, ?_, ?_⟩
    · intro z
      have hz := hu z
      have hz' := hv (Fin.castLE (Nat.succ_le_succ u) z)
      calc
        W.vertex (Fin.castLE (Nat.succ_le_succ htotal) z) =
            W.vertex (Fin.castLE (Nat.succ_le_succ v)
              (Fin.castLE (Nat.succ_le_succ u) z)) := by
                congr 1
        _ = R.vertex (Fin.castLE (Nat.succ_le_succ u) z) := hz'
        _ = S.vertex z := hz
    · intro z
      have hz := hw (Fin.castLE u z)
      calc
        W.edge (Fin.castLE htotal z) =
            W.edge (Fin.castLE v (Fin.castLE u z)) := by
              congr 1
        _ = R.edge (Fin.castLE u z) := hz
        _ = S.edge z := he z
  have stage_chain : ∀ (r : ℕ) (hr : r ≤ d + 1),
      TreeSequenceInitialSegment (H.stage 0)
      (H.stage ⟨r, by omega⟩) := by
    intro r hr
    induction r with
    | zero => exact ⟨Nat.le_refl _, by simp, by simp⟩
    | succ r ih =>
        change r + 1 ≤ H.dividerCount + 1 at hr
        change TreeSequenceInitialSegment (H.stage 0)
          (H.stage ⟨r + 1, by omega⟩)
        exact segment_trans (ih (by omega))
          (H.nested ⟨r, by omega⟩)
  let i : Fin H.dividerCount := ⟨H.dividerCount - 1, by omega⟩
  have last_split : Fin.last H.dividerCount =
      (Fin.cast (by omega) (Fin.last (H.dividerCount - 1))).succ := by
    apply Fin.ext
    change H.dividerCount = (H.dividerCount - 1) + 1
    omega
  have star_eq : HierarchyStarredStage H (Fin.last d) =
      H.stage i.succ.castSucc := by
    dsimp [d]
    unfold HierarchyStarredStage
    rw [last_split]
    simp only [Fin.cases_succ]
    congr 1
  have old_to_star : TreeSequenceInitialSegment (H.stage i.castSucc.castSucc)
      (H.stage i.succ.castSucc) := by
    convert H.nested i.castSucc using 1 <;> congr 1 <;> apply Fin.ext <;> rfl
  have prev_to_star : TreeSequenceInitialSegment
      (HierarchyStarredStage H i.castSucc) (H.stage i.succ.castSucc) := by
    by_cases hdone : H.dividerCount = 1
    · have hiz : i = Fin.mk 0 (by omega) := by
        apply Fin.ext
        simp [i, hdone]
      subst i
      simpa [HierarchyStarredStage, hdone] using H.coreInsideFirst
    · have hiz : i.castSucc ≠ 0 := by
        intro hz
        have : H.dividerCount = 1 := by
          have hi := i.isLt
          simp [i] at hz
          omega
        exact hdone this
      have hstar : HierarchyStarredStage H i.castSucc =
          H.stage i.castSucc.castSucc := by
        unfold HierarchyStarredStage
        generalize hj : i.castSucc = j
        have hjz : j ≠ 0 := by
          intro hz
          apply hiz
          exact hj.trans hz
        cases j using Fin.cases with
        | zero => exact False.elim (hjz rfl)
        | succ l =>
          congr 1
      rw [hstar]
      exact H.nested i.castSucc
  have base_to_old : TreeSequenceInitialSegment
      (M.selected.ett.series.data.tree
        (Fin.last M.selected.ett.rounds).castSucc) (H.stage i.castSucc.castSucc) := by
    rw [← H.baseStage]
    exact stage_chain (d - 1) (by omega)
  have star_to_terminal : TreeSequenceInitialSegment
      (H.stage i.succ.castSucc) M.selected.T := by
    have hend : H.stage (Fin.last (H.dividerCount + 1)) = M.selected.T :=
      H.terminalStage
    have hindex : i.succ.succ = Fin.last (H.dividerCount + 1) := by
      apply Fin.ext
      simp [i]
      omega
    have hn := H.nested i.succ
    convert hn using 1
    · calc
        M.selected.T = H.stage (Fin.last (H.dividerCount + 1)) := hend.symm
        _ = H.stage i.succ.succ := congrArg H.stage hindex.symm
  let stored : Finset (Fin k) :=
    HierarchyStoredColorsAt H i.succ
  let excluded : Finset (Fin k) :=
    stored.biUnion (M.selected.good.gamma i.castSucc)
  have stored_card : stored.card ≤ M.selected.ett.rounds := by
    simpa [stored] using HierarchyStoredColorsCardinality H i.succ
  have stored_old : stored ⊆ HierarchyStoredColorsAt H i.castSucc := by
    intro eta heta
    simp only [stored, HierarchyStoredColorsAt, Finset.mem_sdiff] at heta ⊢
    exact ⟨heta.1, fun hm => heta.2 (missing_mono
      (HierarchyStarredStage H i.castSucc) (H.stage i.succ.castSucc)
        prev_to_star hm)⟩
  have excluded_card : excluded.card ≤ 2 * M.selected.ett.rounds := by
    calc
      excluded.card ≤ Finset.sum stored (fun eta =>
        (M.selected.good.gamma i.castSucc eta).card) :=
        Finset.card_biUnion_le
      _ = Finset.sum stored (fun _ => 2) := by
        apply Finset.sum_congr rfl
        intro eta heta
        exact M.selected.good.twoColors i.castSucc eta (stored_old heta)
      _ = 2 * stored.card := by simp [Nat.mul_comm]
      _ ≤ 2 * M.selected.ett.rounds := Nat.mul_le_mul_left 2 stored_card
  let forbidden : Finset (Fin k) := {M.selected.a, M.selected.b} ∪ excluded
  have forbidden_card : forbidden.card ≤ 2 + 2 * M.selected.ett.rounds := by
    have hu := Finset.card_union_le ({M.selected.a, M.selected.b} : Finset (Fin k)) excluded
    have hp : ({M.selected.a, M.selected.b} : Finset (Fin k)).card ≤ 2 :=
      Finset.card_le_two
    dsimp [forbidden] at *
    omega
  let trunk := M.selected.ett.series.data.tree
      (Fin.last M.selected.ett.rounds).castSucc
  have trunk_large : 2 * M.selected.ett.rounds + 11 ≤ (TreeMissingColors M.selected.phi trunk).card := by
    simpa [trunk, H] using M.selected.large
  have choice_nonempty : (TreeMissingColors M.selected.phi trunk \ forbidden).Nonempty := by
    by_contra hn
    have he : TreeMissingColors M.selected.phi trunk \ forbidden = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hn
    have hs : TreeMissingColors M.selected.phi trunk ⊆ forbidden := by
      intro c hc
      by_contra hcf
      have : c ∈ TreeMissingColors M.selected.phi trunk \ forbidden :=
        Finset.mem_sdiff.mpr ⟨hc, hcf⟩
      rw [he] at this
      simpa using this
    have hc := Finset.card_le_card hs
    omega
  obtain ⟨theta, htheta⟩ := choice_nonempty
  have theta_trunk : theta ∈ TreeMissingColors M.selected.phi trunk :=
    Finset.mem_sdiff.mp htheta |>.1
  have theta_forbidden : theta ∉ forbidden :=
    Finset.mem_sdiff.mp htheta |>.2
  have theta_a : theta ≠ M.selected.a := by
    intro h
    apply theta_forbidden
    simp [forbidden, h]
  have theta_b : theta ≠ M.selected.b := by
    intro h
    apply theta_forbidden
    simp [forbidden, h]
  have theta_old : theta ∉ excluded := by
    intro h
    apply theta_forbidden
    exact Finset.mem_union_right _ h
  have theta_star : theta ∈ TreeMissingColors M.selected.phi
      (HierarchyStarredStage H (Fin.last d)) := by
    rw [star_eq]
    apply missing_mono (H.stage i.castSucc.castSucc)
      (H.stage i.succ.castSucc) old_to_star
    apply missing_mono trunk (H.stage i.castSucc.castSucc)
      base_to_old
    exact theta_trunk
  have theta_closed_star : TreeColorSetClosed G M.selected.phi
      (HierarchyStarredStage H (Fin.last d)) {theta} := by
    rw [star_eq]
    have hm := M.selected.good.minusClosed i
    unfold TreeColorSetMinusClosed at hm
    rw [star_eq] at theta_star
    intro alpha halpha
    have ha : alpha = theta := Finset.mem_singleton.mp halpha
    subst alpha
    apply hm theta
    simp only [Finset.mem_sdiff]
    exact ⟨theta_star, by simpa [excluded, stored] using theta_old⟩
  have terminal_subset : HierarchyTerminalStoredColors H ⊆ stored := by
    intro eta heta
    simp only [HierarchyTerminalStoredColors, Finset.mem_sdiff] at heta
    dsimp [stored]
    simp only [HierarchyStoredColorsAt, Finset.mem_sdiff]
    refine ⟨heta.1, ?_⟩
    intro hm
    apply heta.2
    apply missing_mono (HierarchyStarredStage H i.succ) M.selected.T
      star_to_terminal
    exact hm
  have vertex_subset : ∀ {A B : TreeSequence G e0},
      TreeSequenceInitialSegment A B →
        TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro A B h v hv
    rcases h with ⟨hlen, heq, hedge⟩
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hv ⊢
    rcases hv with ⟨j, rfl⟩
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) j, heq j⟩
  have old_to_prev : TreeSequenceInitialSegment
      (H.stage i.castSucc.castSucc) (HierarchyStarredStage H i.castSucc) := by
    by_cases hone : H.dividerCount = 1
    · have hiz : i = Fin.mk 0 (by omega) := by
        apply Fin.ext
        simp [i, hone]
      subst i
      simp [HierarchyStarredStage, hone]
      rw [H.baseStage]
      by_cases hkind : M.selected.ett.series.data.kind
          (Fin.last M.selected.ett.rounds) =
          some TashkinovExtensionKind.PE
      · rcases M.selected.base.parallel hkind with
          ⟨_, _, ⟨hunite⟩⟩
        exact hunite.leftSegment
      · have hcore := M.selected.base.nonparallel hkind
        rw [hcore]
        exact ⟨Nat.le_refl _, (fun _ => rfl), (fun _ => rfl)⟩
    · have hiz : i.castSucc ≠ 0 := by
        intro hz
        have : H.dividerCount = 1 := by
          have hi := i.isLt
          simp [i] at hz
          omega
        exact hone this
      have hstar : HierarchyStarredStage H i.castSucc =
          H.stage i.castSucc.castSucc := by
        unfold HierarchyStarredStage
        generalize hj : i.castSucc = j
        have hjz : j ≠ 0 := by
          intro hz
          exact hiz (hj.trans hz)
        cases j using Fin.cases with
        | zero => exact False.elim (hjz rfl)
        | succ l => congr 1
      rw [hstar]
      exact ⟨Nat.le_refl _, by simp, by simp⟩
  obtain ⟨refreshed, refreshed_data, refreshed_unique⟩ :=
    M.selected.good.uniqueRefresh i
  rcases refreshed_data with ⟨refreshed_mem, refreshed_sub, unchanged⟩
  refine ⟨theta, theta_a, theta_b, theta_star, theta_closed_star, ?_⟩
  unfold TreeColorSetClosed
  intro alpha halpha
  have ha : alpha = theta := Finset.mem_singleton.mp halpha
  subst alpha
  apply M.selected.terminalMinusClosed theta
  simp only [Finset.mem_sdiff]
  refine ⟨?_, ?_⟩
  · apply missing_mono (H.stage i.succ.castSucc) M.selected.T
      star_to_terminal
    rw [← star_eq]
    exact theta_star
  · intro hbad
    rcases Finset.mem_biUnion.mp hbad with ⟨eta, heta, hgamma⟩
    have hstored : eta ∈ stored := terminal_subset heta
    have level_eq : i.succ = Fin.last H.dividerCount := by
      apply Fin.ext
      simp [i]
      omega
    rw [← level_eq] at hgamma
    by_cases heq : eta = refreshed
    · subst eta
      rcases Finset.mem_biUnion.mp (refreshed_sub hgamma) with ⟨v, hv, hvtheta⟩
      rcases Finset.mem_sdiff.mp hv with ⟨hvA, hvold⟩
      rcases Finset.mem_biUnion.mp theta_trunk with ⟨u, hu, hutheta⟩
      have hnot : u ≠ v := by
        intro huv
        subst v
        exact hvold (by
          apply vertex_subset old_to_prev
          apply vertex_subset base_to_old
          exact hu)
      have old_to_terminal :=
        segment_trans (segment_trans base_to_old old_to_star) star_to_terminal
      have hdj : Disjoint (MissingColors G M.selected.phi u)
          (MissingColors G M.selected.phi v) :=
        M.elementary (vertex_subset old_to_terminal hu)
          (vertex_subset star_to_terminal hvA) hnot
      exact Finset.disjoint_left.1 hdj hutheta hvtheta
    · have he := unchanged eta hstored heq
      apply theta_old
      apply Finset.mem_biUnion.mpr
      exact ⟨eta, hstored, he ▸ hgamma⟩
