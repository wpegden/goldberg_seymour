import Tablet.OrderedTreeUnion

-- [TABLET NODE: OrderedTreeUnionExists]
theorem OrderedTreeUnionExists
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    {G : LooplessMultigraph V E} {e0 : E}
    (A B : TreeSequence G e0) :
    exists U : TreeSequence G e0, Nonempty (OrderedTreeUnion A B U) := by
-- BODY
  classical
  let originalDecidable : DecidableEq V := inferInstance
  letI : DecidableEq V := Classical.decEq V
  let appendStep : ∀ (T : TreeSequence G e0) (f : E) (v : V)
      (i : Fin (T.length + 1)),
      G.ends f = s(v, T.vertex i) →
      v ∉ TreeSequenceVertexSet T →
      (∀ j : Fin T.length, f ≠ T.edge j) → TreeSequence G e0 := by
    intro T f v i hi hv hf
    let U : TreeSequence G e0 :=
      { length := T.length + 1
        positive := by omega
        vertex := Fin.lastCases v (fun j => T.vertex j)
        edge := Fin.lastCases f (fun j => T.edge j)
        vertex_injective := by
          intro a b hab
          revert b
          refine Fin.lastCases ?_ (fun a => ?_) a
          · intro b
            refine Fin.lastCases ?_ (fun b => ?_) b
            · intro h
              apply Fin.ext
              rfl
            · intro h
              dsimp only [Fin.lastCases] at h
              rw [Fin.reverseInduction_last, Fin.reverseInduction_castSucc] at h
              have hm : T.vertex b ∈ TreeSequenceVertexSet T := by
                simp [TreeSequenceVertexSet]
              exact (hv (h ▸ hm)).elim
          · intro b
            refine Fin.lastCases ?_ (fun b => ?_) b
            · intro h
              dsimp only [Fin.lastCases] at h
              rw [Fin.reverseInduction_castSucc, Fin.reverseInduction_last] at h
              have hm : T.vertex a ∈ TreeSequenceVertexSet T := by
                simp [TreeSequenceVertexSet]
              exact (hv (h ▸ hm)).elim
            · intro h
              dsimp only [Fin.lastCases] at h
              rw [Fin.reverseInduction_castSucc, Fin.reverseInduction_castSucc] at h
              exact congrArg Fin.castSucc (T.vertex_injective h)
        edge_injective := by
          intro a b hab
          revert b
          refine Fin.lastCases ?_ (fun a => ?_) a
          · intro b
            refine Fin.lastCases ?_ (fun b => ?_) b
            · intro h
              rfl
            · intro h
              dsimp only [Fin.lastCases] at h
              rw [Fin.reverseInduction_last, Fin.reverseInduction_castSucc] at h
              exact (hf b h).elim
          · intro b
            refine Fin.lastCases ?_ (fun b => ?_) b
            · intro h
              dsimp only [Fin.lastCases] at h
              rw [Fin.reverseInduction_castSucc, Fin.reverseInduction_last] at h
              exact (hf a h.symm).elim
            · intro h
              dsimp only [Fin.lastCases] at h
              rw [Fin.reverseInduction_castSucc, Fin.reverseInduction_castSucc] at h
              exact congrArg Fin.castSucc (T.edge_injective h)
        first_edge := by
          have hz : (⟨0, Nat.succ_pos _⟩ : Fin (T.length + 1)) =
              (⟨0, T.positive⟩ : Fin T.length).castSucc := by rfl
          rw [hz]
          simp only [Fin.lastCases, Fin.reverseInduction_castSucc]
          exact T.first_edge
        attaches := by
          intro j
          by_cases hj : j = Fin.last T.length
          · subst j
            refine ⟨i, ?_⟩
            have hc : (Fin.castLT i (by omega) : Fin (T.length + 1 + 1)) = i.castSucc := by
              apply Fin.ext
              rfl
            rw [hc]
            simp only [Fin.lastCases, Fin.reverseInduction_last,
              Fin.reverseInduction_castSucc]
            rw [hi]
            simpa [Fin.lastCases] using hi
          · have hlast : (Fin.last T.length).val = T.length := by rfl
            have hj' : j.val < T.length := by omega
            obtain ⟨q, hq⟩ := T.attaches (j.castPred hj)
            have hform : j = (j.castPred hj).castSucc := by
              apply Fin.ext
              rfl
            have hle : (j.castPred hj).val + 1 ≤ j.val + 1 := by
              simp
            refine ⟨Fin.castLE hle q, ?_⟩
            convert hq using 1
            · apply congrArg G.ends
              conv_lhs => rw [hform]
              simp only [Fin.lastCases, Fin.reverseInduction_castSucc]
            · apply (Sym2.eq_iff).2
              left
              constructor
              · have hjs : j.succ = (j.castPred hj).succ.castSucc := by
                  apply Fin.ext
                  rfl
                rw [hjs]
                simp only [Fin.lastCases, Fin.reverseInduction_castSucc]
              · have hq' : q.val < T.length + 1 := by omega
                have heq : (Fin.castLE hle q).castLT (by omega) =
                    (q.castLT hq').castSucc := by
                  apply Fin.ext
                  rfl
                rw [heq]
                simp only [Fin.lastCases, Fin.reverseInduction_castSucc] }
    exact U
  have vertex_in_set : ∀ (T : TreeSequence G e0) (i : Fin (T.length + 1)),
      T.vertex i ∈ TreeSequenceVertexSet T := by
    intro T i
    simp [TreeSequenceVertexSet]
  have hA2 : 1 < A.length + 1 := by
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) (Nat.succ_le_succ A.positive)
  have hB2 : 1 < B.length + 1 := by
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) (Nat.succ_le_succ B.positive)
  have first_in_left : B.vertex ⟨0, Nat.zero_lt_succ B.length⟩ ∈ TreeSequenceVertexSet A := by
    obtain ⟨i, hi⟩ := B.attaches ⟨0, B.positive⟩
    have hi0 : i = ⟨0, Nat.zero_lt_succ _⟩ := Fin.eq_zero i
    subst i
    rw [B.first_edge] at hi
    obtain ⟨j, hj⟩ := A.attaches ⟨0, A.positive⟩
    have hj0 : j = ⟨0, Nat.zero_lt_succ _⟩ := Fin.eq_zero j
    subst j
    rw [A.first_edge] at hj
    have hm : B.vertex ⟨0, Nat.zero_lt_succ B.length⟩ ∈ G.ends e0 := by
      rw [hi]
      exact (Sym2.mem_iff).2 (Or.inr rfl)
    rw [hj] at hm
    rcases Sym2.mem_iff.mp hm with hm | hm
    · refine Finset.mem_image.mpr ⟨⟨1, hA2⟩, Finset.mem_univ _, ?_⟩
      convert hm.symm using 1
      exact congrArg A.vertex (by apply Fin.ext; rfl)
    · refine Finset.mem_image.mpr ⟨⟨0, Nat.zero_lt_succ _⟩, Finset.mem_univ _, ?_⟩
      convert hm.symm using 1
      exact congrArg A.vertex (by apply Fin.ext; rfl)
  have first_next_in_left : B.vertex ⟨1, hB2⟩ ∈
      TreeSequenceVertexSet A := by
    obtain ⟨i, hi⟩ := B.attaches ⟨0, B.positive⟩
    have hi0 : i = ⟨0, Nat.zero_lt_succ _⟩ := Fin.eq_zero i
    subst i
    rw [B.first_edge] at hi
    obtain ⟨j, hj⟩ := A.attaches ⟨0, A.positive⟩
    have hj0 : j = ⟨0, Nat.zero_lt_succ _⟩ := Fin.eq_zero j
    subst j
    rw [A.first_edge] at hj
    have hm : B.vertex ⟨1, hB2⟩ ∈ G.ends e0 := by
      rw [hi]
      simp
    rw [hj] at hm
    rcases Sym2.mem_iff.mp hm with hm | hm
    · refine Finset.mem_image.mpr ⟨⟨1, hA2⟩, Finset.mem_univ _, ?_⟩
      convert hm.symm using 1
      exact congrArg A.vertex (by apply Fin.ext; rfl)
    · refine Finset.mem_image.mpr ⟨⟨0, Nat.zero_lt_succ _⟩, Finset.mem_univ _, ?_⟩
      exact hm.symm
  let Good : ℕ → TreeSequence G e0 → Prop := fun n T =>
    TreeSequenceInitialSegment A T ∧
    (∀ i : Fin (B.length + 1), i.val ≤ n → B.vertex i ∈ TreeSequenceVertexSet T) ∧
    TreeSequenceVertexSet T ⊆ TreeSequenceVertexSet A ∪ TreeSequenceVertexSet B ∧
    (∀ j : Fin T.length, A.length ≤ j.val →
      ∃ i : Fin B.length, i.val < n ∧
        T.edge j = B.edge i ∧ T.vertex j.succ = B.vertex i.succ) ∧
    (∀ i : Fin B.length, i.val < n → B.vertex i.succ ∉ TreeSequenceVertexSet A →
      ∃ j : Fin T.length, A.length ≤ j.val ∧
        T.edge j = B.edge i ∧ T.vertex j.succ = B.vertex i.succ) ∧
    (∀ i j : Fin B.length, i.val < n → j.val < n →
      B.vertex i.succ ∉ TreeSequenceVertexSet A →
      B.vertex j.succ ∉ TreeSequenceVertexSet A → i.val < j.val →
      ∀ p q : Fin T.length, T.vertex p.succ = B.vertex i.succ →
      T.vertex q.succ = B.vertex j.succ → p.val < q.val)
  have process : ∀ n : ℕ, n ≤ B.length → ∃ T : TreeSequence G e0, Good n T := by
    intro n
    induction n with
    | zero =>
        intro hn
        refine ⟨A, ?_⟩
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · refine ⟨le_rfl, ?_, ?_⟩
          · intro i
            rfl
          · intro j
            rfl
        · intro i hi
          have hi0 : i.val = 0 := by omega
          have heq : i = ⟨0, by omega⟩ := by apply Fin.ext; exact hi0
          rw [heq]
          exact first_in_left
        · intro x hx
          exact Finset.mem_union_left _ hx
        · intro j hj
          have hj' := j.isLt
          omega
        · intro i hi hout
          omega
        · intro i j hi hj ho1 ho2 hlt
          omega
    | succ n ih =>
        intro hn
        obtain ⟨T, hT⟩ := ih (by omega)
        by_cases hout : B.vertex ⟨n + 1, Nat.lt_succ_of_le hn⟩ ∈ TreeSequenceVertexSet A
        · refine ⟨T, ?_⟩
          rcases hT with ⟨hseg, hall, hsub, hnew, hcov, hord⟩
          refine ⟨hseg, ?_, hsub, ?_, ?_, ?_⟩
          · intro i hi
            by_cases hil : i.val ≤ n
            · exact hall i (by omega)
            · have heq : i = ⟨n + 1, Nat.lt_succ_of_le hn⟩ := by
                apply Fin.ext
                have hil' : n < i.val := Nat.lt_of_not_ge hil
                change i.val = n + 1
                omega
              rw [heq]
              have hleft : B.vertex ⟨n + 1, Nat.lt_succ_of_le hn⟩ ∈ TreeSequenceVertexSet T := by
                rcases hseg with ⟨hlen, hv, he⟩
                simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
                  true_and] at hout ⊢
                obtain ⟨k, hk⟩ := hout
                refine ⟨Fin.castLE (Nat.succ_le_succ hlen) k, ?_⟩
                rw [hv k]
                exact hk
              exact hleft
          · intro j hj
            obtain ⟨k, hk, he, hv⟩ := hnew j hj
            exact ⟨k, by omega, he, hv⟩
          · intro i hi ho
            by_cases hil : i.val < n
            · exact hcov i hil ho
            · have heq : i.succ = ⟨n + 1, Nat.lt_succ_of_le hn⟩ := by
                apply Fin.ext
                change i.val + 1 = n + 1
                omega
              exact (ho (heq ▸ hout)).elim
          · intro i j hi hj ho1 ho2 hlt
            have hil : i.val < n := by
              by_contra hni
              have heq : i.succ = ⟨n + 1, Nat.lt_succ_of_le hn⟩ := by
                apply Fin.ext
                change i.val + 1 = n + 1
                omega
              exact (ho1 (heq ▸ hout)).elim
            have hjl : j.val < n := by
              by_contra hnj
              have heq : j.succ = ⟨n + 1, Nat.lt_succ_of_le hn⟩ := by
                apply Fin.ext
                change j.val + 1 = n + 1
                omega
              exact (ho2 (heq ▸ hout)).elim
            exact hord i j hil hjl ho1 ho2 hlt
        · rcases hT with ⟨hseg, hall, hsub, hnew, hcov, hord⟩
          let k : Fin B.length := ⟨n, by omega⟩
          obtain ⟨i, hi⟩ := B.attaches k
          have hiBound : (i : ℕ) ≤ n := by
            have hiSmall := Nat.le_of_lt_succ i.isLt
            simpa [k] using hiSmall
          let iB : Fin (B.length + 1) := ⟨i.val, by omega⟩
          have hiAll : B.vertex iB ∈ TreeSequenceVertexSet T := by
            apply hall iB
            exact hiBound
          have iBForm : iB = i.castLT (by omega) := by
            apply Fin.ext
            rfl
          simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
            true_and] at hiAll
          obtain ⟨q, hq⟩ := hiAll
          have hattach : G.ends (B.edge k) =
              s(B.vertex k.succ, T.vertex q) := by
            rw [hi, ← iBForm, hq]
          have hnewv : B.vertex k.succ ∉ TreeSequenceVertexSet T := by
            intro hv
            simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
              true_and] at hv
            obtain ⟨r, hr⟩ := hv
            by_cases hold : r.val ≤ A.length
            · rcases hseg with ⟨hlen, hvertices, hedges⟩
              apply hout
              let rA : Fin (A.length + 1) := r.castLT (by omega)
              refine Finset.mem_image.mpr ⟨rA,
                Finset.mem_univ _, ?_⟩
              have ridx : Fin.castLE (Nat.succ_le_succ hlen) rA = r := by
                apply Fin.ext
                rfl
              rw [← hvertices rA, ridx]
              exact hr
            · by_cases rz : r.val = 0
              · rcases hseg with ⟨hlen, hvertices, hedges⟩
                apply hout
                refine Finset.mem_image.mpr ⟨⟨0, Nat.zero_lt_succ _⟩,
                  Finset.mem_univ _, ?_⟩
                rw [← hvertices (⟨0, Nat.zero_lt_succ _⟩ : Fin (A.length + 1))]
                have rr : r = ⟨0, Nat.zero_lt_succ _⟩ := by apply Fin.ext; exact rz
                rw [rr] at hr
                exact hr
              · have rz' : r ≠ 0 := by
                  intro hrz
                  apply rz
                  simpa [hrz]
                let j := r.pred rz'
                have rpos : 1 ≤ r.val := by
                  apply Nat.one_le_iff_ne_zero.mpr
                  intro hrzero
                  apply rz
                  exact hrzero
                have jform : j.val + 1 = r.val := by
                  dsimp [j]
                  exact Nat.sub_add_cancel rpos
                obtain ⟨z, hz, he, hvz⟩ := hnew j (by omega)
                have hrj : T.vertex j.succ = B.vertex k.succ := by
                  calc
                    T.vertex j.succ = T.vertex r := by
                      congr 1
                      apply Fin.ext
                      simp [j]
                    _ = B.vertex k.succ := hr
                have zedge : B.vertex z.succ = B.vertex k.succ := hvz.symm.trans hrj
                have zsucc : z.succ = k.succ := B.vertex_injective zedge
                have zval : z.val + 1 = k.val + 1 := congrArg Fin.val zsucc
                have zk : z = k := by
                  apply Fin.ext
                  exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using zval)
                have zkval : z.val = k.val := congrArg Fin.val zk
                have kval : k.val = n := rfl
                omega
          have hedge : ∀ j : Fin T.length, B.edge k ≠ T.edge j := by
            intro j he
            obtain ⟨r, hr⟩ := T.attaches j
            have hv : B.vertex k.succ ∈ TreeSequenceVertexSet T := by
              have hm : B.vertex k.succ ∈ G.ends (T.edge j) := by
                rw [← he, hi]
                exact (Sym2.mem_iff).2 (Or.inl rfl)
              rw [hr] at hm
              rcases Sym2.mem_iff.mp hm with hm | hm
              · rw [hm]
                exact vertex_in_set T j.succ
              · rw [hm]
                exact vertex_in_set T (Fin.castLT r (by omega))
            exact (hnewv hv).elim
          let S := appendStep T (B.edge k) (B.vertex k.succ) q hattach hnewv hedge
          have oldVertex : ∀ r : Fin (T.length + 1),
              S.vertex r.castSucc = T.vertex r := by
            intro r
            simp [S, appendStep, Fin.reverseInduction_castSucc]
          have oldEdge : ∀ r : Fin T.length,
              S.edge r.castSucc = T.edge r := by
            intro r
            simp [S, appendStep, Fin.reverseInduction_castSucc]
          have newVertex : S.vertex (Fin.last (T.length + 1)) = B.vertex k.succ := by
            simp [S, appendStep]
          have newEdge : S.edge (Fin.last T.length) = B.edge k := by
            simp [S, appendStep]
          refine ⟨S, ?_⟩
          dsimp [S, appendStep]
          rcases hseg with ⟨hlenT, hvT, heT⟩
          constructor
          · have hlen' : A.length ≤ T.length + 1 := by omega
            refine ⟨by omega, ?_, ?_⟩
            · intro i
              have hi : (Fin.castLE (Nat.succ_le_succ (by omega : A.length ≤ T.length + 1)) i) =
                  (Fin.castLE (Nat.succ_le_succ hlenT) i).castSucc := by
                apply Fin.ext
                rfl
              rw [hi]
              exact oldVertex _ |>.trans (hvT i)
            · intro i
              have hi : (Fin.castLE (by omega : A.length ≤ T.length + 1) i) =
                  (Fin.castLE hlenT i).castSucc := by
                apply Fin.ext
                rfl
              rw [hi]
              exact oldEdge _ |>.trans (heT i)
          constructor
          · intro i hi
            by_cases hold : i.val ≤ n
            · have hm := hall i hold
              simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
                true_and] at hm
              obtain ⟨q, hq⟩ := hm
              apply Finset.mem_image.mpr
              refine ⟨⟨q.val, Nat.lt.step q.isLt⟩, Finset.mem_univ _, ?_⟩
              have hqi : (⟨q.val, by omega⟩ : Fin (T.length + 2)) = q.castSucc := by
                apply Fin.ext
                rfl
              rw [hqi]
              exact (oldVertex q).trans hq
            · have hi' : i = ⟨n + 1, by omega⟩ := by
                apply Fin.ext
                have hle : i.val ≤ n + 1 := hi
                have hgt : n < i.val := Nat.lt_of_not_ge hold
                exact Nat.le_antisymm hle ((Nat.succ_le_iff).2 hgt)
              rw [hi']
              apply Finset.mem_image.mpr
              refine ⟨⟨T.length + 1, Nat.lt_succ_self _⟩, Finset.mem_univ _, ?_⟩
              have hi : (⟨T.length + 1, by omega⟩ : Fin (T.length + 2)) =
                  Fin.last (T.length + 1) := by apply Fin.ext; rfl
              rw [hi]
              exact newVertex
          constructor
          · intro x hx
            simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
              true_and] at hx
            obtain ⟨i, hi⟩ := hx
            by_cases hlt : i.val ≤ T.length
            · have hi' : (⟨i.val, by omega⟩ : Fin (T.length + 1)).castSucc = i := by
                apply Fin.ext
                rfl
              apply hsub
              let r : Fin (T.length + 1) := ⟨i.val, by omega⟩
              have hir : r.castSucc = i := by apply Fin.ext; rfl
              exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, by
                have hix := hi
                rw [← hir] at hix
                exact (oldVertex r).symm.trans hix⟩
            · have hi' : i = Fin.last (T.length + 1) := by
                apply Fin.ext
                simp only [Fin.last, Fin.val]
                omega
              rw [hi'] at hi
              apply Finset.mem_union_right _
              exact Finset.mem_image.mpr ⟨k.succ, Finset.mem_univ _, by
                simpa [newVertex] using hi⟩
          constructor
          · intro j hj
            by_cases hlt : j.val < T.length
            · let jT : Fin T.length := ⟨j.val, hlt⟩
              have hj' : j = jT.castSucc := by apply Fin.ext; rfl
              rw [hj']
              simp only [Fin.lastCases, Fin.reverseInduction_castSucc]
              obtain ⟨i, hi, he, hv⟩ := hnew jT (by omega)
              have hjs : jT.castSucc.succ = jT.succ.castSucc := by
                apply Fin.ext
                rfl
              rw [hjs]
              simp only [Fin.lastCases, Fin.reverseInduction_castSucc]
              exact ⟨i, by omega, he, hv⟩
            · have hj' : j = Fin.last T.length := by
                apply Fin.ext
                simp only [Fin.last, Fin.val]
                have hjlt : j.val < T.length + 1 := by simpa using j.isLt
                omega
              rw [hj']
              exact ⟨k, Nat.lt_succ_self _, newEdge, newVertex⟩
          constructor
          · intro i hi ho
            by_cases hlt : i.val < n
            · obtain ⟨j, hj, he, hv⟩ := hcov i hlt ho
              refine ⟨j.castSucc, (by simpa using hj), ?_, ?_⟩
              · simp only [Fin.lastCases, Fin.reverseInduction_castSucc]
                exact he
              · have hjs : j.castSucc.succ = j.succ.castSucc := by
                  apply Fin.ext
                  rfl
                rw [hjs]
                simp only [Fin.lastCases, Fin.reverseInduction_castSucc]
                exact hv
            · have hi' : i.val = n := by
                have hle : i.val ≤ n := by omega
                have hgt : n ≤ i.val := by omega
                exact Nat.le_antisymm hle hgt
              have hi'' : i = k := by apply Fin.ext; exact hi'
              subst i
              exact ⟨Fin.last T.length, (by simpa using hlenT), newEdge, newVertex⟩
          · intro i j hi hj hoi hoj hlt p q hp hq
            by_cases hpi : p.val < T.length
            · by_cases hqj : q.val < T.length
              · let pT : Fin T.length := ⟨p.val, hpi⟩
                let qT : Fin T.length := ⟨q.val, hqj⟩
                have pp : p = pT.castSucc := by apply Fin.ext; rfl
                have qq : q = qT.castSucc := by apply Fin.ext; rfl
                rw [pp] at hp
                rw [qq] at hq
                have hps : pT.castSucc.succ = pT.succ.castSucc := by
                  apply Fin.ext
                  rfl
                have hqs : qT.castSucc.succ = qT.succ.castSucc := by
                  apply Fin.ext
                  rfl
                rw [hps] at hp
                rw [hqs] at hq
                simp only [Fin.lastCases, Fin.reverseInduction_castSucc] at hp hq
                rw [pp, qq]
                have hiold : i.val < n := by
                  by_contra hn'
                  have hik : i = k := by apply Fin.ext; omega
                  subst i
                  apply hnewv
                  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
                    true_and]
                  exact ⟨pT.succ, hp⟩
                have hjold : j.val < n := by
                  by_contra hn'
                  have hjk : j = k := by
                    apply Fin.ext
                    have hjbound : j.val ≤ n := by omega
                    have hjlow : n ≤ j.val := by omega
                    exact Nat.le_antisymm hjbound hjlow
                  subst j
                  apply hnewv
                  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
                    true_and]
                  exact ⟨qT.succ, hq⟩
                exact hord i j hiold hjold hoi hoj hlt pT qT hp hq
              · have qq : q = Fin.last T.length := by
                  apply Fin.ext
                  simp only [Fin.last, Fin.val]
                  have hqbound : q.val < T.length + 1 := by simpa using q.isLt
                  omega
                rw [qq] at hq
                simp only [Fin.lastCases, Fin.reverseInduction_last] at hq
                rw [qq]
                omega
            · have pp : p = Fin.last T.length := by
                apply Fin.ext
                simp only [Fin.last, Fin.val]
                have hpbound : p.val < T.length + 1 := by simpa using p.isLt
                omega
              rw [pp] at hp
              simp only [Fin.lastCases, Fin.reverseInduction_last] at hp
              by_cases hqj : q.val < T.length
              · rw [pp]
                have hqbound : q.val < T.length := hqj
                have hpval : (Fin.last T.length).val = T.length := rfl
                have hpi' : B.vertex k.succ = B.vertex i.succ := by
                  simpa [S, appendStep] using hp
                have hik : k.succ = i.succ := B.vertex_injective hpi'
                have hikval : k.val = i.val :=
                  Nat.succ.inj (congrArg Fin.val hik)
                have hkn : k.val = n := rfl
                exfalso
                omega
              · have qq : q = Fin.last T.length := by
                  apply Fin.ext
                  simp only [Fin.last, Fin.val]
                  have hqbound : q.val < T.length + 1 := by simpa using q.isLt
                  omega
                rw [qq] at hq
                simp only [Fin.lastCases, Fin.reverseInduction_last] at hq
                have hp' : B.vertex k.succ = B.vertex i.succ := by
                  simpa [S, appendStep] using hp
                have hq' : B.vertex k.succ = B.vertex j.succ := by
                  simpa [S, appendStep] using hq
                have hki : k.succ = i.succ := by
                  apply B.vertex_injective
                  exact hp'
                have hkj : k.succ = j.succ := by
                  apply B.vertex_injective
                  exact hq'
                have hij : i = j := by
                  apply Fin.ext
                  exact Nat.succ.inj (congrArg Fin.val (hki.symm.trans hkj))
                omega
  obtain ⟨U, hU⟩ := process B.length (le_rfl)
  letI : DecidableEq V := originalDecidable
  refine ⟨U, ⟨?_⟩⟩
  rcases hU with ⟨hleft, hvertices, hsub, hnewentries, hcoverage, horder⟩
  rcases hleft with ⟨hlen, hv, he⟩
  have vertex_mem_iff : ∀ (T : TreeSequence G e0) (x : V),
      x ∈ TreeSequenceVertexSet T ↔ ∃ i : Fin (T.length + 1), T.vertex i = x := by
    intro T x
    simp [TreeSequenceVertexSet]
  exact
    { leftSegment := ⟨hlen, hv, he⟩
      vertexSet := by
        apply Finset.Subset.antisymm
        · intro x hx
          have hx' := hsub hx
          simpa only [Finset.mem_union] using hx'
        · intro x hx
          rcases Finset.mem_union.mp hx with hx | hx
          · obtain ⟨i, hi⟩ := (vertex_mem_iff A x).mp hx
            apply (vertex_mem_iff U x).mpr
            exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i, (hv i).trans hi⟩
          ·
            obtain ⟨i, hi⟩ := (vertex_mem_iff B x).mp hx
            have him := hvertices i (Nat.le_of_lt_succ i.isLt)
            rw [hi] at him
            exact him
      newEntryFromRight := by
        intro j hj
        obtain ⟨i, _, he', hv'⟩ := hnewentries j hj
        exact ⟨i, he', hv'⟩
      everyNewRightEntry := by
        intro i hi
        obtain ⟨j, hj, he, hv⟩ := hcoverage i (by omega) hi
        exact ⟨j, hj, he, hv⟩
      rightOrder := by
        intro i j hi hj hlt
        exact horder i j (by omega) (by omega) hi hj hlt }
