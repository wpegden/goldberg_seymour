import Tablet.TashTreeSuffixIterate
import Tablet.TashTreeSuffixTerminalReplacement

-- [TABLET NODE: TashTreeCaseRepeatedOnPath]
theorem TashTreeCaseRepeatedOnPath {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hbefore : TashTreePathIndex G T < T.length)
    (hrepeat : ∃ alpha : Fin k, ∃ i : Fin (T.length + 1),
      TashTreePathIndex G T ≤ i.val ∧ i.val < T.length ∧
      alpha ∈ MissingColors G phi (T.vertex i) ∧
      alpha ∈ MissingColors G phi (T.vertex (Fin.last T.length))) : False := by
-- BODY
  rcases hrepeat with ⟨beta, i, hiSuffix, hiLength, hi, hlast⟩
  let i' : Fin T.length := Fin.castLT i hiLength
  have hiCast : i'.castSucc = i := by
    apply Fin.ext
    rfl
  have hi' : beta ∈ MissingColors G phi (T.vertex i'.castSucc) := by
    rw [hiCast]
    exact hi
  have hiSuffix' : TashTreePathIndex G T ≤ i'.val := by
    simpa [i'] using hiSuffix
  obtain ⟨psi, p, hp, hpSuffix, hminPsi, hprev, hlastPsi⟩ :=
    TashTreeSuffixIterate G k e0 phi T hmin beta i' hiSuffix' hi' hlast
  have hlen : 2 ≤ T.length := by
    omega
  obtain ⟨_hpos, _hle, _delta, _j, _psiStar, _hdelta, _hjlt,
      _hmissing, _hformula, hbad, hrank⟩ :=
    TashTreeSuffixTerminalReplacement G k e0 psi T hminPsi hlen beta p
      hpSuffix hp hprev hlastPsi
  exact (hminPsi.2 hbad) hrank
