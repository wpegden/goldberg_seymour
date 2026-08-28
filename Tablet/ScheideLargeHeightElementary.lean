import Tablet.Critical
import Tablet.Elementary
import Tablet.GlobalMaximumTriple
import Tablet.GlobalMaximumTripleExists
import Tablet.Incident
import Tablet.MaximumDegree
import Tablet.NormalGlobalMaximumTriple
import Tablet.ScheideBalancedExists
import Tablet.ScheideGlobalMaximumOrder
import Tablet.ScheideGraphHeight
import Tablet.ScheideGraphHeightOdd
import Tablet.ScheideLargeHeightFullTrunk
import Tablet.ScheideLargeHeightOneTailPair
import Tablet.TashkinovOrder
import Tablet.TreeSequence

-- [TABLET NODE: ScheideLargeHeightElementary]
theorem ScheideLargeHeightElementary {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ)
    (hcritical : Critical G) (hindex : ChromaticIndex G = k + 1)
    (hdegree : MaximumDegree G + 1 ≤ k)
    (hnoisolated : ∀ v : V, ∃ e : E, Incident G v e)
    (hlarge : TashkinovOrder G - 4 < ScheideGraphHeight G) :
    Elementary G := by
-- BODY
  classical
  letI : DecidableEq V := Classical.decEq V
  obtain ⟨e0, phi, T, hglobal⟩ :=
    GlobalMaximumTripleExists G k hcritical hindex hdegree
  obtain ⟨e1, psi, S, N, hbalanced⟩ :=
    ScheideBalancedExists G k e0 phi T hglobal
  have hcard : (TreeSequenceVertexSet S).card = S.length + 1 := by
    unfold TreeSequenceVertexSet
    rw [Finset.card_image_of_injective Finset.univ S.vertex_injective]
    simp
  have hheight_le : ScheideGraphHeight G ≤ TashkinovOrder G := by
    calc
      ScheideGraphHeight G = N.height := hbalanced.1.symm
      _ ≤ S.length + 1 := N.height_upper
      _ = (TreeSequenceVertexSet S).card := hcard.symm
      _ = TashkinovOrder G := N.global.2.2
  have hheight_odd : Odd (ScheideGraphHeight G) :=
    (ScheideGraphHeightOdd G k e0 phi T hglobal).2
  have horder_odd : Odd (TashkinovOrder G) :=
    N.global.2.2 ▸
      (ScheideGlobalMaximumOrder G k e1 psi S N.global).2.2.1
  rcases hheight_odd with ⟨a, ha⟩
  rcases horder_odd with ⟨b, hb⟩
  have hcases : ScheideGraphHeight G = TashkinovOrder G ∨
      ScheideGraphHeight G + 2 = TashkinovOrder G := by
    omega
  rcases hcases with heq | heq
  · exact ScheideLargeHeightFullTrunk G k e1 psi S N hbalanced
      hnoisolated heq
  · exact ScheideLargeHeightOneTailPair G k e1 psi S N hbalanced
      hnoisolated heq
