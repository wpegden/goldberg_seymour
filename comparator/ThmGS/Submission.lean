import ChallengeDeps
import Submission.ThmGS

namespace Submission

theorem ThmGS {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) :
    ChromaticIndex G ≤ max (MaximumDegree G + 1) (DensityCeil G) := by
  exact _root_.Tablet.ThmGS G

end Submission
