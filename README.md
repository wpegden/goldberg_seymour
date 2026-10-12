# Goldberg–Seymour in Lean

This repository contains a Lean formalization of the Goldberg–Seymour bound for finite loopless multigraphs (parallel edges are allowed):

$$\chi'(G) \le \max\{\Delta(G)+1,\lceil\Gamma(G)\rceil\}.$$

Here $\chi'(G)$ is the chromatic index, $\Delta(G)$ the maximum degree, and $\Gamma(G)$ the maximum of $2|E(U)|/(|U|-1)$ over odd vertex sets of size at least three, with value zero when there are none.

The root theorem is [`ThmGS`](Tablet/ThmGS.lean), imported by [`Tablet.lean`](Tablet.lean):

```lean
theorem ThmGS {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) :
    ChromaticIndex G ≤ max (MaximumDegree G + 1) (DensityCeil G)
```

## Target and paper

The reference is Guantao Chen, Guangming Jing and Wenan Zang, *Proof of the Goldberg-Seymour Conjecture on Edge-Colorings of Multigraphs*, [arXiv:1901.10316v2](https://arxiv.org/abs/1901.10316v2), revised 7 June 2022.

[`paper/paper.tex`](paper/paper.tex) identifies itself as a rechecked editorial working version based on that paper, **not an author-issued revision**. The two explicitly included companion references, [`scheide.tex`](paper/refs/scheide.tex) and [`edge_coloring_book.tex`](paper/refs/edge_coloring_book.tex), identify themselves as ChatGPT-prepared mathematical notes. The pinned source has no `GOAL.md`; the target above is taken from the actual root declaration and paper, rather than a reconstructed goal document.

## Status and provenance

The formalization was produced with **Trellis**, which organizes mathematical statements, natural-language proofs and Lean proofs into a dependency graph and coordinates their development and review. Each `Tablet/*.lean` file has a corresponding mathematical `Tablet/*.tex` document. The exported criteria documents describe correspondence, paper-faithfulness, soundness and substantiveness.

This snapshot is pinned to source commit `3ce0b531835cb02062083703e4b04d0fd10e6f13`, checkpoint `005759`, cycle 921, in the `Cleanup` phase. The source's generated node summary reports 683/683 nodes closed. Cleanup remains in progress, and further cleanup commits will follow. That source status is separate from the independent Lean build and root-axiom check used for publication.

An independent isolated `lake build` passed for the pinned Lean sources. The root check `#print axioms ThmGS` reports exactly `[propext, Classical.choice, Quot.sound]`. There are no custom axioms or `sorryAx` in the root dependency closure. The complete final export is also checked against the scratch sources before publication.

## Reproduce the Lean check

The exact pins are:

- Lean: `leanprover/lean4:v4.33.0` in [`lean-toolchain`](lean-toolchain).
- mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d` in [`lakefile.lean`](lakefile.lean).
- Transitive dependency commits are recorded in [`lake-manifest.json`](lake-manifest.json).

With the pinned Lean toolchain available, run from the repository root:

```sh
lake exe cache get
lake build
printf 'import Tablet\n#print ThmGS\n#print axioms ThmGS\n' > /tmp/GoldbergSeymourAxioms.lean
lake env lean /tmp/GoldbergSeymourAxioms.lean
```

[`APPROVED_AXIOMS.json`](APPROVED_AXIOMS.json) approves no project-specific axioms: both its global list and per-node map are empty. The publication check requires the root's axioms to be confined to Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with no `sorryAx` or custom axiom. Kernel checking establishes the exported Lean statement; the accompanying mathematical criteria are not additional axioms.

## History and updates

The initial history selects the last checkpoint by ancestry in each of 890 represented cycles spanning cycles 1–921, preserving the source author date, then adds a final pinned-head snapshot and this README. Missing cycle numbers are not fabricated. Legacy checkpoints without an active node are labelled `unspecified`; a repeated checkpoint number within cycle 232 is resolved by ancestry. Historical snapshots record development and are not asserted to build or be complete.

Published cycle commits are permanent. A checkpoint added later within an already published cycle is represented in a new final-head snapshot; its old cycle commit is preserved. Newly seen cycles append their latest checkpoints as of the next freeze, followed by another final-head snapshot. Unchanged reruns add no commits. This permits continuing cleanup updates without rewriting public history. Export mappings and validation receipts are retained outside this repository.

## License

**TODO: select a license.** No repository license has been selected or added.
