# Comparator

A comparator check takes a prescribed statement of a theorem and a submitted
proof, and confirms that the proof proves exactly that statement using no axiom
outside `propext`, `Quot.sound` and `Classical.choice`, by replaying the proof
term through the Lean kernel.

`ThmGS/` is the comparator workspace for the main theorem:

- `Challenge.lean` — the prescribed statement of `ThmGS`; its proof is `sorry`.
- `ChallengeDeps.lean` — the definitions the statement is written over: exactly
  the 16 declarations in the kernel-recorded semantic closure of `ThmGS`
  (`../semantic-closure.json`), copied byte for byte from `Tablet/`, and nothing
  else.
- `Solution.lean`, `Submission.lean` — the bridge that discharges the prescribed
  statement from this repository's proof by `exact`.
- `config.json`, `lakefile.toml`, `lean-toolchain`, `WorkspaceTest.lean` —
  workspace configuration.

## Which commits were checked

Each checked commit carries a tag of the form `comparator-checked-cycle-<N>`:

    git tag -l 'comparator-checked-*'

A tag asserts that at that commit the comparator accepted the proof of `ThmGS`.
Cleanup continues past a checked commit, so the tip of the repository may be
ahead of the most recent tag.

## Rebuilding the workspace

`Submission/` is not committed because it is a mechanical copy of `Tablet/`:
copy `Tablet/*.lean` into `ThmGS/Submission/`, rewriting `import Tablet.` to
`import Submission.`; replace the body of each of the 16 files whose declaration
is already in `ChallengeDeps.lean` with `import ChallengeDeps`, so that each
declaration exists once; and wrap `Submission/ThmGS.lean` in
`namespace Tablet ... end Tablet`. Then, from `ThmGS/`, build the four libraries
and run the comparator on `config.json`.
