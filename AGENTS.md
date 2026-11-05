# Katamaran: instructions for coding agents

## Building

A full build takes a long time.

- Git worktrees are optional. If you use one, **restore its build** before
  the first build: `scripts/build-cache`. It takes the compiled files of the
  closest existing build (other worktrees, snapshots, CI's builds on cachix)
  for the sources that match, and fixes mtimes so `make` rebuilds only what
  differs.
  Plain copying doesn't work, because checked-out `.v` files are newer than
  the copied `.vo` files. Run it again after a rebase, checkout or stash:
  they give unchanged `.v` files new mtimes too.
- **Build with `scripts/worktree/build [TARGET.vo...]`**, as a background
  command, and wait for the notification. Don't sleep or poll. It prints a
  summary or the first errors. The full log is `build.log` in the worktree's
  git directory; `grep` it rather than reading it whole.
- Build only the targets you need. Do the full build once, at the end.

## Working efficiently

- Read large files (e.g. `Bitvector.v`) by range: locate with `git grep -n`,
  then read only that part. Don't reread unchanged files.
- Use `git grep`, not `grep -r`, which also searches `.vo` and `.glob` files.
- Keep Rocq output small: narrow `Search` queries, look at one goal at a time.
- Step through proofs with the `rocq` MCP tools rather than recompiling the
  file after each attempt.
- Use subagents only for independent work, and point them at exact files and
  line ranges.

## Changing `theories/Bitvector.v`

Almost everything depends on `Bitvector.v`, so editing it forces a long
rebuild. Instead:

1. Put new work in `theories/BitvectorNext.v`, in `Module bvnext`, importing
   `Katamaran.Bitvector`. Add the file to `_CoqProject` after `Bitvector.v`.
2. Develop and test it there.
3. When done, move it into the `bv` module in `Bitvector.v`, rename `bvnext.`
   uses to `bv.`, delete `BitvectorNext.v` and its `_CoqProject` entry, and do
   one full rebuild.

Don't merge a branch that still contains `BitvectorNext.v`.

## Bitvectors: use `bv.unsigned`, not `bv.bin`

- `bv.bin` is internal to `Bitvector.v`. Elsewhere, state things with
  `bv.unsigned` or `bv.signed` in `Z`. Existing `bv.bin` uses elsewhere are to
  be removed, not copied.
- Don't unfold `bv.unsigned`, `bv.signed`, `bv.ule`, `bv.uleb` etc.; that
  exposes `bv.bin`. Use lemmas such as `bv.uleb_ule`, `bv.uleb_ugt`,
  `bv.ule_iff_unsigned_le` (and `ult`/`ugt`/`uge`) and
  `bv.unsigned_add_small`. Add missing lemmas to `Bitvector.v` (via
  `BitvectorNext.v`).
- Factor recurring proof steps into lemmas.
- `cbn`/`simpl` can expand a width like `xlenbits` inside `bv.unsigned`, so
  `lia` sees different atoms. Avoid `simpl`, or use
  `change (bv.unsigned x) with (@bv.unsigned xlenbits x) in *`.

## Type classes

- When you add or touch a `Class`, give it a mode with the `#[mode="…"]`
  attribute, e.g. `#[mode="- + +"] Class …`, and drop any separate
  `Hint Mode` line for it. Leave the attribute out only if every argument is
  `-`, which is the default.

## Case studies

- `examples/GVT` has copies of some RiscvPmp lemmas; keep them in sync.

## Reporting

When done, say which cases were not straightforward and what you deliberately
left unchanged, and why.
