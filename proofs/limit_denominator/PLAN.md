# What's next

Both listings are now translated, specified, proved, tested and documented.
[README.md](README.md) and [PROOF.md](PROOF.md) are the canonical documents, and everything
this file used to say about the work now lives in one of them, in a docstring, or in the proof
itself. What is left here is the one piece of work still to do.

## A command-line executable

isqrt has one (`lake exe isqrt N`), and the shape would be the same here: take `m n l`, print
`r/s`, and lean on the correctness proof to omit handling for the impossible exception case. It
would add a `lean_exe` to [`lakefile.toml`](lakefile.toml), a `Main.lean`, and a section to
README.md.

One thing to settle while building it: the tie to the theorem is weaker than isqrt's, because
isqrt's executable can be cross-checked in the kernel by `rfl` on a concrete input and a
`while` translation cannot. So the executable and the proved function need to be visibly the
same function by construction — sharing the definition rather than agreeing by inspection —
since nothing in the build will catch a divergence.
