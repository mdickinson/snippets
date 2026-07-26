# Open proposals

Both listings are now translated, specified, proved, tested and documented.
[README.md](README.md) and [PROOF.md](PROOF.md) are the canonical documents, and everything
this file used to say about the work now lives in one of them, in a docstring, or in the proof
itself. What is left here is what has been proposed and not agreed.

## A command-line executable

isqrt has one (`lake exe isqrt N`), and the shape would be the same here: take `m n l`, print
`r/s`, and lean on the correctness proof to omit handling for the impossible exception case. It
would add a `lean_exe` to [`lakefile.toml`](lakefile.toml), a `Main.lean`, and a section to
README.md. The tie to the theorem is weaker than isqrt's, though: isqrt's executable can be
cross-checked in the kernel by `rfl` on a concrete input, and a `while` translation cannot be.

## A fraction structure in the proof layer

A structure bundling numerator, denominator, `0 < den` and `gcd num den = 1`, with a
`limitDenominator` on it built from the `Int`-level function together with
`isCorrectLimitDenominator_stdlib` to discharge the coprimality field — `_from_coprime_ints`'s
informal "trust me" replaced by the proof, at no cost to the trusted layer.

This is not the bundled *definition* that README.md § Scope rejects. That one would have put a
coprimality proof into `Definitions`; this one lives above the theorem and uses it.
