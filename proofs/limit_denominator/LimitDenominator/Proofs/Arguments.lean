module

/-!
The arguments to the `limitDenominator` algorithm, and the two special forms of input:
the trivial case and the ambiguous case.
-/

/--
The arguments to `limitDenominator` comprise a (possibly non-reduced) fraction `m/n`
with `n` positive, along with the positive denominator limit.
-/
public structure Arguments where
  /-- Numerator of the fraction to be approximated. -/
  m : Int
  /-- Denominator of the fraction to be approximated. -/
  n : Int
  /-- Upper bound on the denominator of the approximation. -/
  limit : Int
  n_pos : 0 < n
  one_le_limit : 1 ≤ limit

namespace Arguments

/- We fix arguments `args` throughout this section. -/
variable (args : Arguments)

/--
We say a set of arguments is *trivial* if the target is in lowest terms with its
denominator already within the limit.
-/
@[expose] public def trivial := Int.gcd args.m args.n = 1 ∧ args.n ≤ args.limit

/--
We say a set of arguments is *ambiguous* if the limit is `1` and `m/n` is a
half-integer, that is, `m/n = w + 1/2` for some integer `w`.
-/
@[expose] public def ambiguous :=
  args.limit = 1 ∧ ∃ (w : Int), 2 * args.m = (2 * w + 1) * args.n

/-- If `m/n = w + 1/2` then `⌊m/n⌋ = w`. -/
public theorem floor_eq_of_half_integer {w : Int}
    (hw : 2 * args.m = (2 * w + 1) * args.n) : args.m / args.n = w :=
  (Int.ediv_eq_iff_of_pos args.n_pos).mpr (by grind only [args.n_pos])

end Arguments
