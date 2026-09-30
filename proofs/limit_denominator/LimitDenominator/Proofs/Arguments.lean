module

/-!
The arguments to the `limitDenominator` algorithm.
-/

/--
The arguments to `limitDenominator` comprise a (possibly reducible) target fraction
`m/n` with `n` positive, along with the positive denominator limit.
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
