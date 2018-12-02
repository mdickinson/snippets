/-

This file provides a formal proof of correctness of the recursive integer
square root algorithm presented in isqrt.py.

We use the "Lean" Theorem Prover, which can be obtained from:

    https://leanprover.github.io

This proof was verified using version 3.4.1 of Lean. After installing Lean,
you can run the verification yourself from a command line using:

    lean isqrt_lean

On a successful verification, this will produce no output.

-/

/-

For reference, here's the Python code that we'll translate into Lean.

    def isqrt_aux(b, n):
        """
        Recursive approximate integer sqrt.

        Given a positive integer n, and the number b of base-4 digits of n,
        return an integer close to the square root of n.

        It can be proved that for n > 0, (a - 1)**2 < n < (a + 1)**2.
        """
        if b < 2:
            return b
        else:
            k = b >> 1
            a = isqrt_aux(b - k, n >> 2 * k)
            return (a << k - 1) + (n >> k + 1) // a


    def size4(n):
        """ Number of base-4 digits of n. """
        return (1 + n.bit_length()) // 2


    def isqrt(n):
        """ Largest a satisfying a * a <= n. """
        if n < 0:
            raise ValueError("Square root of negative number")

        a = isqrt_aux(size4(n), n)
        return a if a * a <= n else a - 1

-/



/-
  Introduce notation for left and right shifts, so that we
  can make the Lean code look more like Python code.
-/

reserve infix ` << `:60
reserve infix ` >> `:60

notation n >> k := nat.shiftr n k
notation n << k := nat.shiftl n k

/- Definition of the isqrt function -/

section isqrt

/- Lemma used to show that the recursive call in isqrt_aux terminates. -/
lemma isqrt_aux_wf (c : ℕ) : c + 2 - (c + 2 >> 1) < c + 2 :=
begin
  apply nat.sub_lt,
  { show 0 < c + 2, apply nat.zero_lt_succ },
  {
    rw nat.shiftr_eq_div_pow,
    change 0 < (c + 2) / 2 ^ 1 with 1 ≤ (c + 2) / 2,
    rw nat.le_div_iff_mul_le,
    apply nat.le_add_left,
    repeat {constructor},
  }
end

/- Given a natural number n together with b, the number of base 4
   digits of n, if n = 0 return 0; otherwise, return
   a value a satisfying (a - 1)^2 < n < (a + 1)^2 -/
def isqrt_aux : ℕ → ℕ → ℕ
| 0 n := 0
| 1 n := 1
| b@(c+2) n :=
    let k := b >> 1 in
    let a := have b - k < b, from isqrt_aux_wf c,
             isqrt_aux (b - k) (n >> 2 * k) in
    (a << k - 1) + (n >> k + 1) / a

/- Number of base-4 digits of n -/
def size4 (n : ℕ) := (1 + nat.size n) / 2

/- Given n, return the largest natural number a satisfying
   a * a <= n. -/
def isqrt (n : ℕ) :=
  let a := isqrt_aux (size4 n) n in
  if a * a <= n then a else a - 1

/-

Before we embark on the formal proof, we give some comments and an informal
proof.

Informal proof
--------------

Notation. Our informal proof uses a blend of Python syntax, Lean syntax, and
ordinary mathematical notation. We write // for the floor division operation
(the floor of the true quotient). This is the same as Lean's "/" operator on ℕ,
or Python's "//" on int. We'll write / for normal mathematical division on
real numbers. ^ represents exponentiation, and √ is the usual real square root.

The expression isqrt_aux (size4 n) n gives an approximation to the square root
of n.  We'll show by strong induction on n that the result of isqrt_aux differs
from the true root by less than 1. That is, if d = isqrt_aux (size4 n) n then
assuming 0 < n, (d - 1)^2 < n < (d + 1)^2. The correctness of isqrt follows.

For n < 4, the result can be verified directly by case-by-case computation.
For n ≥ 4, the isqrt_aux definition enters the recursive call. Define:

    k = size4 n // 2
    m = n // 4^k
    a = isqrt_aux (size4 m) m

then unwinding the definitions in isqrt_aux, the return value of
isqrt_aux (size4 n) n is

    (1)  d = 2^(k-1) a + n // 2^(k+1) // a

The induction hypothesis allows us to assume that a is within 1 of the
square root of m:

    (2)  (a - 1)^2 < m < (a + 1)^2

and we must deduce that (d - 1)^2 < n < (d + 1)^2.

Unfolding the definition of m in (2), (a - 1)^2 < n // 4^k < (a + 1)^2. Since
(a + 1)^2 is an integer, it follows that n / 4^k < (a + 1)^2, so we can replace
floor division with true division and (2) implies the (slightly weaker, but
sufficient for our purposes) statement:

    (3)  (a - 1)^2 < n / 4^k < (a + 1)^2

Taking square roots in (3) and rearranging gives

    (4)  abs(√n - 2^k a) < 2^k

Define the real number e by:

    (5)  e = 2^(k-1) a + n / (2^(k+1) a)

And note for future use that:

    (6)  d = floor(e)

Now:

    (7)  e - √n = ( 2^(k-1) a + n / (2^(k+1) a) - √n )
                = ( 2^(2k) a^2 + n - 2^(k+1) a √n ) / (2^(k+1) a)
                = ( √n - 2^k a )^2 / (2^(k+1) a)

Using the bound on abs(√n - 2^k a) in (4), and noting that the quantity
on the right-hand side of (7) is nonnegative, we have

    (8)  0 ≤ e - √n < 2^(2k) / (2^(k+1) a)

To complete the proof we need a lower bound on a. We have 4^(size4 n - 1) ≤ n
and 2k ≤ size4 n, by the definitions of size4 and k respectively. So:

    (9)  4^(2k - 1) ≤ 4^(size4 n - 1) ≤ n

Dividing both sizes by 4^k and combining with the right-hand-side of (3),

    (10)  4^(k - 1) < (a + 1)^2

Taking square roots gives 2^(k - 1) < (a + 1), or equivalently, since 2^(k-1)
and a are both integers,

    (11)  2^(k - 1) ≤ a

Combining this with (8) gives

    (12)  0 ≤ e - √n < 1

Finally, using that d = floor(e) (from (6)), it follows that

    (13)  -1 < d - √n < 1

which gives (d - 1)^2 < n < (d + 1)^2, as required. ∎


Notes on the formal proof
-------------------------

The informal proof would normally be considered to be a proof over the field
ℝ of real numbers, though it suffices to work in the subfield ℚ[√n], which has
the advantage (from the point of view of giving a constructive proof) that
equality is decidable. However, it requires some work to set up the machinery
to work in ℚ[√n] or ℤ[√n] in Lean, and to pass between the various domains
as required.

An alternative approach is to work entirely within the domain of the natural
numbers, and this is what we do below, avoiding even use of ℤ. This necessarily
complicates some aspects of the proof. For comparison, we may at some point
construct the more natural proof, working in ℚ[√n].

-/


/- Random easy-to-prove facts -/

-- it's surprising how often a proof by contradiction below ends
-- with a proof of 0 < 0.

lemma zero_lt_zero (P : Prop) (h : 0 < 0) : P := by cases h

/- Goals of 0 < 2 and 0 < 4 come up often enough to be worth encapsulating. -/

lemma nat.two_pos : 0 < 2 := by repeat {constructor}
lemma nat.four_pos : 0 < 4 := by repeat {constructor}

/- logical negations, used with mt to generate the contrapositive
   of a statement. -/

lemma le_iff_not_lt {m n : ℕ} : m ≤ n ↔ ¬ (n < m) := begin
  split,
  {
    intros m_le_n n_lt_m, apply nat.lt_irrefl n,
    apply nat.lt_of_lt_of_le n_lt_m m_le_n
  },
  {
    cases nat.lt_or_ge n m with n_lt_m m_le_n; intro,
    { contradiction }, { exact m_le_n }
  }
end

lemma lt_iff_not_le {m n : ℕ} : m < n ↔ ¬ (n ≤ m) := begin
  split,
  {
    intros m_lt_n n_le_m, apply nat.lt_irrefl n,
    apply nat.lt_of_le_of_lt n_le_m m_lt_n
  },
  {
    cases nat.lt_or_ge m n with m_lt_n n_le_m; intro,
    { exact m_lt_n }, { contradiction }
  }
end


lemma pos_iff_nonzero (n : ℕ) : 0 < n ↔ n ≠ 0 := begin
  split,
  { intros n_pos n_zero, apply zero_lt_zero, rw n_zero at n_pos, exact n_pos },
  { intro n_nonzero, cases nat.eq_zero_or_pos n with n_zero n_pos,
    { contradiction }, { exact n_pos }
  }
end


lemma le_iff_succ_lt (x y : ℕ) : x ≤ y ↔ x < y + 1 :=
begin
  split; intro h,
  apply nat.lt_succ_of_le h,
  apply nat.le_of_lt_succ h,
end


-- it's sometimes useful to split into cases a <= b and b <= a,
-- to be able to make use of symmetry

lemma le_or_ge (a b : ℕ) : a ≤ b ∨ b ≤ a :=
begin
  cases nat.lt_or_ge a b with hlt hge,
  { left, exact nat.le_of_lt hlt },
  { right, exact hge }
end

/- Galois connection for addition and subtraction in nat -/

lemma pred_le_iff_le_succ {a b : ℕ} : nat.pred a ≤ b ↔ a ≤ nat.succ b :=
begin
  split; intro h,
  { apply nat.le_succ_of_pred_le h },
  {
    cases a, { apply nat.zero_le },
    { rw nat.pred_succ, apply nat.le_of_succ_le_succ h }
  }
end


lemma sub_le_iff_le_add {a b c : ℕ} : a - c ≤ b ↔ a ≤ b + c :=
begin
  revert b, induction c with c IH; intro b, { refl },
  { -- case c > 0
    change a - nat.succ c with nat.pred (a - c),
    change b + nat.succ c with nat.succ (b + c),
    rw [pred_le_iff_le_succ, IH, nat.succ_add]
  }
end


lemma sub_lt_of_lt_add {a b c : ℕ} :
    0 < b → a < b + c → a - c < b :=
begin
  intros b_pos lt_add,
  cases nat.lt_or_ge a c with hlt hge,
  {
    have a_sub_c : a - c = 0,
    { apply nat.sub_eq_zero_of_le, apply nat.le_of_lt, exact hlt },
    rw a_sub_c, clear a_sub_c,
    exact b_pos,
  },
  {
    apply @nat.lt_of_add_lt_add_left c,
    rw nat.add_sub_of_le,
    rw add_comm,
    exact lt_add,
    exact hge
  }
end

lemma lt_add_of_sub_lt (a b c : ℕ):
  a - c < b → a < b + c :=
begin
  intro sub_lt,
  cases nat.lt_or_ge a c with hlt hge,
  {
    apply lt_of_lt_of_le hlt,
    apply nat.le_add_left
  },
  {
    have h1 : a = c + (a - c), { rw nat.add_sub_of_le, exact hge },
    rw h1,
    rw add_comm,
    apply add_lt_add_right,
    exact sub_lt
  }
end

/- result making use of those contrapositives -/

lemma lt_of_mul_lt_mul (a : ℕ) {b c : ℕ} : a * b < a * c → b < c :=
begin
  repeat {rw lt_iff_not_le}, apply mt, apply nat.mul_le_mul_left
end

/- can't find this one easily in the standard library, but it's probably
   there somewhere -/

lemma le_mul_of_pos {a b : ℕ} : 0 < b → a ≤ a * b := begin
  intro b_pos,
  have h : a * 1 ≤ a * b := nat.mul_le_mul_left a b_pos,
  rw mul_one at h, exact h
end


/- Some facts about nat.pow that seem to be missing from the standard library -/

lemma pow_two (a : ℕ) : a ^ 2 = a * a := by rw [nat.pow_succ, nat.pow_one]


lemma pow_mul_pow (a b c : ℕ) : a^(b + c) = a^b * a^c := begin
  induction c with c ih,
  {
    rw nat.add_zero,
    rw nat.pow_zero,
    symmetry,
    apply nat.mul_one,
   },
  {
    change a ^ (b + nat.succ c) with a ^ (b + c) * a,
    rw ih,
    change a ^ nat.succ c with a ^ c * a,
    apply nat.mul_assoc,
  },
end

lemma pow_assoc (a b c : ℕ) : (a^b)^c = a^(b*c) := begin
  induction c with c ih,
  { refl },
  {
    rw nat.pow_succ,
    rw ih,
    change b * nat.succ c with b * c + b,
    rw pow_mul_pow
  }
end

lemma mul_pow (a b c : ℕ) : (a * b)^c = a^c * b^c := begin
  induction c with c ih,
  {
    repeat {rw nat.pow_zero}, refl
  },
  {
    repeat {rw nat.pow_succ},
    rw ih,
    rw mul_assoc,
    rw mul_assoc,
    apply congr_arg,
    rw mul_comm,
    rw mul_assoc,
    apply congr_arg,
    apply mul_comm
  }
end


/- division-multiplication results, supplementing the main
   results nat.le_div_iff_mul_le and nat.div_lt_iff_lt_mul -/

lemma nat.mul_lt_of_lt_div {x y k : ℕ} :
  x < y / k → x * k < y :=
begin
  /- this is just the contrapositive of nat.div_le_of_le_mul -/
  rw [lt_iff_not_le, lt_iff_not_le], apply mt, rw mul_comm,
  apply nat.div_le_of_le_mul
end


lemma nat.sum_div_le_iff_le_mul {x y k} :
  0 < k → ((x + (k - 1)) / k ≤ y ↔ x ≤ y * k) :=
begin
  intro kpos,
  rw le_iff_succ_lt,
  rw nat.div_lt_iff_lt_mul _ _ kpos,
  rw add_mul,
  have h : 1 * k = (k - 1) + 1,
  {
    rw one_mul,
    symmetry,
    apply nat.sub_add_cancel kpos
  },
  rw [h, ←add_assoc, ←le_iff_succ_lt],
  apply nat.add_le_add_iff_le_right
end


/- squares and inequalities -/

lemma square_lt_square (a b : ℕ) : a < b → a^2 < b^2 :=
begin
  intro a_lt_b, simp [pow_two],
  have b_pos : 0 < b := nat.lt_of_le_of_lt (nat.zero_le a) a_lt_b,
  exact nat.lt_of_le_of_lt (nat.mul_le_mul_left a (nat.le_of_lt a_lt_b))
                           (nat.mul_lt_mul_of_pos_right a_lt_b b_pos)
end


lemma square_le_square (a b : ℕ) : a ≤ b → a^2 ≤ b^2 :=
begin
  intro a_le_b, simp [pow_two],
  exact nat.le_trans (nat.mul_le_mul_left a a_le_b)
                     (nat.mul_le_mul_right b a_le_b)
end


lemma lt_of_square_lt_square (a b : ℕ) : a^2 < b^2 → a < b :=
begin
  rw lt_iff_not_le,
  rw lt_iff_not_le,
  apply mt,
  apply square_le_square
end

lemma cauchy_schwarz (a b : nat) : 2*a*b ≤ a^2 + b^2 :=
begin
  repeat {rw pow_two},
  cases le_or_ge a b with a_le_b b_le_a,
  { -- a ≤ b
    let c := b - a,
    have hb : a + c = b, by apply nat.add_sub_of_le a_le_b,
    rw ← hb,
    rw [mul_add, mul_add, add_mul, add_mul],
    rw [two_mul, add_mul, add_mul],
    repeat {rw add_assoc},
    apply nat.add_le_add_left,
    apply nat.add_le_add_left,
    rw mul_comm,
    apply nat.add_le_add_left,
    apply nat.le_add_right
  },
  {
    let c := a - b,
    have ha : b + c = a, by apply nat.add_sub_of_le b_le_a,
    rw ← ha,
    rw two_mul,
    repeat {rw add_mul},
    repeat {rw mul_add},
    repeat {rw add_assoc},
    apply nat.add_le_add_left,
    rw mul_comm,
    apply nat.add_le_add_left,
    rw add_comm,
    apply nat.add_le_add_left,
    apply nat.le_add_left
  }
end


lemma square_add {a b : ℕ} : (a + b)^2 = a^2 + b^2 + 2*a*b :=
  by simp [pow_two, two_mul, add_mul, mul_add, mul_comm b a]


lemma abs_lt_sublemma {a b c : ℕ} : a ≤ b →
  b < a + c → a^2 + b^2 < c^2 + 2*a*b :=
begin
  /- replace b with a + d throughout -/
  intro a_le_b,
  let d := b - a,
  have bsubst : d + a = b := nat.sub_add_cancel a_le_b,
  rw ← bsubst, clear bsubst, clear a_le_b,

  /- now just a matter of simplification -/
  intro b_low,
  have lhs : a ^ 2 + (d + a) ^ 2 = d ^ 2 + 2 * a * (d + a), by
    simp [pow_two, two_mul, add_mul, mul_add, mul_comm d a],
  rw lhs, clear lhs,
  apply nat.add_lt_add_right,
  apply square_lt_square,
  rw add_comm at b_low,
  exact lt_of_add_lt_add_left b_low
end


lemma abs_lt {a b c : ℕ} : a < b + c → b < a + c →
  a^2 + b^2 < c^2 + 2*a*b :=
begin
  intros a_low b_low,
  cases le_or_ge a b with a_le_b b_le_a,
  { exact abs_lt_sublemma a_le_b b_low },
  { rw [add_comm, mul_assoc, mul_comm a b, ← mul_assoc],
    exact abs_lt_sublemma b_le_a a_low }
end


lemma am_gm (a b : ℕ) : 4*a*b ≤ (a + b)^2 :=
begin
  have rhs : (a + b)^2 = a*a + b*b + 2*a*b,
  {
    rw [pow_two, add_mul, mul_add, mul_add],
    repeat {rw add_assoc},
    apply congr_arg,
    symmetry,
    rw ← add_assoc,
    symmetry,
    rw add_comm,
    apply congr_arg,
    rw two_mul,
    rw add_mul,
    apply congr_arg,
    apply mul_comm
  },
  have lhs : 4 * a * b = 2 * a * b + 2 * a * b,
  {
    change 4 with 2 + 2,
    rw add_mul,
    rw add_mul
  },
  rw lhs, clear lhs,
  rw rhs, clear rhs,
  apply nat.add_le_add_right,
  repeat {rw ← pow_two},
  apply cauchy_schwarz
end


/- Conclusion is (c - b)^2 ≤ (c - a)^2, rearranged. -/

lemma squares_diffs {a b c : ℕ} : a ≤ b → b ≤ c →
  2*a*c + b^2 ≤ 2*b*c + a^2 :=
begin
  intros a_le_b b_le_c,
  have h1 : b = a + (b - a), {
    symmetry,
    apply nat.add_sub_of_le a_le_b,
  },
  rw h1,
  let d := b - a,
  change b - a with d,
  repeat {rw two_mul},
  repeat {rw pow_two},
  repeat {rw add_mul},
  repeat {rw mul_add},
  simp,
  apply nat.add_le_add_left,
  apply nat.add_le_add_left,
  apply nat.add_le_add_left,
  rw mul_comm,
  repeat {rw ← mul_add},
  apply nat.mul_le_mul_left,
  apply @nat.le_trans _ (a + c),
  apply nat.add_le_add_left,
  rw ← h1,
  apply b_le_c,
  apply nat.add_le_add_right,
  apply nat.le_trans a_le_b b_le_c
end


lemma more_squares {a b c : ℕ} :
  c ≤ a + b →
  (a + b + c)^2 < 4*a*b + 4*a*c + 4*b*c →
  (a + b - c)^2 < 4*a*b :=
begin
  intros c_bound hmain,
  let d := a + b - c,
  change a + b - c with d,
  have ab_cd : a + b = c + d, {
    symmetry, rw [add_comm, nat.sub_add_cancel c_bound]
  },
  have h2 : 4 * a * b + 4 * a * c + 4 * b * c = 4 * a * b + 4 * (c + d) * c,
  { rw [←ab_cd, mul_add, add_mul], simp },
  rw h2 at hmain, clear h2,
  have h2 : (a + b + c)^2 = d^2 + 4*(c + d)*c, {
    rw [ab_cd, pow_two, pow_two],
    change 4 with 2 * 2, rw two_mul,
    repeat {rw add_mul}, rw two_mul,
    repeat {rw mul_add}, repeat {rw add_mul},
    repeat {rw (mul_comm d c)},
    simp,
  },
  rw h2 at hmain, clear h2,
  apply lt_of_add_lt_add_right,
  exact hmain
end

section main_arithmetic_sublemma

/-

In this section we prove the main arithmetic sublemma, which
in turn will be used to prove the validity of the recursive step.

We'll show, roughly, that if a is an approximation to √n, with error
smaller than √(2a), then

    (a ^ 2 + n - 2 * a) ^ 2 < 4 * a ^ 2 * n

More precisely, we'll prove:

    main_arithmetic_sublemma : ∀ (n a b : ℕ),
      b ≤ a →
      (a - b) ^ 2 < n → n < (a + b) ^ 2 →
      b ^ 2 ≤ 2 * a → 2 * a ≤ a ^ 2 + n →
      (a ^ 2 + n - 2 * a) ^ 2 < 4 * a ^ 2 * n

-/

parameters {n a b : ℕ}
parameter b_le_a : b ≤ a
parameter n_lower : (a - b)^2 < n
parameter n_upper : n < (a + b)^2
parameter b_lower_a : b^2 ≤ 2*a
parameter a_lower : 2*a ≤ a^2 + n

include b_le_a n_lower n_upper b_lower_a a_lower

lemma b_lower : b^2 ≤ a^2 + n := nat.le_trans b_lower_a a_lower

lemma diff_bound1 : a^2 + b^2 < n + 2*a*b :=
begin
  let c := a - b,
  have a_subst : a = c + b, { symmetry, exact nat.sub_add_cancel b_le_a },
  change a - b with c at n_lower,
  rw a_subst,
  have lhs : (c + b) ^ 2 + b ^ 2 = c^2 + 2 * (c + b) * b, by
    simp [pow_two, two_mul, add_mul, mul_add, mul_comm c b],
  rw lhs, apply nat.add_lt_add_right n_lower
end

lemma diff_bound2 : n < a^2 + b^2 + 2*a*b :=
begin
  have rhs : a ^ 2 + b ^ 2 + 2 * a * b = (a + b)^2, by
    simp [pow_two, two_mul, add_mul, mul_add, mul_comm b a],
  rw rhs, exact n_upper
end

/- single inequality that captures the upper and lower bounds on n -/

lemma both_bounds : (a^2 + b^2 + n)^2 < 4*a^2*b^2 + 4*a^2*n + 4*b^2*n :=
begin
  have lhs :
    (a^2 + b^2 + n)^2 = (a ^ 2 + b ^ 2) ^ 2 + n ^ 2 + 2 * (a ^ 2 + b ^ 2) * n,
      by apply square_add,
  rw lhs, clear lhs,
  have rhs :
    4*a^2*b^2 + 4*a^2*n + 4*b^2*n =
          (2 * a * b) ^ 2 + 2 * (a ^ 2 + b ^ 2) * n + 2 * (a ^ 2 + b ^ 2) * n,
    {
      change 4 with 2 + 2,
      simp [pow_two, two_mul, add_mul, mul_add, mul_assoc, mul_comm b (a*b)],
    },
  rw rhs, clear rhs,
  apply add_lt_add_right,
  apply abs_lt,
  apply diff_bound1,
  apply diff_bound2
end


lemma main_arithmetic_sublemma_rhs : (a^2 + n - b^2)^2 < 4 * a^2 * n := begin
  apply more_squares b_lower,
  have lhs : a^2 + n + b^2 = a^2 + b^2 + n, by simp, rw lhs, clear lhs,
  have rhs : 4 * n * b ^ 2 = 4 * b^2 * n,
    by simp [mul_assoc, mul_comm (b^2) n],
  rw rhs, clear rhs,
  rw add_comm (4 * a ^ 2 * n) (4 * a^2 * b^2),
  apply both_bounds
end


lemma main_arithmetic_sublemma_lhs : (a^2 + n - 2*a)^2 ≤ (a^2 + n - b^2)^2 :=
begin
  apply square_le_square,
  apply nat.sub_le_sub_left _ b_lower_a
end

lemma main_arithmetic_sublemma : (a^2 + n - 2*a)^2 < 4 * a^2 * n :=
  nat.lt_of_le_of_lt main_arithmetic_sublemma_lhs main_arithmetic_sublemma_rhs

end main_arithmetic_sublemma

section induction_step

/- This section introduces the main lemma used to show the validity
   of the recursion. -/

parameters {n M d : ℕ}
parameter M_pos : 0 < M
parameter n_lower_bound : 4 * M^4 ≤ n

definition m := n / (4 * M^2)
definition a := M*d + n / (4*M*d)

/- We assume that d gives an accurate approximation to the square root
   of m, and show that a gives an accurate approximation to the square
   root of n. -/

parameter d_bounds : (d - 1)^2 < m ∧ m < (d + 1)^2

include M_pos n_lower_bound m a d_bounds

lemma m_denom_pos : 0 < 4 * M^2 := begin
  rw pow_two, exact mul_pos nat.four_pos (mul_pos M_pos M_pos)
end

/- Result that's useful for simplification. -/

lemma pow_four : M^4 = M^2 * M^2 := pow_mul_pow M 2 2

/- A key inequality in the proof is that M ≤ d. -/

lemma M_le_d : M ≤ d := begin
  apply nat.le_of_lt_succ, change nat.succ d with d + 1,
  apply lt_of_square_lt_square,
  apply lt_of_le_of_lt _ d_bounds.right,
  rw [m, nat.le_div_iff_mul_le _ _ m_denom_pos],
  rw [mul_comm, mul_assoc, ← pow_four],
  exact n_lower_bound
end

/- We also need to know that 1 ≤ d to be sure that (d - 1)^2 means
   what we think it means. -/

lemma one_le_d : 1 ≤ d := nat.lt_of_lt_of_le M_pos M_le_d

/- Similarly, we need to know that the denominators in the divisions
   are positive. -/

lemma d_pos : 0 < d := nat.lt_of_succ_le one_le_d

lemma a_denom_pos : 0 < 4*M*d := mul_pos (mul_pos nat.four_pos M_pos) d_pos

/- Establish lower and upper bounds on n from d_bounds. These come
   from clearing denominators in d_bounds. -/

lemma n_lower : (2*M*d - 2*M)^2 < n := begin
  have lhs : 2*M*d - 2*M = 2*M*(d - 1), by simp [nat.mul_sub_left_distrib],
  rw [lhs, mul_pow, mul_comm, mul_pow],
  apply nat.mul_lt_of_lt_div,
  exact d_bounds.left
end

lemma n_upper : n < (2*M*d + 2*M)^2 := begin
  have rhs : 2*M*d + 2*M = 2*M*(d+1), by simp [mul_add],
  rw [rhs, mul_pow, mul_pow, mul_comm],
  change 2^2 with 4,
  rw ← nat.div_lt_iff_lt_mul _ _ m_denom_pos,
  exact d_bounds.right
end

/- The following rewrites come up in proving both bounds -/

lemma four_m_d_rewrite : (4*M*d) * (M*d) = (2 * M * d)^2 := begin
  symmetry, rw [mul_assoc, mul_pow, pow_two, pow_two],
  change 2 * 2 with 4, simp [mul_assoc],
end

lemma four_m_d_rewrite2 : (4 * M * d) ^ 2 = 4 * (2 * M * d)^2 := begin
  repeat {rw mul_pow}, repeat {rw ← mul_assoc}, refl
end


/- Establish the lower bound on a:  √n - 1 < a -/

theorem key_isqrt_lemma_rhs : n < (a + 1)^2 := begin
  /- clear denominators in definition of a -/
  apply lt_of_mul_lt_mul ((4*M*d)^2),
  have lhs : (4 * M * d) ^ 2 * n ≤ ((4*M*d) * (M*d) + n)^2,
  { rw [four_m_d_rewrite, four_m_d_rewrite2], apply am_gm },
  apply nat.lt_of_le_of_lt lhs,
  rw ← mul_pow,
  apply square_lt_square,
  change a with M*d + n / (4*M*d),
  rw [add_assoc, mul_add],
  apply add_lt_add_left,
  rw [mul_comm, ← nat.div_lt_iff_lt_mul _ _ a_denom_pos],
  apply nat.le_refl,
end

/- Upper bound on a, a < √n + 1 -/

lemma two_M_le_two_M_d : 2 * M ≤ 2 * M * d := le_mul_of_pos d_pos

/- Rewrite of the key bound, in the form that it appears when
   we're using the main arithmetic sublemma. -/

lemma key_bound_rewrite : (2 * M) ^ 2 ≤ 2 * (2 * M * d) := begin
  rw [mul_pow, pow_two, pow_two],
  repeat { rw mul_assoc },
  repeat {apply nat.mul_le_mul_left},
  apply M_le_d
end


lemma key_isqrt_lemma_lhs_lhs :
  (4 * M * d) ^ 2 * (a - 1) ^ 2 ≤ ((4*M*d) * (M*d) + n - 4*M*d)^2 :=
begin
  rw ← mul_pow,
  apply square_le_square,
  rw [nat.mul_sub_left_distrib, mul_one],
  apply nat.sub_le_sub_right,
  change a with M*d + n / (4*M*d),
  rw mul_add,
  apply add_le_add_left,
  rw mul_comm,
  rw ← nat.le_div_iff_mul_le _ _ a_denom_pos
end


lemma key_isqrt_lemma_lhs_rhs :
  (4 * M * d * (M * d) + n - 4 * M * d) ^ 2 < (4 * M * d) ^ 2 * n :=
begin
  have h : 4 * M * d = 2 * (2 * M * d),
    { change 4 with 2*2, simp [mul_assoc] },
  rw [four_m_d_rewrite, four_m_d_rewrite2, h],

  apply main_arithmetic_sublemma two_M_le_two_M_d n_lower n_upper,
  apply key_bound_rewrite,

  /- Left with: 2 * (2 * M * d) ≤ (2 * M * d) ^ 2 + n -/
  apply nat.le_trans _ (nat.le_add_right _ _),
  rw pow_two,
  apply nat.mul_le_mul_right,
  rw mul_assoc,
  apply le_mul_of_pos (mul_pos M_pos d_pos)
end


theorem key_isqrt_lemma_lhs : (a - 1)^2 < n := begin
  /- clear denominators in definition of a -/
  apply lt_of_mul_lt_mul ((4*M*d)^2),
  apply nat.lt_of_le_of_lt key_isqrt_lemma_lhs_lhs key_isqrt_lemma_lhs_rhs
end

theorem key_isqrt_lemma_all : (a - 1)^2 < n ∧ n < (a + 1)^2 :=
  and.intro key_isqrt_lemma_lhs key_isqrt_lemma_rhs

end induction_step

/- We restate, to fix up use of the peculiar definitions from the
   section above. -/

theorem key_isqrt_lemma {n M d} :
  1 ≤ M → 4 * M^4 ≤ n →
  let m := n / (4 * M^2) in
  ((d - 1)^2 < m ∧ m < (d + 1)^2) →
  let a := M*d + n / (4 * M * d) in
  ((a - 1)^2 < n ∧ n < (a + 1)^2) := key_isqrt_lemma_all

/-

Now that we have the main lemma, we can set about proving the
main theorem. This mostly consists of handling the base case, and
translating the induction step to a state where we can use the main lemma.

But we're missing some essential facts about size and size4;
we establish those first.

-/


/- Facts about nat.size; there seems to be nothing in the standard library
   beyond the definition. -/

/- Unwinding the definition in the zero and nonzero cases -/

lemma size_zero : nat.size 0 = 0 := rfl

lemma size_nonzero {n : ℕ} : n ≠ 0 →
  nat.size n = nat.succ (nat.size (nat.div2 n)) :=
begin
  intro n_nonzero, conv begin to_lhs, rw nat.size end,
  rw [nat.binary_rec, dif_neg n_nonzero], refl
end

/- More convenient re-expression of size_nonzero -/

lemma size_pos {n : ℕ} : 0 < n → nat.size n = nat.size (n / 2) + 1 := begin
  intro n_pos, rw [←nat.div2_val, ←nat.succ_eq_add_one],
  apply size_nonzero, rw ← pos_iff_nonzero, exact n_pos
end


lemma size_pos_of_pos {n : ℕ} : 0 < n → 0 < nat.size n := begin
  intro n_pos, rw size_pos n_pos, apply nat.zero_lt_succ
end


lemma size_one : nat.size 1 = 1 := begin
  rw size_pos zero_lt_one,
  have h : 1 / 2 = 0, by refl, rw h,
  rw size_zero
end


lemma zero_of_size_zero (n : ℕ) : nat.size n = 0 → n = 0 :=
begin
  cases (nat.eq_zero_or_pos n) with n_zero n_pos,
  { intro, assumption },
  intro size_zero,
  have size_pos : 0 < nat.size n := size_pos_of_pos n_pos,
  rewrite size_zero at size_pos,
  revert size_pos,
  apply zero_lt_zero
end


lemma size_zero_iff_zero (n : ℕ) : nat.size n = 0 ↔ n = 0 :=
begin
  split,
  { exact zero_of_size_zero n },
  { intro n_zero, rewrite n_zero, apply size_zero }
end


lemma le_zero_of_size_le_zero {n : ℕ} : nat.size n ≤ 0 → n ≤ 0 := begin
  repeat {rw le_iff_not_lt},
  apply mt, apply size_pos_of_pos,
end


lemma le_zero_iff_eq_zero {n : ℕ} : n ≤ 0 ↔ n = 0 :=
  ⟨ nat.eq_zero_of_le_zero, nat.le_of_eq ⟩


/- defining characteristic of nat.size: n < 2^k iff size n <= k -/

lemma size_le_iff_lt_exp2 {k n : ℕ} : nat.size n ≤ k ↔ n < 2^k := begin
  revert n, induction k with k IH,
  { -- case k = 0
    simp, intro n, rw [le_zero_iff_eq_zero, size_zero_iff_zero],
    split,
    { intro n_zero, rw n_zero, apply zero_lt_one },
    { intro lt_one, rw ← le_zero_iff_eq_zero, apply nat.le_of_lt_succ lt_one }
  },
  { -- case k > 0
    intro n,
    cases (nat.eq_zero_or_pos n) with n_zero n_pos,
    { -- case n = 0
      rw [n_zero, size_zero],
      split; intro,
      {exact nat.pos_pow_of_pos _ nat.two_pos}, {exact nat.zero_le _}
    },
    { -- case n > 0
      rw [nat.pow_succ, ←nat.div_lt_iff_lt_mul _ _ nat.two_pos,
        size_pos n_pos, ← IH],
      change nat.size (n / 2) + 1 with nat.succ (nat.size (n / 2)),
      exact ⟨ nat.le_of_succ_le_succ, nat.succ_le_succ ⟩
    }
  }
end


/- facts about size4 -/

lemma base4base2 (n : ℕ) : 4^n = 2^(2 * n) := begin
  change 4 with 2^2,
  apply pow_assoc,
end


lemma size4_zero : size4 0 = 0 := rfl


lemma size4_positive (n : ℕ) : 0 < n → 0 < size4 n := begin
  intro n_positive,
  rw size4,
  apply nat.lt_of_succ_le,
  rw nat.le_div_iff_mul_le _ _ nat.two_pos,
  simp,
  change 2 with 1 + 1,
  apply add_le_add_right,
  apply size_pos_of_pos,
  assumption,
end


/- defining properties of size4 -/

lemma size4_le_iff_lt_exp4 {k n : ℕ} : size4 n ≤ k ↔ n < 4^k :=
begin
  rw [base4base2, size4, ←size_le_iff_lt_exp2, add_comm],
  have h : nat.size n + 1 = nat.size n + (2 - 1), { change 2 - 1 with 1, refl },
  rw [h, nat.sum_div_le_iff_le_mul nat.two_pos, mul_comm]
end


lemma lt_size4_iff_exp4_le {k n : ℕ} : k < size4 n ↔ 4^k ≤ n :=
begin
  rw [le_iff_not_lt, lt_iff_not_le],
  exact not_iff_not_of_iff size4_le_iff_lt_exp4
end


/- The following is used to establish the validity of the first
   argument in the recursive call in isqrt_aux. -/

lemma size4_shift (k n : ℕ) :
  size4 (n >> 2 * k) = size4 n - k :=
begin
  rw nat.shiftr_eq_div_pow,
  rw ← base4base2,
  have fourpow_pos : 0 < 4^k := nat.pos_pow_of_pos _ nat.four_pos,
  apply nat.le_antisymm,
  {
    rw [size4_le_iff_lt_exp4, nat.div_lt_iff_lt_mul _ _ fourpow_pos],
    rw [←pow_mul_pow, ←size4_le_iff_lt_exp4, ←sub_le_iff_le_add]
  },
  {
    rw [sub_le_iff_le_add, size4_le_iff_lt_exp4, pow_mul_pow],
    rw [←nat.div_lt_iff_lt_mul _ _ fourpow_pos, ←size4_le_iff_lt_exp4]
  }
end


/- lemmas to help with unfolding the definition of isqrt_aux -/

lemma isqrt_aux_zero (n : ℕ): isqrt_aux 0 n = 0 := by rw isqrt_aux

lemma isqrt_aux_one (n : ℕ) : isqrt_aux 1 n = 1 := by rw isqrt_aux

lemma isqrt_aux_recurse (b n : ℕ) : 2 ≤ b →
  isqrt_aux b n = let k := b >> 1 in
                  let d := isqrt_aux (b - k) (n >> 2 * k) in
                  (d << k - 1) + (n >> k + 1) / d :=
begin
  intro two_le_b,
  cases b with b,
  cases two_le_b,
  cases b with c,
  exfalso,
  cases two_le_b,
  cases two_le_b_a,
  rw isqrt_aux
end


lemma random (k) : 0 < k → k + 1 = 2 + (k - 1) := begin
  intro kpos,
  change 2 with 1 + 1,
  symmetry, rw add_comm, symmetry,
  rw ← add_assoc,
  conv
  begin
    to_lhs,
    rw ← nat.sub_add_cancel kpos,
  end
end

lemma random2 (k) : 0 < k → 1 + (k - 1) * 2 + 1 = k * 2 := begin
  intro kpos,
  let m := k - 1,
  have hk : k = m + 1,
  rw nat.sub_add_cancel kpos,
  change k - 1 with m,
  rw hk,
  generalize : m = n,
  clear kpos hk m k,
  symmetry,
  rw mul_comm,
  rw mul_add,
  rw mul_comm,
  symmetry,
  rw add_assoc,
  rw add_comm,
  rw add_assoc,
  refl
end


lemma random3 (k) : 0 < k → 2 + (k - 1) * 2 = 2 * k := begin
  intro kpos,
  let m := k - 1,
  have hk : k = m + 1,
  rw nat.sub_add_cancel kpos,
  change k - 1 with m,
  rw hk,
  generalize : m = n,
  clear kpos hk m k,
  symmetry,
  rw mul_add,
  rw mul_comm,
  rw add_comm,
  refl
end

theorem isqrt_aux_bounds (b n : ℕ) :
    b = size4 n →
    0 < n →
    let a := isqrt_aux b n in (a - 1)^2 < n ∧ n < (a + 1)^2 :=

begin
/- Prove by complete induction (i.e., well-founded induction) on b -/
revert n,
apply (well_founded.induction nat.lt_wf b),
clear b, intro b,
cases b,
{
  /- case b = 0 -/
  intros IH n n_no_digits n_positive,
  clear IH,
  exfalso,
  have h2 : 0 < size4 n, from size4_positive n n_positive,
  rw ←n_no_digits at h2,
  apply nat.lt_irrefl 0,
  assumption,
},
{
  cases b with c,
  {
    /- case b = 1 -/
    intros IH n len1 npos a,
    have a_eq_1 : a = 1, by apply isqrt_aux_one,
    rw a_eq_1,
    simp,
    change 0^2 with 0,
    change (1+1)^2 with 4,
    change (0 < n) with (1 ≤ n),
    /- now showing that 0 < n and n < 4,
       but this should follow just from
       properties of size4
     -/
    split,
    change 1 with 4^0,

    rw ←lt_size4_iff_exp4_le,
    rw ←len1,
    exact nat.zero_lt_one,
    change 4 with 4^1,
    rw ←size4_le_iff_lt_exp4,
    rw ←len1,
  },
  {
    intro IH,
    intro n,
    intro nsize4,
    intro npos,
    intro a,
    let b := nat.succ (nat.succ c),
    have two_le_b : 2 ≤ b,
    change 2 with 0 + 2,
    change b with c + 2,
    apply nat.add_le_add_right,
    apply nat.zero_le,

    have a_def : a = isqrt_aux b n, refl,
    have b_def : b = size4 n, assumption,
    clear npos,
    rw isqrt_aux_recurse b n two_le_b at a_def,
    let k := b >> 1,
    let m := n >> 2 * k,
    let d := isqrt_aux (b - k) m,
    have a_def2 : a = (d << k - 1) + (n >> k + 1) / d,
    rw a_def,
    clear a_def,
    have size4_m : size4 m = b - k, { rw b_def, apply size4_shift},
    have IH2 : (d-1)^2 < m ∧ m < (d + 1)^2,
    apply IH,
    change nat.succ (nat.succ c) with b,
    apply nat.sub_lt,
    apply nat.lt_of_lt_of_le nat.two_pos,
    exact two_le_b,
    change k with b >> 1,
    rw nat.shiftr_eq_div_pow,
    change 2^1 with 2,
    change 0 < b / 2 with 1 ≤ b / 2,
    rw nat.le_div_iff_mul_le _ _ nat.two_pos,
    apply two_le_b,
    {
      symmetry, assumption
    },
    {
      change 0 < m with 4^0 ≤ m,
      rw ← lt_size4_iff_exp4_le,
      rw size4_m,
      apply nat.sub_pos_of_lt,
      change k with b >> 1,
      rw nat.shiftr_eq_div_pow,
      change 2^1 with 2,
      rw nat.div_lt_iff_lt_mul _ _ nat.two_pos,
      rw mul_comm,
      rw two_mul,
      apply nat.lt_add_of_pos_right,
      apply nat.lt_of_lt_of_le nat.two_pos two_le_b
    },
    {
      clear IH,
      let M := 2^(k-1),
      have a_def3 : a = M * d + n / (4 * M * d),
      rewrite a_def2,
      have h4 : d << k - 1 = M * d,
      rewrite nat.shiftl_eq_mul_pow,
      apply mul_comm,
      have h5 : (n >> k + 1) / d = n / (4 * M * d),
      rw nat.shiftr_eq_div_pow,
      have h6 : 2^(k+1) = 4 * M,
      have h7 : k + 1 = 2 + (k - 1),
      have kpos : 0 < k,
      change k with b >> 1,
      rw nat.shiftr_eq_div_pow,
      change 0 < b / 2^1 with 1 ≤ b / 2,
      rw nat.le_div_iff_mul_le _ _ nat.two_pos,
      exact two_le_b,
      apply random,
      apply kpos,
      rw h7,
      rw pow_mul_pow,
      refl,
      rw h6,
      apply nat.div_div_eq_div_mul,
      rw h4,
      rw h5,
      rw a_def3,
      apply key_isqrt_lemma,
      change 1 ≤ M with 0 < M,
      apply nat.pos_pow_of_pos,
      apply nat.two_pos,
      change M with 2^(k-1),
      change 4 with 2 * 2,
      rw ← pow_assoc,
      have h8 : (2^(k-1))^2 = 2^(2*(k-1)),
      rw mul_comm,
      rw pow_assoc,
      rw h8,
      rw ← pow_assoc,
      change 2^2 with 4,
      change 2*2 with 4^1,
      rw pow_assoc,
      rw ← pow_mul_pow,
      rw ← lt_size4_iff_exp4_le,
      rw ← b_def,
      change 1 + (k - 1) * 2 < b with 1 + (k - 1) * 2 + 1 ≤ b,
      have h9 : 1 + (k - 1) * 2 + 1 = k * 2,
      apply random2,
      change 0 < k with 1 ≤ b >> 1,
      rw nat.shiftr_eq_div_pow,
      simp,
      rw nat.le_div_iff_mul_le _ _ nat.two_pos,
      apply two_le_b,
      rw h9,
      rw ← nat.le_div_iff_mul_le _ _ nat.two_pos,
      change k with b >> 1,
      rw nat.shiftr_eq_div_pow,
      apply le_refl,
      have h10: n / (4 * M ^ 2) = m,
      change m with n >> 2 * k,
      rw nat.shiftr_eq_div_pow,
      have h11 : 4 * M^2 = 2 ^ (2 * k),
      change M with 2^(k-1),
      change 4 with 2^2,
      rw pow_assoc,
      rw ← pow_mul_pow,
      rw random3,
      change 0 < k with 1 ≤ b >> 1,
      rw nat.shiftr_eq_div_pow,
      simp,
      rw nat.le_div_iff_mul_le _ _ nat.two_pos,
      apply two_le_b,
      rw h11,
      rw h10,
      exact IH2
    },
  },
}

end


lemma isqrt_zero : isqrt 0 = 0 := by refl

lemma isqrt_small (n : ℕ) :
  let a := isqrt_aux (size4 n) n in a * a ≤ n → isqrt n = a :=
begin
  rw isqrt, simp, intro h, rw if_pos, exact h
end

lemma isqrt_large (n : ℕ) :
  let a := isqrt_aux (size4 n) n in ¬ (a * a ≤ n) → isqrt n = a - 1 :=
begin
  rw isqrt, simp, intro h, rw if_neg, exact h
end

theorem isqrt_correct (n : ℕ) :
  let b := isqrt n in b * b ≤ n ∧ n < (b + 1) * (b + 1) :=
begin
  cases nat.eq_zero_or_pos n,
  { -- case n = 0
    rw h,
    rw isqrt_zero,
    intro,
    change b with 0,
    split,
    apply le_refl,
    exact nat.zero_lt_one,
  },
  { -- case 0 < n
    intro c,
    change c with isqrt n,
    let a := isqrt_aux (size4 n) n,
    have abounds : (a - 1)^2 < n ∧ n < (a + 1)^2,
    apply isqrt_aux_bounds,
    refl,
    assumption,
    cases nat.decidable_le (a * a) n with hneg hpos,
    {
      have h3 : isqrt n = a - 1,
      apply isqrt_large,
      apply hneg,
      rw h3,
      split,
      apply nat.le_of_lt,
      rw ← pow_two,
      apply abounds.left,
      have h4 : a - 1 + 1 = a,
      symmetry,
      rw nat.sub_add_cancel,
      cases nat.eq_zero_or_pos a with h4 h4,
      rw h4 at hneg,
      exfalso,
      change 0 * 0 with 0 at hneg,
      apply hneg,
      apply nat.zero_le,
      apply h4,
      rw h4,
      rw lt_iff_not_le,
      exact hneg,
    },
    {
      have h3 : isqrt n = a,
      apply isqrt_small,
      apply hpos,
      rw h3,
      split,
      {
        exact hpos
      },
      {
        rw ← pow_two,
        apply abounds.right
      }
    }
  }
end

end isqrt



/- the harder part is showing that c is not too large: i.e.,
   (c-1)^2 < n. So let's show that first.

   It suffices to show that:

      (Ma + n/(4Ma) - 1)^2 < n

  (Why? For general a, b, c, need to show that (a//b)^2 < c follows from
   a < b^2 c.)

   So if we want to stay in ℕ or ℤ, rescale to show:

      (4M^2a^2 + n - 4Ma)^2 < 16M^2a^2 n

   or with d = Ma,

      (n + 4d^2 - 4d)^2 < 16d^2n

   But that follows from:

      (n + 4d^2 - 4M^2)^2 < 16d^2n

   which rearranges to:

      ( n - 4d^2 - 4M^2 )^2 < 64d^2M^2


-/



/-

Informal proof:

For ease of notation, we write / for true division and // for floor division
in what follows.

- It's easy to check that the theorem is true for n = 0, so assume n positive.
- In calls to isqrt_aux, the arguments b and n always satisfy b >= 1, n >= 1,
  and

      4^(b-1) <= n < 4^b

  That is, b is the number of digits required to write n in base 4.
- Now prove by induction that under the above assumption on b and n,
  isqrt_aux b n differs from √n by strictly less than 1.

  Case b = 1 (base case): then 1 <= n < 4, so 1 <= √n < 2, and the result
  holds.

  Case b > 1 (induction step): let k = b // 2 and a be
  isqrt_aux (b - k) (n // 4^k), then by the induction hypothesis we have

      | a - √(n // 4^k) | < 1

  or:

      (a - 1)^2 < (n // 4^k) < (a + 1)^2

  It follows that we can replace // with / above:

      a - 1 < √(n / 4^k) < a + 1,

  or

     | a - √(n / 4^k) | < 1

  or

     | 2^k a - √n | < 2^k

  Now consider c := 2^(k-1) a + n / (2^(k+1) a). Then

      c - √n = 2^(k-1) a + n / (2^(k+1) a) - √n
             = (2^(2k) a^2 + n - 2 2^k a √n) / (2^(k+1) a)
             = (2^k a - √n)^2 / (2^(k+1) a)

  So

      0 <= c - √n < 4^k / (2^(k+1) a)

  But n >= 4^(b-1), so √n >= 2^(b-1), so √(n / 4^k) >= 2^(b-1-k),
  so a >= 2^(b-1-k) and 2^(k+1) a >= 2^b. So

      0 <= c - √n < 4^k / 2^b <= 4^(b/2) / 2^b = 1

  and hence

     -1 < floor(c) - √n < 1

  as required.

- So given a result a from the top-level sqrt_inner call, we have

     (a - 1)^2 < n < (a + 1)^2

  So if a^2 <= n, our desired result is a, else a - 1.

The interesting part of the proof is the induction step; as written, the
proof is over the real numbers (or at least, over the decidable ring Z[√n]).
When formalising, we have a choice of making use of Z[√n], or recasting the
proof to operate entirely in ℤ or ℕ. Here we try to recast over ℕ.

Here's one of the key lemmas that we need, over ℝ:

Lemma: suppose a, M and n are natural numbers, with M positive, satisfying:

1. a >= M
2. | a - √(n/4M^2) | < 1

Let c = Ma + n / 4Ma. Then c < 1 + √n

The proof over ℝ is direct: c - √n can be rewritten as |2Ma - √n|^2/4Ma, and
assumption 2 implies that |2Ma - √n| < 2M.

Can we recast that proof over ℕ? First we need to restate the lemma.

Assumption 2 can be restated as 4M^2(a - 1)^2 < n < 4M^2(a + 1)^2.
Similarly, the conclusion can be stated as: (c - 1)^2 < n.

Simplifying (here d corresponds to Ma in the original):

Lemma: suppose d, M and n are real numbers, 0 <= n, 0 < M, M^2 <= d.
Let c = 4d^2 + n. If |2d - √n| < 2M, then 0 <= c - 4d√n < 4d.

Proof: Clear from rearranging c - 4d√n as (2d - √n)^2.

We shouldn't need square roots to state or prove this lemma.

If we assume that M <= d, the main hypothesis is equivalent to:

   (2d - 2M)^2 < n < (2d + 2M)^2

which is equivalent to:

    (1)  ( n - 4d^2 - 4M^2 )^2 < 64d^2M^2

which can be rearranged to:

    (2)  ( n + 4d^2 - 4M^2 )^2 < 16d^2n

The < part of the conclusion is equivalent to

    (3)  ( n + 4d^2 - 4d)^2 < 16d^2n,

But now it's clear that (3) follows from (2), provided only that

    (5)  |n + 4d^2 - 4d|^2 <= |n + 4d^2 - 4M^2|^2

i.e., that

        0 <= (4d - 4M^2)(2n + 8d^2 - 4d - 4M^2)

so it's enough that

        2d + 2M^2 <= n + 4d^2

-/
