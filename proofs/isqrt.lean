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
        return an integer a close to the square root of n.

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

/- A goal of 0 < 2 comes up so often that it's worth encapsulating. -/

lemma zero_lt_two : 0 < 2 := by repeat {constructor}

/- Lemma used to show that the recursive call in isqrt_aux terminates. -/
lemma isqrt_aux_wf (c : ℕ) : c + 2 - (c + 2 >> 1) < c + 2 :=
begin
  apply nat.sub_lt,
  { show 0 < c + 2, apply nat.zero_lt_succ },
  {
    rw nat.shiftr_eq_div_pow,
    change 0 < (c + 2) / 2 ^ 1 with 1 ≤ (c + 2) / 2,
    rw nat.le_div_iff_mul_le 1 (c + 2) zero_lt_two,
    apply nat.le_add_left
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
Before launching into the formal proof, we give an informal proof.

Notation. Our informal proof uses a blend of Python notation, Lean notation and
ordinary mathematical notation. We write // for the floor division operation
(the floor of the true quotient). This is the same as Lean's "/" operator on ℕ,
or Python's // on int. We'll write / for normal mathematical division on real
numbers. * represents multiplication, ^ represents exponentiation, and √
represents the usual real square root.

We'll show by strong induction on n that for n positive, if d = isqrt_aux
(size4 n) n then (d - 1)^2 < n < (d + 1)^2. This then implies the correctness
of isqrt.

For 0 < n < 4, the result can be verified by case-by-case computation.
For n ≥ 4, the isqrt_aux definition enters the recursive call. Define:

    k = size4 n // 2
    m = n // 4^k
    a = isqrt_aux (size4 m) m

then unwinding the definitions in isqrt_aux, the return value of
isqrt_aux (size4 n) n is

    (1)  d = 2^(k-1) * a + n // 2^(k+1) // a

The induction hypothesis gives:

    (2)  (a - 1)^2 < m < (a + 1)^2

and we must deduce that (d - 1)^2 < n < (d + 1)^2.

Unfolding the definition of m in (2), (a - 1)^2 < floor(n / 4^k) < (a + 1)^2.
Since (a + 1)^2 is an integer, it follows that n / 4^k < (a + 1)^2, so (2)
implies the (slightly weaker, but sufficient for our purposes) statement:

    (3)  (a - 1)^2 < n / 4^k < (a + 1)^2

Taking square roots in (3) and rearranging gives

    (4)  abs(√n - 2^k a) < 2^k

Define the real number e by:

    (5)  e = 2^(k-1) * a + n / (2^(k+1) * a)

Then d = floor(e), so

    (6)  d ≤ e < d + 1

Now:

    (7)  e - √n = ( 2^(k-1) * a + n / (2^(k+1) * a) - √n )
                = ( 2^(2k) * a^2 + n - 2^(k+1) * a * √n ) / (2^(k+1) * a)
                = ( √n - 2^k * a )^2 / (2^(k+1) * a)

Using the bound on abs(√n - 2^k * a) in (4), and noting that the quantity
on the right-hand side of (7) is nonnegative, we have

    (8)  0 ≤ e - √n < 2^(2*k) / (2^(k+1) * a)

To complete this we need a lower bound on a. We have 4^(size4 n - 1) ≤ n and
2*k ≤ size4 n, by the definitions of size4 and k respectively. So:

    (9)  4^(2*k - 1) ≤ 4^(size4 n - 1) ≤ n

Dividing both sizes by 4^k and combining with the right-hand-side of (3),

    (10)  4^(k - 1) < (a + 1)^2

Taking square roots gives 2^(k - 1) < (a + 1), or equivalently, since 2^(k-1)
is an integer,

    (11)  2^(k - 1) ≤ a

Combining this with (8) gives

    (12)  0 ≤ e - √n < 1

Since d = floor(e), it follows that

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


/- logical negations, used with mt to generate the contrapositive
   of a statement. See also not_iff_not_of_iff. -/

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

-- it's sometimes useful to split into cases a <= b and b <= a,
-- to be able to make use of symmetry

lemma le_or_ge (a b : ℕ) : a ≤ b ∨ b ≤ a :=
begin
  cases nat.lt_or_ge a b with hlt hge,
  { left, exact nat.le_of_lt hlt },
  { right, exact hge }
end

/- Galois connection for addition and subtraction in nat -/

lemma le_add_of_sub_le (a b c : ℕ) :
    a - c ≤ b → a ≤ b + c :=
begin
  revert b,
  induction c with c IH,
  { intro, apply id },
  {
    intro b,
    change a - nat.succ c with nat.pred (a - c),
    intro h,
    change b + nat.succ c with nat.succ (b + c),
    rw nat.add_comm,
    change nat.succ (c + b) with c + nat.succ b,
    rw nat.add_comm,
    apply IH,
    apply nat.le_succ_of_pred_le,
    exact h
  }
end

lemma sub_le_of_le_add {a b c : ℕ} :
    a ≤ b + c → a - c ≤ b :=
begin
  intro h,
  rw ← nat.add_sub_cancel b c,
  apply nat.sub_le_sub_right,
  exact h
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

lemma lt_of_mul_lt_mul (a b c : ℕ) : a * b < a * c → b < c :=
begin
  repeat {rw lt_iff_not_le}, apply mt, apply nat.mul_le_mul_left
end

/- Complete induction for natural numbers is a special case of
   well-founded induction. Also look at nat.strong_induction_on -/

lemma complete_induction (C : ℕ → Prop) :
   (∀ x, (∀ y, y < x → C y) → C x) → ∀ a, C a :=
begin
  intros IH a, apply well_founded.induction nat.lt_wf, exact IH
end

/- Some facts about nat.pow that seem to be missing from the standard library -/

lemma pow_zero (a : ℕ) : a ^ 0 = 1 := rfl

lemma pow_two (a : ℕ) : a ^ 2 = a * a := begin
  rw nat.pow_succ,
  rw nat.pow_one
end

lemma pow_mul_pow (a b c : ℕ) : a^(b + c) = a^b * a^c := begin
  induction c with c ih,
  {
    rw nat.add_zero,
    rw pow_zero,
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
    repeat {rw pow_zero}, refl
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

/- Division Galois connections spelled out as one-way implications -/

lemma nat.le_div_of_mul_le {x y k : ℕ} :
  0 < k → x * k ≤ y → x ≤ y / k :=
begin
  intros,
  apply (nat.le_div_iff_mul_le x y _).mpr,
  assumption,
  assumption,
end

lemma nat.mul_le_of_le_div {x y k : ℕ} :
  0 < k → x ≤ y / k → x * k ≤ y :=
begin
  intro kpos,
  apply (nat.le_div_iff_mul_le x y kpos).mp
end

lemma nat.div_lt_of_lt_mul {x y k : ℕ} :
  0 < k → x < y * k → x / k < y :=
begin
  intro kpos,
  apply (nat.div_lt_iff_lt_mul x y kpos).mpr,
end

lemma nat.lt_mul_of_div_lt {x y k : ℕ} :
  0 < k → x / k < y → x < y * k :=
begin
  intro kpos,
  apply (nat.div_lt_iff_lt_mul x y kpos).mp
end

lemma nat.le_mul_of_div_le (x y : ℕ) {k : ℕ} :
  0 < k → (x + (k - 1)) / k ≤ y → x ≤ y * k :=
begin
  intro kpos,
  intro div_le,
  apply nat.le_of_lt_succ,
  change nat.succ (y * k) with y * k + 1,
  apply @nat.lt_of_add_lt_add_left (k - 1),
  have h1 : k - 1 + (y * k + 1) = (y + 1) * k,
  rw add_comm,
  rw add_assoc,
  have h2 : 1 + (k - 1) = k,
  rw add_comm,
  apply nat.succ_pred_eq_of_pos,
  assumption,
  rw h2,
  symmetry,
  rw mul_comm,
  rw nat.mul_succ,
  rw mul_comm,
  rw h1,
  rw add_comm,
  apply nat.lt_mul_of_div_lt,
  assumption,
  apply nat.lt_succ_of_le,
  assumption
end


lemma nat.div_le_of_le_mul2 (x y : ℕ) {k : ℕ} :
  0 < k → x ≤ y * k → (x + (k - 1)) / k ≤ y :=
begin
  intros kpos le_mul,
  apply nat.le_of_lt_succ,
  apply nat.div_lt_of_lt_mul kpos,
  rw mul_comm,
  rw nat.mul_succ,
  change x + (k - 1) < k * y + k with x + (k - 1) + 1 ≤ k * y + k,
  rw add_assoc,
  have h2 : k - 1 + 1 = k,
  apply nat.succ_pred_eq_of_pos,
  assumption,
  rw h2,
  apply nat.add_le_add_right,
  rw mul_comm,
  assumption
end

/- squares and inequalities -/

lemma square_lt_square (a b : ℕ) : a < b → a^2 < b^2 :=
begin
  rw pow_two,
  rw pow_two,
  intro a_lt_b,
  have h : a * a ≤ a * b,
  apply nat.mul_le_mul_left,
  apply nat.le_of_lt,
  exact a_lt_b,
  apply nat.lt_of_le_of_lt h,
  apply nat.mul_lt_mul_of_pos_right,
  exact a_lt_b,
  apply nat.lt_of_le_of_lt,
  apply nat.zero_le,
  apply a_lt_b
end


lemma square_le_square (a b : ℕ) : a ≤ b → a^2 ≤ b^2 :=
begin
  rw pow_two,
  rw pow_two,
  intro a_le_b,
  have h : a * a ≤ a * b,
  apply nat.mul_le_mul_left,
  exact a_le_b,
  apply nat.le_trans h,
  apply nat.mul_le_mul_right,
  exact a_le_b,
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

lemma square_sub {a b : ℕ} : b ≤ a → (a - b)^2 = a^2 + b^2 - 2*a*b :=
begin
  intro b_le_a,
  apply @nat.add_right_cancel _ (2*a*b),
  rw nat.sub_add_cancel,
  {
    let c := a - b,
    have ha : b + c = a, by apply nat.add_sub_of_le b_le_a,
    change a - b with c,
    rw ← ha,
    repeat {rw pow_two},
    rw two_mul,
    repeat {rw add_mul},
    repeat {rw mul_add},
    simp,
    apply congr_arg,
    apply congr_arg,
    rw mul_comm
  },
  {
    apply cauchy_schwarz
  }
end

lemma abs_lt {a b c : ℕ} : a - b < c → b - a < c →
  a^2 + b^2 < c^2 + 2*a*b :=
begin
  intros a_sub_b b_sub_a,
  cases le_or_ge a b with a_le_b b_le_a,
  {
    let d := b - a,
    have hd : b = a + d, { symmetry, apply nat.add_sub_of_le a_le_b },
    rw hd,
    rw hd at b_sub_a,
    rw nat.add_sub_cancel_left at b_sub_a,
    repeat {rw pow_two},
    rw two_mul,
    repeat {rw mul_add},
    repeat {rw add_mul},
    simp,
    repeat {apply nat.add_lt_add_left},
    rw mul_comm,
    apply nat.add_lt_add_left,
    repeat {rw ← pow_two},
    apply square_lt_square,
    exact b_sub_a
  },
  {
    let d := a - b,
    have hd : a = b + d, { symmetry, apply nat.add_sub_of_le b_le_a },
    rw hd,
    rw hd at a_sub_b,
    rw nat.add_sub_cancel_left at a_sub_b,
    repeat {rw pow_two},
    rw two_mul,
    repeat {rw mul_add},
    repeat {rw add_mul},
    simp,
    repeat {apply nat.add_lt_add_left},
    rw mul_comm,
    have h1 : c * c + (d * b + d * b) = d * b + (d * b + c * c), by simp,
    rw h1, clear h1,
    repeat {apply nat.add_lt_add_left},
    repeat {rw ← pow_two},
    apply square_lt_square,
    exact a_sub_b
  }
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


/- the main arithmetic sublemma -/

theorem key_isqrt_sublemma (n a b : ℕ) :
  b ≤ a →
  (a - b) ^ 2 < n →
  n < (a + b)^2 →
  b ^ 2 ≤ 2 * a →
  (a ^ 2 + n - 2 * a) ^ 2 < 4 * a^2 * n :=
begin
  intro b_le_a,
  intro n_lower_bound,
  intro n_upper_bound,
  intro b_small,
  have b_pos : 0 < b, {
    cases nat.eq_zero_or_pos b with hzero hpos,
    {
      exfalso,
      rw hzero at n_lower_bound,
      rw hzero at n_upper_bound,
      change a - 0 with a at n_lower_bound,
      change a + 0 with a at n_upper_bound,
      apply lt_irrefl n,
      apply nat.lt_trans n_upper_bound n_lower_bound
    },
    {
      exact hpos
    }
  },
  have a_small : 2 * a ≤ a^2 + n, {
    apply @nat.le_trans _ (a^2 + 1),
    {
      change a^2 + 1 with a^2 + 1^2,
      have h1 : 2 * a = 2 * a * 1, { symmetry, apply mul_one },
      rw h1, clear h1,
      apply cauchy_schwarz
    },
    {
      apply add_le_add_left,
      apply nat.succ_le_of_lt,
      apply nat.lt_of_le_of_lt _ n_lower_bound,
      apply nat.zero_le
    }
  },
  /- the following inequality represents the delta between what we know
     and what we have to prove -/
  have delta := squares_diffs b_small a_small,
  /- now recast what we know as a single inequality -/
  have wwk1 : n - (a^2 + b^2) < 2*a*b,
  {
    apply sub_lt_of_lt_add,
    apply mul_pos,
    apply mul_pos,
    apply zero_lt_two,
    apply nat.lt_of_lt_of_le b_pos b_le_a,
    apply b_pos,
    have h1 : 2 * a * b + (a ^ 2 + b ^ 2) = (a + b)^2, {
      repeat {rw pow_two},
      rw two_mul,
      repeat {rw add_mul},
      repeat {rw mul_add},
      simp,
      apply congr_arg,
      apply congr_arg,
      rw mul_comm
    },
    rw h1, clear h1,
    exact n_upper_bound
  },
  have wwk2 : (a^2 + b^2) - n < 2*a*b,
  {
    apply sub_lt_of_lt_add,
    apply mul_pos,
    apply mul_pos,
    apply zero_lt_two,
    apply nat.lt_of_lt_of_le b_pos b_le_a,
    apply b_pos,
    have h1 : 2 * a * b + n = n + 2 * a * b, by rw add_comm,
    rw h1, clear h1,
    apply lt_add_of_sub_lt,
    rw ← square_sub,
    exact n_lower_bound,
    exact b_le_a
  },
  have wwk := abs_lt wwk2 wwk1, clear wwk1 wwk2,

  /- now rewrite the target to eliminate subtractions -/
  rw square_sub a_small,
  apply sub_lt_of_lt_add,
  apply mul_pos,
  apply mul_pos,
  { repeat {constructor} },
  rw pow_two,
  apply mul_pos,
  apply nat.lt_of_lt_of_le b_pos b_le_a,
  apply nat.lt_of_lt_of_le b_pos b_le_a,
  apply nat.lt_of_le_of_lt _ n_lower_bound,
  apply nat.zero_le,

  /- clear out the junk that we no longer need -/
  clear a_small b_pos b_small n_upper_bound n_lower_bound b_le_a,

  /- now it's just a matter of shifting terms around -/
  /- first simplify and multiply everything out -/
  apply @nat.lt_of_add_lt_add_left (b^4 + 2 * a^2 * b^2),
  apply @nat.lt_of_lt_of_le _ (4*a^2*b^2 + 4*a^2*n + 2*b^2*n + 4*a^2),
  {
    have lhs : b ^ 4 + 2 * a ^ 2 * b ^ 2 + ((a ^ 2 + n) ^ 2 + (2 * a) ^ 2) =
      (a ^ 2 + b ^ 2) ^ 2 + n ^ 2 + (2*a^2*n + 4*a^2),
    {
      change 4 with 2 * 2,
      rw ← pow_assoc,
      repeat {rw pow_two},
      repeat {rw two_mul},
      repeat {rw add_mul},
      repeat {rw mul_add},
      repeat {rw two_mul},
      simp,
      repeat {apply congr_arg},
      rw mul_comm,
      repeat {apply congr_arg},
      rw mul_comm,
    },
    rw lhs, clear lhs,
    have rhs : 4 * a ^ 2 * b ^ 2 + 4 * a ^ 2 * n + 2 * b ^ 2 * n + 4 * a ^ 2 =
      (2 * a * b) ^ 2 + 2 * (a ^ 2 + b ^ 2) * n + (2*a^2*n + 4*a^2),
    {
      change 4 with 2 * 2,
      repeat {rw pow_two},
      repeat {rw two_mul},
      repeat {rw add_mul},
      repeat {rw mul_add},
      repeat {rw two_mul},
      repeat {rw add_mul},
      repeat {rw mul_add},
      simp,
      repeat {apply congr_arg},
      have h1 : a * a * (b * b) = a * b * (a * b),
      {
        repeat {rw mul_assoc},
        apply congr_arg,
        rw mul_comm,
        repeat {rw mul_assoc},
        apply congr_arg,
        apply mul_comm
      },
      repeat {rw h1},
    },
    rw rhs, clear rhs,
    apply add_lt_add_right wwk
  },
  {
    have lhs : 4 * a ^ 2 * b ^ 2 + 4 * a ^ 2 * n + 2 * b ^ 2 * n + 4 * a ^ 2 =
      2 * b ^ 2 * (a ^ 2 + n) + (2 * a) ^ 2 + (2*a^2*b^2 + 4*a^2*n),
    {
      change 4 with 2 * 2,
      repeat {rw pow_two},
      repeat {rw two_mul},
      repeat {rw add_mul},
      repeat {rw mul_add},
      repeat {rw two_mul},
      repeat {rw add_mul},
      repeat {rw mul_add},
      simp,
      repeat {apply congr_arg},
      rw mul_comm,
    },
    rw lhs, clear lhs,
    have rhs : b ^ 4 + 2 * a ^ 2 * b ^ 2 + (4 * a ^ 2 * n + 2 * (a ^ 2 + n) * (2 * a)) =
      2 * (2 * a) * (a ^ 2 + n) + (b ^ 2) ^ 2 + (2*a^2*b^2 + 4*a^2*n),
    {
      repeat {rw mul_add},
      repeat {rw add_mul},
      change b^4 with b^(2*2),
      rw pow_assoc,
      simp,
      apply congr_arg,
      have h1 : 2 * n * (2 * a) = 2 * (2 * a) * n,
      {
        repeat {rw mul_assoc},
        apply congr_arg,
        rw mul_comm,
        rw mul_assoc
      },
      rw h1, clear h1,
      apply congr_arg,
      apply congr_arg,
      have h1 : 2 * a ^ 2 * (2 * a) = 2 * (2 * a) * a ^ 2,
      {
        repeat {rw mul_assoc},
        apply congr_arg,
        rw mul_comm,
        rw mul_assoc
      },
      rw h1
    },
    rw rhs, clear rhs,
    apply add_le_add_right,
    exact delta
  }
end

/- the main lemma used in the recursion -/

theorem key_isqrt_lemma (n M d : ℕ) :
  1 ≤ M → 4 * M^4 ≤ n →
  let m := n / (4 * M^2) in
  ((d - 1)^2 < m ∧ m < (d + 1)^2) →
  let a := M*d + n / (4 * M * d) in
  ((a - 1)^2 < n ∧ n < (a + 1)^2) :=

begin
  intro M_positive,
  intro n_lower_bound,
  intro m,
  intro d_bounds,
  intro a,

  have M_le_d : M ≤ d,
  {
    apply @nat.le_of_add_le_add_right 1,
    change M + 1 ≤ d + 1 with M < d + 1,
    apply lt_of_square_lt_square,
    apply @nat.lt_of_le_of_lt _ m,
    change m with n / (4 * M^2),
    apply nat.le_div_of_mul_le,
    apply mul_pos,
    { repeat {constructor} },
    rw pow_two,
    apply mul_pos,
    exact M_positive,
    exact M_positive,
    rw mul_comm,
    rw mul_assoc,
    rw ← pow_two,
    rw pow_assoc,
    exact n_lower_bound,
    exact d_bounds.right,
  },

  /- because of the use of 4*M*d as a denominator, we'll frequently
     need to use the fact that it's positive -/
  have four_m_d_pos : 0 < 4*M*d,
  {
    apply mul_pos,
    apply mul_pos,
    { repeat {constructor }},
    assumption,
    exact nat.lt_of_lt_of_le M_positive M_le_d
  },
  have m_lower : n < (2*M*d + 2*M)^2,
  {
    have h : 2 * M * d + 2 * M = 2 * M * (d + 1),
    {
      rw mul_add,
      rw mul_one,
    },
    rw h,
    rw mul_pow,
    rw mul_comm,
    apply nat.lt_mul_of_div_lt,
    apply nat.pos_pow_of_pos,
    rw mul_comm,
    apply nat.lt_mul_of_div_lt,
    apply zero_lt_two,
    exact M_positive,
    rw mul_pow,
    exact d_bounds.right
  },
  have m_upper : (2*M*d - 2*M)^2 < n,
  {
    apply @nat.lt_of_lt_of_le _ (4 * M^2 * m),
    have h : 2 * M * d - 2 * M = 2 * M * (d - 1),
    {
      rw nat.mul_sub_left_distrib,
      rw mul_one
    },
    rw h,
    rw mul_pow,
    rw mul_pow,
    change 2^2 with 4,
    apply nat.mul_lt_mul_of_pos_left,
    exact d_bounds.left,
    apply mul_pos,
    { repeat {constructor} },
    rw pow_two,
    apply mul_pos,
    exact M_positive,
    exact M_positive,
    rw mul_comm,
    apply nat.mul_le_of_le_div,
    apply mul_pos,
    { repeat {constructor} },
    rw pow_two,
    apply mul_pos,
    exact M_positive,
    exact M_positive,
    apply le_refl,
  },
  split,
  {
    apply lt_of_mul_lt_mul ((4*M*d)^2),
    rw ← mul_pow,
    apply @nat.lt_of_le_of_lt _ ((4*(M*d)^2 + n - 4*M*d)^2),
    {
      apply square_le_square,
      rw nat.mul_sub_left_distrib,
      rw mul_one,
      apply nat.sub_le_sub_right,
      change a with M * d + n / (4 * M * d),
      rw mul_add,
      rw pow_two,
      have h1 : 4 * M * d * (M * d) = 4 * (M * d * (M * d)),
        by repeat {rewrite mul_assoc},
      rw h1, clear h1,
      apply nat.add_le_add_left,
      rw mul_comm,
      apply nat.mul_le_of_le_div four_m_d_pos,
      apply nat.le_refl
    },
    {
      clear a d_bounds m n_lower_bound four_m_d_pos,
      let a := 2*M*d,
      have h1 : 4*M*d = 2 * a,
      {
        change a with 2*M*d,
        change 4 with 2*2,
        repeat {rw mul_assoc}
      },
      rw h1, clear h1,
      have h1 : 4 * (M * d) ^ 2 = a^2,
      {
        change a with 2 * M * d,
        rw mul_assoc,
        generalize : M*d = Md,
        rw mul_pow,
        refl
      },
      rw h1, clear h1,
      change 2*M*d with a at m_lower,
      change 2*M*d with a at m_upper,
      let b := 2 * M,
      change 2 * M with b,
      change 2 * M with b at m_lower,
      change 2 * M with b at m_upper,
      have b_small : b^2 ≤ 2*a,
      {
        change b with 2 * M,
        change a with 2 * M * d,
        rw mul_pow,
        rw pow_two,
        rw pow_two,
        repeat {rw mul_assoc},
        apply nat.mul_le_mul_left,
        apply nat.mul_le_mul_left,
        apply nat.mul_le_mul_left,
        exact M_le_d
      },
      have b_le_a : b ≤ a, {
        change a with 2 * M * d,
        change b with 2 * M,
        repeat {rw mul_assoc},
        apply nat.mul_le_mul_left,
        rw ← mul_one M,
        repeat {rw mul_assoc},
        apply nat.mul_le_mul_left,
        rw one_mul,
        apply le_trans M_positive M_le_d
      },
      have h1 : (2 * a) ^ 2 = 4 * a^2, {
        rw mul_pow,
        refl
      },
      rw h1, clear h1,
      apply key_isqrt_sublemma n a b b_le_a m_upper m_lower b_small
    }
  },
  {
    apply lt_of_mul_lt_mul ((4*M*d)^2),
    rw ← mul_pow,
    apply @nat.lt_of_le_of_lt _ ((4*(M*d)^2 + n)^2),
    {
      have h1 : (4 * M * d) ^ 2 = 4 * (4 * (M * d)^2),
      {
        rw mul_assoc, rw mul_pow, repeat {rw pow_two}, repeat {rw mul_assoc}
      },
      rw h1, clear h1,
      generalize : 4 * (M * d)^2 = p,
      apply am_gm
    },
    {
      apply square_lt_square,
      change a with M * d + n / (4 * M * d),
      repeat {rw mul_add},
      rw pow_two,
      rw mul_one,
      repeat {rw mul_assoc},
      rw add_assoc,
      apply nat.add_lt_add_left,
      repeat {rw ← mul_assoc},
      revert four_m_d_pos,
      generalize : 4*M*d = N,
      intro N_pos,
      have h1 : N * (n / N) + N = (n / N + 1) * N,
      {
        symmetry,
        rw [mul_comm, mul_add, mul_one]
      },
      rw h1, clear h1,
      apply nat.lt_mul_of_div_lt N_pos,
      apply nat.le_refl
    }
  }
end


/- Facts about nat.size; there seems to be nothing in the standard library -/

lemma size_zero : nat.size 0 = 0 := rfl

lemma nat_size_unfold (n : ℕ) : nat.size n =
    if n = 0 then 0 else nat.succ (nat.size (nat.div2 n)) := begin
  /- unfold nat.size definition only on the LHS -/
  change nat.size n with nat.binary_rec 0 (λ (_x : bool) (_x : ℕ), nat.succ) n,
  rw nat.binary_rec,
  refl,
end

lemma nat_size_pos {n : ℕ} : 0 < n → nat.size n = nat.size (n / 2) + 1 := begin
  intro npos,
  rw [nat_size_unfold, if_neg, nat.div2_val],
  intro n_zero,
  rw n_zero at npos,
  revert npos, apply zero_lt_zero
end

lemma succ_size_bit (b : bool) (n : ℕ) :
      0 < nat.bit b n → 0 < nat.size (nat.bit b n) :=
begin
  intro pos,
  rw nat_size_unfold,
  have h : ¬(nat.bit b n = 0), from begin
    intro h2,
    rw h2 at pos,
    apply nat.lt_irrefl 0,
    assumption,
  end,
  rw (if_neg _),
  apply nat.zero_lt_succ,
  assumption,
end

lemma size_one : nat.size 1 = 1 := begin
  rw [nat_size_unfold, if_neg], refl, trivial
end

lemma size_pos_of_pos {n : ℕ} : 0 < n → 0 < nat.size n :=
  @nat.binary_rec (λ n, 0 < n → 0 < nat.size n) (λ h, false.elim (nat.lt_irrefl 0 h))
  (λ b n _, succ_size_bit b n) n

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

/- defining characteristic of nat.size: n < 2^k iff size n <= k -/

lemma lt_exp2_of_size_le (k n : ℕ) : nat.size n ≤ k → n < 2^k := begin
  revert n,
  induction k with k IH,
  all_goals { intro n, cases (nat.eq_zero_or_pos n) with n_zero n_pos },
  -- k = 0, n = 0
  { rw n_zero, intro, simp, constructor },
  -- k = 0, n > 0,
  {
    intro size_le_zero, apply zero_lt_zero,
    exact nat.lt_of_lt_of_le (size_pos_of_pos n_pos) size_le_zero,
  },
  -- ind step, n = 0,
  { rw n_zero, intro, apply nat.pos_pow_of_pos, apply zero_lt_two },
  -- ind step, n > 0,
  {
    intro size_le, rw nat.pow_succ,
    apply (nat.lt_mul_of_div_lt zero_lt_two),
    apply IH,
    apply nat.le_of_succ_le_succ,
    revert size_le,
    rw (nat_size_pos n_pos),
    exact id,
  }
end

lemma size_le_of_lt_exp2 (k n : ℕ) : n < 2^k → nat.size n ≤ k := begin
  revert n,
  induction k with k IH,
  all_goals { intro n, cases (nat.eq_zero_or_pos n) with n_zero n_pos },
  -- k = 0, n = 0
  { rw n_zero, intro, rw size_zero },
  -- k = 0, n > 0
  { simp, rw lt_iff_not_ge, intro, contradiction },
  -- induction step, n = 0
  { rw n_zero, intro, rewrite size_zero, apply nat.zero_le },
  -- induction step, n > 0
  {
    intro n_lt,
    rw (nat_size_pos n_pos),
    apply nat.succ_le_succ,
    apply IH,
    apply nat.div_lt_of_lt_mul zero_lt_two,
    rw ←nat.pow_succ,
    exact n_lt
  }
end

/- contrapositives of the above -/

lemma exp2_le_of_lt_size (k n : ℕ) : k < nat.size n → 2^k ≤ n := begin
  rw [le_iff_not_lt, lt_iff_not_le], apply mt, apply size_le_of_lt_exp2
end

lemma lt_size_of_exp2_le (k n : ℕ) : 2^k ≤ n → k < nat.size n := begin
  rw [lt_iff_not_le, le_iff_not_lt], apply mt, apply lt_exp2_of_size_le
end

lemma exp2_size_le (n : ℕ) : 0 < n → 2 ^ (nat.size n - 1) ≤ n := begin
  intro n_pos,
  apply exp2_le_of_lt_size,
  change nat.size n - 1 < nat.size n with nat.size n - 1 + 1 ≤ nat.size n,
  rw nat.sub_add_cancel,
  exact (size_pos_of_pos n_pos)
end

lemma lt_exp2_size (n : ℕ) : n < 2 ^ (nat.size n) := begin
  apply lt_exp2_of_size_le,
  trivial
end

/- facts about size4 -/

lemma size4_positive (n) : 0 < n → 0 < size4 n := begin
  intro n_positive,
  apply nat.le_div_of_mul_le,
  repeat {constructor},
  simp,
  change 2 with 1 + 1,
  apply add_le_add_right,
  apply size_pos_of_pos,
  assumption,
end

lemma size4_zero : size4 0 = 0 := rfl

lemma base4base2 (n : ℕ) : 4^n = 2^(2 * n) := begin
  change 4 with 2^2,
  apply pow_assoc,
end


lemma lt_exp4_of_size4_le (k n : ℕ) : size4 n ≤ k → n < 4^k :=
begin
  unfold size4, intro h,
  rw base4base2,
  apply lt_exp2_of_size_le,
  rw mul_comm,
  apply nat.le_mul_of_div_le _ _ zero_lt_two,
  rw add_comm,
  assumption
end


lemma size4_le_of_lt_exp4 (k n : ℕ) : n < 4^k → size4 n ≤ k :=
begin
  unfold size4, intro h,
  rw add_comm,
  change 1 with 2 - 1,
  apply nat.div_le_of_le_mul2 _ _ zero_lt_two,
  apply size_le_of_lt_exp2,
  rw mul_comm,
  rw ← base4base2,
  assumption
end

/- contrapositives again -/

lemma lt_size_4_of_exp4_le (k n : ℕ) : 4^k ≤ n → k < size4 n :=
begin
  rw [lt_iff_not_le, le_iff_not_lt],
  apply mt, apply lt_exp4_of_size4_le
end

lemma exp4_le_of_lt_size4 (k n : ℕ) : k < size4 n → 4^k ≤ n :=
begin
  rw [le_iff_not_lt, lt_iff_not_le],
  apply mt, apply size4_le_of_lt_exp4
end

lemma size4_shift (k n : ℕ) :
  size4 (n >> 2 * k) = size4 n - k :=
begin
  rw nat.shiftr_eq_div_pow,
  rw ← base4base2,
  apply nat.le_antisymm,
  {
    apply size4_le_of_lt_exp4,
    apply nat.div_lt_of_lt_mul,
    apply nat.pos_pow_of_pos,
    repeat {constructor},
    rw ← pow_mul_pow,
    apply lt_exp4_of_size4_le,
    apply le_add_of_sub_le,
    apply le_refl
  },
  {
    apply sub_le_of_le_add,
    apply size4_le_of_lt_exp4,
    rw pow_mul_pow,
    apply nat.lt_mul_of_div_lt,
    apply nat.pos_pow_of_pos,
    repeat {constructor},
    apply lt_exp4_of_size4_le,
    apply le_refl,
  },
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
    apply exp4_le_of_lt_size4,
    rw ← len1,
    constructor,
    change 4 with 4^1,
    apply lt_exp4_of_size4_le,
    rw ← len1,
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
    apply nat.lt_of_lt_of_le zero_lt_two,
    exact two_le_b,
    change k with b >> 1,
    rw nat.shiftr_eq_div_pow,
    change 2^1 with 2,
    change 0 < b / 2 with 1 ≤ b / 2,
    apply nat.le_div_of_mul_le,
    apply zero_lt_two,
    apply two_le_b,
    {
      symmetry, assumption
    },
    {
      change 0 < m with 4^0 ≤ m,
      apply exp4_le_of_lt_size4,
      rw size4_m,
      apply nat.sub_pos_of_lt,
      change k with b >> 1,
      rw nat.shiftr_eq_div_pow,
      change 2^1 with 2,
      apply nat.div_lt_of_lt_mul,
      apply zero_lt_two,
      rw mul_comm,
      rw two_mul,
      apply nat.lt_add_of_pos_right,
      apply nat.lt_of_lt_of_le zero_lt_two two_le_b
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
      apply nat.le_div_of_mul_le,
      apply zero_lt_two,
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
      apply zero_lt_two,
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
      apply exp4_le_of_lt_size4,
      rw ← b_def,
      change 1 + (k - 1) * 2 < b with 1 + (k - 1) * 2 + 1 ≤ b,
      have h9 : 1 + (k - 1) * 2 + 1 = k * 2,
      apply random2,
      change 0 < k with 1 ≤ b >> 1,
      rw nat.shiftr_eq_div_pow,
      apply nat.le_div_of_mul_le,
      apply zero_lt_two,
      apply two_le_b,
      rw h9,
      apply nat.mul_le_of_le_div,
      apply zero_lt_two,
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
      apply nat.le_div_of_mul_le,
      apply zero_lt_two,
      apply two_le_b,
      rw h11,
      rw h10,
      exact IH2
    },
  },
}

end


/-

key_isqrt_lemma :
  ∀ (n M d : ℕ),
    1 ≤ M →
    4 * M ^ 4 ≤ n →
    (let m : ℕ := n / (4 * M ^ 2)
     in (d - 1) ^ 2 < m ∧ m < (d + 1) ^ 2 →
        (let a : ℕ := M * d + n / (4 * M * d) in
          (a - 1) ^ 2 < n ∧ n < (a + 1) ^ 2))
-/

/- def isqrt (n : ℕ) : ℕ :=
  let a := isqrt_aux (size4 n) n in if a * a <= n then a else a - 1

  -/

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
    constructor,
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
