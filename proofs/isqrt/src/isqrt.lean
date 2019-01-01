/-

This file provides a formal proof of correctness of a recursive integer
square root algorithm originally written in Python.

We use the "Lean" Theorem Prover, which can be obtained from:

    https://leanprover.github.io

This proof was verified using version 3.4.1 of Lean. After installing Lean,
you can run the verification yourself from a command line using:

    lean isqrt_lean

On a successful verification, this will produce no output.

-/

/-

For reference, here's the Python code that we'll translate into Lean.


  def isqrt_aux(c, n):
      if c == 0:
          return 1
      else:
          k = (c - 1) // 2
          a = isqrt_aux(c // 2, n >> 2*k + 2)
          return (a << k) + (n >> k+2) // a


  def isqrt(n):
      if n == 0:
          return 0
      else:
          a = isqrt_aux((n.bit_length() - 1) // 2, n)
          return a - 1 if n < a * a else a


On input to isqrt_aux, n should be positive and c should be floor(log4(n))
(i.e., one less than the number of base-4 digits of n). It returns a value
a satisfying (a - 1)^2 < n < (a + 1)^2.

-/

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
complicates some aspects of the proof, but avoids some of the pain of having
to deal with type coercions.

-/

import data.nat.basic
import tactic.ring
import tactic.split_ifs


/- Goals of 0 < 2 and 0 < 4 come up often enough to be worth encapsulating. -/

lemma nat.two_pos : 0 < 2 := dec_trivial
lemma nat.four_pos : 0 < 4 := dec_trivial


/- nat.div_lt_of_lt_mul : ∀ {m n k : ℕ}, m < n * k → m / n < k -/

lemma nat.lt_mul_of_div_lt {k x y : ℕ} : 0 < k → x / k < y → x < y * k :=
  assume k_pos, (nat.div_lt_iff_lt_mul _ _ k_pos).mp

/- counterpart to nat.div_mul_le_self -/

theorem self_lt_div_succ_mul (m n : ℕ) : 0 < n → m < (m / n + 1) * n :=
  assume n_pos, nat.lt_mul_of_div_lt n_pos (nat.lt_succ_self (m / n))

/- logical negations, used with mt to generate the contrapositive
   of a statement. Note that lt_iff_not_ge is in the standard library,
   but we restate it since we rarely use the ≥ comparison. -/

lemma lt_iff_not_le {m n : ℕ} : m < n ↔ ¬ (n ≤ m) :=
  lt_iff_not_ge m n


lemma le_iff_not_lt {m n : ℕ} : m ≤ n ↔ ¬ (n < m) :=
  ⟨ not_lt_of_le, le_of_not_lt ⟩


lemma le_iff_lt_succ (x y : ℕ) : x ≤ y ↔ x < y + 1 :=
  ⟨ nat.lt_succ_of_le, nat.le_of_lt_succ ⟩


lemma lt_of_mul_lt_mul (a : ℕ) {b c : ℕ} : a * b < a * c → b < c :=
begin
  repeat {rw lt_iff_not_le}, apply mt, apply nat.mul_le_mul_left
end


/- division-multiplication results, supplementing the main
   results nat.le_div_iff_mul_le and nat.div_lt_iff_lt_mul -/

lemma nat.mul_lt_of_lt_div {x y k : ℕ} :
  x < y / k → x * k < y :=
begin
  /- this is just the contrapositive of nat.div_le_of_le_mul -/
  simp only [lt_iff_not_le], apply mt,
  rw mul_comm, apply nat.div_le_of_le_mul
end


/- Some general-purposes lemmas used for manipulating inequalities later. -/

/- The following can be used with the 'cases' tactic to turn a hypothesis
   a ≤ b into a nat c and a hypothesis b = a + c; then rewriting with the
   hypothesis replaces uses of b with a + c throughout. This is a way to
   get rid of subtractions.
-/

lemma exists_add_of_le {a b : ℕ} : a ≤ b → exists (c : ℕ), b = a + c :=
begin
  intro a_le_b,
  existsi b - a,
  rw [add_comm, nat.sub_add_cancel a_le_b]
end


/- These lemmas allows us to deduce an inequality from an equivalent one.
   They generate an equality that can frequently be solved by high-powered
   tactics like "ring".
-/

lemma lt_equiv {a b c d : ℕ} : a < b → a + d = b + c → c < d :=
begin
  intros a_lt_b sums_equal,
  apply @nat.lt_of_add_lt_add_left a,
  rw sums_equal,
  apply nat.add_lt_add_right a_lt_b
end

lemma le_equiv {a b c d : ℕ} : a ≤ b → a + d = b + c → c ≤ d :=
begin
  intros a_le_b sums_equal,
  apply @nat.le_of_add_le_add_left a,
  rw sums_equal,
  apply nat.add_le_add_right a_le_b
end


/- squares and inequalities -/

lemma square_lt_square {a b : ℕ} : a < b → a^2 < b^2 :=
begin
  intro a_lt_b, simp only [nat.pow_two],
  have b_pos : 0 < b := nat.lt_of_le_of_lt (nat.zero_le a) a_lt_b,
  exact nat.lt_of_le_of_lt (nat.mul_le_mul_left a (nat.le_of_lt a_lt_b))
                           (nat.mul_lt_mul_of_pos_right a_lt_b b_pos)
end


lemma square_le_square {a b : ℕ} : a ≤ b → a^2 ≤ b^2 :=
begin
  intro a_le_b, simp only [nat.pow_two],
  exact nat.le_trans (nat.mul_le_mul_left a a_le_b)
                     (nat.mul_le_mul_right b a_le_b)
end


lemma lt_of_square_lt_square {a b : ℕ} : a^2 < b^2 → a < b :=
begin
  simp only [lt_iff_not_le], exact mt square_le_square
end


lemma close_to_sublemma {a b c : ℕ} : a ≤ b →
  b < a + c → a^2 + b^2 < c^2 + 2*a*b :=
begin
  intro a_le_b,
  cases exists_add_of_le a_le_b with d subst_b,
  rw subst_b,
  intro ad_lt_ac,
  apply lt_equiv (square_lt_square (nat.lt_of_add_lt_add_left ad_lt_ac)),
  ring
end


lemma close_to {a b c : ℕ} : a < b + c → b < a + c →
  a^2 + b^2 < c^2 + 2*a*b :=
begin
  intros a_low b_low,
  cases le_total a b with a_le_b b_le_a,
  { apply lt_equiv (close_to_sublemma a_le_b b_low), ring },
  { apply lt_equiv (close_to_sublemma b_le_a a_low), ring }
end


lemma am_gm (a b : ℕ) : 4*a*b ≤ (a + b)^2 :=
begin
  cases le_total a b with h_le h_le;
  {
    cases exists_add_of_le h_le with c to_c, rewrite to_c,
    apply le_equiv (nat.zero_le (c^2)), ring
  }
end


/- Conclusion is (c - b)^2 ≤ (d - a)^2, in disguise -/

theorem square_squeeze {a b c d : ℕ} : a ≤ b → b ≤ c → c ≤ d →
  b^2 + c^2 + 2*a*d ≤ a^2 + d^2 + 2*b*c :=
begin
  intro a_le_b, cases exists_add_of_le a_le_b with e b_rw, rw b_rw,
  intro b_le_c, cases exists_add_of_le b_le_c with f c_rw, rw c_rw,
  intro c_le_d, cases exists_add_of_le c_le_d with g d_rw, rw d_rw,
  apply le_equiv (nat.zero_le (e^2 + g^2 + 2*e*f + 2*e*g + 2*f*g)),
  ring
end


lemma sub_elimination {a b c : ℕ} (one_le_a : 1 ≤ a) : (a - 1)^2 * b < c →
  a^2*b + b < c + 2*a*b :=
begin
  cases exists_add_of_le one_le_a with e a_eq,
  rw [a_eq, nat.add_sub_cancel_left],
  intro orig_bound, apply lt_equiv orig_bound, ring
end


lemma sub_elimination2 {a c : ℕ} (one_le_a : 1 ≤ a) :
  (a - 1)^2 < c ↔ a^2 + 1 < c + 2*a :=
begin
  cases exists_add_of_le one_le_a with e a_eq,
  rw [a_eq, nat.add_sub_cancel_left],
  split; {intro h, apply lt_equiv h, ring}
end



section induction_step

/- This section introduces the main lemma used to show the validity
   of the recursion.

   We assume that d gives an accurate approximation to the square root
   of m, and show that a gives an accurate approximation to the square
   root of n. -/


parameters {n M d : ℕ}
parameter M_pos : 1 ≤ M
parameter n_lower_bound : 4 * M^4 ≤ n
parameter d_bounds : let m := n / (4 * M^2) in
  1 ≤ d ∧ (d - 1)^2 < m ∧ m < (d + 1)^2

include M_pos n_lower_bound d_bounds

/- Various simple inequalities -/

lemma m_denom_pos : 0 < 4*M^2 :=
  mul_pos (nat.four_pos) (nat.pow_pos M_pos 2)
lemma a_denom_pos : 0 < 4*M*d :=
  mul_pos (mul_pos nat.four_pos M_pos) d_bounds.left
lemma one_le_Md : 1 ≤ M*d :=
  nat.succ_le_of_lt (mul_pos M_pos d_bounds.left)


/- The following key inequality follows mainly from the lower bound on n -/

lemma key_inequality : 4*M^2 ≤ 4*M*d := begin
  have : M^2 ≤ n / (4 * M^2), {
    rw [nat.le_div_iff_mul_le _ _ m_denom_pos],
    apply le_equiv n_lower_bound, ring
  },
  have : M ≤ d, {
    exact nat.le_of_lt_succ
      (lt_of_square_lt_square (nat.lt_of_le_of_lt this d_bounds.right.right))
  },
  apply le_equiv (nat.mul_le_mul_left (4*M) this),
  ring
end

/- Other specific inequalities needed below -/

lemma key_inequality2 : 4*M*d ≤ 4*M^2*d^2 + 4*M*d * (n/(4*M*d)) :=
begin
  apply le_add_right,
  apply le_equiv (nat.mul_le_mul_left (4*M*d) one_le_Md),
  ring
end

lemma key_inequality3 : (4*M^2*d^2 + 4*M*d*(n/(4*M*d))) ≤ 4*M^2*d^2 + n :=
begin
  apply le_equiv (nat.div_mul_le_self n (4*M*d)),
  generalize : n / (4 * M * d) = e,
  ring
end


/- follows from n / (4*M^2) < (d + 1)^2 -/

lemma d_large : n < 4*M^2*d^2 + 4*M^2 + 8*M^2*d :=
begin
  apply lt_equiv (nat.lt_mul_of_div_lt m_denom_pos d_bounds.right.right),
  ring
end

/- follows from (d - 1)^2 < n / (4*M^2) -/

lemma d_small : 4*M^2*d^2 + 4*M^2 < n + 8*M^2*d :=
begin
  apply lt_equiv
    (sub_elimination d_bounds.left (nat.mul_lt_of_lt_div d_bounds.right.left)),
  ring
end


lemma key_isqrt_lemma_bound :
  let a := M*d + n / (4*M*d) in 1 ≤ a := le_add_right one_le_Md


lemma key_isqrt_lemma_lhs :
  let a := M*d + n / (4*M*d) in (a - 1)^2 < n :=
begin
  intro a,
  rw sub_elimination2 key_isqrt_lemma_bound,
  apply lt_of_mul_lt_mul ((4*M*d)^2),
  apply lt_equiv
    (add_lt_add_of_le_of_lt
      (square_squeeze key_inequality key_inequality2 key_inequality3)
      (close_to d_large d_small)),
  change a with M * d + n / (4 * M * d),
  generalize : n / (4 * M * d) = e,
  ring
end


lemma key_isqrt_lemma_rhs :
  let a := M*d + n / (4*M*d) in
  n < (a + 1)^2 :=
begin
  apply lt_of_mul_lt_mul ((4*M*d)^2),
  apply lt_equiv
    (add_lt_add_of_le_of_lt
      (am_gm (4*M^2*d^2) n)
      (square_lt_square
        (add_lt_add_left
          (self_lt_div_succ_mul n (4*M*d) a_denom_pos)
          (4*M^2*d^2)))),
  generalize : n / (4 * M * d) = e,
  ring
end


theorem key_isqrt_lemma :
  let a := M*d + n / (4*M*d) in 1 ≤ a ∧ (a - 1)^2 < n ∧ n < (a + 1)^2 :=
  ⟨ key_isqrt_lemma_bound, key_isqrt_lemma_lhs,  key_isqrt_lemma_rhs ⟩


end induction_step

/-

Now that we have the main lemma, we can set about proving the
main theorem. This mostly consists of handling the base case, and
translating the induction step to a state where we can use the main lemma.

But we're missing some essential facts about size and size4;
we establish those first.

-/


lemma size_nonzero_iff_nonzero {n : ℕ} : nat.size n ≠ 0 ↔ n ≠ 0 :=
  not_iff_not_of_iff nat.size_eq_zero


/- facts about size4 -/

lemma base4base2 {n : ℕ} : 4^n = 2^(2 * n) := (nat.pow_mul 2 n 2).symm


/- Number of base-4 digits of n -/
def size4 (n : ℕ) := (1 + nat.size n) / 2


lemma size4_le_iff_lt_exp4 {k n : ℕ} : size4 n ≤ k ↔ n < 4^k :=
begin
  rw [base4base2, size4, ←nat.size_le, le_iff_lt_succ, le_iff_lt_succ,
      nat.div_lt_iff_lt_mul _ _ nat.two_pos],
  generalize : nat.size n = m,
  split; { intro h, apply lt_equiv h, ring }
end


lemma lt_size4_iff_exp4_le {k n : ℕ} : k < size4 n ↔ 4^k ≤ n :=
begin
  rw [le_iff_not_lt, lt_iff_not_le],
  exact not_iff_not_of_iff size4_le_iff_lt_exp4
end

/-
  Introduce notation for left and right shifts, so that we
  can make the Lean code look more like Python code.
-/

reserve infix ` << `:60
reserve infix ` >> `:60

notation n >> k := nat.shiftr n k
notation n << k := nat.shiftl n k


/- The following is used to establish the validity of the first
   argument in the recursive call in isqrt_aux. -/

lemma size4_shift (k n : ℕ) :
  size4 (n >> 2 * k) = size4 n - k :=
begin
  rw [nat.shiftr_eq_div_pow, ←base4base2],
  have fourpow_pos : 0 < 4^k := nat.pos_pow_of_pos _ nat.four_pos,
  apply nat.le_antisymm,
  {
    rw [size4_le_iff_lt_exp4, nat.div_lt_iff_lt_mul _ _ fourpow_pos],
    rw [←nat.pow_add, ←size4_le_iff_lt_exp4, ←nat.sub_le_right_iff_le_add]
  },
  {
    rw [nat.sub_le_right_iff_le_add, size4_le_iff_lt_exp4, nat.pow_add],
    rw [←nat.div_lt_iff_lt_mul _ _ fourpow_pos, ←size4_le_iff_lt_exp4]
  }
end


lemma big_half_little_half (n : ℕ) : n = (n + 1) / 2 + n / 2 := begin
  induction n,
  case nat.zero : { refl },
  case nat.succ : n induction_hypothesis {
    calc
      nat.succ n = (n + 1) / 2 + n / 2 + 1 : congr_arg _ induction_hypothesis
             ... = (n + 1) / 2 + (n / 2 + 1) : by rw add_assoc
             ... = (n + 1) / 2 + (n + 2) / 2 : by rw nat.add_div_right _ nat.two_pos
             ... = (n + 2) / 2 + (n + 1) / 2 : by rw add_comm
             ... = ((nat.succ n + 1) / 2) + (nat.succ n) / 2 : by refl
  }
end


/- In calls to isqrt_aux c n, correctness assumes that size4 n = c + 1.
   Here we prove that this condition holds in the initial call to isqrt_aux
   (from isqrt).
-/

lemma size4_condition_initial {n : ℕ} :
  n ≠ 0 → size4 n = (nat.size n - 1) / 2 + 1 :=
begin
  intro n_nonzero,
  unfold size4,
  have size_pos : 1 ≤ nat.size n, {
    change 0 < nat.size n,
    rw nat.size_pos,
    exact nat.pos_of_ne_zero n_nonzero,
  },
  cases exists_add_of_le size_pos with m size_n_rw,
  rw [size_n_rw, nat.add_sub_cancel_left],
  ring
end


lemma size4_condition_step {c n : ℕ} :
  c ≠ 0 →
  size4 n = c + 1 →
  let k := (c - 1) / 2 in
  size4 (n >> 2*k + 2) = c / 2 + 1 :=
begin
  intros c_nonzero size4_n k,
  have twok : 2 * k + 2 = 2 * (k + 1), by ring,
  rw [twok, size4_shift, size4_n],
  change k with (c - 1) / 2,
  cases exists_add_of_le (nat.pos_of_ne_zero c_nonzero) with d c_rw,
  rw [c_rw, nat.add_sub_cancel_left],
  apply nat.sub_eq_of_eq_add,
  show 1 + d + 1 = d / 2 + 1 + ((1 + d) / 2 + 1),
  conv begin to_lhs, rw big_half_little_half d, end,
  simp
end


/- Definition of the auxiliary function -/

lemma isqrt_aux_well_founded {c : ℕ} : c ≠ 0 → c / 2 < c := begin
    intro c_ne_zero,
    rw [nat.div_lt_iff_lt_mul _ _ nat.two_pos, mul_comm, two_mul],
    apply nat.lt_add_of_pos_left (nat.pos_of_ne_zero c_ne_zero)
end


def isqrt_aux : ℕ → ℕ → ℕ | c n :=
    if h : c = 0 then
        1
    else
        have c / 2 < c := isqrt_aux_well_founded h,
        let k := (c - 1) / 2,
            a := isqrt_aux (c / 2) (n >> 2*k + 2) in
        (a << k) + (n >> k+2) / a


/- Validity of isqrt_aux in base case. -/

lemma isqrt_aux_base {c n : ℕ} : c = 0 → size4 n = c + 1 →
  1 ≤ 1 ∧ (1 - 1)^2 < n ∧ n < (1 + 1)^2 :=
begin
  intro c_zero, rw c_zero, simp, intro size4_n,
  have n_low : 4^0 ≤ n, {
    rw [←lt_size4_iff_exp4_le, size4_n],
    exact nat.zero_lt_one
  },
  have n_high : n < 4^1, {
    rw [←size4_le_iff_lt_exp4, size4_n]
  },
  exact ⟨ nat.le_refl 1, n_low, n_high ⟩
end

/- Bound used in the reduction step. -/

lemma isqrt_aux_M_bound {c n : ℕ} :
  c ≠ 0 → size4 n = c + 1 →
  let k := (c - 1) / 2, M := 2^k in
  4*M^4 ≤ n :=
begin
  intros c_nonzero size4_n k M,
  dsimp only [M],
  have h : 4 * (2 ^ k) ^ 4 = 4^(2 * k + 1),
  {
    change (2^2) * (2 ^ k) ^ 4 = (2^2)^(2 * k + 1),
    repeat {rw ←nat.pow_mul}, rw ←nat.pow_add,
    apply congr_arg,
    ring
  },
  rw [h, ←lt_size4_iff_exp4_le, size4_n],
  dsimp only [k],
  cases exists_add_of_le (nat.pos_of_ne_zero c_nonzero) with d c_rw,
  rw [c_rw, nat.add_sub_cancel_left, ←le_iff_lt_succ],
  have hd : 2 * (d / 2) ≤ d,
    by rw [mul_comm, ←nat.le_div_iff_mul_le _ _ nat.two_pos],
  apply le_equiv hd,
  generalize : d / 2 = e,
  ring,
end


lemma isqrt_aux_step {c n a : ℕ} :
  c ≠ 0 → size4 n = c + 1 →
  let k := (c - 1) / 2, m := n >> 2 * k + 2 in
  1 ≤ a ∧ (a - 1)^2 < m ∧ m < (a + 1)^2 →
  let d := (a << k) + (n >> k + 2) / a in
  1 ≤ d ∧ (d - 1)^2 < n ∧ n < (d + 1)^2 :=
begin
  intros c_ne_zero size4_n k,
  rw [nat.shiftl_eq_mul_pow, nat.shiftr_eq_div_pow, nat.shiftr_eq_div_pow],
  intros m a_bounds d,

  let M := 2^k,
  have n_bound : 4 * M^4 ≤ n := isqrt_aux_M_bound c_ne_zero size4_n,
  have change_m : m = n / (4 * M^2), {
    change n / 2 ^ (2 * k + 2) = n / ((2^2) * (2^k) ^ 2),
    rw [←nat.pow_mul, ←nat.pow_add, add_comm, mul_comm]
  },
  rw change_m at a_bounds,

  have change_d : d = M * a + n / (4 * M * a), {
    change a * 2 ^ k + n / 2 ^ (k + 2) / a = 2^k * a + n / (2^2 * 2^k * a),
    have lhs : a * 2^k = 2^k * a, by rw mul_comm,
    have rhs : n / 2 ^ (k + 2) / a = n / (2^2 * 2^k * a), by
      rw [nat.div_div_eq_div_mul, add_comm, nat.pow_add],
    rw [lhs, rhs],
  },
  rw change_d,

  exact key_isqrt_lemma (nat.pos_pow_of_pos k nat.two_pos) n_bound a_bounds
end


/- Statement of correctness for the auxiliary function -/

theorem isqrt_aux_correctness : ∀ {c n : ℕ}, size4 n = c + 1 →
  let d := isqrt_aux c n in 1 ≤ d ∧ (d - 1)^2 < n ∧ n < (d + 1)^2 :=
begin
  intro c, apply nat.strong_induction_on c, clear c,
  intros c induction_hypothesis n size4_n, rw isqrt_aux,
  split_ifs with is_c_zero,
  {
    apply isqrt_aux_base is_c_zero size4_n
  },
  {
    apply isqrt_aux_step is_c_zero size4_n,
    apply induction_hypothesis _ (isqrt_aux_well_founded is_c_zero),
    exact size4_condition_step is_c_zero size4_n
  }
end


/- Definition of the main function -/

def isqrt (n : ℕ) : ℕ :=
    if n = 0 then
        0
    else
        let a := isqrt_aux ((nat.size n - 1) / 2) n in
        if n < a^2 then a - 1 else a


/- Statement of correctness for the main function -/

theorem isqrt_is_sqrt (n : ℕ) :
  let a := isqrt n in
  a^2 ≤ n ∧ n < (a + 1)^2 :=
begin
  rw isqrt, split_ifs with h_if h_if2,
  { -- h_if : n = 0
    rw h_if, exact ⟨ nat.le_refl 0, nat.zero_lt_one ⟩
  },
  { -- h_if2 : n < a^2
    have n_bounds := isqrt_aux_correctness (size4_condition_initial h_if),
    rw nat.sub_add_cancel n_bounds.left,
    exact ⟨nat.le_of_lt n_bounds.right.left, h_if2⟩
  },
  { -- h_if2 : ¬(n < a^2)
    have n_bounds := isqrt_aux_correctness (size4_condition_initial h_if),
    exact ⟨le_of_not_lt h_if2, n_bounds.right.right⟩
  }
end
