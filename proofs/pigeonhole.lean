/-

Attempt to prove some form of the pigeonhole principle in Lean.

We prove two different versions; the first says that for any map

    f : fin n → ℕ

with n ≥ 1, there's an element x of fin n such that f x ≥ m / n.

The second says that for any map f : fin m → fin n, again with n ≥ 1,
there's an element y of fin n such that the preimage of y has at
least m/n elements.

-/

/-
Definitions of partial summation (up to a given m) and summation on fin n.
-/

def partial_sum {n : ℕ} (m : ℕ) (m_le_n : m ≤ n) (f : fin n → ℕ) : ℕ := begin
    induction m with k ind_hyp,
    exact 0,
    exact ind_hyp (nat.le_of_succ_le m_le_n) + f ⟨k, m_le_n⟩,
end

def sum_of {n : ℕ} (f : fin n → ℕ) : ℕ := partial_sum n (nat.le_refl n) f

/-
Lemmas to help with unwinding the recursive partial_sum definition.
-/

lemma partial_sum_zero {n : ℕ} (f : fin n → ℕ) :
    partial_sum 0 (nat.zero_le n) f = 0 := rfl


lemma partial_sum_succ {n : ℕ} (m : ℕ) (succ_m_le_n : nat.succ m ≤ n) (f) :
    partial_sum (nat.succ m) succ_m_le_n f =
        partial_sum m (nat.le_of_succ_le succ_m_le_n) f +
            f ⟨ m, succ_m_le_n ⟩ := by rw partial_sum; refl

/-
Basic properties of partial_sum.
-/





lemma partial_sum_eq {n m : ℕ} (m_le_n : m ≤ n)
    (f : fin n → ℕ) (g : fin n → ℕ) :
    (∀ x, f x = g x) → partial_sum m m_le_n f = partial_sum m m_le_n g :=
begin
    intro f_eq_g,
    induction m with k ind_hyp,
    refl,  -- base case
    repeat {rw partial_sum_succ},
    rw ind_hyp (nat.le_of_succ_le m_le_n),
    rw f_eq_g
end


lemma partial_sum_of_zero {n m : ℕ} (m_le_n : m ≤ n) :
    partial_sum m m_le_n (λ x, 0) = 0 :=
begin
    induction m with k ind_hyp,
    refl, -- base case
    repeat {rw partial_sum_succ},
    rw ind_hyp (nat.le_of_succ_le m_le_n)
end


lemma partial_sum_of_add
    {n : ℕ} (m : ℕ) (m_le_n : m ≤ n) (f : fin n → ℕ) (g : fin n → ℕ) :
    partial_sum m m_le_n (λ x, f x + g x) =
    partial_sum m m_le_n f + partial_sum m m_le_n g :=
begin
    induction m with k ind_hyp,
    refl, -- base case
    repeat {rw partial_sum_succ},
    rw ind_hyp (nat.le_of_succ_le m_le_n),
    simp,
end


lemma partial_sum_of_one {n m : ℕ} (m_le_n : m ≤ n) :
    partial_sum m m_le_n (λ x, 1) = m :=
begin
    induction m with k ind_hyp,
    refl, -- base case
    repeat {rw partial_sum_succ},
    rw ind_hyp (nat.le_of_succ_le m_le_n)
end


lemma partial_sum_of_indicator {n : ℕ} (m : ℕ) (m_le_n : m ≤ n) (x : fin n) :
    partial_sum m m_le_n (λ y, if x = y then 1 else 0) =
    if x.val < m then 1 else 0 :=
begin
    induction m with k ind_hyp,
    refl, -- base case
    repeat {rw partial_sum_succ},
    rw ind_hyp (nat.le_of_succ_le m_le_n),

    have take_vals : ite (x = (⟨k, m_le_n⟩ : fin n)) 1 0 = ite (x.val = k) 1 0,
    {
        cases nat.decidable_eq x.val k with x_ne_k x_eq_k,
        rw [if_neg, if_neg],

        exact x_ne_k,
        apply fin.ne_of_vne,
        exact x_ne_k,

        rw [if_pos, if_pos],
        exact x_eq_k,
        apply fin.eq_of_veq,
        exact x_eq_k,
    },
    rw take_vals,

    cases lt_trichotomy x.val k with hlt heq_hgt,
    { -- x < k
        rw [if_pos, if_neg, if_pos],
        exact nat.lt_succ_of_lt hlt,
        exact ne_of_lt hlt,
        exact hlt
    },
    cases heq_hgt with heq hgt,
    { -- x = k
        rw [if_neg, if_pos, if_pos]; rw heq,
        apply nat.lt_succ_self,
        apply nat.lt_irrefl
    },
    { -- x > k
        rw [if_neg, if_neg, if_neg],
        intro lt_succ,
        have x_le_k : x.val ≤ k, {
            apply nat.le_of_lt_succ lt_succ,
        },
        revert hgt,
        apply not_lt_of_ge,
        apply x_le_k,
        intro x_eq_k,
        revert hgt,
        rw x_eq_k,
        apply nat.lt_irrefl,
        apply not_lt_of_lt,
        apply hgt
    }
end


/- Helper for the induction step -/

lemma pigeonhole_ind_step {m S fm fx : ℕ} :
    0 < m →
    S ≤ m * fx →
    nat.succ m * fm < S + fm →
    S + fm ≤ nat.succ m * fx :=
begin
    change nat.succ m with m + 1,
    intros m_pos ind_hyp h2,
    rw [add_mul, one_mul],
    apply add_le_add ind_hyp,
    apply le_of_mul_le_mul_left _ m_pos,
    apply le_trans _ ind_hyp,
    rw ← nat.add_le_add_iff_le_right fm,
    rw [add_mul, one_mul] at h2,
    exact nat.le_of_lt h2
end

/- Version of the target statement for partial_sum, proved by induction -/

lemma pigeonhole_partial {n m : ℕ} (f : fin n → ℕ) :
    1 ≤ m → ∀ (m_le_n : m ≤ n),
    exists x, partial_sum m m_le_n f ≤ m * f x :=
begin
    intro m_ge_1, induction m_ge_1 with k k_ge_1 induction_hypothesis,
    { -- base case m = 1
        intro n_ge_1, existsi (⟨0, n_ge_1⟩ : fin n),
        rw partial_sum_succ,
        change 0 + f ⟨0, n_ge_1⟩ ≤ 1 * f ⟨0, n_ge_1⟩,
        simp,
    },
    { -- induction step
        intro k_lt_n,
        -- either f k works, or it doesn't
        let top : fin n := ⟨ k, k_lt_n ⟩,
        cases nat.lt_or_ge (nat.succ k * f top) (partial_sum (nat.succ k) k_lt_n f)
            with top_not_ok top_ok,
        { -- top doesn't work; use the induction hypothesis
            cases induction_hypothesis (nat.le_of_succ_le k_lt_n) with x x_ok,
            existsi x,
            apply pigeonhole_ind_step k_ge_1 x_ok top_not_ok
        },
        { -- top works! use it
            existsi top, exact top_ok
        }
    }
end

/- The main statement then follows immediately. -/

theorem pigeonhole_principle {n : ℕ} (n_pos : 1 ≤ n) (f : fin n → ℕ) :
    exists x : fin n, sum_of f ≤ n * f x := by apply pigeonhole_partial _ n_pos

/- Alternative formulation: given a function f : fin m → fin n,
   there should be an element x of fin n whose preimage has at
   least m / n elements.

   But that means we need some way to count the size of the preimage.
-/

lemma sum_of_indicator {n : ℕ} (fx : fin n) :
    sum_of (λ (y : fin n), if fx = y then 1 else 0) = 1 :=
begin
    rw sum_of,
    rw partial_sum_of_indicator n (nat.le_refl n) fx,
    rw if_pos,
    cases fx,
    exact fx_is_lt
end


lemma sum_of_zero {n : ℕ} : sum_of (λ x : fin n, 0) = 0 :=
    partial_sum_of_zero _


lemma sum_of_add {n : ℕ} (f g : fin n → ℕ) :
        sum_of (λ x, f x + g x) = sum_of f + sum_of g :=
    partial_sum_of_add _ _ _ _


lemma sum_of_one {n : ℕ} : sum_of (λ x : fin n, 1) = n :=
    partial_sum_of_one _


lemma sum_of_equality {n : ℕ} (f g : fin n → ℕ) :
    (∀ x, f x = g x) → sum_of f = sum_of g := partial_sum_eq _ _ _

lemma partial_order_of_summation {m n k : ℕ} (k_le_m : k ≤ m) (f : fin m → fin n → nat) :
    partial_sum k k_le_m (λ x, sum_of (λ y, f x y)) =
    sum_of (λ y, partial_sum k k_le_m (λ x, f x y)) :=
begin
    induction k with k ind_hyp,
    {
        rw partial_sum_zero, apply sum_of_zero.symm
    },
    {
        rename k_le_m succ_k_le_m,
        rw partial_sum_succ,
        have rhs : sum_of (λ y : fin n, partial_sum (nat.succ k) succ_k_le_m
                                (λ x : fin m, f x y)) =
                   sum_of (λ y : fin n, partial_sum k (nat.le_of_succ_le succ_k_le_m)
                                (λ x : fin m, f x y) + f ⟨ k, _ ⟩  y),
        {
            apply sum_of_equality, intro y, rw partial_sum_succ
        },
        rw rhs,
        rw ind_hyp (nat.le_of_succ_le succ_k_le_m),
        rw sum_of_add
    }
end




theorem order_of_summation {m n : ℕ} (f : fin m → fin n → nat) :
    sum_of (λ x : fin m, sum_of (λ y : fin n, f x y)) =
    sum_of (λ y : fin n, sum_of (λ x : fin m, f x y)) :=
begin
    apply partial_order_of_summation
end


/- the sizes of the preimages sum to the size of the domain -/

def preimage_size {m n : ℕ} (f : fin m → fin n) (y : fin n) : ℕ :=
    sum_of (λ x, if f x = y then 1 else 0)


lemma sum_of_preimage_size {m n : ℕ} (f : fin m → fin n) :
    sum_of (preimage_size f) = m :=

begin
    change sum_of (λ y, sum_of (λ x, if f x = y then 1 else 0)) = m,
    rw order_of_summation,
    have h : sum_of (λ (x : fin m), sum_of (λ (y : fin n), ite (f x = y) 1 0)) =
             sum_of (λ (x : fin m), 1),
    {
        apply sum_of_equality, intro x, apply sum_of_indicator
    },
    rewrite h,
    apply sum_of_one
end


theorem pigeonhole_principle_bis {m n : ℕ} (n_pos : 1 ≤ n) (f : fin m → fin n) :
    exists y : fin n, m ≤ n * preimage_size f y :=

begin
    have preimage_sum := sum_of_preimage_size f,
    have pp1 := pigeonhole_principle n_pos (λ y : fin n, preimage_size f y),
    rw preimage_sum at pp1,
    exact pp1
end
