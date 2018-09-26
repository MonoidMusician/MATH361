import analysis.real tactic.ring tactic.interactive
import seq naturally background binomial

namespace problem1

noncomputable theory

lemma converges_of_bdd_not_decr (s : seq ℝ) :
  bdd_above {x : ℝ | ∃ n, x = s n} → (∀ n, s n ≤ s (n+1)) → converges s := sorry

lemma converges_to_cSup (s : seq ℝ) : (∀ n, s n ≤ s (n+1)) → converges_to s (lattice.Sup {x : ℝ | ∃ n, x = s n}) := sorry

def a : seq ℝ := shift 1 $ λ n, (1+1/n)^n
def b : seq ℝ := shift 1 $ λ n, (1+1/n)^(n+1)
def I : seq (set ℝ) := λ n, set.Icc (a n) (b n)

def b_rat : seq ℚ := shift 1 $ λ n, (1+1/n)^(n+1)
def e_seq : seq ℚ := shift 1 $ λ n, (1+1/n)^n

lemma rat.cast_pow {α : Type} [division_ring α] [char_zero α] :
  ∀ a : ℚ, ∀ n : ℕ, ((a^n : ℚ) : α) = (a : α)^n :=
  begin
  intros,
  induction n with n ih,
  simpa,
  simp [has_pow.pow, monoid.pow] at *,
  rw ih,
  end

example : a = coe ∘ e_seq :=
  begin
  apply funext, intro n,
  simp [e_seq, a, shift],
  rwa
    [ rat.cast_pow
    , rat.cast_add
    , rat.cast_one
    , rat.cast_inv
    , rat.cast_add
    , rat.cast_one
    , rat.cast_coe_nat
    ],
  end

lemma binomial_e_seq : ∀ n, e_seq n = binomial.expansion 1 (1/(n+1)) (n+1) :=
  λ n, binomial_theorem 1 (1/(n+1)) (n+1)

lemma binomial_b_rat : ∀ n, b_rat n = binomial.expansion 1 (1/(n+1)) (n+2) :=
  λ n, binomial_theorem 1 (1/(n+1)) (n+2)

def e_seq_incr : ∀ n, e_seq (n+1) > e_seq n :=
  begin
  intro,
  end

-- #check @add_le_add

lemma list.sum_map_le {α : Type} {l : list α} {f g : α → ℚ} :
  (∀ e ∈ l, f e ≤ g e) →
  list.sum (list.map f l) ≤ list.sum (list.map g l) :=
  begin
  intro ha,
  induction l with l0 l ih, simp,
  simp,
  apply add_le_add,
  apply ha, left, refl,
  apply ih, intros e m, apply ha, right, exact m,
  end

lemma helper' {α : Type} {l : list α} {f g : α → ℚ} {c : ℚ} :
  (∃ e ∈ l, c + f e < g e) →
  (∀ e ∈ l, f e ≤ g e) →
  c + list.sum (list.map f l) < list.sum (list.map g l) :=
  begin
  intros he ha,
  induction l with l0 l ih,
  exfalso,
  apply exists.elim he,
  intros e e_mem_nil,
  apply exists.elim e_mem_nil,
  intros e_mem_nil _,
  exact list.not_mem_nil e e_mem_nil,
  simp at he |-,
  apply exists.elim he,
  rintro e ⟨e_here | e_there, e_prop⟩,
  rw e_here at e_prop,
  rw [← add_assoc],
  apply lt_of_le_of_lt,
  apply add_le_add_left,
  show list.sum (list.map f l) ≤ list.sum (list.map g l),
  apply list.sum_map_le,
  intros e m, apply ha, right, exact m,
  apply add_lt_add_right,
  assumption,
  rw [← add_assoc, add_comm c, add_assoc],
  apply lt_of_lt_of_le,
  apply add_lt_add_left,
  apply ih,
  existsi e, existsi e_there, exact e_prop,
  intros e m, apply ha, right, exact m,
  apply add_le_add_right,
  apply ha, left, refl,
  end

@[simp] lemma B_1 : ∀ n, B n 1 = n :=
  begin
  intro n,
  induction n with n ih,
  refl,
  simp [B], rw ih, ring,
  end

@[simp] lemma B_2 : ∀ n, B (n+2) 2 = ((n+2) * (n+1))/2 :=
  begin
  intro n,
  induction n with n ih,
  refl,
  unfold1 B, rw [B_1, ih],
  admit,
  end

-- I stumbled upon the fact that this is true for all n=i
-- It says that one item in the list is sufficiently smaller
-- than the corresponding term in the other list
-- to offset the extra term
#eval ((λ (n i : ℕ), (2 + ↑n : ℚ)⁻¹ ^ (n + 3) + ↑(B (n + 3) (nat.succ i)) * (1 + (1 + ↑n))⁻¹ ^ (n + 2 - i) <
    ↑(B (n + 2) i) * (1 + ↑n)⁻¹ ^ (n + 2 - i)) 6 6 : bool)

def blah (n : ℕ) :
  (2 + ↑n : ℚ)⁻¹ ^ (n + 3) +
  ↑(B (n + 3) (n + 1)) * (1 + (1 + ↑n))⁻¹ ^ (n + 2 - n) <
    ↑(B (n + 2) n) * (1 + ↑n)⁻¹ ^ (n + 2 - n) :=
  begin
  ring,
  rw [B.symm (by norm_num : n+1≤n+3), B.symm (by norm_num : n≤n+2)],
  simp [nat.add_sub_cancel_left],
  admit,
  -- Reasoning:
  --   B (n+3) (n+1) * ((n+2)⁻¹ ^ 2) = (n+3)*(n+2)/2 * ((n+2)⁻¹ ^ 2)
  -- and
  --   B (n+2) n * (n+1)⁻¹ ^ 2 = (n+2)*(n+1)/2 * ((n+1)⁻¹ ^ 2)
  -- So we want
  --   (n+2)⁻¹ ^ (n+3) + (n+3)*(n+2)/2 * ((n+2)⁻¹ ^ 2) < (n+2)*(n+1)/2 * ((n+1)⁻¹ ^ 2)
  -- Clear the (positive) denominators:
  --   2*(n+1)*((n+2)⁻¹ ^ (n+2)) + (n+3)*(n+1) < (n+2)^2
  --   ---------/-----/--------- + n^2 + 4*n + 3 < n^2 + 4*n + 4
  -- And we have
  --   2*(n+1)*((n+2)⁻¹ ^ (n+2))
  -- = 2*((n+1)/(n+2))*((n+2)⁻¹ ^ (n+1))
  -- = 2*((n+2)⁻¹ ^ (n+1))*((n+1)/(n+2))
  -- ≤ 2*(1/2)*((n+1)/(n+2))
  -- = 1*(n+1)/(n+2)
  -- < 1*1 = 1
  -- So this is done.
  end

-- Hm
#eval (λ n i, (B (n + 3) (nat.succ i) : ℚ) * (↑n + 2)⁻¹ ^ (n + 2 - i)
    ≤ ↑(B (n + 2) i) * (↑n + 1)⁻¹ ^ (n + 2 - i) : ℕ → ℕ → bool) 1 0

def b_rat_decr : ∀ n, b_rat (n+1) < b_rat n :=
  begin
  intro n,
  rw [binomial_b_rat, binomial_b_rat],
  unfold binomial.expansion,
  rw [list.range_succ_eq_map],
  simp, ring,
  suffices : (∃ i ∈ list.range (n+3),
    (n + 2 : ℚ)⁻¹ ^ (n + 3) +
      ((λ (i : ℕ), (B (n + 3) i : ℚ) * (1 + (1 + ↑n))⁻¹ ^ (n + 3 - i)) ∘ nat.succ) i
    < (λ (i : ℕ), (B (n + 2) i : ℚ) * (1 + ↑n)⁻¹ ^ (n + 2 - i)) i)
    ∧ (∀ i ∈ list.range (n+3), 
      ((λ (i : ℕ), (B (n + 3) i : ℚ) * (1 + (1 + ↑n))⁻¹ ^ (n + 3 - i)) ∘ nat.succ) i
    ≤ (λ (i : ℕ), (B (n + 2) i : ℚ) * (1 + ↑n)⁻¹ ^ (n + 2 - i)) i),
    {
      exact helper' this.1 this.2,
    },
  simp,
  constructor,
  existsi n,
  constructor,
  norm_num,
  exact blah n,
  intros i i_mem,
  ring,
  show (B (n + 3) (i + 1) : ℚ) * (↑n + 2)⁻¹ ^ (n + 2 - i)
    ≤ ↑(B (n + 2) i) * (↑n + 1)⁻¹ ^ (n + 2 - i),
  -- have: n+2-i ≥ 0
  -- B (n+3) (i+1) * (n+2)⁻¹ ^ (n+2-i)
  -- = list.prod (list.map (λ j, (n+3-j)/(n+2)) (list.range (n+2-i)))
  -- B (n+2) i * (n+1)⁻¹ ^ (n+2-i)
  -- = list.prod (list.map (λ j, (n+2-j)/(n+1)) (list.range (n+2-i)))
  -- and we have
  -- ∀ j ∈ list.range (n+2-i),
  --    (n+3-j)/(n+2) ≤ (n+2-j)/(n+1)
  --  ↔ (n+1)(n+3-j) ≤ (n+2)(n+2-j)
  --  ↔ n^2 + 4*n + 3 - j*(n+1) ≤ n^2 + 4*n + 4 - j*(n+2)
  --  ↔ j ≤ 1
  -- nope, that's not right
  -- I give up ...
  end

def real.e : ℝ := quotient.mk ⟨e_seq,
  begin
  have binomial_b_rat := binomial_b_rat,
  simp [binomial.expansion, list.range_succ_eq_map] at binomial_b_rat,
  intros ε ε_pos,
  admit,
  end⟩

-- ∀ n, b n = a n * (1 + 1/(n+1)) > a n
-- intervals are properly nested since a n increasing, b n decreasing (unproven)
-- thus (set.Inter I = {real.e}), because e is obviously the supremum of
-- the set of a n terms and the infimum of b n terms, since their difference goes to 0

lemma converge : converges_to (a - b) 0 :=
  begin
  rw [converges_to.def],
  have : ∀ (n : ℕ), (a - b) n = (1 + (1 + n : ℝ)⁻¹) ^ (n + 1) * (1 - (1 + (1 + n : ℝ)⁻¹)),
    intro n,
    change (a - b) n with a n - b n,
    unfold a b shift,
    rw
      [ one_div_eq_inv
      , nat.cast_succ
      , add_comm (1 : ℝ) (n : ℝ)
      , mul_sub_left_distrib
      , pow_succ _ (n+1)
      , mul_one
      , mul_comm
      ],
  simp only [this],
  rw [← converges_to.def, ← mul_zero],
  apply converges_to.prod,
  admit, -- a n converges to real.e
  simp,
  admit, -- and -(1 + ↑n)⁻¹ converges to 0, obviously
  exact real.e,
  end

end problem1

namespace problem2

def group_by {α : Type} [topological_space α] [add_monoid α]
  (s : seq α) (n : seq ℕ) : seq α
  | 0 := list.sum (s <$> list.range' 0 (n 0))
  | (i+1) := list.sum (s <$> list.range' (n i) (n (i+1) - n i))

-- This says that summing the terms of s from 0 to n i
-- is the same as summing the terms of (group_by s n) from 0 to i+1
-- (where n must be an increasing function; encoded here as a subsequence of id)
lemma group_by.prop {α : Type} [topological_space α] [add_monoid α]
  (s : seq α) (n : seq ℕ) (Hn : is_subsequence_of (@id ℕ) n) : ∀ i,
  seq.sum s (n i) = seq.sum (group_by s n) (i+1) :=
  begin
  have monotone : ∀ a b, a < b → n a < n b,
    begin
    apply exists.elim Hn,
    rintros f ⟨monote, f_eq_n⟩,
    simp only [id] at f_eq_n,
    have : f = n := funext f_eq_n,
    simp [this] at monote,
    exact monote,
    end,
  intro i,
  unfold seq.sum,
  induction i with i ih,
  simp [list.range, list.range_core, group_by],
  rw [← list.range_eq_range'],
  refl,
  -- rw [list.range'_eq_map_range],
  have range_split : ∀ j, list.range (n (nat.succ j)) = list.range (n j) ++ list.range' (n j) (n (nat.succ j) - n j) :=
    begin
    intro j,
    rw [list.range_eq_range'],
    rw [list.range_eq_range'],
    rw [← zero_add (n j)] { occs := occurrences.pos [2] },
    rw [list.range'_append],
    congr,
    rw [add_comm _ (n _)], symmetry,
    apply nat.add_sub_cancel',
    apply le_of_lt,
    apply monotone,
    apply nat.lt_succ_self,
    end,
  have sum_split : list.sum (s <$> list.range (n (nat.succ i))) =
    list.sum (s <$> list.range (n i)) + list.sum (s <$> list.range' (n i) (n (i+1) - n i)),
    begin
    simp,
    rw [← list.sum_append],
    rw [← list.map_append s],
    congr,
    exact range_split i,
    end,
  transitivity, exact sum_split,
  rw ih,
  have : list.range (nat.succ i + 1) = list.range' 0 (nat.succ i) ++ list.range' (nat.succ i) 1,
    begin
    rw [add_comm],
    rw [← zero_add (nat.succ i)] { occs := occurrences.pos [3] },
    rw [list.range_eq_range'],
    symmetry,
    apply list.range'_append,
    end,
  rw this,
  unfold functor.map,
  rw [list.map_append, list.sum_append],
  congr' 1,
  rw [list.range_eq_range'],
  unfold list.range',
  rw [list.map_singleton, list.sum_cons, list.sum_nil],
  simp [group_by],
  end

lemma proof {α : Type} [metric_space α] [add_monoid α]
  (s : seq α) (l : α)
  (Hs : converges_to (seq.sum s) l)
  -- it's kind of funny that "a subsequence of ℕ" really means
  -- "a subsequence of @id ℕ"
  (n : seq ℕ) (Hn : is_subsequence_of (@id ℕ) n) :
  converges_to (seq.sum (group_by s n)) l :=
  begin
  suffices : converges_to (shift 1 (seq.sum (group_by s n))) l,
    rw [shift.converges_to], exact this,
  rw [converges_to.def] at *,
  intros,
  apply Exists.imp _ (Hs ε H),
  intros a this,
  intros i i_ge_a,
  have monotone : ∀ a b, a < b → n a < n b,
    begin
    apply exists.elim Hn,
    rintros f ⟨monote, f_eq_n⟩,
    simp only [id] at f_eq_n,
    have : f = n := funext f_eq_n,
    simp [this] at monote,
    exact monote,
    end,
  have := this (n i)
    begin
    suffices : ∀ j, n j ≥ j,
      transitivity, apply this, exact i_ge_a,
    intro j,
    induction j with j ih,
    apply nat.zero_le,
    suffices : n (j+1) > n j,
      apply nat.succ_le_of_lt,
      apply lt_of_le_of_lt,
      exact ih, exact this,
    apply monotone,
    apply nat.lt_succ_self,
    end,
  suffices e : seq.sum s (n i) = seq.sum (group_by s n) (i+1),
    rw e at this, exact this,
  apply group_by.prop,
  assumption,
  end

end problem2

namespace problem3

-- Explanation:
-- group_by effects the "adding of parentheses"
-- by grouping many terms of the original series
-- under one term of the new series
-- (thus evaluation will seem to skip many indices
-- of the original sequence); adding even
-- infinite parentheses would produce the same effect,
-- since each top-level parenthesis group counts for one term.

end problem3

namespace problem4

-- This pairs the terms in a sum like
-- (a 0 + a 1) + (a 2 + a 3) + ···
def pairs {α : Type} [has_add α] (s : seq α) : seq α :=
  λ n, s (2*n) + s (2*n+1)

-- This goes 1 - 1 + 1 - 1 + ···
def a : seq ℤ := seq.sum signed
-- This goes (1 - 1) + (1 - 1) + ···
def pairs_a : seq ℤ := seq.sum (pairs signed)

lemma pairs_a_conv : converges_to pairs_a 0 :=
  begin
  -- It is enough to prove that each term is equal to 0
  suffices : ∀ n, pairs signed n = 0,
    begin
    rw [converges_to.def],
    intros, existsi 0, intros,
    -- because then the sum is equal to zero
    have : pairs_a n = 0,
      begin
      unfold pairs_a seq.sum,
      -- `list.repeat` means a list of fixed terms (viz. 0)
      rw [(@list.eq_repeat' ℤ 0 (pairs signed <$> list.range n)).2 _],
      -- so its sum unfolds to a (additive monoid) multiplication of the term
      rwa [list.sum_repeat, add_monoid.smul_zero],
      -- just proving that each term is 0
      simp, intros _ i _ _, have := this i, cc
      end,
    rw [this, dist_self], assumption,
    end,
  intro n,
  unfold pairs a seq.sum,
  rw [signed_even, signed_odd],
  simp,
  end

-- This obvious instance needs to be added
-- for converges_to_zero_of_sum_converges
instance int.normed_group : normed_group ℤ :=
{ norm := λ a, norm (coe a : ℝ)
, dist_eq :=
  begin
  intros,
  change dist x y with dist (coe x) (coe y),
  simp [norm, dist_eq_norm],
  end
}

-- This sum diverges, since its terms do not go to 0
lemma a_div : ¬converges a :=
  begin
  intro conv,
  have := converges_to_zero_of_sum_converges conv,
  rw [converges_to.def] at this,
  -- (1/2) is the easiest 0 < ε < 1
  have := this (1/2) one_half_pos,
  apply exists.elim this, intros N this,
  -- similarly N is the easiest n ≥ N
  have := this N (le_refl N),
  -- simplify ∥1∥, used below
  -- relies on the above instance defining it via coe
  -- (under the hood it has to convert
  -- norm (1 : ℤ) to norm (1 : ℝ), which is defeq)
  have norm_one : norm (1 : ℤ) = 1 :=
    eq.trans (real.norm_eq_abs 1) abs_one,
  -- the semicolon essentially means keep solving
  -- each case with a similar line of argument
  cases signed_cases N;
    -- reduced it to 1 < 2⁻¹
    simp [h, norm_one] at this;
    apply not_lt_of_gt this;
    -- but 2⁻¹ < 1, in fact
    simpa using (@one_half_lt_one ℝ _)
  end

end problem4