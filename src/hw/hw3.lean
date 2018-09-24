import analysis.real tactic.ring tactic.interactive
import seq naturally background

namespace problem1

noncomputable theory

def a : seq ℝ := λ n, (1+1/(1+n))^n
def b : seq ℝ := a ∘ nat.succ
def I : seq (set ℝ) := λ n, set.Icc (a n) (b n)

def real.e_seq : seq ℚ := λ n, (1+1/(1+n))^n
def real.e : ℝ := take_limit real.e_seq
  begin
  end

#check set.Inter I = {real.e}

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
end problem3

namespace problem4

-- This pairs the terms in a sum like
-- (a 1 + a 2) + (a 3 + a 4) + ···
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