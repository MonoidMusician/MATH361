import analysis.real tactic.ring tactic.interactive
import seq naturally background

open set

namespace hw2

namespace problem1

-- (1) Give an example (with proof) of a countable bounded subset A ⊂ ℝ
--     whose inf and sup are both in ℝ \ A.

-- I'm going to start with the harmonic sequence, bounded between 0 and 1
-- (but never reaching a value of 0).
def harmonic := {x : ℝ | ∃ n:ℕ+, x = 1/n}

def harmonic_inf : ℝ := 0
def harmonic_sup : ℝ := 1

lemma harmonic_inf_proof : is_glb harmonic harmonic_inf :=
  begin
  unfold is_glb is_greatest lower_bounds upper_bounds,
  constructor,
  show ∀ (a : ℝ), a ∈ harmonic → harmonic_inf ≤ a,
  simp [harmonic],
  suffices : ∀ (x : ℕ+), (0 : ℝ) ≤ (↑↑x)⁻¹,
    intro a, intro x, intro a_x, rw a_x, exact this x,
  intro x, apply le_of_lt, apply inv_pos,
  cases x, simp, exact x_property,
  simp [harmonic, harmonic_inf],
  intro a, intro a_lb,
  apply le_of_not_lt, intro a_pos,
  let := exists_nat_gt (a⁻¹),
  apply exists.elim this, intros n h,
  have : (n : ℝ) > 0, transitivity, exact h, exact inv_pos a_pos,
  have : n > 0, rw [← nat.cast_zero] at this, exact nat.cast_lt.1 this,
  have h' := (inv_lt_inv _ _).2 h, rw @inv_inv' _ _ a at h',
  have := a_lb _ ⟨n, _⟩ rfl, simp at this,
  have := lt_of_le_of_lt this h',
  exact lt_irrefl a this, cc,
  show ↑n > (0 : ℝ), cc,
  apply inv_pos a_pos,
  end

lemma harmonic_sup_proof : is_lub harmonic harmonic_sup :=
  begin
  unfold is_lub is_least upper_bounds lower_bounds,
  constructor,
  show ∀ (a : ℝ), a ∈ harmonic → a ≤ 1,
  unfold harmonic, simp,
  suffices : ∀ (x : ℕ+), (↑↑x)⁻¹ ≤ (1 : ℝ),
    intro a, intro x, intro a_x, rw a_x, exact this x,
  intro x, cases x, simp,
  cases x_val, exfalso, exact ne_of_lt x_property rfl,
  induction x_val with n ih, exact le_of_eq inv_one,
  transitivity,
  refine (inv_le_inv _ _).2 _,
  exact ↑(nat.succ n),
  suffices : 0 < n + 2,
    rw [← nat.cast_zero],
    exact nat.cast_lt.2 this,
  exact nat.zero_lt_succ _,
  suffices : 0 < n + 1,
    rw [← nat.cast_zero],
    exact nat.cast_lt.2 this,
  exact nat.zero_lt_succ _,
  rw nat.cast_le, exact nat.le_succ _,
  exact ih (nat.zero_lt_succ _),
  simp [harmonic, harmonic_sup],
  intro a, intro a_ub,
  have a_ub_1 := a_ub _ 1 rfl, simp at a_ub_1,
  exact a_ub_1,
  end

-- And if we make it alternate sign, then it will approach ±1, but
-- never reach those
def A := {x:ℝ | ∃ n:ℕ+, x = signed n * (1 - 1/n)}

def A_inf : ℝ := -1
def A_sup : ℝ := 1

lemma A_inf_proof : is_glb A A_inf :=
  begin
  unfold is_glb is_greatest lower_bounds upper_bounds,
  constructor,
  show ∀ (a : ℝ), a ∈ A → -1 ≤ a,
  unfold A, simp,
  suffices : ∀ (n : ℕ+), (-1 : ℝ) ≤ signed n * (1 - (n : ℝ)⁻¹),
    intro a, intro x, intro a_x, rw a_x, exact this x,
  intro n,
  have n_mod_2 := nat.mod_two_eq_zero_or_one n,
  cases n_mod_2,
  have := nat.dvd_of_mod_eq_zero n_mod_2,
  cases this with n', rw this_h, rw signed_even,
  suffices : (↑(2 * n') : ℝ)⁻¹ ≤ 1,
    simp, simp at this,
    apply le_add_of_neg_add_le, ring, apply neg_le_neg,
    simp [this_h],
    transitivity, exact this, exact le_of_lt one_lt_two,
  apply harmonic_sup_proof.1, simp [harmonic],
  existsi n, simp [this_h],
  rw [← nat.mod_add_div n 2, n_mod_2],
  rw [add_comm 1 _, signed_odd], simp,
  apply harmonic_inf_proof.1,
  existsi n, simp,
  simp [A_inf], intro a, simp [A], intro a_lb,
  have := harmonic_inf_proof.2 (a+1)
    begin
    intros v v_h,
    apply exists.elim v_h, intros n n_h, rw n_h,
    have n_mod_2 := nat.mod_two_eq_zero_or_one n,
    cases n_mod_2,
    {
      have := nat.dvd_of_mod_eq_zero n_mod_2,
      cases this with n',
      apply add_le_of_le_sub_right,
      transitivity,
      apply a_lb _ (2*n'+1).to_pnat' rfl,
      rw [(@pnat.to_pnat'_coe (2*n'+1) dec_trivial)],
      rw [signed_odd, int.cast_neg, int.cast_one, ← this_h],
      simp, rw inv_le_inv,
      apply le_add_of_sub_right_le, simp, exact zero_le_one,
      rw [← nat.cast_zero, ← nat.cast_one, ← nat.cast_add, nat.cast_lt, add_comm],
      exact nat.zero_lt_succ _,
      rw [← nat.cast_zero, nat.cast_lt],
      exact pnat.pos n,
    }, {
      have : (n : ℕ) = 2*(n/2)+1,
        begin
        transitivity,
        symmetry,
        exact nat.mod_add_div n 2,
        rw [add_comm, n_mod_2],
        end,
      apply add_le_of_le_sub_right,
      transitivity,
      apply a_lb _ (2*(↑n/2)+1 : ℕ).to_pnat' rfl,
      rw [(@pnat.to_pnat'_coe (2*(↑n/2)+1 : ℕ) dec_trivial)],
      rw [signed_odd, ← this, int.cast_neg, int.cast_one],
      simp,
    }
    end,
  transitivity,
  apply le_add_of_sub_left_le,
  rw [← neg_neg (1 : ℝ)] at this,
  exact this,
  simp [harmonic_inf],
  end

end problem1

namespace problem2

-- (2) If A is a nonempty bounded subset of ℝ, and B is the set of all
--     upper bounds for A, prove: inf B = sup A

open lattice

-- this is kind of ugly, mixing variables and constants
-- I think it forces me to annotate the types of the sets
-- (so it knows what the variable α should be),
-- but I think that's better than parameterizing B over A.
variable {α : Type}
variable [_inst_1 : conditionally_complete_lattice α]
constant A : set α
constant A_nonempty : (A : set α) ≠ ∅
constant A_bdd_above : bdd_above (A : set α)
constant A_bdd_below : bdd_below (A : set α)
def B : set α := upper_bounds A

-- The implementation of is_lub is instructive
#print is_lub
#print is_least
-- That is, a least upper bound is an upper bound which is
-- a lower bounds on the upper bounds.
-- So it makes sense that Inf B and Sup A both represent the
-- exact boundary between these sets, informally speaking,
-- so they will be equal.

-- This already exists
#check exists_mem_of_ne_empty
#check cInf_lower_bounds_eq_cSup
-- Here's another proof of it
lemma proof : Inf (B : set α) = Sup (A : set α) :=
  begin
  -- B is bounded below by Sup A, since B consists of upper bounds
  -- and Sup A is the _least_ upper bound.
  have B_bdd_below : bdd_below (B : set α),
    begin
    unfold B upper_bounds,
    existsi (Sup (A : set α)), intros y y_upper_bound,
    simp at y_upper_bound,
    apply cSup_le A_nonempty y_upper_bound,
    end,
  -- B is nonempty, from the proof that A is bounded above.
  have B_nonempty : (B : set α) ≠ ∅ :=
    set.ne_empty_iff_exists_mem.2 A_bdd_above,
  apply le_antisymm,
  {
    -- Inf B ≤ Sup A since Sup A ∈ B and Inf is a lower bound
    apply cInf_le B_bdd_below,
    simp [B, upper_bounds],
    intros a a_mem_A,
    exact le_cSup A_bdd_above a_mem_A,
  }, {
    -- Sup A ≤ Inf B since Inf is the greatest lower bound of B and
    -- Sup A is a lower bound of B (aka the upper bounds of A)
    apply le_cInf B_nonempty,
    intros b b_mem_B,
    apply cSup_le A_nonempty,
    intros a a_mem_A,
    exact b_mem_B a a_mem_A,
  },
  end

end problem2

namespace problem3

-- Helper lemma
lemma eq_singleton_of_nonempty_of_subset_singleton
  {α : Type} {A : set α} {a : α} : A ≠ ∅ → A ⊆ {a} → A = {a} :=
  begin
  intro A_nonempty, intro A_subset_singleton,
  rw subset_def at A_subset_singleton,
  have := exists_mem_of_ne_empty A_nonempty,
  apply exists.elim this, intros b b_mem,
  apply set.ext,
  intro x,
  constructor,
  exact A_subset_singleton x,
  intro x_mem, rw mem_singleton_iff at x_mem, rw x_mem,
  have : b = a := eq_of_mem_singleton (A_subset_singleton _ b_mem),
  rw this at b_mem, exact b_mem,
  end

-- (3) If A is a nonempty bounded subset of R and inf A = sup A, what can you say about A? Give proof.

open lattice

variable {α : Type}
variable [_inst_1 : conditionally_complete_lattice α]
constant A : set α
constant A_nonempty : (A : set α) ≠ ∅
constant A_bdd_above : bdd_above (A : set α)
constant A_bdd_below : bdd_below (A : set α)

-- A must be a singleton set {a}, thus a = Inf A = Sup A
lemma proof (a : α) (a_Inf : a = Inf A) (a_Sup : a = Sup A) : (A : set α) = {a} :=
  begin
  -- a must be the least upper bound
  have a_lub : is_lub A a,
    rw a_Sup, constructor,
    simp [upper_bounds],
    intro a, exact le_cSup A_bdd_above,
    simp [lower_bounds, upper_bounds],
    intro a, exact cSup_le A_nonempty,
  -- and the greatest lower bound
  have a_glb : is_glb A a,
    rw a_Inf, constructor,
    simp [lower_bounds],
    intro a, exact cInf_le A_bdd_below,
    simp [upper_bounds, lower_bounds],
    intro a, exact le_cInf A_nonempty,
  apply eq_singleton_of_nonempty_of_subset_singleton A_nonempty,
  rw subset_def, simp only [mem_singleton_iff],
  -- we need to show that any element x in the set is just a
  intro x,
  intro x_in_A,
  -- so we show it is ≤ a and ≥ a, since a is sup and inf
  apply le_antisymm,
  exact a_lub.1 _ x_in_A,
  exact a_glb.1 _ x_in_A,
  end

end problem3

namespace problem4

-- (4) Prove that the sequence {n − 1/n}∞n=1 does not have a limit.
noncomputable def s : seq ℝ := λ n, n - n⁻¹

lemma s_pos : ∀ n, s (n+2) > 0 :=
  begin
  intro n, unfold s,
  rw [← sub_self (2 : ℝ)],
  apply sub_lt_sub_of_le_of_lt,
  natureally,
  apply lt_of_le_of_lt,
  apply problem1.harmonic_sup_proof.1,
  simp [problem1.harmonic],
  existsi (⟨n+2, nat.succ_pos _⟩ : ℕ+),
  simp,
  simp only [problem1.harmonic_sup], natureally,
  end

-- It suffices to show that the sequence is not bounded, so,
-- given a real number, illustrate an index where the sequence
-- is actually larger than it.
lemma proof : ¬converges s :=
  begin
  intro c, exfalso,
  suffices : ¬∃ M, ∀ n, M > norm (s n),
    exact this (bounded_of_converges c),
  intro ex, apply exists.elim ex, intros M bound,
  simp [s, real.norm_eq_abs] at bound,
  cases h : ceil M,
    -- if the ceiling is a positive value a, use a+2 as the index.
    have : M ≤ abs (↑(a+2) + -(↑(a+2))⁻¹),
      begin
      rw abs_of_pos,
      transitivity,
      exact le_ceil M, rw h,
      simp,
      apply le_of_sub_nonneg, simp,
      rw [← sub_self (1 : ℝ), ← sub_eq_add_neg],
      apply sub_le_sub, exact le_of_lt one_lt_two,
      apply problem1.harmonic_sup_proof.1,
      simp [problem1.harmonic],
      existsi (⟨a+2, nat.succ_pos _⟩ : ℕ+),
      simp,
      apply s_pos,
      end,
      exact not_le_of_gt (bound (a+2)) this,
    -- otherwise, if it is negative, use the index 0
    have : M < 0,
      begin
      apply lt_of_le_of_lt,
      exact le_ceil M, rw h,
      rw [int.cast_lt_zero],
      unfold has_lt.lt int.lt,
      rw [int.neg_succ_of_nat_eq'],
      simp,
      end,
      exact not_lt_of_gt this (lt_of_le_of_lt (abs_nonneg _) (bound 0)),
  end

end problem4

local infix `⟶`:50 := converges_to

lemma converges_iff_bdd_not_decr (s : seq ℝ) :
  bdd_above {x : ℝ | ∃ n, x = s n} → (∀ n, s n ≤ s (n+1)) → converges s := sorry

lemma converges_to_cSup (s : seq ℝ) : (∀ n, s n ≤ s (n+1)) → s ⟶ lattice.Sup {x : ℝ | ∃ n, x = s n} := sorry

namespace problem5

-- (5) Prove that if {|sn|}∞n=1 converges to 0 then {sn}∞n=1 converges to 0 also.

-- This can actually be a biconditional; it is true almost by definition.
lemma proof (s : seq ℝ) : abs ∘ s ⟶ 0 ↔ s ⟶ 0 :=
  begin
  simp [converges_to.def],
  suffices : ∀ n, norm (abs (s n)) = norm (s n), simp only [this],
  intro n, rw real.norm_eq_abs, rw real.norm_eq_abs,
  exact abs_abs _,
  end

end problem5

noncomputable def alternating (s : seq ℝ) : seq ℝ := λ n, signed n * s n

namespace problem6

-- (6) Suppose {sn}∞n=1 converges to 0. Prove that {(−1)^n*sn}∞n=1 converges to 0 also.

-- This again is a biconditional along the same lines.
lemma proof (s : seq ℝ) : s ⟶ 0 ↔ alternating s ⟶ 0 :=
  begin
  simp only [converges_to.def],
  suffices : ∀ n, dist (s n) 0 = dist (alternating s n) 0, simp only [this],
  intro n, rw real.dist_0_eq_abs, rw real.dist_0_eq_abs,
  simp [alternating],
  cases signed_cases n; simp [h]
  end

end problem6

namespace problem7

-- (7) Suppose {sn}∞n=1 is a sequence of positive numbers with the property that sn+1 < (1/2)sn for all n ∈ N. Prove that limn→∞ sn = 0. How would you change your proof if 1/2 was replaced by a fixed number x ∈ (0, 1)?

-- So it's actually easier if I do the more abstract version ...
variable r : ℝ
variable r_in_0_1 : r ∈ (Ioo 0 1 : set ℝ)

-- whoops, we don't have these functions ...
def powℝ (b : ℝ) (p : ℝ) : ℝ := sorry
def log_base (b : ℝ) (x : ℝ) : ℝ := sorry
lemma log_pow (b p : ℝ) : log_base b (powℝ b p) = p := sorry
lemma pow_log (b p : ℝ) : powℝ b (log_base b p) = p := sorry

include r_in_0_1
lemma proof (s : seq ℝ) : (∀ n, abs (s (n+1)) < r*abs (s n)) → s ⟶ 0 :=
  begin
  simp only [converges_to.def],
  intro prop,
  -- This uses transitivity to compare it with a geometric sequence
  have : ∀ n, abs (s n) ≤ r^n * abs (s 0),
    intro n,
    cases n with n, simp,
    induction n with n ih,
    { have := prop 0, apply le_of_lt, simpa },
    transitivity,
    apply le_of_lt,
    apply prop,
    rw pow_succ r,
    rw mul_assoc,
    apply (mul_le_mul_left r_in_0_1.1).2,
    exact ih,
  -- now we just need to ensure it is less than ε
  -- solve: (r^n * s 0 < ε) ← (n > log_base r (ε / s 0)), with 0 < r < 1
  intros ε ε_pos,
  have get_N := exists_nat_gt (log_base r (ε / abs (s 0))),
  apply exists_imp_exists _ get_N,
  intro N, intro N_gt, intro n, intro n_ge,
  rw real.dist_0_eq_abs,
  apply lt_of_le_of_lt,
  exact this n,
  have : (N : ℝ) ≤ (n : ℝ), rw nat.cast_le, exact n_ge,
  have := lt_of_lt_of_le N_gt this,
  suffices finishing : log_base r (ε / abs (s 0)) < n → r ^ n * abs (s 0) < ε,
    exact finishing this,
  -- can't prove this in Lean
  admit,
  end

end problem7


namespace problem8

noncomputable theory

-- (8) Suppose limn→∞ (s n − 1)/(s n + 1) = 0. Prove that limn→∞ s n = 1.
variable (s : seq ℝ)
def ratio : seq ℝ := λ n, (s n - 1)/(s n + 1)

open classical
local attribute [instance] prop_decidable

-- I don't know how to show that it converges ...
-- but assuming it converges, and is never equal to -1,
-- and does not approach -1, it would be easy enough
-- to appeal to the algebraic limit theorems to say that
--   lim (s n - 1) = 0 * lim (s n + 1) = 0
--   lim s n = 0 + 1 = 1
lemma proof : (ratio s ⟶ 0) → (s ⟶ 1) := sorry

end problem8

namespace problem9

-- sorry constructivism ... I tried
noncomputable theory
open real

-- (9) Let s1 = √2 and let sn+1 = √2 ·√sn for n ≥ 1.
--     (a) Prove, by induction, that sn ≤ 2 for all n.
--     (b) Prove that sn+1 ≥ sn for all n.
--     (c) Prove that {sn}∞n=1 is convergent.
--     (d) Prove that limn→∞ sn = 2.

noncomputable def s : seq ℝ
| 0 := 1
| (n+1) := sqrt 2 * sqrt (s n)
@[simp] lemma s_0 : s 0 = 1 := rfl
@[simp] lemma s_1 : s 1 = sqrt 2 := by simp [s]
@[simp] lemma s_succ_n : ∀ n, s (n+1) = sqrt 2*sqrt (s n) :=
  by intro n; unfold s

lemma s_pos : ∀ n, 0 < s n :=
  begin
  intro n, induction n with n ih,
  exact zero_lt_one, simp,
  have : 0 < sqrt (s n),
    rw sqrt_pos, exact ih,
  apply mul_pos _ this,
  show 0 < sqrt 2, rw sqrt_pos, exact two_pos,
  end


-- The base case reduces to this ... not fun.
lemma ugh : sqrt (2 * sqrt 2) ≥ 3/2 :=
  begin
  rw [← @sqrt_sqr (3/2)],
  apply (sqrt_le _ _).2,
  unfold pow monoid.pow, simp, rw [div_mul_div, mul_comm _ (sqrt 2)],
  apply le_mul_of_div_le two_pos, ring,
  rw [← @sqrt_sqr (9/8)],
  apply (sqrt_le _ _).2,
  unfold pow monoid.pow, ring,
  apply div_le_of_le_mul,
  show (81 : ℝ) ≤ 64 * 2,
  transitivity,
  { show (81 : ℝ) ≤ 128, norm_num, natureally },
  { apply le_of_eq, ring },
  show 0 ≤ 2 * sqrt 2,
  {
    apply mul_nonneg, tactic.swap, apply sqrt_nonneg, repeat { exact le_of_lt two_pos },
  },
  any_goals { unfold pow monoid.pow, rw [mul_one, div_mul_div] },
  all_goals { norm_num },
  end

-- Trust me, this looks a lot easier since I created natureally.
lemma sigh : ∀ (n : ℕ), @has_le.le ℝ _ ((n+2)+2*(n+3)^2) (4*(n+2)*(n+3)) :=
    begin
    intro n,
    ring, rw [right_distrib, right_distrib],
    apply le_of_sub_nonneg,
    ring, natureally
    end

-- This is the main lemma for proving that s converges to 2
-- by comparing it to the easy harmonic sequence.
-- 2 - s n < ε ... n > 1/ε
lemma s_sup : ∀ n : {n : ℕ // n > 1}, s n ≥ 2 - 1/n :=
  begin
  intro n,
  cases n with n n_pos,
  cases n, exfalso, exact not_lt_of_ge (nat.zero_le 1) n_pos,
  cases n, exfalso, exact lt_irrefl 1 n_pos,
  induction n with n ih,
  simp, rw [← sqrt_mul (le_of_lt two_pos), one_add_one_eq_two],
  have : @eq ℝ (2 + -2⁻¹) (3/2),
  {
    apply eq_div_of_mul_eq _ _ two_ne_zero,
    rw [right_distrib, neg_mul_eq_neg_mul_symm, inv_mul_cancel two_ne_zero],
    refl,
  },
  rw this,
  exact ugh,
  simp,
  have n_1_1 : @eq ℝ (1 + (1 + ↑n)) ↑(n+2),
  {
    natureally, simp,
  },
  rw n_1_1,
  have m_1 : ∀ (m : ℕ), @eq ℝ (1 + ↑m) ↑(m+1),
  {
    intro m,
    natureally, simp,
  },
  have n_2 : @eq ℝ (2 + ↑n) ↑(n+2),
  {
    natureally, simp,
  },
  rw m_1 (n+2),
  show (2 : ℝ) + -(↑(n + 3))⁻¹ ≤ sqrt 2 * sqrt (sqrt 2 * sqrt (sqrt 2 * sqrt (s n))),
  have ih' := mul_le_mul (le_refl (sqrt 2)) ((sqrt_le _ _).2 (ih dec_trivial)) _ _,
  simp at ih',
  rw n_1_1 at ih',
  refine le_trans _ ih',
  rw ← sqrt_mul, transitivity, apply le_of_eq, symmetry,
  apply sqrt_sqr _, tactic.swap,
  rw sqrt_le,
  unfold pow monoid.pow, simp,
  rw [left_distrib, right_distrib],
  ring, apply add_le_add_right,
  rw [← neg_sub, neg_mul_eq_neg_mul_symm],
  apply neg_le_neg,
  rw [sub_mul], apply le_sub_left_of_add_le,
  ring,
  rw [← @div_eq_mul_inv ℝ _ 4],
  apply le_div_of_mul_le _,
  rw [right_distrib],
  unfold pow monoid.pow, simp,
  rw [mul_assoc (3 + ↑n : ℝ)⁻¹, inv_mul_cancel, mul_one],
  rw [mul_assoc, mul_comm _⁻¹, ← mul_assoc],
  apply add_le_of_le_sub_right,
  rw [← div_eq_mul_inv],
  apply div_le_of_le_mul _,
  simp, rw [left_distrib (2 + ↑n : ℝ), ← neg_mul_eq_mul_neg, ← sub_eq_add_neg],
  apply le_sub_left_of_add_le,
  apply add_le_of_le_sub_right,
  rw [← div_eq_mul_inv],
  apply div_le_of_le_mul _,
  simp, rw [left_distrib (3 + ↑n : ℝ), ← neg_mul_eq_mul_neg, ← sub_eq_add_neg],
  apply le_sub_left_of_add_le,
  refine eq.mp _ (sigh n),
  { unfold pow monoid.pow, simp, ring, },
  -- ugly tactics to kill off the remaining goals en masse
  any_goals {
    try { unfold pow monoid.pow },
    simp,
  },
  any_goals { unfold gt },
  any_goals { iterate { apply sqrt_nonneg <|> apply mul_nonneg } },
  any_goals { unfold ge },
  any_goals {
    try { rw [add_comm _ (n : ℕ)] <|> rw [add_comm _ (n : ℝ)] },
    natureally,
  },
  all_goals {
    have : ∀ m : ℕ, ((2 : ℕ) : ℝ) + -(nat.succ m : ℝ)⁻¹ ≥ ↑0,
    {
      intro m,
      rw [← sub_eq_add_neg],
      apply le_sub_left_of_add_le,
      rw [nat.cast_zero, add_zero],
      transitivity,
      show (nat.succ m : ℝ)⁻¹ ≤ 1,
      rw [← @inv_inv' ℝ _ 1, inv_le_inv, inv_one, ← nat.cast_one, nat.cast_le],
      exact nat.zero_lt_succ m,
      rw [← nat.cast_zero, nat.cast_lt],
      exact nat.zero_lt_succ m,
      rw [inv_one],
      exact zero_lt_one,
      exact le_of_lt two_gt_one,
    },
    exact this _,
  }
  end

-- Easy enough to show that is is bounded above by 2.
lemma part_a : ∀ n, s n ≤ 2 :=
  begin
  intro n, induction n with n ih,
  simp, exact le_of_lt one_lt_two,
  simp,
  have : sqrt (s n) ≤ sqrt 2,
    rw sqrt_le, exact ih,
    apply le_of_lt, exact s_pos n,
    apply le_of_lt, exact two_pos,
  transitivity,
  have sqrt_two_pos : 0 < sqrt 2, rw sqrt_pos, exact two_pos,
  apply (mul_le_mul_left sqrt_two_pos).2, exact this,
  rw mul_self_sqrt, apply le_of_lt, exact two_pos,
  end

-- And always increasing (strictly!).
lemma part_b : ∀ n, s n < s (n+1) :=
  begin
  intro n, induction n with n ih,
  simp, apply lt_of_le_of_lt, exact le_of_eq (eq.symm sqrt_one),
  rw sqrt_lt, exact two_gt_one,
  apply le_of_lt, exact zero_lt_one,
  apply le_of_lt, exact two_pos,
  simp,
  have sqrt_two_pos : 0 < sqrt 2, rw sqrt_pos, exact two_pos,
  apply (mul_lt_mul_left sqrt_two_pos).2, rw sqrt_lt,
  simp at ih,
  exact ih,
  exact le_of_lt (s_pos n),
  have := le_of_lt (s_pos (n+1)), simpa
  end

-- So it must converge!
lemma part_c : converges s :=
  begin
  apply converges_iff_bdd_not_decr,
  existsi (2 : ℝ), simp, intros y x y_x, rw y_x, exact part_a x,
  intro n, exact le_of_lt (part_b n),
  end

lemma blah {a b c : ℝ} : c - a < c - b → a > b := le_imp_le_iff_lt_imp_lt.1 (λ h, sub_le_sub_left h _)

-- And we use the stuff above to show that it converges to 2.
lemma part_d : s ⟶ 2 :=
  begin
  suffices : Sup {x : ℝ | ∃ (n : ℕ), x = s n} = 2,
    rw ← this, apply converges_to_cSup,
    intro n, exact le_of_lt (part_b n),
  apply lattice.cSup_intro,
  apply ne_empty_of_mem, apply exists.intro 0, refl,
  intros a a_mem, apply exists.elim a_mem, intros n a_n, rw a_n,
  exact part_a n,
  intros w w_lt_2, simp,
  suffices : ∀ ε, ε > 0 → ∃ n, (2 - s n) < ε,
    apply exists.elim (this (2 - w) (sub_pos.2 w_lt_2)), intros n c,
    existsi s n, constructor, existsi n, refl,
    apply blah c,
  intros ε ε_pos,
  apply exists.elim (exists_nat_gt (1/ε)),
  intro n, intro n_gt,
  existsi max n 2,
  have nmax_gt : ↑(max n 2) > 1/ε,
    apply lt_of_lt_of_le, exact n_gt, rw nat.cast_le, apply le_max_left,
  apply lt_of_le_of_lt,
  apply sub_le_of_sub_le,
  apply s_sup ⟨max n 2, _⟩,
  apply lt_of_lt_of_le,
  show 1 < 2, exact nat.le_refl 2,
  exact le_max_right n 2,
  simp at *, rw [← @inv_inv' _ _ ε, inv_lt_inv],
  exact nmax_gt,
  apply lt_of_lt_of_le,
  show (0 : ℝ) < 2, natureally,
  exact le_max_right n 2,
  exact inv_pos ε_pos,
  end

end problem9

end hw2
