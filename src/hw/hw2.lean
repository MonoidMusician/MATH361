import analysis.real tactic.ring
open set

#print lattice.infi
#print is_glb

def bdd (s : set ℝ) := ∃ a b : ℝ, s ⊆ Icc a b

def signed (n : ℕ) : ℤ :=  (-1 : ℤ)^n

lemma signed_cases : ∀ n, (signed n = 1) ∨ (signed n = -1) :=
begin
  intro n, unfold signed,
  cases nat.mod_two_eq_zero_or_one n;
  rw [← nat.mod_add_div n 2, pow_add, pow_mul, h];
  simp [pow_two],
end

lemma signed_even {n : ℕ} : signed (2*n) = 1 :=
  begin
  induction n, refl, unfold signed,
  rw nat.mul_succ, rw pow_succ, rw pow_succ,
  simp, exact n_ih,
  end
lemma signed_odd {n : ℕ} : signed (2*n+1) = -1 :=
  begin
  unfold signed,
  rw pow_succ,
  show -1 * signed (2*n) = -1,
  rw signed_even, refl,
  end

namespace problem1

-- (1) Give an example (with proof) of a countable bounded subset A ⊂ ℝ
--     whose inf and sup are both in ℝ \ A.

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
    have := nat.dvd_of_mod_eq_zero n_mod_2,
    cases this with n',
    admit, admit,
    end,
  admit,
  end

end problem1

namespace problem2

-- (2) If A is a nonempty bounded subset of ℝ, and B is the set of all
--     upper bounds for A, prove: inf B = sup A

open lattice

constant A : set ℝ
constant A_nonempty : A ≠ ∅
constant A_bdd_above : bdd_above A
constant A_bdd_below : bdd_below A
def B : set ℝ := upper_bounds A

#check bdd_above

lemma proof : Inf B = Sup A :=
  begin
  exact cInf_lower_bounds_eq_cSup A_bdd_above A_nonempty,
  end

end problem2

namespace problem3

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

constant A : set ℝ
constant A_nonempty : A ≠ ∅
constant A_bdd_above : bdd_above A
constant A_bdd_below : bdd_below A

lemma proof (a : ℝ) (a_Inf : a = Inf A) (a_Sup : a = Sup A) : A = {a} :=
  begin
  have a_lub : is_lub A a,
    rw a_Sup, constructor,
    simp [upper_bounds],
    intro a, exact le_cSup A_bdd_above,
    simp [lower_bounds, upper_bounds],
    intro a, exact cSup_le A_nonempty,
  have a_glb : is_glb A a,
    rw a_Inf, constructor,
    simp [lower_bounds],
    intro a, exact cInf_le A_bdd_below,
    simp [upper_bounds, lower_bounds],
    intro a, exact le_cInf A_nonempty,
  apply eq_singleton_of_nonempty_of_subset_singleton A_nonempty,
  rw subset_def, simp only [mem_singleton_iff],
  intro x,
  intro x_in_A,
  apply le_antisymm,
  exact a_lub.1 _ x_in_A,
  exact a_glb.1 _ x_in_A,
  end

end problem3

def sequentia (α : Type) := ℕ → α
def converges_to (s : sequentia ℝ) (l : ℝ) :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n > N, dist (s n) l < ε
def converges (s : sequentia ℝ) := Exists (converges_to s)

local infix `⟶`:50 := converges_to

lemma converges_iff_bdd_not_decr (s : sequentia ℝ) :
  bdd_above {x : ℝ | ∃ n, x = s n} → (∀ n, s n ≤ s (n+1)) → converges s := sorry

lemma converges_to_cSup (s : sequentia ℝ) : (∀ n, s n ≤ s (n+1)) → s ⟶ lattice.Sup {x : ℝ | ∃ n, x = s n} := sorry

namespace problem5

-- (5) Prove that if {|sn|}∞n=1 converges to 0 then {sn}∞n=1 converges to 0 also.

lemma proof (s : sequentia ℝ) : abs ∘ s ⟶ 0 ↔ s ⟶ 0 :=
  begin
  simp [converges_to],
  suffices : ∀ n, dist (abs (s n)) 0 = dist (s n) 0, simp only [this],
  intro n, rw real.dist_0_eq_abs, rw real.dist_0_eq_abs,
  exact abs_abs _,
  end

end problem5

def alternating (s : sequentia ℝ) : sequentia ℝ := λ n, signed n * s n

namespace problem6

-- (6) Suppose {sn}∞n=1 converges to 0. Prove that {(−1)^n*sn}∞n=1 converges to 0 also.

lemma proof (s : sequentia ℝ) : s ⟶ 0 ↔ alternating s ⟶ 0 :=
  begin
  simp [converges_to],
  suffices : ∀ n, dist (s n) 0 = dist (alternating s n) 0, simp only [this],
  intro n, rw real.dist_0_eq_abs, rw real.dist_0_eq_abs,
  simp [alternating],
  cases signed_cases n; simp [h]
  end

end problem6

namespace problem7

-- (7) Suppose {sn}∞n=1 is a sequence of positive numbers with the property that sn+1 < (1/2)sn for all n ∈ N. Prove that limn→∞ sn = 0. How would you change your proof if 1/2 was replaced by a fixed number x ∈ (0, 1)?

variable r : ℝ
variable r_in_0_1 : r ∈ (Ioo 0 1 : set ℝ)

def powℝ (b : ℝ) (p : ℝ) : ℝ := sorry
def log_base (b : ℝ) (x : ℝ) : ℝ := sorry
lemma log_pow (b p : ℝ) : log_base b (powℝ b p) = p := sorry
lemma pow_log (b p : ℝ) : powℝ b (log_base b p) = p := sorry

include r_in_0_1
lemma proof (s : sequentia ℝ) : (∀ n, abs (s (n+1)) < r*abs (s n)) → s ⟶ 0 :=
  begin
  intro prop,
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
  -- solve: (r^n * s 0 < ε) ← (n > log_base r (ε / s 0)), with 0 < r < 1
  intros ε ε_pos,
  have get_N := exists_nat_gt (log_base r (ε / abs (s 0))),
  apply exists_imp_exists _ get_N,
  intro N, intro N_gt, intro n, intro n_gt,
  rw real.dist_0_eq_abs,
  apply lt_of_le_of_lt,
  exact this n,
  have : (N : ℝ) < (n : ℝ), rw nat.cast_lt, exact n_gt,
  have := lt_trans N_gt this,
  suffices finishing : log_base r (ε / abs (s 0)) < n → r ^ n * abs (s 0) < ε,
    exact finishing this,
  admit,
  end

end problem7


namespace problem9

-- sorry constructivism ... I tried
noncomputable theory
open real

-- (9) Let s1 = √2 and let sn+1 = √2 ·√sn for n ≥ 1.
--     (a) Prove, by induction, that sn ≤ 2 for all n.
--     (b) Prove that sn+1 ≥ sn for all n.
--     (c) Prove that {sn}∞n=1 is convergent.
--     (d) Prove that limn→∞ sn = 2.

noncomputable def s : sequentia ℝ
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

lemma part_c : converges s :=
  begin
  apply converges_iff_bdd_not_decr,
  existsi (2 : ℝ), simp, intros y x y_x, rw y_x, exact part_a x,
  intro n, exact le_of_lt (part_b n),
  end

lemma blah {a b c : ℝ} : c - a < c - b → a > b := le_imp_le_iff_lt_imp_lt.1 (λ h, sub_le_sub_left h _)

lemma decr (s : sequentia ℝ) : (∀ n, 0 < s n) → (∀ n, s (n+1) < s n) → s ⟶ 0 := well_founded.fix

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
  end

end problem9