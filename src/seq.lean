-- Definitions and theorems relating to sequences
import analysis.real analysis.normed_space
import algebra.big_operators
import tactic.ring

-- The type for a sequence: a function whose domain is ℕ
def seq := (→) ℕ

-- Lift operations to sequences
instance seq.has_zero {α : Type} [has_zero α] : has_zero (seq α) :=
{ zero := λ n, (0 : α) }
instance seq.has_one {α : Type} [has_one α] : has_one (seq α) :=
{ one := λ n, (1 : α) }
instance seq.has_add {α : Type} [has_add α] : has_add (seq α) :=
{ add := λ s z n, s n + z n }
instance seq.has_mul {α : Type} [has_mul α] : has_mul (seq α) :=
{ mul := λ s z n, s n * z n }
instance seq.has_sub {α : Type} [has_sub α] : has_sub (seq α) :=
{ sub := λ s z n, s n - z n }
instance seq.has_neg {α : Type} [has_neg α] : has_neg (seq α) :=
{ neg := λ s n, has_neg.neg (s n) }
instance seq.has_inv {α : Type} [has_inv α] : has_inv (seq α) :=
{ inv := λ s n, has_inv.inv (s n) }
instance seq.add_monoid {α : Type} [add_monoid α] : add_monoid (seq α) :=
{ add := (+), zero := 0
, add_assoc := by intros; apply funext; intro; simp
, zero_add := begin intros; apply funext; intro; simp,
  show 0 + a x = a x, simp,
  end
, add_zero := begin intros; apply funext; intro; simp,
  show a x + 0 = a x, simp,
  end
}

instance seq.add_group {α : Type} [add_group α] : add_group (seq α) :=
{ neg := has_neg.neg
, add_left_neg := by intros; apply funext; intro; simpa
, ..seq.add_monoid
}

def shift {α : Type} (m : ℕ) (s : seq α) : seq α :=
  λ n, s (n + m)

def seq.sum {α : Type} (s : seq α) [add_monoid α] : seq α :=
  λn, list.sum (s <$> list.range n)

-- A topological definition of converging to a point.
-- (Based off a term spotted in analysis.limits in mathlib.)
def converges_to
  {α : Type} [topological_space α]
  (s : seq α) (l : α) : Prop :=
  filter.tendsto s filter.at_top (nhds l)

-- Convergence, without giving the limit specifically.
def converges
  {α : Type} [topological_space α]
  (s : seq α) : Prop := ∃ l, converges_to s l

-- The above definition is equivalent to the more familiar definition.
lemma converges_to.def
  {α : Type} [metric_space α]
  (s : seq α) (l : α) :
  converges_to s l ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (s n) l < ε :=
  -- this is mostly unfolding some definitions, but it includes some simp magic
  by simp
    [ converges_to
    , nhds_eq_metric, ball
    , filter.tendsto_infi
    , filter.tendsto_principal
    ]

lemma converges_to.unique
  {α : Type} [metric_space α]
  (s : seq α) (l₁ l₂ : α) :
  converges_to s l₁ → converges_to s l₂ → ¬¬(l₁ = l₂) :=
  begin
  intros c1 c2,
  suffices arbitrarily_close : ∀ ε > 0, dist l₁ l₂ < ε,
    begin
    by_contradiction,
    rw [← dist_eq_zero] at a,
    have dist_pos : dist l₁ l₂ > 0,
      apply lt_of_le_of_ne,
      apply dist_nonneg,
      exact ne.symm a,
    exact lt_irrefl _ (arbitrarily_close _ dist_pos),
    end,
  rw [converges_to.def] at c1 c2,
  intros ε ε_pos,
  have half_ε_pos : ε/2 > 0 := div_pos ε_pos two_pos,
  apply exists.elim (c1 _ half_ε_pos), intros N1 n1,
  apply exists.elim (c2 _ half_ε_pos), intros N2 n2,
  apply lt_of_le_of_lt,
  apply dist_triangle, exact s (max N1 N2),
  rw [← add_halves ε],
  apply add_lt_add,
  rw [dist_comm],
  apply n1, apply le_max_left,
  apply n2, apply le_max_right,
  end

lemma nat.le_of_add_le : ∀ {m n k : ℕ}, k + m ≤ n → m ≤ n :=
  begin
  intros, induction k with k ih, simp at a, exact a,
  rw [nat.succ_add] at a,
  exact ih (nat.le_of_succ_le a),
  end

lemma shift.converges_to
  {α : Type} [metric_space α]
  {s : seq α} {l : α} {m : ℕ} : converges_to s l ↔ converges_to (shift m s) l :=
  begin
  suffices f : filter.map s filter.at_top = filter.map (shift m s) filter.at_top,
    {
      simp [converges_to, filter.tendsto],
      rwa f,
    },
  apply filter.ext, intro s,
  iterate {
    rw [filter.mem_map],
    rw [filter.mem_at_top_sets],
  },
  simp,
  constructor,
  {
    intro e,
    apply exists.elim e, intros n p,
    existsi n, intros b b_ge_n,
    apply p,
    transitivity,
    apply nat.le_add_right,
    assumption,
  }, {
    intro e,
    apply exists.elim e, intros n p,
    existsi (n+m), intros b b_ge_n_add_m,
    have := p (b-m) (nat.le_sub_right_of_add_le b_ge_n_add_m),
    refine eq.mp _ this,
    congr, unfold shift,
    rw [add_comm, nat.add_sub_cancel'],
    apply nat.le_of_add_le,
    assumption,
  }
  end

def take_limit (s : seq ℚ) : converges s → ℝ :=
  λ conv, quotient.mk $ subtype.mk s $
  begin
  apply exists.elim conv, intros l conv_to_l,
  intros ε ε_pos,
  have half_uε_pos : (↑(ε/2) : ℝ) > 0 := rat.cast_pos.2 (div_pos ε_pos two_pos),
  apply exists.elim ((converges_to.def s l).1 conv_to_l _ half_uε_pos),
  intros i close,
  existsi i,
  intros j j_ge,
  have ci := close i (le_refl i),
  have cj := close j j_ge,
  have : dist (s j) (s i) < ↑(ε/2) + ↑(ε/2),
    begin
    apply lt_of_le_of_lt,
    apply dist_triangle_left (s j) (s i) l,
    rw [dist_comm l, dist_comm l],
    exact add_lt_add cj ci,
    end,
  rw
    [ rat.dist_eq
    , ← rat.cast_sub, ← rat.cast_add
    , ← rat.cast_abs, rat.cast_lt
    ] at this,
  simp at *, exact this,
  end

section cls

open classical
local attribute [instance] prop_decidable

instance gt.is_trans : is_trans ℝ (≥) :=
{ trans := @ge_trans _ _ }
instance gt.is_total : is_total ℝ (≥) :=
{ total := λ a b, @le_total _ _ b a }

lemma bounded_of_converges
  {α : Type} [normed_ring α]
  {s : seq α} : converges s → ∃ M : ℝ, ∀ n : ℕ, ∥s n∥ < M :=
  begin
  intro conv,
  simp only [converges, converges_to.def] at conv,
  apply exists.elim conv, intro l, intro conv_to,
  apply exists.elim (conv_to 1 zero_lt_one),
  intros N rest,
  cases N,
  {
    existsi (∥l∥ + 1 : ℝ),
    intro n,
    have := rest n (nat.zero_le n),
    rw [dist_eq_norm] at this,
    exact calc ∥s n∥
        = ∥l + (s n - l)∥ : by rw [← add_sub_assoc, add_comm, add_sub_cancel]
    ... ≤ ∥l∥ + ∥(s n - l)∥ : norm_triangle _ _
    ... < ∥l∥ + 1 : by apply add_lt_add_left this,
  },
  cases h : list.insertion_sort (≥) (list.map (λ n, norm (s n)) (list.range (N+1))) with head tail,
  {
    exfalso,
    have := list.perm_insertion_sort (≥) (list.map (λ n, norm (s n)) (list.range (N+1))),
    rw h at this,
    have := list.eq_nil_of_perm_nil this,
    rw [list.range_succ_eq_map, list.map_cons] at this,
    cc,
  },
  {
    have := list.sorted_insertion_sort (≥) (list.map (λ (n : ℕ), ∥s n∥) (list.range (N + 1))),
    rw h at this,
    have := list.rel_of_sorted_cons this,
    existsi (∥l∥ + max (head+1) 1),
    intro n,
    by_cases n_comp : n > N,
    {
      have := rest n n_comp, rw [dist_eq_norm] at this,
      exact calc ∥s n∥
          = ∥l + (s n - l)∥ : by rw [← add_sub_assoc, add_comm, add_sub_cancel]
      ... ≤ ∥l∥ + ∥(s n - l)∥ : norm_triangle _ _
      ... < ∥l∥ + 1 : by apply add_lt_add_left this
      ... ≤ ∥l∥ + max (head+1) 1 : by apply add_le_add_left; apply le_max_right,
    },
    {
      have mem_head_cons_tail : norm (s n) ∈ list.cons head tail,
        begin
        have := list.perm_insertion_sort (≥) (list.map (λ n, norm (s n)) (list.range (N+1))),
        rw h at this,
        rw list.mem_of_perm this,
        rw [list.mem_map],
        existsi n,
        rw [list.mem_range],
        simp,
        exact nat.lt_succ_of_le (le_of_not_lt n_comp),
        end,
      have head_lt : head < norm l + max (head+1) 1,
        {
          apply lt_of_lt_of_le,
          apply lt_add_one,
          transitivity,
          apply le_max_left (head+1) 1,
          rw [← zero_add (max _ _)] { occs := occurrences.pos [1] },
          apply add_le_add,
          exact norm_nonneg l,
          refl,
        },
      cases list.eq_or_mem_of_mem_cons mem_head_cons_tail with s_n mem_tail,
      {
        rw s_n, exact head_lt,
      }, {
        apply lt_of_le_of_lt,
        exact this _ mem_tail,
        exact head_lt,
      }
    },
  },
  end

end cls

-- Proving it within a positive constant factor of epsilon is okay.
lemma converges_to.scale_epsilon 
  {α : Type} [metric_space α]
  {s : seq α} {l : α} {c : ℝ} (Hc : c > 0) :
  (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (s n) l < ε*c) ↔
  (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (s n) l < ε) :=
  begin
  constructor,
  intros, have := a (ε / c) (div_pos H Hc),
  simp only [div_mul_cancel _ (ne_of_gt Hc)] at this,
  exact this,
  intros, exact a (ε * c) (mul_pos H Hc),
  end

lemma converges_to.neg
  {α : Type} [normed_group α]
  {s : seq α} {l : α} :
  converges_to s l →
  converges_to (-s) (-l) :=
  begin
  intros h,
  rw [converges_to.def] at *,
  have : ∀ (a b : α), ∥a - b∥ = ∥b - a∥,
    intros, iterate { rw [← dist_eq_norm] }, exact dist_comm a b,
  simp [dist_eq_norm] at *,
  simp [this] at h, exact h,
  end

lemma converges_to.add
  {α : Type} [normed_group α]
  {s₁ s₂ : seq α} {l₁ l₂ : α} :
  converges_to s₁ l₁ → converges_to s₂ l₂ →
  converges_to (s₁ + s₂) (l₁ + l₂) :=
  begin
  intros h₁ h₂,
  rw [converges_to.def] at *,
  simp only [dist_eq_norm] at *,
  intros,
  have half_ε_pos : ε/2 > 0 := div_pos H two_pos,
  apply exists.elim (h₁ _ half_ε_pos), intros N1 n1,
  apply exists.elim (h₂ _ half_ε_pos), intros N2 n2,
  existsi max N1 N2,
  intros n n_ge,
  have δ1 := n1 n (le_trans (le_max_left _ _) n_ge),
  have δ2 := n2 n (le_trans (le_max_right _ _) n_ge),
  change ((s₁ + s₂) n) with s₁ n + s₂ n,
  have : s₁ n + s₂ n - (l₁ + l₂) = (s₁ n - l₁) + (s₂ n - l₂),
    { simp }, rw this,
  apply lt_of_le_of_lt,
  apply norm_triangle,
  rw [← add_halves ε],
  exact add_lt_add δ1 δ2,
  end

lemma converges_to.sub
  {α : Type} [normed_group α]
  {s₁ s₂ : seq α} {l₁ l₂ : α} :
  converges_to s₁ l₁ → converges_to s₂ l₂ →
  converges_to (s₁ - s₂) (l₁ - l₂) :=
  begin
  intros h₁ h₂,
  simp,
  apply converges_to.add,
  assumption,
  apply converges_to.neg,
  assumption,
  end

lemma converges_to.prod
  {α : Type} [normed_field α]
  {s₁ s₂ : seq α} {l₁ l₂ : α} :
  converges_to s₁ l₁ → converges_to s₂ l₂ →
  converges_to (s₁ * s₂) (l₁ * l₂) :=
  begin
  intros h₁ h₂,
  apply exists.elim (bounded_of_converges (exists.intro l₁ h₁)),
  intros M₁ bound₁,
  apply exists.elim (bounded_of_converges (exists.intro l₂ h₂)),
  intros M₂ bound₂,
  have h₁_ε := (converges_to.def _ _).1 h₁,
  have h₂_ε := (converges_to.def _ _).1 h₂,
  rw [converges_to.def],
  simp only [dist_eq_norm] at *,
  intros,
  let M := max (max (max M₁ M₂) (max (norm l₁) (norm l₂))) 1,
  have M_pos : M > 0 := lt_of_lt_of_le zero_lt_one (le_max_right _ 1),
  have M_ge_Ms : M ≥ max M₁ M₂ := le_trans (le_max_left _ _) (le_max_left _ _),
  have M_ge_ls : M ≥ max (norm l₁) (norm l₂) := le_trans (le_max_right _ _) (le_max_left _ _),
  have two_M_pos := mul_pos (@two_pos ℝ _) M_pos,
  have tol_pos := div_pos H two_M_pos,
  apply exists.elim (h₁_ε _ tol_pos), intros N1 n1,
  apply exists.elim (h₂_ε _ tol_pos), intros N2 n2,
  existsi (max N1 N2),
  intros n n_ge,
  have δ1 := n1 n (le_trans (le_max_left _ _) n_ge),
  have δ2 := n2 n (le_trans (le_max_right _ _) n_ge),
  change ((s₁ * s₂) n) with s₁ n * s₂ n,
  exact calc ∥s₁ n * s₂ n - l₁ * l₂∥
      = ∥(s₁ n * s₂ n - l₁ * s₂ n) + (l₁ * s₂ n - l₁ * l₂)∥ :
        by simp [add_assoc]
  ... ≤ ∥s₁ n * s₂ n - l₁ * s₂ n∥ + ∥l₁ * s₂ n - l₁ * l₂∥ :
        norm_triangle _ _
  ... = ∥s₂ n∥ * ∥s₁ n - l₁∥ + ∥l₁∥ * ∥s₂ n - l₂∥ :
        by rw [← mul_sub_left_distrib, ← normed_field.norm_mul]
        ;  rw [← mul_sub_right_distrib, ← normed_field.norm_mul]
        ;  ac_refl
  ... < M * ε/(2*M) + M * ε/(2*M) :
        begin
        apply add_lt_add,
        rw [mul_div_assoc],
        apply mul_lt_mul',
        transitivity,
        exact le_of_lt (bound₂ _),
        transitivity,
        apply le_max_right M₁ M₂,
        exact M_ge_Ms,
        exact δ1,
        apply norm_nonneg,
        exact M_pos,
        rw [mul_div_assoc],
        apply mul_lt_mul',
        transitivity,
        apply le_max_left (norm l₁) (norm l₂),
        exact M_ge_ls,
        exact δ2,
        apply norm_nonneg,
        exact M_pos,
        end
  ... = ε : by rw [← mul_two, mul_comm, mul_div_assoc, ← mul_assoc, ← mul_div_assoc]; exact mul_div_cancel_left ε (ne_of_gt two_M_pos),
  end

-- copypasta from https://math.stackexchange.com/a/1171755
-- I would prefer the approach from https://math.stackexchange.com/a/2605661
-- but I ran out of time
lemma pos_lower_bound_of_ne_zero
  {s : seq ℝ} {l : ℝ} :
  l ≠ 0 → (∀ n, s n ≠ 0) → ∃ M : ℝ, M > 0 ∧ ∀ n, ∥s n∥ ≥ M := sorry

lemma converges_to.inv
  {s : seq ℝ} {l : ℝ} :
  l ≠ 0 → (∀ n, s n ≠ 0) →
  converges_to s l →
  converges_to s⁻¹ l⁻¹ :=
  begin
  intros l_ne_zero s_n_ne_zero,
  intro h,
  apply exists.elim (pos_lower_bound_of_ne_zero l_ne_zero s_n_ne_zero),
  rintros M ⟨M_pos, bound⟩,
  have h_ε := (converges_to.def _ _).1 h,
  rw [converges_to.def],
  simp only [dist_eq_norm] at *,
  intros ε ε_pos,
  have l_M_pos : norm l * M > 0,
    begin
    apply mul_pos, rw norm_pos_iff, assumption, assumption,
    end,
  apply exists.elim (h_ε _ (mul_pos l_M_pos ε_pos)), intros N1 n1,
  existsi N1,
  intros n n_ge_N1,
  change s⁻¹ n with (s n)⁻¹,
  have s_n_ne_zero := s_n_ne_zero n,
  exact calc ∥(s n)⁻¹ - l⁻¹∥
      = ∥(l - s n)/(s n * l)∥ : by rw [inv_sub_inv]; assumption
  ... = ∥(l - s n)∥/∥(s n * l)∥ : by simp [real.norm_eq_abs, abs_div]
  ... = ∥(l - s n)∥/(∥s n∥ * ∥l∥) : by rw [normed_field.norm_mul]
  ... < (norm l * M) * ε / (norm l * M) :
      begin
      apply div_lt_div,
      rw [← dist_eq_norm, dist_comm, dist_eq_norm],
      exact n1 n n_ge_N1,
      rw [mul_comm],
      apply mul_le_mul_of_nonneg_right,
      exact bound n,
      apply norm_nonneg,
      rw mul_assoc,
      apply mul_nonneg,
      apply norm_nonneg,
      apply le_of_lt (mul_pos M_pos ε_pos),
      exact l_M_pos,
      end
  ... = ε : by rw [mul_div_cancel_left _ (ne_of_gt l_M_pos)],
  end

lemma converges_to_zero_of_sum_converges
  {α : Type} {s : seq α} [normed_group α]
  : converges (seq.sum s) → converges_to s 0 :=
  begin
  intro conv,
  apply exists.elim conv,
  intros l conv_to_l,
  have conv_to_l' : converges_to (shift 1 (seq.sum s)) l,
    rw [← shift.converges_to], assumption,
  have conv_to_zero : converges_to (shift 1 (seq.sum s) - seq.sum s) 0,
    have := converges_to.sub conv_to_l' conv_to_l,
    simp at this,
    exact this,
  refine eq.mp _ conv_to_zero,
  congr, funext,
  simp [shift, seq.sum],
  have : list.range (n + 1) = list.range' 0 n ++ list.range' n 1,
    begin
    rw [add_comm],
    rw [← zero_add n] { occs := occurrences.pos [3] },
    rw [list.range_eq_range'],
    symmetry,
    apply list.range'_append,
    end,
  rw [this, list.map_append, list.sum_append, list.range_eq_range'],
  simp,
  end

def is_subsequence_of
  {α : Type} (s₁ s₂ : seq α) :=
    ∃ f : ℕ → ℕ, (∀ n m, n < m → f n < f m) ∧ (∀ n, s₁ (f n) = s₂ n)

def subsequence_of
  {α : Type} (s : seq α) := subtype (is_subsequence_of s)
