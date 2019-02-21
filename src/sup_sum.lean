import data.real.basic data.analysis.filter

open lattice multiset

universes u v

-- `I` is a "set" (actually a type) that is finite and nonempty
variables {I : Type} [fintype I] [nonempty I] [decidable_eq I]
-- `S` is a "set family", a function which produces (sub)sets of ℝ
variables (S : I → set ℝ)

-- Since `I` is finite, we can sum over all values of it
def sumI (f : I → ℝ) : ℝ := finset.univ.sum f
-- A function `s : I → ℝ` is a _choice_ of `S` on `is` when, for each `i ∈ is`, `s i ∈ S i`
def choices_of_on (is : finset I) : set (I → ℝ) := λ s, ∀ i ∈ is, s i ∈ S i

-- A helper to simplify the definition of a choice when used on a finset insertion
@[simp]
lemma choices_insert (a : I → ℝ) (i : I) (is : finset I)
  : a ∈ choices_of_on S (insert i is)
  ↔ a i ∈ S i ∧ a ∈ choices_of_on S is :=
  begin
  unfold choices_of_on,
  constructor,
  intro h, constructor, apply h, simp,
  intros i' i'mem, apply h, exact finset.mem_insert_of_mem i'mem,
  intro h, intros i' i'mem,
  by_cases hi : i' = i, rw hi, exact h.1,
  apply h.2, exact finset.mem_of_mem_insert_of_ne i'mem hi,
  end

-- A helper to simplify the definition of a choice when used on the empty finset
@[simp]
lemma choices_empty (a : I → ℝ) : a ∈ choices_of_on S ∅ ↔ true :=
  begin
  unfold choices_of_on,
  simp [finset.exists_mem_empty_iff],
  end

-- The lemma that Sup (A + B) = Sup A + Sup B
lemma Sup_sum (A B : set ℝ)
  (bddA : bdd_above A) (bddB : bdd_above B)
  (neA : A ≠ ∅) (neB : B ≠ ∅) :
  Sup { x | ∃ (a ∈ A) (b ∈ B), x = a + b } =
    Sup A + Sup B :=
  begin
  apply cSup_intro,
  rw set.ne_empty_iff_exists_mem at *,
  rcases neA with ⟨a, a_mem⟩,
  rcases neB with ⟨b, b_mem⟩,
  simp,
  exact ⟨_, _, a_mem, _, b_mem, rfl⟩,
  rintro x,
  rintro ⟨a, a_mem, b, b_mem, xab⟩, rw xab,
  exact add_le_add (le_cSup bddA a_mem) (le_cSup bddB b_mem),
  rintro w w_lt, simp,
  let ε := (Sup A + Sup B) - w,
  have : ε > 0, exact sub_pos_of_lt w_lt,
  have : ε/2 > 0, exact div_pos_of_pos_of_pos this two_pos,
  have wa : Sup A - ε/2 < Sup A, rw sub_lt, simp, assumption,
  have wb : Sup B - ε/2 < Sup B, rw sub_lt, simp, assumption,
  have := exists_lt_of_lt_cSup neA wa,
  rcases this with ⟨a, a_mem, a_lt⟩,
  have := exists_lt_of_lt_cSup neB wb,
  rcases this with ⟨b, b_mem, b_lt⟩,
  apply exists.intro,
  constructor,
  apply exists.intro a, constructor, exact a_mem,
  apply exists.intro b, constructor, exact b_mem,
  refl,
  have : w = (Sup A + Sup B) - ε,
    show w = (Sup A + Sup B) - ((Sup A + Sup B) - w),
    simp,
  rw this,
  have : Sup A + Sup B - ε = (Sup A - ε/2) + (Sup B - ε/2),
    symmetry,
    calc (Sup A - ε/2) + (Sup B - ε/2)
        = (Sup A + Sup B) - (ε/2 + ε/2)
          : by rw [← add_sub_comm]
    ... = (Sup A + Sup B) - ε : by rw add_halves,
  rw this, apply add_lt_add; assumption,
  end

-- The axiom of choice, but on a finset (sorta kinda not really avoids the axiom part of it)
theorem finset_choice {α : Type u} [decidable_eq α] {β : α → Sort v} {r : Π x, β x → Prop} (h : ∀ x, ∃ y, r x y) :
  ∀ (xs : finset α), ∃ (f : Π x ∈ xs, β x), ∀ x ∈ xs, r x (f x H) :=
  begin
  intro xs,
  apply @finset.case_strong_induction_on α _
    (λ (xs : finset α), ∃ (f : Π x ∈ xs, β x), ∀ x ∈ xs, r x (f x H)),
  apply exists.intro
    (λ x H, false.elim (finset.not_mem_empty _ H)),
  intros x H, apply false.elim (finset.not_mem_empty _ H),
  intros x xs novel ih,
  rcases h x with ⟨w, wr⟩,
  rcases ih xs (by refl) with ⟨f, fr⟩,
  let f' : Π x' ∈ insert x xs, β x' := λ x' H,
    if xx : x = x'
      then (@eq.rec α x β w x' xx : β x')
      else f x' (finset.mem_of_mem_insert_of_ne H (xx ∘ eq.symm)),
  apply exists.intro f',
  intros x' H,
  by_cases xx : x = x', subst xx,
  refine eq.mp _ wr, congr, symmetry, exact dif_pos rfl,
  dsimp [f'], rw [dif_neg xx],
  apply fr,
  end

-- The axiom of choice on a finite type
theorem finite_choice {α : Type u} [decidable_eq α] [fintype α] {β : α → Sort v} {r : Π x, β x → Prop} (h : ∀ x, ∃ y, r x y) :
  ∃ (f : Π x, β x), ∀ x, r x (f x) :=
  begin
  have := finset_choice h finset.univ,
  rcases this with ⟨f, fr⟩,
  apply exists.intro (λ x, f x (finset.mem_univ x)),
  intro x, apply fr x (finset.mem_univ x),
  end

set_option pp.beta true

-- The main lemma: the sum of Sups (over each S i) is the Sup of the sums (over each choice s of S)
theorem sum_sups_eq_sup_sums (bddS : ∀ i, bdd_above (S i)) (neS : ∀ i, S i ≠ ∅) :
  sumI (λ i, Sup (S i)) = Sup (sumI '' choices_of_on S finset.univ) :=
  begin
  -- `I` is nonempty, so so should its universal finite set be
  have : (finset.univ : finset I) ≠ ∅,
  {
    intro e, exfalso,
    have := finset.eq_empty_iff_forall_not_mem.1 e,
    apply nonempty.elim _inst_2, intro i,
    exact this _ (finset.mem_univ i),
  },
  -- Revert `this` so it will be an assumption for each step of induction
  revert this,
  -- Strong induction on finsets: the more formal version of "induction on the size of a finset"
  apply @finset.case_strong_induction_on I _
    (λ is, is ≠ ∅ → is.sum (λ i, Sup (S i)) = Sup (is.sum '' choices_of_on S is)),
  -- The base case is trivial, since we stipulated that `is` is nonempty
  { intro h, cc },
  -- Introduce the member being added `i`, the rest of the finset `is`,
  -- the fact that `i` is not already in `is` (note that we name proofs in
  -- type theory!), and the induction hypothesis, which will notably apply to `is`
  intros i is inotmemis ih _,
  -- This is just some definitional unfolding and simplifying, to make it clearer
  -- what is happening with `insert i is` in the goal.
  unfold set.image at *,
  simp [finset.sum.equations._eqn_1, multiset.ndinsert_of_not_mem inotmemis] at *,
  -- If `is = ∅`, this is the actual base case (a singleton set)
  by_cases empt : is = ∅,
  {
    -- So we end up with Sup … = Sup …
    rw empt, simp,
    -- And just have to prove that the sets are equal
    congr, apply funext, intro x, apply propext,
    constructor,
    intro mem, apply exists.intro (λ _, x), exact ⟨mem, rfl⟩,
    rintro ⟨s, ⟨mem, si_x⟩⟩,
    rw si_x at mem, exact mem,
  },
  -- Apply the inductive hypothesis now
  rw ih; try { simp <|> assumption }, clear ih,
  -- We can add the Sups together, then prove that the set is what we already had
  rw [← Sup_sum], congr, simp, apply funext, intro x, apply propext,
  -- Prove each direction of the equality
  constructor,
  {
    rintro ⟨a, hsi, b, ⟨s, schoice, ssum⟩, hx⟩,
    -- We need a new function that satisfies the following properties
    let s' := (λ i', if i = i' then a else s i'),
    have s'i : s' i = a, exact if_pos rfl,
    have s'is : ∀ i' ∈ is, s' i' = s i',
      {
        intros i' i'mem,
        have : i ≠ i', intro ieqi', rw ieqi' at inotmemis, exact inotmemis i'mem,
        exact if_neg this,
      },
    apply exists.intro s',
    constructor,
    constructor,
    rw s'i, exact hsi,
    intros i' i'mem, rw s'is i' i'mem, exact schoice i' i'mem,
    rw [hx, ← ssum, s'i], congr' 2,
    exact multiset.map_congr s'is,
  }, {
    rintro ⟨s, ⟨schoice0, schoice⟩, ssum⟩,
    -- We already have the function, so just need to specify the numbers
    apply exists.intro (s i),
    constructor, assumption,
    apply exists.intro (sum (map s (is.val))),
    constructor,
    apply exists.intro s, finish, finish
  },

  -- We need to prove that S i and the set of choices are bounded
  exact bddS i,
  -- `bounds i` computes an upper bound on `S i` for each `i`
  -- so, of course, an upper bound on any sum
  have : ∃ (bounds : I → ℝ), ∀ i, ∀ si ∈ S i, si ≤ bounds i,
  {
    apply @finite_choice I _ _ (λ _, ℝ) (λ i bound, ∀ si ∈ S i, si ≤ bound) bddS,
  },
  rcases this with ⟨bounds, isbounds⟩,
  apply exists.intro (sum (map bounds (is.val))),
  simp,
  intros asum s schoice isasum, rw ← isasum,
  apply finset.sum_le_sum,
  intros i i_mem, apply isbounds i (s i) (schoice i i_mem),

  -- We need to prove that S i and the set of choices are nonempty
  exact neS i,
  rw set.ne_empty_iff_exists_mem,
  -- `s i` computes an element of `S i` for each `i`
  have : ∃ (s : I → ℝ), s ∈ choices_of_on S is,
  {
    apply exists_imp_exists _,
    apply @finite_choice I _ _ (λ _, ℝ) (λ i si, si ∈ S i),
    intro i,
    exact set.exists_mem_of_ne_empty (neS i),
    intros s si i i_mem, exact si i,
  },
  rcases this with ⟨si, issi⟩,
  constructor,
  constructor,
  constructor,
  exact issi, refl,
  end
