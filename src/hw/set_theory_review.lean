import data.set.basic data.real.basic tactic.ring
import analysis.topology.continuity
import analysis.real
import data.vector

open set

namespace set_theory_review

def sin (x : ℝ) : ℝ := sorry
def cos (x : ℝ) : ℝ := sorry

namespace problem1

-- (1) Consider the sine function defined by f(x) = sin x for (−∞ < x < ∞).

-- uhm we don't actually have the sin function in Lean yet ...
def f (x : ℝ) : ℝ := sin x
-- nor pi
def pi : ℝ := sorry

-- but if we did, we could prove this!

namespace part_a

-- What is the image of π/2 under f?
lemma answer_proof : f (pi / 2) = 1 := sorry

end part_a

namespace part_b

-- Find f⁻¹(1).

-- so we uh just take the inverse of the function, right?
-- -- lemma part_b : function.inv_fun f 1 = pi/2
-- wrong, that's not well defined, we can't prove anything about it ...

-- might as well just repeat ourselves:
lemma answer_proof : f (pi / 2) = 1 := part_a.answer_proof
-- or give the precise set
def answer : set ℝ := {x | f x = 1}
-- aka the preimage
lemma proof_preimage : answer = f ⁻¹' {1} :=
  begin
  apply set.ext, intro x, simpa,
  end
-- which does include pi/2, by part a
lemma includes_half_pi : pi / 2 ∈ answer := part_a.answer_proof

end part_b

lemma sin_pi_6 : f (pi/6) = 1/2 := sorry

namespace part_c

-- Find f([0, π/6]), f([π/6, π/2]), f([0, π/2]).
lemma part_i : f '' Icc 0 (pi/6) = Icc 0 (1/2) := sorry
lemma part_ii : f '' Icc (pi/6) (pi/2) = Icc (1/2) 1 := sorry
lemma part_iii : f '' Icc 0 (pi/2) = Icc 0 1 := sorry

end part_c

namespace part_d

-- (d) Interpret the result of part (c) in view of the theorem:
--       If f : A → B and if X ⊂ A and Y ⊂ A, then f(X ∪ Y) = f(X) ∪ f(Y).

-- we do have that theorem already:
#check set.image_union

-- I'll just reprove it quickly:
theorem reproof {A B : Type} (f : A → B) (X Y : set A) :
  f '' (X ∪ Y) = f '' X ∪ f '' Y :=
  begin
  unfold set.image,
  unfold has_union.union set.union,
  apply set.ext, intro b, simp,
  constructor,
  intro e, apply exists.elim e, intro a, intro h,
  cases h, cases h_left,
  { left, existsi a, tauto },
  { right, existsi a, tauto },
  intro e, cases e,
  { apply exists.elim e, intro a, intro h,
    existsi a, constructor, left, tauto, tauto
  },
  { apply exists.elim e, intro a, intro h,
    existsi a, constructor, right, tauto, tauto
  },
  end

-- helper theorem: [a, b] ∪ [c, d] = [a, d], given the following assumptions
theorem Icc_union {α : Type*} [linear_order α] (a b c d : α) :
  a ≤ c → b ≥ c → b ≤ d →
  Icc a b ∪ Icc c d = Icc a d :=
    begin
    intros,
    unfold Icc, apply set.ext, intro x, simp,
    constructor,
    {
      intro h, cases h,
      constructor, exact h.1, transitivity, exact h.2, assumption,
      constructor, transitivity, assumption, exact h.1, exact h.2,
    }, {
      intro h,
      have m : x ≤ b ∨ b ≤ x := linear_order.le_total x b,
      cases m,
      left, constructor, exact h.1, exact m,
      right, constructor, transitivity, assumption, exact m, exact h.2,
    }
    end

-- so we can get part_c.part_iii from the previous two
theorem proof : f '' Icc 0 (pi/2) = Icc 0 1 :=
  begin
  have : Icc 0 (pi/6) ∪ Icc (pi/6) (pi/2) = Icc 0 (pi/2),
  {
    apply Icc_union,
    /-
    3 goals
    ⊢ 0 ≤ pi / 6
    ⊢ pi / 6 ≥ pi / 6
    ⊢ pi / 6 ≤ pi / 2
    -/
    -- but we can't prove the ordering of pi since pi isn't defined here
    admit, exact le_refl (pi/6), admit,
  },
  rw ← this, rw reproof, rw part_c.part_i, rw part_c.part_ii,
  apply Icc_union,
  exact le_of_lt one_half_pos,
  exact le_refl (1/2),
  exact le_of_lt one_half_lt_one,
  end

end part_d

namespace part_e

-- (e) Let A = [0, π/6], B = [5π/6, π]. Does f(A ∩ B) = f(A) ∩ f(B)?

-- nope, because A ∩ B = ∅, but f(A) = f(B) = [0, 1/2]

def A := Icc 0 (pi/6)
def B := Icc (5*pi/6) (pi)
lemma A_image : f '' A = Icc 0 (1/2) := sorry
lemma B_image : f '' B = Icc 0 (1/2) := sorry

theorem proof : f '' (A ∩ B) ≠ f '' A ∩ f '' B :=
  begin
  rw [A_image, B_image],
  have : A ∩ B = ∅,
  {
    apply set.ext, intro x, simp,
    show 0 ≤ x ∧ x ≤ pi/6 → ¬ (5*pi/6 ≤ x ∧ x ≤ pi),
    suffices : x ≤ pi/6 → x < 5*pi/6,
    {
      intro h, apply not_and_of_not_left,
      apply not_le_of_lt,
      exact this h.2,
    },
    intro h,
    apply lt_of_le_of_lt,
    exact h,
    show pi / 6 < 5 * pi / 6, admit,
  },
  rw this, simp [-one_div_eq_inv],
  rw set.ext_iff,
  -- proof by contradiction, essentially
  -- (to prove (¬ p) you need to prove (p → false))
  -- (actually, that is true by definition: not p := p → false)
  intro empty_eq_Icc,
  -- 0 is an element in the interval
  exact (empty_eq_Icc 0).2 ⟨le_refl 0, le_of_lt one_half_pos⟩
  end

end part_e

end problem1

namespace problem2

-- (2) Can you give a geometric interpretation for the Cartesian product of
-- (a) A line segment and a triangle?

-- A triangular prism?

-- (b) A large circle and a small circle?

-- An ellipsoid??? Or maybe something in 4d space, since the circles are
-- each 2d ...
-- (My roommate: "Prolly ... a bigger circle?")

end problem2

namespace problem3

-- (3) If f : (−1, 1) → ℝ is defined by f(x) = arcsin x and
--     g : (−π/2, π/2) → ℝ by g(x) = tan x, let h = g ◦ f. Write a simple
--     formula for h. What are the domain and range of h?

-- h x = g (f x) = tan (arcsin x) = sin (arcsin x) / cos (arcsin x)
--     = x / cos (arcsin x) = x / sqrt(1 - x²)
--     = sqrt(x² / (1 - x²))
--     = if x = 0 then 0 else (x⁻² - 1)^(-1/2)

-- aux proof of cos (arcsin x) = sqrt(1 - x^2):
--   forall y:
--   (cos y)^2 + (sin y)^2 = 1
--   cos y = sqrt(1 - (sin y)^2)
--   rewrite y = arcsin x:
--   cos (arcsin x) = sqrt(1 - (sin (arcsin x))^2)
--   cos (arcsin x) = sqrt(1 - x^2)

-- domain of f : (-1, 1), range of f : (-π/2, π/2),
--   since f is continuous and monotonic between f(-1) = -π/2 and f(1) = π/2
-- domain of g : (-π/2, π/2), range of g : (-∞, ∞),
--   since f is continuous and lim[x → ­±π/2] f = ±∞
-- so domain of h : (-1, 1), range of h : (-∞, ∞)

end problem3

namespace problem4

-- (4) Let f : ℝ → ℝ be defined by f(x) = 2x. Can you think of functions g
--     and h which satisfy these two equations?
-- g ◦ f = 2 * g * h
-- h ◦ f = h^2 − g^2

def f (x : ℝ) := 2*x

def problem := ∃ (g h : ℝ → ℝ), ∀ x,
  g (f x) = 2 * g x * h x ∧
  h (f x) = (h x)^2 - (g x)^2

def g (x : ℝ) := sin x
def h (x : ℝ) := cos x

-- graph it! obviously can't prove it here ...
lemma sin_two_eq_two_sin_cos :
  ∀ x, sin (2 * x) = 2 * sin x * cos x := sorry
lemma sin_two_eq_cos_sqr_sub_sin_sqr :
  ∀ x, cos (2 * x) = (cos x)^2 - (sin x)^2 := sorry

-- our proof is just a term with type defined by the problem
-- (that is, it is a proof of the existence of such functions)
def proof : problem :=
  begin
  existsi g,
  existsi h,
  intro x,
  constructor,
  exact sin_two_eq_two_sin_cos x,
  exact sin_two_eq_cos_sqr_sub_sin_sqr x,
  end

end problem4

-- The next few questions concern the notion of the characteristic function
-- of a set, which we now define. Let A be a subset of the real numbers ℝ.
-- Define the characteristic function of A χ_A : ℝ → ℝ to be

-- χ_A(x) = 1 if x ∈ A; 0 if x ∈ ℝ \ A.

-- this is the same spirit, in particular it works for
-- a set of any type (which is also how it was assumed
-- to be generalized in the examples), mapping
-- 1 to true and 0 to false
def χ {α : Type} (A : set α) (a : α) := a ∈ A
-- but really it's just the identity function
-- (this is because sets in set theory are represented as functions
-- α → Prop, for some α : Type, where the proposition returned
-- is true for only the (a : α) in the set.)
-- (in HoTT, a set also means that it has no path constructors.)
@[simp] lemma χ_id {α : Type} (A : set α) : χ A = A := rfl


namespace problem5

-- (5) If f : ℝ → ℝ is defined by f(x) = x^2 and χ_[0,9] is the
--     characteristic function of [0, 9], of what subset of ℝ is
--     χ[0,9] ◦ f the characteristic function?

def real.sqr (x : ℝ) := x ^ 2
def zero_through_nine : set ℝ := Icc 0 9

def answer : set ℝ := Icc (-3) 3

theorem proof : answer = χ zero_through_nine ∘ real.sqr :=
  begin
  apply set.ext, intro x,
  show -3 ≤ x ∧ x ≤ 3 ↔ 0 ≤ x^2 ∧ x^2 ≤ 9,
  unfold has_pow.pow monoid.pow, simp,
  rw (by ring : (9 : ℝ) = 3 * 3),
  constructor,
  {
    intro h,
    have : x * x = abs x * abs x,
      by_cases x = 0, { rw h, simp },
      apply (mul_self_eq_mul_self_iff _ _).2,
      apply abs_by_cases (λ y, x = y ∨ x = -y),
      left, tauto, right, rw neg_neg,
    rw this,
    constructor,
    exact mul_self_nonneg (abs x),
    apply mul_self_le_mul_self,
    exact abs_nonneg x,
    apply abs_le.2, exact h,
  }, {
    intro h,
    rw ← abs_le,
    have : (0 : ℝ) ≤ 3,
      { change real.of_rat 0 ≤ real.of_rat 3
      , apply le_of_lt
      , rw real.of_rat_lt
      , from dec_trivial
      },
    rw ((by rw @real.sqrt_sqr (3 : ℝ); assumption) : 3 = real.sqrt (3^2)),
    unfold has_pow.pow monoid.pow, simp,
    rw ← real.sqrt_mul_self_eq_abs x,
    rw real.sqrt_le,
    exact h.2, exact h.1,
    apply le_of_lt,
    change real.of_rat 0 < real.of_rat (3 * 3),
    rw real.of_rat_lt,
    from dec_trivial
  }
  end

end problem5

namespace problem6

-- (6) If f : A → B is a function and χ_E is the characteristic function of
-- E ⊂ B, of what subset of A is χ_E ◦ f the characteristic function?

-- that's just the preimage of f over E, the set of points in the domain such
-- that their image under f is in E: { x : A | f x ∈ E }
def answer {A B : Type} (f : A → B) (E : set B) := f ⁻¹' E
#print set.preimage
theorem proof {A B : Type} (f : A → B) (E : set B)
  : χ E ∘ f = answer f E :=
  begin apply set.ext, intro x, simpa end

end problem6

namespace problem7

-- (7) Using whatever concept of continuity you possess, answer the
--     following questions (the answer is supposed to be intuitive,
--     and is not meant to include a rigorous proof):

-- (a) Is there a continuous characteristic function on ℝ? That is, is there
--     a subset A of ℝ such that χ_A is continuous?

-- Yes, there are two: A = ℝ, and A = ∅.

-- (b) Are there three such functions?

-- No, any deviation from a constant function produces a discontinuity.

end problem7

namespace problem8

-- (8) Draw the graphs of two continuous functions f and g with the same
--     domain. Would you guess that the functions
--     M := max(f, g) and m := min(f, g) are continuous?

-- [insert graphs badly drawn with crayons as if penned by a 5yo] jk

-- Yes, I would guess so.
-- And it's this is actually a theorem already ...
-- The gist of it is this lemma
#check continuous_if
-- which basically says that piecewise functions, in order to be continuous,
-- must be equal when the if  statement switches between true and false (and
-- of course, the functions should be continuous otherwise). The if
-- statement does indeed switch between true and false when the functions
-- are equal, by the definition of `max` and `min`.

def pointwise {A B I O : Type} (f : A → B → O) (g : I → A) (h : I → B) :=
  λ i, f (g i) (h i)

theorem proof (f g : ℝ → ℝ) : continuous f → continuous g → continuous (pointwise max f g) ∧ continuous (pointwise min f g) :=
  begin
  intros cf cg,
  constructor,
  exact continuous_max cf cg,
  exact continuous_min cf cg,
  end

end problem8

namespace problem9

-- (9) (a) If f : A → B and g : B → C and both f and g are injective,
--         is g ◦ f also injective?
--     (b) If f is not injective, is it still possible that g ◦ f is
--         injective?
--     (c) Give an example in which f is injective, g is not injective,
--         but g ◦ f is injective.
open function

-- it's very straightforward ...
theorem part_a {A B C : Type} (f : A → B) (g : B → C) : function.injective f → function.injective g → function.injective (g ∘ f) :=
  flip function.injective_comp

theorem part_b {A B C : Type} (f : A → B) (g : B → C) : ¬ function.injective f → function.injective g → ¬ function.injective (g ∘ f) :=
  begin
  intros f_ninj g_inj comp_inj,
  apply f_ninj,
  intros a b e,
  unfold function.injective function.comp at comp_inj,
  apply comp_inj (congr_arg _ e),
  end

namespace part_c

def A := unit
def B := bool
def C := unit
def f : A → B := λ _, ff
def g : B → C := λ _, unit.star
theorem proof : injective f ∧ ¬ injective g ∧ injective (g ∘ f) :=
  begin
  constructor,
  intros _ _ _, apply @subsingleton.elim unit,
  constructor,
  intro f,
  exact bool.no_confusion (@f tt ff (by apply @subsingleton.elim unit)),
  intros _ _ _, apply @subsingleton.elim unit,
  end

end part_c

end problem9

namespace problem10

-- (10) Let P_n be the set of polynomial functions f of degree n,
--          f(x) = a_0 + a_1 * x + · · · a_n * x^n
--      where n is a fixed non-negative integer and the coefficients
--      a0, . . . , an are integers. Prove that P_n is countable.

-- In this problem I'll use `encodable α` instead of `countable α`, which is
-- defined as `nonempty (encodable α)` (that is, the mere proposition
-- that there exists an encoding for the type).

-- A vector of numbers of size n essentially represents the data of a
-- polynomial of degree (n-1); that is, there is a bijection between these
-- mathematical objects. So I'll prove that a vector of encodables is
-- encodable.

-- The gist of the proof is induction on n, using cartesian products
-- to add another layer to the vector.

theorem encodable_equiv {α β : Type} : α ≃ β → encodable α → encodable β :=
  begin
  intros eqv c,
  apply encodable.mk (c.encode ∘ eqv.2) (option.map eqv.1 ∘ c.decode),
  intro b, simp, existsi (eqv.2 b),
  rw c.encodek, simp, exact eqv.4 b,
  end

theorem encodable_array {α : Type} : encodable α → ∀ n : ℕ, encodable (vector α n) :=
  begin
  intros c n, induction n with n ih,
  suffices : unit ≃ vector α 0,
  {
    apply encodable_equiv this, apply_instance,
  },
  apply equiv.mk (λ _, vector.nil) (λ _, unit.star),
  intro _, apply subsingleton.elim,
  intro _, rw vector.eq_nil x,
  suffices : (α × vector α n) ≃ vector α (n+1),
  {
    apply encodable_equiv this,
    apply @encodable.prod _ _ c ih,
  },
  apply equiv.mk
    (λ (p : α × vector α n), vector.cons p.1 p.2)
    (λ a, begin
    cases a with l p,
    cases l, exfalso, exact nat.succ_ne_zero _ (eq.symm p),
    constructor, exact l_hd,
    apply subtype.mk l_tl,
    exact nat.succ.inj p,
    end),
  intro a, cases a, cases a_snd, simpa,
  intro a, cases a, simp,
  cases a_val, exfalso, exact nat.succ_ne_zero _ (eq.symm a_property),
  simpa,
  end

end problem10

namespace problem11

-- (11) Prove that if B is a countable subset of an uncountable set A, then
-- A \ B is uncountable.
theorem proof {α : Type} (A B : set α)
  (H : B ⊆ A) (HA : ¬(countable A)) (HB : countable B) : ¬(countable (A \ B)) :=
  λ HC,
  have this : (A \ B) ∪ B = A :=
    eq.trans diff_union_self (union_eq_self_of_subset_right H),
  HA (eq.mp (congr_arg countable this) (countable_union HC HB))

end problem11

end set_theory_review
