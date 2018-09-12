namespace random1

variables {α : Type} [partial_order α] [decidable_eq α] (M : α) (M_is_lb : ∀ a, M ≤ a)

open classical
local attribute [instance] prop_decidable

theorem double_not (p : Prop) : ¬¬p ↔ p :=
  begin
  constructor,
  intro h,
  by_cases a : p, exact a, exfalso, exact h a,
  intro h, intro not_p, exact not_p h,
  end

include M_is_lb
lemma not_gt_equiv_eq : iff (¬ ∃ M', M' > M ∧ ∀ a, M' ≤ a) (¬¬∀ M', (∀ a, M' ≤ a) → M' = M) :=
  begin
  have : ∀ M', (M' > M ∧ ∀ a, M' ≤ a) ↔ ¬ ((∀ a, M' ≤ a) → M' = M),
  {
    intro M',
    constructor,
    {
      intro h,
      intro h',
      apply ne_of_gt h.1,
      exact h' h.2,
    }, {
      intro h,
      by_cases meq : M' = M,
      {
        exfalso, apply h, intro, exact meq,
      }, {
        have : M' > M, exact lt_of_le_of_ne (M_is_lb M') (ne.symm meq),
        constructor, exact this,
        by_cases allfor : ∀ (a : α), M' ≤ a, exact allfor, cc,
      }
    }
  },
  simp only [this],
  transitivity,
  constructor,
  exact forall_not_of_not_exists,
  intro allfor, intro exist,
  apply exists.elim exist,
  intro M', intro h,
  apply allfor M',
  exact h,
  constructor,
  intro h, intro not_h, apply not_h,
  intro M', exact (double_not _).1 (h M'),
  intro h, intro M', intro not_concl,
  apply h, intro concl,
  exact not_concl (concl M'),
  end

end random1
