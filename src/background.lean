import analysis.real

-- Helper definition with some associated lemmas
def signed (n : ℕ) : ℤ :=  (-1 : ℤ)^n

lemma signed_cases : ∀ n, (signed n = 1) ∨ (signed n = -1) :=
begin
  intro n, unfold signed,
  cases nat.mod_two_eq_zero_or_one n;
  rw [← nat.mod_add_div n 2, pow_add, pow_mul, h];
  simp [pow_two],
end

@[simp] lemma signed_even {n : ℕ} : signed (2*n) = 1 :=
  begin
  induction n, refl, unfold signed,
  rw nat.mul_succ, rw pow_succ, rw pow_succ,
  simp, exact n_ih,
  end
@[simp] lemma signed_odd {n : ℕ} : signed (2*n+1) = -1 :=
  begin
  unfold signed,
  rw pow_succ,
  show -1 * signed (2*n) = -1,
  rw signed_even, refl,
  end
