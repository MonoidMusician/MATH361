import algebra.module

open list

-- The binomial coefficient, defined recursively on the natural numbers
def B : ℕ → ℕ → ℕ
| _ 0 := 1
| 0 _ := 0
| (n+1) (k+1) := B n (k+1) + B n k

-- This _almost_ holds definitionally, but requires cases on n
@[simp] lemma B.zero : Π {n : ℕ}, B n 0 = 1
| 0 := rfl
| (n+1) := rfl

@[simp] lemma B.gt : Π {n k : ℕ}, k > n → B n k = 0
| 0 0 h := absurd h (lt_irrefl 0)
| 0 (m+1) h := rfl
| (n+1) (m+1) h :=
    begin
    unfold B,
    rw [B.gt (nat.lt_of_succ_lt h), B.gt (nat.lt_of_succ_lt_succ h)],
    end

@[simp] lemma B.self : Π {n : ℕ}, B n n = 1
| 0 := rfl
| (n+1) := 
    begin
    unfold B,
    rw [@B.self n, B.gt (le_refl (nat.succ n))],
    end

lemma B.symm : Π {n k : ℕ}, k ≤ n → B n k = B n (n-k)
| 0 0 h := rfl
| (n+1) 0 h := by unfold B; simp
| (n+1) (k+1) h :=
    begin
    unfold B, simp,
    by_cases honk : n = k,
    { rw honk, simp [nat.sub_self], rw [B.gt (le_refl (nat.succ k))] },
    have : k < n,
        cases lt_or_eq_of_le (nat.le_of_succ_le_succ h),
        exact h_1, exfalso, cc,
    rw [B.symm (nat.le_of_succ_le_succ h), B.symm this],
    cases heckin : (n-k),
    exfalso, have := nat.sub_pos_of_lt this, exact ne_of_gt this heckin,
    unfold B,
    congr, rw [nat.sub_succ, heckin], refl,
    end

lemma list.range_core.concat : Π {n : ℕ} {l : list ℕ},
    range_core n l = range_core n [] ++ l
| 0 l := rfl
| (n+1) [] := by simp
| (n+1) (hd :: tl) :=
    begin
    unfold1 range_core,
    rw [@list.range_core.concat n [n]],
    rw [@list.range_core.concat n (n :: hd :: tl)],
    simp,
    end


-- Split apart a range into lower and upper parts, where the upper part
-- is a range that is mapped using addition.
lemma list.range_core.split {n m : ℕ} :
    range (n+m) = range n ++ map (λ i, i+n) (range m) :=
    begin
    induction m with m, simp [range, range_core],
    unfold1 range, unfold1 range_core,
    rw [@list.range_core.concat (n+m), @list.range_core.concat m],
    rw [map_append, ← list.append_assoc],
    unfold map, tactic.congr_core, exact m_ih, rw add_comm,
    end

lemma range_core.step {n : ℕ} :
    range (nat.succ n) = range n ++ [n] :=
    have this : map (λ (i : ℕ), i + n) (range 1) = [n]
      := by simp [range, range_core],
    eq.subst this (@list.range_core.split n 1)

-- A product distributes across each term of the sum.
lemma list.sum.distrib {α : Type} [semiring α] {a : α} {l : list α} :
    a * sum l = sum (map (λ b, a*b) l) :=
    begin
    induction l, simp,
    rw [sum_cons, left_distrib, map_cons, sum_cons, l_ih],
    end

-- Sums mapped over the same list can be combined pairwise,
-- when commutativity holds.
lemma list.sum.combine {α β : Type} [add_comm_monoid β] {f g : α → β} {l : list α} :
    sum (map f l) + sum (map g l) = sum (map (λ a, f a+g a) l) :=
    begin
    induction l, { simp },
    unfold map, rw [sum_cons, sum_cons, sum_cons],
    transitivity,
    show f l_hd + sum (map f l_tl) + (g l_hd + sum (map g l_tl))
        = f l_hd + g l_hd + (sum (map f l_tl) + sum (map g l_tl)), ac_refl,
    rw l_ih,
    end

-- This is the formula for the expansion of the power `n` of a binomial `(a+b)`,
-- where `a` and `b` are in some commutative semiring
def binomial.expansion {α : Type} [comm_semiring α] (a b : α) (n : ℕ) : α
    := sum (map (λ i, B n i * a^i * b^(n-i)) (range (n+1)))

-- The theorem that the expansion is correct
theorem binomial_theorem {α : Type} [comm_semiring α] (a b : α) (n : ℕ) :
    (a+b)^n = binomial.expansion a b n :=
    begin
    -- Classic induction on ℕ, of course!
    induction n with n ih,
    -- Base case is trivial, after unfolding some definitions
    { simp [range, range_core, binomial.expansion] },
    -- unfold the definition
    unfold binomial.expansion,
    -- split off the first binomial
    transitivity, apply pow_succ, transitivity,
    calc (a+b)*(a+b)^n
        -- start by expanding using induction hypothesis
        = (a+b) * binomial.expansion a b n : by rw ih
    ... = a * binomial.expansion a b n
        + b * binomial.expansion a b n : by rw right_distrib
        -- we will need to work with the sums separately
    ... = a*sum (map (λ i, B n i * a^i * b^(n-i)) (range (n+1)))
        + b*sum (map (λ i, B n i * a^i * b^(n-i)) (range (n+1))) : rfl
        -- distribute the `a` and `b` factors towards the inside
    ... = sum (map (λ i, a * (B n i * a^i * b^(n-i))) (range (n+1)))
        + sum (map (λ i, b * (B n i * a^i * b^(n-i))) (range (n+1))) :
        by rw [list.sum.distrib, list.sum.distrib, list.map_map, list.map_map]
        -- and add them to the exponents
    ... = sum (map (λ i, B n i * a^(i+1) * b^(n-i))   (range (n+1)))
        + sum (map (λ i, B n i * a^i     * b^(n-i+1)) (range (n+1))) :
        begin
        have : ∀ (c : α) (i : ℕ), c^(i+1) = c*c^i, intros, refl,
        -- simp reduces inside lambdas
        simp only [this a, this b],
        -- just focus on those lambdas
        congr,
        -- funny rearrangement of terms
        apply funext, intro i, simp [mul_comm, mul_assoc],
        apply funext, intro i, simp [mul_comm],
        rw [← mul_assoc, ← mul_assoc]
        end
        -- split off the `a` term
    ... = a^(n+1)
        + sum (map (λ i, B n i * a^(i+1) * b^(n-i))   (range n))
        + sum (map (λ i, B n i * a^i     * b^(n-i+1)) (range (n+1))) :
        begin
        rw [@range_core.step n, map_append, sum_append],
        simp [nat.sub_self],
        end
        -- split off the `b` term
    ... = a^(n+1)
        + sum (map (λ i, B n i     * a^(i+1) * b^(n-i))       (range n))
        + b^(n+1)
        + sum (map (λ i, B n (i+1) * a^(i+1) * b^(n-(i+1)+1)) (range n)) :
        begin
        rw [add_comm n 1, @list.range_core.split 1 n, map_append, sum_append],
        unfold1 range, unfold1 range_core, unfold1 range_core,
        unfold map, simp,
        end
        -- move them to the front, group the sums
    ... = a^(n+1) + b^(n+1)
        + (sum (map (λ i, B n i     * a^(i+1) * b^(n-i))       (range n))
        +  sum (map (λ i, B n (i+1) * a^(i+1) * b^(n-(i+1)+1)) (range n))) :
        by ac_refl
        -- simplify the exponent: `n-(i+1)+1 = n-i` for `i ∈ range n`
    ... = a^(n+1) + b^(n+1)
        + (sum (map (λ i, B n i     * a^(i+1) * b^(n-i)) (range n))
        +  sum (map (λ i, B n (i+1) * a^(i+1) * b^(n-i)) (range n))) :
        begin
            -- `n-(i+1)+1 = nat.pred (n - i) + 1`
            simp only [nat.sub_succ, nat.pred_succ],
            -- focus on this term
            suffices
                : map (λ i, ↑(B n (i + 1)) * a^(i+1) * b^(nat.pred (n-i) + 1)) (range n)
                = map (λ i, ↑(B n (i + 1)) * a^(i+1) * b^(n-i)) (range n),
                by rw this,
            -- which we can apply the special_map lemma to
            apply map_congr, intro i, intro ismem,
            -- and now we focus on this part
            suffices : nat.pred (n - i) + 1 = n - i, by rw this,
            -- `i ∈ range n ↔ i < n`
            rw list.mem_range at ismem,
            apply nat.succ_pred_eq_of_pos,
            exact nat.sub_pos_of_lt ismem,
        end
        -- okay, now we can combine the sums, since they range over the same list
    ... = a^(n+1) + b^(n+1)
        + sum (map (λ i, B n i     * a^(i+1) * b^(n-i)
                       + B n (i+1) * a^(i+1) * b^(n-i)) (range n)) :
        by rw list.sum.combine
        -- and they simplify nicely using the inductive definition of B
    ... = a^(n+1) + b^(n+1)
        + (sum (map (λ i, B (n+1) (i+1) * a^(i+1) * b^(n-i)) (range n))) :
        begin
            simp [mul_assoc, right_distrib, B.equations._eqn_4]
        end,
    -- split off the term a^(n+1) on the RHS to match the LHS
    rw [@range_core.step (n+1), map_append, sum_append],
    simp [nat.sub_self],
    -- and prove that the rest should be equal
    tactic.congr_core, refl,
    -- split off the first term on the RHS now
    rw [add_comm n 1],
    rw [@list.range_core.split 1 n, map_append, sum_append],
    unfold range range_core,
    simp, congr,
    -- prove that the mapping functions are equal
    -- simp helps with `(n+1)-(i+1) = n-i` in particular, yay!
    apply funext, intro i, simp,
    end
