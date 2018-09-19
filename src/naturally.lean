import tactic.interactive algebra.group_power

meta def iterating (t : tactic unit) : tactic ℕ := do
  (nat.succ <$> (t >> iterating)) <|> pure 0

meta def rw_simple : bool → pexpr → tactic unit :=
  λ symm rule, do
  rule' ← tactic.to_expr rule,
  tactic.rewrite_target rule' { symm := symm }

-- tactic to help convert proofs about natural numbers
-- phrased in terms of some other ring to proofs about natural numbers.
meta def naturally : interactive.parse interactive.types.texpr → tactic unit := λ t, do
  i0 ← iterating $ rw_simple tt ``(@nat.cast_zero %%t),
  i1 ← iterating $
    has_bind.and_then (rw_simple tt ``(@nat.cast_one %%t)) $
      tactic.interactive.iterate none $
        rw_simple tt ``(@nat.cast_bit0 %%t) <|> rw_simple tt ``(@nat.cast_bit1 %%t),
  i2 ← iterating $ rw_simple tt ``(@nat.cast_add %%t) <|> rw_simple tt ``(@nat.cast_mul %%t),
  i3 ← iterating $ rw_simple ff ``(@nat.cast_lt %%t) <|> rw_simple ff ``(@nat.cast_le %%t) <|> rw_simple ff ``(@nat.cast_inj %%t) <|> rw_simple ff ``(@nat.cast_max %%t) <|> rw_simple ff ``(@nat.cast_min %%t),
  match i0 + i1 + i2 + i3 with
  | nat.zero := tactic.fail "naturally did nothing"
  | nat.succ _ := tactic.try $ do
    tactic.exact_dec_trivial
  end

meta def natureally : tactic unit := naturally ``(ℝ)