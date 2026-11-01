import Mathlib

/-!
# Machine-checked local facts for the accelerated Collatz map

This file formalizes the exact algebraic fragments used in the accompanying
manuscript.  It deliberately does not claim a proof of the Collatz conjecture.
-/

namespace CollatzLocal

/-- The numerator used in an odd Collatz step. -/
def oddNumerator (n : ℕ) : ℕ := 3 * n + 1

/-- Numbers congruent to `1 mod 4` have an odd-step numerator divisible by `4`. -/
theorem mod4_one_factorization (q : ℕ) :
    oddNumerator (4 * q + 1) = 4 * (3 * q + 1) := by
  simp [oddNumerator]
  omega

/-- For `q > 0`, division by four already sends `4q+1` below itself. -/
theorem mod4_one_quarter_decreases (q : ℕ) (hq : 0 < q) :
    oddNumerator (4 * q + 1) / 4 < 4 * q + 1 := by
  rw [mod4_one_factorization]
  simp
  omega

/-- Numbers congruent to `3 mod 4` have exactly one visible factor of two. -/
theorem mod4_three_factorization (q : ℕ) :
    oddNumerator (4 * q + 3) = 2 * (6 * q + 5) := by
  simp [oddNumerator]
  omega

/-- The cofactor after removing that factor of two is odd. -/
theorem mod4_three_cofactor_odd (q : ℕ) : Odd (6 * q + 5) := by
  use 3 * q + 2
  omega

/-- A single division by two sends `4q+3` to a larger odd integer. -/
theorem mod4_three_half_increases (q : ℕ) :
    oddNumerator (4 * q + 3) / 2 > 4 * q + 3 := by
  rw [mod4_three_factorization]
  simp
  omega

/-! ## Refinement modulo eight -/

/-- The class `1 mod 8` has valuation exactly two: after removing four, the
cofactor is odd. -/
theorem mod8_one_factorization (q : ℕ) :
    oddNumerator (8 * q + 1) = 4 * (6 * q + 1) := by
  simp [oddNumerator]
  omega

theorem mod8_one_cofactor_odd (q : ℕ) : Odd (6 * q + 1) := by
  use 3 * q
  omega

theorem mod8_one_quarter_decreases (q : ℕ) (hq : 0 < q) :
    oddNumerator (8 * q + 1) / 4 < 8 * q + 1 := by
  rw [mod8_one_factorization]
  simp
  omega

/-- The class `5 mod 8` has valuation at least three. Dividing by eight is
already enough to obtain a smaller number; further divisions only decrease it. -/
theorem mod8_five_factorization (q : ℕ) :
    oddNumerator (8 * q + 5) = 8 * (3 * q + 2) := by
  simp [oddNumerator]
  omega

theorem mod8_five_eighth_decreases (q : ℕ) :
    oddNumerator (8 * q + 5) / 8 < 8 * q + 5 := by
  rw [mod8_five_factorization]
  simp
  omega

/-! ## Refinement modulo sixteen -/

theorem mod16_one_factorization (q : ℕ) :
    oddNumerator (16 * q + 1) = 4 * (12 * q + 1) := by
  simp [oddNumerator]
  omega

theorem mod16_one_cofactor_odd (q : ℕ) : Odd (12 * q + 1) := by
  use 6 * q
  omega

theorem mod16_five_factorization (q : ℕ) :
    oddNumerator (16 * q + 5) = 16 * (3 * q + 1) := by
  simp [oddNumerator]
  omega

theorem mod16_five_sixteenth_decreases (q : ℕ) :
    oddNumerator (16 * q + 5) / 16 < 16 * q + 5 := by
  rw [mod16_five_factorization]
  simp
  omega

theorem mod16_nine_factorization (q : ℕ) :
    oddNumerator (16 * q + 9) = 4 * (12 * q + 7) := by
  simp [oddNumerator]
  omega

theorem mod16_nine_cofactor_odd (q : ℕ) : Odd (12 * q + 7) := by
  use 6 * q + 3
  omega

theorem mod16_thirteen_factorization (q : ℕ) :
    oddNumerator (16 * q + 13) = 8 * (6 * q + 5) := by
  simp [oddNumerator]
  omega

theorem mod16_thirteen_cofactor_odd (q : ℕ) : Odd (6 * q + 5) := by
  use 3 * q + 2
  omega

/-- Algebraic form of an integer with at least `ℓ` trailing binary ones. -/
theorem trailing_ones_factorization (ℓ q : ℕ) (hℓ : 2 ≤ ℓ) :
    oddNumerator (2 ^ ℓ * q + (2 ^ ℓ - 1)) =
      2 * (3 * 2 ^ (ℓ - 1) * (q + 1) - 1) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hℓ
  simp [oddNumerator, pow_add, pow_succ]
  ring_nf at ⊢
  have hp : 0 < 2 ^ r := by positivity
  omega

/-- The cofactor in the trailing-ones factorization is odd. -/
theorem trailing_ones_cofactor_odd (ℓ q : ℕ) (hℓ : 2 ≤ ℓ) :
    Odd (3 * 2 ^ (ℓ - 1) * (q + 1) - 1) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hℓ
  simp [pow_add, pow_succ]
  use 3 * 2 ^ r * (q + 1) - 1
  ring_nf at ⊢
  have hp : 0 < 2 ^ r := by positivity
  omega

/-- The accelerated value displayed by the trailing-ones factorization is
strictly larger than the starting value, except at the trivial value one. -/
theorem trailing_ones_increases (ℓ q : ℕ) (hℓ : 2 ≤ ℓ)
    (hn : 1 < 2 ^ ℓ * q + (2 ^ ℓ - 1)) :
    2 ^ ℓ * q + (2 ^ ℓ - 1) <
      3 * 2 ^ (ℓ - 1) * (q + 1) - 1 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hℓ
  simp [pow_add, pow_succ] at hn ⊢
  ring_nf at hn ⊢
  have hb : 0 < 2 ^ r := by positivity
  omega

/-! ## Arbitrarily long expanding chains -/

/-- One step in the explicit chain beginning at `2^m - 1`.  When `b` is
positive, the cofactor is odd and is the next member of the same family. -/
theorem expanding_chain_factorization (a b : ℕ) :
    oddNumerator (3 ^ a * 2 ^ (b + 1) - 1) =
      2 * (3 ^ (a + 1) * 2 ^ b - 1) := by
  let x := 3 ^ a * 2 ^ b
  have hx : 0 < x := by simp [x]
  have hs : 3 ^ a * 2 ^ (b + 1) = 2 * x := by
    simp [x, pow_succ]
    ring
  have ht : 3 ^ (a + 1) * 2 ^ b = 3 * x := by
    simp [x, pow_succ]
    ring
  rw [hs, ht]
  simp only [oddNumerator]
  omega

theorem expanding_chain_cofactor_odd (a b : ℕ) (hb : 0 < b) :
    Odd (3 ^ (a + 1) * 2 ^ b - 1) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  let x := 3 ^ (a + 1) * 2 ^ c
  have hx : 0 < x := by simp [x]
  have hs : 3 ^ (a + 1) * 2 ^ (c + 1) = 2 * x := by
    simp [x, pow_succ]
    ring
  rw [hs]
  use x - 1
  omega

theorem expanding_chain_increases (a b : ℕ) :
    3 ^ a * 2 ^ (b + 1) - 1 < 3 ^ (a + 1) * 2 ^ b - 1 := by
  let x := 3 ^ a * 2 ^ b
  have hx : 0 < x := by simp [x]
  have hs : 3 ^ a * 2 ^ (b + 1) = 2 * x := by
    simp [x, pow_succ]
    ring
  have ht : 3 ^ (a + 1) * 2 ^ b = 3 * x := by
    simp [x, pow_succ]
    ring
  rw [hs, ht]
  omega

/-! ## Universal return to a contracting residue

Writing an odd integer as `2^(a+1)u - 1` with `u` odd exposes its complete
initial run of valuation-one steps.  The following lemmas formalize each
forced transition and the final arrival in the class `1 mod 4`.  They are the
elementary part of the manuscript's controlled-target corollary; Tao's
almost-everywhere theorem itself is used only as an external input.
-/

/-- One forced valuation-one transition in the return chain, with an arbitrary
positive odd multiplier `u`. -/
theorem return_chain_factorization (a b u : ℕ) (hu : 0 < u) :
    oddNumerator (3 ^ a * 2 ^ (b + 1) * u - 1) =
      2 * (3 ^ (a + 1) * 2 ^ b * u - 1) := by
  let x := 3 ^ a * 2 ^ b * u
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hs : 3 ^ a * 2 ^ (b + 1) * u = 2 * x := by
    simp [x, pow_succ]
    ring
  have ht : 3 ^ (a + 1) * 2 ^ b * u = 3 * x := by
    simp [x, pow_succ]
    ring
  rw [hs, ht]
  simp only [oddNumerator]
  omega

/-- Before the last transition, the displayed cofactor is odd, so the
valuation in `return_chain_factorization` is exactly one. -/
theorem return_chain_cofactor_odd (a b u : ℕ) (hb : 0 < b) (hu : 0 < u) :
    Odd (3 ^ (a + 1) * 2 ^ b * u - 1) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  let x := 3 ^ (a + 1) * 2 ^ c * u
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hs : 3 ^ (a + 1) * 2 ^ (c + 1) * u = 2 * x := by
    simp [x, pow_succ]
    ring
  rw [hs]
  use x - 1
  omega

/-- Every forced valuation-one step in the return chain is an increase. -/
theorem return_chain_increases (a b u : ℕ) (hu : 0 < u) :
    3 ^ a * 2 ^ (b + 1) * u - 1 <
      3 ^ (a + 1) * 2 ^ b * u - 1 := by
  let x := 3 ^ a * 2 ^ b * u
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hs : 3 ^ a * 2 ^ (b + 1) * u = 2 * x := by
    simp [x, pow_succ]
    ring
  have ht : 3 ^ (a + 1) * 2 ^ b * u = 3 * x := by
    simp [x, pow_succ]
    ring
  rw [hs, ht]
  omega

/-- The last member of the forced chain is congruent to `1 mod 4`. -/
theorem return_chain_hits_mod4_one (a u : ℕ) (hu : Odd u) :
    ∃ q : ℕ, 2 * 3 ^ a * u - 1 = 4 * q + 1 := by
  have hprod : Odd (3 ^ a * u) :=
    (Odd.pow (by norm_num : Odd (3 : ℕ))).mul hu
  obtain ⟨q, hq⟩ := hprod
  use q
  have hassoc : 2 * 3 ^ a * u = 2 * (3 ^ a * u) := by ring
  rw [hassoc, hq]
  omega

/-- Once the return chain reaches its `1 mod 4` member, division by four
already gives a strict local descent (except at the fixed point one). -/
theorem return_chain_final_decreases (a u : ℕ) (hu : Odd u)
    (hfinal : 1 < 2 * 3 ^ a * u - 1) :
    oddNumerator (2 * 3 ^ a * u - 1) / 4 < 2 * 3 ^ a * u - 1 := by
  obtain ⟨q, hq⟩ := return_chain_hits_mod4_one a u hu
  rw [hq]
  apply mod4_one_quarter_decreases
  omega

/-- A coarse integer size bound for the controlled return value.  It is weaker
than the manuscript's sharp exponent `log₂ 3`, but already suffices to rescale
any target function tending to infinity. -/
theorem return_chain_quadratic_bound (a u : ℕ) (hu : 0 < u) :
    2 * 3 ^ a * u ≤ (2 ^ (a + 1) * u) ^ 2 := by
  have hpow : 3 ^ a ≤ 4 ^ a := Nat.pow_le_pow_left (by norm_num) a
  have hmul : 2 * 3 ^ a * u ≤ 2 * 4 ^ a * u := by
    exact Nat.mul_le_mul_right u (Nat.mul_le_mul_left 2 hpow)
  have hpos : 0 < 4 ^ a := by positivity
  have hfour : (2 ^ a) ^ 2 = 4 ^ a := by
    calc
      (2 ^ a) ^ 2 = 2 ^ (a * 2) := by rw [pow_mul]
      _ = 2 ^ (2 * a) := by rw [Nat.mul_comm]
      _ = (2 ^ 2) ^ a := by rw [pow_mul]
      _ = 4 ^ a := by norm_num
  have hrhs : (2 ^ (a + 1) * u) ^ 2 = 4 * 4 ^ a * u ^ 2 := by
    rw [pow_succ]
    calc
      (2 ^ a * 2 * u) ^ 2 = 4 * (2 ^ a) ^ 2 * u ^ 2 := by ring
      _ = 4 * 4 ^ a * u ^ 2 := by rw [hfour]
  calc
    2 * 3 ^ a * u ≤ 2 * 4 ^ a * u := hmul
    _ ≤ (2 ^ (a + 1) * u) ^ 2 := by
      rw [hrhs]
      nlinarith

/-- The first odd-step numerator for `2^(y+3)+1` has exactly the displayed
factorization by four. -/
theorem pure_family_factorization (y : ℕ) :
    oddNumerator (2 ^ (y + 3) + 1) = 4 * (3 * 2 ^ (y + 1) + 1) := by
  simp [oddNumerator, pow_add]
  ring

/-- After removing the displayed factor four, the pure-family value is smaller
than its starting value. -/
theorem pure_family_decreases (y : ℕ) :
    3 * 2 ^ (y + 1) + 1 < 2 ^ (y + 3) + 1 := by
  simp [pow_add]
  have hpos : 0 < 2 ^ y := by positivity
  ring_nf at ⊢
  omega

/-- The cofactor in the pure-family factorization is odd, so the displayed
factor four is exact. -/
theorem pure_family_cofactor_odd (y : ℕ) : Odd (3 * 2 ^ (y + 1) + 1) := by
  use 3 * 2 ^ y
  simp [pow_succ]
  ring

/-! ## General controlled family `2^(y+3)m + 1` -/

theorem general_controlled_factorization (y m : ℕ) :
    oddNumerator (2 ^ (y + 3) * m + 1) =
      4 * (3 * 2 ^ (y + 1) * m + 1) := by
  simp [oddNumerator, pow_add]
  ring

theorem general_controlled_cofactor_odd (y m : ℕ) :
    Odd (3 * 2 ^ (y + 1) * m + 1) := by
  use 3 * 2 ^ y * m
  simp [pow_succ]
  ring

theorem general_controlled_decreases (y m : ℕ) (hm : 0 < m) :
    3 * 2 ^ (y + 1) * m + 1 < 2 ^ (y + 3) * m + 1 := by
  simp [pow_add]
  have hy : 0 < 2 ^ y := by positivity
  nlinarith

/-- The smallest support example already disproves a simple shift of every
positive binary exponent: `9 = 1 + 8` maps to `7 = 1 + 2 + 4`. -/
theorem support_shift_counterexample :
    oddNumerator 9 / 4 = 7 ∧ 7 = 1 + 2 + 4 := by
  norm_num [oddNumerator]

/-! ## Further sparse starting families -/

/-- The family `2^(y+4)+3` has valuation exactly one at its first odd step. -/
theorem power_plus_three_factorization (y : ℕ) :
    oddNumerator (2 ^ (y + 4) + 3) = 2 * (3 * 2 ^ (y + 3) + 5) := by
  simp [oddNumerator, pow_add]
  ring

theorem power_plus_three_cofactor_odd (y : ℕ) :
    Odd (3 * 2 ^ (y + 3) + 5) := by
  use 3 * 2 ^ (y + 2) + 2
  simp [pow_add]
  ring

theorem power_plus_three_increases (y : ℕ) :
    2 ^ (y + 4) + 3 < 3 * 2 ^ (y + 3) + 5 := by
  simp [pow_add]
  have hpos : 0 < 2 ^ y := by positivity
  nlinarith

/-- A two-power family with lower exponent at least three and exponent gap at
least three again has a factorization by four. -/
theorem two_power_family_factorization (z d : ℕ) :
    oddNumerator (2 ^ (z + d + 6) + 2 ^ (z + 3) + 1) =
      4 * (3 * 2 ^ (z + d + 4) + 3 * 2 ^ (z + 1) + 1) := by
  simp [oddNumerator, pow_add]
  ring

theorem two_power_family_cofactor_odd (z d : ℕ) :
    Odd (3 * 2 ^ (z + d + 4) + 3 * 2 ^ (z + 1) + 1) := by
  use 3 * 2 ^ (z + d + 3) + 3 * 2 ^ z
  simp [pow_add]
  ring

theorem two_power_family_decreases (z d : ℕ) :
    3 * 2 ^ (z + d + 4) + 3 * 2 ^ (z + 1) + 1 <
      2 ^ (z + d + 6) + 2 ^ (z + 3) + 1 := by
  simp [pow_add]
  have hz : 0 < 2 ^ z := by positivity
  have hzd : 0 < 2 ^ (z + d) := by positivity
  ring_nf at ⊢
  omega

/-! ## Accumulated additive terms -/

/-- Two prescribed accelerated steps already contain an additive correction.
The hypotheses encode exact divisibility equations without assuming that every
choice of `k` and `l` occurs on a Collatz orbit. -/
theorem two_step_scaled_identity
    (a b c k l : ℕ)
    (h₁ : 2 ^ k * b = 3 * a + 1)
    (h₂ : 2 ^ l * c = 3 * b + 1) :
    2 ^ (k + l) * c = 9 * a + 3 + 2 ^ k := by
  calc
    2 ^ (k + l) * c = 2 ^ k * (2 ^ l * c) := by
      rw [pow_add]
      ring
    _ = 2 ^ k * (3 * b + 1) := by rw [h₂]
    _ = 3 * (2 ^ k * b) + 2 ^ k := by ring
    _ = 3 * (3 * a + 1) + 2 ^ k := by rw [h₁]
    _ = 9 * a + 3 + 2 ^ k := by ring

/-! ## Binary and ternary prefix coordinates

The finite-iterate identity determines a residue class for the current tail
modulo a power of three.  These lemmas formalize that unconditional algebra.
They do not assert that the dynamically selected residue is equidistributed.
-/

/-- Reducing the finite-iterate identity modulo `3^t` forces the current tail
into its exact ternary residue class. -/
theorem tail_residue_from_iterate_identity
    (K t nTail n0 A : ℕ)
    (hiterate : 2 ^ K * nTail = 3 ^ t * n0 + A) :
    (2 ^ K * nTail) % (3 ^ t) = A % (3 ^ t) := by
  rw [hiterate]
  simp [Nat.add_mod]

/-- Every exact inverse branch has a strict Archimedean scale inequality.
For `k = 1` this is the expanding factor behind the obstruction to a
one-step anchored contraction estimate. -/
theorem inverse_branch_strict_scale
    (k m n : ℕ)
    (hbranch : 2 ^ k * m = 3 * n + 1) :
    3 * n < 2 ^ k * m := by
  omega

/-- A valuation-one forward branch strictly increases its odd value. -/
theorem valuation_one_branch_increases
    (m n : ℕ)
    (hbranch : 2 * m = 3 * n + 1) :
    n < m := by
  omega

/-! ## Surplus-certificate algebra

The following real-variable lemmas formalize the algebra behind the normalized
descent certificate and the weighted-history reformulation.  They do not assert
that a suitable certificate occurs on every Collatz orbit.
-/

/-- The normalized ratio `nr / n = 1 / M + Q / (3n)` is below one exactly
when the multiplicative surplus overcomes the burden `Q`. -/
theorem normalized_descent_iff
    (n nr M Q : ℝ) (hn : 0 < n) (hM : 0 < M)
    (hratio : nr / n = 1 / M + Q / (3 * n)) :
    nr < n ↔ 1 < M * (1 - Q / (3 * n)) := by
  have hMinv : M * (1 / M) = 1 := by
    field_simp [ne_of_gt hM]
  constructor
  · intro hnr
    have hlt : 1 / M + Q / (3 * n) < 1 := by
      rw [← hratio]
      exact (div_lt_one hn).2 hnr
    have hmul := mul_lt_mul_of_pos_left hlt hM
    rw [mul_add, hMinv] at hmul
    nlinarith
  · intro hcert
    have hnum : 1 + M * (Q / (3 * n)) < M := by
      nlinarith
    have hfrac : (1 + M * (Q / (3 * n))) / M < 1 :=
      (div_lt_one hM).2 hnum
    have hrearrange :
        (1 + M * (Q / (3 * n))) / M =
          1 / M + Q / (3 * n) := by
      field_simp [ne_of_gt hM]
    rw [hrearrange, ← hratio] at hfrac
    exact (div_lt_one hn).1 hfrac

/-- Replacing `Q` by `P / M` gives the weighted-history form of the ratio. -/
theorem history_ratio_rewrite
    (n M P : ℝ) (hn : n ≠ 0) (hM : M ≠ 0) :
    1 / M + (P / M) / (3 * n) = (1 + P / (3 * n)) / M := by
  field_simp [hn, hM]

/-- In weighted-history variables, descent is equivalent to the current
surplus power exceeding `1 + P/(3n)`. -/
theorem history_descent_iff
    (n nr M P : ℝ) (hn : 0 < n) (hM : 0 < M)
    (hratio : nr / n = (1 + P / (3 * n)) / M) :
    nr < n ↔ 1 + P / (3 * n) < M := by
  constructor
  · intro hnr
    have hlt : nr / n < 1 := (div_lt_one hn).2 hnr
    rw [hratio] at hlt
    exact (div_lt_one hM).1 hlt
  · intro hhist
    have hlt : (1 + P / (3 * n)) / M < 1 :=
      (div_lt_one hM).2 hhist
    rw [← hratio] at hlt
    exact (div_lt_one hn).1 hlt

/-! ## First-crossing certificates

At a first crossing of the critical valuation line, every earlier surplus
weight is at most one.  The next two lemmas formalize the resulting bound
`P_r ≤ r` and its exact descent consequence.  They are purely finite
statements and do not assert that every orbit has such a crossing.
-/

/-- If every term in a prefix history is at most one, then its total burden is
at most the prefix length. -/
theorem first_crossing_history_bound
    (r : ℕ) (weight : ℕ → ℝ)
    (hweight : ∀ j ∈ Finset.range r, weight j ≤ 1) :
    ∑ j ∈ Finset.range r, weight j ≤ (r : ℝ) := by
  calc
    ∑ j ∈ Finset.range r, weight j
        ≤ ∑ _j ∈ Finset.range r, (1 : ℝ) := Finset.sum_le_sum hweight
    _ = (r : ℝ) := by simp

/-- The bound `P ≤ r`, together with a surplus larger than
`1 + r/(3n)`, gives strict descent at the first crossing. -/
theorem first_crossing_descent_certificate
    (r : ℕ) (n nr M P : ℝ)
    (hn : 0 < n) (hM : 0 < M)
    (hratio : nr / n = (1 + P / (3 * n)) / M)
    (hP : P ≤ (r : ℝ))
    (hcross : 1 + (r : ℝ) / (3 * n) < M) :
    nr < n := by
  apply (history_descent_iff n nr M P hn hM hratio).2
  have hden : 0 < 3 * n := mul_pos (by norm_num) hn
  have hfrac : P / (3 * n) ≤ (r : ℝ) / (3 * n) :=
    (div_le_div_iff_of_pos_right hden).2 hP
  nlinarith

/-- The integer power gap used in the finite Diophantine window implies the
normalized first-crossing threshold.  In applications `twoPow = 2^m` and
`threePow = 3^r`; this lemma isolates only the real algebra. -/
theorem diophantine_gap_certificate
    (n r twoPow threePow : ℝ)
    (hn : 0 < n)
    (hthree : 0 < threePow)
    (hgap : r * threePow < 3 * n * (twoPow - threePow)) :
    1 + r / (3 * n) < twoPow / threePow := by
  have h3n : 0 < 3 * n := by positivity
  have hratio : r * threePow / (3 * n) < twoPow - threePow := by
    apply (div_lt_iff₀ h3n).2
    nlinarith
  apply (lt_div_iff₀ hthree).2
  rw [add_mul]
  have hid : (r / (3 * n)) * threePow = r * threePow / (3 * n) := by ring
  rw [hid]
  nlinarith

/-- A uniform upper bound `C` on the burden yields the corrected sufficient
threshold `M > 1 / (1 - C/(3n))`. -/
theorem bounded_burden_certificate
    (n M Q C : ℝ) (hn : 0 < n) (hQC : Q ≤ C) (hC : C < 3 * n)
    (hthreshold : 1 / (1 - C / (3 * n)) < M) :
    1 < M * (1 - Q / (3 * n)) := by
  have hden : 0 < 3 * n := mul_pos (by norm_num) hn
  have hratio : Q / (3 * n) ≤ C / (3 * n) :=
    (div_le_div_iff_of_pos_right hden).2 hQC
  have hgap : 0 < 1 - C / (3 * n) := by
    have : C / (3 * n) < 1 := (div_lt_one hden).2 hC
    linarith
  have hMpos : 0 < M := by
    have hinv : 0 < 1 / (1 - C / (3 * n)) := one_div_pos.mpr hgap
    linarith
  have hbase : 1 < M * (1 - C / (3 * n)) :=
    (div_lt_iff₀ hgap).1 hthreshold
  have hfactor : 1 - C / (3 * n) ≤ 1 - Q / (3 * n) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hfactor (le_of_lt hMpos)
  exact hbase.trans_le hmul

/-- Solving the scalar recurrence used when every descent certificate fails. -/
theorem weighted_history_geometric_bound
    (P : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hzero : P 0 = 0)
    (hstep : ∀ r, P (r + 1) ≤ (1 + c) * P r + 1) :
    ∀ r, P r ≤ ((1 + c) ^ r - 1) / c := by
  intro r
  induction r with
  | zero => simp [hzero]
  | succ r ihr =>
      calc
        P (r + 1) ≤ (1 + c) * P r + 1 := hstep r
        _ ≤ (1 + c) * (((1 + c) ^ r - 1) / c) + 1 := by
          have hcoef : 0 ≤ 1 + c := by linarith
          have hmul := mul_le_mul_of_nonneg_left ihr hcoef
          nlinarith
        _ = ((1 + c) ^ (r + 1) - 1) / c := by
          field_simp [ne_of_gt hc]
          ring

/-- A finite family dominated by a geometric suffix profile has the stated
uniform sum bound.  Substituting `x = 2⁻ᵟ` and `C = 2ᴮ` gives the manuscript's
suffix-excess estimate. -/
theorem suffix_geometric_bound
    (r : ℕ) (w : ℕ → ℝ) (C x : ℝ)
    (hC : 0 ≤ C) (hx : 0 ≤ x) (hxone : x < 1)
    (hw : ∀ h ∈ Finset.range r, w h ≤ C * x ^ (h + 1)) :
    ∑ h ∈ Finset.range r, w h ≤ C * x / (1 - x) := by
  have hterm :
      ∑ h ∈ Finset.range r, w h ≤
        ∑ h ∈ Finset.range r, C * x ^ (h + 1) :=
    Finset.sum_le_sum hw
  have hfactor :
      ∑ h ∈ Finset.range r, C * x ^ (h + 1) =
        (C * x) * ∑ h ∈ Finset.range r, x ^ h := by
    calc
      ∑ h ∈ Finset.range r, C * x ^ (h + 1) =
          ∑ h ∈ Finset.range r, (C * x) * x ^ h := by
            apply Finset.sum_congr rfl
            intro h hh
            rw [pow_succ]
            ring
      _ = (C * x) * ∑ h ∈ Finset.range r, x ^ h := by
        rw [Finset.mul_sum]
  have hgeom :
      ∑ h ∈ Finset.range r, x ^ h ≤ 1 / (1 - x) := by
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := r) hx hxone
    simpa using h
  calc
    ∑ h ∈ Finset.range r, w h
        ≤ ∑ h ∈ Finset.range r, C * x ^ (h + 1) := hterm
    _ = (C * x) * ∑ h ∈ Finset.range r, x ^ h := hfactor
    _ ≤ (C * x) * (1 / (1 - x)) := by
      exact mul_le_mul_of_nonneg_left hgeom (mul_nonneg hC hx)
    _ = C * x / (1 - x) := by ring

/-! ## Recovery blocks after expanding runs

The manuscript combines the exact burden inherited from a run of expanding
steps with the geometric suffix bound.  The next lemma isolates the final
algebraic implication.  Here `X` is the recovery factor `2^R`, `C` bounds the
burden created inside the recovery block, and `Q` is the total burden after the
block.  The hypothesis `Q < C + 3 / X` is the bound obtained by propagating the
exact expanding-run burden through the block.
-/

/-- An explicit recovery threshold converts a total burden bound into the
normalized descent certificate. -/
theorem recovery_block_certificate
    (n X Q C : ℝ) (hn : 0 < n) (hX : 0 < X)
    (hQ : Q < C + 3 / X) (hC : C < 3 * n)
    (hthreshold : 3 * (n + 1) / (3 * n - C) < X) :
    1 < X * (1 - Q / (3 * n)) := by
  have hn3 : 0 < 3 * n := mul_pos (by norm_num) hn
  have hden : 0 < 3 * n - C := by linarith
  have hscaled : 3 * (n + 1) < X * (3 * n - C) := by
    exact (div_lt_iff₀ hden).1 hthreshold
  have hQdiv : Q / (3 * n) < (C + 3 / X) / (3 * n) := by
    exact (div_lt_div_iff_of_pos_right hn3).2 hQ
  have hcert :
      X * (1 - (C + 3 / X) / (3 * n)) <
        X * (1 - Q / (3 * n)) := by
    have hfactor :
        1 - (C + 3 / X) / (3 * n) < 1 - Q / (3 * n) := by
      linarith
    exact mul_lt_mul_of_pos_left hfactor hX
  have hbase : 1 < X * (1 - (C + 3 / X) / (3 * n)) := by
    field_simp [ne_of_gt hn, ne_of_gt hX]
    nlinarith
  exact hbase.trans hcert

/-- The threshold can equivalently be expressed without a quotient. -/
theorem recovery_threshold_iff
    (n X C : ℝ) (hC : C < 3 * n) :
    3 * (n + 1) / (3 * n - C) < X ↔
      3 * (n + 1) < X * (3 * n - C) := by
  have hden : 0 < 3 * n - C := by linarith
  exact div_lt_iff₀ hden

/-! ## Inverse-history weights and profile certificates

For a valuation word of length `r` and total valuation `K`, the inverse-orbit
weight `3^r / 2^K` is the reciprocal of the multiplicative surplus
`2^K / 3^r`.  This is the exact algebraic bridge to weighted inverse-history
constructions.
-/

/-- The inverse-history weight is the reciprocal multiplicative surplus. -/
theorem inverse_history_weight_eq_reciprocal (r K : ℕ) :
    (3 : ℝ) ^ r / (2 : ℝ) ^ K =
      1 / ((2 : ℝ) ^ K / (3 : ℝ) ^ r) := by
  have htwo : (2 : ℝ) ^ K ≠ 0 := by positivity
  have hthree : (3 : ℝ) ^ r ≠ 0 := by positivity
  field_simp [htwo, hthree]

/-- A reverse prefix is algebraically the corresponding forward suffix
surplus. `Kr` and `Kprev` stand for the valuation totals at the two endpoints. -/
theorem reverse_prefix_surplus_identity
    (Kr Kprev α : ℝ) (r t : ℕ) (ht : t ≤ r) :
    (Kr - (r : ℝ) * α) - (Kprev - ((r - t : ℕ) : ℝ) * α) =
      (Kr - Kprev) - (t : ℝ) * α := by
  rw [Nat.cast_sub ht]
  ring

/-- The positive affine offset in a genuine finite iterate gives the source
charge inequality used to convert inverse-history mass into an integer count. -/
theorem inverse_history_source_charge
    (r K : ℕ) (x R offset : ℝ)
    (hoffset : 0 < offset)
    (hiterate : (2 : ℝ) ^ K * R = (3 : ℝ) ^ r * x + offset) :
    x * ((3 : ℝ) ^ r / (2 : ℝ) ^ K) < R := by
  have htwo : 0 < (2 : ℝ) ^ K := by positivity
  have hscaled : (3 : ℝ) ^ r * x < (2 : ℝ) ^ K * R := by
    nlinarith
  calc
    x * ((3 : ℝ) ^ r / (2 : ℝ) ^ K) =
        ((3 : ℝ) ^ r * x) / (2 : ℝ) ^ K := by ring
    _ < ((2 : ℝ) ^ K * R) / (2 : ℝ) ^ K :=
      (div_lt_div_iff_of_pos_right htwo).2 hscaled
    _ = R := by field_simp

/-- Any termwise upper profile for the historical burden yields a finite
descent certificate once the sum of the profile is below `3n` and the
multiplicative surplus exceeds the corresponding threshold. -/
theorem profile_burden_certificate
    (ι : Type*) [Fintype ι]
    (n M Q : ℝ) (term cap : ι → ℝ)
    (hn : 0 < n)
    (hQ : Q = ∑ i, term i)
    (hprofile : ∀ i, term i ≤ cap i)
    (hcap : ∑ i, cap i < 3 * n)
    (hthreshold : 1 / (1 - (∑ i, cap i) / (3 * n)) < M) :
    1 < M * (1 - Q / (3 * n)) := by
  have hQC : Q ≤ ∑ i, cap i := by
    rw [hQ]
    exact Finset.sum_le_sum fun i _ => hprofile i
  exact bounded_burden_certificate n M Q (∑ i, cap i)
    hn hQC hcap hthreshold

/-! ## Nested least representatives

The large-bit section of the manuscript reduces exclusion of an infinite
noncrossing corridor to escape of the least positive representatives of its
nested finite-prefix cylinders.  The following theorem isolates the general
order-theoretic argument.  It assumes the nested sets and their minima; it does
not prove that the Collatz survivor sets have any quantitative growth rate.
-/

/-- If every integer eventually leaves a nested family, then every finite
initial interval is absent at one common horizon. -/
theorem nested_finite_prefix_avoided
    (C : ℕ → Set ℕ)
    (hnested : ∀ {r s : ℕ}, r ≤ s → C s ⊆ C r)
    (hescape : ∀ n : ℕ, ∃ r : ℕ, n ∉ C r) :
    ∀ B : ℕ, ∃ r : ℕ, ∀ n : ℕ, n ≤ B → n ∉ C r := by
  intro B
  induction B with
  | zero =>
      obtain ⟨r, hr⟩ := hescape 0
      refine ⟨r, ?_⟩
      intro n hn
      have hn0 : n = 0 := by omega
      simpa [hn0] using hr
  | succ B ih =>
      obtain ⟨r, hr⟩ := ih
      obtain ⟨s, hs⟩ := hescape (B + 1)
      refine ⟨max r s, ?_⟩
      intro n hn hmem
      by_cases hle : n ≤ B
      · exact hr n hle (hnested (Nat.le_max_left r s) hmem)
      · have heq : n = B + 1 := by omega
        apply hs
        rw [← heq]
        exact hnested (Nat.le_max_right r s) hmem

/-- For nested nonempty subsets of the naturals with specified least elements,
absence of a common survivor is equivalent to the least representatives
tending to infinity. -/
theorem nested_least_representatives_escape_iff
    (C : ℕ → Set ℕ) (L : ℕ → ℕ)
    (hnested : ∀ {r s : ℕ}, r ≤ s → C s ⊆ C r)
    (hmem : ∀ r : ℕ, L r ∈ C r)
    (hleast : ∀ r n : ℕ, n ∈ C r → L r ≤ n) :
    (∀ n : ℕ, ∃ r : ℕ, n ∉ C r) ↔
      Filter.Tendsto L Filter.atTop Filter.atTop := by
  constructor
  · intro hescape
    have hmono : Monotone L := by
      intro r s hrs
      exact hleast r (L s) (hnested hrs (hmem s))
    apply hmono.tendsto_atTop_atTop_iff.2
    intro B
    obtain ⟨r, hr⟩ := nested_finite_prefix_avoided C hnested hescape B
    refine ⟨r, ?_⟩
    by_contra hnot
    exact hr (L r) (Nat.le_of_not_ge hnot) (hmem r)
  · intro htend n
    rw [Filter.tendsto_atTop_atTop] at htend
    obtain ⟨r, hr⟩ := htend (n + 1)
    refine ⟨r, ?_⟩
    intro hnmem
    have hlow : L r ≤ n := hleast r n hnmem
    have hhigh : n + 1 ≤ L r := hr r (le_refl r)
    omega

end CollatzLocal
