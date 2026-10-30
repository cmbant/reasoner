import Mathlib

/-!
# Fixed-point ball arithmetic for the AH-6 certificate (`lem:seven-joint-scalar-majorant`)

Source of the finite checks: `ResearchNotes/QI/seven_qubit_entanglement/joint_entropy_analytic_proof.tex`
(`sec:seven-joint-analytic-proof`), verifier `code/verify_seven_entropy_joint_majorant.py`.

The Python verifier uses outward-rounded dyadic interval arithmetic.  Here the same arithmetic is a kernel
computation on integers.  A `Ball` is `(m, r, ok)`: the integers `m` and `r` encode the real interval
`[(m - r)/SC, (m + r)/SC]` with the global fixed-point scale `SC = 2^192`, and `ok` is a validity flag that is
cleared when a division by a ball containing zero was attempted.  The relation `Enc x b` ("the real `x` is enclosed
by `b`") is `b.ok = true → |x * SC - m| ≤ r`, so every operation is sound by a one-line statement, and an invalid ball
encloses everything vacuously but is rejected by the final checks (`Ball.pos`).

Only `Int`/`Nat` operations are used (no `Rat`, no well-founded recursion), so the kernel evaluates them with
GMP-accelerated arithmetic (`decide +kernel`).

* `Ball.add`, `Ball.mul`, `Ball.neg`, `Ball.inv` and `Ball.ofInt`, with the soundness lemmas `Enc.add`, `Enc.mul`,
  `Enc.neg`, `Enc.inv`, `Enc.intCast`;
* `Enc.pos`: a ball with `pos b = true` encloses a strictly positive real.
-/

namespace FormalResearch.FourQubitEntropy.AH6

/-- The fixed-point scale. -/
def SC : ℕ := 2 ^ 192

theorem SC_pos : 0 < SC := by unfold SC; positivity

theorem SC_real_pos : (0 : ℝ) < (SC : ℝ) := by exact_mod_cast SC_pos

/-- A ball with integer midpoint `m` and radius `r` (scaled by `SC`) and a validity flag. -/
structure Ball where
  m : ℤ
  r : ℕ
  ok : Bool

namespace Ball

/-- The ball enclosing the integer `n`. -/
def ofInt (n : ℤ) : Ball := ⟨n * SC, 0, true⟩

protected def add (a b : Ball) : Ball := ⟨a.m + b.m, a.r + b.r, a.ok && b.ok⟩

protected def neg (a : Ball) : Ball := ⟨-a.m, a.r, a.ok⟩

/-- Product: the midpoint is rounded down, and the radius absorbs the rounding and the cross terms. -/
protected def mul (a b : Ball) : Ball :=
  ⟨a.m * b.m / (SC : ℤ), (a.m.natAbs * b.r + b.m.natAbs * a.r + a.r * b.r) / SC + 2, a.ok && b.ok⟩

/-- Reciprocal of a ball with positive lower end. -/
def invPos (a : Ball) : Ball :=
  ⟨((SC : ℤ) * SC / (a.m + a.r) + ((SC : ℤ) * SC / (a.m - a.r) + 1)) / 2,
   (((SC : ℤ) * SC / (a.m - a.r) + 1) -
      ((SC : ℤ) * SC / (a.m + a.r) + ((SC : ℤ) * SC / (a.m - a.r) + 1)) / 2).toNat,
   a.ok && decide ((a.r : ℤ) < a.m)⟩

/-- Reciprocal of a ball whose enclosure excludes zero (otherwise the result is invalid). -/
protected def inv (a : Ball) : Ball :=
  if (a.r : ℤ) < a.m then invPos a
  else if a.m < -(a.r : ℤ) then Ball.neg (invPos (Ball.neg a))
  else ⟨0, 0, false⟩

/-- Check that a ball is valid and encloses a strictly positive number. -/
def pos (a : Ball) : Bool := a.ok && decide ((a.r : ℤ) < a.m)

/-- Check that a ball is valid and excludes zero. -/
def nz (a : Ball) : Bool := a.ok && (decide ((a.r : ℤ) < a.m) || decide (a.m < -(a.r : ℤ)))

instance : Add Ball := ⟨Ball.add⟩
instance : Neg Ball := ⟨Ball.neg⟩
instance : Mul Ball := ⟨Ball.mul⟩
instance : Inv Ball := ⟨Ball.inv⟩
instance : IntCast Ball := ⟨ofInt⟩

end Ball

/-- `x` is enclosed by the ball `b` (vacuous for an invalid ball). -/
def Enc (x : ℝ) (b : Ball) : Prop :=
  b.ok = true → |x * (SC : ℝ) - (b.m : ℝ)| ≤ (b.r : ℝ)

theorem Enc.intCast (n : ℤ) : Enc (n : ℝ) (n : Ball) := by
  intro _
  show |(n : ℝ) * (SC : ℝ) - ((n * SC : ℤ) : ℝ)| ≤ ((0 : ℕ) : ℝ)
  simp

theorem Enc.add {x y : ℝ} {a b : Ball} (hx : Enc x a) (hy : Enc y b) : Enc (x + y) (a + b) := by
  intro h
  have h' : a.ok = true ∧ b.ok = true := by
    have h0 : (a.ok && b.ok) = true := h
    exact Bool.and_eq_true_iff.mp h0
  have h1 := hx h'.1
  have h2 := hy h'.2
  show |(x + y) * (SC : ℝ) - ((a.m + b.m : ℤ) : ℝ)| ≤ ((a.r + b.r : ℕ) : ℝ)
  push_cast
  calc |(x + y) * (SC : ℝ) - (↑a.m + ↑b.m)|
      = |(x * SC - a.m) + (y * SC - b.m)| := by ring_nf
    _ ≤ |x * SC - a.m| + |y * SC - b.m| := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2

theorem Enc.neg {x : ℝ} {a : Ball} (hx : Enc x a) : Enc (-x) (-a) := by
  intro h
  have h1 := hx h
  show |(-x) * (SC : ℝ) - ((-a.m : ℤ) : ℝ)| ≤ (a.r : ℝ)
  push_cast
  calc |(-x) * (SC : ℝ) - -(a.m : ℝ)| = |x * SC - a.m| := by
        rw [← abs_neg]; ring_nf
    _ ≤ _ := h1

theorem Enc.mul {x y : ℝ} {a b : Ball} (hx : Enc x a) (hy : Enc y b) : Enc (x * y) (a * b) := by
  intro h
  have h' : a.ok = true ∧ b.ok = true := by
    have h0 : (a.ok && b.ok) = true := h
    exact Bool.and_eq_true_iff.mp h0
  have h1 := hx h'.1
  have h2 := hy h'.2
  show |x * y * (SC : ℝ) - ((a.m * b.m / (SC : ℤ) : ℤ) : ℝ)| ≤
    (((a.m.natAbs * b.r + b.m.natAbs * a.r + a.r * b.r) / SC + 2 : ℕ) : ℝ)
  set t : ℕ := a.m.natAbs * b.r + b.m.natAbs * a.r + a.r * b.r with ht
  have hSC := SC_real_pos
  -- the cross terms
  have hcross : |(x * SC - a.m) * (y * SC - b.m) + a.m * (y * SC - b.m) + b.m * (x * SC - a.m)|
      ≤ (t : ℝ) := by
    have e1 : |(x * SC - a.m) * (y * SC - b.m)| ≤ (a.r : ℝ) * b.r := by
      rw [abs_mul]; exact mul_le_mul h1 h2 (abs_nonneg _) (Nat.cast_nonneg _)
    have e2 : |(a.m : ℝ) * (y * SC - b.m)| ≤ (a.m.natAbs : ℝ) * b.r := by
      rw [abs_mul]
      have : |(a.m : ℝ)| = (a.m.natAbs : ℝ) := by
        rw [Nat.cast_natAbs]; simp
      rw [this]; exact mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
    have e3 : |(b.m : ℝ) * (x * SC - a.m)| ≤ (b.m.natAbs : ℝ) * a.r := by
      rw [abs_mul]
      have : |(b.m : ℝ)| = (b.m.natAbs : ℝ) := by
        rw [Nat.cast_natAbs]; simp
      rw [this]; exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
    calc _ ≤ |(x * SC - a.m) * (y * SC - b.m) + a.m * (y * SC - b.m)| + |b.m * (x * SC - a.m)| :=
          abs_add_le _ _
      _ ≤ |(x * SC - a.m) * (y * SC - b.m)| + |a.m * (y * SC - b.m)| + |b.m * (x * SC - a.m)| :=
          by gcongr; exact abs_add_le _ _
      _ ≤ _ := by
          have : (t : ℝ) = (a.m.natAbs : ℝ) * b.r + (b.m.natAbs : ℝ) * a.r + (a.r : ℝ) * b.r := by
            rw [ht]; push_cast; ring
          rw [this]; linarith
  -- XY = m1 m2 + cross
  have hXY : (x * SC) * (y * SC) = (a.m : ℝ) * b.m +
      ((x * SC - a.m) * (y * SC - b.m) + a.m * (y * SC - b.m) + b.m * (x * SC - a.m)) := by ring
  -- floor
  have hq1 : ((a.m * b.m / (SC : ℤ) : ℤ) : ℝ) * SC ≤ (a.m : ℝ) * b.m := by
    have := Int.ediv_mul_le (a.m * b.m) (by exact_mod_cast SC_pos.ne' : (SC : ℤ) ≠ 0)
    exact_mod_cast this
  have hq2 : (a.m : ℝ) * b.m < (((a.m * b.m / (SC : ℤ) : ℤ) : ℝ) + 1) * SC := by
    have := Int.lt_ediv_add_one_mul_self (a.m * b.m) (by exact_mod_cast SC_pos : (0 : ℤ) < (SC : ℤ))
    exact_mod_cast this
  set M : ℝ := ((a.m * b.m / (SC : ℤ) : ℤ) : ℝ) with hM
  have hdiv : (t : ℝ) < ((t / SC : ℕ) : ℝ) * SC + SC := by
    have h3 := Nat.div_add_mod t SC
    have h4 := Nat.mod_lt t SC_pos
    have h5 : (t : ℝ) = ((t / SC : ℕ) : ℝ) * SC + ((t % SC : ℕ) : ℝ) := by
      have : t = (t / SC) * SC + t % SC := by rw [mul_comm]; exact h3.symm
      exact_mod_cast this
    have h6 : ((t % SC : ℕ) : ℝ) < SC := by exact_mod_cast h4
    linarith
  set cr : ℝ := (x * SC - a.m) * (y * SC - b.m) + a.m * (y * SC - b.m) + b.m * (x * SC - a.m) with hcr
  have key : (x * y * SC - M) * SC = ((a.m : ℝ) * b.m - M * SC) + cr := by
    linear_combination hXY
  have hb1 : |(a.m : ℝ) * b.m - M * SC| ≤ SC := by
    rw [abs_le]; constructor <;> nlinarith [hq1, hq2]
  have hmain : |x * y * SC - M| * SC ≤ SC + t := by
    have : |x * y * SC - M| * SC = |((a.m : ℝ) * b.m - M * SC) + cr| := by
      rw [← abs_of_pos hSC, ← abs_mul, abs_of_pos hSC, key]
    rw [this]
    calc _ ≤ |(a.m : ℝ) * b.m - M * SC| + |cr| := abs_add_le _ _
      _ ≤ SC + t := add_le_add hb1 hcross
  have hfin : |x * y * SC - M| ≤ ((t / SC : ℕ) : ℝ) + 2 := by
    by_contra hcon
    push Not at hcon
    have : (((t / SC : ℕ) : ℝ) + 2) * SC < |x * y * SC - M| * SC :=
      mul_lt_mul_of_pos_right hcon hSC
    nlinarith
  push_cast at hfin ⊢
  exact hfin

theorem Enc.invPos {x : ℝ} {a : Ball} (hx : Enc x a) : Enc x⁻¹ (Ball.invPos a) := by
  intro h
  have h' : a.ok = true ∧ (a.r : ℤ) < a.m := by
    simpa [Ball.invPos] using h
  obtain ⟨hok, hlt⟩ := h'
  have h1 := hx hok
  have hSC := SC_real_pos
  have hlt' : (a.r : ℝ) < a.m := by exact_mod_cast hlt
  rw [abs_le] at h1
  set X : ℝ := x * SC with hX
  have hXpos : 0 < X := by linarith [h1.1]
  have hxpos : 0 < x := by
    by_contra hneg; push Not at hneg
    have : X ≤ 0 := by rw [hX]; exact mul_nonpos_of_nonpos_of_nonneg hneg hSC.le
    linarith
  have hz : x⁻¹ * (SC : ℝ) = (SC : ℝ) * SC / X := by
    rw [hX]; field_simp
  -- the integer bounds
  have hpm : (0 : ℤ) < a.m + a.r := by have := Int.natCast_nonneg a.r; omega
  have hmm : (0 : ℤ) < a.m - a.r := by omega
  set lo : ℤ := (SC : ℤ) * SC / (a.m + a.r) with hlo
  set q : ℤ := (SC : ℤ) * SC / (a.m - a.r) with hq
  have hlo1 : (lo : ℝ) * (a.m + a.r) ≤ (SC : ℝ) * SC := by
    have := Int.ediv_mul_le ((SC : ℤ) * SC) hpm.ne'
    exact_mod_cast this
  have hq1 : (SC : ℝ) * SC < ((q : ℝ) + 1) * (a.m - a.r) := by
    have := Int.lt_ediv_add_one_mul_self ((SC : ℤ) * SC) hmm
    exact_mod_cast this
  have hpmR : (0 : ℝ) < a.m + a.r := by exact_mod_cast hpm
  have hmmR : (0 : ℝ) < a.m - a.r := by exact_mod_cast hmm
  have hlz : (lo : ℝ) ≤ (SC : ℝ) * SC / X := by
    rw [le_div_iff₀ hXpos]
    nlinarith [h1.2, hlo1]
  have hzh : (SC : ℝ) * SC / X ≤ (q : ℝ) + 1 := by
    rw [div_le_iff₀ hXpos]
    nlinarith [h1.1, hq1]
  have hlh : lo ≤ q + 1 := by
    have : (lo : ℝ) ≤ (q + 1 : ℤ) := by push_cast; linarith
    exact_mod_cast this
  set mid : ℤ := (lo + (q + 1)) / 2 with hmid
  have hm1 : mid * 2 ≤ lo + (q + 1) := Int.ediv_mul_le _ (by norm_num)
  have hm2 : lo + (q + 1) < (mid + 1) * 2 := Int.lt_ediv_add_one_mul_self _ (by norm_num)
  have hmh : mid ≤ q + 1 := by omega
  show |x⁻¹ * (SC : ℝ) - ((mid : ℤ) : ℝ)| ≤ (((q + 1 - mid).toNat : ℕ) : ℝ)
  have hnat : (((q + 1 - mid).toNat : ℕ) : ℝ) = ((q + 1 - mid : ℤ) : ℝ) := by
    have : (((q + 1 - mid).toNat : ℕ) : ℤ) = q + 1 - mid := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  rw [hnat, hz]
  have hm1R : (mid : ℝ) * 2 ≤ lo + (q + 1) := by exact_mod_cast hm1
  push_cast
  rw [abs_le]
  constructor <;> linarith

theorem Enc.inv {x : ℝ} {a : Ball} (hx : Enc x a) : Enc x⁻¹ (a⁻¹) := by
  show Enc x⁻¹ (Ball.inv a)
  unfold Ball.inv
  by_cases h1 : (a.r : ℤ) < a.m
  · simp only [h1, ite_true]; exact Enc.invPos hx
  · simp only [h1, ite_false]
    by_cases h2 : a.m < -(a.r : ℤ)
    · simp only [h2, ite_true]
      have := Enc.neg (Enc.invPos (Enc.neg hx))
      rw [inv_neg, neg_neg] at this
      exact this
    · simp only [h2, ite_false]
      intro h; simp at h

theorem Enc.sub {x y : ℝ} {a b : Ball} (hx : Enc x a) (hy : Enc y b) : Enc (x + -y) (a + -b) :=
  Enc.add hx (Enc.neg hy)

/-- A valid ball with `pos b = true` encloses a strictly positive real number. -/
theorem Enc.pos {x : ℝ} {a : Ball} (hx : Enc x a) (h : a.pos = true) : 0 < x := by
  have h' : a.ok = true ∧ (a.r : ℤ) < a.m := by simpa [Ball.pos] using h
  have h1 := hx h'.1
  have hlt : (a.r : ℝ) < a.m := by exact_mod_cast h'.2
  rw [abs_le] at h1
  have : 0 < x * (SC : ℝ) := by linarith [h1.1]
  exact (pos_iff_pos_of_mul_pos this).2 SC_real_pos

/-- A valid ball with `nz b = true` encloses a nonzero real number. -/
theorem Enc.ne_zero {x : ℝ} {a : Ball} (hx : Enc x a) (h : a.nz = true) : x ≠ 0 := by
  have h' : a.ok = true ∧ ((a.r : ℤ) < a.m ∨ a.m < -(a.r : ℤ)) := by
    simpa [Ball.nz] using h
  have h1 := hx h'.1
  intro h0
  rw [h0, zero_mul, zero_sub, abs_neg] at h1
  rcases h'.2 with h2 | h2
  · have : (a.r : ℝ) < a.m := by exact_mod_cast h2
    have := le_abs_self (a.m : ℝ)
    linarith
  · have : (a.m : ℝ) < -(a.r : ℝ) := by exact_mod_cast h2
    have := neg_abs_le (a.m : ℝ)
    linarith

theorem Ball.add_ok (a b : Ball) : (a + b).ok = (a.ok && b.ok) := rfl
theorem Ball.mul_ok (a b : Ball) : (a * b).ok = (a.ok && b.ok) := rfl
theorem Ball.neg_ok (a : Ball) : (-a).ok = a.ok := rfl

/-! The arithmetic is irreducible for the elaborator (so that unification never evaluates ball arithmetic on
numerals); the kernel certificate `decide +kernel` ignores this attribute. -/
attribute [irreducible] SC Ball.ofInt Ball.add Ball.neg Ball.mul Ball.invPos Ball.inv

end FormalResearch.FourQubitEntropy.AH6
