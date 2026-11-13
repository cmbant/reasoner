module

public import FormalResearch.Racah.P2RacahLattice
public import FormalResearch.Wigner.SpecialValues

/-!
# The `c = 0` endpoint row of the Racah lattice (Weyl P2, `eq:Racahdiagzero`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, proof of `thm:6jfiniteRacah`: "At a physical
`c = 0` endpoint, `A = B` and `m = n` make `Ω_R = 0`; the continued row `eq:Racahdiagzero` follows
directly from the `c = 0` and `c = 1` special `6j` formulas (DLMF 34.5.1 and 34.5.7)."

`Phi6_lattice_row_zero` is exactly that row: for `c = 0` physical,
`f(f+1) Φ_f(0) = -a_0^+ Φ_f(1) + b_0 Φ_f(0)` with `b_0 = -κ_R/2` (`bDiagZero`), the `a_0^-` term being
absent.  It uses `sixJ_zero_left` (DLMF 34.5.1) and `sixJ_one_left` (DLMF 34.5.7).  The by-products
`Phi6_zero_value` (`Φ_f(0) = 2A/√(4A²-m²)`, independent of `f`) and the removable-singularity
statement `omegaR_of_zero` (`A = B`, `m = n` give `Ω_R = 0`) are included.
-/

@[expose] public section

namespace FormalResearch.Racah.SixJ

open FormalResearch.Wigner

/-- `b_0 = -κ_R/2` (`eq:Racahdiagzero`). -/
noncomputable def bDiagZero (A B m n : ℝ) : ℝ := -(kapR A B m n) / 2

/-- `Ω_R = 0` when `A = B` and `m = n`. -/
theorem omegaR_of_zero (A m : ℝ) : omegaR A A m m = 0 := by
  unfold omegaR; ring

/-- The triangle `(0, x, y)` forces `x = y`. -/
lemma tri_zero_eq {x y : ℚ} (h : IsTri 0 x y) : x = y := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩, -⟩ := h
  have h1 : (0 : ℚ) ≤ p := by positivity
  have h2 : (0 : ℚ) ≤ q := by positivity
  linarith

lemma isNat_lt_one {x : ℚ} (h : IsNat x) (h1 : x < 1) : x = 0 := by
  obtain ⟨n, rfl⟩ := h
  have : n < 1 := by exact_mod_cast h1
  have : n = 0 := by omega
  simp [this]

/-- `Φ_f(0) = 2A / √((2a+2m+1)(2a+1))` at the `c = 0` endpoint (`b = a`, `n = m`). -/
theorem Phi6_zero_value (a f m : ℚ) (h : IsTri f (a + m) a) :
    Phi6 a a 0 f m m =
      2 * ((a : ℝ) + (m + 1) / 2) / Real.sqrt ((2 * ((a : ℝ) + m) + 1) * (2 * (a : ℝ) + 1)) := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩⟩ := h
  have hN : ((p + q + r : ℕ) : ℚ) = f + (a + m) + a := by push_cast; linarith
  have hA : (0 : ℝ) < (a : ℝ) + (m + 1) / 2 := by
    have hp' : (p : ℝ) = f + (a + m) - a := by exact_mod_cast hp.symm
    have hq' : (q : ℝ) = f - (a + m) + a := by exact_mod_cast hq.symm
    have hr' : (r : ℝ) = -f + (a + m) + a := by exact_mod_cast hr.symm
    have : (0 : ℝ) ≤ p := by positivity
    have : (0 : ℝ) ≤ q := by positivity
    have : (0 : ℝ) ≤ r := by positivity
    linarith
  unfold Phi6
  rw [W6_eq_rank_form, sixJ_zero_left ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩⟩ (p + q + r) hN]
  have e : a + a + 0 + f + m = ((p + q + r : ℕ) : ℚ) := by rw [hN]; ring
  rw [e, sgn_natCast]
  have hs : ((-1 : ℝ) ^ (p + q + r)) * (-1) ^ (p + q + r) = 1 := by
    rw [← mul_pow]; norm_num
  generalize ((-1 : ℝ) ^ (p + q + r)) = u at hs ⊢
  unfold wA wB
  push_cast
  have : Real.sqrt (((a : ℝ) + (m + 1) / 2) * ((a : ℝ) + (m + 1) / 2)) = (a : ℝ) + (m + 1) / 2 :=
    Real.sqrt_mul_self hA.le
  rw [this]
  have hP : 0 < Real.sqrt ((2 * ((a : ℝ) + m) + 1) * (2 * (a : ℝ) + 1)) := by
    apply Real.sqrt_pos.mpr
    have hq' : (q : ℝ) = f - (a + m) + a := by exact_mod_cast hq.symm
    have hr' : (r : ℝ) = -f + (a + m) + a := by exact_mod_cast hr.symm
    have : (0 : ℝ) ≤ q := by positivity
    have : (0 : ℝ) ≤ r := by positivity
    have : (0 : ℝ) ≤ p := by positivity
    have hp' : (p : ℝ) = f + (a + m) - a := by exact_mod_cast hp.symm
    have h1 : 0 < 2 * ((a : ℝ) + m) + 1 := by nlinarith
    have h2 : 0 < 2 * (a : ℝ) + 1 := by nlinarith
    positivity
  field_simp
  linear_combination (2 * ((a : ℝ) + (m + 1) / 2)) * hs

/-- `Φ_f(1)` at the `c = 0` endpoint, via DLMF 34.5.7, when `2a ≥ 1` and `2(a+m) ≥ 1`. -/
theorem Phi6_one_value (a f m : ℚ) (h : IsTri f (a + m) a) (h1 : 1 ≤ 2 * a) (h2 : 1 ≤ 2 * (a + m)) :
    Phi6 a a 1 f m m =
      2 * ((a : ℝ) + (m + 1) / 2) *
        (2 * (((a : ℝ) + m) * ((a : ℝ) + m + 1) + a * (a + 1) - f * (f + 1))) /
        Real.sqrt ((2 * ((a : ℝ) + m)) * (2 * ((a : ℝ) + m) + 1) * (2 * ((a : ℝ) + m) + 2) *
          ((2 * (a : ℝ)) * (2 * a + 1) * (2 * a + 2))) := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩⟩ := h
  have hN : ((p + q + r : ℕ) : ℚ) = f + (a + m) + a := by push_cast; linarith
  have hA : (0 : ℝ) < (a : ℝ) + (m + 1) / 2 := by
    have h1' : (1 : ℝ) ≤ 2 * a := by exact_mod_cast h1
    have h2' : (1 : ℝ) ≤ 2 * (a + m) := by exact_mod_cast h2
    linarith
  unfold Phi6
  rw [W6_eq_rank_form, sixJ_one_left ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩⟩ (p + q + r) hN h2 h1]
  have e : a + a + 1 + f + m = ((p + q + r + 1 : ℕ) : ℚ) := by
    push_cast at hN ⊢; linarith
  rw [e, sgn_natCast]
  have hs : ((-1 : ℝ) ^ (p + q + r + 1)) * (-1) ^ (p + q + r + 1) = 1 := by
    rw [← mul_pow]; norm_num
  generalize ((-1 : ℝ) ^ (p + q + r + 1)) = u at hs ⊢
  unfold wA wB
  push_cast
  have : Real.sqrt (((a : ℝ) + (m + 1) / 2) * ((a : ℝ) + (m + 1) / 2)) = (a : ℝ) + (m + 1) / 2 :=
    Real.sqrt_mul_self hA.le
  rw [this]
  have h1' : (1 : ℝ) ≤ 2 * a := by exact_mod_cast h1
  have h2' : (1 : ℝ) ≤ 2 * (a + m) := by exact_mod_cast h2
  have hP : 0 < Real.sqrt ((2 * ((a : ℝ) + m)) * (2 * ((a : ℝ) + m) + 1) * (2 * ((a : ℝ) + m) + 2) *
          ((2 * (a : ℝ)) * (2 * a + 1) * (2 * a + 2))) := by
    apply Real.sqrt_pos.mpr
    have : 0 < 2 * ((a : ℝ) + m) := by linarith
    have : 0 < 2 * (a : ℝ) := by linarith
    positivity
  generalize Real.sqrt (2 * ((a : ℝ) + m) * (2 * ((a : ℝ) + m) + 1) * (2 * ((a : ℝ) + m) + 2) *
    (2 * (a : ℝ) * (2 * (a : ℝ) + 1) * (2 * (a : ℝ) + 2))) = Z
  linear_combination (2 * ((a : ℝ) + (m + 1) / 2) *
    (2 * (((a : ℝ) + m) * ((a : ℝ) + m + 1) + a * (a + 1) - f * (f + 1))) / Z) * hs

/-- **`eq:Racahdiagzero`** (the `c = 0` endpoint row).  If `c = 0` is physical (`IsTri 0 a b`,
`IsTri 0 (b+m) (a+n)`, so that `a = b` and `m = n`), then
`f(f+1) Φ_f(0) = -a_0^+ Φ_f(1) + b_0 Φ_f(0)` with `b_0 = -κ_R/2`; the term `a_0^-` is absent.
Here `f` is a rank for which `(f, b+m, b)` is a triangle.  Proof: DLMF 34.5.1 and 34.5.7. -/
theorem Phi6_lattice_row_zero (a b f m n : ℚ) (h1 : IsTri 0 a b) (h2 : IsTri 0 (b + m) (a + n))
    (h3 : IsTri f (b + m) b) :
    (f : ℝ) * (f + 1) * Phi6 a b 0 f m n =
      -(aPlus a b m n 0 * Phi6 a b 1 f m n) +
        bDiagZero (wA a n) (wB b m) m n * Phi6 a b 0 f m n := by
  have hab : a = b := tri_zero_eq h1
  subst hab
  have hmn : m = n := by have := tri_zero_eq h2; linarith
  subst hmn
  have e1 : IsNat (2 * a) := by
    have := h1.2.2; rwa [show -0 + a + a = 2 * a by ring] at this
  have e2 : IsNat (2 * (a + m)) := by
    have := h2.2.2; rwa [show -0 + (a + m) + (a + m) = 2 * (a + m) by ring] at this
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩⟩ := h3
  by_cases hnd : 1 ≤ 2 * a ∧ 1 ≤ 2 * (a + m)
  · have h3 : IsTri f (a + m) a := ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩⟩
    have h1' : (1 : ℝ) ≤ 2 * a := by exact_mod_cast hnd.1
    have h2' : (1 : ℝ) ≤ 2 * (a + m) := by exact_mod_cast hnd.2
    have hA : (0 : ℝ) < (a : ℝ) + (m + 1) / 2 := by linarith
    rw [Phi6_zero_value a f m h3, Phi6_one_value a f m h3 hnd.1 hnd.2]
    have hed : edgeA2 a a m m ((0 : ℝ) + 1) = 16 * a * (a + 1) * (((a : ℝ) + m) * ((a : ℝ) + m + 1)) := by
      unfold edgeA2; ring
    have hed0 : 0 < edgeA2 a a m m ((0 : ℝ) + 1) := by
      rw [hed]
      have : 0 < (a : ℝ) := by linarith
      have : 0 < (a : ℝ) + m := by linarith
      positivity
    have hPpos : 0 < (2 * ((a : ℝ) + m) + 1) * (2 * (a : ℝ) + 1) := by
      have : 0 < (a : ℝ) := by linarith
      have : 0 < (a : ℝ) + m := by linarith
      positivity
    have hsq : Real.sqrt ((2 * ((a : ℝ) + m)) * (2 * ((a : ℝ) + m) + 1) * (2 * ((a : ℝ) + m) + 2) *
          ((2 * (a : ℝ)) * (2 * a + 1) * (2 * a + 2))) =
        edgeA a a m m ((0 : ℝ) + 1) * Real.sqrt ((2 * ((a : ℝ) + m) + 1) * (2 * (a : ℝ) + 1)) := by
      unfold edgeA
      rw [← Real.sqrt_mul hed0.le]
      congr 1
      rw [hed]; ring
    have hepos : 0 < edgeA a a m m ((0 : ℝ) + 1) := Real.sqrt_pos.mpr hed0
    have hspos := Real.sqrt_pos.mpr hPpos
    rw [hsq]
    unfold aPlus bDiagZero kapR wA wB
    field_simp
    ring
  · -- degenerate endpoint: `a_0^+ = 0` and the row reduces to `f(f+1) = b_0`
    have hed : edgeA2 a a m m ((0 : ℝ) + 1) = 16 * a * (a + 1) * (((a : ℝ) + m) * ((a : ℝ) + m + 1)) := by
      unfold edgeA2; ring
    have hp' : (0 : ℚ) ≤ p := by positivity
    have hq' : (0 : ℚ) ≤ q := by positivity
    have hr' : (0 : ℚ) ≤ r := by positivity
    have hz : aPlus a a m m 0 = 0 := by
      unfold aPlus edgeA
      rw [hed]
      have : (a : ℝ) = 0 ∨ (a : ℝ) + m = 0 := by
        rcases not_and_or.mp hnd with h | h
        · left
          have : 2 * a = 0 := isNat_lt_one e1 (by linarith)
          have : a = 0 := by linarith
          simp [this]
        · right
          have : 2 * (a + m) = 0 := isNat_lt_one e2 (by linarith)
          have : a + m = 0 := by linarith
          exact_mod_cast this
      rcases this with h | h <;> simp [h]
    have hlam : (f : ℝ) * (f + 1) = bDiagZero (wA a m) (wB a m) m m := by
      rcases not_and_or.mp hnd with h | h
      · have ha : a = 0 := by
          have : 2 * a = 0 := isNat_lt_one e1 (by linarith)
          linarith
        have hfm : f = m := by linarith
        subst ha
        subst hfm
        unfold bDiagZero kapR wA wB
        push_cast
        ring
      · have ham : a + m = 0 := by
          have : 2 * (a + m) = 0 := isNat_lt_one e2 (by linarith)
          linarith
        have hfa : f = a := by linarith
        have hm : m = -a := by linarith
        subst hm
        subst hfa
        unfold bDiagZero kapR wA wB
        push_cast
        ring
    rw [hz, hlam]
    ring

/-- info: 'FormalResearch.Racah.SixJ.Phi6_lattice_row_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi6_lattice_row_zero

/-- info: 'FormalResearch.Racah.SixJ.Phi6_zero_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi6_zero_value

end FormalResearch.Racah.SixJ
