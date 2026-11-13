module

public import FormalResearch.Racah.P2AnalyticCarrier6jInduction

/-!
# The `6j` carrier identity in every chamber (Weyl P2, `lem:sqrtfreecarrier`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `lem:sqrtfreecarrier` ("in any chamber ... the
other chambers follow by the reductions preceding Lemma `lem:6jseed`") and the reduction text before
`eq:canonicalsector`.

`P2AnalyticCarrier6jInduction.lean` proves the carrier identity in the canonical sector `m ≥ |n|`.  Here the
four chambers `|n| ≤ m`, `|n| ≤ -m`, `|m| ≤ n`, `|m| ≤ -n` (which cover every `(m,n)`) are reduced to
it by the exact symmetries `Phi6_swap_ab` (`(a,b;m,n;A,B) ↦ (b,a;n,m;B,A)`) and `Phi6_exch_ab`
(`(a,b;m,n) ↦ (a+n,b+m;-m,-n)`, `A, B` fixed):

| chamber | canonical data | sign |
|---|---|---|
| I `|n| ≤ m` | `(m, n; A, B)` | `+1` |
| II `|n| ≤ -m` | `(-m, -n; A, B)` | `(-1)^{m-n}` |
| III `|m| ≤ n` | `(n, m; B, A)` | `(-1)^{m-n}` |
| IV `|m| ≤ -n` | `(-n, -m; B, A)` | `+1` |

`carrierV m n A B C f d = E W Π_f^{-1/2} P̃_f(τ; A⁻², B⁻², (AB)⁻¹)` is the carrier as a function of the
intrinsic centered variables `(A,B,C)`; `carrierAll` is the chamber-reduced carrier and
`Phi6_carrier_all` is the identity at every physical point.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner FormalResearch.Racah.SixJ

/-- The carrier as a function of the centered variables `A, B, C` and the rank `f = m + d`:
`E_{A,B}(C) W_{6j}(x) Π_f(A,B)^{-1/2} P̃_f(τ; A⁻², B⁻², (AB)⁻¹)`, `τ = (1 - cosA A B C)/2`. -/
noncomputable def carrierV (m n : ℚ) (A B C : ℝ) (f : ℚ) (d : ℕ) : ℝ :=
  edgeFac m n A B C * (Real.sqrt (piSix f A B))⁻¹ *
    ptilde6 m n ((1 - cosA A B C) / 2) (1 / A ^ 2) (1 / B ^ 2) (1 / (A * B)) d

lemma carrier6_eq_carrierV (a b c m n f : ℚ) (d : ℕ) :
    carrier6 a b c m n f d = carrierV m n (wA a n) (wB b m) (wC c) f d := rfl

lemma isTri_swap23 {f y z : ℚ} (h : IsTri f y z) : IsTri f z y := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩⟩ := h
  exact ⟨⟨q, by linarith⟩, ⟨p, by linarith⟩, ⟨r, by linarith⟩⟩

/-- `m - n` is an integer at every physical point. -/
lemma exists_int_sub {a b f m n : ℚ} (h1 : IsTri f (b + m) b) (h2 : IsTri f a (a + n)) :
    ∃ k : ℤ, m - n = k := by
  obtain ⟨p, hp⟩ := h1.2.1
  obtain ⟨q, hq⟩ := h2.1
  exact ⟨(q : ℤ) - p, by push_cast; linarith⟩

/-- Chamber I: the canonical sector. -/
theorem Phi6_carrier_chamberI (a b c f m n : ℚ) (hmn : |n| ≤ m) (h1 : IsTri f (b + m) b)
    (h2 : IsTri f a (a + n)) (h3 : IsTri c a b) (h4 : IsTri c (b + m) (a + n)) :
    Phi6 a b c f m n = carrierV m n (wA a n) (wB b m) (wC c) f ⌊f - m⌋₊ :=
  Phi6_carrier_canonical' a b c f m n hmn h1 h2 h3 h4

/-- Chamber II (`|n| ≤ -m`): second symmetry reduction, sign `(-1)^{m-n}`. -/
theorem Phi6_carrier_chamberII (a b c f m n : ℚ) (hmn : |n| ≤ -m) (h1 : IsTri f (b + m) b)
    (h2 : IsTri f a (a + n)) (h3 : IsTri c a b) (h4 : IsTri c (b + m) (a + n)) (k : ℤ)
    (hk : m - n = k) :
    Phi6 a b c f m n = (-1 : ℝ) ^ k * carrierV (-m) (-n) (wA a n) (wB b m) (wC c) f ⌊f + m⌋₊ := by
  have e1 : IsTri f ((b + m) + -m) (b + m) := by
    rw [show b + m + -m = b by ring]; exact isTri_swap23 h1
  have e2 : IsTri f (a + n) ((a + n) + -n) := by
    rw [show a + n + -n = a by ring]; exact isTri_swap23 h2
  have e3 : IsTri c (a + n) (b + m) := isTri_swap23 h4
  have e4 : IsTri c ((b + m) + -m) ((a + n) + -n) := by
    rw [show b + m + -m = b by ring, show a + n + -n = a by ring]; exact isTri_swap23 h3
  have hc := Phi6_carrier_canonical' (a + n) (b + m) c f (-m) (-n) (by simpa using hmn) e1 e2 e3 e4
  have hx := Phi6_exch_ab a b c f m n k hk
  have hsq : ((-1 : ℝ) ^ k) * (-1 : ℝ) ^ k = 1 := by
    rw [← zpow_add₀ (by norm_num), ← two_mul, zpow_mul]; norm_num
  have : Phi6 a b c f m n = (-1 : ℝ) ^ k * Phi6 (a + n) (b + m) c f (-m) (-n) := by
    rw [hx, ← mul_assoc, hsq, one_mul]
  rw [this, hc, carrier6_eq_carrierV, wA_exch, wB_exch]
  simp only [sub_neg_eq_add]

/-- Chamber III (`|m| ≤ n`): first symmetry reduction, sign `(-1)^{m-n}`, `A ↔ B`. -/
theorem Phi6_carrier_chamberIII (a b c f m n : ℚ) (hmn : |m| ≤ n) (h1 : IsTri f (b + m) b)
    (h2 : IsTri f a (a + n)) (h3 : IsTri c a b) (h4 : IsTri c (b + m) (a + n)) (k : ℤ)
    (hk : m - n = k) :
    Phi6 a b c f m n = (-1 : ℝ) ^ k * carrierV n m (wB b m) (wA a n) (wC c) f ⌊f - n⌋₊ := by
  have hc := Phi6_carrier_canonical' b a c f n m hmn (isTri_swap23 h2) (isTri_swap23 h1)
    (isTri_swap23 h3) (isTri_swap23 h4)
  have hx := Phi6_swap_ab a b c f m n k hk
  have hsq : ((-1 : ℝ) ^ k) * (-1 : ℝ) ^ k = 1 := by
    rw [← zpow_add₀ (by norm_num), ← two_mul, zpow_mul]; norm_num
  have : Phi6 a b c f m n = (-1 : ℝ) ^ k * Phi6 b a c f n m := by
    rw [hx, ← mul_assoc, hsq, one_mul]
  rw [this, hc, carrier6_eq_carrierV]
  rfl

/-- Chamber IV (`|m| ≤ -n`): both reductions, sign `+1`, `A ↔ B`. -/
theorem Phi6_carrier_chamberIV (a b c f m n : ℚ) (hmn : |m| ≤ -n) (h1 : IsTri f (b + m) b)
    (h2 : IsTri f a (a + n)) (h3 : IsTri c a b) (h4 : IsTri c (b + m) (a + n)) :
    Phi6 a b c f m n = carrierV (-n) (-m) (wB b m) (wA a n) (wC c) f ⌊f + n⌋₊ := by
  obtain ⟨k, hk⟩ := exists_int_sub h1 h2
  -- step 1: swap to `(b, a; n, m)`, step 2: exchange to `(b+m, a+n; -n, -m)`
  have g1 : IsTri f (a + n) a := isTri_swap23 h2
  have g2 : IsTri f b (b + m) := isTri_swap23 h1
  have g3 : IsTri c b a := isTri_swap23 h3
  have g4 : IsTri c (a + n) (b + m) := isTri_swap23 h4
  have e1 : IsTri f ((a + n) + -n) (a + n) := by
    rw [show a + n + -n = a by ring]; exact isTri_swap23 g1
  have e2 : IsTri f (b + m) ((b + m) + -m) := by
    rw [show b + m + -m = b by ring]; exact isTri_swap23 g2
  have e3 : IsTri c (b + m) (a + n) := h4
  have e4 : IsTri c ((a + n) + -n) ((b + m) + -m) := by
    rw [show a + n + -n = a by ring, show b + m + -m = b by ring]; exact isTri_swap23 g3
  have hc := Phi6_carrier_canonical' (b + m) (a + n) c f (-n) (-m) (by simpa using hmn)
    e1 e2 h4 e4
  have hx1 := Phi6_swap_ab a b c f m n k hk
  have hx2 := Phi6_exch_ab b a c f n m (-k) (by push_cast; linarith)
  have hsq : ((-1 : ℝ) ^ (-k)) * (-1 : ℝ) ^ k = 1 := by
    rw [← zpow_add₀ (by norm_num), neg_add_cancel, zpow_zero]
  have : Phi6 a b c f m n = Phi6 (b + m) (a + n) c f (-n) (-m) := by
    rw [hx2, hx1, ← mul_assoc, hsq, one_mul]
  rw [this, hc, carrier6_eq_carrierV, wA_exch, wB_exch, sub_neg_eq_add]
  rfl

/-- The chamber-reduced carrier at a physical point: the four chambers of the table above. -/
noncomputable def carrierAll (a b c f m n : ℚ) : ℝ :=
  if |n| ≤ m then carrierV m n (wA a n) (wB b m) (wC c) f ⌊f - m⌋₊
  else if |n| ≤ -m then
    (-1 : ℝ) ^ ⌊m - n⌋ * carrierV (-m) (-n) (wA a n) (wB b m) (wC c) f ⌊f + m⌋₊
  else if |m| ≤ n then
    (-1 : ℝ) ^ ⌊m - n⌋ * carrierV n m (wB b m) (wA a n) (wC c) f ⌊f - n⌋₊
  else carrierV (-n) (-m) (wB b m) (wA a n) (wC c) f ⌊f + n⌋₊

/-- **`lem:sqrtfreecarrier`, `6j` version, every chamber** (`eq:sqrtfreecarrier`).  At every
physical point (the hypotheses of `Phi6_midpoint_recurrence` and `Phi6_seed`),
`Φ_f = ± E W Π^{-1/2} P̃` with the canonical data of the chamber, i.e. `Phi6 = carrierAll`. -/
theorem Phi6_carrier_all (a b c f m n : ℚ) (h1 : IsTri f (b + m) b) (h2 : IsTri f a (a + n))
    (h3 : IsTri c a b) (h4 : IsTri c (b + m) (a + n)) :
    Phi6 a b c f m n = carrierAll a b c f m n := by
  obtain ⟨k, hk⟩ := exists_int_sub h1 h2
  have hfl : ⌊m - n⌋ = k := by rw [hk]; exact Int.floor_intCast k
  by_cases c1 : |n| ≤ m
  · simp only [carrierAll, c1, ↓reduceIte]
    exact Phi6_carrier_chamberI a b c f m n c1 h1 h2 h3 h4
  by_cases c2 : |n| ≤ -m
  · simp only [carrierAll, c1, c2, ↓reduceIte, hfl]
    exact Phi6_carrier_chamberII a b c f m n c2 h1 h2 h3 h4 k hk
  by_cases c3 : |m| ≤ n
  · simp only [carrierAll, c1, c2, c3, ↓reduceIte, hfl]
    exact Phi6_carrier_chamberIII a b c f m n c3 h1 h2 h3 h4 k hk
  have c4 : |m| ≤ -n := by
    rcases le_total 0 n with hn | hn
    · rw [abs_of_nonneg hn] at c1 c2
      exfalso; apply c3; rw [abs_le]; constructor <;> push Not at c1 c2 <;> linarith
    · rw [abs_of_nonpos hn] at c1 c2
      rw [abs_le]; push Not at c1 c2; constructor <;> linarith
  simp only [carrierAll, c1, c2, c3, ↓reduceIte]
  exact Phi6_carrier_chamberIV a b c f m n c4 h1 h2 h3 h4

/-- info: 'FormalResearch.Racah.Phi6_carrier_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi6_carrier_all

end FormalResearch.Racah
