module

public import FormalResearch.Special.DiscreteAiryKappaLeftBand

/-!
# A priori bound on the whole left part of the Hahn chain, including the hard edge (plan K1, step M-c, part 3)

`kl_band` (`DiscreteAiryKappaLeftBand`) controls the pair `Y_{k₀}² + Y_{k₀-1}²` by the pair at `k₁` for `K₀ ≤ k₀ ≤ k₁`.  Here the
finitely many sites between the left edge `kmin = max(|M|, |σ|)` and `K₀` are added by the backward recursion
(`a_j ≥ e/(2K₀)` for `kmin < j ≤ K₀`, since `r_j² ≥ (1-M²/j²)(1-σ²/j²) ≥ 1/j²`).

* `ke_back`: one backward step, `Y_j² + Y_{j-1}² ≤ (1 + (c_j² + a_{j+1}²)/a_j²)(Y_{j+1}² + Y_j²)`;
* `ke_down`: iteration of `ke_back` over a window of rows with a uniform constant;
* `kl_hahn_left`: **for every `Y` solving the closed-form Hahn rows `kmin < k < k₁`, vanishing below `kmin`, with
  `K₀ ≤ k₁` and `((k₁+1)h)² ≤ 1 - e²` (`x < e ≤ 1`): `Y_k² ≤ C_left (Y_{k₁}² + Y_{k₁-1}²)` for every `k ≤ k₁`.**
  `C_left = (1 + D)^{K₀} C_band` with `D = 4K₀²((x+|Mσ|)²+1)/e²` depends on `(M, σ, x, e)` only.

**Claim class: proved**, explicit constants.  No oscillatory input; valid on the entire left part including the hard edge.

**Not formalised.**  The sharp (`1 + o(1)`) amplitude on the left; half-integer `3j` chains (the Racah left bounds are `rl_left`, `rl_leftH` in `RacahKappa*`).
-/

@[expose] public section

open Finset FormalResearch.Racah.P3 FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- One backward step of the three-term recurrence. -/
lemma ke_back {a b c y0 y1 y2 : ℝ} (ha : 0 < a) (h : a * y0 = c * y1 - b * y2) :
    y1 ^ 2 + y0 ^ 2 ≤ (1 + (c ^ 2 + b ^ 2) / a ^ 2) * (y2 ^ 2 + y1 ^ 2) := by
  have h1 : (a * y0) ^ 2 ≤ (c ^ 2 + b ^ 2) * (y1 ^ 2 + y2 ^ 2) := by
    rw [h]
    nlinarith [sq_nonneg (c * y2 + b * y1)]
  have ha2 : 0 < a ^ 2 := by positivity
  have h2 : y0 ^ 2 ≤ (c ^ 2 + b ^ 2) / a ^ 2 * (y1 ^ 2 + y2 ^ 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ ha2]
    nlinarith [h1]
  nlinarith [h2]

/-- Iterating `ke_back`: `S_k ≤ (1+D)^{K₀ - k} S_{K₀}` for `kmin < k ≤ K₀`, `S_k = Y_k² + Y_{k-1}²`. -/
lemma ke_down {a c Y : ℤ → ℝ} {D : ℝ} {kmin K0 : ℤ} (hD : 0 ≤ D)
    (hrow : ∀ j ∈ Finset.Icc (kmin + 1) (K0 - 1),
      jac a c Y j = 0 ∧ 0 < a j ∧ c j ^ 2 + a (j + 1) ^ 2 ≤ D * a j ^ 2) :
    ∀ n : ℕ, kmin + 1 ≤ K0 - (n : ℤ) →
      Y (K0 - (n : ℤ)) ^ 2 + Y (K0 - (n : ℤ) - 1) ^ 2 ≤ (1 + D) ^ n * (Y K0 ^ 2 + Y (K0 - 1) ^ 2) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have hn' : kmin + 1 ≤ K0 - (n : ℤ) := by push_cast at hn; omega
    have ih' := ih hn'
    set j : ℤ := K0 - ((n + 1 : ℕ) : ℤ) with hj
    have hmem : j ∈ Finset.Icc (kmin + 1) (K0 - 1) := by
      rw [Finset.mem_Icc]; omega
    obtain ⟨hr, hapos, hcD⟩ := hrow j hmem
    unfold jac at hr
    have hstep := ke_back (a := a j) (b := a (j + 1)) (c := c j) (y0 := Y (j - 1)) (y1 := Y j) (y2 := Y (j + 1))
      hapos (by linarith)
    have hq : (c j ^ 2 + a (j + 1) ^ 2) / a j ^ 2 ≤ D := by
      rw [div_le_iff₀ (by positivity)]; exact hcD
    have e1 : K0 - (n : ℤ) = j + 1 := by rw [hj]; push_cast; ring
    have e2 : K0 - (n : ℤ) - 1 = j := by rw [hj]; push_cast; ring
    rw [e2, e1] at ih'
    have e3 : K0 - ((n + 1 : ℕ) : ℤ) - 1 = j - 1 := by rw [hj]
    rw [e3]
    have hS : 0 ≤ Y (j + 1) ^ 2 + Y j ^ 2 := by positivity
    calc Y (K0 - ((n + 1 : ℕ) : ℤ)) ^ 2 + Y (j - 1) ^ 2 = Y j ^ 2 + Y (j - 1) ^ 2 := by rw [← hj]
      _ ≤ (1 + (c j ^ 2 + a (j + 1) ^ 2) / a j ^ 2) * (Y (j + 1) ^ 2 + Y j ^ 2) := hstep
      _ ≤ (1 + D) * (Y (j + 1) ^ 2 + Y j ^ 2) := mul_le_mul_of_nonneg_right (by linarith) hS
      _ ≤ (1 + D) * ((1 + D) ^ n * (Y K0 ^ 2 + Y (K0 - 1) ^ 2)) :=
          mul_le_mul_of_nonneg_left ih' (by linarith)
      _ = (1 + D) ^ (n + 1) * (Y K0 ^ 2 + Y (K0 - 1) ^ 2) := by ring

/-- `rr M σ j ≥ 1/j` for `|M|, |σ| ≤ j - 1`, `j ≥ 1`. -/
lemma ke_rr_lower {M σ j : ℝ} (hj1 : 1 ≤ j) (hM : |M| + 1 ≤ j) (hσ : |σ| + 1 ≤ j) : 1 / j ≤ rr M σ j := by
  unfold rr
  have hj0 : 0 < j := by linarith
  have hf : ∀ {m : ℝ}, |m| + 1 ≤ j → 1 / j ≤ 1 - m ^ 2 / j ^ 2 := by
    intro m hm
    have h1 : m ^ 2 ≤ (j - 1) ^ 2 := by
      have : |m| ≤ j - 1 := by linarith
      nlinarith [sq_abs m, abs_nonneg m]
    rw [show 1 - m ^ 2 / j ^ 2 = (j ^ 2 - m ^ 2) / j ^ 2 by field_simp, div_le_div_iff₀ hj0 (by positivity)]
    nlinarith
  have h1 := hf hM
  have h2 := hf hσ
  have hd : 0 < 1 - 1 / (4 * j ^ 2) := by
    have : 1 / (4 * j ^ 2) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hd1 : 1 - 1 / (4 * j ^ 2) ≤ 1 := by
    have : 0 < 1 / (4 * j ^ 2) := by positivity
    linarith
  apply Real.le_sqrt_of_sq_le
  have hp : (1 / j) ^ 2 ≤ (1 - M ^ 2 / j ^ 2) * (1 - σ ^ 2 / j ^ 2) := by
    rw [sq]; exact mul_le_mul h1 h2 (by positivity) (by linarith [show 0 < 1 / j by positivity])
  rw [le_div_iff₀ hd]
  have : 0 ≤ (1 / j) ^ 2 := by positivity
  nlinarith

/-- `rr M σ j ^ 2 ≤ 4/3` for `|M|, |σ| ≤ j`, `j ≥ 1`. -/
lemma ke_rr_sq_le {M σ j : ℝ} (hj1 : 1 ≤ j) (hM : |M| ≤ j) (hσ : |σ| ≤ j) : rr M σ j ^ 2 ≤ 4 / 3 := by
  unfold rr
  have hj0 : 0 < j := by linarith
  have hd : 3 / 4 ≤ 1 - 1 / (4 * j ^ 2) := by
    have : 1 / (4 * j ^ 2) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hf : ∀ {m : ℝ}, |m| ≤ j → 0 ≤ 1 - m ^ 2 / j ^ 2 ∧ 1 - m ^ 2 / j ^ 2 ≤ 1 := by
    intro m hm
    have h1 : m ^ 2 ≤ j ^ 2 := by nlinarith [sq_abs m, abs_nonneg m]
    constructor
    · have : m ^ 2 / j ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; exact h1
      linarith
    · have : 0 ≤ m ^ 2 / j ^ 2 := by positivity
      linarith
  obtain ⟨a1, a2⟩ := hf hM
  obtain ⟨b1, b2⟩ := hf hσ
  rw [Real.sq_sqrt (by positivity)]
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_le_mul a2 b2 b1 (by norm_num : (0 : ℝ) ≤ 1)]

lemma ke_a_pos_facts {M σ e h : ℝ} {j : ℝ} (he : 0 < e) (hj1 : 1 ≤ j) (hM : |M| + 1 ≤ j)
    (hσ : |σ| + 1 ≤ j) (hE : e ≤ Real.sqrt (1 - (j * h) ^ 2)) :
    e / (2 * j) ≤ 1 / 2 * rr M σ j * Real.sqrt (1 - (j * h) ^ 2) := by
  have hj0 : 0 < j := by linarith
  have h1 := ke_rr_lower hj1 hM hσ
  have h2 : 1 / j * e ≤ rr M σ j * Real.sqrt (1 - (j * h) ^ 2) :=
    mul_le_mul h1 hE he.le (by unfold rr; exact Real.sqrt_nonneg _)
  have : e / (2 * j) = 1 / 2 * (1 / j * e) := by field_simp
  rw [this]
  nlinarith

lemma ke_a_sq_le {M σ h : ℝ} {j : ℝ} (hj1 : 1 ≤ j) (hM : |M| ≤ j) (hσ : |σ| ≤ j) :
    (1 / 2 * rr M σ j * Real.sqrt (1 - (j * h) ^ 2)) ^ 2 ≤ 1 / 3 := by
  have h1 := ke_rr_sq_le hj1 hM hσ
  have hE : Real.sqrt (1 - (j * h) ^ 2) ^ 2 ≤ 1 := by
    rcases le_or_gt 0 (1 - (j * h) ^ 2) with h0 | h0
    · rw [Real.sq_sqrt h0]; nlinarith [sq_nonneg (j * h)]
    · rw [Real.sqrt_eq_zero_of_nonpos h0.le]; norm_num
  have : (1 / 2 * rr M σ j * Real.sqrt (1 - (j * h) ^ 2)) ^ 2 =
      1 / 4 * (rr M σ j ^ 2 * Real.sqrt (1 - (j * h) ^ 2) ^ 2) := by ring
  rw [this]
  have h3 : rr M σ j ^ 2 * Real.sqrt (1 - (j * h) ^ 2) ^ 2 ≤ 4 / 3 * 1 :=
    mul_le_mul h1 hE (by positivity) (by norm_num)
  linarith

/-- The backward constant `D = 4K₀²((x+|Mσ|)²+1)/e²`. -/
noncomputable def ke_D (M σ x e : ℝ) (K0 : ℕ) : ℝ := 4 * (K0 : ℝ) ^ 2 * ((x + |M * σ|) ^ 2 + 1) / e ^ 2

/-- The left constant `C_left = (1+D)^{K₀} C_band`. -/
noncomputable def ke_C (M σ x e : ℝ) (K0 : ℕ) : ℝ := (1 + ke_D M σ x e K0) ^ K0 * kl_Cband M σ x e

lemma ke_D_nonneg (M σ x e : ℝ) (K0 : ℕ) : 0 ≤ ke_D M σ x e K0 := by unfold ke_D; positivity

lemma ke_C_ge_one {M σ x e : ℝ} (K0 : ℕ) (hx : 0 < x) (hxe : x < e) (he1 : e ≤ 1) : 1 ≤ ke_C M σ x e K0 := by
  unfold ke_C
  have h1 : 1 ≤ (1 + ke_D M σ x e K0) ^ K0 := one_le_pow₀ (by linarith [ke_D_nonneg M σ x e K0])
  have h2 := kl_Cband_ge_one (M := M) (σ := σ) hxe he1 hx
  nlinarith

/-- **Row facts at the left edge**: for `kmin < j ≤ K₀`, `j ≤ k₁` (band at `k₁ + 1`): `a_j > 0` and
`c_j² + a_{j+1}² ≤ D a_j²`. -/
lemma ke_row_facts {M σ : ℤ} {x e h : ℝ} {K0 : ℕ} (hx : 0 < x) (hxe : x < e) (hh : 0 < h) {j k1 : ℤ}
    (hj : max |M| |σ| + 1 ≤ j) (hjK : j ≤ (K0 : ℤ)) (hjk : j ≤ k1)
    (hband : (((k1 : ℝ) + 1) * h) ^ 2 ≤ 1 - e ^ 2) :
    0 < kl_a (M : ℝ) (σ : ℝ) h j ∧
      kl_c x (M : ℝ) (σ : ℝ) j ^ 2 + kl_a (M : ℝ) (σ : ℝ) h (j + 1) ^ 2 ≤
        ke_D (M : ℝ) (σ : ℝ) x e K0 * kl_a (M : ℝ) (σ : ℝ) h j ^ 2 := by
  have he : 0 < e := by linarith
  have hkmin0 : 0 ≤ max |M| |σ| := le_trans (abs_nonneg M) (le_max_left _ _)
  have hjr1 : (1 : ℝ) ≤ j := by exact_mod_cast (by omega : (1 : ℤ) ≤ j)
  have hjM : |(M : ℝ)| + 1 ≤ (j : ℝ) := by
    have : |M| + 1 ≤ j := by have := le_max_left |M| |σ|; omega
    have h2 : ((|M| + 1 : ℤ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast this
    push_cast at h2; exact h2
  have hjσ : |(σ : ℝ)| + 1 ≤ (j : ℝ) := by
    have : |σ| + 1 ≤ j := by have := le_max_right |M| |σ|; omega
    have h2 : ((|σ| + 1 : ℤ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast this
    push_cast at h2; exact h2
  have hjK' : (j : ℝ) ≤ (K0 : ℝ) := by exact_mod_cast hjK
  have hj0 : (0 : ℝ) < j := by linarith
  have hjk' : (j : ℝ) ≤ k1 := by exact_mod_cast hjk
  have hbj : ((j : ℝ) * h) ^ 2 ≤ 1 - e ^ 2 := by
    refine le_trans ?_ hband
    apply pow_le_pow_left₀ (by positivity); nlinarith
  obtain ⟨hEe, -⟩ := kl_E_bounds (e := e) hbj
  have hlow := ke_a_pos_facts (M := (M : ℝ)) (σ := (σ : ℝ)) (h := h) he hjr1 hjM hjσ hEe
  have hapos : 0 < e / (2 * (j : ℝ)) := by positivity
  unfold kl_a kl_c
  constructor
  · exact lt_of_lt_of_le hapos hlow
  have cast1 : (((j + 1 : ℤ)) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
  rw [cast1]
  have hup := ke_a_sq_le (M := (M : ℝ)) (σ := (σ : ℝ)) (h := h) (j := (j : ℝ) + 1) (by linarith)
    (by linarith) (by linarith)
  have hcabs := kl_cabs (M := (M : ℝ)) (σ := (σ : ℝ)) (x := x) hx hj0
  have hc1 : |x - (M : ℝ) * σ / ((j : ℝ) * ((j : ℝ) + 1))| ≤ x + |(M : ℝ) * σ| := by
    refine hcabs.trans ?_
    have : |(M : ℝ) * σ| / (j : ℝ) ^ 2 ≤ |(M : ℝ) * σ| := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : (1 : ℝ) ≤ (j : ℝ) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h1 (abs_nonneg ((M : ℝ) * σ))]
    linarith
  have hc2 : (x - (M : ℝ) * σ / ((j : ℝ) * ((j : ℝ) + 1))) ^ 2 ≤ (x + |(M : ℝ) * σ|) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hc1 2
  have hasq : e ^ 2 / (4 * (K0 : ℝ) ^ 2) ≤ (1 / 2 * rr (M : ℝ) (σ : ℝ) (j : ℝ) *
      Real.sqrt (1 - ((j : ℝ) * h) ^ 2)) ^ 2 := by
    have h1 : (e / (2 * (j : ℝ))) ^ 2 ≤ (1 / 2 * rr (M : ℝ) (σ : ℝ) (j : ℝ) * Real.sqrt (1 - ((j : ℝ) * h) ^ 2)) ^ 2 :=
      pow_le_pow_left₀ hapos.le hlow 2
    have hK0p : (0 : ℝ) < K0 := lt_of_lt_of_le hj0 hjK'
    refine le_trans ?_ h1
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (j : ℝ) ^ 2 ≤ (K0 : ℝ) ^ 2 := pow_le_pow_left₀ hj0.le hjK' 2
    nlinarith [sq_nonneg e]
  unfold ke_D
  have hK0p : (0 : ℝ) < K0 := lt_of_lt_of_le hj0 hjK'
  have hP : 0 < ((x + |(M : ℝ) * σ|) ^ 2 + 1) := by positivity
  calc _ ≤ (x + |(M : ℝ) * σ|) ^ 2 + 1 / 3 := add_le_add hc2 hup
    _ ≤ (x + |(M : ℝ) * σ|) ^ 2 + 1 := by linarith
    _ = 4 * (K0 : ℝ) ^ 2 * ((x + |(M : ℝ) * σ|) ^ 2 + 1) / e ^ 2 * (e ^ 2 / (4 * (K0 : ℝ) ^ 2)) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hasq (by positivity)

/-- **The a priori bound on the whole left part** (see the module docstring). -/
theorem kl_hahn_left {M σ : ℤ} {x e h : ℝ} (hx : 0 < x) (hxe : x < e) (he1 : e ≤ 1) (hh : 0 < h) {Y : ℤ → ℝ}
    {K0 : ℕ} (hK0 : kl_K0real (M : ℝ) (σ : ℝ) x e ≤ (K0 : ℝ)) {k1 : ℤ} (hk1 : (K0 : ℤ) ≤ k1)
    (hband : (((k1 : ℝ) + 1) * h) ^ 2 ≤ 1 - e ^ 2)
    (hrow : ∀ k ∈ Finset.Icc (max |M| |σ| + 1) (k1 - 1),
      jac (kl_a (M : ℝ) (σ : ℝ) h) (kl_c x (M : ℝ) (σ : ℝ)) Y k = 0)
    (hsupp : ∀ k : ℤ, k < max |M| |σ| → Y k = 0) :
    ∀ k : ℤ, k ≤ k1 → Y k ^ 2 ≤ ke_C (M : ℝ) (σ : ℝ) x e K0 * (Y k1 ^ 2 + Y (k1 - 1) ^ 2) := by
  set kmin : ℤ := max |M| |σ| with hkmin
  have hkmin0 : 0 ≤ kmin := le_trans (abs_nonneg M) (le_max_left _ _)
  have hK0kmin : kmin + 1 ≤ (K0 : ℤ) := by
    have h1 : ((max |M| |σ| : ℤ) : ℝ) + 1 ≤ (K0 : ℝ) := by
      have : max |(M : ℝ)| |(σ : ℝ)| + 1 ≤ kl_K0real (M : ℝ) (σ : ℝ) x e :=
        (le_max_right _ _).trans (le_max_left _ _)
      push_cast
      linarith
    have : (kmin + 1 : ℤ) ≤ K0 := by exact_mod_cast h1
    exact this
  have hCge := ke_C_ge_one (M := (M : ℝ)) (σ := (σ : ℝ)) K0 hx hxe he1
  have hD := ke_D_nonneg (M : ℝ) (σ : ℝ) x e K0
  have hrowD : ∀ j ∈ Finset.Icc (kmin + 1) ((K0 : ℤ) - 1),
      jac (kl_a (M : ℝ) (σ : ℝ) h) (kl_c x (M : ℝ) (σ : ℝ)) Y j = 0 ∧ 0 < kl_a (M : ℝ) (σ : ℝ) h j ∧
        kl_c x (M : ℝ) (σ : ℝ) j ^ 2 + kl_a (M : ℝ) (σ : ℝ) h (j + 1) ^ 2 ≤
          ke_D (M : ℝ) (σ : ℝ) x e K0 * kl_a (M : ℝ) (σ : ℝ) h j ^ 2 := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    obtain ⟨f1, f2⟩ := ke_row_facts (M := M) (σ := σ) (x := x) (e := e) (h := h) (K0 := K0) hx hxe hh
      (j := j) (k1 := k1) hj.1 (by omega) (by omega) hband
    exact ⟨hrow j (by rw [Finset.mem_Icc]; omega), f1, f2⟩
  have hdown := ke_down hD hrowD
  have hS0 : 0 ≤ Y k1 ^ 2 + Y (k1 - 1) ^ 2 := by positivity
  -- the pair bound at every site `kmin + 1 ≤ k' ≤ k₁`
  have hpair : ∀ k' : ℤ, kmin + 1 ≤ k' → k' ≤ k1 →
      Y k' ^ 2 + Y (k' - 1) ^ 2 ≤ ke_C (M : ℝ) (σ : ℝ) x e K0 * (Y k1 ^ 2 + Y (k1 - 1) ^ 2) := by
    intro k' h1 h2
    have hbandK := kl_band (M := (M : ℝ)) (σ := (σ : ℝ)) hx hxe he1 hh hK0 (k0 := (K0 : ℤ)) (k1 := k1) le_rfl hk1
      hband (fun k hk => hrow k (by rw [Finset.mem_Icc] at hk ⊢; omega))
    by_cases hc : (K0 : ℤ) ≤ k'
    · have := kl_band (M := (M : ℝ)) (σ := (σ : ℝ)) hx hxe he1 hh hK0 (k0 := k') (k1 := k1) hc h2
        hband (fun k hk => hrow k (by rw [Finset.mem_Icc] at hk ⊢; omega))
      refine this.trans ?_
      unfold ke_C
      have h3 : 1 ≤ (1 + ke_D (M : ℝ) (σ : ℝ) x e K0) ^ K0 := one_le_pow₀ (by linarith)
      have h4 : 0 ≤ kl_Cband (M : ℝ) (σ : ℝ) x e := by linarith [kl_Cband_ge_one (M := (M : ℝ)) (σ := (σ : ℝ)) hxe he1 hx]
      nlinarith [mul_nonneg h4 hS0]
    · push Not at hc
      obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = (K0 : ℤ) - k' := ⟨((K0 : ℤ) - k').toNat, Int.toNat_of_nonneg (by omega)⟩
      have hk' : (K0 : ℤ) - (n : ℤ) = k' := by omega
      have hd := hdown n (by omega)
      rw [hk'] at hd
      have hnK : n ≤ K0 := by omega
      have h5 : (1 + ke_D (M : ℝ) (σ : ℝ) x e K0) ^ n ≤ (1 + ke_D (M : ℝ) (σ : ℝ) x e K0) ^ K0 :=
        pow_le_pow_right₀ (by linarith) hnK
      calc _ ≤ _ := hd
        _ ≤ (1 + ke_D (M : ℝ) (σ : ℝ) x e K0) ^ K0 * (Y (K0 : ℤ) ^ 2 + Y ((K0 : ℤ) - 1) ^ 2) :=
            mul_le_mul_of_nonneg_right h5 (by positivity)
        _ ≤ (1 + ke_D (M : ℝ) (σ : ℝ) x e K0) ^ K0 * (kl_Cband (M : ℝ) (σ : ℝ) x e * (Y k1 ^ 2 + Y (k1 - 1) ^ 2)) :=
            mul_le_mul_of_nonneg_left hbandK (by positivity)
        _ = _ := by unfold ke_C; ring
  intro k hk
  by_cases hlt : k < kmin
  · rw [hsupp k hlt]
    have : 0 ≤ ke_C (M : ℝ) (σ : ℝ) x e K0 * (Y k1 ^ 2 + Y (k1 - 1) ^ 2) := by positivity
    simpa using this
  · push Not at hlt
    by_cases hk1' : k = k1
    · subst hk1'
      have := hpair k (by omega) le_rfl
      nlinarith [sq_nonneg (Y (k - 1))]
    · have := hpair (k + 1) (by omega) (by omega)
      simp only [add_sub_cancel_right] at this
      nlinarith [sq_nonneg (Y (k + 1))]

/-- info: 'FormalResearch.Special.kl_hahn_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kl_hahn_left

end FormalResearch.Special
