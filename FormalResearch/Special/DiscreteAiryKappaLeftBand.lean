module

public import FormalResearch.Special.DiscreteAiryKappaLeft

/-!
# The Hahn band: comparison of the invariant over `K ≤ k ≤ k₁` (plan K1, step M-c, part 2)

Combines `ki_invariant` with the coefficient facts `kl_coef_facts`: for the closed-form Hahn rows in the band
`((k₁+1)h)² ≤ 1 - e²` (`x < e ≤ 1`) and every start `k₀ ≥ K`, the invariant satisfies
`F_{k₀} ≤ e^{2E₀} F_{k₁}`, hence `Y_{k₀}² + Y_{k₀-1}² ≤ C_band (Y_{k₁}² + Y_{k₁-1}²)`, with `E₀ = W (T + D)`,
`W = 4(1+45/x²)/(e-x)`, `T = β + 2|Mσ|`, `D = 9/(4x)` (`kl_band`).

**Claim class: proved.**  Constants explicit (`kl_W`, `kl_E0`, `kl_K0real`, `kl_Cband`).
-/

@[expose] public section

open Finset FormalResearch.Racah.P3 FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- `Σ_{i<n} 1/(s+i)² ≤ 1/(s-1) - 1/(s+n-1)` for `s > 1`. -/
lemma kl_sum_inv_sq {s : ℝ} (hs : 1 < s) (n : ℕ) :
    ∑ i ∈ range n, 1 / (s + (i : ℝ)) ^ 2 ≤ 1 / (s - 1) - 1 / (s + (n : ℝ) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : 0 < s + (n : ℝ) - 1 := by linarith
    have h2 : 0 < s + (n : ℝ) := by linarith
    have h3 : 1 / (s + (n : ℝ)) ^ 2 ≤ 1 / (s + (n : ℝ) - 1) - 1 / (s + ((n + 1 : ℕ) : ℝ) - 1) := by
      have e : s + ((n + 1 : ℕ) : ℝ) - 1 = s + (n : ℝ) := by push_cast; ring
      rw [e, div_sub_div _ _ h1.ne' h2.ne']
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos h1 h2]
    linarith

lemma kl_sum_inv_sq_le_one {s : ℝ} (hs : 2 ≤ s) (n : ℕ) :
    ∑ i ∈ range n, 1 / (s + (i : ℝ)) ^ 2 ≤ 1 := by
  have h := kl_sum_inv_sq (s := s) (by linarith) n
  have h1 : 1 / (s - 1) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have h2 : 0 ≤ 1 / (s + (n : ℝ) - 1) := by
    have : 0 < s + (n : ℝ) - 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    positivity
  linarith

/-- The constants of the band comparison. -/
noncomputable def kl_W (x e : ℝ) : ℝ := 4 * (1 + 45 / x ^ 2) / (e - x)

noncomputable def kl_T (M σ : ℝ) : ℝ := kl_beta M σ + 2 * |M * σ|

/-- The accumulated variation `E₀ = W (T + D)`. -/
noncomputable def kl_E0 (M σ x e : ℝ) : ℝ := kl_W x e * (kl_T M σ + 9 / (4 * x))

/-- The rank threshold `K` (a real number; `K₀ = ⌈K⌉₊`). -/
noncomputable def kl_K0real (M σ x e : ℝ) : ℝ :=
  max (max 2 (max |M| |σ| + 1)) (max (max (2 * kl_beta M σ) (2 * (kl_beta M σ + |M * σ|) / (e - x)))
    (max (4 * kl_W x e * kl_T M σ) (4 * kl_W x e * (9 / (4 * x)))))

/-- The band constant `(3/m₀) e^{2E₀}` with `m₀ = (e-x)/2`. -/
noncomputable def kl_Cband (M σ x e : ℝ) : ℝ := 6 / (e - x) * Real.exp (2 * kl_E0 M σ x e)

lemma kl_W_pos {x e : ℝ} (hx : 0 < x) (hxe : x < e) : 0 < kl_W x e := by
  unfold kl_W
  have : 0 < e - x := by linarith
  positivity

lemma kl_T_pos (M σ : ℝ) : 0 ≤ kl_T M σ := by
  unfold kl_T kl_beta; positivity

/-- The Hahn coefficients as plain functions on `ℤ` (`= hrAk 1 0 M σ h`, `= hrCk 1 0 1 x M σ h`). -/
noncomputable def kl_a (M σ h : ℝ) (j : ℤ) : ℝ := 1 / 2 * rr M σ (j : ℝ) * Real.sqrt (1 - ((j : ℝ) * h) ^ 2)

noncomputable def kl_c (x M σ : ℝ) (j : ℤ) : ℝ := x - M * σ / ((j : ℝ) * ((j : ℝ) + 1))

lemma kl_hrAk_eq (M σ h : ℝ) : hrAk 1 0 M σ h = kl_a M σ h := funext fun j => kl_hrA M σ h j

lemma kl_hrCk_eq (x M σ h : ℝ) : hrCk 1 0 1 x M σ h = kl_c x M σ := funext fun j => kl_hrC x M σ h j

lemma kl_Cband_ge_one {M σ x e : ℝ} (hxe : x < e) (he1 : e ≤ 1) (hx : 0 < x) : 1 ≤ kl_Cband M σ x e := by
  unfold kl_Cband
  have hγ : 0 < e - x := by linarith
  have h1 : 1 ≤ Real.exp (2 * kl_E0 M σ x e) := by
    apply Real.one_le_exp
    unfold kl_E0
    have := kl_W_pos hx hxe
    have := kl_T_pos M σ
    positivity
  have h2 : 6 ≤ 6 / (e - x) := by
    rw [le_div_iff₀ hγ]; linarith
  nlinarith

/-- **Facts at one index** `j ∈ [K₀, k₁]` (band at `k₁ + 1`): all the hypotheses of `ki_invariant` for the step `j → j + 1`
(`ε_j = W(T/j² + 9h/(4x))`) and the margin/upper bounds used at the ends. -/
lemma kl_index {M σ x e h : ℝ} (hx : 0 < x) (hxe : x < e) (he1 : e ≤ 1) (hh : 0 < h) {K0 : ℕ}
    (hK0 : kl_K0real M σ x e ≤ (K0 : ℝ)) {j k1 : ℤ} (hj : (K0 : ℤ) ≤ j) (hjk : j ≤ k1)
    (hband : (((k1 : ℝ) + 1) * h) ^ 2 ≤ 1 - e ^ 2) :
    (e - x) / 2 ≤ 2 * kl_a M σ h j - |kl_c x M σ j| ∧ 0 < kl_a M σ h j ∧ kl_a M σ h j ≤ 3 / 4 ∧
    x / 4 ≤ kl_a M σ h (j + 1) ∧
    kl_c x M σ j ^ 2 + kl_a M σ h j ^ 2 ≤ 45 / x ^ 2 * kl_a M σ h (j + 1) ^ 2 ∧
    2 * (1 + 45 / x ^ 2) * (|kl_a M σ h (j + 1) - kl_a M σ h j| + |kl_c x M σ (j + 1) - kl_c x M σ j|) ≤
      (e - x) / 2 * (kl_W x e * (kl_T M σ / (j : ℝ) ^ 2 + 9 * h / (4 * x))) ∧
    0 ≤ kl_W x e * (kl_T M σ / (j : ℝ) ^ 2 + 9 * h / (4 * x)) ∧
    kl_W x e * (kl_T M σ / (j : ℝ) ^ 2 + 9 * h / (4 * x)) ≤ 1 / 2 := by
  have hγ0 : 0 < e - x := by linarith
  have hW := kl_W_pos hx hxe
  have hT := kl_T_pos M σ
  have hjK : kl_K0real M σ x e ≤ (j : ℝ) := hK0.trans (by exact_mod_cast hj)
  have hmax : ∀ {t : ℝ}, t ≤ kl_K0real M σ x e → t ≤ (j : ℝ) := fun ht => ht.trans hjK
  have j2 : (2 : ℝ) ≤ j := hmax ((le_max_left _ _).trans (le_max_left _ _))
  have jM : max |M| |σ| + 1 ≤ (j : ℝ) := hmax ((le_max_right _ _).trans (le_max_left _ _))
  have jβ : 2 * kl_beta M σ ≤ (j : ℝ) :=
    hmax ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _)))
  have jγ : 2 * (kl_beta M σ + |M * σ|) / (e - x) ≤ (j : ℝ) :=
    hmax ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _)))
  have jWT : 4 * kl_W x e * kl_T M σ ≤ (j : ℝ) :=
    hmax ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have jWD : 4 * kl_W x e * (9 / (4 * x)) ≤ (j : ℝ) :=
    hmax ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hj0 : (0 : ℝ) < j := by linarith
  have hMj : M ^ 2 ≤ (j : ℝ) ^ 2 := by
    have : |M| ≤ (j : ℝ) := by linarith [le_max_left |M| |σ|]
    nlinarith [sq_abs M, abs_nonneg M]
  have hσj : σ ^ 2 ≤ (j : ℝ) ^ 2 := by
    have : |σ| ≤ (j : ℝ) := by linarith [le_max_right |M| |σ|]
    nlinarith [sq_abs σ, abs_nonneg σ]
  have hbandj : (((j : ℝ) + 1) * h) ^ 2 ≤ 1 - e ^ 2 := by
    refine le_trans ?_ hband
    apply pow_le_pow_left₀ (by positivity)
    have : (j : ℝ) ≤ k1 := by exact_mod_cast hjk
    nlinarith
  have hjh : (j : ℝ) * h ≤ 1 := by
    have h1 : ((j : ℝ) * h) ^ 2 ≤ 1 := by
      have : ((j : ℝ) * h) ^ 2 ≤ (((j : ℝ) + 1) * h) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity); nlinarith
      nlinarith [sq_nonneg e]
    nlinarith [mul_pos hj0 hh]
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := kl_coef_facts (M := M) (σ := σ) (x := x) (e := e) (h := h) (k := (j : ℝ))
    hx hxe he1 hh (by linarith) jβ jγ hMj hσj hbandj
  have cast1 : (((j + 1 : ℤ)) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
  unfold kl_a kl_c
  rw [cast1]
  have eW : (e - x) / 2 * kl_W x e = 2 * (1 + 45 / x ^ 2) := by
    unfold kl_W; field_simp; ring
  have eT : kl_T M σ = kl_beta M σ + 2 * |M * σ| := rfl
  have hWT : kl_W x e * kl_T M σ ≤ (j : ℝ) / 4 := by linarith
  have hWD : kl_W x e * (9 / (4 * x)) ≤ (j : ℝ) / 4 := by linarith
  have hj2 : (0 : ℝ) < (j : ℝ) ^ 2 := by positivity
  have e1 : kl_W x e * (kl_T M σ / (j : ℝ) ^ 2) ≤ 1 / 4 := by
    have h1 : kl_W x e * (kl_T M σ / (j : ℝ) ^ 2) = kl_W x e * kl_T M σ / (j : ℝ) ^ 2 := by ring
    rw [h1, div_le_iff₀ hj2]
    nlinarith only [hWT, j2]
  have e2 : kl_W x e * (9 * h / (4 * x)) ≤ 1 / 4 := by
    have h1 : kl_W x e * (9 * h / (4 * x)) = kl_W x e * (9 / (4 * x)) * h := by ring
    rw [h1]
    calc _ ≤ (j : ℝ) / 4 * h := mul_le_mul_of_nonneg_right hWD hh.le
      _ ≤ 1 / 4 := by linarith only [hjh]
  refine ⟨by linarith only [f1], by linarith only [f2], f3, f4, f5, ?_, ?_, ?_⟩
  · have h1 : |1 / 2 * rr M σ ((j : ℝ) + 1) * √(1 - (((j : ℝ) + 1) * h) ^ 2) -
        1 / 2 * rr M σ (j : ℝ) * √(1 - ((j : ℝ) * h) ^ 2)| +
        |x - M * σ / (((j : ℝ) + 1) * (((j : ℝ) + 1) + 1)) - (x - M * σ / ((j : ℝ) * ((j : ℝ) + 1)))| ≤
        kl_T M σ / (j : ℝ) ^ 2 + 9 * h / (4 * x) := by rw [eT]; exact f6
    have h2 : 0 ≤ 2 * (1 + 45 / x ^ 2) := by positivity
    calc _ ≤ 2 * (1 + 45 / x ^ 2) * (kl_T M σ / (j : ℝ) ^ 2 + 9 * h / (4 * x)) := mul_le_mul_of_nonneg_left h1 h2
      _ = (e - x) / 2 * (kl_W x e * (kl_T M σ / (j : ℝ) ^ 2 + 9 * h / (4 * x))) := by
          rw [← mul_assoc, eW]
  · exact mul_nonneg hW.le (add_nonneg (div_nonneg hT (sq_nonneg _)) (by positivity))
  · rw [mul_add]; linarith

/-- The accumulated variation over a band of `n ≤ 1/h` steps starting at `k₀ ≥ 2` is at most `E₀`. -/
lemma kl_band_sum {M σ x e h : ℝ} (hx : 0 < x) (hxe : x < e) {k0 : ℤ} (hk0r : (2 : ℝ) ≤ k0) (n : ℕ)
    (hnh : (n : ℝ) * h ≤ 1) :
    ∑ i ∈ range n, kl_W x e * (kl_T M σ / ((k0 + (i : ℤ) : ℤ) : ℝ) ^ 2 + 9 * h / (4 * x)) ≤ kl_E0 M σ x e := by
  have hW := kl_W_pos hx hxe
  have hT := kl_T_pos M σ
  have e1 : ∀ i ∈ range n, kl_W x e * (kl_T M σ / ((k0 + (i : ℤ) : ℤ) : ℝ) ^ 2 + 9 * h / (4 * x)) =
      kl_W x e * kl_T M σ * (1 / ((k0 : ℝ) + (i : ℝ)) ^ 2) + kl_W x e * (9 * h / (4 * x)) := by
    intro i _
    push_cast
    ring
  rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 := kl_sum_inv_sq_le_one hk0r n
  have h2 : ∑ i ∈ range n, kl_W x e * (9 * h / (4 * x)) = (n : ℝ) * (kl_W x e * (9 * h / (4 * x))) := by
    simp
  rw [h2]
  unfold kl_E0
  have h3 : (n : ℝ) * (kl_W x e * (9 * h / (4 * x))) ≤ kl_W x e * (9 / (4 * x)) := by
    have : (n : ℝ) * (kl_W x e * (9 * h / (4 * x))) = kl_W x e * (9 / (4 * x)) * ((n : ℝ) * h) := by ring
    rw [this]
    exact mul_le_of_le_one_right (by positivity) hnh
  have h4 : kl_W x e * kl_T M σ * ∑ i ∈ range n, 1 / ((k0 : ℝ) + (i : ℝ)) ^ 2 ≤ kl_W x e * kl_T M σ :=
    mul_le_of_le_one_right (by positivity) h1
  have h5 : kl_W x e * (kl_T M σ + 9 / (4 * x)) = kl_W x e * kl_T M σ + kl_W x e * (9 / (4 * x)) := by ring
  linarith only [h3, h4, h5]

/-- Endgame of the band comparison (pure real arithmetic). -/
lemma kl_final {γ S0 S1 F0 F1 E0 : ℝ} (hγ : 0 < γ) (hlow : γ / 4 * S0 ≤ F0)
    (hup : F1 ≤ 3 / 2 * S1) (hchain : F0 ≤ Real.exp (2 * E0) * F1) (hE : 0 ≤ Real.exp (2 * E0)) :
    S0 ≤ 6 / γ * Real.exp (2 * E0) * S1 := by
  set Ex := Real.exp (2 * E0) with hEx
  have h1 : γ / 4 * S0 ≤ Ex * (3 / 2 * S1) := hlow.trans (hchain.trans (mul_le_mul_of_nonneg_left hup hE))
  have h2 : S0 = 4 / γ * (γ / 4 * S0) := by field_simp
  calc S0 = 4 / γ * (γ / 4 * S0) := h2
    _ ≤ 4 / γ * (Ex * (3 / 2 * S1)) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 6 / γ * Ex * S1 := by ring

/-- **The band comparison** (see the module docstring), for the plain-function form of the coefficients. -/
theorem kl_band {M σ x e h : ℝ} (hx : 0 < x) (hxe : x < e) (he1 : e ≤ 1) (hh : 0 < h) {Y : ℤ → ℝ}
    {K0 : ℕ} (hK0 : kl_K0real M σ x e ≤ (K0 : ℝ)) {k0 k1 : ℤ} (hk0 : (K0 : ℤ) ≤ k0) (hk01 : k0 ≤ k1)
    (hband : (((k1 : ℝ) + 1) * h) ^ 2 ≤ 1 - e ^ 2)
    (hrow : ∀ k ∈ Finset.Icc k0 (k1 - 1), jac (kl_a M σ h) (kl_c x M σ) Y k = 0) :
    Y k0 ^ 2 + Y (k0 - 1) ^ 2 ≤ kl_Cband M σ x e * (Y k1 ^ 2 + Y (k1 - 1) ^ 2) := by
  have hγ0 : 0 < e - x := by linarith
  have hW := kl_W_pos hx hxe
  have hT := kl_T_pos M σ
  have hK2 : (2 : ℝ) ≤ K0 := (le_max_left _ _).trans ((le_max_left _ _).trans hK0)
  have hk0r : (2 : ℝ) ≤ k0 := by
    have : (K0 : ℝ) ≤ k0 := by exact_mod_cast hk0
    linarith
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = k1 - k0 := ⟨(k1 - k0).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hidx : ∀ i : ℕ, i ≤ n → (K0 : ℤ) ≤ k0 + (i : ℤ) ∧ k0 + (i : ℤ) ≤ k1 := fun i hi => by
    constructor <;> omega
  have F := fun (i : ℕ) (hi : i ≤ n) =>
    kl_index (M := M) (σ := σ) (x := x) (e := e) (h := h) hx hxe he1 hh hK0 (hidx i hi).1 (hidx i hi).2 hband
  have inv := ki_invariant (a := kl_a M σ h) (c := kl_c x M σ) (Y := Y)
    (ε := fun j => kl_W x e * (kl_T M σ / (j : ℝ) ^ 2 + 9 * h / (4 * x))) (k0 := k0) (m0 := (e - x) / 2)
    (B := 45 / x ^ 2) (by linarith) n
    (fun i hi => hrow _ (by rw [Finset.mem_Icc]; omega))
    (fun i hi => (F i hi).2.1)
    (fun i hi => (F i hi.le).1)
    (fun i hi => (F i hi.le).2.2.2.2.1)
    (fun i hi => (F i hi.le).2.2.2.2.2.1)
    (fun i hi => (F i hi.le).2.2.2.2.2.2.1)
    (fun i hi => (F i hi.le).2.2.2.2.2.2.2)
  -- bound the sum
  have hk1h : (k1 : ℝ) * h ≤ 1 := by
    have h1 : (((k1 : ℝ) + 1) * h) ^ 2 ≤ 1 := by linarith only [hband, sq_nonneg e]
    have hk1p : (0 : ℝ) < ((k1 : ℝ) + 1) * h := by
      have : (2 : ℝ) ≤ k1 := le_trans hk0r (by exact_mod_cast hk01)
      positivity
    have h2 : ((k1 : ℝ) + 1) * h ≤ 1 := by
      by_contra hcon; push Not at hcon; nlinarith only [h1, hcon]
    nlinarith only [h2, hh]
  have hnh : (n : ℝ) * h ≤ 1 := by
    have h1 : (n : ℝ) ≤ k1 := by
      have : (n : ℤ) ≤ k1 := by omega
      exact_mod_cast this
    exact (mul_le_mul_of_nonneg_right h1 hh.le).trans hk1h
  have hsum := kl_band_sum (M := M) (σ := σ) (x := x) (e := e) (h := h) hx hxe hk0r n hnh
  obtain ⟨hinv1, hinv2⟩ := inv
  have hk1eq : k0 + (n : ℤ) = k1 := by omega
  rw [hk1eq] at hinv2
  have hexp : Real.exp (2 * ∑ i ∈ range n, kl_W x e * (kl_T M σ / ((k0 + (i : ℤ) : ℤ) : ℝ) ^ 2 + 9 * h / (4 * x))) ≤
      Real.exp (2 * kl_E0 M σ x e) := Real.exp_le_exp.2 (by linarith)
  -- ends
  have f0 := F 0 (Nat.zero_le _)
  have fn := F n le_rfl
  simp only [Nat.cast_zero, add_zero] at f0
  rw [show k0 + (n : ℤ) = k1 by omega] at fn
  have hlow := kiF_lower (a := kl_a M σ h) (c := kl_c x M σ) (Y := Y) f0.1
  have hlown := kiF_lower (a := kl_a M σ h) (c := kl_c x M σ) (Y := Y) fn.1
  have hc2 : |kl_c x M σ k1| ≤ 2 * kl_a M σ h k1 := by
    have h1 := fn.1; have h2 := abs_nonneg (kl_c x M σ k1); linarith only [h1, h2, hγ0]
  have hup := kiF_upper (a := kl_a M σ h) (c := kl_c x M σ) (Y := Y) hc2
  have hSn : 0 ≤ Y k1 ^ 2 + Y (k1 - 1) ^ 2 := by positivity
  have hS0 : 0 ≤ Y k0 ^ 2 + Y (k0 - 1) ^ 2 := by positivity
  have hup2 : kiF (kl_a M σ h) (kl_c x M σ) Y k1 ≤ 3 / 2 * (Y k1 ^ 2 + Y (k1 - 1) ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_right fn.2.2.1 hSn
    linarith only [hup, h1]
  have hF1 : 0 ≤ kiF (kl_a M σ h) (kl_c x M σ) Y k1 := by
    have h1 : 0 ≤ (e - x) / 2 / 2 * (Y k1 ^ 2 + Y (k1 - 1) ^ 2) := by positivity
    linarith only [hlown, h1]
  have hchain : kiF (kl_a M σ h) (kl_c x M σ) Y k0 ≤ Real.exp (2 * kl_E0 M σ x e) *
      kiF (kl_a M σ h) (kl_c x M σ) Y k1 :=
    hinv2.trans (mul_le_mul_of_nonneg_right hexp hF1)
  unfold kl_Cband
  have hlow' : (e - x) / 4 * (Y k0 ^ 2 + Y (k0 - 1) ^ 2) ≤ kiF (kl_a M σ h) (kl_c x M σ) Y k0 := by
    have : (e - x) / 2 / 2 = (e - x) / 4 := by ring
    rwa [this] at hlow
  exact kl_final hγ0 hlow' hup2 hchain (Real.exp_pos _).le

/-- info: 'FormalResearch.Special.kl_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kl_band

end FormalResearch.Special
