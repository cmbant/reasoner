module

public import FormalResearch.Special.DiscreteAiryKappaOrderUp
public import FormalResearch.Special.DiscreteAiryKappaMain

/-!
# Order-sharp lower bound for `κ`, abstract part (plan K1, steps 3-5)

Mass accounting `N = Σ Ŷ_k² ≤ Q κ² N^{2/3}` for a sequence `Y = κ g Ai(X) + rest` that is controlled
on the window `[J, k_T]` (`X_J ≍ -δ^{-2}`, `X_{k_T} ≈ δ^{-1}`), bounded on the left by the Hahn bound `kl_hahn_left` (`hleft`) and
monotone beyond `k_T` (`kr_chain_mono`, `hmono`):

* left `k ≤ J + 1`: `Y_k² ≤ C_l(Y_J² + Y_{J+1}²)`, `Ai(X_J)² ≤ 2/√|X_J| ≲ δ` (`kai_sq_le`), so the left mass is `≲ κ² δ^{-2}`;
* window `k ≤ m+1`: `Σ Ai(X_k)² ≲ δ^{-2}` from `kai_sum_upper_bound` (the antiderivative `x Ai² - Ai'²` and `airyKer_diag_neg`);
* `m + 2 ≤ k < k_T`: `|Y_k| ≲ |κ|` and `≲ δ^{-2}` sites;
* `k ≥ k_T`: `Y_k² ≤ Y_{k_T}² ≲ κ² δ` (`Ai(X) ≤ 3e^{-2X/3}`) and `≤ N = δ^{-3}` sites.

**Claim class: proved** (abstract).
-/

@[expose] public section

open Finset

namespace FormalResearch.Special

/-- `|Ai X| ≤ 3 e^{-2X/3}` for `X ≥ 1`. -/
lemma kk_ai_tail {X : ℝ} (hX : 1 ≤ X) : |airyAi X| ≤ 3 * Real.exp (-(2 / 3) * X) := by
  have h := airyAiC_envelope (X : ℂ)
  rw [norm_airyAiC_ofReal, re_ofReal_cpow_three_halves, Complex.norm_real, Real.norm_eq_abs] at h
  have h1 : (1 + |X|) ^ (-(1 / 4) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg X]) (by norm_num)
  have h0 : 0 ≤ X := by linarith
  have h2 : X ≤ (max X 0) ^ (3 / 2 : ℝ) := by
    rw [max_eq_left h0]
    calc X = X ^ (1 : ℝ) := (Real.rpow_one X).symm
      _ ≤ X ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
  have h3 : Real.exp (-(2 / 3) * (max X 0) ^ (3 / 2 : ℝ)) ≤ Real.exp (-(2 / 3) * X) :=
    Real.exp_le_exp.2 (by linarith)
  have h4 : 0 ≤ (1 + |X|) ^ (-(1 / 4) : ℝ) := Real.rpow_nonneg (by positivity) _
  have h5 := Real.exp_pos (-(2 / 3) * (max X 0) ^ (3 / 2 : ℝ))
  calc |airyAi X| ≤ _ := h
    _ ≤ 3 * 1 * Real.exp (-(2 / 3) * X) := by gcongr
    _ = _ := by ring

/-- `e^{-(4/3)X} ≤ δ` for `X ≥ 1/δ`, `0 < δ ≤ 1`... (`δ > 0` suffices). -/
lemma kk_exp_small {δ X : ℝ} (hδ : 0 < δ) (hX : 1 / δ ≤ X) : Real.exp (-(4 / 3) * X) ≤ δ := by
  have h1 : 1 + (4 / 3) * (1 / δ) ≤ Real.exp ((4 / 3) * X) := by
    have := Real.add_one_le_exp ((4 / 3) * X)
    nlinarith
  have h2 : Real.exp (-(4 / 3) * X) = (Real.exp ((4 / 3) * X))⁻¹ := by rw [neg_mul, Real.exp_neg]
  rw [h2]
  have hp : 0 < 1 + (4 / 3) * (1 / δ) := by positivity
  have h3 : (Real.exp ((4 / 3) * X))⁻¹ ≤ (1 + (4 / 3) * (1 / δ))⁻¹ := inv_anti₀ hp h1
  refine h3.trans ?_
  rw [inv_le_comm₀ hp hδ, inv_eq_one_div]
  have : 1 / δ ≤ 1 + (4 / 3) * (1 / δ) := by
    have : 0 ≤ 1 / δ := by positivity
    linarith
  exact this

/-- Pointwise: `Y = κ g A + e`, `|e| ≤ ρ`, `|g| ≤ G` give `Y² ≤ 2 G² κ² A² + 2 ρ²`. -/
lemma kk_y_le {Y g A κ ρ G : ℝ} (hr : |Y - κ * (g * A)| ≤ ρ) (hg : |g| ≤ G) :
    Y ^ 2 ≤ 2 * G ^ 2 * κ ^ 2 * A ^ 2 + 2 * ρ ^ 2 := by
  have h1 : (Y - κ * (g * A)) ^ 2 ≤ ρ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hr 2
  have h2 : (κ * (g * A)) ^ 2 ≤ G ^ 2 * κ ^ 2 * A ^ 2 := by
    have : g ^ 2 ≤ G ^ 2 := by rw [← sq_abs g]; exact pow_le_pow_left₀ (abs_nonneg _) hg 2
    have h3 : (κ * (g * A)) ^ 2 = g ^ 2 * (κ ^ 2 * A ^ 2) := by ring
    rw [h3]; nlinarith [mul_nonneg (sq_nonneg κ) (sq_nonneg A)]
  nlinarith [sq_nonneg (Y - κ * (g * A) - κ * (g * A))]

/-- `Σ_{Ico a c} = Σ_{Ico a b} + Σ_{Ico b c}` over `ℤ`. -/
lemma kk_ico_split (f : ℤ → ℝ) {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    ∑ k ∈ Finset.Ico a c, f k = ∑ k ∈ Finset.Ico a b, f k + ∑ k ∈ Finset.Ico b c, f k := by
  rw [← Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive a b c), Finset.Ico_union_Ico_eq_Ico hab hbc]

/-- A bound `f ≤ B` on `Ico a b` gives `Σ ≤ (b - a) B`. -/
lemma kk_ico_bound (f : ℤ → ℝ) {a b : ℤ} {B : ℝ} (hab : a ≤ b) (hB : ∀ k ∈ Finset.Ico a b, f k ≤ B) :
    ∑ k ∈ Finset.Ico a b, f k ≤ ((b - a : ℤ) : ℝ) * B := by
  have := Finset.sum_le_card_nsmul (Finset.Ico a b) f B hB
  rw [Int.card_Ico, nsmul_eq_mul] at this
  have e : (((b - a).toNat : ℕ) : ℝ) = ((b - a : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  rwa [e] at this

/-- `Σ_{Ico a b} f = Σ_{i < b - a} f (a + i)`. -/
lemma kk_ico_range (f : ℤ → ℝ) {a b : ℤ} (hab : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, f k = ∑ i ∈ range (b - a).toNat, f (a + (i : ℤ)) := by
  have hIco : Finset.Ico a b = (Finset.range (b - a).toNat).image (fun i : ℕ => a + (i : ℤ)) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hk
      exact ⟨(k - a).toNat, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  rw [hIco, Finset.sum_image (by intro i _ j _ hij; simpa using hij)]

/-- **The window sum of `Ai²`**: lattice `X` with gaps in `[ε₀, ε']` on `[J, m+1)`, `X_J ≤ -1`, `X_m ≥ 0`, `X_{m+1} ≤ 1/4`:
`Σ_{J ≤ k < m+2} Ai(X_k)² ≤ (√y_J/π + 1/y_J + 2ε' y_J)/ε₀ + 9(5/(4ε₀) + 2)`, `y_J = -X_J`. -/
lemma kk_win_ai {X : ℤ → ℝ} {J m : ℤ} {ε0 ε' : ℝ} (hJm : J ≤ m) (hε0 : 0 < ε0) (hε' : 0 ≤ ε')
    (hgap : ∀ k : ℤ, J ≤ k → k < m + 1 → ε0 ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ ε')
    (hXJ : X J ≤ -1) (hXm : 0 ≤ X m) (hXm1 : X (m + 1) ≤ 1 / 4) :
    ∑ k ∈ Finset.Ico J (m + 2), airyAi (X k) ^ 2 ≤
      (√(-X J) / Real.pi + 1 / (-X J) + 2 * ε' * (-X J)) / ε0 + 9 * (5 / (4 * ε0) + 2) := by
  obtain ⟨kb, hkb1, hkb2, hkb3, hkb4⟩ := kk_ivt (X := X) (t := -1) hXJ (by linarith) hJm
  rw [kk_ico_split _ hkb1 (by omega : kb ≤ m + 2)]
  have hS1 : ∑ k ∈ Finset.Ico J kb, airyAi (X k) ^ 2 ≤
      (√(-X J) / Real.pi + 1 / (-X J) + 2 * ε' * (-X J)) / ε0 := by
    rw [kk_ico_range _ hkb1, le_div_iff₀ hε0, mul_comm]
    have := kai_sum_upper_bound (X := X) (a := J) (ε0 := ε0) (ε' := ε') (kb - J).toNat
      (fun i hi => by
        have h := hgap (J + (i : ℤ)) (by omega) (by omega)
        have e : J + ((i + 1 : ℕ) : ℤ) = J + (i : ℤ) + 1 := by push_cast; ring
        rw [e]; exact h) hε0 hε' hXJ (by rw [show J + ((kb - J).toNat : ℤ) = kb by omega]; exact hkb3)
    exact this
  have hS2 : ∑ k ∈ Finset.Ico kb (m + 2), airyAi (X k) ^ 2 ≤ 9 * (5 / (4 * ε0) + 2) := by
    have hb := kk_ico_bound (fun k => airyAi (X k) ^ 2) (a := kb) (b := m + 2) (B := 9) (by omega)
      (fun k _ => by
        have := kf_abs_airyAi_le (X k)
        have h2 : airyAi (X k) ^ 2 ≤ 3 ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
        linarith)
    have hspan := kk_span (X := X) (J := kb + 1) (m := m + 1) (ε0 := ε0) (by omega)
      (fun k h1 h2 => (hgap k (by omega) h2).1)
    have hc : ((m + 2 - kb : ℤ) : ℝ) ≤ 5 / (4 * ε0) + 2 := by
      have h1 : ((m + 1 - (kb + 1) : ℤ) : ℝ) * ε0 ≤ 5 / 4 := by linarith
      have h2 : ((m + 1 - (kb + 1) : ℤ) : ℝ) ≤ 5 / (4 * ε0) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have e : ((m + 2 - kb : ℤ) : ℝ) = ((m + 1 - (kb + 1) : ℤ) : ℝ) + 2 := by push_cast; ring
      rw [e]; linarith
    calc _ ≤ ((m + 2 - kb : ℤ) : ℝ) * 9 := hb
      _ ≤ (5 / (4 * ε0) + 2) * 9 := mul_le_mul_of_nonneg_right hc (by norm_num)
      _ = _ := by ring
  linarith

/-- info: 'FormalResearch.Special.kk_win_ai' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kk_win_ai

/-- `Y_k² ≤ 2 G² κ² · 2δ/s₀ + 2ρ²` at a site with `X_k ≤ -(s₀/δ)²/2`-type bound: for `y = -X ≥ y₀ > 0`, `y ≥ 1`:
`Y² ≤ 4 G² κ² / √y₀ + 2ρ²`. -/
lemma kk_site_left {Y g X κ ρ G y0 : ℝ} (hy0 : 0 < y0) (hy : 1 ≤ -X) (hyy : y0 ≤ -X)
    (hr : |Y - κ * (g * airyAi X)| ≤ ρ) (hg : |g| ≤ G) :
    Y ^ 2 ≤ 4 * G ^ 2 * κ ^ 2 / √y0 + 2 * ρ ^ 2 := by
  have h1 := kk_y_le hr hg
  have h2 := kai_sq_le (y := -X) hy
  rw [neg_neg] at h2
  have hs0 : 0 < √y0 := Real.sqrt_pos.2 hy0
  have h3 : 1 / √(-X) ≤ 1 / √y0 := one_div_le_one_div_of_le hs0 (Real.sqrt_le_sqrt hyy)
  have h4 : airyAi X ^ 2 ≤ 2 / √y0 := by
    calc _ ≤ 2 / √(-X) := h2
      _ = 2 * (1 / √(-X)) := by ring
      _ ≤ 2 * (1 / √y0) := by linarith
      _ = 2 / √y0 := by ring
  have h5 : 2 * G ^ 2 * κ ^ 2 * airyAi X ^ 2 ≤ 2 * G ^ 2 * κ ^ 2 * (2 / √y0) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  calc Y ^ 2 ≤ _ := h1
    _ ≤ 2 * G ^ 2 * κ ^ 2 * (2 / √y0) + 2 * ρ ^ 2 := by linarith
    _ = _ := by ring

/-- **Left part**: `Σ_{0 ≤ k < J+2} Y_k² ≤ C_l (J+2)(Y_J² + Y_{J+1}²) ≤ C_l (20 G²/s₀ + 8 (C+1)²) κ²/δ²`. -/
lemma kk_left_part {X Y g : ℤ → ℝ} {J kT : ℤ} {δ c2 G C κ s0 Cl : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs0 : 0 < s0)
    (hCl : 0 ≤ Cl) (hC : 0 ≤ C) (hJ0 : 0 ≤ J) (hJk : J + 1 ≤ kT) (hc2δ : c2 * δ ≤ 1)
    (hgap : ∀ k : ℤ, J ≤ k → k < kT → 0 ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ c2 * δ)
    (hXJ : X J ≤ -((s0 / δ) ^ 2)) (hs : 2 * δ ^ 2 ≤ s0 ^ 2)
    (hrest : ∀ k : ℤ, J ≤ k → k ≤ kT → |Y k - κ * (g k * airyAi (X k))| ≤ (C + 1) * δ ^ 3 * |κ|)
    (hg : ∀ k : ℤ, J ≤ k → k ≤ kT → |g k| ≤ G)
    (hleft : ∀ k : ℤ, k ≤ J + 1 → Y k ^ 2 ≤ Cl * (Y (J + 1) ^ 2 + Y J ^ 2))
    (hJcnt : ((J + 2 : ℤ) : ℝ) ≤ 2 / δ ^ 3) :
    ∑ k ∈ Finset.Ico 0 (J + 2), Y k ^ 2 ≤ Cl * (20 * G ^ 2 / s0 + 8 * (C + 1) ^ 2) * κ ^ 2 / δ ^ 2 := by
  have hs2 : 2 ≤ (s0 / δ) ^ 2 := by
    rw [div_pow, le_div_iff₀ (by positivity)]; linarith
  have hgJ := (hgap J le_rfl (by omega))
  have hXJ1 : X (J + 1) ≤ -((s0 / δ) ^ 2 / 2) := by
    have := hgJ.2
    linarith
  have hy1J : 1 ≤ -X J := by linarith
  have hy1J1 : 1 ≤ -X (J + 1) := by linarith
  have hsq : √((s0 / δ) ^ 2) = s0 / δ := Real.sqrt_sq (by positivity)
  have hρ : ∀ k, J ≤ k → k ≤ kT → True := fun _ _ _ => trivial
  have hρ2 : (2 : ℝ) * (((C + 1) * δ ^ 3 * |κ|)) ^ 2 = 2 * (C + 1) ^ 2 * δ ^ 6 * κ ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]; ring
  have yJ := kk_site_left (y0 := (s0 / δ) ^ 2) (by positivity) hy1J (by linarith) (hrest J le_rfl (by omega))
    (hg J le_rfl (by omega))
  have yJ1 := kk_site_left (y0 := (s0 / δ) ^ 2 / 2) (by positivity) hy1J1 (by linarith)
    (hrest (J + 1) (by omega) hJk) (hg (J + 1) (by omega) hJk)
  have e1 : 1 / √((s0 / δ) ^ 2) = δ / s0 := by rw [hsq]; field_simp
  have e2 : √((s0 / δ) ^ 2 / 2) ≥ s0 / δ / 3 * 2 := by
    apply Real.le_sqrt_of_sq_le
    have : (s0 / δ / 3 * 2) ^ 2 = (s0 / δ) ^ 2 * (4 / 9) := by ring
    rw [this]; nlinarith [sq_nonneg (s0 / δ)]
  have hs0δ : 0 < s0 / δ := by positivity
  have b1 : 4 * G ^ 2 * κ ^ 2 / √((s0 / δ) ^ 2) = 4 * G ^ 2 * κ ^ 2 * (δ / s0) := by
    rw [hsq]; field_simp
  have b2 : 4 * G ^ 2 * κ ^ 2 / √((s0 / δ) ^ 2 / 2) ≤ 6 * G ^ 2 * κ ^ 2 * (δ / s0) := by
    have hpos : 0 < √((s0 / δ) ^ 2 / 2) := Real.sqrt_pos.2 (by positivity)
    rw [div_le_iff₀ hpos]
    have : 6 * G ^ 2 * κ ^ 2 * (δ / s0) * (s0 / δ / 3 * 2) = 4 * G ^ 2 * κ ^ 2 := by field_simp; ring
    calc 4 * G ^ 2 * κ ^ 2 = 6 * G ^ 2 * κ ^ 2 * (δ / s0) * (s0 / δ / 3 * 2) := this.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left e2 (by positivity)
  rw [b1] at yJ
  have hsum : Y J ^ 2 + Y (J + 1) ^ 2 ≤ 10 * G ^ 2 * κ ^ 2 * (δ / s0) + 4 * (C + 1) ^ 2 * δ ^ 6 * κ ^ 2 := by
    nlinarith [hρ2]
  have hk : ∀ k ∈ Finset.Ico 0 (J + 2), Y k ^ 2 ≤ Cl * (10 * G ^ 2 * κ ^ 2 * (δ / s0) + 4 * (C + 1) ^ 2 * δ ^ 6 * κ ^ 2) := by
    intro k hk
    have := hleft k (by have := (Finset.mem_Ico.1 hk).2; omega)
    refine this.trans (mul_le_mul_of_nonneg_left (by linarith) hCl)
  have hb := kk_ico_bound (fun k => Y k ^ 2) (a := 0) (b := J + 2) (by omega) hk
  have hb' : ((J + 2 - 0 : ℤ) : ℝ) = ((J + 2 : ℤ) : ℝ) := by simp
  rw [hb'] at hb
  refine hb.trans ?_
  have hB0 : 0 ≤ Cl * (10 * G ^ 2 * κ ^ 2 * (δ / s0) + 4 * (C + 1) ^ 2 * δ ^ 6 * κ ^ 2) := by positivity
  calc ((J + 2 : ℤ) : ℝ) * (Cl * (10 * G ^ 2 * κ ^ 2 * (δ / s0) + 4 * (C + 1) ^ 2 * δ ^ 6 * κ ^ 2))
      ≤ (2 / δ ^ 3) * (Cl * (10 * G ^ 2 * κ ^ 2 * (δ / s0) + 4 * (C + 1) ^ 2 * δ ^ 6 * κ ^ 2)) :=
        mul_le_mul_of_nonneg_right hJcnt hB0
    _ = Cl * (20 * G ^ 2 / s0 + 8 * (C + 1) ^ 2 * δ ^ 5) * κ ^ 2 / δ ^ 2 := by field_simp; ring
    _ ≤ _ := by
      have : δ ^ 5 ≤ 1 := pow_le_one₀ hδ.le hδ1
      have h1 : 8 * (C + 1) ^ 2 * δ ^ 5 ≤ 8 * (C + 1) ^ 2 := by nlinarith [sq_nonneg (C + 1)]
      have h2 : Cl * (20 * G ^ 2 / s0 + 8 * (C + 1) ^ 2 * δ ^ 5) * κ ^ 2 ≤
          Cl * (20 * G ^ 2 / s0 + 8 * (C + 1) ^ 2) * κ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg κ)
        exact mul_le_mul_of_nonneg_left (by linarith) hCl
      exact div_le_div_of_nonneg_right h2 (by positivity)

/-- **Window part**: `Σ_{J+2 ≤ k < m+2} Y_k² ≤ (2 G² q_Ai + 2 (C+1)² R_c) κ²/δ²`, `q_Ai = (√R₀/π + 1 + 2c₂R₀)/c₁ + 9(5/(4c₁) + 2)`. -/
lemma kk_win_part {X Y g : ℤ → ℝ} {J m kT : ℤ} {δ c1 c2 G C κ R0 Rc : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc1 : 0 < c1)
    (hc2 : 0 ≤ c2) (hR0 : 0 ≤ R0) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hJm : J ≤ m) (hmk : m + 2 ≤ kT)
    (hgap : ∀ k : ℤ, J ≤ k → k < kT → c1 * δ ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ c2 * δ)
    (hXJ : X J ≤ -1) (hXJlow : -X J ≤ R0 / δ ^ 2) (hXm : 0 ≤ X m) (hXm1 : X (m + 1) ≤ 1 / 4)
    (hrest : ∀ k : ℤ, J ≤ k → k ≤ kT → |Y k - κ * (g k * airyAi (X k))| ≤ (C + 1) * δ ^ 3 * |κ|)
    (hg : ∀ k : ℤ, J ≤ k → k ≤ kT → |g k| ≤ G)
    (hmcnt : ((m + 2 - J : ℤ) : ℝ) ≤ Rc / δ ^ 3) :
    ∑ k ∈ Finset.Ico (J + 2) (m + 2), Y k ^ 2 ≤
      (2 * G ^ 2 * ((√R0 / Real.pi + 1 + 2 * c2 * R0) / c1 + 9 * (5 / (4 * c1) + 2)) + 2 * (C + 1) ^ 2 * Rc) * κ ^ 2 / δ ^ 2 := by
  have hε0 : 0 < c1 * δ := by positivity
  have hε' : 0 ≤ c2 * δ := by positivity
  have hAi := kk_win_ai (X := X) (J := J) (m := m) (ε0 := c1 * δ) (ε' := c2 * δ) hJm hε0 hε'
    (fun k h1 h2 => hgap k h1 (by omega)) hXJ hXm hXm1
  set yJ : ℝ := -X J with hyJ
  have hyJ1 : 1 ≤ yJ := by linarith
  have h1 : √yJ ≤ √R0 / δ := by
    have : √(R0 / δ ^ 2) = √R0 / δ := by
      rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hδ.le]
    rw [← this]; exact Real.sqrt_le_sqrt hXJlow
  have h2 : 1 / yJ ≤ 1 := by rw [div_le_one (by linarith)]; exact hyJ1
  have h3 : 2 * (c2 * δ) * yJ ≤ 2 * c2 * R0 / δ := by
    have : 2 * (c2 * δ) * yJ ≤ 2 * (c2 * δ) * (R0 / δ ^ 2) := mul_le_mul_of_nonneg_left hXJlow (by positivity)
    calc _ ≤ _ := this
      _ = 2 * c2 * R0 / δ := by field_simp
  have hnum : √yJ / Real.pi + 1 / yJ + 2 * (c2 * δ) * yJ ≤ (√R0 / Real.pi + 1 + 2 * c2 * R0) / δ := by
    have a1 : √yJ / Real.pi ≤ √R0 / Real.pi / δ := by
      calc _ ≤ √R0 / δ / Real.pi := div_le_div_of_nonneg_right h1 Real.pi_pos.le
        _ = _ := by ring
    have a2 : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
    have e : (√R0 / Real.pi + 1 + 2 * c2 * R0) / δ = √R0 / Real.pi / δ + 1 / δ + 2 * c2 * R0 / δ := by ring
    rw [e]; linarith
  have hAi1 : ∑ k ∈ Finset.Ico J (m + 2), airyAi (X k) ^ 2 ≤
      ((√R0 / Real.pi + 1 + 2 * c2 * R0) / c1 + 9 * (5 / (4 * c1) + 2)) / δ ^ 2 := by
    refine hAi.trans ?_
    have b1 : (√yJ / Real.pi + 1 / yJ + 2 * (c2 * δ) * yJ) / (c1 * δ) ≤ (√R0 / Real.pi + 1 + 2 * c2 * R0) / c1 / δ ^ 2 := by
      calc _ ≤ ((√R0 / Real.pi + 1 + 2 * c2 * R0) / δ) / (c1 * δ) := div_le_div_of_nonneg_right hnum hε0.le
        _ = _ := by field_simp
    have b2 : 9 * (5 / (4 * (c1 * δ)) + 2) ≤ 9 * (5 / (4 * c1) + 2) / δ ^ 2 := by
      have : 5 / (4 * (c1 * δ)) + 2 ≤ (5 / (4 * c1) + 2) / δ ^ 2 := by
        have e : 5 / (4 * (c1 * δ)) = 5 / (4 * c1) / δ := by field_simp
        rw [e]
        have hδ2 : δ ^ 2 ≤ δ := by nlinarith
        have p1 : 5 / (4 * c1) / δ ≤ 5 / (4 * c1) / δ ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hδ2
        have p2 : (2 : ℝ) ≤ 2 / δ ^ 2 := by rw [le_div_iff₀ (by positivity)]; nlinarith
        have e2 : (5 / (4 * c1) + 2) / δ ^ 2 = 5 / (4 * c1) / δ ^ 2 + 2 / δ ^ 2 := by ring
        rw [e2]; linarith
      calc _ ≤ 9 * ((5 / (4 * c1) + 2) / δ ^ 2) := mul_le_mul_of_nonneg_left this (by norm_num)
        _ = _ := by ring
    have e3 : ((√R0 / Real.pi + 1 + 2 * c2 * R0) / c1 + 9 * (5 / (4 * c1) + 2)) / δ ^ 2 =
        (√R0 / Real.pi + 1 + 2 * c2 * R0) / c1 / δ ^ 2 + 9 * (5 / (4 * c1) + 2) / δ ^ 2 := by ring
    rw [e3]; linarith
  have hpt : ∀ k ∈ Finset.Ico J (m + 2), Y k ^ 2 ≤ 2 * G ^ 2 * κ ^ 2 * airyAi (X k) ^ 2 + 2 * ((C + 1) * δ ^ 3 * |κ|) ^ 2 := by
    intro k hk
    have hk' := Finset.mem_Ico.1 hk
    exact kk_y_le (hrest k hk'.1 (by omega)) (hg k hk'.1 (by omega))
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Int.card_Ico, nsmul_eq_mul] at hsum
  have hcast : (((m + 2 - J).toNat : ℕ) : ℝ) = ((m + 2 - J : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  rw [hcast] at hsum
  have hsub : ∑ k ∈ Finset.Ico (J + 2) (m + 2), Y k ^ 2 ≤ ∑ k ∈ Finset.Ico J (m + 2), Y k ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico (by omega) le_rfl) (fun k _ _ => sq_nonneg _)
  refine hsub.trans (hsum.trans ?_)
  have hρ2 : 2 * ((C + 1) * δ ^ 3 * |κ|) ^ 2 = 2 * (C + 1) ^ 2 * δ ^ 6 * κ ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]; ring
  rw [hρ2]
  have t1 : 2 * G ^ 2 * κ ^ 2 * ∑ k ∈ Finset.Ico J (m + 2), airyAi (X k) ^ 2 ≤
      2 * G ^ 2 * κ ^ 2 * (((√R0 / Real.pi + 1 + 2 * c2 * R0) / c1 + 9 * (5 / (4 * c1) + 2)) / δ ^ 2) :=
    mul_le_mul_of_nonneg_left hAi1 (by positivity)
  have t2 : ((m + 2 - J : ℤ) : ℝ) * (2 * (C + 1) ^ 2 * δ ^ 6 * κ ^ 2) ≤ 2 * (C + 1) ^ 2 * Rc * κ ^ 2 / δ ^ 2 := by
    calc _ ≤ (Rc / δ ^ 3) * (2 * (C + 1) ^ 2 * δ ^ 6 * κ ^ 2) := mul_le_mul_of_nonneg_right hmcnt (by positivity)
      _ = 2 * (C + 1) ^ 2 * Rc * δ ^ 3 * κ ^ 2 := by field_simp
      _ ≤ 2 * (C + 1) ^ 2 * Rc * κ ^ 2 / δ ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        have : δ ^ 5 ≤ 1 := pow_le_one₀ hδ.le hδ1
        have h0 : 0 ≤ 2 * (C + 1) ^ 2 * Rc * κ ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left this h0]
  have e4 : (2 * G ^ 2 * ((√R0 / Real.pi + 1 + 2 * c2 * R0) / c1 + 9 * (5 / (4 * c1) + 2)) + 2 * (C + 1) ^ 2 * Rc) * κ ^ 2 / δ ^ 2 =
      2 * G ^ 2 * κ ^ 2 * (((√R0 / Real.pi + 1 + 2 * c2 * R0) / c1 + 9 * (5 / (4 * c1) + 2)) / δ ^ 2) +
        2 * (C + 1) ^ 2 * Rc * κ ^ 2 / δ ^ 2 := by ring
  linarith [e4]

/-- **Middle part** `m+2 ≤ k < k_T`: `Σ Y_k² ≤ (1/c₁ + 1)(3G + C + 1)² κ²/δ²`. -/
lemma kk_mid_part {X Y g : ℤ → ℝ} {m kT : ℤ} {δ c1 c2 G C κ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc1 : 0 < c1)
    (hG : 0 ≤ G) (hC : 0 ≤ C) (hmk : m + 2 ≤ kT) {J : ℤ} (hJm : J ≤ m)
    (hgap : ∀ k : ℤ, J ≤ k → k < kT → c1 * δ ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ c2 * δ)
    (hXm : 0 ≤ X m) (hkT : X (kT - 1) ≤ 1 / δ)
    (hrest : ∀ k : ℤ, J ≤ k → k ≤ kT → |Y k - κ * (g k * airyAi (X k))| ≤ (C + 1) * δ ^ 3 * |κ|)
    (hg : ∀ k : ℤ, J ≤ k → k ≤ kT → |g k| ≤ G) :
    ∑ k ∈ Finset.Ico (m + 2) kT, Y k ^ 2 ≤ (1 / c1 + 1) * (3 * G + C + 1) ^ 2 * κ ^ 2 / δ ^ 2 := by
  have hpt : ∀ k ∈ Finset.Ico (m + 2) kT, Y k ^ 2 ≤ ((3 * G + C + 1) * |κ|) ^ 2 := by
    intro k hk
    have hk' := Finset.mem_Ico.1 hk
    have hr := hrest k (by omega) (by omega)
    have hgk := hg k (by omega) (by omega)
    have hAi := kf_abs_airyAi_le (X k)
    have h1 : |Y k| ≤ (3 * G + C + 1) * |κ| := by
      have h2 : |Y k - κ * (g k * airyAi (X k))| ≤ (C + 1) * δ ^ 3 * |κ| := hr
      have h3 : |κ * (g k * airyAi (X k))| ≤ 3 * G * |κ| := by
        rw [abs_mul, abs_mul]
        have := mul_le_mul hgk hAi (abs_nonneg _) hG
        nlinarith [abs_nonneg κ]
      have h4 : (C + 1) * δ ^ 3 * |κ| ≤ (C + 1) * |κ| := by
        have : δ ^ 3 ≤ 1 := pow_le_one₀ hδ.le hδ1
        have h5 : 0 ≤ (C + 1) * |κ| := by positivity
        nlinarith [mul_le_mul_of_nonneg_left this h5]
      have : |Y k| ≤ |Y k - κ * (g k * airyAi (X k))| + |κ * (g k * airyAi (X k))| := by
        have := abs_add_le (Y k - κ * (g k * airyAi (X k))) (κ * (g k * airyAi (X k)))
        simpa using this
      nlinarith [abs_nonneg κ]
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hb := kk_ico_bound (fun k => Y k ^ 2) (a := m + 2) (b := kT) hmk hpt
  refine hb.trans ?_
  have hB0 : 0 ≤ ((3 * G + C + 1) * |κ|) ^ 2 := sq_nonneg _
  have hcnt : ((kT - (m + 2) : ℤ) : ℝ) ≤ 1 / (c1 * δ ^ 2) + 1 := by
    rcases (show kT = m + 2 ∨ m + 3 ≤ kT by omega) with h | h
    · have h0 : (0 : ℝ) ≤ 1 / (c1 * δ ^ 2) + 1 := by positivity
      rw [h]; simpa using h0
    · have hX2 : 0 ≤ X (m + 2) := by
        have := kk_span (X := X) (J := m) (m := m + 2) (ε0 := c1 * δ) (by omega)
          (fun k h1 h2 => (hgap k (by omega) (by omega)).1)
        have e : ((m + 2 - m : ℤ) : ℝ) = 2 := by push_cast; ring
        rw [e] at this
        nlinarith [mul_pos hc1 hδ]
      have hsp := kk_span (X := X) (J := m + 2) (m := kT - 1) (ε0 := c1 * δ) (by omega)
        (fun k h1 h2 => (hgap k (by omega) (by omega)).1)
      have h1 : ((kT - 1 - (m + 2) : ℤ) : ℝ) * (c1 * δ) ≤ 1 / δ := by linarith
      have h2 : ((kT - 1 - (m + 2) : ℤ) : ℝ) ≤ 1 / δ / (c1 * δ) := by
        rw [le_div_iff₀ (by positivity)]; exact h1
      have e : ((kT - (m + 2) : ℤ) : ℝ) = ((kT - 1 - (m + 2) : ℤ) : ℝ) + 1 := by push_cast; ring
      have e2 : 1 / δ / (c1 * δ) = 1 / (c1 * δ ^ 2) := by field_simp
      rw [e]; linarith
  have hδ2 : 0 < δ ^ 2 := by positivity
  calc ((kT - (m + 2) : ℤ) : ℝ) * ((3 * G + C + 1) * |κ|) ^ 2 ≤ (1 / (c1 * δ ^ 2) + 1) * ((3 * G + C + 1) * |κ|) ^ 2 :=
        mul_le_mul_of_nonneg_right hcnt hB0
    _ ≤ (1 / c1 + 1) / δ ^ 2 * ((3 * G + C + 1) * |κ|) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hB0
        have e : (1 / c1 + 1) / δ ^ 2 = 1 / (c1 * δ ^ 2) + 1 / δ ^ 2 := by field_simp
        rw [e]
        have : 1 ≤ 1 / δ ^ 2 := by rw [le_div_iff₀ hδ2]; nlinarith
        linarith
    _ = (1 / c1 + 1) * (3 * G + C + 1) ^ 2 * κ ^ 2 / δ ^ 2 := by rw [mul_pow, sq_abs]; ring

/-- **Tail part** `k ≥ k_T`: `Σ_{k_T ≤ k < k_T + NN} Y_k² ≤ NN · Y_{k_T}² ≤ (18 G² + 2(C+1)²) κ²/δ²`. -/
lemma kk_tail_part {X Y g : ℤ → ℝ} {kT NN : ℤ} {δ G C κ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hNN0 : 0 ≤ NN)
    (hNN : (NN : ℝ) ≤ 1 / δ ^ 3) (hkT : 1 / δ ≤ X kT)
    (hrest : |Y kT - κ * (g kT * airyAi (X kT))| ≤ (C + 1) * δ ^ 3 * |κ|) (hg : |g kT| ≤ G)
    (hmono : ∀ k : ℤ, kT ≤ k → Y k ^ 2 ≤ Y kT ^ 2) :
    ∑ k ∈ Finset.Ico kT (kT + NN), Y k ^ 2 ≤ (18 * G ^ 2 + 2 * (C + 1) ^ 2) * κ ^ 2 / δ ^ 2 := by
  have hX1 : 1 ≤ X kT := by
    have : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
    linarith
  have h1 := kk_y_le hrest hg
  have hAi := kk_ai_tail hX1
  have hAi2 : airyAi (X kT) ^ 2 ≤ 9 * δ := by
    have h2 : airyAi (X kT) ^ 2 ≤ (3 * Real.exp (-(2 / 3) * X kT)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hAi 2
    have h3 : (3 * Real.exp (-(2 / 3) * X kT)) ^ 2 = 9 * Real.exp (-(4 / 3) * X kT) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      have e : ((2 : ℕ) : ℝ) * (-(2 / 3) * X kT) = -(4 / 3) * X kT := by push_cast; ring
      rw [e]; norm_num
    have h4 := kk_exp_small hδ hkT
    nlinarith
  have hy : Y kT ^ 2 ≤ 18 * G ^ 2 * κ ^ 2 * δ + 2 * (C + 1) ^ 2 * δ ^ 6 * κ ^ 2 := by
    have h5 : 2 * G ^ 2 * κ ^ 2 * airyAi (X kT) ^ 2 ≤ 2 * G ^ 2 * κ ^ 2 * (9 * δ) :=
      mul_le_mul_of_nonneg_left hAi2 (by positivity)
    have h6 : 2 * ((C + 1) * δ ^ 3 * |κ|) ^ 2 = 2 * (C + 1) ^ 2 * δ ^ 6 * κ ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]; ring
    nlinarith
  have hb := kk_ico_bound (fun k => Y k ^ 2) (a := kT) (b := kT + NN) (by omega)
    (B := Y kT ^ 2) (fun k hk => hmono k (Finset.mem_Ico.1 hk).1)
  have e : ((kT + NN - kT : ℤ) : ℝ) = (NN : ℝ) := by push_cast; ring
  rw [e] at hb
  refine hb.trans ?_
  have hY0 : 0 ≤ Y kT ^ 2 := sq_nonneg _
  have hNN0' : (0 : ℝ) ≤ NN := by exact_mod_cast hNN0
  calc (NN : ℝ) * Y kT ^ 2 ≤ (1 / δ ^ 3) * (18 * G ^ 2 * κ ^ 2 * δ + 2 * (C + 1) ^ 2 * δ ^ 6 * κ ^ 2) :=
        mul_le_mul hNN hy hY0 (by positivity)
    _ = (18 * G ^ 2 + 2 * (C + 1) ^ 2 * δ ^ 5) * κ ^ 2 / δ ^ 2 := by field_simp
    _ ≤ _ := by
      have : δ ^ 5 ≤ 1 := pow_le_one₀ hδ.le hδ1
      have h2 : (18 * G ^ 2 + 2 * (C + 1) ^ 2 * δ ^ 5) * κ ^ 2 ≤ (18 * G ^ 2 + 2 * (C + 1) ^ 2) * κ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg κ)
        nlinarith [sq_nonneg (C + 1)]
      exact div_le_div_of_nonneg_right h2 (by positivity)

/-- The constant `Q` of `kk_lb_final`. -/
noncomputable def kkQ (c1 c2 G C s0 R0 Rc Cl : ℝ) : ℝ :=
  Cl * (20 * G ^ 2 / s0 + 8 * (C + 1) ^ 2) +
    (2 * G ^ 2 * ((√R0 / Real.pi + 1 + 2 * c2 * R0) / c1 + 9 * (5 / (4 * c1) + 2)) + 2 * (C + 1) ^ 2 * Rc) +
    (1 / c1 + 1) * (3 * G + C + 1) ^ 2 + (18 * G ^ 2 + 2 * (C + 1) ^ 2)

/-- **Mass accounting**: `1 ≤ Q κ² δ`, i.e. `κ² ≥ N^{1/3}/Q` for `δ³ = 1/N` (abstract form; see the module docstring for the
meaning of the hypotheses). -/
lemma kk_lb_final {X Y g : ℤ → ℝ} {J m kT NN : ℤ} {δ c1 c2 G C κ s0 R0 Rc Cl : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc1 : 0 < c1) (hc2 : 0 ≤ c2) (hs0 : 0 < s0) (hG : 0 ≤ G) (hC : 0 ≤ C) (hR0 : 0 ≤ R0) (hRc : 0 ≤ Rc) (hCl : 0 ≤ Cl)
    (hJ0 : 0 ≤ J) (hJm : J ≤ m) (hmk : m + 2 ≤ kT) (hNN0 : 0 ≤ NN) (hc2δ : c2 * δ ≤ 1)
    (hgap : ∀ k : ℤ, J ≤ k → k < kT → c1 * δ ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ c2 * δ)
    (hXJ : X J ≤ -((s0 / δ) ^ 2)) (hs : 2 * δ ^ 2 ≤ s0 ^ 2) (hXJlow : -X J ≤ R0 / δ ^ 2)
    (hXm : 0 ≤ X m) (hXm1 : X (m + 1) ≤ 1 / 4) (hkT : X (kT - 1) ≤ 1 / δ ∧ 1 / δ ≤ X kT)
    (hrest : ∀ k : ℤ, J ≤ k → k ≤ kT → |Y k - κ * (g k * airyAi (X k))| ≤ (C + 1) * δ ^ 3 * |κ|)
    (hg : ∀ k : ℤ, J ≤ k → k ≤ kT → |g k| ≤ G)
    (hleft : ∀ k : ℤ, k ≤ J + 1 → Y k ^ 2 ≤ Cl * (Y (J + 1) ^ 2 + Y J ^ 2))
    (hmono : ∀ k : ℤ, kT ≤ k → Y k ^ 2 ≤ Y kT ^ 2)
    (hmass : 1 / δ ^ 3 ≤ ∑ k ∈ Finset.Ico 0 (kT + NN), Y k ^ 2) (hNN : (NN : ℝ) ≤ 1 / δ ^ 3)
    (hJcnt : ((J + 2 : ℤ) : ℝ) ≤ 2 / δ ^ 3) (hmcnt : ((m + 2 - J : ℤ) : ℝ) ≤ Rc / δ ^ 3) :
    1 ≤ kkQ c1 c2 G C s0 R0 Rc Cl * (κ ^ 2 * δ) := by
  have hs2 : 2 ≤ (s0 / δ) ^ 2 := by
    rw [div_pow, le_div_iff₀ (by positivity)]; linarith
  have hgap0 : ∀ k : ℤ, J ≤ k → k < kT → 0 ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ c2 * δ := fun k h1 h2 =>
    ⟨le_trans (by positivity) (hgap k h1 h2).1, (hgap k h1 h2).2⟩
  have PA := kk_left_part (X := X) (Y := Y) (g := g) (J := J) (kT := kT) (δ := δ) (c2 := c2) (G := G) (C := C) (κ := κ)
    (s0 := s0) (Cl := Cl) hδ hδ1 hs0 hCl hC hJ0 (by omega) hc2δ hgap0 hXJ hs hrest hg hleft hJcnt
  have PB := kk_win_part (X := X) (Y := Y) (g := g) (J := J) (m := m) (kT := kT) (δ := δ) (c1 := c1) (c2 := c2) (G := G)
    (C := C) (κ := κ) (R0 := R0) (Rc := Rc) hδ hδ1 hc1 hc2 hR0 hRc hC hJm hmk hgap (by linarith) hXJlow hXm hXm1 hrest hg hmcnt
  have PC := kk_mid_part (X := X) (Y := Y) (g := g) (m := m) (kT := kT) (δ := δ) (c1 := c1) (c2 := c2) (G := G) (C := C)
    (κ := κ) hδ hδ1 hc1 hG hC hmk hJm hgap hXm hkT.1 hrest hg
  have PD := kk_tail_part (X := X) (Y := Y) (g := g) (kT := kT) (NN := NN) (δ := δ) (G := G) (C := C) (κ := κ) hδ hδ1 hNN0 hNN hkT.2
    (hrest kT (by omega) le_rfl) (hg kT (by omega) le_rfl) hmono
  have hsplit : ∑ k ∈ Finset.Ico 0 (kT + NN), Y k ^ 2 =
      ∑ k ∈ Finset.Ico 0 (J + 2), Y k ^ 2 + ∑ k ∈ Finset.Ico (J + 2) (m + 2), Y k ^ 2 +
        ∑ k ∈ Finset.Ico (m + 2) kT, Y k ^ 2 + ∑ k ∈ Finset.Ico kT (kT + NN), Y k ^ 2 := by
    rw [kk_ico_split (fun k => Y k ^ 2) (b := J + 2) (by omega) (by omega),
      kk_ico_split (fun k => Y k ^ 2) (a := J + 2) (b := m + 2) (by omega) (by omega),
      kk_ico_split (fun k => Y k ^ 2) (a := m + 2) (b := kT) (by omega) (by omega)]
    ring
  rw [hsplit] at hmass
  have htot : 1 / δ ^ 3 ≤ kkQ c1 c2 G C s0 R0 Rc Cl * κ ^ 2 / δ ^ 2 := by
    unfold kkQ
    have e : (Cl * (20 * G ^ 2 / s0 + 8 * (C + 1) ^ 2) +
        (2 * G ^ 2 * ((√R0 / Real.pi + 1 + 2 * c2 * R0) / c1 + 9 * (5 / (4 * c1) + 2)) + 2 * (C + 1) ^ 2 * Rc) +
        (1 / c1 + 1) * (3 * G + C + 1) ^ 2 + (18 * G ^ 2 + 2 * (C + 1) ^ 2)) * κ ^ 2 / δ ^ 2 =
        Cl * (20 * G ^ 2 / s0 + 8 * (C + 1) ^ 2) * κ ^ 2 / δ ^ 2 +
        (2 * G ^ 2 * ((√R0 / Real.pi + 1 + 2 * c2 * R0) / c1 + 9 * (5 / (4 * c1) + 2)) + 2 * (C + 1) ^ 2 * Rc) * κ ^ 2 / δ ^ 2 +
        (1 / c1 + 1) * (3 * G + C + 1) ^ 2 * κ ^ 2 / δ ^ 2 + (18 * G ^ 2 + 2 * (C + 1) ^ 2) * κ ^ 2 / δ ^ 2 := by ring
    rw [e]; linarith
  have h3 : 0 < δ ^ 3 := by positivity
  have := mul_le_mul_of_nonneg_right htot h3.le
  have e1 : 1 / δ ^ 3 * δ ^ 3 = 1 := by field_simp
  have e2 : kkQ c1 c2 G C s0 R0 Rc Cl * κ ^ 2 / δ ^ 2 * δ ^ 3 = kkQ c1 c2 G C s0 R0 Rc Cl * (κ ^ 2 * δ) := by
    field_simp
  rw [e1, e2] at this
  exact this

/-- info: 'FormalResearch.Special.kk_lb_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kk_lb_final

end FormalResearch.Special
