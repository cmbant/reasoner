module

public import FormalResearch.Special.DiscreteAiryKappaOrderLow
public import FormalResearch.Special.DiscreteAiryKappaOrderData

/-!
# Sharp `κ`: the mass of the turning-point zone is `O(√R₀) N` (plan K1, sharp constant, step 6)

The order-sharp lower bound (`DiscreteAiryKappaOrderLow`) bounds the mass beyond the first Airy zero only up to `O(κ²δ^{-2}) = O(N)`; the
sharp constant needs this part small.  With `Y = κ g Ai(X) + rest` (`|rest| ≤ (C+1)δ³|κ|`), `|g| ≤ G`, lattice gaps `X_{k+1} - X_k ∈ [c₁δ, c₂δ]`:

* `ksz_ai_sq`, `ksz_geo`: for `X ≥ 0`, `Ai(X)² ≤ 9e^{4/3} e^{-4X/3}`; on a lattice with gaps `≥ ε₀` and `X_a ≥ 0`: `Σ Ai(X_k)² ≤ 9e^{4/3}(1 + 3/(4ε₀))`;
* `ksz_win`: `Σ_{jz ≤ k < m+2} Y_k² ≤ 2G²κ²[(√R₀/π + 2c₂R₀)/(c₁δ²) + K₁/δ] + 2(C+1)²R_c δ³κ²` (`-X_{jz} ≤ R₀/δ²`, `m + 2 - jz ≤ R_c/δ³`);
* `ksz_mid`: `Σ_{m+2 ≤ k < k_T} Y_k² ≤ K₂ κ²/δ`;
* `ksz_tail`: `Σ_{k ≥ k_T} Y_k² ≤ (54G² + 2(C+1)²) κ²` (`e^{-t} ≤ 6/t³`).

Hence the mass beyond `jz` is `κ²δ · N · (2G²(√R₀/π + 2c₂R₀)/c₁ + O(δ))`, which is `O(A)·N` for `R₀ = O(A²)`.

**Claim class: proved** (abstract).
-/

@[expose] public section

open Finset

namespace FormalResearch.Special

/-- `Ai(X)² ≤ 9 e^{4/3} e^{-4X/3}` (for every `X`; useful for `X ≥ 0`). -/
lemma ksz_ai_sq (X : ℝ) : airyAi X ^ 2 ≤ 9 * Real.exp (4 / 3) * Real.exp (-(4 / 3) * X) := by
  rcases le_or_gt 1 X with h1 | h1
  · have h := kk_ai_tail h1
    have h2 : airyAi X ^ 2 ≤ (3 * Real.exp (-(2 / 3) * X)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    have h3 : (3 * Real.exp (-(2 / 3) * X)) ^ 2 = 9 * Real.exp (-(4 / 3) * X) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      have e : ((2 : ℕ) : ℝ) * (-(2 / 3) * X) = -(4 / 3) * X := by push_cast; ring
      rw [e]; norm_num
    have h4 : 1 ≤ Real.exp (4 / 3) := Real.one_le_exp (by norm_num)
    have h5 : 0 ≤ Real.exp (-(4 / 3) * X) := (Real.exp_pos _).le
    nlinarith
  · have h2 := kf_abs_airyAi_le X
    have h3 : airyAi X ^ 2 ≤ 9 := by
      have : airyAi X ^ 2 ≤ 3 ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
      linarith
    have h4 : 1 ≤ Real.exp (4 / 3) * Real.exp (-(4 / 3) * X) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    nlinarith

/-- `1/(1 - e^{-t}) ≤ 1 + 1/t` for `t > 0`. -/
lemma ksz_geo_den {t : ℝ} (ht : 0 < t) : 1 / (1 - Real.exp (-t)) ≤ 1 + 1 / t := by
  have h1 : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have h2 : Real.exp (-t) = (Real.exp t)⁻¹ := Real.exp_neg t
  have hp : 0 < Real.exp t := Real.exp_pos t
  have h3 : Real.exp (-t) ≤ 1 / (1 + t) := by
    rw [h2, ← one_div]
    exact one_div_le_one_div_of_le (by linarith) h1
  have h4 : 0 < 1 - Real.exp (-t) := by
    have : Real.exp (-t) < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
    rw [Real.exp_zero] at this
    linarith
  rw [div_le_iff₀ h4]
  have h5 : t / (1 + t) ≤ 1 - Real.exp (-t) := by
    have : 1 - 1 / (1 + t) = t / (1 + t) := by field_simp; ring
    linarith
  have h6 : (1 + 1 / t) * (t / (1 + t)) = 1 := by field_simp; ring
  calc 1 = (1 + 1 / t) * (t / (1 + t)) := h6.symm
    _ ≤ (1 + 1 / t) * (1 - Real.exp (-t)) := mul_le_mul_of_nonneg_left h5 (by positivity)

/-- **Geometric lattice sum of `Ai²` on `X ≥ 0`**. -/
lemma ksz_geo {X : ℤ → ℝ} {a b : ℤ} {ε0 : ℝ} (hε0 : 0 < ε0) (hab : a ≤ b) (hXa : 0 ≤ X a)
    (hgap : ∀ k : ℤ, a ≤ k → k < b → ε0 ≤ X (k + 1) - X k) :
    ∑ k ∈ Finset.Ico a b, airyAi (X k) ^ 2 ≤ 9 * Real.exp (4 / 3) * (1 + 3 / (4 * ε0)) := by
  rw [kk_ico_range _ hab]
  set ρ : ℝ := Real.exp (-(4 / 3 * ε0)) with hρ
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := by
    have : ρ < Real.exp 0 := Real.exp_lt_exp.2 (by have := mul_pos (by norm_num : (0 : ℝ) < 4 / 3) hε0; linarith)
    rwa [Real.exp_zero] at this
  have hterm : ∀ i ∈ range (b - a).toNat, airyAi (X (a + (i : ℤ))) ^ 2 ≤ 9 * Real.exp (4 / 3) * ρ ^ i := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have hspan := kk_span (X := X) (J := a) (m := a + (i : ℤ)) (ε0 := ε0) (by omega)
      (fun k h1 h2 => hgap k h1 (by omega))
    have e : ((a + (i : ℤ) - a : ℤ) : ℝ) = (i : ℝ) := by push_cast; ring
    rw [e] at hspan
    have hX : (i : ℝ) * ε0 ≤ X (a + (i : ℤ)) := by linarith
    have hX0 : 0 ≤ X (a + (i : ℤ)) := by
      have : 0 ≤ (i : ℝ) * ε0 := by positivity
      linarith
    refine (ksz_ai_sq _).trans ?_
    have h1 : Real.exp (-(4 / 3) * X (a + (i : ℤ))) ≤ ρ ^ i := by
      rw [hρ, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.2
      nlinarith [hX]
    nlinarith [Real.exp_pos (4 / 3)]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hgeo : ∑ i ∈ range (b - a).toNat, ρ ^ i ≤ 1 / (1 - ρ) := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := (b - a).toNat) hρ0 hρ1
    rw [Finset.range_eq_Ico]
    simpa using this
  have hden := ksz_geo_den (t := 4 / 3 * ε0) (by positivity)
  have e1 : 1 + 1 / (4 / 3 * ε0) = 1 + 3 / (4 * ε0) := by field_simp
  rw [e1] at hden
  have h9 : 0 ≤ 9 * Real.exp (4 / 3) := by positivity
  exact mul_le_mul_of_nonneg_left (hgeo.trans hden) h9

/-- **Middle part** `a ≤ k < k_T` (`X_a ≥ 0`, `X_{k_T - 1} ≤ 1/δ`): `Σ Y_k² ≤ K₂ κ²/δ`, `K₂ = 18G²e^{4/3}(1 + 3/(4c₁)) + 2(C+1)²(1/c₁ + 1)`. -/
lemma ksz_mid {X Y g : ℤ → ℝ} {a kT : ℤ} {δ c1 G C κ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc1 : 0 < c1) (hC : 0 ≤ C)
    (hak : a ≤ kT) (hgap : ∀ k : ℤ, a ≤ k → k < kT → c1 * δ ≤ X (k + 1) - X k) (hXa : 0 ≤ X a) (hkT : X (kT - 1) ≤ 1 / δ)
    (hrest : ∀ k : ℤ, a ≤ k → k ≤ kT → |Y k - κ * (g k * airyAi (X k))| ≤ (C + 1) * δ ^ 3 * |κ|)
    (hg : ∀ k : ℤ, a ≤ k → k ≤ kT → |g k| ≤ G) :
    ∑ k ∈ Finset.Ico a kT, Y k ^ 2 ≤
      (18 * G ^ 2 * Real.exp (4 / 3) * (1 + 3 / (4 * c1)) + 2 * (C + 1) ^ 2 * (1 / c1 + 1)) * κ ^ 2 / δ := by
  have hε0 : 0 < c1 * δ := by positivity
  have hpt : ∀ k ∈ Finset.Ico a kT, Y k ^ 2 ≤ 2 * G ^ 2 * κ ^ 2 * airyAi (X k) ^ 2 + 2 * ((C + 1) * δ ^ 3 * |κ|) ^ 2 := by
    intro k hk
    have hk' := Finset.mem_Ico.1 hk
    exact kk_y_le (hrest k hk'.1 (by omega)) (hg k hk'.1 (by omega))
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Int.card_Ico, nsmul_eq_mul] at hsum
  have hcast : (((kT - a).toNat : ℕ) : ℝ) = ((kT - a : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  rw [hcast] at hsum
  have hgeo := ksz_geo (X := X) (a := a) (b := kT) hε0 hak hXa (fun k h1 h2 => hgap k h1 h2)
  have hcnt : ((kT - a : ℤ) : ℝ) ≤ (1 / c1 + 1) / δ ^ 2 := by
    rcases (show kT = a ∨ a + 1 ≤ kT by omega) with h | h
    · rw [h]; simp; positivity
    · have hsp := kk_span (X := X) (J := a) (m := kT - 1) (ε0 := c1 * δ) (by omega)
        (fun k h1 h2 => hgap k h1 (by omega))
      have h1 : ((kT - 1 - a : ℤ) : ℝ) * (c1 * δ) ≤ 1 / δ := by linarith
      have h2 : ((kT - 1 - a : ℤ) : ℝ) ≤ 1 / δ / (c1 * δ) := by rw [le_div_iff₀ (by positivity)]; exact h1
      have e : ((kT - a : ℤ) : ℝ) = ((kT - 1 - a : ℤ) : ℝ) + 1 := by push_cast; ring
      have e2 : 1 / δ / (c1 * δ) = 1 / c1 / δ ^ 2 := by field_simp
      have hδ2 : 1 ≤ 1 / δ ^ 2 := by rw [le_div_iff₀ (by positivity)]; nlinarith
      have e3 : (1 / c1 + 1) / δ ^ 2 = 1 / c1 / δ ^ 2 + 1 / δ ^ 2 := by ring
      rw [e, e3]; linarith
  refine hsum.trans ?_
  have hρ2 : 2 * ((C + 1) * δ ^ 3 * |κ|) ^ 2 = 2 * (C + 1) ^ 2 * δ ^ 6 * κ ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]; ring
  rw [hρ2]
  have h9 : 9 * Real.exp (4 / 3) * (1 + 3 / (4 * (c1 * δ))) ≤ 9 * Real.exp (4 / 3) * (1 + 3 / (4 * c1)) / δ := by
    have e : 3 / (4 * (c1 * δ)) = 3 / (4 * c1) / δ := by field_simp
    rw [e, mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
    have e2 : (1 + 3 / (4 * c1)) / δ = 1 / δ + 3 / (4 * c1) / δ := by ring
    rw [e2]; linarith
  have t1 : 2 * G ^ 2 * κ ^ 2 * ∑ k ∈ Finset.Ico a kT, airyAi (X k) ^ 2 ≤
      2 * G ^ 2 * κ ^ 2 * (9 * Real.exp (4 / 3) * (1 + 3 / (4 * c1)) / δ) :=
    mul_le_mul_of_nonneg_left (hgeo.trans h9) (by positivity)
  have t2 : ((kT - a : ℤ) : ℝ) * (2 * (C + 1) ^ 2 * δ ^ 6 * κ ^ 2) ≤ 2 * (C + 1) ^ 2 * (1 / c1 + 1) * κ ^ 2 / δ := by
    calc _ ≤ (1 / c1 + 1) / δ ^ 2 * (2 * (C + 1) ^ 2 * δ ^ 6 * κ ^ 2) := mul_le_mul_of_nonneg_right hcnt (by positivity)
      _ = 2 * (C + 1) ^ 2 * (1 / c1 + 1) * κ ^ 2 * δ ^ 4 := by field_simp
      _ ≤ 2 * (C + 1) ^ 2 * (1 / c1 + 1) * κ ^ 2 / δ := by
        rw [le_div_iff₀ hδ]
        have : δ ^ 4 * δ ≤ 1 := by
          have : δ ^ 5 ≤ 1 := pow_le_one₀ hδ.le hδ1
          nlinarith
        have h0 : 0 ≤ 2 * (C + 1) ^ 2 * (1 / c1 + 1) * κ ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left this h0]
  have e4 : (18 * G ^ 2 * Real.exp (4 / 3) * (1 + 3 / (4 * c1)) + 2 * (C + 1) ^ 2 * (1 / c1 + 1)) * κ ^ 2 / δ =
      2 * G ^ 2 * κ ^ 2 * (9 * Real.exp (4 / 3) * (1 + 3 / (4 * c1)) / δ) + 2 * (C + 1) ^ 2 * (1 / c1 + 1) * κ ^ 2 / δ := by
    ring
  linarith [e4]

/-- `e^{-(4/3) X} ≤ 3δ³` for `X ≥ 1/δ`. -/
lemma ksz_exp_cube {δ X : ℝ} (hδ : 0 < δ) (hX : 1 / δ ≤ X) : Real.exp (-(4 / 3) * X) ≤ 3 * δ ^ 3 := by
  have ht : 0 ≤ 4 / 3 * X := by
    have : 0 ≤ 1 / δ := by positivity
    linarith
  have h1 := Real.pow_div_factorial_le_exp (4 / 3 * X) ht 3
  have h2 : Real.exp (-(4 / 3) * X) = (Real.exp (4 / 3 * X))⁻¹ := by rw [neg_mul, Real.exp_neg]
  rw [h2]
  have hp : 0 < (4 / 3 * X) ^ 3 / ((3 : ℕ).factorial : ℝ) := by
    have : 0 < X := by have : 0 < 1 / δ := by positivity
                       linarith
    have h3 : (0 : ℝ) < ((3 : ℕ).factorial : ℝ) := by positivity
    positivity
  have h3 := inv_anti₀ hp h1
  refine h3.trans ?_
  have hf : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hf, inv_div]
  have hX3 : (4 / 3 * (1 / δ)) ^ 3 ≤ (4 / 3 * X) ^ 3 := by
    apply pow_le_pow_left₀ (by positivity); linarith
  have : 6 / (4 / 3 * X) ^ 3 ≤ 6 / (4 / 3 * (1 / δ)) ^ 3 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity) hX3
  refine this.trans ?_
  have e : 6 / (4 / 3 * (1 / δ)) ^ 3 = 6 * 27 / 64 * δ ^ 3 := by field_simp; ring
  rw [e]; nlinarith [pow_pos hδ 3]

/-- **Tail part** `k ≥ k_T` (`X_{k_T} ≥ 1/δ`, monotone decay, `NN ≤ 1/δ³` sites):
`Σ_{k_T ≤ k < k_T + NN} Y_k² ≤ (54G² + 2(C+1)²) κ²`. -/
lemma ksz_tail {X Y g : ℤ → ℝ} {kT NN : ℤ} {δ G C κ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hNN0 : 0 ≤ NN)
    (hNN : (NN : ℝ) ≤ 1 / δ ^ 3) (hkT : 1 / δ ≤ X kT)
    (hrest : |Y kT - κ * (g kT * airyAi (X kT))| ≤ (C + 1) * δ ^ 3 * |κ|) (hg : |g kT| ≤ G)
    (hmono : ∀ k : ℤ, kT ≤ k → Y k ^ 2 ≤ Y kT ^ 2) :
    ∑ k ∈ Finset.Ico kT (kT + NN), Y k ^ 2 ≤ (54 * G ^ 2 + 2 * (C + 1) ^ 2) * κ ^ 2 := by
  have hX1 : 1 ≤ X kT := by
    have : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
    linarith
  have h1 := kk_y_le hrest hg
  have hAi := kk_ai_tail hX1
  have hAi2 : airyAi (X kT) ^ 2 ≤ 27 * δ ^ 3 := by
    have h2 : airyAi (X kT) ^ 2 ≤ (3 * Real.exp (-(2 / 3) * X kT)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hAi 2
    have h3 : (3 * Real.exp (-(2 / 3) * X kT)) ^ 2 = 9 * Real.exp (-(4 / 3) * X kT) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      have e : ((2 : ℕ) : ℝ) * (-(2 / 3) * X kT) = -(4 / 3) * X kT := by push_cast; ring
      rw [e]; norm_num
    have h4 := ksz_exp_cube hδ hkT
    nlinarith
  have hy : Y kT ^ 2 ≤ 54 * G ^ 2 * κ ^ 2 * δ ^ 3 + 2 * (C + 1) ^ 2 * δ ^ 6 * κ ^ 2 := by
    have h5 : 2 * G ^ 2 * κ ^ 2 * airyAi (X kT) ^ 2 ≤ 2 * G ^ 2 * κ ^ 2 * (27 * δ ^ 3) :=
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
  calc (NN : ℝ) * Y kT ^ 2 ≤ (1 / δ ^ 3) * (54 * G ^ 2 * κ ^ 2 * δ ^ 3 + 2 * (C + 1) ^ 2 * δ ^ 6 * κ ^ 2) :=
        mul_le_mul hNN hy hY0 (by positivity)
    _ = (54 * G ^ 2 + 2 * (C + 1) ^ 2 * δ ^ 3) * κ ^ 2 := by field_simp
    _ ≤ _ := by
      have : δ ^ 3 ≤ 1 := pow_le_one₀ hδ.le hδ1
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg κ)
      nlinarith [sq_nonneg (C + 1)]

/-- **Window part** `jz ≤ k < m+2` (`X_{jz} ≤ -1`, `-X_{jz} ≤ R₀/δ²`, `m + 2 - jz ≤ R_c/δ³`):
`Σ Y_k² ≤ 2G²κ²[(√R₀/π + 2c₂R₀)/(c₁δ²) + K₁/δ] + 2(C+1)² R_c κ²/δ`, `K₁ = 49/(4c₁) + 18`. -/
lemma ksz_win {X Y g : ℤ → ℝ} {jz m : ℤ} {δ c1 c2 G C κ R0 Rc : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc1 : 0 < c1)
    (hc2 : 0 ≤ c2) (hR0 : 0 ≤ R0) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hjm : jz ≤ m)
    (hgap : ∀ k : ℤ, jz ≤ k → k < m + 2 → c1 * δ ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ c2 * δ)
    (hXJ : X jz ≤ -1) (hXJlow : -X jz ≤ R0 / δ ^ 2) (hXm : 0 ≤ X m) (hXm1 : X (m + 1) ≤ 1 / 4)
    (hrest : ∀ k : ℤ, jz ≤ k → k < m + 2 → |Y k - κ * (g k * airyAi (X k))| ≤ (C + 1) * δ ^ 3 * |κ|)
    (hg : ∀ k : ℤ, jz ≤ k → k < m + 2 → |g k| ≤ G)
    (hmcnt : ((m + 2 - jz : ℤ) : ℝ) ≤ Rc / δ ^ 3) :
    ∑ k ∈ Finset.Ico jz (m + 2), Y k ^ 2 ≤
      2 * G ^ 2 * κ ^ 2 * ((√R0 / Real.pi + 2 * c2 * R0) / (c1 * δ ^ 2) + (49 / (4 * c1) + 18) / δ) +
        2 * (C + 1) ^ 2 * Rc * κ ^ 2 / δ := by
  have hε0 : 0 < c1 * δ := by positivity
  have hε' : 0 ≤ c2 * δ := by positivity
  have hAi := kk_win_ai (X := X) (J := jz) (m := m) (ε0 := c1 * δ) (ε' := c2 * δ) hjm hε0 hε'
    (fun k h1 h2 => hgap k h1 (by omega)) hXJ hXm hXm1
  set yJ : ℝ := -X jz with hyJ
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
  have hAi1 : ∑ k ∈ Finset.Ico jz (m + 2), airyAi (X k) ^ 2 ≤
      (√R0 / Real.pi + 2 * c2 * R0) / (c1 * δ ^ 2) + (49 / (4 * c1) + 18) / δ := by
    refine hAi.trans ?_
    have b1 : (√yJ / Real.pi + 1 / yJ + 2 * (c2 * δ) * yJ) / (c1 * δ) ≤
        (√R0 / Real.pi + 2 * c2 * R0) / (c1 * δ ^ 2) + 1 / (c1 * δ) := by
      have a1 : √yJ / Real.pi ≤ √R0 / Real.pi / δ := by
        calc _ ≤ √R0 / δ / Real.pi := div_le_div_of_nonneg_right h1 Real.pi_pos.le
          _ = _ := by ring
      have hnum : √yJ / Real.pi + 1 / yJ + 2 * (c2 * δ) * yJ ≤ (√R0 / Real.pi + 2 * c2 * R0) / δ + 1 := by
        have e : (√R0 / Real.pi + 2 * c2 * R0) / δ = √R0 / Real.pi / δ + 2 * c2 * R0 / δ := by ring
        rw [e]; linarith
      calc _ ≤ ((√R0 / Real.pi + 2 * c2 * R0) / δ + 1) / (c1 * δ) := div_le_div_of_nonneg_right hnum hε0.le
        _ = _ := by field_simp
    have b2 : 9 * (5 / (4 * (c1 * δ)) + 2) ≤ 45 / (4 * c1) / δ + 18 / δ := by
      have e : 5 / (4 * (c1 * δ)) = 5 / (4 * c1) / δ := by field_simp
      rw [e]
      have : 18 ≤ 18 / δ := by rw [le_div_iff₀ hδ]; linarith
      have e2 : 45 / (4 * c1) / δ = 9 * (5 / (4 * c1) / δ) := by ring
      rw [e2]; linarith
    have e3 : 1 / (c1 * δ) = 1 / c1 / δ := by field_simp
    have e4 : (49 / (4 * c1) + 18) / δ = 45 / (4 * c1) / δ + 18 / δ + 1 / c1 / δ := by
      field_simp; ring
    rw [e4]
    rw [e3] at b1
    linarith
  have hpt : ∀ k ∈ Finset.Ico jz (m + 2), Y k ^ 2 ≤ 2 * G ^ 2 * κ ^ 2 * airyAi (X k) ^ 2 + 2 * ((C + 1) * δ ^ 3 * |κ|) ^ 2 := by
    intro k hk
    have hk' := Finset.mem_Ico.1 hk
    exact kk_y_le (hrest k hk'.1 hk'.2) (hg k hk'.1 hk'.2)
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Int.card_Ico, nsmul_eq_mul] at hsum
  have hcast : (((m + 2 - jz).toNat : ℕ) : ℝ) = ((m + 2 - jz : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  rw [hcast] at hsum
  refine hsum.trans ?_
  have hρ2 : 2 * ((C + 1) * δ ^ 3 * |κ|) ^ 2 = 2 * (C + 1) ^ 2 * δ ^ 6 * κ ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]; ring
  rw [hρ2]
  have t1 : 2 * G ^ 2 * κ ^ 2 * ∑ k ∈ Finset.Ico jz (m + 2), airyAi (X k) ^ 2 ≤
      2 * G ^ 2 * κ ^ 2 * ((√R0 / Real.pi + 2 * c2 * R0) / (c1 * δ ^ 2) + (49 / (4 * c1) + 18) / δ) :=
    mul_le_mul_of_nonneg_left hAi1 (by positivity)
  have t2 : ((m + 2 - jz : ℤ) : ℝ) * (2 * (C + 1) ^ 2 * δ ^ 6 * κ ^ 2) ≤ 2 * (C + 1) ^ 2 * Rc * κ ^ 2 / δ := by
    calc _ ≤ (Rc / δ ^ 3) * (2 * (C + 1) ^ 2 * δ ^ 6 * κ ^ 2) := mul_le_mul_of_nonneg_right hmcnt (by positivity)
      _ = 2 * (C + 1) ^ 2 * Rc * δ ^ 3 * κ ^ 2 := by field_simp
      _ ≤ 2 * (C + 1) ^ 2 * Rc * κ ^ 2 / δ := by
        rw [le_div_iff₀ hδ]
        have : δ ^ 4 ≤ 1 := pow_le_one₀ hδ.le hδ1
        have h0 : 0 ≤ 2 * (C + 1) ^ 2 * Rc * κ ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left this h0]
  linarith

/-- The zone constant `K₃`. -/
noncomputable def kszK3 (c1 G C Rc : ℝ) : ℝ :=
  2 * G ^ 2 * (49 / (4 * c1) + 18) + 2 * (C + 1) ^ 2 * Rc +
    (18 * G ^ 2 * Real.exp (4 / 3) * (1 + 3 / (4 * c1)) + 2 * (C + 1) ^ 2 * (1 / c1 + 1)) + (54 * G ^ 2 + 2 * (C + 1) ^ 2)

/-- **The mass beyond `jz`** (`J ≤ jz ≤ m`, `X_{jz} ≤ -1`, `-X_{jz} ≤ R₀/δ²`, `m + 2 - jz ≤ R_c/δ³`):
`Σ_{jz ≤ k < k₁ + 1 + N} Ŷ_k² ≤ 2G²κ²(√R₀/π + 2c₂R₀)/(c₁δ²) + K₃ κ²/δ`, `G = g_max`. -/
lemma ksz_zone {Y X g : ℤ → ℝ} {Nz J m Nw : ℤ} {δ qs r C Cmu ξ0 gmin gmax c1 c2 κmin Cl κ μ σ0 R0 Rc : ℝ}
    (d : KkData Y X g Nz δ qs r C Cmu ξ0 gmin gmax c1 c2 κmin Cl κ μ J m Nw)
    (s : KkSmall δ r C Cmu ξ0 gmin gmax c1 c2 κmin σ0) {k1 : ℤ} (hk1 : m + 1 ≤ k1) (hk1N : k1 + 1 ≤ Nw)
    (hX1 : X k1 ≤ 1 / δ) (hX2 : 1 / δ < X (k1 + 1))
    (hrest : ∀ k : ℤ, J ≤ k → k ≤ k1 + 1 → |Y k - κ * (g k * airyAi (X k))| ≤ (C + 1) * δ ^ 3 * |κ|)
    (hR0 : 0 ≤ R0) (hRc : 0 ≤ Rc) {jz : ℤ} (hjz : J ≤ jz) (hjzm : jz ≤ m) (hXJ : X jz ≤ -1) (hXJlow : -X jz ≤ R0 / δ ^ 2)
    (hmcnt : ((m + 2 - jz : ℤ) : ℝ) ≤ Rc / δ ^ 3) :
    ∑ k ∈ Finset.Ico jz (k1 + 1 + Nz), Y k ^ 2 ≤
      2 * gmax ^ 2 * κ ^ 2 * ((√R0 / Real.pi + 2 * c2 * R0) / (c1 * δ ^ 2)) + kszK3 c1 gmax C Rc * κ ^ 2 / δ := by
  have hδp := s.hδ
  have hδ1' : δ ≤ 1 := by linarith [s.d1]
  have hc2 : 0 < c2 := lt_of_lt_of_le s.hc1 s.hc12
  have hc1 := s.hc1
  have hgmax : 0 < gmax := lt_of_lt_of_le s.hgmin s.hgg
  have hgap : ∀ k : ℤ, J ≤ k → k < Nw → c1 * δ ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ c2 * δ :=
    fun k h1 h2 => d.gap k (Finset.mem_Icc.2 ⟨h1, by omega⟩)
  have hm1 := d.hm1
  have hJm := d.hJm
  have hsplit : ∑ k ∈ Finset.Ico jz (k1 + 1 + Nz), Y k ^ 2 =
      ∑ k ∈ Finset.Ico jz (m + 2), Y k ^ 2 + ∑ k ∈ Finset.Ico (m + 2) (k1 + 1), Y k ^ 2 +
        ∑ k ∈ Finset.Ico (k1 + 1) (k1 + 1 + Nz), Y k ^ 2 := by
    have hNz : 0 ≤ Nz := by have := d.hNz1; omega
    rw [kk_ico_split (fun k => Y k ^ 2) (b := m + 2) (by omega) (by omega),
      kk_ico_split (fun k => Y k ^ 2) (a := m + 2) (b := k1 + 1) (by omega) (by omega)]
    ring
  rw [hsplit]
  have hG : ∀ k : ℤ, J ≤ k → k ≤ k1 + 1 → |g k| ≤ gmax := fun k h1 h2 =>
    d.gup k (Finset.mem_Icc.2 ⟨h1, by omega⟩)
  have Z1 := ksz_win (X := X) (Y := Y) (g := g) (jz := jz) (m := m) (δ := δ) (c1 := c1) (c2 := c2) (G := gmax) (C := C)
    (κ := κ) (R0 := R0) (Rc := Rc) hδp hδ1' hc1 hc2.le hR0 hRc s.hC.le hjzm
    (fun k h1 h2 => hgap k (by omega) (by omega)) hXJ hXJlow d.X0.1 (d.Xm (m + 1) (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩))
    (fun k h1 h2 => hrest k (by omega) (by omega)) (fun k h1 h2 => hG k (by omega) (by omega)) hmcnt
  have hXa : 0 ≤ X (m + 2) := by
    have h1 := (hgap m (by omega) (by omega)).1
    have h2 := (hgap (m + 1) (by omega) (by omega)).1
    have e : m + 1 + 1 = m + 2 := by ring
    rw [e] at h2
    have := d.X0.1
    have : 0 ≤ c1 * δ := by positivity
    linarith
  have Z2 := ksz_mid (X := X) (Y := Y) (g := g) (a := m + 2) (kT := k1 + 1) (δ := δ) (c1 := c1) (G := gmax) (C := C) (κ := κ)
    hδp hδ1' hc1 s.hC.le (by omega) (fun k h1 h2 => (hgap k (by omega) (by omega)).1) hXa (by simpa using hX1)
    (fun k h1 h2 => hrest k (by omega) h2) (fun k h1 h2 => hG k (by omega) h2)
  have hmonoT' : ∀ k : ℤ, k1 + 1 ≤ k → Y k ^ 2 ≤ Y (k1 + 1) ^ 2 := by
    intro k hk
    have := d.mono (k1 + 1 - 1)
      (by
        have : (m : ℝ) ≤ ((k1 + 1 - 1 : ℤ) : ℝ) := by exact_mod_cast (by omega : m ≤ k1 + 1 - 1)
        nlinarith [d.p3, pow_pos hδp 3]) k (by omega)
    simpa using this
  have Z3 := ksz_tail (X := X) (Y := Y) (g := g) (kT := k1 + 1) (NN := Nz) (δ := δ) (G := gmax) (C := C) (κ := κ) hδp hδ1'
    (by have := d.hNz1; omega) d.hNz.le hX2.le (hrest (k1 + 1) (by omega) le_rfl) (hG (k1 + 1) (by omega) le_rfl) hmonoT'
  -- combine
  have hκ2 : 0 ≤ κ ^ 2 := sq_nonneg κ
  have hd1 : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδp]; linarith
  unfold kszK3
  have t3 : (54 * gmax ^ 2 + 2 * (C + 1) ^ 2) * κ ^ 2 ≤ (54 * gmax ^ 2 + 2 * (C + 1) ^ 2) * κ ^ 2 / δ := by
    rw [le_div_iff₀ hδp]
    have h0 : 0 ≤ (54 * gmax ^ 2 + 2 * (C + 1) ^ 2) * κ ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hδ1' h0]
  have e2 : 2 * gmax ^ 2 * κ ^ 2 * (49 / (4 * c1) + 18) / δ = 2 * gmax ^ 2 * (49 / (4 * c1) + 18) * κ ^ 2 / δ := by ring
  have e3 : 2 * gmax ^ 2 * κ ^ 2 * ((√R0 / Real.pi + 2 * c2 * R0) / (c1 * δ ^ 2) + (49 / (4 * c1) + 18) / δ) =
      2 * gmax ^ 2 * κ ^ 2 * ((√R0 / Real.pi + 2 * c2 * R0) / (c1 * δ ^ 2)) + 2 * gmax ^ 2 * (49 / (4 * c1) + 18) * κ ^ 2 / δ := by
    field_simp
  rw [e3] at Z1
  have e4 : (2 * gmax ^ 2 * (49 / (4 * c1) + 18) + 2 * (C + 1) ^ 2 * Rc +
      (18 * gmax ^ 2 * Real.exp (4 / 3) * (1 + 3 / (4 * c1)) + 2 * (C + 1) ^ 2 * (1 / c1 + 1)) +
        (54 * gmax ^ 2 + 2 * (C + 1) ^ 2)) * κ ^ 2 / δ =
      2 * gmax ^ 2 * (49 / (4 * c1) + 18) * κ ^ 2 / δ + 2 * (C + 1) ^ 2 * Rc * κ ^ 2 / δ +
        (18 * gmax ^ 2 * Real.exp (4 / 3) * (1 + 3 / (4 * c1)) + 2 * (C + 1) ^ 2 * (1 / c1 + 1)) * κ ^ 2 / δ +
        (54 * gmax ^ 2 + 2 * (C + 1) ^ 2) * κ ^ 2 / δ := by ring
  rw [e4]
  linarith

/-- info: 'FormalResearch.Special.ksz_geo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksz_geo

/-- info: 'FormalResearch.Special.ksz_win' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksz_win

/-- info: 'FormalResearch.Special.ksz_mid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksz_mid

/-- info: 'FormalResearch.Special.ksz_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksz_tail

/-- info: 'FormalResearch.Special.ksz_zone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksz_zone

end FormalResearch.Special
