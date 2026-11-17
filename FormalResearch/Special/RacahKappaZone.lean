module

public import FormalResearch.Special.DiscreteAiryKappaSharpZone
public import FormalResearch.Special.RacahKappaCompose

/-!
# Mass of the Airy zone with an additive error and a real tail count (Hahn / centred Racah)

`ksz_win`, `ksz_mid`, `ksz_tail`, `ksz_zone` (`DiscreteAiryKappaSharpZone`) bound the mass beyond the band by `O(\sqrt{R_0}) N` but are stated for `KkData` (integer `N_z = 1/\delta^3`,
`Y = \kappa g Ai + {\rm rest}` with `|rest| <= (C+1)\delta^3|\kappa|`).  Here the same estimates are proved for the *pointwise square bound*
`Y_k^2 <= 2G^2K^2 Ai(X_k)^2 + 2((C+1)\delta^3|K|)^2` with a free amplitude `K >= |kappa|` (so a tiny exponentially small `mu`-part can be absorbed into `K`), and the tail sum counts
`NN <= R_t/\delta^3` sites (the Racah support is `O(1/h)`, not `1/h` exactly).

**Claim class: proved** (same proofs as `ksz_*`).
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **Middle part** `a ≤ k < k_T` (`X_a ≥ 0`, `X_{k_T - 1} ≤ 1/δ`): `Σ Y_k² ≤ K₂ K²/δ`, `K₂ = 18G²e^{4/3}(1 + 3/(4c₁)) + 2(C+1)²(1/c₁ + 1)`. -/
lemma rkz_mid {X Y : ℤ → ℝ} {a kT : ℤ} {δ c1 G C K : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc1 : 0 < c1) (hC : 0 ≤ C)
    (hak : a ≤ kT) (hgap : ∀ k : ℤ, a ≤ k → k < kT → c1 * δ ≤ X (k + 1) - X k) (hXa : 0 ≤ X a) (hkT : X (kT - 1) ≤ 1 / δ)
    (hY2 : ∀ k : ℤ, a ≤ k → k ≤ kT → Y k ^ 2 ≤ 2 * G ^ 2 * K ^ 2 * airyAi (X k) ^ 2 + 2 * ((C + 1) * δ ^ 3 * |K|) ^ 2) :
    ∑ k ∈ Finset.Ico a kT, Y k ^ 2 ≤
      (18 * G ^ 2 * Real.exp (4 / 3) * (1 + 3 / (4 * c1)) + 2 * (C + 1) ^ 2 * (1 / c1 + 1)) * K ^ 2 / δ := by
  have hε0 : 0 < c1 * δ := by positivity
  have hpt : ∀ k ∈ Finset.Ico a kT, Y k ^ 2 ≤ 2 * G ^ 2 * K ^ 2 * airyAi (X k) ^ 2 + 2 * ((C + 1) * δ ^ 3 * |K|) ^ 2 := by
    intro k hk
    have hk' := Finset.mem_Ico.1 hk
    exact hY2 k hk'.1 (by omega)
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
  have hρ2 : 2 * ((C + 1) * δ ^ 3 * |K|) ^ 2 = 2 * (C + 1) ^ 2 * δ ^ 6 * K ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]; ring
  rw [hρ2]
  have h9 : 9 * Real.exp (4 / 3) * (1 + 3 / (4 * (c1 * δ))) ≤ 9 * Real.exp (4 / 3) * (1 + 3 / (4 * c1)) / δ := by
    have e : 3 / (4 * (c1 * δ)) = 3 / (4 * c1) / δ := by field_simp
    rw [e, mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
    have e2 : (1 + 3 / (4 * c1)) / δ = 1 / δ + 3 / (4 * c1) / δ := by ring
    rw [e2]; linarith
  have t1 : 2 * G ^ 2 * K ^ 2 * ∑ k ∈ Finset.Ico a kT, airyAi (X k) ^ 2 ≤
      2 * G ^ 2 * K ^ 2 * (9 * Real.exp (4 / 3) * (1 + 3 / (4 * c1)) / δ) :=
    mul_le_mul_of_nonneg_left (hgeo.trans h9) (by positivity)
  have t2 : ((kT - a : ℤ) : ℝ) * (2 * (C + 1) ^ 2 * δ ^ 6 * K ^ 2) ≤ 2 * (C + 1) ^ 2 * (1 / c1 + 1) * K ^ 2 / δ := by
    calc _ ≤ (1 / c1 + 1) / δ ^ 2 * (2 * (C + 1) ^ 2 * δ ^ 6 * K ^ 2) := mul_le_mul_of_nonneg_right hcnt (by positivity)
      _ = 2 * (C + 1) ^ 2 * (1 / c1 + 1) * K ^ 2 * δ ^ 4 := by field_simp
      _ ≤ 2 * (C + 1) ^ 2 * (1 / c1 + 1) * K ^ 2 / δ := by
        rw [le_div_iff₀ hδ]
        have : δ ^ 4 * δ ≤ 1 := by
          have : δ ^ 5 ≤ 1 := pow_le_one₀ hδ.le hδ1
          nlinarith
        have h0 : 0 ≤ 2 * (C + 1) ^ 2 * (1 / c1 + 1) * K ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left this h0]
  have e4 : (18 * G ^ 2 * Real.exp (4 / 3) * (1 + 3 / (4 * c1)) + 2 * (C + 1) ^ 2 * (1 / c1 + 1)) * K ^ 2 / δ =
      2 * G ^ 2 * K ^ 2 * (9 * Real.exp (4 / 3) * (1 + 3 / (4 * c1)) / δ) + 2 * (C + 1) ^ 2 * (1 / c1 + 1) * K ^ 2 / δ := by
    ring
  linarith [e4]


/-- **Tail part** `k ≥ k_T` (`X_{k_T} ≥ 1/δ`, monotone decay, `NN ≤ 1/δ³` sites):
`Σ_{k_T ≤ k < k_T + NN} Y_k² ≤ (54G² + 2(C+1)²) K²`. -/
lemma rkz_tail {X Y : ℤ → ℝ} {kT NN : ℤ} {δ G C K Rt : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hNN0 : 0 ≤ NN)
    (hRt0 : 0 ≤ Rt) (hNN : (NN : ℝ) ≤ Rt / δ ^ 3) (hkT : 1 / δ ≤ X kT)
    (hY : Y kT ^ 2 ≤ 2 * G ^ 2 * K ^ 2 * airyAi (X kT) ^ 2 + 2 * ((C + 1) * δ ^ 3 * |K|) ^ 2)
    (hmono : ∀ k : ℤ, kT ≤ k → Y k ^ 2 ≤ Y kT ^ 2) :
    ∑ k ∈ Finset.Ico kT (kT + NN), Y k ^ 2 ≤ Rt * (54 * G ^ 2 + 2 * (C + 1) ^ 2) * K ^ 2 := by
  have hX1 : 1 ≤ X kT := by
    have : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
    linarith
  have h1 := hY
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
  have hy : Y kT ^ 2 ≤ 54 * G ^ 2 * K ^ 2 * δ ^ 3 + 2 * (C + 1) ^ 2 * δ ^ 6 * K ^ 2 := by
    have h5 : 2 * G ^ 2 * K ^ 2 * airyAi (X kT) ^ 2 ≤ 2 * G ^ 2 * K ^ 2 * (27 * δ ^ 3) :=
      mul_le_mul_of_nonneg_left hAi2 (by positivity)
    have h6 : 2 * ((C + 1) * δ ^ 3 * |K|) ^ 2 = 2 * (C + 1) ^ 2 * δ ^ 6 * K ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]; ring
    nlinarith
  have hb := kk_ico_bound (fun k => Y k ^ 2) (a := kT) (b := kT + NN) (by omega)
    (B := Y kT ^ 2) (fun k hk => hmono k (Finset.mem_Ico.1 hk).1)
  have e : ((kT + NN - kT : ℤ) : ℝ) = (NN : ℝ) := by push_cast; ring
  rw [e] at hb
  refine hb.trans ?_
  have hY0 : 0 ≤ Y kT ^ 2 := sq_nonneg _
  have hNN0' : (0 : ℝ) ≤ NN := by exact_mod_cast hNN0
  calc (NN : ℝ) * Y kT ^ 2 ≤ (Rt / δ ^ 3) * (54 * G ^ 2 * K ^ 2 * δ ^ 3 + 2 * (C + 1) ^ 2 * δ ^ 6 * K ^ 2) :=
        mul_le_mul hNN hy hY0 (by positivity)
    _ = Rt * (54 * G ^ 2 + 2 * (C + 1) ^ 2 * δ ^ 3) * K ^ 2 := by field_simp
    _ ≤ _ := by
      have : δ ^ 3 ≤ 1 := pow_le_one₀ hδ.le hδ1
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg K)
      apply mul_le_mul_of_nonneg_left _ hRt0
      nlinarith [sq_nonneg (C + 1)]


/-- **Window part** `jz ≤ k < m+2` (`X_{jz} ≤ -1`, `-X_{jz} ≤ R₀/δ²`, `m + 2 - jz ≤ R_c/δ³`):
`Σ Y_k² ≤ 2G²K²[(√R₀/π + 2c₂R₀)/(c₁δ²) + K₁/δ] + 2(C+1)² R_c K²/δ`, `K₁ = 49/(4c₁) + 18`. -/
lemma rkz_win {X Y : ℤ → ℝ} {jz m : ℤ} {δ c1 c2 G C K R0 Rc : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc1 : 0 < c1)
    (hc2 : 0 ≤ c2) (hR0 : 0 ≤ R0) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hjm : jz ≤ m)
    (hgap : ∀ k : ℤ, jz ≤ k → k < m + 2 → c1 * δ ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ c2 * δ)
    (hXJ : X jz ≤ -1) (hXJlow : -X jz ≤ R0 / δ ^ 2) (hXm : 0 ≤ X m) (hXm1 : X (m + 1) ≤ 1 / 4)
    (hY2 : ∀ k : ℤ, jz ≤ k → k < m + 2 → Y k ^ 2 ≤ 2 * G ^ 2 * K ^ 2 * airyAi (X k) ^ 2 + 2 * ((C + 1) * δ ^ 3 * |K|) ^ 2)
    (hmcnt : ((m + 2 - jz : ℤ) : ℝ) ≤ Rc / δ ^ 3) :
    ∑ k ∈ Finset.Ico jz (m + 2), Y k ^ 2 ≤
      2 * G ^ 2 * K ^ 2 * ((√R0 / Real.pi + 2 * c2 * R0) / (c1 * δ ^ 2) + (49 / (4 * c1) + 18) / δ) +
        2 * (C + 1) ^ 2 * Rc * K ^ 2 / δ := by
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
  have hpt : ∀ k ∈ Finset.Ico jz (m + 2), Y k ^ 2 ≤ 2 * G ^ 2 * K ^ 2 * airyAi (X k) ^ 2 + 2 * ((C + 1) * δ ^ 3 * |K|) ^ 2 := by
    intro k hk
    have hk' := Finset.mem_Ico.1 hk
    exact hY2 k hk'.1 hk'.2
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Int.card_Ico, nsmul_eq_mul] at hsum
  have hcast : (((m + 2 - jz).toNat : ℕ) : ℝ) = ((m + 2 - jz : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  rw [hcast] at hsum
  refine hsum.trans ?_
  have hρ2 : 2 * ((C + 1) * δ ^ 3 * |K|) ^ 2 = 2 * (C + 1) ^ 2 * δ ^ 6 * K ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]; ring
  rw [hρ2]
  have t1 : 2 * G ^ 2 * K ^ 2 * ∑ k ∈ Finset.Ico jz (m + 2), airyAi (X k) ^ 2 ≤
      2 * G ^ 2 * K ^ 2 * ((√R0 / Real.pi + 2 * c2 * R0) / (c1 * δ ^ 2) + (49 / (4 * c1) + 18) / δ) :=
    mul_le_mul_of_nonneg_left hAi1 (by positivity)
  have t2 : ((m + 2 - jz : ℤ) : ℝ) * (2 * (C + 1) ^ 2 * δ ^ 6 * K ^ 2) ≤ 2 * (C + 1) ^ 2 * Rc * K ^ 2 / δ := by
    calc _ ≤ (Rc / δ ^ 3) * (2 * (C + 1) ^ 2 * δ ^ 6 * K ^ 2) := mul_le_mul_of_nonneg_right hmcnt (by positivity)
      _ = 2 * (C + 1) ^ 2 * Rc * δ ^ 3 * K ^ 2 := by field_simp
      _ ≤ 2 * (C + 1) ^ 2 * Rc * K ^ 2 / δ := by
        rw [le_div_iff₀ hδ]
        have : δ ^ 4 ≤ 1 := pow_le_one₀ hδ.le hδ1
        have h0 : 0 ≤ 2 * (C + 1) ^ 2 * Rc * K ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left this h0]
  linarith

/-- The zone constant. -/
noncomputable def rkzK3 (c1 G C Rc Rt : ℝ) : ℝ :=
  2 * G ^ 2 * (49 / (4 * c1) + 18) + 2 * (C + 1) ^ 2 * Rc +
    (18 * G ^ 2 * Real.exp (4 / 3) * (1 + 3 / (4 * c1)) + 2 * (C + 1) ^ 2 * (1 / c1 + 1)) + Rt * (54 * G ^ 2 + 2 * (C + 1) ^ 2)

/-- **The mass beyond `jz`** (pointwise square bound with amplitude `K`, real tail count `NN <= Rt/δ³`). -/
lemma rkz_zone {Y X : ℤ → ℝ} {jz m k1 NN : ℤ} {δ G C c1 c2 K R0 Rc Rt : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc1 : 0 < c1)
    (hc2 : 0 ≤ c2) (hC : 0 ≤ C) (hR0 : 0 ≤ R0) (hRc : 0 ≤ Rc) (hRt0 : 0 ≤ Rt) (hjzm : jz ≤ m) (hmk : m + 1 ≤ k1) (hNN0 : 0 ≤ NN)
    (hgap : ∀ k : ℤ, jz ≤ k → k < k1 + 1 → c1 * δ ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ c2 * δ)
    (hX0 : 0 ≤ X m) (hXm1 : X (m + 1) ≤ 1 / 4) (hX1 : X k1 ≤ 1 / δ) (hX2 : 1 / δ < X (k1 + 1))
    (hXJ : X jz ≤ -1) (hXJlow : -X jz ≤ R0 / δ ^ 2) (hmcnt : ((m + 2 - jz : ℤ) : ℝ) ≤ Rc / δ ^ 3)
    (hY2 : ∀ k : ℤ, jz ≤ k → k ≤ k1 + 1 →
      Y k ^ 2 ≤ 2 * G ^ 2 * K ^ 2 * airyAi (X k) ^ 2 + 2 * ((C + 1) * δ ^ 3 * |K|) ^ 2)
    (hNN : (NN : ℝ) ≤ Rt / δ ^ 3) (hmono : ∀ k : ℤ, k1 + 1 ≤ k → Y k ^ 2 ≤ Y (k1 + 1) ^ 2) :
    ∑ k ∈ Finset.Ico jz (k1 + 1 + NN), Y k ^ 2 ≤
      2 * G ^ 2 * K ^ 2 * ((√R0 / Real.pi + 2 * c2 * R0) / (c1 * δ ^ 2)) + rkzK3 c1 G C Rc Rt * K ^ 2 / δ := by
  have hsplit : ∑ k ∈ Finset.Ico jz (k1 + 1 + NN), Y k ^ 2 =
      ∑ k ∈ Finset.Ico jz (m + 2), Y k ^ 2 + ∑ k ∈ Finset.Ico (m + 2) (k1 + 1), Y k ^ 2 +
        ∑ k ∈ Finset.Ico (k1 + 1) (k1 + 1 + NN), Y k ^ 2 := by
    rw [kk_ico_split (fun k => Y k ^ 2) (b := m + 2) (by omega) (by omega),
      kk_ico_split (fun k => Y k ^ 2) (a := m + 2) (b := k1 + 1) (by omega) (by omega)]
    ring
  rw [hsplit]
  have Z1 := rkz_win (X := X) (Y := Y) (jz := jz) (m := m) (δ := δ) (c1 := c1) (c2 := c2) (G := G) (C := C)
    (K := K) (R0 := R0) (Rc := Rc) hδ hδ1 hc1 hc2 hR0 hRc hC hjzm
    (fun k h1 h2 => hgap k h1 (by omega)) hXJ hXJlow hX0 hXm1
    (fun k h1 h2 => hY2 k h1 (by omega)) hmcnt
  have hXa : 0 ≤ X (m + 2) := by
    have h1 := (hgap m (by omega) (by omega)).1
    have h2 := (hgap (m + 1) (by omega) (by omega)).1
    have e : m + 1 + 1 = m + 2 := by ring
    rw [e] at h2
    have : 0 ≤ c1 * δ := by positivity
    linarith
  have Z2 := rkz_mid (X := X) (Y := Y) (a := m + 2) (kT := k1 + 1) (δ := δ) (c1 := c1) (G := G) (C := C) (K := K)
    hδ hδ1 hc1 hC (by omega) (fun k h1 h2 => (hgap k (by omega) (by omega)).1) hXa (by simpa using hX1)
    (fun k h1 h2 => hY2 k (by omega) h2)
  have Z3 := rkz_tail (X := X) (Y := Y) (kT := k1 + 1) (NN := NN) (δ := δ) (G := G) (C := C) (K := K) (Rt := Rt) hδ hδ1 hNN0
    hRt0 hNN hX2.le (hY2 (k1 + 1) (by omega) le_rfl) hmono
  have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
  unfold rkzK3
  have hd1 : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
  have t3 : Rt * (54 * G ^ 2 + 2 * (C + 1) ^ 2) * K ^ 2 ≤ Rt * (54 * G ^ 2 + 2 * (C + 1) ^ 2) * K ^ 2 / δ := by
    rw [le_div_iff₀ hδ]
    have h0 : 0 ≤ Rt * (54 * G ^ 2 + 2 * (C + 1) ^ 2) * K ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hδ1 h0]
  have e3 : 2 * G ^ 2 * K ^ 2 * ((√R0 / Real.pi + 2 * c2 * R0) / (c1 * δ ^ 2) + (49 / (4 * c1) + 18) / δ) =
      2 * G ^ 2 * K ^ 2 * ((√R0 / Real.pi + 2 * c2 * R0) / (c1 * δ ^ 2)) + 2 * G ^ 2 * (49 / (4 * c1) + 18) * K ^ 2 / δ := by
    field_simp
  rw [e3] at Z1
  have e4 : (2 * G ^ 2 * (49 / (4 * c1) + 18) + 2 * (C + 1) ^ 2 * Rc +
      (18 * G ^ 2 * Real.exp (4 / 3) * (1 + 3 / (4 * c1)) + 2 * (C + 1) ^ 2 * (1 / c1 + 1)) +
        Rt * (54 * G ^ 2 + 2 * (C + 1) ^ 2)) * K ^ 2 / δ =
      2 * G ^ 2 * (49 / (4 * c1) + 18) * K ^ 2 / δ + 2 * (C + 1) ^ 2 * Rc * K ^ 2 / δ +
        (18 * G ^ 2 * Real.exp (4 / 3) * (1 + 3 / (4 * c1)) + 2 * (C + 1) ^ 2 * (1 / c1 + 1)) * K ^ 2 / δ +
        Rt * (54 * G ^ 2 + 2 * (C + 1) ^ 2) * K ^ 2 / δ := by ring
  rw [e4]
  linarith

/-- info: 'FormalResearch.Special.rkz_zone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.rkz_zone

end FormalResearch.Special
