module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedRegionOneProd

/-!
# Lower bound for the Airy window product `W_D` on the real line (`rem:thmU`, Step (2))

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma U* (`rem:thmU`), Step (2).  For a profile with `u_j = a_j`
(`2 ≤ j ≤ M`), `|a_j - u_j| ≤ C_Z j^{-4/3}` (`j > M`), first site `u_f ≤ a_1`, `a_1 - u_f ≤ (a_1 - a_2)/8`
and a real `u` with `a_K ≤ u < u_f`, `M ≥ 2K` (`window_lower`):

* left half of cell 1 (`u ≥ (a_1 + a_2)/2`): `‖W(u)‖ ≥ c (u_f - u)` (the paper's `|W_D| ≥ c c'^{-1/3}`);
* elsewhere (`u ≤ (a_1 + a_2)/2`): `‖W(u)‖ ≥ c m/(u_f - u)` whenever `m ≤ k^{1/3} ε_k²` for all `2 ≤ k ≤ K + 1`
  (the paper's `|W_D| ≳ n^{1/3} · n^{-2/3} · η_n² n^{-2/3}`, the factor `1/(u_f - u)` being `≍ n^{-2/3}`).

The paper's separate "between discs" estimate `|W_D| ≳ |u|^{-3/2}` is not needed: the cell lemma
(`airy_cell_lower`) gives `Ai(u)²/(u - a_k)² ≳ k^{1/3}` at the nearest zero throughout the cell, and
`(u - u_k)² + ε_k² ≥ ε_k²` is used everywhere.

All results are proved unconditionally.
-/

@[expose] public section

open Set Filter Topology
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Window

/-- `‖W(u)‖` off the Airy zeros (`f = 1`). -/
lemma norm_airyWindowProd_real (uF : ℝ) (uSite epsU : ℕ → ℝ) {u : ℝ}
    (hu : ∀ j : ℕ, 1 ≤ j → u ≠ airyZero j) :
    ‖airyWindowProd 1 uF uSite epsU (u : ℂ)‖ =
      airyAi u ^ 2 * |u - uF| / (u - airyZero 1) ^ 2 * ‖airyProdTail 1 uSite epsU (u : ℂ)‖ := by
  have hu' : ∀ n : ℕ, 1 ≤ n → (u : ℂ) ≠ (airyZero n : ℂ) := fun n hn h =>
    hu n hn (Complex.ofReal_injective h)
  rw [airyWindowProd_eq_of_ne 1 uF uSite epsU hu']
  simp only [Finset.Icc_self, Finset.prod_singleton]
  rw [norm_mul]
  congr 1
  rw [airyAiC_ofReal]
  have : (-(airyAi u : ℂ) ^ 2 * ((u : ℂ) - (uF : ℂ)) / ((u : ℂ) - (airyZero 1 : ℂ)) ^ 2) =
      ((-(airyAi u) ^ 2 * (u - uF) / (u - airyZero 1) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_neg, abs_pow, abs_pow]
  simp only [sq_abs]

lemma exists_cell (K : ℕ) (hK : 1 ≤ K) : ∀ u : ℝ, u ≤ airyZero 1 → airyZero K ≤ u →
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ K ∧ airyZero (n + 1) ≤ u ∧ u ≤ airyZero n := by
  induction K, hK using Nat.le_induction with
  | base =>
    intro u h1 h2
    exact ⟨1, le_rfl, le_rfl, by linarith [airyZero_strictAnti (n := 1) le_rfl], h1⟩
  | succ K hK ih =>
    intro u h1 h2
    by_cases h : airyZero K ≤ u
    · obtain ⟨n, hn1, hn2, hn3, hn4⟩ := ih u h1 h
      exact ⟨n, hn1, by omega, hn3, hn4⟩
    · push Not at h
      exact ⟨K, hK, Nat.le_succ K, h2, h.le⟩

/-- On the cell `[a_{n+1}, a_n]`, an index `k ∈ {n, n+1}` with `|Ai(u)| ≥ c k^{1/6} |u - a_k|` and `k ≥ 2`
(for `n = 1` this uses `u ≤ (a_1 + a_2)/2`). -/
lemma cell_nearest_two {cL : ℝ} (hcL : 0 < cL)
    (hcell : ∀ n : ℕ, 1 ≤ n → ∀ u : ℝ, airyZero (n + 1) ≤ u → u ≤ airyZero n →
      cL * (n : ℝ) ^ (1 / 6 : ℝ) * min (u - airyZero (n + 1)) (airyZero n - u) ≤ |airyAi u|)
    {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (h1 : airyZero (n + 1) ≤ u) (h2 : u ≤ airyZero n)
    (hn1 : n = 1 → u ≤ (airyZero 1 + airyZero 2) / 2) :
    ∃ k : ℕ, 2 ≤ k ∧ n ≤ k ∧ k ≤ n + 1 ∧ cL / 2 * (k : ℝ) ^ (1 / 6 : ℝ) * |u - airyZero k| ≤ |airyAi u| := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hc := hcell n hn u h1 h2
  have hk6 : ∀ k : ℕ, k ≤ n + 1 → (k : ℝ) ^ (1 / 6 : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 6 : ℝ) := by
    intro k hk
    have hk' : (k : ℝ) ≤ 2 * n := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have : (k : ℝ) ≤ n + 1 := by exact_mod_cast hk
      linarith
    have h3 : (k : ℝ) ^ (1 / 6 : ℝ) ≤ (2 * (n : ℝ)) ^ (1 / 6 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hk' (by norm_num)
    rw [Real.mul_rpow (by norm_num) hn0.le] at h3
    have h4 : (2 : ℝ) ^ (1 / 6 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (1 / 6 : ℝ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have hp : 0 ≤ (n : ℝ) ^ (1 / 6 : ℝ) := Real.rpow_nonneg hn0.le _
    nlinarith
  have hmk : ∀ (k : ℕ), k ≤ n + 1 → min (u - airyZero (n + 1)) (airyZero n - u) = |u - airyZero k| →
      cL / 2 * (k : ℝ) ^ (1 / 6 : ℝ) * |u - airyZero k| ≤ |airyAi u| := by
    intro k hk hmin
    rw [← hmin]
    have hm0 : 0 ≤ min (u - airyZero (n + 1)) (airyZero n - u) := le_min (by linarith) (by linarith)
    calc cL / 2 * (k : ℝ) ^ (1 / 6 : ℝ) * min (u - airyZero (n + 1)) (airyZero n - u)
        ≤ cL / 2 * (2 * (n : ℝ) ^ (1 / 6 : ℝ)) * min (u - airyZero (n + 1)) (airyZero n - u) := by
          gcongr; exact hk6 k hk
      _ = cL * (n : ℝ) ^ (1 / 6 : ℝ) * min (u - airyZero (n + 1)) (airyZero n - u) := by ring
      _ ≤ _ := hc
  by_cases hn1' : n = 1
  · subst hn1'
    have hle : u - airyZero (1 + 1) ≤ airyZero 1 - u := by
      have := hn1 rfl
      have h22 : airyZero (1 + 1) = airyZero 2 := rfl
      rw [h22]; linarith
    refine ⟨2, le_rfl, by norm_num, le_rfl, hmk 2 le_rfl ?_⟩
    rw [min_eq_left hle, abs_of_nonneg (by linarith)]
  · have hn2 : 2 ≤ n := by omega
    rcases le_total (u - airyZero (n + 1)) (airyZero n - u) with hle | hle
    · exact ⟨n + 1, by omega, by omega, le_rfl, hmk (n + 1) le_rfl (by
        rw [min_eq_left hle, abs_of_nonneg (by linarith)])⟩
    · exact ⟨n, hn2, le_rfl, by omega, hmk n (by omega) (by
        rw [min_eq_right hle, abs_sub_comm, abs_of_nonneg (by linarith)])⟩

/-- No Airy zero lies in `[(a_1 + a_2)/2, a_1)`. -/
lemma not_zero_of_mid_le {u : ℝ} (hu1 : (airyZero 1 + airyZero 2) / 2 ≤ u) (hu2 : u < airyZero 1)
    {j : ℕ} (hj : 1 ≤ j) : u ≠ airyZero j := by
  intro h
  rcases hj.eq_or_lt with rfl | hj1
  · linarith
  · have h2 : airyZero j ≤ airyZero 2 := airyZero_le_of_le (by norm_num) (by omega)
    have h3 := airyZero_strictAnti (n := 1) le_rfl
    have h4 : airyZero 2 = airyZero (1 + 1) := rfl
    linarith

/-- The algebra of the final step of `window_lower_off`. -/
lemma window_alg {A X E kk c2 eR T V m w : ℝ} (hX : 0 < X) (hE : 0 ≤ E) (hkk : 0 ≤ kk) (hc2 : 0 ≤ c2)
    (heR : 0 ≤ eR) (hA : c2 * kk * X ≤ A) (hT : eR * ((X + E) / X) ≤ T) (hV : 0 ≤ V)
    (hm0 : 0 ≤ m) (hm : m ≤ kk * E) (hw : w ≤ V) :
    c2 * eR * w * m ≤ A * V * T := by
  have hXE : 0 ≤ (X + E) / X := by positivity
  have h1 : c2 * kk * X * V * (eR * ((X + E) / X)) ≤ A * V * T := by
    have h2 : c2 * kk * X * V ≤ A * V := mul_le_mul_of_nonneg_right hA hV
    exact mul_le_mul h2 hT (by positivity) (by nlinarith [mul_nonneg hV (le_trans (by positivity) hA)])
  have h3 : c2 * kk * X * V * (eR * ((X + E) / X)) = c2 * kk * eR * V * (X + E) := by
    field_simp
  have h4 : c2 * kk * eR * V * E ≤ c2 * kk * eR * V * (X + E) := by
    have : 0 ≤ c2 * kk * eR * V := by positivity
    nlinarith [mul_nonneg this hX.le]
  have h5 : c2 * eR * V * m ≤ c2 * kk * eR * V * E := by
    have : 0 ≤ c2 * eR * V := by positivity
    calc c2 * eR * V * m ≤ c2 * eR * V * (kk * E) := mul_le_mul_of_nonneg_left hm this
      _ = _ := by ring
  have h6 : c2 * eR * w * m ≤ c2 * eR * V * m := by
    have : 0 ≤ c2 * eR := by positivity
    have : c2 * eR * w ≤ c2 * eR * V := mul_le_mul_of_nonneg_left hw this
    exact mul_le_mul_of_nonneg_right this hm0
  linarith

lemma caseB_alg {A X E kk c2 eR T V m q : ℝ} (hX : 0 < X) (hE : 0 ≤ E) (hkk : 0 ≤ kk) (hc2 : 0 ≤ c2)
    (heR : 0 ≤ eR) (hq : 1 ≤ q) (hA : c2 * kk * X ≤ A) (hT : eR * ((X + E) / X) ≤ T)
    (hV : 3 / 16 / q ≤ V) (hm : m ≤ kk * E / q) :
    c2 * eR * (3 / 16) * m ≤ A * V * T := by
  have hq0 : 0 < q := by linarith
  have hV0 : 0 ≤ V := le_trans (by positivity) hV
  have h1 := window_alg hX hE hkk hc2 heR hA hT hV0 (mul_nonneg hkk hE) le_rfl hV
  have h2 : (3 / 16) * m ≤ 3 / 16 / q * (kk * E) := by
    calc (3 / 16) * m ≤ (3 / 16) * (kk * E / q) := by gcongr
      _ = _ := by ring
  have hc : 0 ≤ c2 * eR := mul_nonneg hc2 heR
  calc c2 * eR * (3 / 16) * m = c2 * eR * ((3 / 16) * m) := by ring
    _ ≤ c2 * eR * (3 / 16 / q * (kk * E)) := mul_le_mul_of_nonneg_left h2 hc
    _ = c2 * eR * (3 / 16 / q) * (kk * E) := by ring
    _ ≤ _ := h1

lemma caseA_alg {A p y T c eR : ℝ} (hp : 0 < p) (hy : 0 ≤ y) (hc : 0 ≤ c) (heR : 0 ≤ eR)
    (hA : c * p ≤ A) (hT : eR ≤ T) : c * eR * y ≤ A * y / p * T := by
  have h1 : c ≤ A / p := by rw [le_div_iff₀ hp]; exact hA
  calc c * eR * y = c * y * eR := by ring
    _ ≤ A / p * y * T := by
        have : 0 ≤ c * y := mul_nonneg hc hy
        have h2 : c * y ≤ A / p * y := mul_le_mul_of_nonneg_right h1 hy
        exact mul_le_mul h2 hT heR (le_trans this h2)
    _ = A * y / p * T := by ring

lemma airy_sq_lower {cL : ℝ} (hcL : 0 < cL) {k : ℕ} (hk : 1 ≤ k) {u : ℝ}
    (h : cL / 2 * (k : ℝ) ^ (1 / 6 : ℝ) * |u - airyZero k| ≤ |airyAi u|) :
    (cL / 2) ^ 2 * (k : ℝ) ^ (1 / 3 : ℝ) * (u - airyZero k) ^ 2 ≤ airyAi u ^ 2 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : (cL / 2 * (k : ℝ) ^ (1 / 6 : ℝ) * |u - airyZero k|) ^ 2 ≤ |airyAi u| ^ 2 :=
    pow_le_pow_left₀ (by positivity) h 2
  rw [sq_abs] at h1
  refine le_trans (le_of_eq ?_) h1
  rw [mul_pow, mul_pow, sq_abs, ← Real.rpow_natCast ((k : ℝ) ^ (1 / 6 : ℝ)) 2, ← Real.rpow_mul hk0.le]
  norm_num

/-- Geometry of case B: `(u_f - u)/(u - a_1)² ≥ (3/16)/(k+1)^{2/3}` when `a_{k+1} ≤ u ≤ (a_1+a_2)/2`. -/
lemma geo_ratio {uF u : ℝ} {k : ℕ} (huF : uF ≤ airyZero 1) (hd : airyZero 1 - uF ≤ airyGap 1 / 8)
    (hlow : u ≤ (airyZero 1 + airyZero 2) / 2) (huuF : u < uF) (hk : 1 ≤ k) (hukk : airyZero (k + 1) ≤ u) :
    3 / 16 / ((k : ℝ) + 1) ^ (2 / 3 : ℝ) ≤ (uF - u) / (u - airyZero 1) ^ 2 := by
  have hg1 : airyGap 1 = airyZero 1 - airyZero 2 := rfl
  have hu_le : airyZero 1 - u ≥ airyGap 1 / 2 := by rw [hg1]; linarith
  have hgap : 0 < airyGap 1 := airyGap_pos le_rfl
  have hFu : 0 < uF - u := sub_pos.2 huuF
  have hu1 : 0 < airyZero 1 - u := by linarith
  have hden1 : 0 < (u - airyZero 1) ^ 2 := by nlinarith
  have hk1p : 0 < ((k : ℝ) + 1) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hFle : uF - u ≤ 3 * ((k : ℝ) + 1) ^ (2 / 3 : ℝ) := by
    have h1 := airyZero_abs_le_pow (n := k + 1) (by omega)
    rw [abs_of_neg (airyZero_neg _)] at h1
    have h2 : airyZero 1 < 0 := airyZero_neg 1
    push_cast at h1
    linarith
  have hA : 9 / 16 / (uF - u) ≤ (uF - u) / (u - airyZero 1) ^ 2 := by
    rw [div_le_div_iff₀ hFu hden1]
    have h5 : (airyZero 1 - u) ≤ 4 / 3 * (uF - u) := by linarith
    have h6 : (u - airyZero 1) ^ 2 ≤ (4 / 3 * (uF - u)) ^ 2 := by
      rw [show (u - airyZero 1) ^ 2 = (airyZero 1 - u) ^ 2 by ring]
      exact pow_le_pow_left₀ hu1.le h5 2
    nlinarith
  refine le_trans ?_ hA
  rw [div_le_div_iff₀ hk1p hFu]
  linarith [hFle]

/-- **Lower bound for `W_D` on the real line off the zeros.** -/
theorem window_lower_off {C_Z : ℝ} (hCZ : 0 < C_Z) :
    ∃ c : ℝ, 0 < c ∧ ∀ (uSite epsU : ℕ → ℝ) (uF : ℝ), AiryProdTailHypothesis 1 uSite epsU →
      ∀ (M K : ℕ), 1 ≤ K → 2 * K ≤ M → 8 * C_Z ≤ (M : ℝ) ^ 2 →
      (∀ j : ℕ, 2 ≤ j → j ≤ M → uSite j = airyZero j) →
      (∀ j : ℕ, M < j → |airyZero j - uSite j| ≤ C_Z * (j : ℝ) ^ (-(4 / 3 : ℝ))) →
      uF ≤ airyZero 1 → airyZero 1 - uF ≤ airyGap 1 / 8 →
      ∀ u : ℝ, airyZero K ≤ u → u < uF → (∀ j : ℕ, 1 ≤ j → u ≠ airyZero j) →
        ((airyZero 1 + airyZero 2) / 2 ≤ u →
          c * (uF - u) ≤ ‖airyWindowProd 1 uF uSite epsU (u : ℂ)‖) ∧
        (u ≤ (airyZero 1 + airyZero 2) / 2 → ∀ m : ℝ, 0 ≤ m →
          (∀ k : ℕ, 2 ≤ k → k ≤ K + 1 →
            m ≤ (k : ℝ) ^ (1 / 3 : ℝ) * epsU k ^ 2 / ((k : ℝ) + 1) ^ (2 / 3 : ℝ)) →
          c * m ≤ ‖airyWindowProd 1 uF uSite epsU (u : ℂ)‖) := by
  obtain ⟨R, hR0, hR⟩ := airyProdTail_lower hCZ
  obtain ⟨cL, hcL, hcell⟩ := airy_cell_lower
  have hgap1 : 0 < airyGap 1 := airyGap_pos le_rfl
  set eR := Real.exp (-R) with heR
  have heRpos : 0 < eR := Real.exp_pos _
  refine ⟨min (cL ^ 2 * eR) ((cL / 2) ^ 2 * eR * (3 / 16)), lt_min (by positivity) (by positivity),
    fun uSite epsU uF hH M K hK hMK hM hsite hdel huF hd u hKu huuF hne => ?_⟩
  have hM2 : 2 ≤ M := by omega
  have hW := norm_airyWindowProd_real uF uSite epsU hne
  have habs : |u - uF| = uF - u := by rw [abs_sub_comm]; exact abs_of_pos (sub_pos.2 huuF)
  rw [habs] at hW
  have ha12 := airyZero_strictAnti (n := 1) le_rfl
  have ha12' : airyZero (1 + 1) = airyZero 2 := rfl
  have hu1 : 0 < airyZero 1 - u := by linarith
  have hAi2 : ∀ k : ℕ, 2 ≤ k → k ≤ M →
      eR * (((u - airyZero k) ^ 2 + epsU k ^ 2) / (u - airyZero k) ^ 2) ≤
        ‖airyProdTail 1 uSite epsU (u : ℂ)‖ := fun k hk hkM =>
    hR uSite epsU hH M K hK hMK hM hsite hdel u hKu hne k hk hkM
  constructor
  · intro hmid
    have hcl := hcell 1 le_rfl u (by linarith) (by linarith)
    have hmin : min (u - airyZero (1 + 1)) (airyZero 1 - u) = airyZero 1 - u := by
      rw [ha12']; exact min_eq_right (by linarith)
    rw [hmin] at hcl
    simp only [Nat.cast_one, Real.one_rpow, mul_one] at hcl
    have hAisq : cL ^ 2 * (airyZero 1 - u) ^ 2 ≤ airyAi u ^ 2 := by
      rw [← mul_pow, ← sq_abs (airyAi u)]
      exact pow_le_pow_left₀ (by positivity) hcl 2
    have hT := hAi2 2 le_rfl hM2
    have hne2 : 0 < (u - airyZero 2) ^ 2 := by
      have := sub_ne_zero.mpr (hne 2 (by norm_num)); positivity
    have hp1 : 1 ≤ ((u - airyZero 2) ^ 2 + epsU 2 ^ 2) / (u - airyZero 2) ^ 2 := by
      rw [le_div_iff₀ hne2]; nlinarith [sq_nonneg (epsU 2)]
    have hT' : eR ≤ ‖airyProdTail 1 uSite epsU (u : ℂ)‖ := by
      refine le_trans ?_ hT
      exact le_mul_of_one_le_right heRpos.le hp1
    rw [hW]
    have hsq : (u - airyZero 1) ^ 2 = (airyZero 1 - u) ^ 2 := by ring
    rw [hsq]
    have hpos : 0 < (airyZero 1 - u) ^ 2 := by positivity
    have hA := caseA_alg (A := airyAi u ^ 2) (p := (airyZero 1 - u) ^ 2) (y := uF - u)
      (T := ‖airyProdTail 1 uSite epsU (u : ℂ)‖) (c := cL ^ 2) (eR := eR) hpos
      (sub_pos.2 huuF).le (by positivity) heRpos.le hAisq hT'
    calc min (cL ^ 2 * eR) ((cL / 2) ^ 2 * eR * (3 / 16)) * (uF - u)
        ≤ cL ^ 2 * eR * (uF - u) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (sub_pos.2 huuF).le
      _ ≤ _ := hA
  · intro hlow m hm0 hm
    obtain ⟨n, hn1, hnK, hn3, hn4⟩ := exists_cell K hK u (huuF.le.trans huF) hKu
    obtain ⟨k, hk2, hnk, hkn, hAik⟩ := cell_nearest_two hcL hcell hn1 hn3 hn4 (fun _ => hlow)
    have hkK : k ≤ K + 1 := by omega
    have hkM : k ≤ M := by omega
    have hT := hAi2 k hk2 hkM
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hukne : 0 < (u - airyZero k) ^ 2 := by
      have := sub_ne_zero.mpr (hne k (by omega)); positivity
    have hAisq := airy_sq_lower hcL (by omega : 1 ≤ k) hAik
    have hukk : airyZero (k + 1) ≤ u := by
      have : airyZero (k + 1) ≤ airyZero (n + 1) := airyZero_le_of_le (by omega) (by omega)
      linarith
    have hgeo := geo_ratio huF hd hlow huuF (by omega : 1 ≤ k) hukk
    have hden1 : 0 < (u - airyZero 1) ^ 2 := by
      have := sub_ne_zero.mpr (hne 1 le_rfl); positivity
    have hFu : 0 < uF - u := sub_pos.2 huuF
    have hq1 : 1 ≤ ((k : ℝ) + 1) ^ (2 / 3 : ℝ) := by
      apply Real.one_le_rpow
      · linarith
      · norm_num
    have hkp : 0 ≤ (k : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_nonneg hk0.le _
    have hV0 : 0 ≤ (uF - u) / (u - airyZero 1) ^ 2 := div_nonneg hFu.le hden1.le
    have hmk : m ≤ (k : ℝ) ^ (1 / 3 : ℝ) * epsU k ^ 2 / ((k : ℝ) + 1) ^ (2 / 3 : ℝ) := hm k hk2 hkK
    have hfin := caseB_alg (A := airyAi u ^ 2) (X := (u - airyZero k) ^ 2) (E := epsU k ^ 2)
      (kk := (k : ℝ) ^ (1 / 3 : ℝ)) (c2 := (cL / 2) ^ 2) (eR := eR)
      (T := ‖airyProdTail 1 uSite epsU (u : ℂ)‖) (V := (uF - u) / (u - airyZero 1) ^ 2)
      (m := m) (q := ((k : ℝ) + 1) ^ (2 / 3 : ℝ))
      hukne (sq_nonneg _) hkp (sq_nonneg _) heRpos.le hq1 hAisq hT hgeo hmk
    rw [hW]
    have e : airyAi u ^ 2 * (uF - u) / (u - airyZero 1) ^ 2 =
        airyAi u ^ 2 * ((uF - u) / (u - airyZero 1) ^ 2) := mul_div_assoc _ _ _
    rw [e]
    exact le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hm0) hfin

lemma le_of_right_nbhd {Ψ Φ : ℝ → ℝ} {u t0 : ℝ} (hΨ : ContinuousAt Ψ u) (hΦ : ContinuousAt Φ u)
    (ht0 : 0 < t0) (h : ∀ t : ℝ, 0 < t → t < t0 → Ψ (u + t) ≤ Φ (u + t)) : Ψ u ≤ Φ u := by
  have hshift : Tendsto (fun t : ℝ => u + t) (𝓝[>] (0 : ℝ)) (𝓝 u) := by
    have : Tendsto (fun t : ℝ => u + t) (𝓝 (0 : ℝ)) (𝓝 (u + 0)) :=
      (continuous_const.add continuous_id).tendsto 0
    rw [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun t : ℝ => Ψ (u + t)) (𝓝[>] (0 : ℝ)) (𝓝 (Ψ u)) := hΨ.tendsto.comp hshift
  have h2 : Tendsto (fun t : ℝ => Φ (u + t)) (𝓝[>] (0 : ℝ)) (𝓝 (Φ u)) := hΦ.tendsto.comp hshift
  refine le_of_tendsto_of_tendsto h1 h2 ?_
  filter_upwards [Ioo_mem_nhdsGT ht0] with t ht using h t ht.1 ht.2

/-- **Lower bound for `W_D` on the real line** (`rem:thmU` Step (2)), including the Airy zeros (by continuity). -/
theorem window_lower {C_Z : ℝ} (hCZ : 0 < C_Z) :
    ∃ c : ℝ, 0 < c ∧ ∀ (uSite epsU : ℕ → ℝ) (uF : ℝ), AiryProdTailHypothesis 1 uSite epsU →
      ∀ (M K : ℕ), 1 ≤ K → 2 * K ≤ M → 8 * C_Z ≤ (M : ℝ) ^ 2 →
      (∀ j : ℕ, 2 ≤ j → j ≤ M → uSite j = airyZero j) →
      (∀ j : ℕ, M < j → |airyZero j - uSite j| ≤ C_Z * (j : ℝ) ^ (-(4 / 3 : ℝ))) →
      uF ≤ airyZero 1 → airyZero 1 - uF ≤ airyGap 1 / 8 →
      ∀ u : ℝ, airyZero K ≤ u → u < uF →
        ((airyZero 1 + airyZero 2) / 2 ≤ u →
          c * (uF - u) ≤ ‖airyWindowProd 1 uF uSite epsU (u : ℂ)‖) ∧
        (u ≤ (airyZero 1 + airyZero 2) / 2 → ∀ m : ℝ, 0 ≤ m →
          (∀ k : ℕ, 2 ≤ k → k ≤ K + 1 →
            m ≤ (k : ℝ) ^ (1 / 3 : ℝ) * epsU k ^ 2 / ((k : ℝ) + 1) ^ (2 / 3 : ℝ)) →
          c * m ≤ ‖airyWindowProd 1 uF uSite epsU (u : ℂ)‖) := by
  obtain ⟨c, hc, hoff⟩ := window_lower_off hCZ
  refine ⟨c, hc, fun uSite epsU uF hH M K hK hMK hM hsite hdel huF hd u hKu huuF => ⟨?_, ?_⟩⟩
  · intro hmid
    exact (hoff uSite epsU uF hH M K hK hMK hM hsite hdel huF hd u hKu huuF
      (fun j hj => not_zero_of_mid_le hmid (huuF.trans_le huF) hj)).1 hmid
  · intro hlow m hm0 hm
    by_cases hz : ∀ j : ℕ, 1 ≤ j → u ≠ airyZero j
    · exact (hoff uSite epsU uF hH M K hK hMK hM hsite hdel huF hd u hKu huuF hz).2 hlow m hm0 hm
    · push Not at hz
      obtain ⟨j, hj1, hju⟩ := hz
      have ha12 := airyZero_strictAnti (n := 1) le_rfl
      have ha12' : airyZero (1 + 1) = airyZero 2 := rfl
      have hj2 : 2 ≤ j := by
        by_contra hlt
        have : j = 1 := by omega
        subst this
        rw [hju] at hlow
        have hg : 0 < airyGap 1 := airyGap_pos le_rfl
        have hg1 : airyGap 1 = airyZero 1 - airyZero 2 := rfl
        linarith
      have hajle : airyZero j ≤ airyZero 2 := airyZero_le_of_le (by norm_num) hj2
      have hprev : airyZero j < airyZero (j - 1) := by
        have := airyZero_strictAnti (n := j - 1) (by omega)
        rwa [show j - 1 + 1 = j by omega] at this
      set t0 : ℝ := min (airyZero (j - 1) - airyZero j) (min ((airyZero 1 + airyZero 2) / 2 - airyZero j)
        (uF - airyZero j)) with ht0
      have ht0pos : 0 < t0 := by
        refine lt_min (by linarith) (lt_min (by linarith) (by linarith))
      have hΦ : Continuous (fun v : ℝ => ‖airyWindowProd 1 uF uSite epsU (v : ℂ)‖) :=
        continuous_norm.comp ((airyWindowProd_differentiable 1 le_rfl uF uSite epsU hH).continuous.comp
          Complex.continuous_ofReal)
      have hΨ : ContinuousAt (fun _ : ℝ => c * m) u := continuousAt_const
      refine le_of_right_nbhd hΨ hΦ.continuousAt ht0pos fun t ht1 ht2 => ?_
      have hmin1 : t0 ≤ airyZero (j - 1) - airyZero j := min_le_left _ _
      have hmin2 : t0 ≤ (airyZero 1 + airyZero 2) / 2 - airyZero j := (min_le_right _ _).trans (min_le_left _ _)
      have hmin3 : t0 ≤ uF - airyZero j := (min_le_right _ _).trans (min_le_right _ _)
      have hne' : ∀ i : ℕ, 1 ≤ i → u + t ≠ airyZero i := by
        intro i hi h
        have hAi : airyAi (u + t) = 0 := by rw [h]; exact airyAi_airyZero i
        refine airyAi_ne_zero_of_mem_gap (n := j) (by omega) ?_ hAi
        rw [mem_airyClarkGap]
        exact ⟨by rw [hju]; linarith, Or.inr (by rw [hju]; linarith)⟩
      have hKu' : airyZero K ≤ u + t := by linarith
      have huuF' : u + t < uF := by rw [hju]; linarith
      have hlow' : u + t ≤ (airyZero 1 + airyZero 2) / 2 := by rw [hju]; linarith
      have := (hoff uSite epsU uF hH M K hK hMK hM hsite hdel huF hd (u + t) hKu' huuF' hne').2 hlow' m hm0 hm
      simpa using this

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.window_lower_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms window_lower_off

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.window_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms window_lower

end FormalResearch.ModularBootstrap.Upper.Ramped
