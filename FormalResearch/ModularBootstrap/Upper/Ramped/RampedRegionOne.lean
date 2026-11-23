module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedRegionOneAmp
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedRegionTwo

/-!
# Region I of Lemma U\* for the ramped comb (`rem:thmU`, Step (2))

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma U* (`rem:thmU`), Step (2).  For the ramped comb `D_*` (`rampedComb`)
and `t = c' x²/3`, `ξ_I = ξ_* + c'^{-3/5}`: the test function `g` of the design is positive,
`2 g(t) = (h_0 - ĥ_0)(x) > 0` (`twoG`), for `t_* + 1 ≤ t ≤ t(ξ_I)`, `t_* = c' χ'_1²/3`, uniformly in `d ∈ [0, d_0]`
and in `C_mid ≥ 1`, `M_0 > 0`.

* `regionI_W_lower`: for every `Q > 0` there is `C_I ≥ 1` (depending on `Q` and absolute constants only) with
  `‖W_D(-κ σ(x))‖ ≥ Q c'^{-1/2}` on Region I.  The proof is the elementary cell argument of
  `RampedRegionOneAiry`/`Window`: `K = ⌈2 N_tr⌉ + 1`, `u ≥ a_K` (`airyZero_le_neg_kappa`), the left half of cell 1
  (`regionI_gap`: `u_f - u ≥ c_1 c'^{-1/3}`) and, on the other cells, `k^{1/3} ε_k²/(k+1)^{2/3} ≥ c_ρ η_k²/k`
  with `η_k²/k ≥ C_I²/(3√c')` for `k ≤ 3 N_tr` (`etaSq_div_lower`, `N_tr ≍ c'^{1/10}`);
* `rampedRegionI` (headline): `2g > 0` on Region I, `C_I` chosen first and absolutely;
* `rampedPositive_tstar`: Regions I and II together, `2g > 0` for `t ≥ t_* + 1` at `d = M_0 c'^{-1/3}` (what R8 consumes).

**Order of constants** (compatible with `rampedRegionII`): `C_I` (absolute) → `C_mid` (absolute, `rampedRegionII`) →
`M_0` → threshold `c_0` (depending on `C_I, C_mid, M_0`).  The proof of `regionI_W_lower` uses `C_mid ≥ 1` only
through `η_k² ≥ min(1/16, C_I² min(k, N_tr)/√c')`, which holds for every `C_mid`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb Upper.Design Upper.Holes Upper.Positivity Upper.Hankel
  FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Window

lemma rpow_neg_half_eq {c' : ℝ} (hc' : 0 < c') : c' ^ (-(1 / 2 : ℝ)) = (Real.sqrt c')⁻¹ := by
  rw [Real.sqrt_eq_rpow, Real.rpow_neg hc'.le]

/-- `C_I²/(3√c') ≤ 1/(48 N)` once `16 N C_I² ≤ √c'`, which holds for `N ≤ b c'^{1/10}` and `c'` large. -/
lemma regionI_hBA {c' N b CI : ℝ} (hc'0 : 0 < c') (hN0 : 0 < N) (hNu : N ≤ b * c' ^ (1 / 10 : ℝ))
    (e3 : 16 * b * CI ^ 2 ≤ c' ^ (2 / 5 : ℝ)) : CI ^ 2 / (3 * Real.sqrt c') ≤ 1 / (48 * N) := by
  have hs2 : 0 < Real.sqrt c' := Real.sqrt_pos.2 hc'0
  have hsq : c' ^ (1 / 2 : ℝ) = Real.sqrt c' := (Real.sqrt_eq_rpow c').symm
  have hsplit : c' ^ (1 / 2 : ℝ) = c' ^ (2 / 5 : ℝ) * c' ^ (1 / 10 : ℝ) := by
    rw [← Real.rpow_add hc'0]; norm_num
  have hp10 : 0 < c' ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hc'0 _
  have h1 : 16 * N * CI ^ 2 ≤ Real.sqrt c' := by
    rw [← hsq, hsplit]
    have h2 : 16 * N ≤ 16 * (b * c' ^ (1 / 10 : ℝ)) := by linarith
    calc 16 * N * CI ^ 2 ≤ 16 * (b * c' ^ (1 / 10 : ℝ)) * CI ^ 2 :=
          mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
      _ = (16 * b * CI ^ 2) * c' ^ (1 / 10 : ℝ) := by ring
      _ ≤ c' ^ (2 / 5 : ℝ) * c' ^ (1 / 10 : ℝ) := mul_le_mul_of_nonneg_right e3 hp10.le
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [h1]

/-- `m = c_ρ C_I²/(3√c')` is below `k^{1/3} (κ ε̂_k)²/(k+1)^{2/3}` for `2 ≤ k ≤ K + 1`, `K ≤ 2 N_tr + 2`. -/
lemma regionI_hmk (P : RampedParams) {c' : ℝ} (hc'0 : 0 < c') {N : ℝ} (hNn : N = nTr c') (hN3 : 3 ≤ N)
    {K : ℕ} (hKup : (K : ℝ) ≤ 2 * N + 2) {cρ CI : ℝ} (hcρ : 0 < cρ)
    (hρ : ∀ (η : ℝ) (k : ℕ), 1 ≤ k →
      cρ * η ^ 2 / k ≤ (k : ℝ) ^ (1 / 3 : ℝ) *
        (kappaAiry * (η * (phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ)))) ^ 2 / ((k : ℝ) + 1) ^ (2 / 3 : ℝ))
    (hP : P.CI = CI) (hBA : CI ^ 2 / (3 * Real.sqrt c') ≤ 1 / (48 * N)) :
    ∀ k : ℕ, 2 ≤ k → k ≤ K + 1 →
      cρ * CI ^ 2 / (3 * Real.sqrt c') ≤
        (k : ℝ) ^ (1 / 3 : ℝ) * (kappaAiry * epsHat (rampedEta P c') k) ^ 2 / ((k : ℝ) + 1) ^ (2 / 3 : ℝ) := by
  intro k hk2 hkK
  have hk1 : 1 ≤ k := by omega
  have hkN : (k : ℝ) ≤ 3 * N := by
    have : (k : ℝ) ≤ (K : ℝ) + 1 := by exact_mod_cast hkK
    linarith
  have h1 := hρ (rampedEta P c' k) k hk1
  have h2 := etaSq_div_lower P hc'0 hk1 (hNn ▸ hkN) (hNn ▸ (by linarith : 0 < N))
  rw [hP, ← hNn, min_eq_right hBA, ← rampedEta_sq P hc'0 k] at h2
  have h3 : cρ * CI ^ 2 / (3 * Real.sqrt c') ≤ cρ * rampedEta P c' k ^ 2 / k := by
    calc cρ * CI ^ 2 / (3 * Real.sqrt c') = cρ * (CI ^ 2 / (3 * Real.sqrt c')) := by ring
      _ ≤ cρ * (rampedEta P c' k ^ 2 / k) := mul_le_mul_of_nonneg_left h2 hcρ.le
      _ = _ := by ring
  exact h3.trans (by simpa only [epsHat] using h1)

/-- The index `K = ⌈2 N⌉ + 1`: `K ≥ 1`, `2N ≤ K ≤ 2N + 2` and `2K ≤ n_Ai` for `c'` large. -/
lemma regionI_K {c' b N : ℝ} (hc'1 : 1 ≤ c') (hN0 : 0 ≤ N) (hNu : N ≤ b * c' ^ (1 / 10 : ℝ))
    (e2 : 4 * b + 4 ≤ c' ^ (1 / 15 : ℝ)) :
    ∃ K : ℕ, 1 ≤ K ∧ 2 * N ≤ (K : ℝ) ∧ (K : ℝ) ≤ 2 * N + 2 ∧ 2 * K ≤ nAi c' := by
  have hc'0 : 0 < c' := by linarith
  refine ⟨⌈2 * N⌉₊ + 1, by omega, ?_, ?_, ?_⟩
  · have := Nat.le_ceil (2 * N)
    push_cast; linarith
  · have := Nat.ceil_lt_add_one (show 0 ≤ 2 * N by linarith)
    push_cast; linarith
  · have hp10 : 0 < c' ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hc'0 _
    have hsplit : c' ^ (1 / 6 : ℝ) = c' ^ (1 / 15 : ℝ) * c' ^ (1 / 10 : ℝ) := by
      rw [← Real.rpow_add hc'0]; norm_num
    have h1 : 1 ≤ c' ^ (1 / 10 : ℝ) := Real.one_le_rpow hc'1 (by norm_num)
    have hKup : ((⌈2 * N⌉₊ + 1 : ℕ) : ℝ) ≤ 2 * N + 2 := by
      have := Nat.ceil_lt_add_one (show 0 ≤ 2 * N by linarith)
      push_cast; linarith
    have h3 : 2 * ((⌈2 * N⌉₊ + 1 : ℕ) : ℝ) ≤ c' ^ (1 / 6 : ℝ) := by
      rw [hsplit]
      nlinarith [mul_le_mul_of_nonneg_right e2 hp10.le]
    have h4 := nAi_ge (c' := c')
    have : 2 * ((⌈2 * N⌉₊ + 1 : ℕ) : ℝ) ≤ (nAi c' : ℝ) := h3.trans h4
    exact_mod_cast this

/-- Case A of `regionI_W_lower`: the left half of cell 1. -/
lemma regionI_caseA_alg {Q cW c₁ c' : ℝ} (hc'0 : 0 < c') (hcW : 0 < cW) (hc₁ : 0 < c₁)
    (e4 : Q / (cW * c₁) ≤ c' ^ (1 / 6 : ℝ)) :
    Q * c' ^ (-(1 / 2 : ℝ)) ≤ cW * (c₁ * c' ^ (-(1 / 3 : ℝ))) := by
  have hq : Q ≤ cW * c₁ * c' ^ (1 / 6 : ℝ) := by
    have := (div_le_iff₀ (by positivity : 0 < cW * c₁)).1 e4
    linarith
  have hsplit : c' ^ (-(1 / 2 : ℝ)) = c' ^ (-(1 / 3 : ℝ)) * c' ^ (-(1 / 6 : ℝ)) := by
    rw [← Real.rpow_add hc'0]; norm_num
  have hinv : c' ^ (-(1 / 6 : ℝ)) * c' ^ (1 / 6 : ℝ) = 1 := by
    rw [← Real.rpow_add hc'0]; norm_num
  have hp : 0 < c' ^ (-(1 / 6 : ℝ)) := Real.rpow_pos_of_pos hc'0 _
  have hp3 : 0 < c' ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hc'0 _
  have h2 : Q * c' ^ (-(1 / 6 : ℝ)) ≤ cW * c₁ := by
    calc Q * c' ^ (-(1 / 6 : ℝ)) ≤ cW * c₁ * c' ^ (1 / 6 : ℝ) * c' ^ (-(1 / 6 : ℝ)) :=
          mul_le_mul_of_nonneg_right hq hp.le
      _ = cW * c₁ := by rw [mul_assoc, mul_comm (c' ^ (1 / 6 : ℝ)), hinv, mul_one]
  calc Q * c' ^ (-(1 / 2 : ℝ)) = (Q * c' ^ (-(1 / 6 : ℝ))) * c' ^ (-(1 / 3 : ℝ)) := by rw [hsplit]; ring
    _ ≤ (cW * c₁) * c' ^ (-(1 / 3 : ℝ)) := mul_le_mul_of_nonneg_right h2 hp3.le
    _ = cW * (c₁ * c' ^ (-(1 / 3 : ℝ))) := by ring

/-- Case B of `regionI_W_lower`: the constant `C_I`. -/
lemma regionI_caseB_alg {Q cW cρ CI c' : ℝ} (hc'0 : 0 < c') (hCIsq : 3 * Q ≤ cW * cρ * CI ^ 2) :
    Q * c' ^ (-(1 / 2 : ℝ)) ≤ cW * (cρ * CI ^ 2 / (3 * Real.sqrt c')) := by
  have hs2 : 0 < Real.sqrt c' := Real.sqrt_pos.2 hc'0
  rw [rpow_neg_half_eq hc'0]
  have : cW * (cρ * CI ^ 2 / (3 * Real.sqrt c')) = (cW * cρ * CI ^ 2) / 3 * (Real.sqrt c')⁻¹ := by
    field_simp
  rw [this]
  have hinv : 0 ≤ (Real.sqrt c')⁻¹ := inv_nonneg.2 hs2.le
  have : Q ≤ (cW * cρ * CI ^ 2) / 3 := by linarith
  exact mul_le_mul_of_nonneg_right this hinv

/-- **The window `W_D` on Region I is at least `Q c'^{-1/2}`** (`rem:thmU` Step (2)). -/
theorem regionI_W_lower {Q : ℝ} (hQ : 0 < Q) : ∃ CI : ℝ, 1 ≤ CI ∧ ∀ P : RampedParams, P.CI = CI →
    ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ rampedD0 → ∀ x : ℝ, 0 ≤ x →
      c' * designSite c' (rampedSigma d c') 1 ^ 2 / 3 + 1 ≤ c' * x ^ 2 / 3 →
      x ≤ xiStar + c' ^ (-(3 / 5 : ℝ)) →
      Q * c' ^ (-(1 / 2 : ℝ)) ≤ ‖designAiryW (rampedNode d c') (rampedEta P c') (-kappaAiry * sigmaOf c' x)‖ := by
  obtain ⟨cW, hcW, hwin⟩ := ramped_window_lower
  obtain ⟨cρ, hcρ, hρ⟩ := rho_lower
  obtain ⟨c₁, hc₁, hgap⟩ := regionI_gap
  obtain ⟨a, b, ha, hb, hnT⟩ := nTr_bounds
  obtain ⟨CI, hCI1, hCIsq⟩ : ∃ CI : ℝ, 1 ≤ CI ∧ 3 * Q ≤ cW * cρ * CI ^ 2 := by
    refine ⟨max 1 (Real.sqrt (3 * Q / (cW * cρ))), le_max_left _ _, ?_⟩
    have h0 : 0 ≤ 3 * Q / (cW * cρ) := by positivity
    have h1 : 3 * Q / (cW * cρ) ≤ (max 1 (Real.sqrt (3 * Q / (cW * cρ)))) ^ 2 :=
      calc 3 * Q / (cW * cρ) = (Real.sqrt (3 * Q / (cW * cρ))) ^ 2 := (Real.sq_sqrt h0).symm
        _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right _ _) 2
    have := (div_le_iff₀ (by positivity : 0 < cW * cρ)).1 h1
    linarith
  refine ⟨CI, hCI1, fun P hP => ?_⟩
  have ev1 : ∀ᶠ c' : ℝ in atTop, 3 / a ≤ c' ^ (1 / 10 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually_ge_atTop _
  have ev2 : ∀ᶠ c' : ℝ in atTop, 4 * b + 4 ≤ c' ^ (1 / 15 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 15)).eventually_ge_atTop _
  have ev3 : ∀ᶠ c' : ℝ in atTop, 16 * b * CI ^ 2 ≤ c' ^ (2 / 5 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 5)).eventually_ge_atTop _
  have ev4 : ∀ᶠ c' : ℝ in atTop, Q / (cW * c₁) ≤ c' ^ (1 / 6 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).eventually_ge_atTop _
  filter_upwards [hwin, ev1, ev2, ev3, ev4, eventually_ge_atTop (1 : ℝ)]
    with c' hw e1 e2 e3 e4 hc'1
  intro d hd hdD x hx0 ht hxI
  have hc'0 : 0 < c' := by linarith
  obtain ⟨hχ0, hχx, hgapx⟩ := hgap c' hc'1 d hd (hdD.trans rampedD0_le_one) x hx0 ht hxI
  have hσ := regionI_sigma_bounds hc'0 (hχ0.trans hχx.le) hxI
  obtain ⟨hNl, hNu⟩ := hnT c' hc'1
  have hN3 : 3 ≤ nTr c' := by
    have := (div_le_iff₀ ha).1 e1
    linarith
  obtain ⟨K, hK1, hK2N, hKup, h2K⟩ := regionI_K hc'1 (by linarith : 0 ≤ nTr c') hNu e2
  have hKu : airyZero K ≤ -kappaAiry * sigmaOf c' x :=
    airyZero_le_neg_kappa (by linarith : 0 ≤ nTr c') hσ.1 hσ.2 hK1 hK2N
  have hc1pos : 0 < c₁ * c' ^ (-(1 / 3 : ℝ)) := mul_pos hc₁ (Real.rpow_pos_of_pos hc'0 _)
  have huu : -kappaAiry * sigmaOf c' x < airyZero 1 - d := by linarith
  obtain ⟨hwA, hwB⟩ := hw P d hd hdD K hK1 h2K _ hKu huu
  by_cases hmid : (airyZero 1 + airyZero 2) / 2 ≤ -kappaAiry * sigmaOf c' x
  · have h1 : cW * (c₁ * c' ^ (-(1 / 3 : ℝ))) ≤ cW * (airyZero 1 - d - -kappaAiry * sigmaOf c' x) :=
      mul_le_mul_of_nonneg_left hgapx hcW.le
    exact (regionI_caseA_alg hc'0 hcW hc₁ e4).trans (h1.trans (hwA hmid))
  · push Not at hmid
    have hBA := regionI_hBA (CI := CI) hc'0 (by linarith : 0 < nTr c') hNu e3
    have hmk := regionI_hmk P hc'0 (N := nTr c') rfl hN3 hKup hcρ hρ hP hBA
    have hm0 : 0 ≤ cρ * CI ^ 2 / (3 * Real.sqrt c') := by
      have := Real.sqrt_pos.2 hc'0
      positivity
    exact (regionI_caseB_alg hc'0 hCIsq).trans (hwB hmid.le _ hm0 hmk)

/-- **Region I of Lemma U\*** (`rem:thmU`, Step (2)): there is an absolute `C_I ≥ 1` such that for every
`P` with `P.CI = C_I` (any `C_mid ≥ 1`, `M_0 > 0`), for `c'` large, `d ∈ [0, d_0]` and every `x ≥ 0` with
`t_* + 1 ≤ t ≤ t(ξ_I)` (`t = c' x²/3`, `t_* = c' χ'_1²/3`, `ξ_I = ξ_* + c'^{-3/5}`), the test function of the
ramped design is positive: `2 g(c' x²/3) > 0`. -/
theorem rampedRegionI : ∃ CI : ℝ, 1 ≤ CI ∧ ∀ P : RampedParams, P.CI = CI →
    ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ rampedD0 → ∀ x : ℝ, 0 ≤ x →
      c' * designSite c' (rampedSigma d c') 1 ^ 2 / 3 + 1 ≤ c' * x ^ 2 / 3 →
      c' * x ^ 2 / 3 ≤ c' * (xiStar + c' ^ (-(3 / 5 : ℝ))) ^ 2 / 3 →
      0 < twoG c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c') (rampedEps P c') x := by
  obtain ⟨Q, hQ, hmain⟩ := regionI_twoG_of_W
  obtain ⟨CI, hCI, hW⟩ := regionI_W_lower hQ
  obtain ⟨c₁, hc₁, hgap⟩ := regionI_gap
  refine ⟨CI, hCI, fun P hP => ?_⟩
  filter_upwards [hmain P, hW P hP, eventually_ge_atTop (1 : ℝ)] with c' hm hw hc'1
  intro d hd hdD x hx0 ht htI
  have hc'0 : 0 < c' := by linarith
  have hxI : x ≤ xiStar + c' ^ (-(3 / 5 : ℝ)) := by
    have hr : 0 < c' ^ (-(3 / 5 : ℝ)) := Real.rpow_pos_of_pos hc'0 _
    by_contra hcon
    push Not at hcon
    have h1 : (xiStar + c' ^ (-(3 / 5 : ℝ))) ^ 2 < x ^ 2 :=
      pow_lt_pow_left₀ hcon (by linarith [xiStar_pos]) (by norm_num)
    have := mul_lt_mul_of_pos_left h1 hc'0
    linarith
  obtain ⟨_, hχx, _⟩ := hgap c' hc'1 d hd (hdD.trans rampedD0_le_one) x hx0 ht hxI
  exact hm d hd hdD x hχx hxI (hw d hd hdD x hx0 ht hxI)

/-- The shift `d(c) = M_0 c'^{-1/3}` of `D_*` lies in `[0, d_0]` for `c'` large. -/
lemma rampedD_mem (P : RampedParams) : ∀ᶠ c' : ℝ in atTop, 0 ≤ rampedD P c' ∧ rampedD P c' ≤ rampedD0 := by
  filter_upwards [rampedD_le P, eventually_gt_atTop (0 : ℝ)] with c' h hc'
  refine ⟨?_, ?_⟩
  · unfold rampedD
    have := P.M0_pos
    positivity
  · exact h

/-- **`g > 0` for `t ≥ t_* + 1`** (`rem:thmU`, Steps (2)-(4) combined): with `C_I` from `rampedRegionI` and `C_mid`
from `rampedRegionII` (both absolute, `C_I` chosen first), for every `P` with `P.CI = C_I`, `P.Cmid = C_mid` (any
`M_0 > 0`) and `c'` large, `2 g(c' x²/3) > 0` for all `x ≥ 0` with `t ≥ t_*(P, c') + 1`, `d = M_0 c'^{-1/3}`. -/
theorem rampedPositive_tstar : ∃ CI Cmid : ℝ, 1 ≤ CI ∧ 1 ≤ Cmid ∧ ∀ P : RampedParams, P.CI = CI → P.Cmid = Cmid →
    ∀ᶠ c' : ℝ in atTop, ∀ x : ℝ, 0 ≤ x → rampedTstar P c' + 1 ≤ c' * x ^ 2 / 3 →
      0 < twoG c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma (rampedD P c') c') (rampedEps P c') x := by
  obtain ⟨CI, hCI, hI⟩ := rampedRegionI
  obtain ⟨Cmid, hCmid, hII⟩ := rampedRegionII
  refine ⟨CI, Cmid, hCI, hCmid, fun P hP1 hP2 => ?_⟩
  filter_upwards [hI P hP1, hII P hP2, rampedD_mem P, eventually_ge_atTop (1 : ℝ)] with c' h1 h2 hd hc'1
  intro x hx0 ht
  by_cases hx : x ≤ xiStar + c' ^ (-(3 / 5 : ℝ))
  · refine h1 _ hd.1 hd.2 x hx0 ht ?_
    have hr : 0 < c' ^ (-(3 / 5 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
    have h3 : x ^ 2 ≤ (xiStar + c' ^ (-(3 / 5 : ℝ))) ^ 2 := pow_le_pow_left₀ hx0 hx 2
    have := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ c')
    linarith
  · push Not at hx
    exact h2 _ hd.1 (hd.2.trans rampedD0_le_one) x hx.le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.regionI_W_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms regionI_W_lower

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedRegionI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedRegionI

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedPositive_tstar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedPositive_tstar

end FormalResearch.ModularBootstrap.Upper.Ramped
