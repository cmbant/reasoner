module

public import FormalResearch.ModularBootstrap.Upper.Ramped.GapDisc

/-!
# Lemma `P_unif`, growth bound (`rem:profile`, `n2_ramped_comb.tex`)

The profile-uniform version of Lemma G (`ut:G`): for an *admissible profile* (sites `u_k` with
`|u_k - a_k| ≤ C₀ k^{-4/3}`, widths `0 ≤ ε_k ≤ C₀ k^{-1/3}`, `k ≥ 2`) and a first site `u_f` in a
bounded set, the Airy product `W = airyWindowProd f u_f u ε` satisfies
`‖W(u)‖ ≤ C (1 + ‖u‖)^{-(2f - 1/2)} e(u)` with `C = C(C₀, bound of u_f)`: no dependence on `N`, on
the shift `d`, or on the height profile `η_k`.  The proof is that of `airyProdTail_norm_le_of_avoid`
and `airyWindowProd_bound` (Window/Product.lean) with the constants tracked.

* `ProfHyp C₀ u ε`: the admissible profile class.
* `airyProdTail_norm_le_unif`: uniform bound of the tail product off the gap discs.
* `airyWindowProd_bound_unif`: uniform entire-plane growth bound for `W^{(f)}`.
* `pUnif_bound`: the case `f = 1`, `u_f = a_1 - d`, `d ∈ [0, 1]`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Window

/-- **Admissible profile** (`rem:profile`): for `k ≥ 2` the site is within `C₀ k^{-4/3}` of the Airy
zero `a_k` and the width lies in `[0, C₀ k^{-1/3}]`. -/
def ProfHyp (C₀ : ℝ) (uSite epsU : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 2 ≤ k → |uSite k - airyZero k| ≤ C₀ * (k : ℝ) ^ (-(4 / 3 : ℝ)) ∧
    0 ≤ epsU k ∧ epsU k ≤ C₀ * (k : ℝ) ^ (-(1 / 3 : ℝ))

/-- An admissible profile satisfies the tail hypothesis of `airyWindowProd` (Lemma Z for the
WKB comparison). -/
lemma ProfHyp.tailHyp {f : ℕ} (hf : 1 ≤ f) {C₀ : ℝ} (hC₀ : 0 < C₀) {uSite epsU : ℕ → ℝ}
    (hP : ProfHyp C₀ uSite epsU) : AiryProdTailHypothesis f uSite epsU := by
  obtain ⟨C_Z, hC_Z, hZ⟩ := deltaWKB_le_exists
  refine ⟨C₀ + C_Z, by positivity, fun k hk => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hP k (by omega)
  have hk1 : 1 ≤ k := by omega
  have hZk := hZ k hk1
  unfold deltaWKB at hZk
  have hk43 : 0 ≤ (k : ℝ) ^ (-(4 / 3 : ℝ)) := by positivity
  have hk13 : 0 ≤ (k : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
  constructor
  · have : |uSite k - uWKB k| ≤ |uSite k - airyZero k| + |airyZero k - uWKB k| := abs_sub_le _ _ _
    nlinarith
  · rw [abs_of_nonneg h2]
    have : C₀ * (k : ℝ) ^ (-(1 / 3 : ℝ)) ≤ (C₀ + C_Z) * (k : ℝ) ^ (-(1 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) hk13
    linarith

/-- **Uniform bound of the tail product** off the discs: the constant depends only on `C₀` and `c₀`. -/
lemma airyProdTail_norm_le_unif (f : ℕ) (hf : 1 ≤ f) {C0 : ℝ} (hC0 : 0 < C0) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∃ C > 0, ∀ uSite epsU : ℕ → ℝ, ProfHyp C0 uSite epsU → ∀ u : ℂ,
      (∀ k : ℕ, 1 ≤ k → c₀ * airyGap k ≤ ‖u - (airyZero k : ℂ)‖) →
      ‖airyProdTail f uSite epsU u‖ ≤ C := by
  obtain ⟨K_sum, hK_sum, hsum_lem⟩ := airyGap_kernel_sum hc₀
  obtain ⟨c₁, _, hc₁, _, hgap⟩ := airyGap_bounds_exists
  set Z₂ : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2
  have hZ₂ : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa using this
  have hZ₂_nn : 0 ≤ Z₂ := tsum_nonneg fun _ => by positivity
  set M_H := C0 / c₁
  set C_eps := C0 / c₁
  set B := 2 * M_H * √(K_sum * Z₂) + (M_H ^ 2 + C_eps ^ 2) * K_sum
  refine ⟨Real.exp B, Real.exp_pos _, fun uSite epsU hP u hu => ?_⟩
  have hH : AiryProdTailHypothesis f uSite epsU := ProfHyp.tailHyp hf hC0 hP
  have hu_ne : ∀ k : ℕ, f < k → u ≠ (airyZero k : ℂ) := fun k hk h => by
    have := hu k (by omega)
    rw [h, sub_self, norm_zero] at this
    linarith [mul_pos hc₀ (airyGap_pos (by omega : 1 ≤ k))]
  have hp := hasProd_airyProdTail hH hu_ne
  have hnorm_tend : Tendsto (fun s : Finset ℕ => ‖∏ m ∈ s, airyProdFactor uSite epsU (f + 1 + m) u‖)
      atTop (𝓝 ‖airyProdTail f uSite epsU u‖) :=
    continuous_norm.continuousAt.tendsto.comp hp
  obtain ⟨hker_sum, hker_le⟩ := hsum_lem u hu
  refine le_of_tendsto hnorm_tend (Eventually.of_forall fun s => ?_)
  rw [norm_prod]
  have hfac_bd : ∀ m : ℕ,
      ‖airyProdFactor uSite epsU (f + 1 + m) u‖ ≤
        Real.exp (2 * M_H * (airyGap (f + 1 + m) / ‖u - (airyZero (f + 1 + m) : ℂ)‖) *
            (1 / ((f + 1 + m : ℕ) : ℝ)) +
          (M_H ^ 2 + C_eps ^ 2) *
            (airyGap (f + 1 + m) ^ 2 / ‖u - (airyZero (f + 1 + m) : ℂ)‖ ^ 2)) := by
    intro m
    set k := f + 1 + m
    have hk1 : 1 ≤ k := by omega
    have hfk : f < k := by omega
    have hnorm := norm_airyProdFactor_sub_one_le uSite epsU k (hu_ne k hfk)
    have htri : ‖airyProdFactor uSite epsU k u‖ ≤ 1 + ‖airyProdFactor uSite epsU k u - 1‖ := by
      have := norm_add_le (1 : ℂ) (airyProdFactor uSite epsU k u - 1)
      simpa using this
    obtain ⟨h_u, h_nn, h_e⟩ := hP k (by omega)
    have hgap_k := (hgap k hk1).1
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk1
    have hk_rpow : (k : ℝ) ^ (-(4 / 3 : ℝ)) = (k : ℝ) ^ (-(1 / 3 : ℝ)) / k := by
      conv_rhs => rw [div_eq_mul_inv, ← Real.rpow_neg_one (k : ℝ)]
      rw [← Real.rpow_add hk_pos]; congr 2; norm_num
    have h_diff : |airyZero k - uSite k| ≤ M_H * airyGap k / k := by
      have h1 : |airyZero k - uSite k| ≤ C0 * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
        rw [abs_sub_comm]; exact h_u
      rw [hk_rpow] at h1
      calc |airyZero k - uSite k| ≤ C0 * ((k : ℝ) ^ (-(1 / 3 : ℝ)) / k) := h1
        _ = M_H * (c₁ * (k : ℝ) ^ (-(1 / 3 : ℝ))) / k := by dsimp [M_H]; field_simp [hc₁.ne']
        _ ≤ M_H * airyGap k / k := by gcongr
    have h_eps : |epsU k| ≤ C_eps * airyGap k := by
      calc |epsU k| ≤ C0 * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by rw [abs_of_nonneg h_nn]; exact h_e
        _ = C_eps * (c₁ * (k : ℝ) ^ (-(1 / 3 : ℝ))) := by dsimp [C_eps]; field_simp [hc₁.ne']
        _ ≤ C_eps * airyGap k := by gcongr
    have h_abs1 : 2 * |airyZero k - uSite k| / ‖u - (airyZero k : ℂ)‖ ≤
        2 * M_H * (airyGap k / ‖u - (airyZero k : ℂ)‖) * (1 / (k : ℝ)) := by
      calc 2 * |airyZero k - uSite k| / ‖u - (airyZero k : ℂ)‖
          ≤ 2 * (M_H * airyGap k / k) / ‖u - (airyZero k : ℂ)‖ := by gcongr
        _ = 2 * M_H * (airyGap k / ‖u - (airyZero k : ℂ)‖) * (1 / (k : ℝ)) := by ring
    have h_abs2 : (|airyZero k - uSite k| ^ 2 + |epsU k| ^ 2) / ‖u - (airyZero k : ℂ)‖ ^ 2 ≤
        (M_H ^ 2 + C_eps ^ 2) * (airyGap k ^ 2 / ‖u - (airyZero k : ℂ)‖ ^ 2) := by
      have hk_ge1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      have h_diff2 : |airyZero k - uSite k| ≤ M_H * airyGap k := by
        calc |airyZero k - uSite k| ≤ M_H * airyGap k / k := h_diff
          _ ≤ M_H * airyGap k / 1 := by gcongr; exact mul_nonneg (by positivity) (airyGap_pos hk1).le
          _ = M_H * airyGap k := div_one _
      have hs1 := pow_le_pow_left₀ (abs_nonneg _) h_diff2 2
      have hs2 := pow_le_pow_left₀ (abs_nonneg _) h_eps 2
      rw [mul_pow] at hs1 hs2
      calc (|airyZero k - uSite k| ^ 2 + |epsU k| ^ 2) / ‖u - (airyZero k : ℂ)‖ ^ 2
          ≤ ((M_H * airyGap k) ^ 2 + (C_eps * airyGap k) ^ 2) / ‖u - (airyZero k : ℂ)‖ ^ 2 := by gcongr
        _ = (M_H ^ 2 + C_eps ^ 2) * (airyGap k ^ 2 / ‖u - (airyZero k : ℂ)‖ ^ 2) := by ring
    exact (htri.trans (by linarith [hnorm, h_abs1, h_abs2])).trans (Real.add_one_le_exp _)
  have hprod_le : ∏ m ∈ s, ‖airyProdFactor uSite epsU (f + 1 + m) u‖ ≤
      Real.exp (∑ m ∈ s, (2 * M_H * (airyGap (f + 1 + m) / ‖u - (airyZero (f + 1 + m) : ℂ)‖) *
          (1 / ((f + 1 + m : ℕ) : ℝ)) +
        (M_H ^ 2 + C_eps ^ 2) * (airyGap (f + 1 + m) ^ 2 / ‖u - (airyZero (f + 1 + m) : ℂ)‖ ^ 2))) := by
    calc ∏ m ∈ s, ‖airyProdFactor uSite epsU (f + 1 + m) u‖
        ≤ ∏ m ∈ s, Real.exp _ := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun m _ => hfac_bd m)
      _ = Real.exp _ := (Real.exp_sum s _).symm
  refine hprod_le.trans (Real.exp_le_exp.mpr ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  set S_ker := ∑ m ∈ s, airyGap (f + 1 + m) ^ 2 / ‖u - (airyZero (f + 1 + m) : ℂ)‖ ^ 2
  have hS_ker_le : S_ker ≤ K_sum := by
    have hinj : Set.InjOn (fun m : ℕ => f + m) s := fun a _ b _ h => Nat.add_left_cancel h
    have hsub_sum : S_ker = ∑ j ∈ s.image (fun m => f + m),
        airyGap (j + 1) ^ 2 / ‖u - (airyZero (j + 1) : ℂ)‖ ^ 2 := by
      dsimp [S_ker]; rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun m _ => by
        rw [show f + m + 1 = f + 1 + m by ring]
    rw [hsub_sum]
    exact (hker_sum.sum_le_tsum _ fun _ _ => by positivity).trans hker_le
  have hS_inv_le : ∑ m ∈ s, (1 / ((f + 1 + m : ℕ) : ℝ)) ^ 2 ≤ Z₂ := by
    have hinj : Set.InjOn (fun m : ℕ => f + m) s := fun a _ b _ h => Nat.add_left_cancel h
    have hsub_sum : ∑ m ∈ s, (1 / ((f + 1 + m : ℕ) : ℝ)) ^ 2 =
        ∑ j ∈ s.image (fun m => f + m), 1 / ((j : ℝ) + 1) ^ 2 := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun m _ => by push_cast; rw [one_div, one_div, inv_pow]; congr 1; ring
    rw [hsub_sum]
    exact hZ₂.sum_le_tsum _ fun _ _ => by positivity
  have hcs : ∑ m ∈ s, 2 * M_H * (airyGap (f + 1 + m) / ‖u - (airyZero (f + 1 + m) : ℂ)‖) *
      (1 / ((f + 1 + m : ℕ) : ℝ)) ≤ 2 * M_H * √(K_sum * Z₂) := by
    have h1 : ∑ m ∈ s, 2 * M_H * (airyGap (f + 1 + m) / ‖u - (airyZero (f + 1 + m) : ℂ)‖) *
        (1 / ((f + 1 + m : ℕ) : ℝ)) =
        2 * M_H * ∑ m ∈ s, (airyGap (f + 1 + m) / ‖u - (airyZero (f + 1 + m) : ℂ)‖) *
          (1 / ((f + 1 + m : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
    rw [h1]
    have hcs0 := Finset.sum_mul_sq_le_sq_mul_sq s
      (fun m => airyGap (f + 1 + m) / ‖u - (airyZero (f + 1 + m) : ℂ)‖)
      (fun m => 1 / ((f + 1 + m : ℕ) : ℝ))
    have hsq_ker : ∑ m ∈ s, (airyGap (f + 1 + m) / ‖u - (airyZero (f + 1 + m) : ℂ)‖) ^ 2 = S_ker := by
      refine Finset.sum_congr rfl fun m _ => by rw [div_pow]
    rw [hsq_ker] at hcs0
    have hsqrt := Real.sqrt_le_sqrt hcs0
    have hnn : 0 ≤ ∑ m ∈ s, (airyGap (f + 1 + m) / ‖u - (airyZero (f + 1 + m) : ℂ)‖) *
        (1 / ((f + 1 + m : ℕ) : ℝ)) :=
      Finset.sum_nonneg fun m _ => mul_nonneg (div_nonneg (airyGap_pos (by omega)).le (norm_nonneg _)) (by positivity)
    rw [Real.sqrt_sq hnn] at hsqrt
    have hprod_le2 : S_ker * ∑ m ∈ s, (1 / ((f + 1 + m : ℕ) : ℝ)) ^ 2 ≤ K_sum * Z₂ :=
      mul_le_mul hS_ker_le hS_inv_le (Finset.sum_nonneg fun _ _ => by positivity) hK_sum.le
    exact mul_le_mul_of_nonneg_left (hsqrt.trans (Real.sqrt_le_sqrt hprod_le2)) (by positivity)
  have h2 : (M_H ^ 2 + C_eps ^ 2) * S_ker ≤ (M_H ^ 2 + C_eps ^ 2) * K_sum :=
    mul_le_mul_of_nonneg_left hS_ker_le (by positivity)
  linarith

/-- **Lemma `P_unif`, growth bound, general `f`.**  Uniformly over the admissible profiles
`ProfHyp C₀` and the first sites `|u_f| ≤ U`:
`‖W^{(f)}(u)‖ ≤ C (1 + ‖u‖)^{-(2f - 1/2)} e(u)` for all `u ∈ ℂ`. -/
theorem airyWindowProd_bound_unif (f : ℕ) (hf : 1 ≤ f) {C0 : ℝ} (hC0 : 0 < C0) {U : ℝ} (hU : 0 ≤ U) :
    ∃ C > 0, ∀ uF : ℝ, |uF| ≤ U → ∀ uSite epsU : ℕ → ℝ, ProfHyp C0 uSite epsU → ∀ u : ℂ,
      ‖airyWindowProd f uF uSite epsU u‖ ≤
        C * (1 + ‖u‖) ^ (-((2 * (f : ℝ) - 1 / 2))) * airyEnv u := by
  obtain ⟨C_tail, hC_tail, htail_bd⟩ :=
    airyProdTail_norm_le_unif f hf hC0 (c₀ := 1 / 4) (by norm_num)
  obtain ⟨C_rat, hC_rat, hrat_bd⟩ := ratio_prefix_bound_unif f hU (c₀ := 1 / 4) (by norm_num)
  obtain ⟨C_env, hC_env, hext⟩ := norm_le_of_gap_disc_extension
  set C_out := 9 * C_rat * C_tail
  have hC_out : 0 < C_out := by positivity
  have hν : 0 ≤ 2 * (f : ℝ) - 1 / 2 := by
    have : (1 : ℝ) ≤ f := by exact_mod_cast hf
    linarith
  refine ⟨(3 : ℝ) ^ (2 * (f : ℝ) - 1 / 2) * C_env * C_out, by positivity,
    fun uF huF uSite epsU hP => ?_⟩
  have hH : AiryProdTailHypothesis f uSite epsU := ProfHyp.tailHyp hf hC0 hP
  have h_out : ∀ u : ℂ, (∀ k : ℕ, 1 ≤ k → airyGap k / 4 ≤ ‖u - (airyZero k : ℂ)‖) →
      ‖airyWindowProd f uF uSite epsU u‖ ≤
        C_out * (1 + ‖u‖) ^ (-((2 * (f : ℝ) - 1 / 2))) * airyEnv u := by
    intro u hu
    have hu' : ∀ k : ℕ, 1 ≤ k → (1 / 4 : ℝ) * airyGap k ≤ ‖u - (airyZero k : ℂ)‖ := fun k hk => by
      linarith [hu k hk]
    have hu_ne : ∀ k : ℕ, 1 ≤ k → u ≠ (airyZero k : ℂ) := fun k hk h => by
      have := hu k hk
      rw [h, sub_self, norm_zero] at this
      linarith [airyGap_pos hk]
    rw [airyWindowProd_eq_of_ne f uF uSite epsU hu_ne]
    have hai := airyAiC_norm_sq_le u
    have hrat := hrat_bd uF huF u hu'
    have htail := htail_bd uSite epsU hP u hu'
    have h1u : 0 < 1 + ‖u‖ := by positivity
    have henv_nn : 0 ≤ airyEnv u := (airyEnv_pos u).le
    have h_eq : -airyAiC u ^ 2 * (u - (uF : ℂ)) /
        (∏ k ∈ Finset.Icc 1 f, (u - (airyZero k : ℂ)) ^ 2) * airyProdTail f uSite epsU u =
        (-airyAiC u ^ 2) * ((u - (uF : ℂ)) / ∏ k ∈ Finset.Icc 1 f, (u - (airyZero k : ℂ)) ^ 2) *
          airyProdTail f uSite epsU u := by ring
    rw [h_eq, norm_mul, norm_mul, norm_neg, norm_pow]
    have hrpow : (1 + ‖u‖) ^ (-(1 / 2 : ℝ)) * (1 + ‖u‖) ^ (1 - 2 * (f : ℝ)) =
        (1 + ‖u‖) ^ (-((2 * (f : ℝ) - 1 / 2))) := by
      rw [← Real.rpow_add h1u]
      congr 1; ring
    calc ‖airyAiC u‖ ^ 2 * ‖(u - (uF : ℂ)) / ∏ k ∈ Finset.Icc 1 f, (u - (airyZero k : ℂ)) ^ 2‖ *
          ‖airyProdTail f uSite epsU u‖
        ≤ (9 * (1 + ‖u‖) ^ (-(1 / 2 : ℝ)) * airyEnv u) *
            (C_rat * (1 + ‖u‖) ^ (1 - 2 * (f : ℝ))) * C_tail := by
          gcongr
      _ = C_out * ((1 + ‖u‖) ^ (-(1 / 2 : ℝ)) * (1 + ‖u‖) ^ (1 - 2 * (f : ℝ))) * airyEnv u := by
          dsimp [C_out]; ring
      _ = C_out * (1 + ‖u‖) ^ (-((2 * (f : ℝ) - 1 / 2))) * airyEnv u := by rw [hrpow]
  exact hext hν (airyWindowProd_differentiable f hf uF uSite epsU hH) hC_out.le h_out

/-- **Lemma `P_unif` (`rem:profile`), growth bound** for the `f = 1` product with first site
`a_1 - d`, `d ∈ [0, 1]`: uniformly over admissible profiles and shifts,
`‖W(u)‖ ≤ C (1 + ‖u‖)^{-3/2} e(u)`. -/
theorem pUnif_bound {C0 : ℝ} (hC0 : 0 < C0) :
    ∃ C > 0, ∀ d : ℝ, 0 ≤ d → d ≤ 1 → ∀ uSite epsU : ℕ → ℝ, ProfHyp C0 uSite epsU → ∀ u : ℂ,
      ‖airyWindowProd 1 (airyZero 1 - d) uSite epsU u‖ ≤
        C * (1 + ‖u‖) ^ (-(3 / 2 : ℝ)) * airyEnv u := by
  obtain ⟨C, hC, hbd⟩ := airyWindowProd_bound_unif 1 le_rfl hC0 (U := |airyZero 1| + 1) (by positivity)
  refine ⟨C, hC, fun d hd0 hd1 uSite epsU hP u => ?_⟩
  have hF : |airyZero 1 - d| ≤ |airyZero 1| + 1 :=
    (abs_sub _ _).trans (by rw [abs_of_nonneg hd0]; linarith)
  have hu := hbd (airyZero 1 - d) hF uSite epsU hP u
  rw [show -((2 * ((1 : ℕ) : ℝ) - 1 / 2)) = -(3 / 2 : ℝ) by norm_num] at hu
  exact hu

end FormalResearch.ModularBootstrap.Upper.Ramped
