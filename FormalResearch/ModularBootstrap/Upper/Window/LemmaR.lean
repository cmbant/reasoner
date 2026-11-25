module

public import FormalResearch.ModularBootstrap.Upper.Window.AiryProdPositive
public import FormalResearch.ModularBootstrap.Upper.Window.DesignBridge
public import FormalResearch.ModularBootstrap.Upper.Window.Identification
public import FormalResearch.ModularBootstrap.Upper.Window.TailGeometry
public import FormalResearch.ModularBootstrap.Upper.Positivity.DesignReal

/-!
# Lemma R (`ut:R`): compactness of the Airy window at the tip, division by `σ - σ_f`

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, Lemma R (`ut:R`).  For a finite modification
`B_D^{(f)}` of the reference comb with simple zero at `χ'_f = ξ_* + λ σ_f` and `h₀ = sech²(πb/2) B_D^{(f)}`:
on `[σ_f, Σ₀]`, `h₀(x) e^{c' L(x)} = K̃_c^{(f)} (σ - σ_f) w_c(σ)` with `w_c → w_∞` uniformly and
`w_∞ ≥ w₀ > 0`.

* `windowRegular f σf σSeq εHat σ = W̃^{±(f)}(σ)/(σ - σ_f)` (`w_∞`), defined through the window limit
  with the zero moved to `σ_f - 1` (`W̃(σ; σ_f - 1)·(σ - σ_f + 1)^{-1}`), which is the same function
  where `σ ≠ σ_f` and makes the division before the limit explicit (`tildeW_eq_mul_windowRegular`).
* `tildeW_pos`, `tildeW_neg`, `tildeW_eq_zero_iff`, `windowRegular_pos`: **the Airy product has exactly one
  real zero, simple, at `σ_f`**; `W̃ > 0` on the band `σ > σ_f` and `W̃ < 0` on the lobe `σ < σ_f`
  (under `ε̂_k ≠ 0` for `k > f`), via Lemma ID and `airyWindowProd_eq_neg_mul_pos`.
* `windowRegular_lower`: `w_∞ ≥ w₀ > 0` on `[σ_f - 1/2, Σ₀]`.
* `lemma_R`: the uniform convergence `w_c → w_∞` on `σ_f(c') < σ ≤ Σ₀`, proved with the division done
  before the limit: `T_{χ'_f}(x)` is compared with `T_{χ'_f - λ}(x)` through the exact identity
  `h₀^{σ_f} T_{χ'_f - λ} = h₀^{σ_f - 1} T_{χ'_f}` of real `tanh` products, and `lemma_W_comb` is applied to
  the family with zero moved by `-1`.
* `lemma_R_lower`: for large `c'`, `h₀ e^{c'L} ≥ K̃_c^{(f)} w₀ (σ - σ_f(c'))/2` on `σ_f(c') < σ ≤ Σ₀`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Window

open FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Positivity
  FormalResearch.ModularBootstrap.Upper.Window.Tail

/-! ### `tanh` estimates -/

/-- `sinh z ≤ z cosh z` for `z ≥ 0`. -/
lemma sinh_le_mul_cosh {z : ℝ} (hz : 0 ≤ z) : sinh z ≤ z * cosh z := by
  have hmono : MonotoneOn (fun t : ℝ => t * cosh t - sinh t) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (continuous_id.mul Real.continuous_cosh |>.sub Real.continuous_sinh).continuousOn
    · exact ((differentiable_id.mul Real.differentiable_cosh).sub
        Real.differentiable_sinh).differentiableOn
    · intro t ht
      rw [interior_Ici] at ht
      have hd : HasDerivAt (fun t : ℝ => t * cosh t - sinh t)
          (1 * cosh t + t * sinh t - cosh t) t :=
        ((hasDerivAt_id' t).mul (Real.hasDerivAt_cosh t)).sub (Real.hasDerivAt_sinh t)
      rw [hd.deriv, show 1 * cosh t + t * sinh t - cosh t = t * sinh t by ring]
      exact mul_nonneg ht.out.le (Real.sinh_nonneg_iff.mpr ht.out.le)
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hz) hz
  change 0 * cosh 0 - sinh 0 ≤ z * cosh z - sinh z at this
  simp only [Real.cosh_zero, Real.sinh_zero, zero_mul, sub_zero] at this
  linarith

lemma tanh_le_self' {z : ℝ} (hz : 0 ≤ z) : tanh z ≤ z := by
  rw [Real.tanh_eq_sinh_div_cosh, div_le_iff₀ (Real.cosh_pos z)]
  exact sinh_le_mul_cosh hz

/-- `tanh y - tanh z ≤ y - z` for `0 ≤ z ≤ y`. -/
lemma tanh_sub_le' {y z : ℝ} (hz : 0 ≤ z) (hzy : z ≤ y) : tanh y - tanh z ≤ y - z := by
  have hy : 0 ≤ y := hz.trans hzy
  have hch := Real.cosh_pos y
  have hcz := Real.cosh_pos z
  have hd : tanh y - tanh z = sinh (y - z) / (cosh y * cosh z) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, Real.sinh_sub]
    field_simp
  have hc2 : cosh (y - z) ≤ cosh y * cosh z := by
    rw [Real.cosh_sub]
    have := mul_nonneg (Real.sinh_nonneg_iff.mpr hy) (Real.sinh_nonneg_iff.mpr hz)
    linarith
  have hs : 0 ≤ sinh (y - z) := Real.sinh_nonneg_iff.mpr (sub_nonneg.mpr hzy)
  rw [hd]
  calc sinh (y - z) / (cosh y * cosh z) ≤ sinh (y - z) / cosh (y - z) :=
        div_le_div_of_nonneg_left hs (Real.cosh_pos _) hc2
    _ = tanh (y - z) := (Real.tanh_eq_sinh_div_cosh _).symm
    _ ≤ y - z := tanh_le_self' (sub_nonneg.mpr hzy)

/-- The two-sided estimate of the ratio of `tanh` products: with `δ = cosh(a(S+1))(1 + a/t₀) - 1`,
`|ρ - 1/(s+1)| ≤ δ/(s+1)` for `ρ = tanh(a s) tanh(y₂ + a) / (s tanh(a(s+1)) tanh y₂)`. -/
lemma tanh_ratio_close {a s S y₂ t₀ : ℝ} (ha : 0 < a) (hs : 0 < s) (hsS : s ≤ S) (ht₀ : 0 < t₀)
    (hy₂ : t₀ ≤ tanh y₂) (hy₂0 : 0 < y₂) :
    |tanh (a * s) * tanh (y₂ + a) / (s * (tanh (a * (s + 1)) * tanh y₂)) - 1 / (s + 1)| ≤
      (cosh (a * (S + 1)) * (1 + a / t₀) - 1) / (s + 1) := by
  set ch := cosh (a * (S + 1)) with hch
  have hch1 : 1 ≤ ch := Real.one_le_cosh _
  have hs1 : 0 < s + 1 := by linarith
  have hz1 : 0 ≤ a * s := by positivity
  have hz2 : 0 ≤ a * (s + 1) := by positivity
  have hz1' : a * s ≤ a * (S + 1) := by nlinarith
  have hz2' : a * (s + 1) ≤ a * (S + 1) := by nlinarith
  have t1l := tanh_ge_div_cosh hz1 hz1'
  have t2l := tanh_ge_div_cosh hz2 hz2'
  have t1u := tanh_le_self' hz1
  have t2u := tanh_le_self' hz2
  have t2pos : 0 < tanh (a * (s + 1)) := lt_of_lt_of_le (by positivity) t2l
  have t1pos : 0 < tanh (a * s) := lt_of_lt_of_le (by positivity) t1l
  have hty : 0 < tanh y₂ := lt_of_lt_of_le ht₀ hy₂
  have hty1 : tanh y₂ ≤ tanh (y₂ + a) := tanh_mono_real (by linarith)
  have hty2 : tanh (y₂ + a) - tanh y₂ ≤ a := by
    have := tanh_sub_le' (y := y₂ + a) (z := y₂) hy₂0.le (by linarith)
    linarith
  have hBlo : 1 ≤ tanh (y₂ + a) / tanh y₂ := by rw [le_div_iff₀ hty]; linarith
  have hBhi : tanh (y₂ + a) / tanh y₂ ≤ 1 + a / t₀ := by
    rw [div_le_iff₀ hty]
    have h1 : a / t₀ * tanh y₂ ≥ a / t₀ * t₀ := mul_le_mul_of_nonneg_left hy₂ (by positivity)
    have h2 : a / t₀ * t₀ = a := by field_simp
    nlinarith
  have hAlo : 1 / (ch * (s + 1)) ≤ tanh (a * s) / (s * tanh (a * (s + 1))) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e1 : a * s / ch ≤ tanh (a * s) := t1l
    have e2 : tanh (a * (s + 1)) ≤ a * (s + 1) := t2u
    rw [div_le_iff₀ (by positivity)] at e1
    calc 1 * (s * tanh (a * (s + 1))) = s * tanh (a * (s + 1)) := one_mul _
      _ ≤ s * (a * (s + 1)) := mul_le_mul_of_nonneg_left e2 hs.le
      _ = (a * s) * (s + 1) := by ring
      _ ≤ (tanh (a * s) * ch) * (s + 1) := mul_le_mul_of_nonneg_right e1 hs1.le
      _ = tanh (a * s) * (ch * (s + 1)) := by ring
  have hAhi : tanh (a * s) / (s * tanh (a * (s + 1))) ≤ ch / (s + 1) := by
    rw [div_le_div_iff₀ (by positivity) hs1]
    have e2 : a * (s + 1) / ch ≤ tanh (a * (s + 1)) := t2l
    rw [div_le_iff₀ (by positivity)] at e2
    calc tanh (a * s) * (s + 1) ≤ (a * s) * (s + 1) := mul_le_mul_of_nonneg_right t1u hs1.le
      _ = s * (a * (s + 1)) := by ring
      _ ≤ s * (tanh (a * (s + 1)) * ch) := mul_le_mul_of_nonneg_left e2 hs.le
      _ = ch * (s * tanh (a * (s + 1))) := by ring
  have hrho : tanh (a * s) * tanh (y₂ + a) / (s * (tanh (a * (s + 1)) * tanh y₂)) =
      (tanh (a * s) / (s * tanh (a * (s + 1)))) * (tanh (y₂ + a) / tanh y₂) := by
    field_simp
  rw [hrho]
  set A := tanh (a * s) / (s * tanh (a * (s + 1)))
  set B := tanh (y₂ + a) / tanh y₂
  have hA0 : 0 ≤ A := by positivity
  have hup : A * B ≤ ch * (1 + a / t₀) / (s + 1) := by
    calc A * B ≤ (ch / (s + 1)) * (1 + a / t₀) :=
          mul_le_mul hAhi hBhi (by linarith) (by positivity)
      _ = _ := by ring
  have hlo : 1 / (ch * (s + 1)) ≤ A * B := by
    calc 1 / (ch * (s + 1)) ≤ A := hAlo
      _ = A * 1 := (mul_one A).symm
      _ ≤ A * B := mul_le_mul_of_nonneg_left hBlo hA0
  have hδ : ch - 1 ≤ ch * (1 + a / t₀) - 1 := by
    have : 0 ≤ ch * (a / t₀) := by positivity
    nlinarith
  have key1 : (2 - ch) / (s + 1) ≤ 1 / (ch * (s + 1)) := by
    rw [div_le_div_iff₀ hs1 (by positivity)]
    nlinarith [sq_nonneg (ch - 1)]
  rw [abs_le]
  constructor
  · have h1 : (2 - ch) / (s + 1) ≤ A * B := key1.trans hlo
    have h2 : -((ch * (1 + a / t₀) - 1) / (s + 1)) ≤ (2 - ch) / (s + 1) - 1 / (s + 1) := by
      rw [← sub_div, ← neg_div]
      exact div_le_div_of_nonneg_right (by linarith) hs1.le
    linarith
  · have : ch * (1 + a / t₀) / (s + 1) - 1 / (s + 1) =
        (ch * (1 + a / t₀) - 1) / (s + 1) := by ring
    linarith

/-! ### The regularised window limit `w_∞` and the sign of `W̃` -/

/-- `w_∞(σ) = W̃^{±(f)}(σ)/(σ - σ_f)` of Lemma R, written as `W̃(σ; σ_f - 1)/(σ - σ_f + 1)`: both are
the same function off `σ_f` (`tildeW_eq_mul_windowRegular`), and the former has no division by `0`. -/
noncomputable def windowRegular (f : ℕ) (σf : ℝ) (σSeq εHat : ℕ → ℝ) (σ : ℝ) : ℝ :=
  tildeW f (σf - 1) σSeq εHat σ / (σ - σf + 1)

section FamilyID

variable {f N : ℕ} (𝒦 : CompactCombFamily f N) {d : ModifiedCombData f N} (hd : d ∈ 𝒦.members)

include hd

lemma family_hyps (σf : ℝ) :
    ∃ M : ℝ, 0 < M ∧ |σf| ≤ M ∧
      (∀ k ∈ Finset.Icc (f + 1) N, |d.allSigmaLim k| ≤ M ∧ |d.allEpsLim k| ≤ M) := by
  obtain ⟨-, hlim⟩ := 𝒦.lim_bounds d hd
  refine ⟨max 𝒦.M |σf| + 1, by positivity, ?_, fun k hk => ?_⟩
  · linarith [le_max_right 𝒦.M |σf|]
  · have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
    simp only [ModifiedCombData.allSigmaLim, ModifiedCombData.allEpsLim, hkN, ↓reduceIte]
    obtain ⟨h1, h2, h3⟩ := hlim k hk
    exact ⟨by linarith [le_max_left 𝒦.M |σf|], by
      rw [abs_of_nonneg h2]; linarith [le_max_left 𝒦.M |σf|]⟩

lemma family_airyHyp :
    AiryProdTailHypothesis f (fun k => -kappaAiry * d.allSigmaLim k)
      (fun k => kappaAiry * d.allEpsLim k) :=
  airyProdTailHypothesis_of_tail 𝒦.hN one_pos
    (d.tail_bound_all (𝒦.eta0_bounds d hd).1 (𝒦.eta0_bounds d hd).2)

/-- `W̃ = C_*^{(f)} κ Re W^{(f)}(-κσ)` (Lemma ID) for a member of a compact family. -/
lemma tildeW_eq_airy (σf σ : ℝ) :
    tildeW f σf d.allSigmaLim d.allEpsLim σ =
      CStarF f * kappaAiry *
        (airyWindowProd f (-kappaAiry * σf) (fun k => -kappaAiry * d.allSigmaLim k)
          (fun k => kappaAiry * d.allEpsLim k) ((-kappaAiry * σ : ℝ) : ℂ)).re := by
  obtain ⟨M, hM, hσf, hmod⟩ := family_hyps 𝒦 hd σf
  exact lemma_ID f N 𝒦.hf 𝒦.hN hM one_pos hσf hmod
    (d.tail_bound_all (𝒦.eta0_bounds d hd).1 (𝒦.eta0_bounds d hd).2) σ

/-- Positive widths of the limit: `ε̂_k^* ≠ 0` for `k > f`. -/
def PosLimitWidths (d : ModifiedCombData f N) : Prop := ∀ k : ℕ, f < k → d.allEpsLim k ≠ 0

lemma tildeW_pos (hε : PosLimitWidths d) {σf σ : ℝ} (hσ : σf < σ) :
    0 < tildeW f σf d.allSigmaLim d.allEpsLim σ := by
  rw [tildeW_eq_airy 𝒦 hd]
  have hκ := kappaAiry_pos
  refine mul_pos (mul_pos (CStarF_pos f) hκ) (airyWindowProd_re_pos _ (family_airyHyp 𝒦 hd)
    (fun k hk => mul_ne_zero hκ.ne' (hε k hk)) ?_)
  nlinarith

lemma tildeW_neg (hε : PosLimitWidths d) {σf σ : ℝ} (hσ : σ < σf) :
    tildeW f σf d.allSigmaLim d.allEpsLim σ < 0 := by
  rw [tildeW_eq_airy 𝒦 hd]
  have hκ := kappaAiry_pos
  have := airyWindowProd_re_neg (-kappaAiry * σf) (family_airyHyp 𝒦 hd)
    (fun k hk => mul_ne_zero hκ.ne' (hε k hk)) (u := -kappaAiry * σ) (by nlinarith)
  have h2 : 0 < CStarF f * kappaAiry := mul_pos (CStarF_pos f) hκ
  nlinarith

lemma tildeW_eq_zero_iff (hε : PosLimitWidths d) (σf σ : ℝ) :
    tildeW f σf d.allSigmaLim d.allEpsLim σ = 0 ↔ σ = σf := by
  have hκ := kappaAiry_pos
  constructor
  · intro h0
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (tildeW_neg 𝒦 hd hε h).ne h0
    · exact (tildeW_pos 𝒦 hd hε h).ne' h0
  · rintro rfl
    rw [tildeW_eq_airy 𝒦 hd]
    have := (airyWindowProd_re_eq_zero_iff (-kappaAiry * σ) (family_airyHyp 𝒦 hd)
      (fun k hk => mul_ne_zero hκ.ne' (hε k hk)) (-kappaAiry * σ)).mpr rfl
    rw [this, mul_zero]

lemma windowRegular_pos (hε : PosLimitWidths d) {σf σ : ℝ} (hσ : σf - 1 < σ) :
    0 < windowRegular f σf d.allSigmaLim d.allEpsLim σ := by
  unfold windowRegular
  exact div_pos (tildeW_pos 𝒦 hd hε hσ) (by linarith)

lemma continuous_tildeW_family (σf : ℝ) :
    Continuous (tildeW f σf d.allSigmaLim d.allEpsLim) := by
  obtain ⟨M, hM, hσf, hmod⟩ := family_hyps 𝒦 hd σf
  exact continuous_tildeW f N 𝒦.hf 𝒦.hN hM one_pos hσf hmod
    (d.tail_bound_all (𝒦.eta0_bounds d hd).1 (𝒦.eta0_bounds d hd).2)

lemma tendsto_windowFiniteProd_family (σf σ : ℝ) :
    Tendsto (fun K : ℕ => windowFiniteProd f σf d.allSigmaLim d.allEpsLim K σ) atTop
      (𝓝 (tildeW f σf d.allSigmaLim d.allEpsLim σ)) := by
  obtain ⟨M, hM, hσf, hmod⟩ := family_hyps 𝒦 hd σf
  obtain ⟨K_min, C, -, -, -, hrate⟩ := tendsto_windowFiniteProd_uniform f N 𝒦.hf 𝒦.hN (M := M)
    (C_t := 1) (S := |σ|) hM one_pos (abs_nonneg _)
  have hr : ∀ {K : ℕ} {σ' : ℝ}, K_min ≤ K → σ' ∈ Icc (-|σ|) |σ| →
      |windowFiniteProd f σf d.allSigmaLim d.allEpsLim K σ' -
        tildeW f σf d.allSigmaLim d.allEpsLim σ'| ≤ C / (K : ℝ) :=
    (hrate hσf hmod (d.tail_bound_all (𝒦.eta0_bounds d hd).1 (𝒦.eta0_bounds d hd).2)).2
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_
    (tendsto_const_div_atTop_nhds_zero_nat C)
  filter_upwards [eventually_ge_atTop K_min] with K hK
  rw [Real.dist_eq]
  exact hr hK ⟨neg_abs_le σ, le_abs_self σ⟩

/-- `W̃(σ) = (σ - σ_f) w_∞(σ)`: the regularised limit is `W̃/(σ - σ_f)`. -/
lemma tildeW_eq_mul_windowRegular {σf σ : ℝ} (hσ : σ ≠ σf - 1) :
    tildeW f σf d.allSigmaLim d.allEpsLim σ =
      (σ - σf) * windowRegular f σf d.allSigmaLim d.allEpsLim σ := by
  have hne : σ - σf + 1 ≠ 0 := fun h => hσ (by linarith)
  have hfun : ∀ K : ℕ, windowFiniteProd f σf d.allSigmaLim d.allEpsLim K σ =
      (σ - σf) / (σ - (σf - 1)) *
        windowFiniteProd f (σf - 1) d.allSigmaLim d.allEpsLim K σ := by
    intro K
    unfold windowFiniteProd
    have : σ - (σf - 1) = σ - σf + 1 := by ring
    rw [this]
    field_simp
  have h1 := tendsto_windowFiniteProd_family 𝒦 hd σf σ
  have h2 := (tendsto_windowFiniteProd_family 𝒦 hd (σf - 1) σ).const_mul ((σ - σf) / (σ - (σf - 1)))
  simp_rw [← hfun] at h2
  rw [tendsto_nhds_unique h1 h2]
  unfold windowRegular
  have : σ - (σf - 1) = σ - σf + 1 := by ring
  rw [this]
  field_simp

/-- `w_∞ ≥ w₀ > 0` on `[σ_f - 1/2, Σ₀]`. -/
lemma windowRegular_lower (hε : PosLimitWidths d) (Sg0 : ℝ) :
    ∃ w0 : ℝ, 0 < w0 ∧ ∀ σ ∈ Icc (d.sigmaFLim - 1 / 2) Sg0,
      w0 ≤ windowRegular f d.sigmaFLim d.allSigmaLim d.allEpsLim σ := by
  have hcont : ContinuousOn (windowRegular f d.sigmaFLim d.allSigmaLim d.allEpsLim)
      (Icc (d.sigmaFLim - 1 / 2) Sg0) := by
    unfold windowRegular
    refine ((continuous_tildeW_family 𝒦 hd (d.sigmaFLim - 1)).continuousOn).div
      (by fun_prop) (fun σ hσ => ?_)
    have := hσ.1
    linarith
  rcases Set.eq_empty_or_nonempty (Icc (d.sigmaFLim - 1 / 2) Sg0) with he | hne
  · exact ⟨1, one_pos, fun σ hσ => by rw [he] at hσ; exact absurd hσ (Set.notMem_empty σ)⟩
  · obtain ⟨σ0, hσ0, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont
    refine ⟨windowRegular f d.sigmaFLim d.allSigmaLim d.allEpsLim σ0,
      windowRegular_pos 𝒦 hd hε (by linarith [hσ0.1]), fun σ hσ => hmin hσ⟩

end FamilyID

/-! ### The comb with the zero factor removed -/

/-- `B_D^{(f)}` without the first factor `T_{χ'_f}`: the product over the modified and reference pairs. -/
noncomputable def modifiedCombRest (f N : ℕ) (d : ModifiedCombData f N) (c' : ℝ) (z : ℂ) : ℂ :=
  (∏ k ∈ Finset.Icc (f + 1) N,
      let χk : ℝ := xiStar + lambdaComb c' * d.sigmaK c' k
      let εk : ℝ := lambdaComb c' * d.epsHat c' k
      blaschkeT ((χk : ℂ) + (εk : ℂ) * Complex.I) z *
        blaschkeT ((χk : ℂ) - (εk : ℂ) * Complex.I) z) *
    (∏' m : ℕ,
      let χm : ℝ := chiQuantile c' (N + 1 + m : ℕ)
      let εm : ℝ := d.eta0 * siteGap c' (N + 1 + m)
      blaschkeT ((χm : ℂ) + (εm : ℂ) * Complex.I) z *
        blaschkeT ((χm : ℂ) - (εm : ℂ) * Complex.I) z)

lemma modifiedCombB_eq_mul_rest (f N : ℕ) (d : ModifiedCombData f N) (c' : ℝ) (z : ℂ) :
    modifiedCombB f N d c' z =
      blaschkeT (((xiStar + lambdaComb c' * d.sigmaF c' : ℝ)) : ℂ) z * modifiedCombRest f N d c' z := by
  unfold modifiedCombB modifiedCombRest
  simp only []
  ring

lemma modifiedCombRest_shiftF (f N : ℕ) (d : ModifiedCombData f N) (δ c' : ℝ) (z : ℂ) :
    modifiedCombRest f N (d.shiftF δ) c' z = modifiedCombRest f N d c' z := rfl

lemma modifiedH0_eq_tanh (f N : ℕ) (d : ModifiedCombData f N) (c' x : ℝ) :
    modifiedH0 f N d c' x = (1 / Real.cosh (π * x / 2) ^ 2) *
      ((Real.tanh (π * (x - (xiStar + lambdaComb c' * d.sigmaF c')) / 2) *
        Real.tanh (π * (x + (xiStar + lambdaComb c' * d.sigmaF c')) / 2)) *
        (modifiedCombRest f N d c' (x : ℂ)).re) := by
  unfold modifiedH0
  rw [modifiedCombB_eq_mul_rest, blaschkeT_ofReal_eq, Complex.re_ofReal_mul]

/-- The algebra of the final estimate. -/
lemma combine_bound {F W B ρ q s s0 ε1 ε2 : ℝ} (hs : 0 ≤ s) (hs0 : 1 / 2 ≤ s0 + 1) (hq : 0 ≤ q)
    (hρ : |ρ - 1 / (s + 1)| ≤ q / (s + 1)) (hF : |F - W| ≤ ε1) (hW : |W| ≤ B)
    (hss : |s0 - s| ≤ ε2) (hε1 : 0 ≤ ε1) :
    |F * ρ - W / (s0 + 1)| ≤ ε1 * (1 + q) + B * q + 2 * B * ε2 := by
  have hs1 : 1 ≤ s + 1 := by linarith
  have hs1p : 0 < s + 1 := by linarith
  have hs0p : 0 < s0 + 1 := by linarith
  have hB : 0 ≤ B := (abs_nonneg W).trans hW
  have hρabs : |ρ| ≤ 1 + q := by
    have h1 := abs_sub_abs_le_abs_sub ρ (1 / (s + 1))
    have h2 : |1 / (s + 1)| ≤ 1 := by
      rw [abs_of_pos (by positivity), div_le_one hs1p]; exact hs1
    have h3 : q / (s + 1) ≤ q := div_le_self hq hs1
    linarith
  have hq1 : |ρ - 1 / (s + 1)| ≤ q := (hρ.trans (div_le_self hq hs1))
  have hd : |1 / (s + 1) - 1 / (s0 + 1)| ≤ 2 * ε2 := by
    have : 1 / (s + 1) - 1 / (s0 + 1) = (s0 - s) / ((s + 1) * (s0 + 1)) := by
      field_simp; ring
    rw [this, abs_div, abs_of_pos (by positivity : 0 < (s + 1) * (s0 + 1))]
    rw [div_le_iff₀ (by positivity)]
    have hε2 : 0 ≤ ε2 := (abs_nonneg _).trans hss
    have hprod : 1 / 2 ≤ (s + 1) * (s0 + 1) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hprod hε2]
  have heq : F * ρ - W / (s0 + 1) = (F - W) * ρ + W * (ρ - 1 / (s + 1)) +
      W * (1 / (s + 1) - 1 / (s0 + 1)) := by ring
  rw [heq]
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [abs_mul]; exact mul_le_mul hF hρabs (abs_nonneg _) hε1
  · rw [abs_mul]; exact mul_le_mul hW hq1 (abs_nonneg _) hB
  · rw [abs_mul]
    calc |W| * |1 / (s + 1) - 1 / (s0 + 1)| ≤ B * (2 * ε2) := mul_le_mul hW hd (abs_nonneg _) hB
      _ = 2 * B * ε2 := by ring

lemma windowNormKTilde_pos (f : ℕ) {c' : ℝ} (hc' : 0 < c') : 0 < windowNormKTilde f c' := by
  unfold windowNormKTilde
  have hlam : 0 < lambdaComb c' := Real.rpow_pos_of_pos (mul_pos kTip_pos hc') _
  positivity

lemma exists_nat_phiWKB_ge (S : ℝ) : ∃ N₁ : ℕ, S ≤ phiWKB (N₁ + 1) := by
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt ((max S 0) ^ (3 / 2 : ℝ))
  refine ⟨N₁, ?_⟩
  have h0 : 0 ≤ max S 0 := le_max_right _ _
  have h1 : (max S 0) ^ (3 / 2 : ℝ) ≤ ((N₁ + 1 : ℕ) : ℝ) - 1 / 4 := by push_cast; linarith
  have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 2 / 3)
  rw [← Real.rpow_mul h0, show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num, Real.rpow_one] at h2
  exact (le_max_left S 0).trans h2

lemma ratio_algebra {A B C D R E K s sech : ℝ} (hC : C ≠ 0) (hD : D ≠ 0) (hs : s ≠ 0) (hK : K ≠ 0) :
    sech * ((A * B) * R) * E / (K * s) = (sech * ((C * D) * R) * E / K) * (A * B / (s * (C * D))) := by
  field_simp

/-- The `tanh` algebra of Lemma R: with the zero moved by `-1`, the ratio
`ρ = T_{χ'_f}(x)/(T_{χ'_f - λ}(x) (σ - σ_f))` satisfies `h₀ e^{c'L}/(K̃ (σ - σ_f)) = F' ρ` where
`F'` is the window quotient of the shifted modification, and `|ρ - 1/(s+1)| ≤ δ/(s+1)`,
`s = σ - σ_f`, `δ = cosh(a(S+1))(1 + a/t₀) - 1`, `a = πλ/2`, `t₀ = tanh(πξ_*/2)`. -/
lemma lemma_R_ratio {f N : ℕ} (d : ModifiedCombData f N) {c' σ Sbar : ℝ} (hc' : 0 < c')
    (hσ : d.sigmaF c' < σ) (hsS : σ - d.sigmaF c' ≤ Sbar)
    (hy : lambdaComb c' * (1 - σ - d.sigmaF c') ≤ xiStar) :
    ∃ ρ : ℝ,
      modifiedH0 f N d c' (xiStar + lambdaComb c' * σ) *
          Real.exp (c' * slitL (xiStar + lambdaComb c' * σ)) /
          (windowNormKTilde f c' * (σ - d.sigmaF c')) =
        (modifiedH0 f N (d.shiftF 1) c' (xiStar + lambdaComb c' * σ) *
          Real.exp (c' * slitL (xiStar + lambdaComb c' * σ)) / windowNormKTilde f c') * ρ ∧
      |ρ - 1 / ((σ - d.sigmaF c') + 1)| ≤
        (Real.cosh (π * lambdaComb c' / 2 * (Sbar + 1)) *
          (1 + (π * lambdaComb c' / 2) / Real.tanh (π * xiStar / 2)) - 1) / ((σ - d.sigmaF c') + 1) := by
  have hlam : 0 < lambdaComb c' := Real.rpow_pos_of_pos (mul_pos kTip_pos hc') _
  have hxi := xiStar_pos
  have hapos : 0 < π * lambdaComb c' / 2 := by positivity
  have hs : 0 < σ - d.sigmaF c' := sub_pos.mpr hσ
  have ht0pos : 0 < Real.tanh (π * xiStar / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by positivity)) (Real.cosh_pos _)
  have hy₂ge : π * xiStar / 2 ≤
      π * ((xiStar + lambdaComb c' * σ) + (xiStar + lambdaComb c' * d.sigmaF c') - lambdaComb c') / 2 := by
    have : xiStar ≤ (xiStar + lambdaComb c' * σ) + (xiStar + lambdaComb c' * d.sigmaF c') - lambdaComb c' := by
      nlinarith
    nlinarith [Real.pi_pos]
  have hy₂pos : 0 < π * ((xiStar + lambdaComb c' * σ) + (xiStar + lambdaComb c' * d.sigmaF c') -
      lambdaComb c') / 2 := lt_of_lt_of_le (by positivity) hy₂ge
  have hty₂ := tanh_mono_real hy₂ge
  have hratio := tanh_ratio_close hapos hs hsS ht0pos hty₂ hy₂pos
  have e1 : π * ((xiStar + lambdaComb c' * σ) - (xiStar + lambdaComb c' * d.sigmaF c')) / 2 =
      π * lambdaComb c' / 2 * (σ - d.sigmaF c') := by ring
  have e2 : π * ((xiStar + lambdaComb c' * σ) + (xiStar + lambdaComb c' * d.sigmaF c')) / 2 =
      π * ((xiStar + lambdaComb c' * σ) + (xiStar + lambdaComb c' * d.sigmaF c') - lambdaComb c') / 2 +
        π * lambdaComb c' / 2 := by ring
  have e3 : π * ((xiStar + lambdaComb c' * σ) - (xiStar + lambdaComb c' * (d.sigmaF c' - 1))) / 2 =
      π * lambdaComb c' / 2 * ((σ - d.sigmaF c') + 1) := by ring
  have e4 : π * ((xiStar + lambdaComb c' * σ) + (xiStar + lambdaComb c' * (d.sigmaF c' - 1))) / 2 =
      π * ((xiStar + lambdaComb c' * σ) + (xiStar + lambdaComb c' * d.sigmaF c') - lambdaComb c') / 2 := by
    ring
  have hH := modifiedH0_eq_tanh f N d c' (xiStar + lambdaComb c' * σ)
  have hH' := modifiedH0_eq_tanh f N (d.shiftF 1) c' (xiStar + lambdaComb c' * σ)
  rw [e1, e2] at hH
  have hsh : (d.shiftF 1).sigmaF c' = d.sigmaF c' - 1 := rfl
  rw [hsh, e3, e4, modifiedCombRest_shiftF] at hH'
  refine ⟨_, ?_, hratio⟩
  have hK := windowNormKTilde_pos f hc'
  have t1 : 0 < Real.tanh (π * lambdaComb c' / 2 * ((σ - d.sigmaF c') + 1)) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by positivity)) (Real.cosh_pos _)
  rw [hH, hH']
  exact ratio_algebra t1.ne' (lt_of_lt_of_le ht0pos hty₂).ne' hs.ne' hK.ne'

/-- **Lemma R (`ut:R`), uniform convergence of `w_c`.**  For a finite modification `d` of a compact
family, `Σ₀ ∈ ℝ`, `ε > 0` and all large `c'`: for every `σ` with `σ_f(c') < σ ≤ Σ₀` (`x = ξ_* + λσ`),
`|h₀(x) e^{c' L(x)} / (K̃_c^{(f)} (σ - σ_f(c'))) - w_∞(σ)| ≤ ε`, where `w_∞ = W̃/(σ - σ_f)`
(`windowRegular`) is continuous and positive (`windowRegular_pos`, `windowRegular_lower`) when the limit
widths are non-zero.  The division by `σ - σ_f` is done before the limit. -/
theorem lemma_R {f N : ℕ} (𝒦 : CompactCombFamily f N) {d : ModifiedCombData f N} (hd : d ∈ 𝒦.members)
    (Sg0 : ℝ) :
    ∀ ε > 0, ∃ C₀ > 0, ∀ {c' : ℝ}, C₀ ≤ c' → ∀ σ : ℝ, d.sigmaF c' < σ → σ ≤ Sg0 →
      |modifiedH0 f N d c' (xiStar + lambdaComb c' * σ) *
          Real.exp (c' * slitL (xiStar + lambdaComb c' * σ)) /
          (windowNormKTilde f c' * (σ - d.sigmaF c')) -
        windowRegular f d.sigmaFLim d.allSigmaLim d.allEpsLim σ| ≤ ε := by
  intro ε hε
  have hd' : d.shiftF 1 ∈ (𝒦.shiftF 1).members := ⟨d, hd, rfl⟩
  have hM0 : 0 < 𝒦.M := 𝒦.hM
  obtain ⟨N₁, hN₁⟩ := exists_nat_phiWKB_ge Sg0
  have hWcont : Continuous (tildeW f (d.shiftF 1).sigmaFLim (d.shiftF 1).allSigmaLim
      (d.shiftF 1).allEpsLim) := continuous_tildeW_family (𝒦.shiftF 1) hd' _
  obtain ⟨B₀, hB₀⟩ := (isCompact_Icc (a := -(𝒦.M + 1)) (b := Sg0)).exists_bound_of_continuousOn
    hWcont.continuousOn
  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ σ ∈ Icc (-(𝒦.M + 1)) Sg0,
      |tildeW f (d.shiftF 1).sigmaFLim (d.shiftF 1).allSigmaLim (d.shiftF 1).allEpsLim σ| ≤ B :=
    ⟨max B₀ 0, le_max_right _ _, fun σ hσ => by
      have := hB₀ σ hσ
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)⟩
  obtain ⟨C1, hC1pos, hC1⟩ := lemma_W_comb (𝒦.shiftF 1) (S := 𝒦.M + 1) (by positivity) N₁
    (ε / 6) (by positivity)
  obtain ⟨ε2, hε2pos, hε2half, hε2B⟩ : ∃ ε2 : ℝ, 0 < ε2 ∧ ε2 ≤ 1 / 2 ∧ ε2 ≤ ε / (6 * (B + 1)) :=
    ⟨min (1 / 2) (ε / (6 * (B + 1))), lt_min (by norm_num) (by positivity), min_le_left _ _,
      min_le_right _ _⟩
  obtain ⟨C2, hC2pos, hC2⟩ := 𝒦.uniform_tendsto hε2pos
  obtain ⟨q0, hq0pos, hq0one, hq0B⟩ : ∃ q0 : ℝ, 0 < q0 ∧ q0 ≤ 1 ∧ q0 ≤ ε / (3 * (B + 1)) :=
    ⟨min 1 (ε / (3 * (B + 1))), lt_min one_pos (by positivity), min_le_left _ _, min_le_right _ _⟩
  have ht0pos : 0 < Real.tanh (π * xiStar / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by have := xiStar_pos; positivity)) (Real.cosh_pos _)
  have hg : Tendsto (fun c' : ℝ => Real.cosh (π * lambdaComb c' / 2 * (Sg0 + 𝒦.M + 1)) *
      (1 + (π * lambdaComb c' / 2) / Real.tanh (π * xiStar / 2)) - 1) atTop (𝓝 0) := by
    have hcont : Continuous (fun l : ℝ => Real.cosh (π * l / 2 * (Sg0 + 𝒦.M + 1)) *
        (1 + (π * l / 2) / Real.tanh (π * xiStar / 2)) - 1) := by fun_prop
    have h0 := hcont.tendsto 0
    simp only [mul_zero, zero_mul, zero_div, Real.cosh_zero, add_zero, mul_one, sub_self] at h0
    exact h0.comp tendsto_lambdaComb_atTop
  have hev : ∀ᶠ c' in atTop, 0 < c' ∧ lambdaComb c' * (𝒦.M + 1 + 𝒦.M + 1) ≤ xiStar ∧
      Real.cosh (π * lambdaComb c' / 2 * (Sg0 + 𝒦.M + 1)) *
        (1 + (π * lambdaComb c' / 2) / Real.tanh (π * xiStar / 2)) - 1 ≤ q0 := by
    refine (eventually_gt_atTop (0 : ℝ)).and ((?_ : ∀ᶠ c' in atTop,
      lambdaComb c' * (𝒦.M + 1 + 𝒦.M + 1) ≤ xiStar).and (hg.eventually_le_const hq0pos))
    have h := tendsto_lambdaComb_atTop.mul_const (𝒦.M + 1 + 𝒦.M + 1)
    rw [zero_mul] at h
    exact h.eventually_le_const xiStar_pos
  obtain ⟨C3, hC3⟩ := eventually_atTop.mp hev
  refine ⟨max (max C1 C2) (max C3 1), lt_of_lt_of_le one_pos ((le_max_right _ _).trans (le_max_right _ _)),
    fun {c'} hc' σ hσ1 hσ2 => ?_⟩
  have hc1 : C1 ≤ c' := (le_max_left _ _).trans ((le_max_left _ _).trans hc')
  have hc2 : C2 ≤ c' := (le_max_right _ _).trans ((le_max_left _ _).trans hc')
  have hc3 : C3 ≤ c' := (le_max_left _ _).trans ((le_max_right _ _).trans hc')
  obtain ⟨hcpos, hlamS, hδq⟩ := hC3 c' hc3
  have hlam : 0 < lambdaComb c' := Real.rpow_pos_of_pos (mul_pos kTip_pos hcpos) _
  obtain ⟨hσfb, -⟩ := 𝒦.finite_bounds d hd hcpos
  have hσfM := abs_le.mp hσfb
  have hsS : σ - d.sigmaF c' ≤ Sg0 + 𝒦.M := by linarith [hσfM.1]
  have hσlow : -(𝒦.M + 1) ≤ σ := by linarith [hσfM.1]
  have hy : lambdaComb c' * (1 - σ - d.sigmaF c') ≤ xiStar := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hlam.le) hlamS
    linarith [hσfM.2]
  obtain ⟨ρ, hid, hρ⟩ := lemma_R_ratio d (Sbar := Sg0 + 𝒦.M) hcpos hσ1 hsS hy
  have hσmem : σ ∈ Icc (-(𝒦.M + 1)) (phiWKB (N₁ + 1)) := ⟨hσlow, hσ2.trans hN₁⟩
  have hF := hC1 hc1 _ hd' σ hσmem
  have hW := hB σ ⟨hσlow, hσ2⟩
  obtain ⟨hf1, -⟩ := hC2 hc2 d hd
  rw [hid]
  have hwreg : windowRegular f d.sigmaFLim d.allSigmaLim d.allEpsLim σ =
      tildeW f (d.shiftF 1).sigmaFLim (d.shiftF 1).allSigmaLim (d.shiftF 1).allEpsLim σ /
        (σ - d.sigmaFLim + 1) := rfl
  rw [hwreg]
  set q : ℝ := Real.cosh (π * lambdaComb c' / 2 * (Sg0 + 𝒦.M + 1)) *
    (1 + (π * lambdaComb c' / 2) / Real.tanh (π * xiStar / 2)) - 1 with hqdef
  have hqpos : 0 ≤ q := by
    have : 0 ≤ (π * lambdaComb c' / 2) / Real.tanh (π * xiStar / 2) := by positivity
    nlinarith [Real.one_le_cosh (π * lambdaComb c' / 2 * (Sg0 + 𝒦.M + 1))]
  have hρ' : |ρ - 1 / ((σ - d.sigmaF c') + 1)| ≤ q / ((σ - d.sigmaF c') + 1) := by
    convert hρ using 4
  have hfinal := combine_bound (F := modifiedH0 f N (d.shiftF 1) c' (xiStar + lambdaComb c' * σ) *
      Real.exp (c' * slitL (xiStar + lambdaComb c' * σ)) / windowNormKTilde f c')
    (W := tildeW f (d.shiftF 1).sigmaFLim (d.shiftF 1).allSigmaLim (d.shiftF 1).allEpsLim σ)
    (B := B) (ρ := ρ) (q := q) (s := σ - d.sigmaF c') (s0 := σ - d.sigmaFLim) (ε1 := ε / 6)
    (ε2 := ε2) (sub_pos.mpr hσ1).le
    (by
      have : σ - d.sigmaFLim + 1 = ((σ - d.sigmaF c') + 1) + (d.sigmaF c' - d.sigmaFLim) := by ring
      rw [this]
      have := (abs_le.mp hf1).1
      have hsp := (sub_pos.mpr hσ1).le
      linarith)
    hqpos hρ' hF hW
    (by
      have : σ - d.sigmaFLim - (σ - d.sigmaF c') = d.sigmaF c' - d.sigmaFLim := by ring
      rw [this]; exact hf1)
    (by positivity)
  refine hfinal.trans ?_
  have hq1 : q ≤ 1 := hδq.trans hq0one
  have hq2 : q ≤ ε / (3 * (B + 1)) := hδq.trans hq0B
  have hB1 : 0 < B + 1 := by linarith
  have e1 : ε / 6 * (1 + q) ≤ ε / 3 := by nlinarith
  have e2 : B * q ≤ ε / 3 := by
    calc B * q ≤ B * (ε / (3 * (B + 1))) := mul_le_mul_of_nonneg_left hq2 hB0
      _ ≤ (B + 1) * (ε / (3 * (B + 1))) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = ε / 3 := by field_simp
  have e3 : 2 * B * ε2 ≤ ε / 3 := by
    calc 2 * B * ε2 ≤ 2 * B * (ε / (6 * (B + 1))) := mul_le_mul_of_nonneg_left hε2B (by positivity)
      _ ≤ 2 * (B + 1) * (ε / (6 * (B + 1))) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = ε / 3 := by field_simp; ring
  linarith

/-- **Lemma R (`ut:R`)**, lower bound form: `w₀ > 0` with `h₀(x) e^{c'L(x)} ≥ K̃_c^{(f)} w₀ (σ - σ_f(c'))` for
all large `c'` and `σ_f(c') < σ ≤ Σ₀`, `x = ξ_* + λσ`. -/
theorem lemma_R_lower {f N : ℕ} (𝒦 : CompactCombFamily f N) {d : ModifiedCombData f N}
    (hd : d ∈ 𝒦.members) (hε : PosLimitWidths d) (Sg0 : ℝ) :
    ∃ w0 : ℝ, 0 < w0 ∧ ∃ C₀ : ℝ, ∀ {c' : ℝ}, C₀ ≤ c' → ∀ σ : ℝ, d.sigmaF c' < σ → σ ≤ Sg0 →
      windowNormKTilde f c' * w0 * (σ - d.sigmaF c') ≤
        modifiedH0 f N d c' (xiStar + lambdaComb c' * σ) *
          Real.exp (c' * slitL (xiStar + lambdaComb c' * σ)) := by
  obtain ⟨w1, hw1, hlow⟩ := windowRegular_lower 𝒦 hd hε Sg0
  obtain ⟨C₀, hC₀, hR⟩ := lemma_R 𝒦 hd Sg0 (w1 / 2) (half_pos hw1)
  obtain ⟨C₁, hC₁, hU⟩ := 𝒦.uniform_tendsto (ε := 1 / 2) (by norm_num)
  refine ⟨w1 / 2, half_pos hw1, max C₀ (max C₁ 1), fun {c'} hc' σ hσ1 hσ2 => ?_⟩
  have hc0 : C₀ ≤ c' := (le_max_left _ _).trans hc'
  have hc1 : C₁ ≤ c' := (le_max_left _ _).trans ((le_max_right _ _).trans hc')
  have hcpos : 0 < c' := lt_of_lt_of_le one_pos ((le_max_right _ _).trans ((le_max_right _ _).trans hc'))
  have hK := windowNormKTilde_pos f hcpos
  have hs : 0 < σ - d.sigmaF c' := sub_pos.mpr hσ1
  have hσlim : d.sigmaFLim - 1 / 2 ≤ σ := by
    have := (abs_le.mp (hU hc1 d hd).1).1
    linarith
  have h1 := hlow σ ⟨hσlim, hσ2⟩
  have h2 := hR hc0 σ hσ1 hσ2
  have h3 := (abs_le.mp h2).1
  have h4 : w1 / 2 ≤ modifiedH0 f N d c' (xiStar + lambdaComb c' * σ) *
      Real.exp (c' * slitL (xiStar + lambdaComb c' * σ)) / (windowNormKTilde f c' * (σ - d.sigmaF c')) := by
    linarith
  rw [le_div_iff₀ (mul_pos hK hs)] at h4
  calc windowNormKTilde f c' * (w1 / 2) * (σ - d.sigmaF c') = w1 / 2 * (windowNormKTilde f c' * (σ - d.sigmaF c')) := by ring
    _ ≤ _ := h4

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.lemma_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_R

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.lemma_R_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_R_lower

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.tildeW_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tildeW_eq_zero_iff

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.tildeW_eq_mul_windowRegular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tildeW_eq_mul_windowRegular

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.windowRegular_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms windowRegular_lower

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.tildeW_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tildeW_pos

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.tildeW_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tildeW_neg

end FormalResearch.ModularBootstrap.Upper.Window
