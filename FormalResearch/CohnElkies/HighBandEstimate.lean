module

public import FormalResearch.CohnElkies.OuterWeightedBound

/-!
# `O.3(2)`: the high-band estimate `(e4)` for the one-level seeds

Source: `CFT/sign_uncertainty/paper/u1c_o1_upper.tex`, Lemma `O.3`(2) (`u1co:O3`, `(e4)`), proof in `u1c_estimate_proofs.tex`: for `δ₀ = β₁ K ε / 2`,
`K ≥ 1`, `M₁ ≥ 1`, `c ≥ max(2000, 8K³)` and `S ≥ max(100, M₁ K^{-2} c^{2/3})`,
`|I_main[F](ξ) - 𝒜_F(ξ)| ≤ C_HB [M₁^{-m/2} + K^{-m} + S^{-1/2}] 𝒜_F(ξ)`.
Here the Lean statements are the absolute form `|I_main - 𝒜| ≤ C [M₁^{-m/2} + K^{-m} + S^{-1/2}] A^{-3/2}/(2π ξ)` with `𝒜 = γ₀ √π A^{-3/2}/(2π ξ)`,
`A = π² S`, for one fixed seed (`hb_estimate_airySeed`, `hb_estimate_hbSeed_m1`) or for any `X` with square-root data (`hb_estimate_of_sqData`); the
relative form `≤ C' [...] |𝒜|` needs `γ₀ ≠ 0` (`hb_estimate_airySeed_rel`).

The `χ_ξ`-part is Piece C (`pieceC_main_term_smooth`, with the regularity `SmoothSymbol` of `G_sm` proved in `SeedSqrtForm`); the `(1-χ_ξ)`-part is
the weighted outer bound (`outer_amplitude`, `outer_bound_small_L`, `outer_bound_large_tau`, with the `(e27)` data of `ImagAxisBounds`).

Status: proved, unconditional.

Not formalised: (i) the identification of the leading coefficient with the paper's `γ₀(F) = c_s^{1/2} 2^{2/3} π^{-1/2} β_∞(F)`: here `γ₀ = -c_s^{1/2} B(0)`
is the square-root coefficient of the seed's twisted Laplace transform, and the statements only assert that this `γ₀` works (it is unique, since the error
is relatively `o(1)`); (ii) uniformity of `C` over a bounded family of seeds: `C` depends on the seed (for `hb_estimate_hbSeed_m1`, on `γ₁, γ₂, δ, r`) and on `m`,
and is independent of `K, M₁, c, ξ` only; (iii) the second claim of `O.3`(2), `|I_main| ≤ C_{L₀}(1 + K^{-m}) ξ^{-1} c^{-1}` for `L ≥ L₀`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.CohnElkies

open FormalResearch.Asymptotics FormalResearch.Special

/-! ### The cut-off -/

/-- A cut-off `χ`: `C²`, `χ = 1` on `[-1/2, 1/2]`, `χ = 0` off `[-1, 1]`, with `|χ|, |χ'|, |χ''| ≤ K_χ`. -/
structure CutoffData (χ : ℝ → ℝ) (Kχ : ℝ) : Prop where
  contDiff : ContDiff ℝ 2 χ
  one : ∀ u : ℝ, |u| ≤ 1 / 2 → χ u = 1
  zero : ∀ u : ℝ, 1 < |u| → χ u = 0
  b0 : ∀ u : ℝ, |χ u| ≤ Kχ
  b1 : ∀ u : ℝ, |deriv χ u| ≤ Kχ
  b2 : ∀ u : ℝ, |deriv (deriv χ) u| ≤ Kχ

lemma exists_cutoffData : ∃ (χ : ℝ → ℝ) (Kχ : ℝ), CutoffData χ Kχ := by
  obtain ⟨χ, hχ, h1, h0⟩ := exists_cutoff_chi1
  have hcd : ContDiff ℝ 2 χ := hχ 2
  have hcs : HasCompactSupport χ := HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun v hv => h0 v (by
    by_contra h; exact hv ⟨(abs_le.mp (not_lt.mp h)).1, (abs_le.mp (not_lt.mp h)).2⟩)
  have hd1 : ContDiff ℝ 1 (deriv χ) := (contDiff_succ_iff_deriv (n := 1)).mp (by simpa [one_add_one_eq_two] using hcd) |>.2.2
  have hd2 : ContDiff ℝ 0 (deriv (deriv χ)) := (contDiff_succ_iff_deriv (n := 0)).mp (by simpa using hd1) |>.2.2
  obtain ⟨K0, hK0⟩ := hcs.exists_bound_of_continuous hcd.continuous
  obtain ⟨K1, hK1⟩ := hcs.deriv.exists_bound_of_continuous hd1.continuous
  obtain ⟨K2, hK2⟩ := hcs.deriv.deriv.exists_bound_of_continuous hd2.continuous
  refine ⟨χ, max K0 (max K1 K2), ⟨hcd, h1, h0, fun u => ?_, fun u => ?_, fun u => ?_⟩⟩
  · exact ((Real.norm_eq_abs (χ u)).symm.trans_le (hK0 u)).trans (le_max_left _ _)
  · exact ((Real.norm_eq_abs (deriv χ u)).symm.trans_le (hK1 u)).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact ((Real.norm_eq_abs (deriv (deriv χ) u)).symm.trans_le (hK2 u)).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- The outer cut-off `χ_o(τ) = 1 - χ(τ/τ_*)`: vanishes on `|τ| < τ_*/2` and has `|χ_o^{(r)}| ≤ (1+K_χ)|τ|^{-r}` for `|τ| ≥ τ_*/2`. -/
lemma outerCutoff {χ : ℝ → ℝ} {Kχ : ℝ} (hχ : CutoffData χ Kχ) {τs : ℝ} (hτs : 0 < τs) :
    ContDiff ℝ 2 (fun τ : ℝ => 1 - χ (τ / τs)) ∧ (∀ τ : ℝ, |τ| < τs / 2 → 1 - χ (τ / τs) = 0) ∧
      (∀ τ : ℝ, τs / 2 ≤ |τ| → |1 - χ (τ / τs)| ≤ 1 + Kχ) ∧
      (∀ τ : ℝ, τs / 2 ≤ |τ| → |deriv (fun τ : ℝ => 1 - χ (τ / τs)) τ| ≤ (1 + Kχ) * |τ| ^ (-(1 : ℝ))) ∧
      (∀ τ : ℝ, τs / 2 ≤ |τ| → |deriv (deriv (fun τ : ℝ => 1 - χ (τ / τs))) τ| ≤ (1 + Kχ) * |τ| ^ (-(2 : ℝ))) := by
  have hK : 0 ≤ Kχ := (abs_nonneg _).trans (hχ.b0 0)
  have hτs0 : τs ≠ 0 := hτs.ne'
  have hdf : ContDiff ℝ 1 (deriv χ) := (contDiff_succ_iff_deriv (n := 1)).mp (by simpa [one_add_one_eq_two] using hχ.contDiff) |>.2.2
  have hd1 : ∀ τ, deriv (fun τ : ℝ => 1 - χ (τ / τs)) τ = -((1 / τs) * deriv χ (τ / τs)) := fun τ => by
    have h1 : HasDerivAt (fun x : ℝ => x / τs) (1 / τs) τ := by simpa using (hasDerivAt_id τ).div_const τs
    have := ((hχ.contDiff.differentiable (by norm_num) (τ / τs)).hasDerivAt.scomp τ h1).const_sub 1
    simpa [smul_eq_mul, mul_comm] using this.deriv
  have hd2 : ∀ τ, deriv (deriv (fun τ : ℝ => 1 - χ (τ / τs))) τ = -((1 / τs) * ((1 / τs) * deriv (deriv χ) (τ / τs))) := fun τ => by
    have : deriv (fun τ : ℝ => 1 - χ (τ / τs)) = fun τ => -((1 / τs) * deriv χ (τ / τs)) := funext hd1
    rw [this]
    have h1 : HasDerivAt (fun x : ℝ => x / τs) (1 / τs) τ := by simpa using (hasDerivAt_id τ).div_const τs
    have := (((hdf.differentiable one_ne_zero (τ / τs)).hasDerivAt.scomp τ h1).const_mul (1 / τs)).neg
    simpa [smul_eq_mul, mul_comm] using this.deriv
  have hopen : IsOpen {u : ℝ | 1 < |u|} := isOpen_lt continuous_const continuous_abs
  have hz1 : ∀ u : ℝ, 1 < |u| → deriv χ u = 0 := fun u hu => by
    have : χ =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [hopen.mem_nhds hu] with x hx using hχ.zero x hx
    rw [this.deriv_eq]; simp
  have hz2 : ∀ u : ℝ, 1 < |u| → deriv (deriv χ) u = 0 := fun u hu => by
    have : deriv χ =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [hopen.mem_nhds hu] with x hx using hz1 x hx
    rw [this.deriv_eq]; simp
  refine ⟨contDiff_const.sub (hχ.contDiff.comp (contDiff_id.div_const τs)), fun τ hτ => ?_, fun τ hτ => ?_, fun τ hτ => ?_, fun τ hτ => ?_⟩
  · rw [hχ.one _ (by rw [abs_div, abs_of_pos hτs, div_le_iff₀ hτs]; linarith)]; ring
  · calc |1 - χ (τ / τs)| ≤ |1| + |χ (τ / τs)| := abs_sub _ _
      _ ≤ 1 + Kχ := by rw [abs_one]; linarith [hχ.b0 (τ / τs)]
  · have ht0 : 0 < |τ| := by linarith
    rw [hd1, abs_neg, abs_mul, abs_of_pos (by positivity : 0 < 1 / τs)]
    by_cases hu : 1 < |τ / τs|
    · rw [hz1 _ hu]; simp; positivity
    · have hle : |τ| ≤ τs := by
        have hu' := not_lt.mp hu
        rw [abs_div, abs_of_pos hτs, div_le_one hτs] at hu'; exact hu'
      have : 1 / τs ≤ |τ| ^ (-(1 : ℝ)) := by
        rw [Real.rpow_neg_one, one_div]; exact inv_anti₀ ht0 hle
      calc 1 / τs * |deriv χ (τ / τs)| ≤ |τ| ^ (-(1 : ℝ)) * Kχ := mul_le_mul this (hχ.b1 _) (abs_nonneg _) (by positivity)
        _ ≤ (1 + Kχ) * |τ| ^ (-(1 : ℝ)) := by
          have : 0 ≤ |τ| ^ (-(1 : ℝ)) := by positivity
          nlinarith
  · have ht0 : 0 < |τ| := by linarith
    rw [hd2, abs_neg, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 1 / τs)]
    by_cases hu : 1 < |τ / τs|
    · rw [hz2 _ hu]; simp; positivity
    · have hle : |τ| ≤ τs := by
        have hu' := not_lt.mp hu
        rw [abs_div, abs_of_pos hτs, div_le_one hτs] at hu'; exact hu'
      have h1 : 1 / τs ≤ |τ|⁻¹ := by rw [one_div]; exact inv_anti₀ ht0 hle
      have : 1 / τs * (1 / τs) ≤ |τ| ^ (-(2 : ℝ)) := by
        have e : |τ| ^ (-(2 : ℝ)) = |τ|⁻¹ * |τ|⁻¹ := by
          rw [Real.rpow_neg ht0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_two, mul_inv]
        rw [e]; exact mul_le_mul h1 h1 (by positivity) (by positivity)
      calc 1 / τs * (1 / τs * |deriv (deriv χ) (τ / τs)|) = (1 / τs * (1 / τs)) * |deriv (deriv χ) (τ / τs)| := by ring
        _ ≤ |τ| ^ (-(2 : ℝ)) * Kχ := mul_le_mul this (hχ.b2 _) (abs_nonneg _) (by positivity)
        _ ≤ (1 + Kχ) * |τ| ^ (-(2 : ℝ)) := by
          have : 0 ≤ |τ| ^ (-(2 : ℝ)) := by positivity
          nlinarith

/-! ### The parameters of `(e4)` -/

/-- `S_eff = L / (π² ε²)`, `L = log(π² ξ)`, `ε = c^{-1/3}`. -/
noncomputable def hbS (c ξ : ℝ) : ℝ := Real.log (Real.pi ^ 2 * ξ) / (Real.pi ^ 2 * liftEps c ^ 2)

/-- `A = c ε L`, equal to `π² S_eff`. -/
noncomputable def hbA (c ξ : ℝ) : ℝ := c * liftEps c * Real.log (Real.pi ^ 2 * ξ)

lemma liftEps_cube_mul {c : ℝ} (hc : 0 < c) : liftEps c ^ 3 * c = 1 := by
  unfold liftEps
  rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]
  norm_num
  rw [← Real.rpow_add_one hc.ne']; norm_num

lemma rpow_third_eq {c : ℝ} (hc : 0 < c) : c ^ (1 / 3 : ℝ) = (liftEps c)⁻¹ := (liftEps_inv hc).symm

lemma rpow_neg_half_eq {c : ℝ} (hc : 0 < c) : c ^ (-(1 / 2 : ℝ)) = liftEps c ^ (3 / 2 : ℝ) := by
  unfold liftEps
  rw [← Real.rpow_mul hc.le]; norm_num

lemma cEps_rpow {c : ℝ} (hc : 0 < c) : (c * liftEps c) ^ (-(3 / 2 : ℝ)) = liftEps c ^ 3 := by
  have hε := liftEps_pos hc
  have h1 : c * liftEps c = (liftEps c ^ 2)⁻¹ := by
    have := liftEps_cube_mul hc
    field_simp; nlinarith [this]
  rw [h1, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]
  norm_num

lemma hbA_eq {c ξ : ℝ} (hc : 0 < c) : hbA c ξ = Real.pi ^ 2 * hbS c ξ := by
  unfold hbA hbS
  have hε := liftEps_pos hc
  have := liftEps_cube_mul hc
  have h3 : c * liftEps c ^ 3 = 1 := by linarith [this]
  field_simp
  linear_combination (Real.log (Real.pi ^ 2 * ξ)) * h3

lemma hbA_pow {c ξ : ℝ} (hc : 0 < c) (hL : 0 < Real.log (Real.pi ^ 2 * ξ)) :
    hbA c ξ ^ (-(3 / 2 : ℝ)) = liftEps c ^ 3 * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) := by
  unfold hbA
  rw [Real.mul_rpow (by have := liftEps_pos hc; positivity) hL.le, cEps_rpow hc]

lemma liftEps_sq_mul {c : ℝ} (hc : 0 < c) : liftEps c ^ 2 * c ^ (2 / 3 : ℝ) = 1 := by
  unfold liftEps
  rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le, ← Real.rpow_add hc]
  norm_num

lemma hb_L_eq {c ξ : ℝ} (hc : 0 < c) : Real.log (Real.pi ^ 2 * ξ) = Real.pi ^ 2 * liftEps c ^ 2 * hbS c ξ := by
  have := liftEps_pos hc
  unfold hbS; field_simp

lemma hb_K_eps {K c : ℝ} (hK : 1 ≤ K) (hc8 : 8 * K ^ 3 ≤ c) : K * liftEps c ≤ 1 / 2 := by
  have hc : 0 < c := by nlinarith [pow_pos (by linarith : (0 : ℝ) < K) 3]
  have hε := liftEps_pos hc
  have h3 := liftEps_cube_mul hc
  by_contra hlt
  push Not at hlt
  have h1 : (1 / 2 : ℝ) ^ 3 < (K * liftEps c) ^ 3 := pow_lt_pow_left₀ hlt (by norm_num) (by norm_num)
  have h2 : (K * liftEps c) ^ 3 * 8 ≤ 1 := by
    calc (K * liftEps c) ^ 3 * 8 = (8 * K ^ 3) * liftEps c ^ 3 := by ring
      _ ≤ c * liftEps c ^ 3 := mul_le_mul_of_nonneg_right hc8 (by positivity)
      _ = 1 := by linarith [h3]
  nlinarith

lemma hb_eps_small {c : ℝ} (hc2k : 2000 ≤ c) : liftEps c ≤ 1 / 12 := by
  have hc : 0 < c := by linarith
  have hε := liftEps_pos hc
  have h3 := liftEps_cube_mul hc
  by_contra hlt
  push Not at hlt
  have h1 : (1 / 12 : ℝ) ^ 3 < liftEps c ^ 3 := pow_lt_pow_left₀ hlt (by norm_num) (by norm_num)
  nlinarith [h3]

lemma tauStar_pos {L : ℝ} (hL : 0 < L) : 0 < tauStar L := by
  unfold tauStar
  split_ifs
  · exact div_pos (Real.sqrt_pos.mpr hL) Real.pi_pos
  · exact div_pos (Real.exp_pos _) Real.pi_pos

lemma eps_mix {c : ℝ} (hc : 0 < c) : c ^ (1 / 3 : ℝ) * liftEps c ^ (5 / 2 : ℝ) * c ^ (-(1 / 2 : ℝ)) = liftEps c ^ 3 := by
  have hε := liftEps_pos hc
  rw [rpow_third_eq hc, rpow_neg_half_eq hc, ← Real.rpow_neg_one, ← Real.rpow_add hε, ← Real.rpow_add hε,
    show (-1 + 5 / 2 + 3 / 2 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The `L`-algebra of the small-`τ₁` case. -/
lemma small_algebra {L τ₁ κ : ℝ} (m : ℕ) (hL : 0 < L) (hτ : 0 < τ₁) (hκ : 0 < κ) (hΛ : L ^ (1 / 2 : ℝ) ≤ 20 * τ₁) (hτ1 : τ₁ ≤ 1) :
    ((κ ^ m)⁻¹ * τ₁ ^ (-((m : ℝ) + 5 / 2)) * (1 + τ₁)) * L ^ (-(1 / 4 : ℝ)) ≤
      2 * 20 ^ (5 / 2 : ℝ) * ((κ * τ₁) ^ m)⁻¹ * L ^ (-(3 / 2 : ℝ)) := by
  have h1 : τ₁ ^ (-((m : ℝ) + 5 / 2)) = (τ₁ ^ m)⁻¹ * τ₁ ^ (-(5 / 2 : ℝ)) := by
    rw [show -((m : ℝ) + 5 / 2) = -(m : ℝ) + -(5 / 2 : ℝ) by ring, Real.rpow_add hτ, Real.rpow_neg hτ.le, Real.rpow_natCast]
  have h2 : L ^ (-(1 / 4 : ℝ)) = L ^ (-(3 / 2 : ℝ)) * L ^ (5 / 4 : ℝ) := by
    rw [← Real.rpow_add hL]; norm_num
  have h3 : τ₁ ^ (-(5 / 2 : ℝ)) * L ^ (5 / 4 : ℝ) ≤ 20 ^ (5 / 2 : ℝ) := by
    have h4 : L ^ (5 / 4 : ℝ) = (L ^ (1 / 2 : ℝ)) ^ (5 / 2 : ℝ) := by rw [← Real.rpow_mul hL.le]; norm_num
    have h5 : (L ^ (1 / 2 : ℝ)) ^ (5 / 2 : ℝ) ≤ (20 * τ₁) ^ (5 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) hΛ (by norm_num)
    rw [h4]
    calc τ₁ ^ (-(5 / 2 : ℝ)) * (L ^ (1 / 2 : ℝ)) ^ (5 / 2 : ℝ) ≤ τ₁ ^ (-(5 / 2 : ℝ)) * (20 * τ₁) ^ (5 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = 20 ^ (5 / 2 : ℝ) := by
          rw [Real.mul_rpow (by norm_num) hτ.le, Real.rpow_neg hτ.le]
          field_simp
  have h6 : (κ ^ m)⁻¹ * (τ₁ ^ m)⁻¹ = ((κ * τ₁) ^ m)⁻¹ := by rw [mul_pow, mul_inv]
  rw [h1, h2]
  have hP : 0 ≤ ((κ * τ₁) ^ m)⁻¹ := by positivity
  have h7 : 1 + τ₁ ≤ 2 := by linarith
  calc (κ ^ m)⁻¹ * ((τ₁ ^ m)⁻¹ * τ₁ ^ (-(5 / 2 : ℝ))) * (1 + τ₁) * (L ^ (-(3 / 2 : ℝ)) * L ^ (5 / 4 : ℝ))
      = ((κ ^ m)⁻¹ * (τ₁ ^ m)⁻¹) * (τ₁ ^ (-(5 / 2 : ℝ)) * L ^ (5 / 4 : ℝ)) * (1 + τ₁) * L ^ (-(3 / 2 : ℝ)) := by ring
    _ ≤ ((κ * τ₁) ^ m)⁻¹ * 20 ^ (5 / 2 : ℝ) * 2 * L ^ (-(3 / 2 : ℝ)) := by
        rw [h6]; gcongr
    _ = _ := by ring

lemma ceBeta1_cube : ceBeta1 ^ 3 = Real.pi ^ 4 * 3 := by
  have hsq : (Real.pi ^ 2 * √3) ^ 2 = Real.pi ^ 4 * 3 := by rw [mul_pow, ← pow_mul, Real.sq_sqrt (by norm_num)]
  unfold ceBeta1; rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity)]; norm_num; exact hsq

lemma ceCs_mul_ceBeta1 : ceCs * ceBeta1 = Real.pi ^ 2 := by
  have h1 : (ceCs * ceBeta1) ^ 3 = (Real.pi ^ 2) ^ 3 := by
    rw [mul_pow, ceCs_cube', ceBeta1_cube]; ring
  exact (pow_left_inj₀ (by have := ceCs_pos; have := ceBeta1_pos; positivity) (by positivity) (by norm_num)).mp h1

lemma kappa_eq {K ε : ℝ} (m : ℕ) (hm : 1 ≤ m) (hε : 0 < ε) :
    ceCs * (ceBeta1 * K * ε / 2) / m / ε = Real.pi ^ 2 * K / (2 * m) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < m).ne'
  have h := ceCs_mul_ceBeta1
  field_simp
  linear_combination K * h

lemma eps_sq_rpow {ε : ℝ} (hε : 0 < ε) : (ε ^ 2) ^ (3 / 2 : ℝ) = ε ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]; norm_num

/-! ### Elementary bounds on `κ τ₁` -/

lemma kappa_inv_bound {K : ℝ} (hK : 1 ≤ K) (m : ℕ) (hm : 1 ≤ m) :
    ((Real.pi ^ 2 * K / (2 * m)) ^ m)⁻¹ = (2 * m / Real.pi ^ 2) ^ m * K ^ (-(m : ℝ)) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hK0 : 0 < K := by linarith
  rw [Real.rpow_neg hK0.le, Real.rpow_natCast, ← inv_pow, ← inv_pow, ← mul_pow]
  congr 1
  field_simp

lemma kt_bound_le_one {K M₁ L : ℝ} (m : ℕ) (hm : 1 ≤ m) (hK : 1 ≤ K) (hM₁ : 1 ≤ M₁) (hL : 0 < L)
    (hLl : Real.pi ^ 2 * M₁ * (K ^ 2)⁻¹ ≤ L) :
    (((Real.pi ^ 2 * K / (2 * m)) * (Real.sqrt L / 2 / Real.pi)) ^ m)⁻¹ ≤ (4 * m / Real.pi ^ 2) ^ m * M₁ ^ (-((m : ℝ) / 2)) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hK0 : 0 < K := by linarith
  have hM0 : 0 < M₁ := by linarith
  have hpi := Real.pi_pos
  have h1 : Real.pi * Real.sqrt M₁ ≤ K * Real.sqrt L := by
    have : Real.pi ^ 2 * M₁ ≤ K ^ 2 * L := by
      have := mul_le_mul_of_nonneg_left hLl (sq_nonneg K)
      calc Real.pi ^ 2 * M₁ = K ^ 2 * (Real.pi ^ 2 * M₁ * (K ^ 2)⁻¹) := by field_simp
        _ ≤ K ^ 2 * L := this
    have h2 := Real.sqrt_le_sqrt this
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hpi.le, Real.sqrt_sq hK0.le] at h2
  set y : ℝ := (Real.pi ^ 2 * K / (2 * m)) * (Real.sqrt L / 2 / Real.pi) with hy
  have hy_ge : Real.pi ^ 2 * Real.sqrt M₁ / (4 * m) ≤ y := by
    have : y = Real.pi * (K * Real.sqrt L) / (4 * m) := by rw [hy]; field_simp; ring
    rw [this, div_le_div_iff_of_pos_right (by positivity)]
    calc Real.pi ^ 2 * Real.sqrt M₁ = Real.pi * (Real.pi * Real.sqrt M₁) := by ring
      _ ≤ Real.pi * (K * Real.sqrt L) := mul_le_mul_of_nonneg_left h1 hpi.le
  have hpos : 0 < Real.pi ^ 2 * Real.sqrt M₁ / (4 * m) := by positivity
  have h3 : ((y) ^ m)⁻¹ ≤ ((Real.pi ^ 2 * Real.sqrt M₁ / (4 * m)) ^ m)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ hpos.le hy_ge m)
  refine h3.trans (le_of_eq ?_)
  have e1 : ((M₁ ^ (1 / 2 : ℝ)) ^ m)⁻¹ = M₁ ^ (-((m : ℝ) / 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM0.le, ← Real.rpow_neg hM0.le]; congr 1; ring
  rw [Real.sqrt_eq_rpow, ← e1, ← inv_pow, ← inv_pow, ← mul_pow]
  congr 1
  field_simp

lemma kt_bound_gt_one {K τ₁ : ℝ} (m : ℕ) (hm : 1 ≤ m) (hK : 1 ≤ K) (hτ₁ : 1 / (2 * Real.pi) ≤ τ₁) :
    (((Real.pi ^ 2 * K / (2 * m)) * τ₁) ^ m)⁻¹ ≤ (4 * m / Real.pi) ^ m * K ^ (-(m : ℝ)) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hK0 : 0 < K := by linarith
  have hpi := Real.pi_pos
  have hy_ge : Real.pi * K / (4 * m) ≤ (Real.pi ^ 2 * K / (2 * m)) * τ₁ := by
    calc Real.pi * K / (4 * m) = (Real.pi ^ 2 * K / (2 * m)) * (1 / (2 * Real.pi)) := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hτ₁ (by positivity)
  have h3 : (((Real.pi ^ 2 * K / (2 * m)) * τ₁) ^ m)⁻¹ ≤ ((Real.pi * K / (4 * m)) ^ m)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hy_ge m)
  refine h3.trans (le_of_eq ?_)
  rw [Real.rpow_neg hK0.le, Real.rpow_natCast, ← inv_pow, ← inv_pow, ← mul_pow]
  congr 1
  field_simp
lemma close_aux {C1 C2 C3 a b R x : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3) (ha : 0 ≤ a) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hx : x ≤ C1 * a * R ∨ x ≤ C2 * b * R ∨ x ≤ C3 * b * R) : x ≤ (C1 + C2 + C3 + 1) * (a + b) * R := by
  have e1 : C1 * a ≤ (C1 + C2 + C3 + 1) * (a + b) := by
    nlinarith [mul_nonneg hC1 hb, mul_nonneg hC2 (add_nonneg ha hb), mul_nonneg hC3 (add_nonneg ha hb)]
  have e2 : C2 * b ≤ (C1 + C2 + C3 + 1) * (a + b) := by
    nlinarith [mul_nonneg hC2 ha, mul_nonneg hC1 (add_nonneg ha hb), mul_nonneg hC3 (add_nonneg ha hb)]
  have e3 : C3 * b ≤ (C1 + C2 + C3 + 1) * (a + b) := by
    nlinarith [mul_nonneg hC3 ha, mul_nonneg hC1 (add_nonneg ha hb), mul_nonneg hC2 (add_nonneg ha hb)]
  rcases hx with hx | hx | hx
  · exact hx.trans (mul_le_mul_of_nonneg_right e1 hR)
  · exact hx.trans (mul_le_mul_of_nonneg_right e2 hR)
  · exact hx.trans (mul_le_mul_of_nonneg_right e3 hR)

/-! ### The `(1 - χ_ξ)`-part -/

set_option maxHeartbeats 1600000 in
/-- **`O.3(2)`, the `(1 - χ_ξ)`-part of `I_main`.** For a symbol with `SymbolTail` data (`(e27)` off `|v| ≤ 1`) and a cut-off `χ`, the outer part
`(2πξ)⁻¹ ∫ (1 - χ(ε v / τ_*(L))) K₀ W dv` has norm `≤ C (M₁^{-m/2} + K^{-m}) A^{-3/2}/(2π ξ)` in the parameter range of `(e4)` (`δ₀ = β₁ K ε / 2`,
`K, M₁ ≥ 1`, `c ≥ max(2000, 8K³)`, `S ≥ max(100, M₁ K^{-2} c^{2/3})`); `C` depends on `CG, Kχ, m` only. -/
theorem hb_outer {X : ℝ → ℝ} {CG : ℝ} (hCG : 0 ≤ CG)
    (hG : SymbolTail (fun v : ℝ => airyTwistedLaplaceC X (yv v)) CG) {χ : ℝ → ℝ} {Kχ : ℝ} (hχ : CutoffData χ Kχ)
    {m : ℕ} (hm : 1 ≤ m) :
    ∃ C > 0, ∀ {K M₁ c ξ : ℝ}, 1 ≤ K → 1 ≤ M₁ → 8 * K ^ 3 ≤ c → 2000 ≤ c → 0 < ξ → 100 ≤ hbS c ξ →
      M₁ * (K ^ 2)⁻¹ * c ^ (2 / 3 : ℝ) ≤ hbS c ξ →
      ‖((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, ((1 - χ (liftEps c * v / tauStar (Real.log (Real.pi ^ 2 * ξ))) : ℝ) : ℂ) *
          iMainIntegrand X (ceBeta1 * K * liftEps c / 2) m c ξ v‖ ≤
        C * (M₁ ^ (-((m : ℝ) / 2)) + K ^ (-(m : ℝ))) * (hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ)) := by
  obtain ⟨Cs, hCs, hsmall⟩ := outer_bound_small_L
  obtain ⟨Cl, hCl, hlarge⟩ := outer_bound_large_tau
  have hK0 : 0 ≤ Kχ := (abs_nonneg _).trans (hχ.b0 0)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  let Q₀ : ℝ := 4 * ((m : ℝ) + 2) ^ 2 * (1 + Kχ) * CG
  have hQ₀ : 0 ≤ Q₀ := by positivity
  let Γs : ℝ := Cs * 4 ^ m * Q₀
  let Γl : ℝ := Cl * 2 ^ m * (2 ^ (5 / 4 : ℝ) * Q₀)
  let C1 : ℝ := Γs * (2 * 20 ^ (5 / 2 : ℝ)) * (4 * m / Real.pi ^ 2) ^ m
  let C2 : ℝ := Γs * (2 * 20 ^ (5 / 2 : ℝ)) * (4 * m / Real.pi) ^ m
  let C3 : ℝ := Γl * (2 * m / Real.pi ^ 2) ^ m
  have hC1 : 0 ≤ C1 := by positivity
  have hC2 : 0 ≤ C2 := by positivity
  have hC3 : 0 ≤ C3 := by positivity
  refine ⟨C1 + C2 + C3 + 1, by positivity, fun {K M₁ c ξ} hK hM₁ hc8 hc2k hξ hS100 hSM => ?_⟩
  have hc0 : 0 < c := by linarith
  have hc2 : 2 ≤ c := by linarith
  have hε := liftEps_pos hc0
  have hKε := hb_K_eps hK hc8
  have hε12 := hb_eps_small hc2k
  have hLeq := hb_L_eq (ξ := ξ) hc0
  have hS0 : 0 < hbS c ξ := by linarith
  set ε := liftEps c with hεdef
  set L := Real.log (Real.pi ^ 2 * ξ) with hLdef
  have hL : 0 < L := by rw [hLeq]; positivity
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi < 3.15 := Real.pi_lt_d2
  -- the scaling parameters
  have hδ : 0 < ceBeta1 * K * ε / 2 := by have := ceBeta1_pos; positivity
  have hκ_eq := kappa_eq (K := K) m hm hε
  set κ : ℝ := ceCs * (ceBeta1 * K * ε / 2) / m / ε with hκdef
  have hκ : 0 < κ := by rw [hκ_eq]; positivity
  -- lower bound on `L`
  have hLlow : Real.pi ^ 2 * M₁ * (K ^ 2)⁻¹ ≤ L := by
    have h1 : Real.pi ^ 2 * ε ^ 2 * (M₁ * (K ^ 2)⁻¹ * c ^ (2 / 3 : ℝ)) ≤ L := by
      rw [hLeq]; exact mul_le_mul_of_nonneg_left hSM (by positivity)
    calc Real.pi ^ 2 * M₁ * (K ^ 2)⁻¹ = Real.pi ^ 2 * ε ^ 2 * (M₁ * (K ^ 2)⁻¹ * c ^ (2 / 3 : ℝ)) := by
          have := liftEps_sq_mul hc0
          calc Real.pi ^ 2 * M₁ * (K ^ 2)⁻¹ = Real.pi ^ 2 * M₁ * (K ^ 2)⁻¹ * (ε ^ 2 * c ^ (2 / 3 : ℝ)) := by rw [this, mul_one]
            _ = _ := by ring
      _ ≤ L := h1
  have hK2 : 0 < K ^ 2 := by positivity
  have hmκ : (m : ℝ) * κ ≤ c * L / 2 := by
    rw [hκ_eq]
    have h1 : Real.pi ^ 2 * K ≤ c * L := by
      have h2 : K ≤ c * (K ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hK2]; nlinarith only [hc8, pow_pos (by linarith only [hK] : (0 : ℝ) < K) 3]
      calc Real.pi ^ 2 * K ≤ Real.pi ^ 2 * (c * (K ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ Real.pi ^ 2 * (c * (M₁ * (K ^ 2)⁻¹)) := by
            gcongr; nlinarith only [mul_le_mul_of_nonneg_right hM₁ (inv_pos.mpr hK2).le]
        _ = c * (Real.pi ^ 2 * M₁ * (K ^ 2)⁻¹) := by ring
        _ ≤ c * L := mul_le_mul_of_nonneg_left hLlow hc0.le
    field_simp
    linarith
  have hcL : 1 ≤ c * (L / 2) ^ (3 / 2 : ℝ) := by
    have h1 : ε ^ 2 ≤ L / 2 := by
      have hπ2 : 9 ≤ Real.pi ^ 2 := by nlinarith only [hpi3]
      have hk : 1 ≤ Real.pi ^ 2 * hbS c ξ / 2 := by nlinarith only [hπ2, hS100, mul_nonneg (sub_nonneg.2 hπ2) (sub_nonneg.2 hS100)]
      calc ε ^ 2 = ε ^ 2 * 1 := (mul_one _).symm
        _ ≤ ε ^ 2 * (Real.pi ^ 2 * hbS c ξ / 2) := mul_le_mul_of_nonneg_left hk (by positivity)
        _ = L / 2 := by rw [hLeq]; ring
    have h2 : (ε ^ 2) ^ (3 / 2 : ℝ) ≤ (L / 2) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    rw [eps_sq_rpow hε] at h2
    have h3 := liftEps_cube_mul hc0
    calc (1 : ℝ) = c * ε ^ 3 := by linarith [h3]
      _ ≤ c * (L / 2) ^ (3 / 2 : ℝ) := mul_le_mul_of_nonneg_left h2 hc0.le
  -- the cut-off scale
  set τs := tauStar L with hτsdef
  have hτs : 0 < τs := tauStar_pos hL
  have hετ : ε < τs / 2 := by
    by_cases hL1 : L ≤ 1
    · have : τs = Real.sqrt L / Real.pi := by simp [hτsdef, tauStar, hL1]
      rw [this]
      have h1 : 2 * Real.pi * ε < Real.sqrt L := by
        rw [Real.lt_sqrt (by positivity)]
        rw [hLeq]
        have : 4 < hbS c ξ := by linarith
        nlinarith only [mul_pos (mul_pos (by positivity : 0 < Real.pi ^ 2) (by positivity : 0 < ε ^ 2)) (by linarith : 0 < hbS c ξ - 4)]
      rw [div_div, lt_div_iff₀ (by positivity)]; linarith
    · have : τs = Real.exp ((L - 1) / 2) / Real.pi := by simp [hτsdef, tauStar, hL1]
      rw [this]
      have h1 : 1 ≤ Real.exp ((L - 1) / 2) := Real.one_le_exp (by linarith [not_le.mp hL1])
      rw [div_div, lt_div_iff₀ (by positivity)]
      nlinarith only [hε12, hpi4, hpi3, h1, mul_nonneg (sub_nonneg.2 hε12) (by linarith only [hpi3] : (0 : ℝ) ≤ Real.pi)]
  set χo : ℝ → ℝ := fun τ => 1 - χ (τ / τs) with hχodef
  obtain ⟨hχo_cd, hχo_van, hk0, hk1, hk2⟩ := outerCutoff hχ hτs
  obtain ⟨h, hh_cd, hh_van, hh_rel, hh_bd⟩ := outer_amplitude (G := fun v : ℝ => airyTwistedLaplaceC X (yv v)) hG hCG (m := m)
    (κ := κ) (ε := ε) (τ₁ := τs / 2) (Kχ := 1 + Kχ) hκ hε hετ (χo := χo) hχo_cd hχo_van hk0 hk1 hk2
  have hrel : ∀ τ : ℝ, (χo τ : ℂ) * airyTwistedLaplaceC X ((ceCs : ℂ) * (((τ / ε : ℝ) : ℂ) * Complex.I)) =
      (Complex.I * ((ceCs * (ceBeta1 * K * ε / 2) / m / ε : ℝ) : ℂ) * (τ : ℂ)) ^ m * h τ := fun τ => by
    have := hh_rel τ
    simpa only [yv] using this
  have hred : ‖((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, ((1 - χ (liftEps c * v / τs) : ℝ) : ℂ) * iMainIntegrand X (ceBeta1 * K * ε / 2) m c ξ v‖ =
      (2 * Real.pi * ξ)⁻¹ * c ^ (1 / 3 : ℝ) * ‖∫ τ : ℝ, ((1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) *
        Complex.exp (binetDiff c (Complex.I * (τ : ℂ))) * (bsplineImag κ m τ *
          ((Complex.I * (κ : ℂ) * (τ : ℂ)) ^ m * h τ))) * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))‖ :=
    iMain_outer_eq hm X χo hc2 hξ hrel
  rw [hred]
  have hR : hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) = (2 * Real.pi * ξ)⁻¹ * (ε ^ 3 * L ^ (-(3 / 2 : ℝ))) := by
    rw [hbA_pow hc0 hL, div_eq_inv_mul]
  rw [hR]
  have hmix := eps_mix hc0
  set Q : ℝ := 4 * ((m : ℝ) + 2) ^ 2 * (1 + Kχ) * CG * ε ^ (5 / 2 : ℝ) * (κ ^ m)⁻¹ with hQdef
  have hQ0 : 0 ≤ Q := by positivity
  have hRnn : 0 ≤ (2 * Real.pi * ξ)⁻¹ * (ε ^ 3 * L ^ (-(3 / 2 : ℝ))) := by positivity
  have hpre : 0 ≤ (2 * Real.pi * ξ)⁻¹ * c ^ (1 / 3 : ℝ) := by positivity
  have ha : 0 ≤ M₁ ^ (-((m : ℝ) / 2)) := by positivity
  have hb : 0 ≤ K ^ (-(m : ℝ)) := by positivity
  by_cases hτ1 : τs / 2 < 1
  · -- the small case `τ₁ < 1`
    have hτ₁pos : 0 < τs / 2 := by positivity
    have hL5 : L < 5 := by
      by_contra hL5; push Not at hL5
      have hL1 : ¬ L ≤ 1 := by linarith only [hL5]
      have hts : τs = Real.exp ((L - 1) / 2) / Real.pi := by simp [hτsdef, tauStar, hL1]
      have he : 7 < Real.exp ((L - 1) / 2) := by
        have h1 : Real.exp 2 ≤ Real.exp ((L - 1) / 2) := Real.exp_le_exp.mpr (by linarith only [hL5])
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith only [h1, h2, Real.exp_one_gt_d9, mul_self_nonneg (Real.exp 1 - 2.7182818283)]
      rw [hts, div_div, div_lt_one (by positivity)] at hτ1
      nlinarith only [hτ1, he, hpi4]
    have hΛ : L ^ (1 / 2 : ℝ) ≤ 20 * (τs / 2) := by
      by_cases hL1 : L ≤ 1
      · have hts : τs = Real.sqrt L / Real.pi := by simp [hτsdef, tauStar, hL1]
        rw [← Real.sqrt_eq_rpow, hts]
        have h10 : 1 ≤ 10 / Real.pi := by rw [le_div_iff₀ Real.pi_pos]; linarith only [hpi4]
        have e : 20 * (Real.sqrt L / Real.pi / 2) = Real.sqrt L * (10 / Real.pi) := by ring
        rw [e]
        calc Real.sqrt L = Real.sqrt L * 1 := (mul_one _).symm
          _ ≤ Real.sqrt L * (10 / Real.pi) := mul_le_mul_of_nonneg_left h10 (Real.sqrt_nonneg L)
      · have hts : τs = Real.exp ((L - 1) / 2) / Real.pi := by simp [hτsdef, tauStar, hL1]
        have h1 : 1 ≤ Real.exp ((L - 1) / 2) := Real.one_le_exp (by linarith only [not_le.mp hL1])
        have h2 : 1 / Real.pi ≤ τs := by rw [hts]; exact div_le_div_of_nonneg_right h1 Real.pi_pos.le
        have h3 : 3 ≤ 10 / Real.pi := by rw [le_div_iff₀ Real.pi_pos]; linarith only [hpi4]
        have h4 : L ^ (1 / 2 : ℝ) ≤ 3 := by
          rw [← Real.sqrt_eq_rpow]
          exact Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith only [hL5]⟩
        have h5 : 10 / Real.pi ≤ 10 * τs := by
          calc 10 / Real.pi = 10 * (1 / Real.pi) := by ring
            _ ≤ 10 * τs := mul_le_mul_of_nonneg_left h2 (by norm_num)
        linarith only [h3, h4, h5]
    have hAlg := small_algebra m hL hτ₁pos hκ hΛ hτ1.le
    have hB := hsmall hm hκ hc2 hL (by linarith) hmκ hcL hQ0 hτ₁pos hh_cd hh_van hh_bd
    have hstep : (2 * Real.pi * ξ)⁻¹ * c ^ (1 / 3 : ℝ) * ‖∫ τ : ℝ, ((1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) *
        Complex.exp (binetDiff c (Complex.I * (τ : ℂ))) * (bsplineImag κ m τ *
          ((Complex.I * (κ : ℂ) * (τ : ℂ)) ^ m * h τ))) * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))‖ ≤
        Γs * (2 * 20 ^ (5 / 2 : ℝ)) * (((κ * (τs / 2)) ^ m)⁻¹) * ((2 * Real.pi * ξ)⁻¹ * (ε ^ 3 * L ^ (-(3 / 2 : ℝ)))) := by
      calc (2 * Real.pi * ξ)⁻¹ * c ^ (1 / 3 : ℝ) * _ ≤ (2 * Real.pi * ξ)⁻¹ * c ^ (1 / 3 : ℝ) *
            (Cs * 4 ^ m * Q * (τs / 2) ^ (-((m : ℝ) + 5 / 2)) * (1 + τs / 2) * c ^ (-(1 / 2 : ℝ)) * L ^ (-(1 / 4 : ℝ))) :=
            mul_le_mul_of_nonneg_left hB hpre
        _ = (2 * Real.pi * ξ)⁻¹ * (ε ^ 3 * (Γs * ((κ ^ m)⁻¹ * (τs / 2) ^ (-((m : ℝ) + 5 / 2)) * (1 + τs / 2) * L ^ (-(1 / 4 : ℝ))))) := by
            simp only [hQdef, Γs, Q₀]
            linear_combination ((2 * Real.pi * ξ)⁻¹ * (Cs * 4 ^ m * (4 * ((m : ℝ) + 2) ^ 2 * (1 + Kχ) * CG) * (κ ^ m)⁻¹ * (τs / 2) ^ (-((m : ℝ) + 5 / 2)) *
              (1 + τs / 2) * L ^ (-(1 / 4 : ℝ)))) * hmix
        _ ≤ (2 * Real.pi * ξ)⁻¹ * (ε ^ 3 * (Γs * (2 * 20 ^ (5 / 2 : ℝ) * ((κ * (τs / 2)) ^ m)⁻¹ * L ^ (-(3 / 2 : ℝ))))) := by
            gcongr
        _ = _ := by ring
    refine close_aux hC1 hC2 hC3 ha hb hRnn ?_
    by_cases hL1 : L ≤ 1
    · left
      have hts : τs = Real.sqrt L / Real.pi := by simp [hτsdef, tauStar, hL1]
      have hts' : τs / 2 = Real.sqrt L / 2 / Real.pi := by rw [hts]; ring
      have hW : ((κ * (τs / 2)) ^ m)⁻¹ ≤ (4 * m / Real.pi ^ 2) ^ m * M₁ ^ (-((m : ℝ) / 2)) := by
        rw [hκ_eq, hts']; exact kt_bound_le_one m hm hK hM₁ hL hLlow
      refine hstep.trans ?_
      calc Γs * (2 * 20 ^ (5 / 2 : ℝ)) * ((κ * (τs / 2)) ^ m)⁻¹ * ((2 * Real.pi * ξ)⁻¹ * (ε ^ 3 * L ^ (-(3 / 2 : ℝ))))
          ≤ Γs * (2 * 20 ^ (5 / 2 : ℝ)) * ((4 * m / Real.pi ^ 2) ^ m * M₁ ^ (-((m : ℝ) / 2))) * ((2 * Real.pi * ξ)⁻¹ * (ε ^ 3 * L ^ (-(3 / 2 : ℝ)))) := by
            have hΓ : 0 ≤ Γs * (2 * 20 ^ (5 / 2 : ℝ)) := by positivity
            gcongr
        _ = _ := by simp only [C1]; ring
    · right; left
      have hL1' : 1 < L := not_le.mp hL1
      have hts : τs = Real.exp ((L - 1) / 2) / Real.pi := by simp [hτsdef, tauStar, hL1]
      have h1 : 1 ≤ Real.exp ((L - 1) / 2) := Real.one_le_exp (by linarith only [hL1'])
      have h2 : 1 / Real.pi ≤ τs := by rw [hts]; exact div_le_div_of_nonneg_right h1 Real.pi_pos.le
      have hτ12 : 1 / (2 * Real.pi) ≤ τs / 2 := by
        calc 1 / (2 * Real.pi) = (1 / Real.pi) / 2 := by field_simp
          _ ≤ τs / 2 := by linarith only [h2]
      have hW : ((κ * (τs / 2)) ^ m)⁻¹ ≤ (4 * m / Real.pi) ^ m * K ^ (-(m : ℝ)) := by
        rw [hκ_eq]; exact kt_bound_gt_one m hm hK hτ12
      refine hstep.trans ?_
      calc Γs * (2 * 20 ^ (5 / 2 : ℝ)) * ((κ * (τs / 2)) ^ m)⁻¹ * ((2 * Real.pi * ξ)⁻¹ * (ε ^ 3 * L ^ (-(3 / 2 : ℝ))))
          ≤ Γs * (2 * 20 ^ (5 / 2 : ℝ)) * ((4 * m / Real.pi) ^ m * K ^ (-(m : ℝ))) * ((2 * Real.pi * ξ)⁻¹ * (ε ^ 3 * L ^ (-(3 / 2 : ℝ)))) := by
            have hΓ : 0 ≤ Γs * (2 * 20 ^ (5 / 2 : ℝ)) := by positivity
            gcongr
        _ = _ := by simp only [C2]; ring
  · -- the large case `τ₁ ≥ 1`
    have hτ₁ : 1 ≤ τs / 2 := not_lt.mp hτ1
    have hL1 : 1 < L := by
      by_contra hL1; push Not at hL1
      have hts : τs = Real.sqrt L / Real.pi := by simp [hτsdef, tauStar, hL1]
      have : Real.sqrt L ≤ 1 := Real.sqrt_le_one.mpr hL1
      have h2 : Real.sqrt L / Real.pi ≤ 1 / Real.pi := div_le_div_of_nonneg_right this Real.pi_pos.le
      have h3 : 1 / Real.pi < 1 := by rw [div_lt_one Real.pi_pos]; linarith only [hpi3]
      linarith only [hts, h2, h3, hτ₁]
    have hB := hlarge hm hκ hc2 hL hmκ hcL hQ0 hτ₁ hh_cd hh_van hh_bd
    have hτm : (τs / 2) ^ (-(m : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτ₁ (by simp)
    have hmin : min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) ≤ L ^ (-(3 / 2 : ℝ)) := min_le_right _ _
    refine close_aux hC1 hC2 hC3 ha hb hRnn ?_
    right; right
    have hκinv : (κ ^ m)⁻¹ = (2 * m / Real.pi ^ 2) ^ m * K ^ (-(m : ℝ)) := by rw [hκ_eq]; exact kappa_inv_bound hK m hm
    calc (2 * Real.pi * ξ)⁻¹ * c ^ (1 / 3 : ℝ) * _ ≤ (2 * Real.pi * ξ)⁻¹ * c ^ (1 / 3 : ℝ) *
          (Cl * 2 ^ m * (2 ^ (5 / 4 : ℝ) * Q * (τs / 2) ^ (-(m : ℝ))) * c ^ (-(1 / 2 : ℝ)) * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ)))) :=
          mul_le_mul_of_nonneg_left hB hpre
      _ ≤ (2 * Real.pi * ξ)⁻¹ * c ^ (1 / 3 : ℝ) *
          (Cl * 2 ^ m * (2 ^ (5 / 4 : ℝ) * Q * 1) * c ^ (-(1 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ))) := by gcongr
      _ = (2 * Real.pi * ξ)⁻¹ * (ε ^ 3 * (Γl * ((κ ^ m)⁻¹ * L ^ (-(3 / 2 : ℝ))))) := by
          simp only [hQdef, Γl, Q₀]
          linear_combination ((2 * Real.pi * ξ)⁻¹ * (Cl * 2 ^ m * (2 ^ (5 / 4 : ℝ) * (4 * ((m : ℝ) + 2) ^ 2 * (1 + Kχ) * CG)) * (κ ^ m)⁻¹ *
            L ^ (-(3 / 2 : ℝ)))) * hmix
      _ = _ := by rw [hκinv]; simp only [C3]; ring

/-! ### The `χ_ξ`-part (Piece C) -/

lemma hb_L_pos {c ξ : ℝ} (hc : 0 < c) (hS : 0 < hbS c ξ) : 0 < Real.log (Real.pi ^ 2 * ξ) := by
  have := liftEps_pos hc
  rw [hb_L_eq hc]; positivity

lemma hb_eps_lt_tau {c ξ : ℝ} (hc2k : 2000 ≤ c) (hS100 : 100 ≤ hbS c ξ) :
    liftEps c < tauStar (Real.log (Real.pi ^ 2 * ξ)) / 2 := by
  have hc0 : 0 < c := by linarith
  have hε := liftEps_pos hc0
  have hε12 := hb_eps_small hc2k
  have hS0 : 0 < hbS c ξ := by linarith
  have hL := hb_L_pos hc0 hS0
  have hLeq := hb_L_eq (ξ := ξ) hc0
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi < 3.15 := Real.pi_lt_d2
  set ε := liftEps c
  set L := Real.log (Real.pi ^ 2 * ξ)
  by_cases hL1 : L ≤ 1
  · have : tauStar L = Real.sqrt L / Real.pi := by simp [tauStar, hL1]
    rw [this]
    have h1 : 2 * Real.pi * ε < Real.sqrt L := by
      rw [Real.lt_sqrt (by positivity)]
      rw [hLeq]
      have : 4 < hbS c ξ := by linarith
      nlinarith only [mul_pos (mul_pos (by positivity : 0 < Real.pi ^ 2) (by positivity : 0 < ε ^ 2)) (by linarith : 0 < hbS c ξ - 4)]
    rw [div_div, lt_div_iff₀ (by positivity)]; linarith
  · have : tauStar L = Real.exp ((L - 1) / 2) / Real.pi := by simp [tauStar, hL1]
    rw [this]
    have h1 : 1 ≤ Real.exp ((L - 1) / 2) := Real.one_le_exp (by linarith [not_le.mp hL1])
    rw [div_div, lt_div_iff₀ (by positivity)]
    nlinarith

lemma cEps_eq {c : ℝ} (hc : 0 < c) : c * liftEps c = c ^ (2 / 3 : ℝ) := by
  calc c * liftEps c = c ^ (1 : ℝ) * c ^ (-(1 / 3 : ℝ)) := by rw [Real.rpow_one]; rfl
    _ = c ^ (1 + -(1 / 3 : ℝ)) := (Real.rpow_add hc _ _).symm
    _ = c ^ (2 / 3 : ℝ) := by norm_num

lemma hbA_eq_div {c ξ : ℝ} (hc : 0 < c) : hbA c ξ = Real.log (Real.pi ^ 2 * ξ) / liftEps c ^ 2 := by
  have hε := liftEps_pos hc
  have := liftEps_cube_mul hc
  have h3 : c * liftEps c ^ 3 = 1 := by linarith [this]
  unfold hbA
  field_simp
  linear_combination (Real.log (Real.pi ^ 2 * ξ)) * h3

/-- **`O.3(2)`, the `χ_ξ`-part of `I_main` (Piece C).** If the subtracted symbol `G_sm` has `SmoothSymbol` regularity, then
`(2πξ)⁻¹ ∫ χ(v/v_*) K₀ W dv = γ₀ √π A^{-3/2}/(2π ξ) + O(S^{-1/2} A^{-3/2}/(2π ξ))` for `δ₀ = β₁ K ε / 2`, `K ≥ 1`, `c ≥ max(2000, 8K³)`, `S ≥ 100`,
with `v_* = τ_*(L)/ε`; `C` depends on `CG`, `γ₀`, `χ`, `Kχ`, `m` only. -/
theorem hb_inner (X : ℝ → ℝ) (γ₀ CG : ℝ) {χ : ℝ → ℝ} {Kχ : ℝ} (hχ : CutoffData χ Kχ)
    (hG : SmoothSymbol (fun v : ℝ => airyTwistedLaplaceC X ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) +
        (γ₀ : ℂ) * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) * Complex.exp (Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) * (χ v : ℂ)) CG)
    (m : ℕ) :
    ∃ C > 0, ∀ {K c ξ : ℝ}, 1 ≤ K → 8 * K ^ 3 ≤ c → 2000 ≤ c → 0 < ξ → 100 ≤ hbS c ξ →
      ‖((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * (∫ v : ℝ, (χ (v / (tauStar (Real.log (Real.pi ^ 2 * ξ)) / liftEps c)) : ℂ) *
          iMainIntegrand X (ceBeta1 * K * liftEps c / 2) m c ξ v) -
        ((γ₀ * Real.sqrt Real.pi * hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) : ℝ) : ℂ)‖ ≤
      C * hbS c ξ ^ (-(1 / 2 : ℝ)) * (hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ)) := by
  obtain ⟨B0, B1, B2, hB⟩ := pcAmp_bd2 m
  obtain ⟨M, hM⟩ := exists_uniform_bounds_chi_pcH m hχ.contDiff hχ.zero
  let Cin : ℝ := smoothConst (2 * CG * (Kχ * B0 + (Kχ * B0 + Kχ * B1) + (Kχ * B0 + 2 * (Kχ * B1) + Kχ * B2))) 1 +
    |γ₀| * ((12 * (∫ t in Set.Ioi (0 : ℝ), fresnelDom t) + 2) * M)
  refine ⟨|Cin| / Real.pi + 1, by positivity, fun {K c ξ} hK hc8 hc2k hξ hS100 => ?_⟩
  have hc0 : 0 < c := by linarith
  have hc2 : 2 ≤ c := by linarith
  have hε := liftEps_pos hc0
  have hKε := hb_K_eps hK hc8
  have hS0 : 0 < hbS c ξ := by linarith
  have hL := hb_L_pos hc0 hS0
  have hετ := hb_eps_lt_tau (ξ := ξ) hc2k hS100
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have hAS := hbA_eq (ξ := ξ) hc0
  have hA100 : 900 ≤ hbA c ξ := by
    rw [hAS]
    have hπ2 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith only [hpi3]
    linarith only [mul_le_mul hπ2 hS100 (by norm_num) (sq_nonneg Real.pi)]
  have hApos : 0 < hbA c ξ := by linarith
  set ε := liftEps c with hεdef
  set L := Real.log (Real.pi ^ 2 * ξ) with hLdef
  set τs := tauStar L with hτsdef
  have hτs : 0 < τs := tauStar_pos hL
  set vs := τs / ε with hvsdef
  have hvs2 : 2 ≤ vs := by rw [hvsdef, le_div_iff₀ hε]; linarith
  have hδ : 0 < ceBeta1 * K * ε / 2 := by have := ceBeta1_pos; positivity
  have hδ4 : ceBeta1 * K * ε / 2 ≤ 4 := by
    have := ceBeta1_lt_eight
    linarith only [this, mul_le_mul_of_nonneg_left hKε ceBeta1_pos.le]
  obtain ⟨hφ, b0, b1, b2⟩ := hM hδ hδ4 hc2
  have hcase : (1 + vs) ^ (1 / 2 : ℝ) ≤ 1 * hbA c ξ ^ 2 ∨ c ^ (2 / 3 : ℝ) ≤ hbA c ξ := by
    by_cases hL1 : L ≤ 1
    · left
      have hts : τs = Real.sqrt L / Real.pi := by simp [hτsdef, tauStar, hL1]
      -- `A = (√L/ε)²` and `vs = (√L/ε)/π ≤ A`
      have hAdiv : hbA c ξ = (Real.sqrt L / ε) ^ 2 := by
        rw [hbA_eq_div hc0, div_pow, Real.sq_sqrt hL.le]
      set y : ℝ := Real.sqrt L / ε with hy
      have hy0 : 0 ≤ y := by positivity
      have hy1 : 1 ≤ y := by
        by_contra hlt; push Not at hlt
        have : y ^ 2 < 1 := by nlinarith only [hlt, hy0]
        linarith [hAdiv]
      have hvsy : vs = y / Real.pi := by rw [hvsdef, hts, hy]; field_simp
      have hvsA : vs ≤ hbA c ξ := by
        rw [hvsy, hAdiv]
        calc y / Real.pi ≤ y := div_le_self hy0 (by linarith)
          _ ≤ y ^ 2 := by nlinarith only [hy1, hy0]
      have h1 : (1 + vs) ^ (1 / 2 : ℝ) ≤ 1 + vs := by
        calc (1 + vs) ^ (1 / 2 : ℝ) ≤ (1 + vs) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
          _ = 1 + vs := Real.rpow_one _
      calc (1 + vs) ^ (1 / 2 : ℝ) ≤ 1 + vs := h1
        _ ≤ 2 * hbA c ξ := by linarith
        _ ≤ 1 * hbA c ξ ^ 2 := by nlinarith only [hA100]
    · right
      have hL1' : 1 < L := not_le.mp hL1
      have : hbA c ξ = c ^ (2 / 3 : ℝ) * L := by unfold hbA; rw [← cEps_eq hc0]
      rw [this]
      exact le_mul_of_one_le_right (by positivity) hL1'.le
  have hmain := pieceC_main_term_smooth X (ceBeta1 * K * ε / 2) m hc2 hξ hL γ₀ χ χ vs (by linarith)
    (fun v hv => by
      have hv1 : |v| ≤ 1 := by
        by_contra h; exact hv (hχ.zero v (not_le.mp h))
      refine hχ.one _ ?_
      rw [abs_div, abs_of_pos (by linarith : 0 < vs), div_le_iff₀ (by linarith)]
      linarith)
    (hχ.one 0 (by simp)) hχ.zero hχ.contDiff hχ.zero hχ.b0 hχ.b1 hχ.b2 hχ.contDiff.continuous hφ b0 b1 b2
    (A := hbA c ξ) rfl (by linarith) (hB hδ hδ4 hc2) hG (le_of_eq (by rw [hvsdef]; field_simp; rfl)) (by norm_num : (0 : ℝ) ≤ 1) hcase
  have hA32 : 1 / hbA c ξ ^ 2 = hbA c ξ ^ (-(1 / 2 : ℝ)) * hbA c ξ ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_add hApos, show (-(1 / 2 : ℝ) + -(3 / 2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hApos.le,
      Real.rpow_natCast, one_div]
  have hAhalf : hbA c ξ ^ (-(1 / 2 : ℝ)) = Real.pi⁻¹ * hbS c ξ ^ (-(1 / 2 : ℝ)) := by
    rw [hAS, Real.mul_rpow (by positivity) hS0.le]
    congr 1
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq Real.pi_pos.le]
  refine hmain.trans ?_
  have hξπ : 0 < 2 * Real.pi * ξ := by positivity
  have hS12 : 0 ≤ hbS c ξ ^ (-(1 / 2 : ℝ)) := by positivity
  have hA32' : 0 ≤ hbA c ξ ^ (-(3 / 2 : ℝ)) := by positivity
  calc (smoothConst (2 * CG * (Kχ * B0 + (Kχ * B0 + Kχ * B1) + (Kχ * B0 + 2 * (Kχ * B1) + Kχ * B2))) 1 +
        |γ₀| * ((12 * (∫ t in Set.Ioi (0 : ℝ), fresnelDom t) + 2) * M)) / (2 * Real.pi * ξ * hbA c ξ ^ 2)
      = Cin * (1 / hbA c ξ ^ 2) / (2 * Real.pi * ξ) := by simp only [Cin]; field_simp
    _ ≤ |Cin| * (1 / hbA c ξ ^ 2) / (2 * Real.pi * ξ) := by
        gcongr
        exact le_abs_self _
    _ = (|Cin| / Real.pi) * hbS c ξ ^ (-(1 / 2 : ℝ)) * (hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ)) := by
        rw [hA32, hAhalf]; field_simp
    _ ≤ (|Cin| / Real.pi + 1) * hbS c ξ ^ (-(1 / 2 : ℝ)) * (hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ)) := by
        gcongr
        linarith

/-! ### The assembly -/

/-- **`O.3(2)`, `(e4)`, absolute form, from the square-root data.**  Let `X` have `HasU2`, with `X̃ = A + y^{1/2} B` on the closed right half-plane
(`A, B` entire, `B(0) = b₀`) and the `(e27)` bounds on the imaginary axis (`ImagAxisBounds`).  With `γ₀ = -c_s^{1/2} b₀` and
`𝒜 = γ₀ √π A^{-3/2}/(2π ξ)` (`A = π² S`), for `δ₀ = β₁ K ε / 2`, `K, M₁ ≥ 1`, `c ≥ max(2000, 8K³)`, `S ≥ max(100, M₁K^{-2}c^{2/3})`:
`|I_main - 𝒜| ≤ C [M₁^{-m/2} + K^{-m} + S^{-1/2}] · A^{-3/2}/(2π ξ)`. -/
theorem hb_estimate_of_sqData {X : ℝ → ℝ} (hU2 : HasU2 X) {A B : ℂ → ℂ} {b0 : ℝ} (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) (hb : B 0 = b0)
    (hT : ∀ y : ℂ, 0 ≤ y.re → airyTwistedLaplaceC X y = A y + y ^ (1 / 2 : ℂ) * B y)
    (himag : ImagAxisBounds (airyTwistedLaplaceC X)) {m : ℕ} (hm : 1 ≤ m) :
    ∃ C > 0, ∀ {K M₁ c ξ : ℝ}, 1 ≤ K → 1 ≤ M₁ → 8 * K ^ 3 ≤ c → 2000 ≤ c → 0 < ξ → 100 ≤ hbS c ξ →
      M₁ * (K ^ 2)⁻¹ * c ^ (2 / 3 : ℝ) ≤ hbS c ξ →
      ‖iMain X (ceBeta1 * K * liftEps c / 2) m c ξ -
          ((-(b0 * ceCs ^ (1 / 2 : ℝ)) * Real.sqrt Real.pi * hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) : ℝ) : ℂ)‖ ≤
        C * (M₁ ^ (-((m : ℝ) / 2)) + K ^ (-(m : ℝ)) + hbS c ξ ^ (-(1 / 2 : ℝ))) *
          (hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ)) := by
  obtain ⟨χ, Kχ, hχ⟩ := exists_cutoffData
  obtain ⟨CG, hCG⟩ := smoothSymbol_of_sqData hA hB hb hT himag hχ.contDiff hχ.one hχ.zero
  obtain ⟨Ct, hCt, htail⟩ := symbolTail_of_sqData hA hB hT himag
  obtain ⟨Co, hCo, hout⟩ := hb_outer hCt.le htail hχ hm
  obtain ⟨Ci, hCi, hin⟩ := hb_inner X (-(b0 * ceCs ^ (1 / 2 : ℝ))) CG hχ hCG m
  refine ⟨Co + Ci, by positivity, fun {K M₁ c ξ} hK hM hc8 hc2k hξ hS100 hMS => ?_⟩
  have hc0 : 0 < c := by linarith
  have hε := liftEps_pos hc0
  have hL := hb_L_pos hc0 (by linarith : 0 < hbS c ξ)
  have hτ := tauStar_pos hL
  have hKε := hb_K_eps hK hc8
  have hδ : 0 ≤ ceBeta1 * K * liftEps c / 2 := by have := ceBeta1_pos; positivity
  have hint := hU2.integrable_iMainIntegrand hδ m hc0 hξ
  have hχc : Continuous fun v : ℝ => (χ (liftEps c * v / tauStar (Real.log (Real.pi ^ 2 * ξ))) : ℂ) :=
    Complex.continuous_ofReal.comp (hχ.contDiff.continuous.comp ((continuous_const.mul continuous_id).div_const _))
  have hχb : ∀ v : ℝ, ‖(χ (liftEps c * v / tauStar (Real.log (Real.pi ^ 2 * ξ))) : ℂ)‖ ≤ Kχ := fun v => by
    simpa [Complex.norm_real] using hχ.b0 _
  have hi1 : Integrable fun v : ℝ => (χ (liftEps c * v / tauStar (Real.log (Real.pi ^ 2 * ξ))) : ℂ) *
      iMainIntegrand X (ceBeta1 * K * liftEps c / 2) m c ξ v :=
    hint.bdd_mul hχc.aestronglyMeasurable (ae_of_all _ hχb)
  have hi2 : Integrable fun v : ℝ => ((1 - χ (liftEps c * v / tauStar (Real.log (Real.pi ^ 2 * ξ))) : ℝ) : ℂ) *
      iMainIntegrand X (ceBeta1 * K * liftEps c / 2) m c ξ v := by
    have := hint.sub hi1
    refine this.congr (ae_of_all _ fun v => ?_)
    simp only [Pi.sub_apply]; push_cast; ring
  have hsplit : iMain X (ceBeta1 * K * liftEps c / 2) m c ξ =
      ((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * (∫ v : ℝ, (χ (v / (tauStar (Real.log (Real.pi ^ 2 * ξ)) / liftEps c)) : ℂ) *
          iMainIntegrand X (ceBeta1 * K * liftEps c / 2) m c ξ v) +
      ((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, ((1 - χ (liftEps c * v / tauStar (Real.log (Real.pi ^ 2 * ξ))) : ℝ) : ℂ) *
          iMainIntegrand X (ceBeta1 * K * liftEps c / 2) m c ξ v := by
    unfold iMain
    rw [← mul_add]
    congr 1
    have hfe : ∀ v : ℝ, v / (tauStar (Real.log (Real.pi ^ 2 * ξ)) / liftEps c) = liftEps c * v / tauStar (Real.log (Real.pi ^ 2 * ξ)) := fun v => by
      rw [div_div_eq_mul_div]; ring_nf
    simp only [hfe]
    rw [← integral_add hi1 hi2]
    congr 1; ext v; push_cast; ring
  have h1 := hin hK hc8 hc2k hξ hS100
  have h2 := hout hK hM hc8 hc2k hξ hS100 hMS
  rw [hsplit, add_sub_right_comm]
  refine (norm_add_le _ _).trans ?_
  have hP : 0 ≤ hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) := by
    have : 0 < hbA c ξ := by rw [hbA_eq hc0]; have := Real.pi_pos; positivity
    positivity
  have hS12 : 0 ≤ hbS c ξ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hM1 : 0 ≤ M₁ ^ (-((m : ℝ) / 2)) := Real.rpow_nonneg (by linarith) _
  have hK1 : 0 ≤ K ^ (-(m : ℝ)) := Real.rpow_nonneg (by linarith) _
  linarith [mul_nonneg hM1 hP, mul_nonneg hK1 hP, mul_nonneg hS12 hP, mul_nonneg hCo.le hP, mul_nonneg hCi.le hP,
    mul_nonneg (mul_nonneg hCo.le hM1) hP, mul_nonneg (mul_nonneg hCo.le hK1) hP, mul_nonneg (mul_nonneg hCi.le hS12) hP,
    mul_nonneg (mul_nonneg hCo.le hS12) hP, mul_nonneg (mul_nonneg hCi.le hM1) hP, mul_nonneg (mul_nonneg hCi.le hK1) hP]

/-- **`O.3(2)`, `(e4)`, for every one-level seed** `a f₁ + b g₁ + c g₁'` (absolute form).  The leading coefficient `γ₀` is the square-root
coefficient `-c_s^{1/2} B(0)` of the seed's twisted Laplace transform; the constants `γ₀, C` depend on the seed `(a, b, c₀)` and on `m`, and not on
`K, M₁, c, ξ`. Not formalised: the identification `γ₀ = c_s^{1/2} 2^{2/3} π^{-1/2} β_∞(F)`, uniformity of `C` over a bounded family of seeds, and the `L ≥ L₀`
second claim of `O.3`(2). -/
theorem hb_estimate_airySeed (a b c₀ : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    ∃ γ₀ : ℝ, ∃ C > 0, ∀ {K M₁ c ξ : ℝ}, 1 ≤ K → 1 ≤ M₁ → 8 * K ^ 3 ≤ c → 2000 ≤ c → 0 < ξ → 100 ≤ hbS c ξ →
      M₁ * (K ^ 2)⁻¹ * c ^ (2 / 3 : ℝ) ≤ hbS c ξ →
      ‖iMain (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m c ξ -
          ((γ₀ * Real.sqrt Real.pi * hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) : ℝ) : ℂ)‖ ≤
        C * (M₁ ^ (-((m : ℝ) / 2)) + K ^ (-(m : ℝ)) + hbS c ξ ^ (-(1 / 2 : ℝ))) *
          (hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ)) := by
  obtain ⟨A, B, hA, hB, ⟨b0, hb⟩, hT⟩ := (airySeedU2_sqForm a b c₀).closed (hasU2_airySeedU2 a b c₀).continuousOn
  obtain ⟨C, hC, h⟩ := hb_estimate_of_sqData (hasU2_airySeedU2 a b c₀) hA hB hb hT (airySeedU2_imagAxisBounds a b c₀) hm
  exact ⟨-(b0 * ceCs ^ (1 / 2 : ℝ)), C, hC, h⟩

/-- **`(e4)` for every one-level seed, with the leading coefficient pinned**: `γ₀ = (c₀ - a) · 2 k c_A c_s^{1/2}` for `a f₁ + b g₁ + c₀ g₁'`
(from `airySeedU2_sqFormAt`: `B 0 = (a - c₀) · 2 k c_A`). -/
theorem hb_estimate_airySeed_val (a b c₀ : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    ∃ C > 0, ∀ {K M₁ c ξ : ℝ}, 1 ≤ K → 1 ≤ M₁ → 8 * K ^ 3 ≤ c → 2000 ≤ c → 0 < ξ → 100 ≤ hbS c ξ →
      M₁ * (K ^ 2)⁻¹ * c ^ (2 / 3 : ℝ) ≤ hbS c ξ →
      ‖iMain (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m c ξ -
          ((((c₀ - a) * (2 * ceK * cA * ceCs ^ (1 / 2 : ℝ))) * Real.sqrt Real.pi * hbA c ξ ^ (-(3 / 2 : ℝ)) /
            (2 * Real.pi * ξ) : ℝ) : ℂ)‖ ≤
        C * (M₁ ^ (-((m : ℝ) / 2)) + K ^ (-(m : ℝ)) + hbS c ξ ^ (-(1 / 2 : ℝ))) *
          (hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ)) := by
  obtain ⟨A, B, hA, hB, hb, hT⟩ := (airySeedU2_sqFormAt a b c₀).closed (hasU2_airySeedU2 a b c₀).continuousOn
  obtain ⟨C, hC, h⟩ := hb_estimate_of_sqData (hasU2_airySeedU2 a b c₀) hA hB hb hT (airySeedU2_imagAxisBounds a b c₀) hm
  refine ⟨C, hC, fun {K M₁ c ξ} hK hM hc8 hc2k hξ hS hMS => ?_⟩
  have e : (c₀ - a) * (2 * ceK * cA * ceCs ^ (1 / 2 : ℝ)) = -(((a - c₀) * (2 * ceK * cA)) * ceCs ^ (1 / 2 : ℝ)) := by ring
  rw [e]
  exact h hK hM hc8 hc2k hξ hS hMS

/-- **`(e4)`, relative form.**  If `γ₀ ≠ 0` (the paper's `β_∞(F) ≥ β_min > 0`), the absolute bound is a relative one:
`|I_main - 𝒜| ≤ C' [M₁^{-m/2} + K^{-m} + S^{-1/2}] |𝒜|` with `𝒜 = γ₀ √π A^{-3/2}/(2π ξ)`. -/
theorem hb_estimate_airySeed_rel (a b c₀ : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    ∃ γ₀ : ℝ, (γ₀ ≠ 0 → ∃ C > 0, ∀ {K M₁ c ξ : ℝ}, 1 ≤ K → 1 ≤ M₁ → 8 * K ^ 3 ≤ c → 2000 ≤ c → 0 < ξ → 100 ≤ hbS c ξ →
      M₁ * (K ^ 2)⁻¹ * c ^ (2 / 3 : ℝ) ≤ hbS c ξ →
      ‖iMain (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m c ξ -
          ((γ₀ * Real.sqrt Real.pi * hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) : ℝ) : ℂ)‖ ≤
        C * (M₁ ^ (-((m : ℝ) / 2)) + K ^ (-(m : ℝ)) + hbS c ξ ^ (-(1 / 2 : ℝ))) *
          ‖((γ₀ * Real.sqrt Real.pi * hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) : ℝ) : ℂ)‖) := by
  obtain ⟨γ₀, C, hC, h⟩ := hb_estimate_airySeed a b c₀ hm
  refine ⟨γ₀, fun hγ => ⟨C / (|γ₀| * Real.sqrt Real.pi), by positivity, fun {K M₁ c ξ} hK hM hc8 hc2k hξ hS hMS => ?_⟩⟩
  refine (h hK hM hc8 hc2k hξ hS hMS).trans (le_of_eq ?_)
  have hc0 : 0 < c := by linarith
  have hS0 : 0 < hbS c ξ := by linarith
  have hApos : 0 < hbA c ξ := by rw [hbA_eq hc0]; have := Real.pi_pos; positivity
  have hP : 0 ≤ hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) := by positivity
  have hsq : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hγ' : 0 < |γ₀| := abs_pos.mpr hγ
  rw [Complex.norm_real, Real.norm_eq_abs, mul_div_assoc, abs_mul, abs_mul, abs_of_pos hsq, abs_of_nonneg hP]
  field_simp

/-- **`(e4)` for the `m₀ = 1` Hermite–Biehler seed** (the one-level seed `F_δ` with `δ`-dependent coefficients), absolute form. The seed
parameters `γ₁, γ₂, δ, r` are fixed before `C` is chosen, so `C` is not uniform in `δ` (the paper's `δ = K c^{-1/3}` varies with `c`). -/
theorem hb_estimate_hbSeed_m1 (γ₁ γ₂ δ r : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    ∃ γ₀ : ℝ, ∃ C > 0, ∀ {K M₁ c ξ : ℝ}, 1 ≤ K → 1 ≤ M₁ → 8 * K ^ 3 ≤ c → 2000 ≤ c → 0 < ξ → 100 ≤ hbS c ξ →
      M₁ * (K ^ 2)⁻¹ * c ^ (2 / 3 : ℝ) ≤ hbS c ξ →
      ‖iMain (fun u : ℝ => -ceF1 u - γ₁ * δ * ceG1 (airyZero 1) u + γ₂ * δ * ceSb 1 u + r * ceG1 (airyZero 1) u)
          (ceBeta1 * K * liftEps c / 2) m c ξ -
          ((γ₀ * Real.sqrt Real.pi * hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) : ℝ) : ℂ)‖ ≤
        C * (M₁ ^ (-((m : ℝ) / 2)) + K ^ (-(m : ℝ)) + hbS c ξ ^ (-(1 / 2 : ℝ))) *
          (hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ)) := by
  rw [hbSeed_m1_eq_airySeedU2]; exact hb_estimate_airySeed _ _ _ hm

/-- info: 'FormalResearch.CohnElkies.hb_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.hb_outer
/-- info: 'FormalResearch.CohnElkies.hb_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.hb_inner
/-- info: 'FormalResearch.CohnElkies.hb_estimate_of_sqData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.hb_estimate_of_sqData
/-- info: 'FormalResearch.CohnElkies.hb_estimate_airySeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.hb_estimate_airySeed
/-- info: 'FormalResearch.CohnElkies.hb_estimate_airySeed_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hb_estimate_airySeed_val
/-- info: 'FormalResearch.CohnElkies.hb_estimate_airySeed_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.hb_estimate_airySeed_rel
/-- info: 'FormalResearch.CohnElkies.hb_estimate_hbSeed_m1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.hb_estimate_hbSeed_m1

end FormalResearch.CohnElkies
