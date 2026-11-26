module

public import FormalResearch.ModularBootstrap.StripBand.StripPoissonRep
public import FormalResearch.ModularBootstrap.StripBand.BandReductionBV
public import FormalResearch.TwoEdgeBootstrap.EdgeOsc
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# Unified Strip Band Reduction (Proposition TE.3(1))

Source: `CFT/common/two_edge_bootstrap.tex` (Proposition `TE.3` `teb:mellin`, part `(1)`,
`(MS1)`–`(MS2)`, and `(TE.9)`, l.420–472).

* `BandReductionParams`: fixed constants `(M, b, κ_ζ, A₀, C_W, C_a, c₁, c₂, C_ν, κ_sub, C_τ)`.
* `BandReductionInstance`: strip density `(W̃_c, dm)` at scale `c ≥ 1` satisfying `(MS1)`–`(MS2)`
  and the `τ₀` band/threshold bounds.
* `teb_band_reduction`: **Proposition TE.3(1)** (`TE.9`), proving
  `‖W̃_c(ζ₀)‖ ≤ C_Y c^{-5/6} (c^{1/3}(B₁ + B₂) + c^{-1/6}) / cos ψ`
  and `≤ C_Y c^{-5/6} (c^{1/3}(B₁ + B₂) / cos ψ + c^{-1/12})` on the sector `𝔖`.
* `teb_band_reduction_quantified`: quantified large-`c` form (`∃ C_Y c₂'`).
* `bandReductionInstance_nonvacuous`: concrete witness proving the hypotheses are satisfiable.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real Interval Pointwise

namespace FormalResearch.ModularBootstrap.StripBand

open FormalResearch.StripPoisson
open FormalResearch.TwoEdgeBootstrap

section ParamsAndInstance

/-- Fixed constants for Proposition `TE.3(1)` (`two_edge_bootstrap.tex` l.421–449). -/
structure BandReductionParams where
  M : ℝ
  b : ℝ
  κ_ζ : ℝ
  A_0 : ℝ
  C_W : ℝ
  C_a : ℝ
  c_1 : ℝ
  c_2 : ℝ
  C_ν : ℝ
  κ_sub : ℝ
  C_τ : ℝ
  hM : 0 ≤ M
  hb : 0 < b
  hκ_ζ : 0 < κ_ζ
  hA_0 : 0 < A_0
  hC_W : 0 < C_W
  hC_a : 0 < C_a
  hc_1 : 0 < c_1
  hc_2 : 0 < c_2
  hC_ν : 0 < C_ν
  hκ_sub : 0 < κ_sub
  hC_τ : 0 < C_τ

/-- Annulus scale `ρ_R := κ_ζ c^{-1/3} √R`. -/
noncomputable def rhoR (P : BandReductionParams) (c R : ℝ) : ℝ :=
  P.κ_ζ * c ^ (-(1 / 3 : ℝ)) * √R

/-- Packaged `(MS1)`–`(MS2)` and `τ₀` hypotheses for a strip density `(W̃_c, dm)` at scale `c`
(`two_edge_bootstrap.tex`, Proposition `TE.3(1)`). The real signed measure `dm` on `(0, ∞)` is
represented by its positive and negative parts `(dmPos, dmNeg)`. -/
structure BandReductionInstance (P : BandReductionParams) where
  c : ℝ
  ε : ℝ
  R : ℝ
  hc : 1 ≤ c
  hε : ε = 1 ∨ ε = -1
  hR_lb : P.b ^ 2 * c ^ (2 / 3 : ℝ) ≤ R
  hR_ub : R ≤ P.b ^ 2 * c ^ (2 / 3 : ℝ) + 1
  hρR_ub : 2 * rhoR P c R ≤ 0.035
  -- (MS1): strip symmetry and polynomial growth
  W_tilde : ℂ → ℂ
  hW_cont : ContinuousOn W_tilde {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1}
  hW_holo : DifferentiableOn ℂ W_tilde {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1}
  hW_symm : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → W_tilde (1 - ζ) = (ε : ℂ) * W_tilde ζ
  hW_bound : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖W_tilde ζ‖ ≤ P.C_W * (1 + ‖ζ‖) ^ P.M
  -- (MS2): signed measure `dm = dmPos - dmNeg` on `(0, ∞)`
  dmPos : Measure ℝ
  dmNeg : Measure ℝ
  hdmPos_fin : IsFiniteMeasure dmPos
  hdmNeg_fin : IsFiniteMeasure dmNeg
  hdmPos_supp : dmPos (Iic 0) = 0
  hdmNeg_supp : dmNeg (Iic 0) = 0
  hdm_tv : (dmPos univ).toReal + (dmNeg univ).toReal ≤ 1
  T : ℝ
  hdm_nonneg_tail : dmNeg (Ici T) = 0
  -- Sub-Cardy set `E_sub ⊆ (0, T)` and edge kernel `K_edge`
  E_sub : Set ℝ
  hE_sub_meas : MeasurableSet E_sub
  hE_sub_sub : E_sub ⊆ Ioo 0 T
  K_edge : ℝ → ℝ → ℂ
  hK_meas : Measurable (Function.uncurry K_edge)
  hW_edge : ∀ τ : ℝ, W_tilde ((τ : ℂ) * Complex.I) =
    (∫ ξ : ℝ, K_edge τ ξ ∂dmPos) - (∫ ξ : ℝ, K_edge τ ξ ∂dmNeg)
  hK_sub : ∀ ξ ∈ E_sub, ∀ τ : ℝ, ‖K_edge τ ξ‖ ≤ P.C_a * Real.exp (-P.κ_sub * c)
  -- Kernel factorization off `E_sub`
  a_0 : ℝ → ℂ
  a_0' : ℝ → ℂ
  a_2 : ℝ → ℂ
  R_0 : ℝ → ℝ → ℝ
  Phi : ℝ → ℝ → ℝ
  hK_factor : ∀ ξ ∈ Ioi 0 \ E_sub, ∀ τ : ℝ,
    K_edge τ ξ = a_0 τ * a_2 ξ *
      Complex.exp ((c : ℂ) * ((R_0 τ ξ : ℂ) - Complex.I * (Phi τ ξ : ℂ)))
  ha_2_bd : ∀ ξ ∈ Ioi 0 \ E_sub, ‖a_2 ξ‖ ≤ P.C_a
  ha_0_deriv : ∀ τ : ℝ, HasDerivAt a_0 (a_0' τ) τ
  ha_0_bd : ∀ τ : ℝ, ‖a_0 τ‖ + ‖a_0' τ‖ ≤ P.C_a * (1 + |τ|) ^ P.M
  hR_0_nonpos : ∀ ξ ∈ Ioi 0 \ E_sub, ∀ τ : ℝ, R_0 τ ξ ≤ 0
  hR_0_cont : ∀ ξ ∈ Ioi 0 \ E_sub, ContinuousOn (fun τ => R_0 τ ξ) (Ioi 0)
  hR_0_even : ∀ ξ ∈ Ioi 0 \ E_sub, ∀ τ : ℝ, R_0 (-τ) ξ = R_0 τ ξ
  hR_0_unimodal : ∀ ξ ∈ Ioi 0 \ E_sub, ∃ τ_p : ℝ,
    MonotoneOn (fun τ => R_0 τ ξ) (Ioi 0 ∩ Iic τ_p) ∧
    AntitoneOn (fun τ => R_0 τ ξ) (Ioi 0 ∩ Ici τ_p)
  hPhi_odd : ∀ ξ ∈ Ioi 0 \ E_sub, ∀ τ : ℝ, Phi (-τ) ξ = -Phi τ ξ
  -- Coordinate `w = ν(τ)` and dispersion `m(τ)`
  ν : ℝ → ℝ
  ν' : ℝ → ℝ
  invNu' : ℝ → ℝ
  hν_deriv : ∀ τ > 0, HasDerivAt ν (ν' τ) τ
  hν'_cont : ContinuousOn ν' (Ioi 0)
  hν'_inv_pos : ∀ τ > 0, 0 < (ν' τ)⁻¹ ∧ (ν' τ)⁻¹ ≤ P.C_ν
  hν'_inv_deriv : ∀ τ > 0, HasDerivAt (fun t => (ν' t)⁻¹) (invNu' τ) τ
  hinvNu'_cont : ContinuousOn invNu' (Ioi 0)
  hinvNu'_int : ∫ τ in Ioi (0 : ℝ), |invNu' τ| ≤ P.C_ν
  hinvNu'_integrable : IntegrableOn invNu' (Ioi 0)
  μ : ℝ → ℝ
  m : ℝ → ℝ
  m' : ℝ → ℝ
  hPhi_deriv : ∀ ξ ∈ Ioi 0 \ E_sub, ∀ τ > 0, HasDerivAt (fun t => Phi t ξ) (ν' τ * (μ ξ - m τ)) τ
  hm_0 : m 0 = 0
  hm_cont : ContinuousOn m (Ici 0)
  hm_strictMono : StrictMonoOn m (Ici 0)
  hm_deriv : ∀ τ > 0, HasDerivAt m (m' τ) τ
  hm_step : ∀ τ > 0, P.c_1 * min (τ ^ 2) 1 ≤ m τ - m (τ / 2)
  hm_slope : ∀ τ > 0, P.c_2 * τ / (1 + τ ^ 3) ≤ m' τ / ν' τ
  -- Stationary point `τ₀` and band moments `B₁, B₂`
  τ_0 : ℝ → ℝ
  hτ_0_nn : ∀ ξ, 0 ≤ τ_0 ξ
  hτ_0_eq_zero : ∀ ξ, μ ξ ≤ 0 → τ_0 ξ = 0
  hτ_0_root : ∀ ξ, 0 < μ ξ → m (τ_0 ξ) = μ ξ
  u_tilde : ℝ → ℝ
  Delta : ℝ → ℝ
  hτ_0_below : ∀ ξ ∈ Iio T \ E_sub, τ_0 ξ ≤ P.A_0 * c ^ (-(1 / 3 : ℝ))
  hτ_0_band : ∀ ξ ∈ Icc T (Delta (-R)), τ_0 ξ ^ 2 ≤ P.C_τ * c ^ (-(2 / 3 : ℝ)) * (-u_tilde ξ)
  hu_tilde_int : IntegrableOn (fun ξ => -u_tilde ξ) (Icc T (Delta (-R))) dmPos

/-- Band moment `B₁ := R⁻¹ ∫_{[T, Δ(-R)]} (-ũ) dm` (`TE.2` / `teb:bootstrap`). -/
noncomputable def bandB1 {P : BandReductionParams} (I : BandReductionInstance P) : ℝ :=
  I.R⁻¹ * ∫ ξ in Icc I.T (I.Delta (-I.R)), (-I.u_tilde ξ) ∂I.dmPos

/-- Tail moment `B₂ := ∫_{[Δ(-R), ∞)} dm` (`TE.2` / `teb:bootstrap`). -/
noncomputable def bandB2 {P : BandReductionParams} (I : BandReductionInstance P) : ℝ :=
  (I.dmPos (Ici (I.Delta (-I.R)))).toReal

lemma bandB1_nonneg {P : BandReductionParams} (I : BandReductionInstance P) :
    0 ≤ bandB1 I := by
  unfold bandB1
  have hc_pos : 0 < I.c := lt_of_lt_of_le zero_lt_one I.hc
  have hR_pos : 0 < I.R := lt_of_lt_of_le (by have := P.hb; positivity) I.hR_lb
  refine mul_nonneg (inv_nonneg.mpr hR_pos.le) (setIntegral_nonneg measurableSet_Icc fun ξ hξ => ?_)
  have h1 := I.hτ_0_band ξ hξ
  have h2 : 0 ≤ I.τ_0 ξ ^ 2 := sq_nonneg _
  have hCτ := P.hC_τ
  have hc23 : 0 < I.c ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hc_pos _
  have hmul : 0 ≤ P.C_τ * I.c ^ (-(2 / 3 : ℝ)) * (-I.u_tilde ξ) := h2.trans h1
  exact nonneg_of_mul_nonneg_right hmul (mul_pos hCτ hc23)

lemma bandB2_nonneg {P : BandReductionParams} (I : BandReductionInstance P) :
    0 ≤ bandB2 I :=
  ENNReal.toReal_nonneg

end ParamsAndInstance

section CoordinateInverse

private lemma strictMonoOn_nu {P : BandReductionParams} (I : BandReductionInstance P) :
    StrictMonoOn I.ν (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · intro τ hτ
    exact (I.hν_deriv τ hτ).continuousAt.continuousWithinAt
  · intro τ hτ
    rw [interior_Ioi] at hτ
    rw [(I.hν_deriv τ hτ).deriv]
    exact inv_pos.mp (I.hν'_inv_pos τ hτ).1

private lemma continuousAt_invFunOn_nu {P : BandReductionParams} (I : BandReductionInstance P)
    {τ₀ : ℝ} (hτ₀ : 0 < τ₀) :
    ContinuousAt (Function.invFunOn I.ν (Ioi 0)) (I.ν τ₀) ∧
      ∀ᶠ y in 𝓝 (I.ν τ₀), I.ν (Function.invFunOn I.ν (Ioi 0) y) = y := by
  set g := Function.invFunOn I.ν (Ioi 0)
  have hmono := strictMonoOn_nu I
  have hcont : ContinuousOn I.ν (Ioi 0) := fun τ hτ =>
    (I.hν_deriv τ hτ).continuousAt.continuousWithinAt
  have hτ₁ : 0 < τ₀ / 2 := by linarith
  have hτ₂ : τ₀ / 2 < 2 * τ₀ := by linarith
  have hν_lt1 : I.ν (τ₀ / 2) < I.ν τ₀ := hmono hτ₁ hτ₀ (by linarith)
  have hν_lt2 : I.ν τ₀ < I.ν (2 * τ₀) := hmono hτ₀ (mul_pos zero_lt_two hτ₀) (by linarith)
  have hsub_img : Ioo (I.ν (τ₀ / 2)) (I.ν (2 * τ₀)) ⊆ I.ν '' Ioi 0 := by
    intro y hy
    have hIcc_sub : Icc (τ₀ / 2) (2 * τ₀) ⊆ Ioi 0 := fun t ht => lt_of_lt_of_le hτ₁ ht.1
    have hmem := intermediate_value_Ioo hτ₂.le (hcont.mono hIcc_sub) hy
    exact ⟨hmem.choose, hIcc_sub (Ioo_subset_Icc_self hmem.choose_spec.1), hmem.choose_spec.2⟩
  have hev : ∀ᶠ y in 𝓝 (I.ν τ₀), I.ν (g y) = y := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hν_lt1, hν_lt2⟩] with y hy
    exact Function.invFunOn_eq (hsub_img hy)
  refine ⟨?_, hev⟩
  rw [Metric.continuousAt_iff]
  intro ε hε
  set ε' := min (ε / 2) (τ₀ / 2)
  have hε'_pos : 0 < ε' := lt_min (half_pos hε) (half_pos hτ₀)
  have ha_pos : 0 < τ₀ - ε' := by linarith [min_le_right (ε / 2) (τ₀ / 2)]
  have hb_pos : 0 < τ₀ + ε' := by linarith
  have hν_a : I.ν (τ₀ - ε') < I.ν τ₀ := hmono ha_pos hτ₀ (by linarith)
  have hν_b : I.ν τ₀ < I.ν (τ₀ + ε') := hmono hτ₀ hb_pos (by linarith)
  set δ := min (I.ν τ₀ - I.ν (τ₀ - ε')) (I.ν (τ₀ + ε') - I.ν τ₀)
  have hδ_pos : 0 < δ := lt_min (sub_pos.mpr hν_a) (sub_pos.mpr hν_b)
  have hsub_sub : Ioo (I.ν (τ₀ - ε')) (I.ν (τ₀ + ε')) ⊆ I.ν '' Ioi 0 := by
    intro y hy
    have hIcc_sub : Icc (τ₀ - ε') (τ₀ + ε') ⊆ Ioi 0 := fun t ht => lt_of_lt_of_le ha_pos ht.1
    have hmem := intermediate_value_Ioo (by linarith : τ₀ - ε' ≤ τ₀ + ε') (hcont.mono hIcc_sub) hy
    exact ⟨hmem.choose, hIcc_sub (Ioo_subset_Icc_self hmem.choose_spec.1), hmem.choose_spec.2⟩
  refine ⟨δ, hδ_pos, fun {y} hy => ?_⟩
  rw [Real.dist_eq] at hy ⊢
  have hy_mem : y ∈ Ioo (I.ν (τ₀ - ε')) (I.ν (τ₀ + ε')) := by
    have h1 : |y - I.ν τ₀| < I.ν τ₀ - I.ν (τ₀ - ε') := hy.trans_le (min_le_left _ _)
    have h2 : |y - I.ν τ₀| < I.ν (τ₀ + ε') - I.ν τ₀ := hy.trans_le (min_le_right _ _)
    rcases abs_lt.mp h1 with ⟨h1l, _⟩
    rcases abs_lt.mp h2 with ⟨_, h2r⟩
    exact ⟨by linarith, by linarith⟩
  have h_gy_mem : g y ∈ Ioi 0 := Function.invFunOn_mem (hsub_sub hy_mem)
  have h_eq_y : I.ν (g y) = y := Function.invFunOn_eq (hsub_sub hy_mem)
  have h_eq_0 : g (I.ν τ₀) = τ₀ := hmono.injOn (Function.invFunOn_mem ⟨τ₀, hτ₀, rfl⟩) hτ₀
    (Function.invFunOn_eq ⟨τ₀, hτ₀, rfl⟩)
  have h_lt1 : τ₀ - ε' < g y := by
    by_contra hle
    have hge : I.ν (g y) ≤ I.ν (τ₀ - ε') := hmono.monotoneOn h_gy_mem ha_pos (not_lt.mp hle)
    linarith [hy_mem.1]
  have h_lt2 : g y < τ₀ + ε' := by
    by_contra hle
    have hge : I.ν (τ₀ + ε') ≤ I.ν (g y) := hmono.monotoneOn hb_pos h_gy_mem (not_lt.mp hle)
    linarith [hy_mem.2]
  rw [h_eq_0]
  rw [abs_lt]
  constructor <;> linarith [min_le_left (ε / 2) (τ₀ / 2)]

private lemma hasDerivAt_invFunOn_nu {P : BandReductionParams} (I : BandReductionInstance P)
    {τ₀ : ℝ} (hτ₀ : 0 < τ₀) :
    HasDerivAt (Function.invFunOn I.ν (Ioi 0)) (I.ν' τ₀)⁻¹ (I.ν τ₀) := by
  have hmono := strictMonoOn_nu I
  have h0 : Function.invFunOn I.ν (Ioi 0) (I.ν τ₀) = τ₀ :=
    hmono.injOn (Function.invFunOn_mem ⟨τ₀, hτ₀, rfl⟩) hτ₀ (Function.invFunOn_eq ⟨τ₀, hτ₀, rfl⟩)
  obtain ⟨hc, hev⟩ := continuousAt_invFunOn_nu I hτ₀
  have hν'0 : I.ν' τ₀ ≠ 0 := (inv_pos.mp (I.hν'_inv_pos τ₀ hτ₀).1).ne'
  refine HasDerivAt.of_local_left_inverse hc ?_ hν'0 hev
  rw [h0]
  exact I.hν_deriv τ₀ hτ₀

end CoordinateInverse

section MainProof

/-- Constant `C_osc` in `teb_band_reduction` depending only on `P`. -/
noncomputable def tebBandOscConst (P : BandReductionParams) : ℝ :=
  let b₀ := min P.c_1 (P.c_2 / 16)
  let N := P.M + 11 / 2
  let C_amp := 26112 * (2 : ℝ) ^ P.M * P.C_a ^ 2 * P.C_ν
  2 * tebOscConst b₀ N * C_amp

private lemma tebBandOscConst_pos (P : BandReductionParams) : 0 < tebBandOscConst P := by
  unfold tebBandOscConst
  have hb₀ : 0 < min P.c_1 (P.c_2 / 16) := lt_min P.hc_1 (div_pos P.hc_2 (by norm_num))
  have hosc := tebOscConst_pos hb₀ (P.M + 11 / 2)
  have hCa := P.hC_a
  have hCν := P.hC_ν
  positivity

private lemma rpow_mul_exp_neg_sq_le_fac {p q : ℝ} (_hpq : 0 ≤ p + q) {x : ℝ} (hx : 1 ≤ x) :
    x ^ p * Real.exp (-x ^ 2) ≤ (Nat.factorial (Nat.ceil ((p + q) / 2)) : ℝ) * x ^ (-q : ℝ) := by
  set m := Nat.ceil ((p + q) / 2)
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hm_ge : (p + q) / 2 ≤ (m : ℝ) := Nat.le_ceil _
  have hm2 : p + q ≤ (2 * m : ℝ) := by linarith
  have hpow_fac : (x ^ 2) ^ m / (Nat.factorial m : ℝ) ≤ Real.exp (x ^ 2) :=
    Real.pow_div_factorial_le_exp (x ^ 2) (sq_nonneg x) m
  have hfac_pos : (0 : ℝ) < (Nat.factorial m : ℝ) := by positivity
  have hexp_pos : 0 < Real.exp (x ^ 2) := Real.exp_pos _
  have hexp_le : Real.exp (-x ^ 2) ≤ (Nat.factorial m : ℝ) * ((x ^ 2) ^ m)⁻¹ := by
    rw [Real.exp_neg]
    have h1 : (x ^ 2) ^ m ≤ Real.exp (x ^ 2) * (Nat.factorial m : ℝ) :=
      (div_le_iff₀ hfac_pos).mp hpow_fac
    have hpow_pos : 0 < (x ^ 2) ^ m := by positivity
    rw [inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ hexp_pos hpow_pos]
    linarith
  have hinv_pow : ((x ^ 2) ^ m)⁻¹ = x ^ (-(2 * (m : ℝ))) := by
    rw [← pow_mul, ← Real.rpow_natCast x (2 * m), ← Real.rpow_neg hx_pos.le]
    push_cast; rfl
  have hrpow_le : x ^ (p + -(2 * (m : ℝ))) ≤ x ^ (-q : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  calc x ^ p * Real.exp (-x ^ 2)
      ≤ x ^ p * ((Nat.factorial m : ℝ) * x ^ (-(2 * (m : ℝ)))) := by
        rw [← hinv_pow]
        exact mul_le_mul_of_nonneg_left hexp_le (Real.rpow_nonneg hx_pos.le _)
    _ = (Nat.factorial m : ℝ) * (x ^ p * x ^ (-(2 * (m : ℝ)))) := by ring
    _ = (Nat.factorial m : ℝ) * x ^ (p + -(2 * (m : ℝ))) := by
        rw [← Real.rpow_add hx_pos]
    _ ≤ (Nat.factorial m : ℝ) * x ^ (-q : ℝ) := by gcongr

private lemma integrable_one_add_abs_rpow_mul_exp_neg_sq {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun τ : ℝ => (1 + |τ|) ^ p * Real.exp (-τ ^ 2)) := by
  let g : ℝ → ℝ := fun τ => (1 + |τ|) ^ p * Real.exp (-τ ^ 2)
  have hg_cont : Continuous g := by
    unfold g
    refine Continuous.mul ((continuous_const.add continuous_abs).rpow_const fun τ => ?_)
      (Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2)))
    left; change 1 + |τ| ≠ 0; linarith [abs_nonneg τ]
  have h_top : IntegrableOn g (Ioi 1) := by
    set m := Nat.ceil ((p + 2) / 2)
    have hm_int : IntegrableOn (fun τ : ℝ => (2 : ℝ) ^ p * (Nat.factorial m : ℝ) * τ ^ (-2 : ℝ))
        (Ioi 1) :=
      ((integrableOn_Ioi_rpow_iff (s := (-2 : ℝ)) zero_lt_one).mpr (by norm_num)).const_mul _
    refine hm_int.mono' (hg_cont.aestronglyMeasurable.mono_measure Measure.restrict_le_self) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ fun τ (hτ : 1 < τ) => ?_
    have h1 : 1 ≤ τ := hτ.le
    have hg_nn : 0 ≤ g τ := mul_nonneg (Real.rpow_nonneg (by linarith [abs_nonneg τ]) _) (Real.exp_pos _).le
    rw [Real.norm_of_nonneg hg_nn]
    have h1τ : (1 + |τ|) ^ p ≤ (2 : ℝ) ^ p * τ ^ p := by
      rw [abs_of_pos (lt_of_lt_of_le zero_lt_one h1), ← Real.mul_rpow (by norm_num) (by linarith)]
      exact Real.rpow_le_rpow (by linarith) (by linarith) hp
    have hr := rpow_mul_exp_neg_sq_le_fac (p := p) (q := 2) (by linarith) h1
    dsimp [g]
    calc (1 + |τ|) ^ p * Real.exp (-τ ^ 2)
        ≤ (2 : ℝ) ^ p * τ ^ p * Real.exp (-τ ^ 2) := by gcongr
      _ = (2 : ℝ) ^ p * (τ ^ p * Real.exp (-τ ^ 2)) := by ring
      _ ≤ (2 : ℝ) ^ p * ((Nat.factorial m : ℝ) * τ ^ (-2 : ℝ)) := by gcongr
      _ = (2 : ℝ) ^ p * (Nat.factorial m : ℝ) * τ ^ (-2 : ℝ) := by ring
  have h_bot : IntegrableOn g (Iio (-1)) := by
    have hpre : -Ioi (1 : ℝ) = Iio (-1) := by ext x; simp [lt_neg]
    have hev : (fun τ : ℝ => g (-τ)) = g := funext fun τ => by
      dsimp [g]; simp [abs_neg]
    have h_neg := h_top.comp_neg
    rw [hpre] at h_neg
    exact h_neg.congr_fun (fun τ _ => by dsimp [g]; simp [abs_neg]) measurableSet_Iio
  have h_mid : IntegrableOn g (Icc (-1) 1) := hg_cont.continuousOn.integrableOn_Icc
  have h_univ : (univ : Set ℝ) ⊆ Iio (-1) ∪ Icc (-1) 1 ∪ Ioi 1 := fun x _ => by
    rcases lt_or_ge x (-1) with h1 | h1
    · left; left; exact h1
    · rcases le_or_gt x 1 with h2 | h2
      · left; right; exact ⟨h1, h2⟩
      · right; exact h2
  exact integrableOn_univ.mp (((h_bot.union h_mid).union h_top).mono_set h_univ)

private lemma continuous_tebAmp0 (c : ℝ) : Continuous (tebAmp0 c) :=
  continuousOn_univ.mp
    ((tebPrefactor_continuousOn c).comp (by fun_prop) (fun τ _ => by simp [Complex.mul_re]))

private lemma integral_real_eq_pos_add_neg {f : ℝ → ℂ} (hf : Integrable f) :
    ∫ τ : ℝ, f τ = (∫ τ in Ioi (0 : ℝ), f τ) + ∫ τ in Ioi (0 : ℝ), f (-τ) := by
  have h1 : (∫ τ in Ioi (0 : ℝ), f τ) + ∫ τ in (Ioi (0 : ℝ))ᶜ, f τ = ∫ τ : ℝ, f τ :=
    integral_add_compl measurableSet_Ioi hf
  rw [compl_Ioi] at h1
  have hneg : ∫ τ in Iic (0 : ℝ), f τ = ∫ τ in Ioi (0 : ℝ), f (-τ) := by
    have h := integral_comp_neg_Ioi (0 : ℝ) f
    rw [neg_zero] at h
    exact h.symm
  rw [hneg] at h1
  exact h1.symm

private lemma strictMonoOn_invFunOn_nu {P : BandReductionParams} (I : BandReductionInstance P) :
    StrictMonoOn (Function.invFunOn I.ν (Ioi 0)) (I.ν '' Ioi 0) := by
  have hmono := strictMonoOn_nu I
  rintro y₁ hy₁ y₂ hy₂ hy
  have hx₁ : Function.invFunOn I.ν (Ioi 0) y₁ ∈ Ioi 0 := Function.invFunOn_mem hy₁
  have hx₂ : Function.invFunOn I.ν (Ioi 0) y₂ ∈ Ioi 0 := Function.invFunOn_mem hy₂
  by_contra hle
  have hν_le := hmono.monotoneOn hx₂ hx₁ (not_lt.mp hle)
  rw [Function.invFunOn_eq hy₁, Function.invFunOn_eq hy₂] at hν_le
  exact not_lt.mpr hν_le hy

private lemma jchi_half_osc_bound {P : BandReductionParams} (I : BandReductionInstance P)
    {ζ₀ : ℂ} (hσ₀ : 0 < ζ₀.re) (hσ₀_le : ζ₀.re ≤ 0.04)
    {ξ : ℝ} (hξ : ξ ∈ Ioi 0 \ I.E_sub) {sgn : ℝ} (hsgn : sgn = 1 ∨ sgn = -1) :
    let δ := P.A_0 * I.c ^ (-(1 / 3 : ℝ))
    let F : ℝ → ℂ := fun τ => (tebCutoff δ τ : ℂ) *
      (stripPoissonQ ζ₀.re ζ₀.im I.ε τ : ℂ) * tebAmp0 I.c τ * I.K_edge τ ξ
    IntegrableOn (fun τ => F (sgn * τ)) (Ioi 0) →
    ‖∫ τ in Ioi (0 : ℝ), F (sgn * τ)‖ ≤ (tebBandOscConst P / 2 / ζ₀.re) * I.c ^ (5 / 6 : ℝ) *
      (I.c⁻¹ + I.c ^ (-(1 / 2 : ℝ)) * min (I.τ_0 ξ ^ 2) 1 *
        if P.A_0 * I.c ^ (-(1 / 3 : ℝ)) < I.τ_0 ξ then 1 else 0) := by
  intro δ F hF_int
  have hc_pos : 0 < I.c := lt_of_lt_of_le zero_lt_one I.hc
  have hσ₁ : ζ₀.re < 1 := by linarith
  have hδ_pos : 0 < δ := by dsimp [δ]; have := P.hA_0; positivity
  have hsgn_abs : |sgn| = 1 := by rcases hsgn with rfl | rfl <;> norm_num
  have hsgn_sq : sgn ^ 2 = 1 := by rcases hsgn with rfl | rfl <;> norm_num
  have hε_abs : |I.ε| ≤ 1 := by rcases I.hε with hε | hε <;> norm_num [hε]
  have hτ₀_nn : 0 ≤ I.τ_0 ξ := I.hτ_0_nn ξ
  set νInv := Function.invFunOn I.ν (Ioi 0)
  let φ : ℝ → ℝ := fun y => -sgn * I.Phi (νInv y) ξ
  let φ' : ℝ → ℝ := fun y => -sgn * (I.μ ξ - I.m (νInv y))
  let φ'' : ℝ → ℝ := fun y => sgn * (I.m' (νInv y) / I.ν' (νInv y))
  let h0 : ℝ → ℂ := fun τ =>
    (tebCutoff δ τ : ℂ) *
      (stripPoissonQ ζ₀.re ζ₀.im I.ε (sgn * τ) : ℂ) *
      tebAmp0 I.c (sgn * τ) *
      I.a_0 (sgn * τ) *
      ((Real.exp (I.c * I.R_0 τ ξ) : ℝ) : ℂ) *
      (((I.ν' τ)⁻¹ : ℝ) : ℂ)
  have hR0_sgn : ∀ τ : ℝ, I.R_0 (sgn * τ) ξ = I.R_0 τ ξ := fun τ => by
    rcases hsgn with rfl | rfl
    · simp
    · simpa using I.hR_0_even ξ hξ τ
  have hPhi_sgn : ∀ τ : ℝ, I.Phi (sgn * τ) ξ = sgn * I.Phi τ ξ := fun τ => by
    rcases hsgn with rfl | rfl
    · simp
    · simpa using I.hPhi_odd ξ hξ τ
  have hinv_eq : ∀ τ, 0 < τ → νInv (I.ν τ) = τ := fun τ hτ =>
    (strictMonoOn_nu I).injOn (Function.invFunOn_mem ⟨τ, hτ, rfl⟩) hτ
      (Function.invFunOn_eq ⟨τ, hτ, rfl⟩)
  have hF_rw : ∀ τ ∈ Ioi (0 : ℝ),
      I.a_2 ξ * (h0 τ * ((I.ν' τ : ℝ) : ℂ) * Complex.exp (Complex.I * (I.c : ℂ) * (φ (I.ν τ) : ℂ))) =
        F (sgn * τ) := by
    intro τ (hτ : 0 < τ)
    dsimp [F, h0, φ]
    rw [I.hK_factor ξ hξ (sgn * τ), hR0_sgn τ, hPhi_sgn τ, hinv_eq τ hτ]
    have hχ_even : tebCutoff δ (sgn * τ) = tebCutoff δ τ := by
      rcases hsgn with rfl | rfl
      · simp
      · simpa using tebCutoff_even δ τ
    have hν'0 : ((I.ν' τ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (inv_pos.mp (I.hν'_inv_pos τ hτ).1).ne'
    have h_inv_mul : (((I.ν' τ)⁻¹ : ℝ) : ℂ) * ((I.ν' τ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ (by exact_mod_cast hν'0), Complex.ofReal_one]
    have hexp_eq : Complex.exp ((I.c : ℂ) * ((I.R_0 τ ξ : ℂ) - Complex.I * ((sgn * I.Phi τ ξ : ℝ) : ℂ))) =
        ((Real.exp (I.c * I.R_0 τ ξ) : ℝ) : ℂ) *
          Complex.exp (Complex.I * (I.c : ℂ) * ((-sgn * I.Phi τ ξ : ℝ) : ℂ)) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hχ_even, hexp_eq]
    calc I.a_2 ξ *
          (((tebCutoff δ τ : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im I.ε (sgn * τ) : ℂ) *
              tebAmp0 I.c (sgn * τ) * I.a_0 (sgn * τ) *
              ((Real.exp (I.c * I.R_0 τ ξ) : ℝ) : ℂ) * (((I.ν' τ)⁻¹ : ℝ) : ℂ)) *
            ((I.ν' τ : ℝ) : ℂ) *
            Complex.exp (Complex.I * (I.c : ℂ) * ((-sgn * I.Phi τ ξ : ℝ) : ℂ)))
        = (tebCutoff δ τ : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im I.ε (sgn * τ) : ℂ) *
            tebAmp0 I.c (sgn * τ) *
            (I.a_0 (sgn * τ) * I.a_2 ξ *
              (((Real.exp (I.c * I.R_0 τ ξ) : ℝ) : ℂ) *
                Complex.exp (Complex.I * (I.c : ℂ) * ((-sgn * I.Phi τ ξ : ℝ) : ℂ)))) *
            ((((I.ν' τ)⁻¹ : ℝ) : ℂ) * ((I.ν' τ : ℝ) : ℂ)) := by ring
      _ = _ := by rw [h_inv_mul, mul_one]
  set b₀ := min P.c_1 (P.c_2 / 16)
  set N := P.M + 11 / 2
  set C_amp0 := 26112 * (2 : ℝ) ^ P.M * P.C_a * P.C_ν
  set M_osc := (C_amp0 / ζ₀.re) * I.c ^ (5 / 6 : ℝ)
  have hb₀ : 0 < b₀ := lt_min P.hc_1 (div_pos P.hc_2 (by norm_num))
  have hφ_deriv : ∀ y ∈ I.ν '' Ioi 0, HasDerivAt φ (φ' y) y := by
    rintro y ⟨τ, hτ, rfl⟩
    have h1 := hasDerivAt_invFunOn_nu I hτ
    have h2 : HasDerivAt (fun t => I.Phi t ξ) (I.ν' τ * (I.μ ξ - I.m τ)) (νInv (I.ν τ)) := by
      rw [hinv_eq τ hτ]; exact I.hPhi_deriv ξ hξ τ hτ
    have h3 := h2.comp (I.ν τ) h1
    have hν'0 : I.ν' τ ≠ 0 := (inv_pos.mp (I.hν'_inv_pos τ hτ).1).ne'
    have h4 := h3.const_mul (-sgn)
    have h_eq_d : -sgn * (I.ν' τ * (I.μ ξ - I.m τ) * (I.ν' τ)⁻¹) = φ' (I.ν τ) := by
      dsimp [φ']
      rw [hinv_eq τ hτ]
      field_simp [hν'0]
    simpa [φ, h_eq_d] using h4
  have hφ'_deriv : ∀ y ∈ I.ν '' Ioi 0, HasDerivAt φ' (φ'' y) y := by
    rintro y ⟨τ, hτ, rfl⟩
    have h1 := hasDerivAt_invFunOn_nu I hτ
    have h2 : HasDerivAt I.m (I.m' τ) (νInv (I.ν τ)) := by
      rw [hinv_eq τ hτ]; exact I.hm_deriv τ hτ
    have h3 := (h2.comp (I.ν τ) h1).const_sub (I.μ ξ)
    have h4 := h3.const_mul (-sgn)
    have h_eq_d : -sgn * -(I.m' τ * (I.ν' τ)⁻¹) = φ'' (I.ν τ) := by
      dsimp [φ'']
      rw [hinv_eq τ hτ]
      ring
    simpa [φ', h_eq_d] using h4
  have hφ'_mono : MonotoneOn φ' (I.ν '' Ioi 0) ∨ AntitoneOn φ' (I.ν '' Ioi 0) := by
    have h_m_inv : MonotoneOn (fun y => I.m (νInv y)) (I.ν '' Ioi 0) := by
      intro y₁ hy₁ y₂ hy₂ hy
      have hx₁ : νInv y₁ ∈ Ici 0 := (Function.invFunOn_mem hy₁ : νInv y₁ ∈ Ioi 0).le
      have hx₂ : νInv y₂ ∈ Ici 0 := (Function.invFunOn_mem hy₂ : νInv y₂ ∈ Ioi 0).le
      exact I.hm_strictMono.monotoneOn hx₁ hx₂ ((strictMonoOn_invFunOn_nu I).monotoneOn hy₁ hy₂ hy)
    rcases hsgn with rfl | rfl
    · left
      intro y₁ hy₁ y₂ hy₂ hy
      dsimp [φ']
      linarith [h_m_inv hy₁ hy₂ hy]
    · right
      intro y₁ hy₁ y₂ hy₂ hy
      dsimp [φ']
      linarith [h_m_inv hy₁ hy₂ hy]
  have hφ'_eq : ∀ τ > 0, φ' (I.ν τ) = -sgn * (I.μ ξ - I.m τ) := fun τ hτ => by
    dsimp [φ']; rw [hinv_eq τ hτ]
  have h_abs_φ' : ∀ τ > 0, |φ' (I.ν τ)| = |I.m τ - I.μ ξ| := fun τ hτ => by
    rw [hφ'_eq τ hτ, abs_mul, abs_neg, hsgn_abs, one_mul, abs_sub_comm]
  have h_upper : ∀ τ, 2 * I.τ_0 ξ < τ → b₀ * min (τ ^ 2) 1 ≤ |φ' (I.ν τ)| := by
    intro τ hτ
    have hτ_pos : 0 < τ := lt_of_le_of_lt (mul_nonneg zero_le_two (I.hτ_0_nn ξ)) hτ
    rw [h_abs_φ' τ hτ_pos]
    have hm_step : P.c_1 * min (τ ^ 2) 1 ≤ I.m τ - I.m (τ / 2) := I.hm_step τ hτ_pos
    have hm_diff : I.m τ - I.m (τ / 2) ≤ I.m τ - I.μ ξ := by
      rcases le_or_gt (I.μ ξ) 0 with hμ | hμ
      · have h0le : I.m 0 ≤ I.m (τ / 2) :=
          I.hm_strictMono.monotoneOn (by simp) (by show 0 ≤ τ / 2; linarith) (by linarith)
        rw [I.hm_0] at h0le
        linarith
      · have hτ0_lt : I.τ_0 ξ < τ / 2 := by linarith
        have hm_lt : I.m (I.τ_0 ξ) ≤ I.m (τ / 2) :=
          I.hm_strictMono.monotoneOn (I.hτ_0_nn ξ) (by show 0 ≤ τ / 2; linarith) hτ0_lt.le
        rw [I.hτ_0_root ξ hμ] at hm_lt
        linarith
    have hb₀_le : b₀ ≤ P.c_1 := min_le_left _ _
    have hmin_nn : 0 ≤ min (τ ^ 2) 1 := le_min (sq_nonneg _) zero_le_one
    calc b₀ * min (τ ^ 2) 1 ≤ P.c_1 * min (τ ^ 2) 1 := by gcongr
      _ ≤ I.m τ - I.μ ξ := hm_step.trans hm_diff
      _ ≤ |I.m τ - I.μ ξ| := le_abs_self _
  have h_lower : ∀ τ, 0 < τ → τ < I.τ_0 ξ / 2 → b₀ * min (I.τ_0 ξ ^ 2) 1 ≤ |φ' (I.ν τ)| := by
    intro τ hτ hτ_lt
    rw [h_abs_φ' τ hτ]
    have hτ0_pos : 0 < I.τ_0 ξ := by linarith
    have hμ_pos : 0 < I.μ ξ := by
      by_contra hle
      have h0 := I.hτ_0_eq_zero ξ (not_lt.mp hle)
      linarith
    have hm_eq : I.m (I.τ_0 ξ) = I.μ ξ := I.hτ_0_root ξ hμ_pos
    have hm_lt : I.m τ ≤ I.m (I.τ_0 ξ / 2) :=
      I.hm_strictMono.monotoneOn hτ.le (by show 0 ≤ I.τ_0 ξ / 2; linarith) hτ_lt.le
    have hm_step : P.c_1 * min (I.τ_0 ξ ^ 2) 1 ≤ I.m (I.τ_0 ξ) - I.m (I.τ_0 ξ / 2) :=
      I.hm_step (I.τ_0 ξ) hτ0_pos
    have hb₀_le : b₀ ≤ P.c_1 := min_le_left _ _
    have hmin_nn : 0 ≤ min (I.τ_0 ξ ^ 2) 1 := le_min (sq_nonneg _) zero_le_one
    calc b₀ * min (I.τ_0 ξ ^ 2) 1 ≤ P.c_1 * min (I.τ_0 ξ ^ 2) 1 := by gcongr
      _ ≤ I.μ ξ - I.m τ := by linarith
      _ ≤ |I.m τ - I.μ ξ| := by rw [abs_sub_comm]; exact le_abs_self _
  have h_mid : 0 < I.τ_0 ξ → ∀ τ, I.τ_0 ξ / 2 ≤ τ → τ ≤ 2 * I.τ_0 ξ →
      b₀ * I.τ_0 ξ / (1 + I.τ_0 ξ ^ 3) ≤ |φ'' (I.ν τ)| := by
    intro hτ0_pos τ hτ_lo hτ_hi
    have hτ_pos : 0 < τ := lt_of_lt_of_le (half_pos hτ0_pos) hτ_lo
    have hφ''_eq : |φ'' (I.ν τ)| = |I.m' τ / I.ν' τ| := by
      dsimp [φ'']; rw [hinv_eq τ hτ_pos, abs_mul, hsgn_abs, one_mul]
    rw [hφ''_eq]
    have hslope := I.hm_slope τ hτ_pos
    have hden1 : 1 + τ ^ 3 ≤ 8 * (1 + I.τ_0 ξ ^ 3) := by
      have hpow : τ ^ 3 ≤ (2 * I.τ_0 ξ) ^ 3 := pow_le_pow_left₀ hτ_pos.le hτ_hi 3
      linarith [show (2 * I.τ_0 ξ) ^ 3 = 8 * I.τ_0 ξ ^ 3 by ring]
    have hden_pos : 0 < 1 + τ ^ 3 := by positivity
    have hden0_pos : 0 < 1 + I.τ_0 ξ ^ 3 := by positivity
    have hfrac : I.τ_0 ξ / (16 * (1 + I.τ_0 ξ ^ 3)) ≤ τ / (1 + τ ^ 3) := by
      rw [div_le_div_iff₀ (by positivity) hden_pos]
      nlinarith
    have hb₀_le : b₀ ≤ P.c_2 / 16 := min_le_right _ _
    have hc2_pos := P.hc_2
    calc b₀ * I.τ_0 ξ / (1 + I.τ_0 ξ ^ 3)
        ≤ (P.c_2 / 16) * I.τ_0 ξ / (1 + I.τ_0 ξ ^ 3) := by gcongr
      _ = P.c_2 * (I.τ_0 ξ / (16 * (1 + I.τ_0 ξ ^ 3))) := by field_simp
      _ ≤ P.c_2 * (τ / (1 + τ ^ 3)) := by gcongr
      _ = P.c_2 * τ / (1 + τ ^ 3) := by ring
      _ ≤ I.m' τ / I.ν' τ := hslope
      _ ≤ |I.m' τ / I.ν' τ| := le_abs_self _
  have hh_cont : ContinuousOn h0 (Ioi 0) := by
    have hQ_cont : Continuous (stripPoissonQ ζ₀.re ζ₀.im I.ε) := by
      unfold stripPoissonQ stripPoissonP stripPoissonP1
      refine Continuous.div continuous_const
        ((Real.continuous_cosh.comp (continuous_const.mul (continuous_id.sub continuous_const))).sub
          continuous_const) (fun τ => (stripPoissonP_den_pos hσ₀ hσ₁ _).ne') |>.add
        (continuous_const.mul (Continuous.div continuous_const
          ((Real.continuous_cosh.comp (continuous_const.mul (continuous_id.add continuous_const))).add
            continuous_const) (fun τ => (stripPoissonP1_den_pos hσ₀ hσ₁ _).ne')))
    have hA0_cont : Continuous (tebAmp0 I.c) := continuous_tebAmp0 I.c
    have ha0_cont : Continuous I.a_0 := continuous_iff_continuousAt.mpr fun τ =>
      (I.ha_0_deriv τ).continuousAt
    have hR0_cont : ContinuousOn (fun τ => Real.exp (I.c * I.R_0 τ ξ)) (Ioi 0) :=
      Real.continuous_exp.continuousOn.comp (continuousOn_const.mul (I.hR_0_cont ξ hξ)) (mapsTo_univ _ _)
    have hinv_cont : ContinuousOn (fun τ => (I.ν' τ)⁻¹) (Ioi 0) := by
      refine I.hν'_cont.inv₀ fun τ hτ => ?_
      exact (inv_pos.mp (I.hν'_inv_pos τ hτ).1).ne'
    refine ((((Complex.continuous_ofReal.comp (tebCutoff_continuous δ)).continuousOn.mul
      (Complex.continuous_ofReal.comp (hQ_cont.comp (continuous_const.mul continuous_id))).continuousOn).mul
      (hA0_cont.comp (continuous_const.mul continuous_id)).continuousOn).mul
      (ha0_cont.comp (continuous_const.mul continuous_id)).continuousOn).mul
      (Complex.continuous_ofReal.continuousOn.comp hR0_cont (mapsTo_univ _ _)) |>.mul
      (Complex.continuous_ofReal.continuousOn.comp hinv_cont (mapsTo_univ _ _))
  have hh_vanish : ∀ τ, 0 < τ → τ ≤ 2 * P.A_0 * I.c ^ (-(1 / 3 : ℝ)) → h0 τ = 0 := by
    intro τ _ hτ_le
    dsimp [h0]
    have hχ0 : tebCutoff δ τ = 0 := tebCutoff_eq_zero hδ_pos (by
      rw [abs_of_pos ‹0 < τ›]; dsimp [δ]; linarith)
    rw [hχ0, Complex.ofReal_zero, zero_mul, zero_mul, zero_mul, zero_mul, zero_mul]
  have hh_bv : ∀ s > 0, BoundedVariationOn h0 (Icc s (2 * s)) ∧
      ∀ τ ∈ Icc s (2 * s), ‖h0 τ‖ + (eVariationOn h0 (Icc s (2 * s))).toReal ≤
        M_osc * s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2) := by
    intro s hs
    have hs_le : s ≤ 2 * s := by linarith
    -- Factor 1: cutoff
    have hf1_bd : ∀ τ ∈ Icc s (2 * s), ‖(tebCutoff δ τ : ℂ)‖ ≤ 1 := fun τ _ => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [tebCutoff_nonneg δ τ], tebCutoff_le_one δ τ⟩
    have hf1_bv : eVariationOn (fun τ => (tebCutoff δ τ : ℂ)) (Icc s (2 * s)) ≤ ENNReal.ofReal 1 := by
      rw [eVariationOn_ofReal]; exact tebCutoff_eVariationOn_le hδ_pos hs.le hs_le
    -- Factor 2: Poisson kernel Q
    have hf2_bd : ∀ τ ∈ Icc s (2 * s), ‖(stripPoissonQ ζ₀.re ζ₀.im I.ε (sgn * τ) : ℂ)‖ ≤ 1 / ζ₀.re :=
      fun τ _ => by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact (stripPoissonQ_abs_le hσ₀ hσ₁ ζ₀.im hε_abs _).trans (stripPoissonCalQ_le hσ₀ hσ₀_le ζ₀.im _)
    have hf2_bv : eVariationOn (fun τ => (stripPoissonQ ζ₀.re ζ₀.im I.ε (sgn * τ) : ℂ)) (Icc s (2 * s)) ≤
        ENNReal.ofReal (1 / ζ₀.re) := by
      rw [eVariationOn_ofReal]
      have hQ_tv_all : eVariationOn (stripPoissonQ ζ₀.re ζ₀.im I.ε) univ ≤ ENNReal.ofReal (1 / ζ₀.re) :=
        eVariationOn_stripPoissonQ_le hσ₀ hσ₀_le ζ₀.im hε_abs
      rcases hsgn with rfl | rfl
      · simpa using le_trans (eVariationOn.mono _ (subset_univ _)) hQ_tv_all
      · have hcomp : eVariationOn (fun τ => stripPoissonQ ζ₀.re ζ₀.im I.ε (-τ)) univ ≤
            ENNReal.ofReal (1 / ζ₀.re) :=
          le_trans (eVariationOn_comp_neg (stripPoissonQ ζ₀.re ζ₀.im I.ε)) hQ_tv_all
        have hsub : eVariationOn (fun τ => stripPoissonQ ζ₀.re ζ₀.im I.ε (-1 * τ)) (Icc s (2 * s)) ≤
            eVariationOn (fun τ => stripPoissonQ ζ₀.re ζ₀.im I.ε (-τ)) univ := by
          simpa using eVariationOn.mono (fun τ => stripPoissonQ ζ₀.re ζ₀.im I.ε (-τ)) (subset_univ _)
        exact hsub.trans hcomp
    -- Combine f1 * f2
    have h12 := bv_norm_add_tv_mul (by norm_num) (by positivity) (by norm_num) (by positivity)
      hf1_bd hf2_bd hf1_bv hf2_bv
    have h12_bd : ∀ τ ∈ Icc s (2 * s),
        ‖(tebCutoff δ τ : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im I.ε (sgn * τ) : ℂ)‖ ≤ 1 * (1 / ζ₀.re) :=
      fun τ hτ => by
        rw [norm_mul]; exact mul_le_mul (hf1_bd τ hτ) (hf2_bd τ hτ) (norm_nonneg _) zero_le_one
    have h12_tv_le : eVariationOn (fun τ => (tebCutoff δ τ : ℂ) *
          (stripPoissonQ ζ₀.re ζ₀.im I.ε (sgn * τ) : ℂ)) (Icc s (2 * s)) ≤
        ENNReal.ofReal (1 * (1 / ζ₀.re) + (1 / ζ₀.re) * 1) := h12.2.1
    -- Factor 3: tebAmp0
    have hamp_all := (tebAmp0_block_bv_le hc_pos.le hsgn_abs hs).1
    have hamp_bv_fin := (tebAmp0_block_bv_le hc_pos.le hsgn_abs hs).2
    set B := I.c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (9 / 2 : ℝ) * Real.exp (-s ^ 2)
    have hB_nn : 0 ≤ B := by dsimp [B]; positivity
    have hf3_bd : ∀ τ ∈ Icc s (2 * s), ‖tebAmp0 I.c (sgn * τ)‖ ≤ 272 * B := fun τ hτ => by
      have := hamp_all τ hτ
      have htv_nn : 0 ≤ (eVariationOn (fun t => tebAmp0 I.c (sgn * t)) (Icc s (2 * s))).toReal :=
        ENNReal.toReal_nonneg
      dsimp [B]; linarith
    have hf3_bv : eVariationOn (fun τ => tebAmp0 I.c (sgn * τ)) (Icc s (2 * s)) ≤
        ENNReal.ofReal (272 * B) := by
      have hτs := hamp_all s ⟨le_rfl, hs_le⟩
      have htv_le : (eVariationOn (fun t => tebAmp0 I.c (sgn * t)) (Icc s (2 * s))).toReal ≤ 272 * B := by
        have := norm_nonneg (tebAmp0 I.c (sgn * s))
        dsimp [B]; linarith
      exact (ENNReal.ofReal_toReal hamp_bv_fin).symm ▸ ENNReal.ofReal_le_ofReal htv_le
    -- Factor 4: a_0 (sgn * τ)
    set K_a0 := P.C_a * (2 : ℝ) ^ P.M * (1 + s) ^ P.M
    have hKa0_nn : 0 ≤ K_a0 := by dsimp [K_a0]; have := P.hC_a; positivity
    have ha0_both : ∀ τ ∈ Icc s (2 * s), ‖I.a_0 (sgn * τ)‖ ≤ K_a0 ∧ ‖(sgn : ℂ) * I.a_0' (sgn * τ)‖ ≤ K_a0 := by
      intro τ hτ
      have habs : |sgn * τ| ≤ 2 * s := by
        rw [abs_mul, hsgn_abs, one_mul, abs_of_pos (lt_of_lt_of_le hs hτ.1)]
        exact hτ.2
      have h1τ : (1 + |sgn * τ|) ^ P.M ≤ (2 : ℝ) ^ P.M * (1 + s) ^ P.M := by
        have hle : 1 + |sgn * τ| ≤ 2 * (1 + s) := by linarith
        rw [← Real.mul_rpow (by norm_num) (by linarith)]
        exact Real.rpow_le_rpow (by linarith [abs_nonneg (sgn * τ)]) hle P.hM
      have hbd := (I.ha_0_bd (sgn * τ)).trans (mul_le_mul_of_nonneg_left h1τ P.hC_a.le)
      have h1 : ‖I.a_0 (sgn * τ)‖ ≤ K_a0 := by
        dsimp [K_a0]; linarith [norm_nonneg (I.a_0' (sgn * τ))]
      have h2 : ‖(sgn : ℂ) * I.a_0' (sgn * τ)‖ ≤ K_a0 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hsgn_abs, one_mul]
        dsimp [K_a0]; linarith [norm_nonneg (I.a_0 (sgn * τ))]
      exact ⟨h1, h2⟩
    have hf4_bd : ∀ τ ∈ Icc s (2 * s), ‖I.a_0 (sgn * τ)‖ ≤ K_a0 := fun τ hτ => (ha0_both τ hτ).1
    have hf4_bv : eVariationOn (fun τ => I.a_0 (sgn * τ)) (Icc s (2 * s)) ≤
        ENNReal.ofReal (K_a0 * (1 + s)) := by
      have hderiv_a0 : ∀ τ ∈ Icc s (2 * s),
          HasDerivAt (fun t => I.a_0 (sgn * t)) ((sgn : ℂ) * I.a_0' (sgn * τ)) τ := by
        intro τ _
        have hd1 := I.ha_0_deriv (sgn * τ)
        have hd2 : HasDerivAt (fun t : ℝ => sgn * t) sgn τ := by
          simpa using (hasDerivAt_id τ).const_mul sgn
        have hcomp := hd1.scomp τ hd2
        refine hcomp.congr_deriv ?_
        simp [Complex.real_smul]
      have htv := eVariationOn_le_of_hasDerivAt_le hs_le hKa0_nn hderiv_a0 (fun τ hτ => (ha0_both τ hτ).2)
      refine htv.trans (ENNReal.ofReal_le_ofReal ?_)
      have : 2 * s - s = s := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left (by linarith) hKa0_nn
    -- Factor 5: exp (c * R_0)
    have hf5_bd : ∀ τ ∈ Icc s (2 * s), ‖((Real.exp (I.c * I.R_0 τ ξ) : ℝ) : ℂ)‖ ≤ 1 := fun τ _ => by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hc_pos.le (I.hR_0_nonpos ξ hξ τ))
    have hf5_bv : eVariationOn (fun τ => ((Real.exp (I.c * I.R_0 τ ξ) : ℝ) : ℂ)) (Icc s (2 * s)) ≤
        ENNReal.ofReal 2 := by
      rw [eVariationOn_ofReal]
      obtain ⟨τ_p, hmono_R, hanti_R⟩ := I.hR_0_unimodal ξ hξ
      refine eVariationOn_unimodal_Icc_le (τ_p := τ_p) hs hs_le
        (fun τ _ => (Real.exp_pos _).le)
        (fun τ _ => Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hc_pos.le (I.hR_0_nonpos ξ hξ τ)))
        ?_ ?_
      · exact fun a ha b hb hab => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hmono_R ha hb hab) hc_pos.le)
      · exact fun a ha b hb hab => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hanti_R ha hb hab) hc_pos.le)
    -- Factor 6: (ν' τ)⁻¹
    have hf6_bd : ∀ τ ∈ Icc s (2 * s), ‖(((I.ν' τ)⁻¹ : ℝ) : ℂ)‖ ≤ P.C_ν := fun τ hτ => by
      have hpos := I.hν'_inv_pos τ (lt_of_lt_of_le hs hτ.1)
      rw [Complex.norm_real, Real.norm_of_nonneg hpos.1.le]
      exact hpos.2
    have hf6_bv : eVariationOn (fun τ => (((I.ν' τ)⁻¹ : ℝ) : ℂ)) (Icc s (2 * s)) ≤
        ENNReal.ofReal P.C_ν := by
      rw [eVariationOn_ofReal]
      have hsub : Icc s (2 * s) ⊆ Ioi 0 := fun τ hτ => lt_of_lt_of_le hs hτ.1
      have htv := eVariationOn_le_integral_abs_deriv hs_le
        (fun τ hτ => I.hν'_inv_deriv τ (hsub hτ))
        ((I.hinvNu'_cont.mono hsub).intervalIntegrable_of_Icc hs_le)
      refine htv.trans (ENNReal.ofReal_le_ofReal ?_)
      have hIoc_sub : Ioc s (2 * s) ⊆ Ioi 0 := fun τ hτ => lt_of_lt_of_le hs hτ.1.le
      have hint_abs : IntegrableOn (fun τ => |I.invNu' τ|) (Ioi 0) := I.hinvNu'_integrable.abs
      calc ∫ τ in s..(2 * s), |I.invNu' τ|
          = ∫ τ in Ioc s (2 * s), |I.invNu' τ| := intervalIntegral.integral_of_le hs_le
        _ ≤ ∫ τ in Ioi (0 : ℝ), |I.invNu' τ| :=
            setIntegral_mono_set hint_abs (ae_of_all _ fun _ => abs_nonneg _) (Eventually.of_forall hIoc_sub)
        _ ≤ P.C_ν := I.hinvNu'_int
    -- Multiply all 6 BV bounds using bv_norm_add_tv_mul
    have h123 := bv_norm_add_tv_mul (by positivity) (by positivity) (by positivity) (by positivity)
      h12_bd hf3_bd h12_tv_le hf3_bv
    have h45 := bv_norm_add_tv_mul hKa0_nn zero_le_one (by positivity) zero_le_two
      hf4_bd hf5_bd hf4_bv hf5_bv
    have h45_bd : ∀ τ ∈ Icc s (2 * s),
        ‖I.a_0 (sgn * τ) * ((Real.exp (I.c * I.R_0 τ ξ) : ℝ) : ℂ)‖ ≤ K_a0 * 1 := fun τ hτ => by
      rw [norm_mul]; exact mul_le_mul (hf4_bd τ hτ) (hf5_bd τ hτ) (norm_nonneg _) hKa0_nn
    have h456 := bv_norm_add_tv_mul (by positivity) P.hC_ν.le (by positivity) P.hC_ν.le
      h45_bd hf6_bd h45.2.1 hf6_bv
    have h123_bd : ∀ τ ∈ Icc s (2 * s),
        ‖(tebCutoff δ τ : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im I.ε (sgn * τ) : ℂ) * tebAmp0 I.c (sgn * τ)‖ ≤
          (1 * (1 / ζ₀.re)) * (272 * B) := fun τ hτ => by
      rw [norm_mul]; exact mul_le_mul (h12_bd τ hτ) (hf3_bd τ hτ) (norm_nonneg _) (by positivity)
    have h456_bd : ∀ τ ∈ Icc s (2 * s),
        ‖I.a_0 (sgn * τ) * ((Real.exp (I.c * I.R_0 τ ξ) : ℝ) : ℂ) * (((I.ν' τ)⁻¹ : ℝ) : ℂ)‖ ≤
          (K_a0 * 1) * P.C_ν := fun τ hτ => by
      rw [norm_mul]; exact mul_le_mul (h45_bd τ hτ) (hf6_bd τ hτ) (norm_nonneg _) (by positivity)
    have hnn_123 : 0 ≤ (1 * (1 / ζ₀.re)) * (272 * B) := mul_nonneg (by positivity) (by linarith)
    have hnn_456 : 0 ≤ (K_a0 * 1) * P.C_ν := mul_nonneg (mul_nonneg hKa0_nn zero_le_one) P.hC_ν.le
    have hnn_v123 : 0 ≤ (1 * (1 / ζ₀.re)) * (272 * B) +
        (272 * B) * (1 * (1 / ζ₀.re) + (1 / ζ₀.re) * 1) := by
      have := mul_nonneg (by linarith : 0 ≤ 272 * B) (by positivity : 0 ≤ 1 * (1 / ζ₀.re) + (1 / ζ₀.re) * 1)
      linarith
    have hnn_v456 : 0 ≤ (K_a0 * 1) * P.C_ν + P.C_ν * (K_a0 * 2 + 1 * (K_a0 * (1 + s))) := by
      have : 0 ≤ K_a0 * 2 + 1 * (K_a0 * (1 + s)) := by nlinarith
      exact add_nonneg hnn_456 (mul_nonneg P.hC_ν.le this)
    have h_all := bv_norm_add_tv_mul hnn_123 hnn_456 hnn_v123 hnn_v456
      h123_bd h456_bd h123.2.1 h456.2.1
    have hh0_eq : (fun τ => ((tebCutoff δ τ : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im I.ε (sgn * τ) : ℂ) *
          tebAmp0 I.c (sgn * τ)) *
        (I.a_0 (sgn * τ) * ((Real.exp (I.c * I.R_0 τ ξ) : ℝ) : ℂ) * (((I.ν' τ)⁻¹ : ℝ) : ℂ))) = h0 := by
      ext τ; dsimp [h0]; ring
    rw [hh0_eq] at h_all
    refine ⟨h_all.1, fun τ hτ => ?_⟩
    have h22 := h_all.2.2 τ hτ
    simp only [show ∀ t, ((tebCutoff δ t : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im I.ε (sgn * t) : ℂ) *
          tebAmp0 I.c (sgn * t)) *
        (I.a_0 (sgn * t) * ((Real.exp (I.c * I.R_0 t ξ) : ℝ) : ℂ) * (((I.ν' t)⁻¹ : ℝ) : ℂ)) = h0 t
      from fun t => by dsimp [h0]; ring] at h22
    refine h22.trans ?_
    have hexp_N : (1 + s) ^ (9 / 2 : ℝ) * (1 + s) ^ P.M * (1 + s) = (1 + s) ^ N := by
      have h1s : 0 < 1 + s := by linarith
      calc (1 + s) ^ (9 / 2 : ℝ) * (1 + s) ^ P.M * (1 + s)
          = (1 + s) ^ (9 / 2 : ℝ) * (1 + s) ^ P.M * (1 + s) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = (1 + s) ^ (9 / 2 + P.M + 1) := by rw [Real.rpow_add h1s, Real.rpow_add h1s]
        _ = (1 + s) ^ N := by dsimp [N]; ring_nf
    have h123_fac : (1 * (1 / ζ₀.re)) * (272 * B) +
          ((1 * (1 / ζ₀.re)) * (272 * B) + (272 * B) * (1 * (1 / ζ₀.re) + (1 / ζ₀.re) * 1)) =
        (1088 / ζ₀.re) * B := by ring
    have h456_fac : (K_a0 * 1) * P.C_ν + ((K_a0 * 1) * P.C_ν + P.C_ν * (K_a0 * 2 + 1 * (K_a0 * (1 + s)))) ≤
        12 * K_a0 * P.C_ν * (1 + s) := by
      have h1s1 : 1 ≤ 1 + s := by linarith
      nlinarith [mul_nonneg hKa0_nn P.hC_ν.le]
    calc ((1 * (1 / ζ₀.re)) * (272 * B) +
            ((1 * (1 / ζ₀.re)) * (272 * B) + (272 * B) * (1 * (1 / ζ₀.re) + (1 / ζ₀.re) * 1))) *
          ((K_a0 * 1) * P.C_ν +
            ((K_a0 * 1) * P.C_ν + P.C_ν * (K_a0 * 2 + 1 * (K_a0 * (1 + s)))))
        ≤ ((1088 / ζ₀.re) * B) * (12 * K_a0 * P.C_ν * (1 + s)) := by
          rw [h123_fac]
          exact mul_le_mul_of_nonneg_left h456_fac (by positivity)
      _ ≤ M_osc * s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2) := by
          rw [← hexp_N]
          dsimp [M_osc, C_amp0, B, K_a0]
          have h_term_nn : 0 ≤ (1 / ζ₀.re) * I.c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ) *
              (1 + s) ^ (9 / 2 : ℝ) * Real.exp (-s ^ 2) *
              (P.C_a * (2 : ℝ) ^ P.M * (1 + s) ^ P.M * P.C_ν * (1 + s)) := by
            have := P.hC_a.le; have := P.hC_ν.le; positivity
          linarith [show ((1088 / ζ₀.re) *
                (I.c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (9 / 2 : ℝ) * Real.exp (-s ^ 2))) *
              (12 * (P.C_a * (2 : ℝ) ^ P.M * (1 + s) ^ P.M) * P.C_ν * (1 + s)) =
              13056 * ((1 / ζ₀.re) * I.c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ) *
                (1 + s) ^ (9 / 2 : ℝ) * Real.exp (-s ^ 2) *
                (P.C_a * (2 : ℝ) ^ P.M * (1 + s) ^ P.M * P.C_ν * (1 + s))) by ring,
            show ((26112 * (2 : ℝ) ^ P.M * P.C_a * P.C_ν / ζ₀.re) * I.c ^ (5 / 6 : ℝ)) *
                s ^ (5 / 2 : ℝ) *
                ((1 + s) ^ (9 / 2 : ℝ) * (1 + s) ^ P.M * (1 + s)) * Real.exp (-s ^ 2) =
              26112 * ((1 / ζ₀.re) * I.c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ) *
                (1 + s) ^ (9 / 2 : ℝ) * Real.exp (-s ^ 2) *
                (P.C_a * (2 : ℝ) ^ P.M * (1 + s) ^ P.M * P.C_ν * (1 + s))) by ring]
  have ha2_or : I.a_2 ξ = 0 ∨ I.a_2 ξ ≠ 0 := eq_or_ne _ _
  rcases ha2_or with ha2_zero | ha2_ne
  · have h_zero : EqOn (fun τ => F (sgn * τ)) 0 (Ioi 0) := fun τ hτ => by
      dsimp only
      rw [← hF_rw τ hτ, ha2_zero, zero_mul]
      rfl
    rw [setIntegral_congr_fun measurableSet_Ioi h_zero]
    simp only [Pi.zero_apply, integral_zero, norm_zero]
    have hosc_pos := tebBandOscConst_pos P
    have hc56 : 0 ≤ I.c ^ (5 / 6 : ℝ) := Real.rpow_nonneg hc_pos.le _
    have h1 : 0 ≤ I.c⁻¹ + I.c ^ (-(1 / 2 : ℝ)) * min (I.τ_0 ξ ^ 2) 1 *
        (if P.A_0 * I.c ^ (-(1 / 3 : ℝ)) < I.τ_0 ξ then 1 else 0) := by
      have := Real.rpow_nonneg hc_pos.le (-(1 / 2 : ℝ))
      have : 0 ≤ min (I.τ_0 ξ ^ 2) 1 := le_min (sq_nonneg _) zero_le_one
      positivity
    exact mul_nonneg (mul_nonneg (div_nonneg (div_nonneg hosc_pos.le zero_le_two) hσ₀.le) hc56) h1
  have hint_osc : IntegrableOn
      (fun τ => h0 τ * ((I.ν' τ : ℝ) : ℂ) * Complex.exp (Complex.I * (I.c : ℂ) * (φ (I.ν τ) : ℂ)))
      (Ioi 0) := by
    have h_eq : EqOn
        (fun τ => h0 τ * ((I.ν' τ : ℝ) : ℂ) * Complex.exp (Complex.I * (I.c : ℂ) * (φ (I.ν τ) : ℂ)))
        (fun τ => (I.a_2 ξ)⁻¹ * F (sgn * τ)) (Ioi 0) := by
      intro τ hτ
      dsimp only
      rw [← hF_rw τ hτ, ← mul_assoc, inv_mul_cancel₀ ha2_ne, one_mul]
    exact IntegrableOn.congr_fun (hF_int.const_mul (I.a_2 ξ)⁻¹) h_eq.symm measurableSet_Ioi
  have h_edge_osc := teb_edge_osc hτ₀_nn P.hA_0 hb₀ I.hc
    I.hν_deriv I.hν'_cont (fun τ hτ => inv_pos.mp (I.hν'_inv_pos τ hτ).1)
    hφ_deriv hφ'_deriv hφ'_mono h_upper h_lower h_mid hh_cont hh_vanish hh_bv hint_osc
  have h_int_eq : ∫ τ in Ioi (0 : ℝ), F (sgn * τ) =
      I.a_2 ξ * ∫ τ in Ioi (0 : ℝ),
        h0 τ * ((I.ν' τ : ℝ) : ℂ) * Complex.exp (Complex.I * (I.c : ℂ) * (φ (I.ν τ) : ℂ)) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun τ hτ => (hF_rw τ hτ).symm
  rw [h_int_eq, norm_mul]
  have ha2_bd : ‖I.a_2 ξ‖ ≤ P.C_a := I.ha_2_bd ξ hξ
  have hosc_nn : 0 ≤ tebOscConst b₀ N * M_osc *
      (I.c⁻¹ + I.c ^ (-(1 / 2 : ℝ)) * min (I.τ_0 ξ ^ 2) 1 *
        if P.A_0 * I.c ^ (-(1 / 3 : ℝ)) < I.τ_0 ξ then 1 else 0) := by
    have h1 := tebOscConst_pos hb₀ N
    have h2 : 0 ≤ M_osc := by
      dsimp [M_osc, C_amp0]; have := P.hC_a; have := P.hC_ν; positivity
    positivity
  calc ‖I.a_2 ξ‖ * ‖∫ τ in Ioi (0 : ℝ),
          h0 τ * ((I.ν' τ : ℝ) : ℂ) * Complex.exp (Complex.I * (I.c : ℂ) * (φ (I.ν τ) : ℂ))‖
      ≤ P.C_a * (tebOscConst b₀ N * M_osc *
          (I.c⁻¹ + I.c ^ (-(1 / 2 : ℝ)) * min (I.τ_0 ξ ^ 2) 1 *
            if P.A_0 * I.c ^ (-(1 / 3 : ℝ)) < I.τ_0 ξ then 1 else 0)) :=
        mul_le_mul ha2_bd h_edge_osc (norm_nonneg _) P.hC_a.le
    _ = (tebBandOscConst P / 2 / ζ₀.re) * I.c ^ (5 / 6 : ℝ) *
          (I.c⁻¹ + I.c ^ (-(1 / 2 : ℝ)) * min (I.τ_0 ξ ^ 2) 1 *
            if P.A_0 * I.c ^ (-(1 / 3 : ℝ)) < I.τ_0 ξ then 1 else 0) := by
        dsimp [tebBandOscConst, b₀, N, M_osc, C_amp0]
        ring

/-- Oscillatory bound on `J_χ(ξ)` for `ξ ∈ Ioi 0 \ E_sub` via `teb_edge_osc`. -/
private lemma jchi_osc_bound {P : BandReductionParams} (I : BandReductionInstance P)
    {ζ₀ : ℂ} (hσ₀ : 0 < ζ₀.re) (hσ₀_le : ζ₀.re ≤ 0.04)
    {ξ : ℝ} (hξ : ξ ∈ Ioi 0 \ I.E_sub) :
    let δ := P.A_0 * I.c ^ (-(1 / 3 : ℝ))
    let F : ℝ → ℂ := fun τ => (tebCutoff δ τ : ℂ) *
      (stripPoissonQ ζ₀.re ζ₀.im I.ε τ : ℂ) * tebAmp0 I.c τ * I.K_edge τ ξ
    Integrable F ∧
    ‖∫ τ : ℝ, F τ‖ ≤ (tebBandOscConst P / ζ₀.re) * I.c ^ (5 / 6 : ℝ) *
      (I.c⁻¹ + I.c ^ (-(1 / 2 : ℝ)) * min (I.τ_0 ξ ^ 2) 1 *
        if P.A_0 * I.c ^ (-(1 / 3 : ℝ)) < I.τ_0 ξ then 1 else 0) := by
  intro δ F
  have hc_pos : 0 < I.c := lt_of_lt_of_le zero_lt_one I.hc
  have hδ_pos : 0 < δ := by dsimp [δ]; have := P.hA_0; positivity
  have hσ₁ : ζ₀.re < 1 := by linarith
  have hε_abs : |I.ε| ≤ 1 := by rcases I.hε with hε | hε <;> norm_num [hε]
  have hQ_bd : ∀ τ : ℝ, |stripPoissonQ ζ₀.re ζ₀.im I.ε τ| ≤ 1 / ζ₀.re := fun τ =>
    (stripPoissonQ_abs_le hσ₀ hσ₁ ζ₀.im hε_abs τ).trans (stripPoissonCalQ_le hσ₀ hσ₀_le ζ₀.im τ)
  have hF_maj : ∀ τ : ℝ, ‖F τ‖ ≤ (1 / ζ₀.re) * P.C_a ^ 2 * I.c ^ (5 / 6 : ℝ) *
      ((1 + |τ|) ^ (P.M + 5) * Real.exp (-τ ^ 2)) := by
    intro τ
    dsimp [F]
    rw [I.hK_factor ξ hξ τ]
    have h_amp : ‖tebAmp0 I.c τ‖ ≤
        I.c ^ (5 / 6 : ℝ) * |τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * Real.exp (-τ ^ 2) :=
      norm_tebAmp0_le hc_pos.le
    have ha0 : ‖I.a_0 τ‖ ≤ P.C_a * (1 + |τ|) ^ P.M :=
      le_trans (by linarith [norm_nonneg (I.a_0' τ)]) (I.ha_0_bd τ)
    have ha2 : ‖I.a_2 ξ‖ ≤ P.C_a := I.ha_2_bd ξ hξ
    have hexp : ‖Complex.exp ((I.c : ℂ) * ((I.R_0 τ ξ : ℂ) - Complex.I * (I.Phi τ ξ : ℂ)))‖ ≤ 1 := by
      rw [Complex.norm_exp]
      apply Real.exp_le_one_iff.mpr
      have hre : ((I.c : ℂ) * ((I.R_0 τ ξ : ℂ) - Complex.I * (I.Phi τ ξ : ℂ))).re =
          I.c * I.R_0 τ ξ := by
        simp [Complex.mul_re]
      rw [hre]
      exact mul_nonpos_of_nonneg_of_nonpos hc_pos.le (I.hR_0_nonpos ξ hξ τ)
    have hχ : |tebCutoff δ τ| ≤ 1 := abs_le.mpr ⟨by linarith [tebCutoff_nonneg δ τ], tebCutoff_le_one δ τ⟩
    have hQ : |stripPoissonQ ζ₀.re ζ₀.im I.ε τ| ≤ 1 / ζ₀.re := hQ_bd τ
    have h1τ_le : |τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ P.M ≤
        (1 + |τ|) ^ (P.M + 5) := by
      have h1 : |τ| ^ (5 / 2 : ℝ) ≤ (1 + |τ|) ^ (5 / 2 : ℝ) :=
        Real.rpow_le_rpow (abs_nonneg _) (by linarith) (by norm_num)
      have h1τ : 0 < 1 + |τ| := by linarith [abs_nonneg τ]
      have hcomb : (1 + |τ|) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ P.M =
          (1 + |τ|) ^ (P.M + 5) := by
        rw [← Real.rpow_add h1τ, ← Real.rpow_add h1τ]
        ring_nf
      calc |τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ P.M
          ≤ (1 + |τ|) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ P.M := by gcongr
        _ = (1 + |τ|) ^ (P.M + 5) := hcomb
    have h12_norm : |tebCutoff δ τ| * |stripPoissonQ ζ₀.re ζ₀.im I.ε τ| ≤ 1 * (1 / ζ₀.re) :=
      mul_le_mul hχ hQ (abs_nonneg _) zero_le_one
    have ha02_norm : ‖I.a_0 τ‖ * ‖I.a_2 ξ‖ *
          ‖Complex.exp ((I.c : ℂ) * ((I.R_0 τ ξ : ℂ) - Complex.I * (I.Phi τ ξ : ℂ)))‖ ≤
        P.C_a * (1 + |τ|) ^ P.M * P.C_a * 1 := by
      have ha0_nn : 0 ≤ P.C_a * (1 + |τ|) ^ P.M :=
        mul_nonneg P.hC_a.le (Real.rpow_nonneg (by linarith [abs_nonneg τ]) _)
      have ha02_le : ‖I.a_0 τ‖ * ‖I.a_2 ξ‖ ≤ P.C_a * (1 + |τ|) ^ P.M * P.C_a :=
        mul_le_mul ha0 ha2 (norm_nonneg _) ha0_nn
      exact mul_le_mul ha02_le hexp (norm_nonneg _) (mul_nonneg ha0_nn P.hC_a.le)
    calc ‖(tebCutoff δ τ : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im I.ε τ : ℂ) * tebAmp0 I.c τ *
            (I.a_0 τ * I.a_2 ξ * Complex.exp ((I.c : ℂ) * ((I.R_0 τ ξ : ℂ) - Complex.I * (I.Phi τ ξ : ℂ))))‖
        = (|tebCutoff δ τ| * |stripPoissonQ ζ₀.re ζ₀.im I.ε τ|) * ‖tebAmp0 I.c τ‖ *
            (‖I.a_0 τ‖ * ‖I.a_2 ξ‖ *
              ‖Complex.exp ((I.c : ℂ) * ((I.R_0 τ ξ : ℂ) - Complex.I * (I.Phi τ ξ : ℂ)))‖) := by
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (1 * (1 / ζ₀.re)) *
            (I.c ^ (5 / 6 : ℝ) * |τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * Real.exp (-τ ^ 2)) *
            (P.C_a * (1 + |τ|) ^ P.M * P.C_a * 1) := by
          have hamp_nn : 0 ≤ (1 * (1 / ζ₀.re)) *
              (I.c ^ (5 / 6 : ℝ) * |τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * Real.exp (-τ ^ 2)) := by
            have := Real.rpow_nonneg hc_pos.le (5 / 6 : ℝ)
            have := Real.rpow_nonneg (abs_nonneg τ) (5 / 2 : ℝ)
            have := Real.rpow_nonneg (by linarith [abs_nonneg τ] : 0 ≤ 1 + |τ|) (5 / 2 : ℝ)
            positivity
          refine mul_le_mul (mul_le_mul h12_norm h_amp (norm_nonneg _) (by positivity))
            ha02_norm (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)) hamp_nn
      _ = (1 / ζ₀.re) * P.C_a ^ 2 * I.c ^ (5 / 6 : ℝ) *
            ((|τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ P.M) * Real.exp (-τ ^ 2)) := by
          ring
      _ ≤ (1 / ζ₀.re) * P.C_a ^ 2 * I.c ^ (5 / 6 : ℝ) *
            ((1 + |τ|) ^ (P.M + 5) * Real.exp (-τ ^ 2)) := by
          have hc56 : 0 ≤ I.c ^ (5 / 6 : ℝ) := Real.rpow_nonneg hc_pos.le _
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h1τ_le (Real.exp_pos _).le) (by positivity)
  have hF_cont : Continuous F := by
    have hQ_cont : Continuous (stripPoissonQ ζ₀.re ζ₀.im I.ε) := by
      unfold stripPoissonQ stripPoissonP stripPoissonP1
      refine Continuous.div continuous_const
        ((Real.continuous_cosh.comp (continuous_const.mul (continuous_id.sub continuous_const))).sub
          continuous_const) (fun τ => (stripPoissonP_den_pos hσ₀ hσ₁ _).ne') |>.add
        (continuous_const.mul (Continuous.div continuous_const
          ((Real.continuous_cosh.comp (continuous_const.mul (continuous_id.add continuous_const))).add
            continuous_const) (fun τ => (stripPoissonP1_den_pos hσ₀ hσ₁ _).ne')))
    have hA0_cont : Continuous (tebAmp0 I.c) := continuous_tebAmp0 I.c
    have ha0_cont : Continuous I.a_0 := continuous_iff_continuousAt.mpr fun τ =>
      (I.ha_0_deriv τ).continuousAt
    have hPhi_pos : ContinuousOn (fun τ => I.Phi τ ξ) (Ioi 0) := fun τ hτ =>
      (I.hPhi_deriv ξ hξ τ hτ).continuousAt.continuousWithinAt
    have hPhi_neg : ContinuousOn (fun τ => I.Phi τ ξ) (Iio 0) := by
      have heq : (fun τ => I.Phi τ ξ) = fun τ => -I.Phi (-τ) ξ := funext fun τ => by
        have := I.hPhi_odd ξ hξ (-τ); rw [neg_neg] at this; linarith
      rw [heq]
      refine ContinuousOn.neg (hPhi_pos.comp continuousOn_neg fun τ (hτ : τ < 0) => ?_)
      exact neg_pos.mpr hτ
    have hR0_neg : ContinuousOn (fun τ => I.R_0 τ ξ) (Iio 0) := by
      have heq : (fun τ => I.R_0 τ ξ) = fun τ => I.R_0 (-τ) ξ := funext fun τ =>
        (I.hR_0_even ξ hξ τ).symm
      rw [heq]
      exact (I.hR_0_cont ξ hξ).comp continuousOn_neg fun τ (hτ : τ < 0) => neg_pos.mpr hτ
    have hK_pos : ContinuousOn (fun τ => I.K_edge τ ξ) (Ioi 0) := by
      rw [show (fun τ => I.K_edge τ ξ) = fun τ => I.a_0 τ * I.a_2 ξ *
          Complex.exp ((I.c : ℂ) * ((I.R_0 τ ξ : ℂ) - Complex.I * (I.Phi τ ξ : ℂ))) from
        funext (I.hK_factor ξ hξ)]
      refine (ha0_cont.continuousOn.mul continuousOn_const).mul
        (Complex.continuous_exp.continuousOn.comp
          (continuousOn_const.mul ((Complex.continuous_ofReal.continuousOn.comp (I.hR_0_cont ξ hξ)
            (mapsTo_univ _ _)).sub (continuousOn_const.mul
            (Complex.continuous_ofReal.continuousOn.comp hPhi_pos (mapsTo_univ _ _)))))
          (mapsTo_univ _ _))
    have hK_neg : ContinuousOn (fun τ => I.K_edge τ ξ) (Iio 0) := by
      rw [show (fun τ => I.K_edge τ ξ) = fun τ => I.a_0 τ * I.a_2 ξ *
          Complex.exp ((I.c : ℂ) * ((I.R_0 τ ξ : ℂ) - Complex.I * (I.Phi τ ξ : ℂ))) from
        funext (I.hK_factor ξ hξ)]
      refine (ha0_cont.continuousOn.mul continuousOn_const).mul
        (Complex.continuous_exp.continuousOn.comp
          (continuousOn_const.mul ((Complex.continuous_ofReal.continuousOn.comp hR0_neg
            (mapsTo_univ _ _)).sub (continuousOn_const.mul
            (Complex.continuous_ofReal.continuousOn.comp hPhi_neg (mapsTo_univ _ _)))))
          (mapsTo_univ _ _))
    have hpre_cont : Continuous (fun τ => (tebCutoff δ τ : ℂ) *
        (stripPoissonQ ζ₀.re ζ₀.im I.ε τ : ℂ) * tebAmp0 I.c τ) :=
      ((Complex.continuous_ofReal.comp (tebCutoff_continuous δ)).mul
        (Complex.continuous_ofReal.comp hQ_cont)).mul hA0_cont
    rw [continuous_iff_continuousAt]
    intro τ
    rcases lt_trichotomy τ 0 with hτ | hτ | hτ
    · exact (hpre_cont.continuousOn.mul hK_neg).continuousAt (isOpen_Iio.mem_nhds hτ)
    · subst hτ
      have hev : F =ᶠ[𝓝 (0 : ℝ)] 0 := by
        have h2δ : 0 < 2 * δ := mul_pos zero_lt_two hδ_pos
        filter_upwards [isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr h2δ, h2δ⟩] with t ht
        dsimp [F]
        have hχ0 : tebCutoff δ t = 0 := tebCutoff_eq_zero hδ_pos (abs_le.mpr ⟨ht.1.le, ht.2.le⟩)
        rw [hχ0, Complex.ofReal_zero, zero_mul, zero_mul, zero_mul]
      exact (continuousAt_const (y := (0 : ℂ))).congr hev.symm
    · exact (hpre_cont.continuousOn.mul hK_pos).continuousAt (isOpen_Ioi.mem_nhds hτ)
  have hF_int : Integrable F := by
    have hdom : Integrable (fun τ : ℝ => (1 / ζ₀.re) * P.C_a ^ 2 * I.c ^ (5 / 6 : ℝ) *
        ((1 + |τ|) ^ (P.M + 5) * Real.exp (-τ ^ 2))) :=
      (integrable_one_add_abs_rpow_mul_exp_neg_sq (by linarith [P.hM])).const_mul _
    exact hdom.mono' hF_cont.aestronglyMeasurable (ae_of_all _ fun τ => by
      simpa [Real.norm_eq_abs] using hF_maj τ)
  refine ⟨hF_int, ?_⟩
  rw [integral_real_eq_pos_add_neg hF_int]
  have h1 := jchi_half_osc_bound I hσ₀ hσ₀_le hξ (Or.inl rfl)
    (by simp only [one_mul]; exact hF_int.integrableOn)
  have h2 := jchi_half_osc_bound I hσ₀ hσ₀_le hξ (Or.inr rfl)
    (by simp only [neg_one_mul]; exact hF_int.comp_neg.integrableOn)
  simp only [one_mul, neg_one_mul] at h1 h2
  calc ‖(∫ τ in Ioi (0 : ℝ), F τ) + ∫ τ in Ioi (0 : ℝ), F (-τ)‖
      ≤ ‖∫ τ in Ioi (0 : ℝ), F τ‖ + ‖∫ τ in Ioi (0 : ℝ), F (-τ)‖ := norm_add_le _ _
    _ ≤ (tebBandOscConst P / 2 / ζ₀.re) * I.c ^ (5 / 6 : ℝ) *
          (I.c⁻¹ + I.c ^ (-(1 / 2 : ℝ)) * min (I.τ_0 ξ ^ 2) 1 *
            if P.A_0 * I.c ^ (-(1 / 3 : ℝ)) < I.τ_0 ξ then 1 else 0) +
        (tebBandOscConst P / 2 / ζ₀.re) * I.c ^ (5 / 6 : ℝ) *
          (I.c⁻¹ + I.c ^ (-(1 / 2 : ℝ)) * min (I.τ_0 ξ ^ 2) 1 *
            if P.A_0 * I.c ^ (-(1 / 3 : ℝ)) < I.τ_0 ξ then 1 else 0) :=
        add_le_add h1 h2
    _ = (tebBandOscConst P / ζ₀.re) * I.c ^ (5 / 6 : ℝ) *
          (I.c⁻¹ + I.c ^ (-(1 / 2 : ℝ)) * min (I.τ_0 ξ ^ 2) 1 *
            if P.A_0 * I.c ^ (-(1 / 3 : ℝ)) < I.τ_0 ξ then 1 else 0) := by
        ring

/-- Universal constant `C_Y` in Proposition `TE.3(1)` (`TE.9`), depending only on `P`. -/
noncomputable def tebBandConst (P : BandReductionParams) : ℝ :=
  let ρ_min := P.κ_ζ * P.b / 3
  let C_pf := ρ_min ^ (5 / 2 : ℝ) * (0.965 : ℝ) ^ (5 / 2 : ℝ) * Real.exp (-0.04)
  let C_gauss5 := ∫ τ : ℝ, (1 + |τ|) ^ (5 : ℝ) * Real.exp (-τ ^ 2)
  let C_core := 8 * P.A_0 * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (P.M + 5 / 2) * P.C_W
  let C_sub := P.C_a * C_gauss5 / P.κ_sub
  let C_tail := C_core + C_sub + 2 * tebBandOscConst P
  let C_band := tebBandOscConst P * max (P.C_τ * (P.b ^ 2 + 1)) 1
  max C_tail C_band / (C_pf * ρ_min)

lemma tebBandConst_pos (P : BandReductionParams) : 0 < tebBandConst P := by
  unfold tebBandConst
  have hρ_min : 0 < P.κ_ζ * P.b / 3 := div_pos (mul_pos P.hκ_ζ P.hb) (by norm_num)
  have hC_pf : 0 < (P.κ_ζ * P.b / 3) ^ (5 / 2 : ℝ) * (0.965 : ℝ) ^ (5 / 2 : ℝ) * Real.exp (-0.04) := by
    positivity
  have h_osc := tebBandOscConst_pos P
  have h_gauss : 0 ≤ ∫ τ : ℝ, (1 + |τ|) ^ (5 : ℝ) * Real.exp (-τ ^ 2) :=
    integral_nonneg fun τ => mul_nonneg (Real.rpow_nonneg (by linarith [abs_nonneg τ]) _) (Real.exp_pos _).le
  have hA0 := P.hA_0
  have hCW := P.hC_W
  have hC_core : 0 < 8 * P.A_0 * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (P.M + 5 / 2) * P.C_W := by
    positivity
  have hC_sub : 0 ≤ P.C_a * (∫ τ : ℝ, (1 + |τ|) ^ (5 : ℝ) * Real.exp (-τ ^ 2)) / P.κ_sub := by
    have := P.hC_a.le; have := P.hκ_sub; positivity
  have hC_tail : 0 < 8 * P.A_0 * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (P.M + 5 / 2) * P.C_W +
      P.C_a * (∫ τ : ℝ, (1 + |τ|) ^ (5 : ℝ) * Real.exp (-τ ^ 2)) / P.κ_sub +
      2 * tebBandOscConst P := by linarith
  exact div_pos (lt_of_lt_of_le hC_tail (le_max_left _ _)) (mul_pos hC_pf hρ_min)

private lemma teb_H_bounded {P : BandReductionParams} (I : BandReductionInstance P) :
    ∃ M_H : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖tebPrefactor I.c ζ * I.W_tilde ζ‖ ≤ M_H := by
  have hc_pos : 0 < I.c := lt_of_lt_of_le zero_lt_one I.hc
  set K_bd : ℝ := P.M + 5
  have hK_nn : 0 ≤ K_bd := by dsimp [K_bd]; linarith [P.hM]
  set m_H := Nat.ceil (K_bd / 2)
  refine ⟨I.c ^ (5 / 6 : ℝ) * P.C_W * (2 : ℝ) ^ K_bd * ((2 : ℝ) ^ K_bd * max 1 (Nat.factorial m_H : ℝ)),
    fun ζ h0 h1 => ?_⟩
  have hpf := norm_tebPrefactor_le I.c hc_pos.le h0 h1
  have hW := I.hW_bound ζ h0 h1
  have hζ1 : ‖ζ‖ ≤ 1 + |ζ.im| := by
    have hre1 : ζ.re ^ 2 ≤ 1 := by nlinarith
    have hsq : ‖ζ‖ ^ 2 ≤ (1 + |ζ.im|) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      nlinarith [sq_abs ζ.im, abs_nonneg ζ.im]
    nlinarith [norm_nonneg ζ, abs_nonneg ζ.im]
  have h1ζ : 1 + ‖ζ‖ ≤ 2 * (1 + |ζ.im|) := by linarith [abs_nonneg ζ.im]
  have hprod_le : ‖ζ * (1 - ζ)‖ ≤ (1 + ‖ζ‖) ^ 2 := by
    rw [norm_mul, sq]
    have h1 : ‖ζ‖ ≤ 1 + ‖ζ‖ := by linarith
    have h2 : ‖1 - ζ‖ ≤ 1 + ‖ζ‖ := (norm_sub_le 1 ζ).trans (by rw [norm_one])
    exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  have hpow_le : ‖ζ * (1 - ζ)‖ ^ (5 / 2 : ℝ) * (1 + ‖ζ‖) ^ P.M ≤
      (2 : ℝ) ^ K_bd * (1 + |ζ.im|) ^ K_bd := by
    have h1 : ‖ζ * (1 - ζ)‖ ^ (5 / 2 : ℝ) ≤ (1 + ‖ζ‖) ^ (5 : ℝ) := by
      have h := Real.rpow_le_rpow (norm_nonneg _) hprod_le (by norm_num : (0 : ℝ) ≤ 5 / 2)
      rwa [← Real.rpow_natCast (1 + ‖ζ‖) 2, ← Real.rpow_mul (by positivity),
        show (2 : ℕ) * (5 / 2 : ℝ) = 5 by norm_num] at h
    have h2 : (1 + ‖ζ‖) ^ (5 : ℝ) * (1 + ‖ζ‖) ^ P.M ≤ (2 * (1 + |ζ.im|)) ^ K_bd := by
      rw [← Real.rpow_add (by positivity : 0 < 1 + ‖ζ‖)]
      have hpow_eq : (5 : ℝ) + P.M = K_bd := by dsimp [K_bd]; ring
      rw [hpow_eq]
      exact Real.rpow_le_rpow (by positivity) h1ζ hK_nn
    calc ‖ζ * (1 - ζ)‖ ^ (5 / 2 : ℝ) * (1 + ‖ζ‖) ^ P.M
        ≤ (1 + ‖ζ‖) ^ (5 : ℝ) * (1 + ‖ζ‖) ^ P.M := by gcongr
      _ ≤ (2 * (1 + |ζ.im|)) ^ K_bd := h2
      _ = (2 : ℝ) ^ K_bd * (1 + |ζ.im|) ^ K_bd := Real.mul_rpow (by norm_num) (by positivity)
  have him_bound : (1 + |ζ.im|) ^ K_bd * Real.exp (-ζ.im ^ 2) ≤
      (2 : ℝ) ^ K_bd * max 1 (Nat.factorial m_H : ℝ) := by
    rcases le_or_gt |ζ.im| 1 with him | him
    · have h1 : (1 + |ζ.im|) ^ K_bd ≤ (2 : ℝ) ^ K_bd :=
        Real.rpow_le_rpow (by positivity) (by linarith) hK_nn
      have h2 : Real.exp (-ζ.im ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ζ.im])
      calc (1 + |ζ.im|) ^ K_bd * Real.exp (-ζ.im ^ 2)
          ≤ (2 : ℝ) ^ K_bd * 1 := mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
        _ ≤ (2 : ℝ) ^ K_bd * max 1 (Nat.factorial m_H : ℝ) := by
            gcongr; exact le_max_left _ _
    · have h1 : (1 + |ζ.im|) ^ K_bd ≤ (2 : ℝ) ^ K_bd * |ζ.im| ^ K_bd := by
        rw [← Real.mul_rpow (by norm_num) (abs_nonneg _)]
        exact Real.rpow_le_rpow (by positivity) (by linarith) hK_nn
      have hr := rpow_mul_exp_neg_sq_le_fac (p := K_bd) (q := 0) (by linarith) him.le
      simp only [add_zero, neg_zero, Real.rpow_zero, mul_one, sq_abs] at hr
      calc (1 + |ζ.im|) ^ K_bd * Real.exp (-ζ.im ^ 2)
          ≤ ((2 : ℝ) ^ K_bd * |ζ.im| ^ K_bd) * Real.exp (-ζ.im ^ 2) := by gcongr
        _ = (2 : ℝ) ^ K_bd * (|ζ.im| ^ K_bd * Real.exp (-ζ.im ^ 2)) := by ring
        _ ≤ (2 : ℝ) ^ K_bd * (Nat.factorial m_H : ℝ) := by gcongr
        _ ≤ (2 : ℝ) ^ K_bd * max 1 (Nat.factorial m_H : ℝ) := by
            gcongr; exact le_max_right _ _
  have hc56 : 0 ≤ I.c ^ (5 / 6 : ℝ) := Real.rpow_nonneg hc_pos.le _
  calc ‖tebPrefactor I.c ζ * I.W_tilde ζ‖
      = ‖tebPrefactor I.c ζ‖ * ‖I.W_tilde ζ‖ := norm_mul _ _
    _ ≤ (I.c ^ (5 / 6 : ℝ) * ‖ζ * (1 - ζ)‖ ^ (5 / 2 : ℝ) * Real.exp (-ζ.im ^ 2)) *
          (P.C_W * (1 + ‖ζ‖) ^ P.M) := by gcongr
    _ = I.c ^ (5 / 6 : ℝ) * P.C_W * (‖ζ * (1 - ζ)‖ ^ (5 / 2 : ℝ) * (1 + ‖ζ‖) ^ P.M) *
          Real.exp (-ζ.im ^ 2) := by ring
    _ ≤ I.c ^ (5 / 6 : ℝ) * P.C_W * ((2 : ℝ) ^ K_bd * (1 + |ζ.im|) ^ K_bd) *
          Real.exp (-ζ.im ^ 2) := by
        gcongr; exact mul_nonneg (Real.rpow_nonneg hc_pos.le _) P.hC_W.le
    _ = I.c ^ (5 / 6 : ℝ) * P.C_W * (2 : ℝ) ^ K_bd * ((1 + |ζ.im|) ^ K_bd * Real.exp (-ζ.im ^ 2)) := by
        ring
    _ ≤ I.c ^ (5 / 6 : ℝ) * P.C_W * (2 : ℝ) ^ K_bd *
          ((2 : ℝ) ^ K_bd * max 1 (Nat.factorial m_H : ℝ)) := by
        gcongr; exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hc_pos.le _) P.hC_W.le) (by positivity)

private lemma teb_core_bound {P : BandReductionParams} (I : BandReductionInstance P)
    {ζ₀ : ℂ} (hσ₀ : 0 < ζ₀.re) (hσ₀_le : ζ₀.re ≤ 0.04)
    (hcore_int : Integrable (fun τ : ℝ => ((1 - tebCutoff (P.A_0 * I.c ^ (-(1 / 3 : ℝ))) τ : ℝ) : ℂ) *
      (stripPoissonQ ζ₀.re ζ₀.im I.ε τ : ℂ) * (tebAmp0 I.c τ * I.W_tilde ((τ : ℂ) * Complex.I)))) :
    ‖∫ τ : ℝ, ((1 - tebCutoff (P.A_0 * I.c ^ (-(1 / 3 : ℝ))) τ : ℝ) : ℂ) *
      (stripPoissonQ ζ₀.re ζ₀.im I.ε τ : ℂ) * (tebAmp0 I.c τ * I.W_tilde ((τ : ℂ) * Complex.I))‖ ≤
    (8 * P.A_0 * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (P.M + 5 / 2) * P.C_W / ζ₀.re) *
      I.c ^ (-(1 / 3 : ℝ)) := by
  have hc_pos : 0 < I.c := lt_of_lt_of_le zero_lt_one I.hc
  have hσ₁ : ζ₀.re < 1 := by linarith
  set δ := P.A_0 * I.c ^ (-(1 / 3 : ℝ))
  have hδ_pos : 0 < δ := by dsimp [δ]; have := P.hA_0; positivity
  have hε_abs : |I.ε| ≤ 1 := by rcases I.hε with hε | hε <;> norm_num [hε]
  have hQ_bd : ∀ τ : ℝ, |stripPoissonQ ζ₀.re ζ₀.im I.ε τ| ≤ 1 / ζ₀.re := fun τ =>
    (stripPoissonQ_abs_le hσ₀ hσ₁ ζ₀.im hε_abs τ).trans (stripPoissonCalQ_le hσ₀ hσ₀_le ζ₀.im τ)
  let coreFn : ℝ → ℂ := fun τ => ((1 - tebCutoff δ τ : ℝ) : ℂ) *
    (stripPoissonQ ζ₀.re ζ₀.im I.ε τ : ℂ) * (tebAmp0 I.c τ * I.W_tilde ((τ : ℂ) * Complex.I))
  have hsupp : ∫ τ : ℝ, coreFn τ = ∫ τ in Icc (-4 * δ) (4 * δ), coreFn τ := by
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun τ hτ => ?_
    have hgt : 4 * δ ≤ |τ| := by
      by_contra hlt
      have hlt' := abs_lt.mp (not_le.mp hlt)
      exact hτ ⟨by linarith, by linarith⟩
    dsimp [coreFn]
    rw [tebCutoff_eq_one hδ_pos hgt, sub_self, Complex.ofReal_zero, zero_mul, zero_mul]
  change ‖∫ τ : ℝ, coreFn τ‖ ≤ _
  rw [hsupp]
  have hpt : ∀ τ ∈ Icc (-4 * δ) (4 * δ), ‖coreFn τ‖ ≤
      (1 / ζ₀.re) * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (P.M + 5 / 2) * P.C_W := by
    intro τ hτ
    have habs : |τ| ≤ 4 * δ := abs_le.mpr ⟨by linarith [hτ.1], hτ.2⟩
    have hδ_le : δ ≤ P.A_0 := by
      dsimp [δ]
      have hc_le : I.c ^ (-(1 / 3 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos I.hc (by norm_num)
      nlinarith [P.hA_0]
    have habs_A : |τ| ≤ 4 * P.A_0 := habs.trans (by linarith)
    have h1χ : |1 - tebCutoff δ τ| ≤ 1 := abs_le.mpr
      ⟨by linarith [tebCutoff_le_one δ τ], by linarith [tebCutoff_nonneg δ τ]⟩
    have hQ := hQ_bd τ
    have hA0 : ‖tebAmp0 I.c τ‖ ≤ (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (5 / 2 : ℝ) := by
      have h1 := norm_tebAmp0_le hc_pos.le (τ := τ)
      have hτ52 : |τ| ^ (5 / 2 : ℝ) ≤ (4 * δ) ^ (5 / 2 : ℝ) :=
        Real.rpow_le_rpow (abs_nonneg _) habs (by norm_num)
      have h1τ52 : (1 + |τ|) ^ (5 / 2 : ℝ) ≤ (1 + 4 * P.A_0) ^ (5 / 2 : ℝ) :=
        Real.rpow_le_rpow (by linarith [abs_nonneg τ]) (by linarith) (by norm_num)
      have hexp1 : Real.exp (-τ ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg τ])
      have hc_cancel : I.c ^ (5 / 6 : ℝ) * (4 * δ) ^ (5 / 2 : ℝ) = (4 * P.A_0) ^ (5 / 2 : ℝ) := by
        dsimp [δ]
        rw [show 4 * (P.A_0 * I.c ^ (-(1 / 3 : ℝ))) = (4 * P.A_0) * I.c ^ (-(1 / 3 : ℝ)) by ring]
        rw [Real.mul_rpow (by have := P.hA_0; positivity) (Real.rpow_nonneg hc_pos.le _),
          ← Real.rpow_mul hc_pos.le]
        have hexp : -(1 / 3 : ℝ) * (5 / 2 : ℝ) = -(5 / 6 : ℝ) := by norm_num
        rw [hexp, ← mul_assoc, mul_comm (I.c ^ (5 / 6 : ℝ)), mul_assoc, ← Real.rpow_add hc_pos]
        simp
      have hcτ : I.c ^ (5 / 6 : ℝ) * |τ| ^ (5 / 2 : ℝ) ≤ I.c ^ (5 / 6 : ℝ) * (4 * δ) ^ (5 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hτ52 (Real.rpow_nonneg hc_pos.le _)
      have hcτ1 : I.c ^ (5 / 6 : ℝ) * |τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) ≤
          I.c ^ (5 / 6 : ℝ) * (4 * δ) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (5 / 2 : ℝ) :=
        mul_le_mul hcτ h1τ52 (Real.rpow_nonneg (by linarith [abs_nonneg τ]) _)
          (mul_nonneg (Real.rpow_nonneg hc_pos.le _) (Real.rpow_nonneg (by positivity) _))
      calc ‖tebAmp0 I.c τ‖
          ≤ I.c ^ (5 / 6 : ℝ) * |τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * Real.exp (-τ ^ 2) := h1
        _ ≤ (I.c ^ (5 / 6 : ℝ) * (4 * δ) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (5 / 2 : ℝ)) * 1 :=
            mul_le_mul hcτ1 hexp1 (Real.exp_pos _).le
              (mul_nonneg (mul_nonneg (Real.rpow_nonneg hc_pos.le _) (Real.rpow_nonneg (by positivity) _))
                (Real.rpow_nonneg (by have := P.hA_0; positivity) _))
        _ = (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (5 / 2 : ℝ) := by rw [hc_cancel, mul_one]
    have hW : ‖I.W_tilde ((τ : ℂ) * Complex.I)‖ ≤ P.C_W * (1 + 4 * P.A_0) ^ P.M := by
      have hre : ((τ : ℂ) * Complex.I).re = 0 := by simp
      have hb := I.hW_bound ((τ : ℂ) * Complex.I) hre.ge (by linarith)
      have hnorm : ‖(τ : ℂ) * Complex.I‖ = |τ| := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
      rw [hnorm] at hb
      have hpow : (1 + |τ|) ^ P.M ≤ (1 + 4 * P.A_0) ^ P.M :=
        Real.rpow_le_rpow (by linarith [abs_nonneg τ]) (by linarith) P.hM
      exact hb.trans (mul_le_mul_of_nonneg_left hpow P.hC_W.le)
    have h1pow : (1 + 4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ P.M =
        (1 + 4 * P.A_0) ^ (P.M + 5 / 2) := by
      rw [← Real.rpow_add (by have := P.hA_0; positivity)]
      ring_nf
    dsimp [coreFn]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    have h12 : |1 - tebCutoff δ τ| * |stripPoissonQ ζ₀.re ζ₀.im I.ε τ| ≤ 1 * (1 / ζ₀.re) :=
      mul_le_mul h1χ hQ (abs_nonneg _) zero_le_one
    have h34 : ‖tebAmp0 I.c τ‖ * ‖I.W_tilde ((τ : ℂ) * Complex.I)‖ ≤
        ((4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (5 / 2 : ℝ)) *
          (P.C_W * (1 + 4 * P.A_0) ^ P.M) :=
      mul_le_mul hA0 hW (norm_nonneg _) (by have := P.hA_0; positivity)
    calc |1 - tebCutoff δ τ| * |stripPoissonQ ζ₀.re ζ₀.im I.ε τ| *
          (‖tebAmp0 I.c τ‖ * ‖I.W_tilde ((τ : ℂ) * Complex.I)‖)
        ≤ (1 * (1 / ζ₀.re)) *
            (((4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (5 / 2 : ℝ)) *
              (P.C_W * (1 + 4 * P.A_0) ^ P.M)) :=
          mul_le_mul h12 h34 (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
      _ = (1 / ζ₀.re) * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (P.M + 5 / 2) * P.C_W := by
          rw [← h1pow]; ring
  have hint_core_Icc : IntegrableOn coreFn (Icc (-4 * δ) (4 * δ)) := hcore_int.integrableOn
  have hconst_int : IntegrableOn (fun _ : ℝ =>
      (1 / ζ₀.re) * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (P.M + 5 / 2) * P.C_W)
      (Icc (-4 * δ) (4 * δ)) := integrableOn_const (hs := measure_Icc_lt_top.ne)
  calc ‖∫ τ in Icc (-4 * δ) (4 * δ), coreFn τ‖
      ≤ ∫ τ in Icc (-4 * δ) (4 * δ), ‖coreFn τ‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ _ in Icc (-4 * δ) (4 * δ),
          ((1 / ζ₀.re) * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (P.M + 5 / 2) * P.C_W) :=
        setIntegral_mono_on hint_core_Icc.norm hconst_int measurableSet_Icc hpt
    _ = (volume.real (Icc (-4 * δ) (4 * δ))) *
          ((1 / ζ₀.re) * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (P.M + 5 / 2) * P.C_W) := by
        rw [setIntegral_const, smul_eq_mul]
    _ = (8 * P.A_0 * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (P.M + 5 / 2) * P.C_W / ζ₀.re) *
          I.c ^ (-(1 / 3 : ℝ)) := by
        rw [Real.volume_real_Icc_of_le (by linarith)]
        dsimp [δ]
        ring

private lemma teb_tail_bound {P : BandReductionParams} (I : BandReductionInstance P)
    {ζ₀ : ℂ} (hσ₀ : 0 < ζ₀.re) (hσ₀_le : ζ₀.re ≤ 0.04) :
    let δ := P.A_0 * I.c ^ (-(1 / 3 : ℝ))
    let C_gauss5 := ∫ τ : ℝ, (1 + |τ|) ^ (5 : ℝ) * Real.exp (-τ ^ 2)
    ‖∫ τ : ℝ, (tebCutoff δ τ : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im I.ε τ : ℂ) *
      (tebAmp0 I.c τ * I.W_tilde ((τ : ℂ) * Complex.I))‖ ≤
    ((P.C_a * C_gauss5 / P.κ_sub + 2 * tebBandOscConst P) / ζ₀.re) * I.c ^ (5 / 6 : ℝ) * I.c⁻¹ +
    (tebBandOscConst P * max (P.C_τ * (P.b ^ 2 + 1)) 1 / ζ₀.re) *
      I.c ^ (5 / 6 : ℝ) * I.c ^ (-(1 / 2 : ℝ)) * (bandB1 I + bandB2 I) := by
  intro δ C_gauss5
  have hc_pos : 0 < I.c := lt_of_lt_of_le zero_lt_one I.hc
  have hσ₁ : ζ₀.re < 1 := by linarith
  have hR_pos : 0 < I.R := lt_of_lt_of_le (by have := P.hb; positivity) I.hR_lb
  have hε_abs : |I.ε| ≤ 1 := by rcases I.hε with hε | hε <;> norm_num [hε]
  have hQ_bd : ∀ τ : ℝ, |stripPoissonQ ζ₀.re ζ₀.im I.ε τ| ≤ 1 / ζ₀.re := fun τ =>
    (stripPoissonQ_abs_le hσ₀ hσ₁ ζ₀.im hε_abs τ).trans (stripPoissonCalQ_le hσ₀ hσ₀_le ζ₀.im τ)
  have : IsFiniteMeasure I.dmPos := I.hdmPos_fin
  have : IsFiniteMeasure I.dmNeg := I.hdmNeg_fin
  let g0 : ℝ → ℂ := fun τ =>
    (tebCutoff δ τ : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im I.ε τ : ℂ) * tebAmp0 I.c τ
  let G : ℝ → ℝ → ℂ := fun τ ξ => g0 τ * I.K_edge τ ξ
  have hg0_cont : Continuous g0 := by
    have hQ_cont : Continuous (stripPoissonQ ζ₀.re ζ₀.im I.ε) := by
      unfold stripPoissonQ stripPoissonP stripPoissonP1
      refine Continuous.div continuous_const
        ((Real.continuous_cosh.comp (continuous_const.mul (continuous_id.sub continuous_const))).sub
          continuous_const) (fun τ => (stripPoissonP_den_pos hσ₀ hσ₁ _).ne') |>.add
        (continuous_const.mul (Continuous.div continuous_const
          ((Real.continuous_cosh.comp (continuous_const.mul (continuous_id.add continuous_const))).add
            continuous_const) (fun τ => (stripPoissonP1_den_pos hσ₀ hσ₁ _).ne')))
    exact ((Complex.continuous_ofReal.comp (tebCutoff_continuous δ)).mul
      (Complex.continuous_ofReal.comp hQ_cont)).mul (continuous_tebAmp0 I.c)
  have hG_meas : Measurable (Function.uncurry G) :=
    (hg0_cont.measurable.comp measurable_fst).mul I.hK_meas
  have hg0_bd : ∀ τ : ℝ, ‖g0 τ‖ ≤ (1 / ζ₀.re) * I.c ^ (5 / 6 : ℝ) *
      ((1 + |τ|) ^ (5 : ℝ) * Real.exp (-τ ^ 2)) := fun τ => by
    dsimp [g0]
    have hχ : |tebCutoff δ τ| ≤ 1 := abs_le.mpr ⟨by linarith [tebCutoff_nonneg δ τ], tebCutoff_le_one δ τ⟩
    have hQ := hQ_bd τ
    have hamp := norm_tebAmp0_le hc_pos.le (τ := τ)
    have h1τ : |τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) ≤ (1 + |τ|) ^ (5 : ℝ) := by
      have h1 : |τ| ^ (5 / 2 : ℝ) ≤ (1 + |τ|) ^ (5 / 2 : ℝ) :=
        Real.rpow_le_rpow (abs_nonneg _) (by linarith) (by norm_num)
      have h1τ_pos : 0 < 1 + |τ| := by linarith [abs_nonneg τ]
      calc |τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ)
          ≤ (1 + |τ|) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) := by gcongr
        _ = (1 + |τ|) ^ (5 : ℝ) := by rw [← Real.rpow_add h1τ_pos]; norm_num
    have h12 : |tebCutoff δ τ| * |stripPoissonQ ζ₀.re ζ₀.im I.ε τ| ≤ 1 * (1 / ζ₀.re) :=
      mul_le_mul hχ hQ (abs_nonneg _) zero_le_one
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |tebCutoff δ τ| * |stripPoissonQ ζ₀.re ζ₀.im I.ε τ| * ‖tebAmp0 I.c τ‖
        ≤ (1 * (1 / ζ₀.re)) *
            (I.c ^ (5 / 6 : ℝ) * |τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * Real.exp (-τ ^ 2)) :=
          mul_le_mul h12 hamp (norm_nonneg _) (by positivity)
      _ = (1 / ζ₀.re) * I.c ^ (5 / 6 : ℝ) * (|τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ)) * Real.exp (-τ ^ 2) := by
          ring
      _ ≤ (1 / ζ₀.re) * I.c ^ (5 / 6 : ℝ) * (1 + |τ|) ^ (5 : ℝ) * Real.exp (-τ ^ 2) := by
          gcongr
      _ = (1 / ζ₀.re) * I.c ^ (5 / 6 : ℝ) * ((1 + |τ|) ^ (5 : ℝ) * Real.exp (-τ ^ 2)) := by ring
  have hK_all_bd : ∀ τ ξ : ℝ, 0 < ξ → ‖I.K_edge τ ξ‖ ≤ max P.C_a (P.C_a ^ 2) * (1 + |τ|) ^ P.M := by
    intro τ ξ hξ_pos
    by_cases hE : ξ ∈ I.E_sub
    · have hexp : Real.exp (-P.κ_sub * I.c) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr P.hκ_sub.le) hc_pos.le)
      have h1τ : (1 : ℝ) ≤ (1 + |τ|) ^ P.M := Real.one_le_rpow (by linarith [abs_nonneg τ]) P.hM
      have hCa_nn : 0 ≤ P.C_a := P.hC_a.le
      calc ‖I.K_edge τ ξ‖
          ≤ P.C_a * Real.exp (-P.κ_sub * I.c) := I.hK_sub ξ hE τ
        _ ≤ P.C_a * 1 := mul_le_mul_of_nonneg_left hexp P.hC_a.le
        _ ≤ max P.C_a (P.C_a ^ 2) * (1 + |τ|) ^ P.M := by
            have h1 : P.C_a * 1 ≤ max P.C_a (P.C_a ^ 2) * (1 + |τ|) ^ P.M :=
              mul_le_mul (le_max_left P.C_a (P.C_a ^ 2)) h1τ zero_le_one (by positivity)
            exact h1
    · have hξ' : ξ ∈ Ioi 0 \ I.E_sub := ⟨hξ_pos, hE⟩
      rw [I.hK_factor ξ hξ' τ, norm_mul, norm_mul]
      have ha0 : ‖I.a_0 τ‖ ≤ P.C_a * (1 + |τ|) ^ P.M :=
        le_trans (by linarith [norm_nonneg (I.a_0' τ)]) (I.ha_0_bd τ)
      have ha2 : ‖I.a_2 ξ‖ ≤ P.C_a := I.ha_2_bd ξ hξ'
      have hexp : ‖Complex.exp ((I.c : ℂ) * ((I.R_0 τ ξ : ℂ) - Complex.I * (I.Phi τ ξ : ℂ)))‖ ≤ 1 := by
        rw [Complex.norm_exp]; apply Real.exp_le_one_iff.mpr
        have hre : ((I.c : ℂ) * ((I.R_0 τ ξ : ℂ) - Complex.I * (I.Phi τ ξ : ℂ))).re = I.c * I.R_0 τ ξ := by
          simp [Complex.mul_re]
        rw [hre]; exact mul_nonpos_of_nonneg_of_nonpos hc_pos.le (I.hR_0_nonpos ξ hξ' τ)
      have ha02 : ‖I.a_0 τ‖ * ‖I.a_2 ξ‖ ≤ (P.C_a * (1 + |τ|) ^ P.M) * P.C_a :=
        mul_le_mul ha0 ha2 (norm_nonneg _) (mul_nonneg P.hC_a.le (Real.rpow_nonneg (by linarith [abs_nonneg τ]) _))
      calc ‖I.a_0 τ‖ * ‖I.a_2 ξ‖ *
            ‖Complex.exp ((I.c : ℂ) * ((I.R_0 τ ξ : ℂ) - Complex.I * (I.Phi τ ξ : ℂ)))‖
          ≤ ((P.C_a * (1 + |τ|) ^ P.M) * P.C_a) * 1 :=
            mul_le_mul ha02 hexp (norm_nonneg _)
              (mul_nonneg (mul_nonneg P.hC_a.le (Real.rpow_nonneg (by linarith [abs_nonneg τ]) _)) P.hC_a.le)
        _ = P.C_a ^ 2 * (1 + |τ|) ^ P.M := by ring
        _ ≤ max P.C_a (P.C_a ^ 2) * (1 + |τ|) ^ P.M := by gcongr; exact le_max_right _ _
  have hG_int_of : ∀ (dm : Measure ℝ), IsFiniteMeasure dm → dm (Iic 0) = 0 →
      Integrable (Function.uncurry G) (volume.prod dm) := by
    intro dm hfin hsupp
    have : IsFiniteMeasure dm := hfin
    let dom : ℝ → ℝ := fun τ => (1 / ζ₀.re) * max P.C_a (P.C_a ^ 2) * I.c ^ (5 / 6 : ℝ) *
      ((1 + |τ|) ^ (P.M + 5) * Real.exp (-τ ^ 2))
    have hdom_int : Integrable dom :=
      (integrable_one_add_abs_rpow_mul_exp_neg_sq (by linarith [P.hM])).const_mul _
    have hprod_int : Integrable (fun p : ℝ × ℝ => dom p.1) (volume.prod dm) := by
      rw [integrable_prod_iff hdom_int.aestronglyMeasurable.comp_fst]
      refine ⟨ae_of_all _ fun τ => by dsimp only; exact integrable_const (dom τ), ?_⟩
      have hdom_nn : ∀ τ, 0 ≤ dom τ := fun τ => by
        dsimp [dom]; have := P.hC_a.le; positivity
      refine (hdom_int.const_mul (dm univ).toReal).congr (ae_of_all _ fun τ => ?_)
      dsimp only
      rw [integral_const, smul_eq_mul, Measure.real_def, Real.norm_of_nonneg (hdom_nn τ)]
    refine hprod_int.mono' hG_meas.aestronglyMeasurable ?_
    have hae_pos : ∀ᵐ ξ ∂dm, 0 < ξ := by
      have : dm (Ioi (0 : ℝ))ᶜ = 0 := by rw [compl_Ioi]; exact hsupp
      exact ae_iff.mpr this
    have hs_meas : MeasurableSet {p : ℝ × ℝ | 0 < p.2} :=
      measurableSet_lt measurable_const measurable_snd
    have hae_prod : ∀ᵐ p : ℝ × ℝ ∂(volume.prod dm), 0 < p.2 := by
      rw [Measure.ae_prod_iff_ae_ae hs_meas]
      exact ae_of_all _ fun _ => hae_pos
    filter_upwards [hae_prod] with p hp
    dsimp [Function.uncurry, G, dom]
    rw [norm_mul]
    have hg := hg0_bd p.1
    have hK := hK_all_bd p.1 p.2 hp
    have hpow : (1 + |p.1|) ^ (5 : ℝ) * (1 + |p.1|) ^ P.M = (1 + |p.1|) ^ (P.M + 5) := by
      rw [← Real.rpow_add (by linarith [abs_nonneg p.1])]; ring_nf
    have hCa_nn : 0 ≤ P.C_a := P.hC_a.le
    calc ‖g0 p.1‖ * ‖I.K_edge p.1 p.2‖
        ≤ ((1 / ζ₀.re) * I.c ^ (5 / 6 : ℝ) * ((1 + |p.1|) ^ (5 : ℝ) * Real.exp (-p.1 ^ 2))) *
            (max P.C_a (P.C_a ^ 2) * (1 + |p.1|) ^ P.M) := by
          gcongr
      _ = (1 / ζ₀.re) * max P.C_a (P.C_a ^ 2) * I.c ^ (5 / 6 : ℝ) *
            (((1 + |p.1|) ^ (5 : ℝ) * (1 + |p.1|) ^ P.M) * Real.exp (-p.1 ^ 2)) := by ring
      _ = (1 / ζ₀.re) * max P.C_a (P.C_a ^ 2) * I.c ^ (5 / 6 : ℝ) *
            ((1 + |p.1|) ^ (P.M + 5) * Real.exp (-p.1 ^ 2)) := by rw [hpow]
  have hG_pos_int := hG_int_of I.dmPos I.hdmPos_fin I.hdmPos_supp
  have hG_neg_int := hG_int_of I.dmNeg I.hdmNeg_fin I.hdmNeg_supp
  have htail_eq : (fun τ : ℝ => (tebCutoff δ τ : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im I.ε τ : ℂ) *
        (tebAmp0 I.c τ * I.W_tilde ((τ : ℂ) * Complex.I))) =
      fun τ => (∫ ξ : ℝ, G τ ξ ∂I.dmPos) - ∫ ξ : ℝ, G τ ξ ∂I.dmNeg := by
    ext τ
    dsimp [G, g0]
    rw [I.hW_edge τ, integral_const_mul, integral_const_mul]
    ring
  have hleft_pos : Integrable (fun τ => ∫ ξ : ℝ, G τ ξ ∂I.dmPos) := hG_pos_int.integral_prod_left
  have hleft_neg : Integrable (fun τ => ∫ ξ : ℝ, G τ ξ ∂I.dmNeg) := hG_neg_int.integral_prod_left
  let Jχ : ℝ → ℂ := fun ξ => ∫ τ : ℝ, G τ ξ
  have hJ_pos_int : Integrable Jχ I.dmPos := hG_pos_int.integral_prod_right
  have hJ_neg_int : Integrable Jχ I.dmNeg := hG_neg_int.integral_prod_right
  have htail_split_int : ∫ τ : ℝ, (tebCutoff δ τ : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im I.ε τ : ℂ) *
        (tebAmp0 I.c τ * I.W_tilde ((τ : ℂ) * Complex.I)) =
      (∫ ξ : ℝ, Jχ ξ ∂I.dmPos) - ∫ ξ : ℝ, Jχ ξ ∂I.dmNeg := by
    rw [htail_eq, integral_sub hleft_pos hleft_neg, integral_integral_swap hG_pos_int,
      integral_integral_swap hG_neg_int]
  have h_restrict_Ioi : ∀ (dm : Measure ℝ), dm (Iic 0) = 0 → Integrable Jχ dm →
      ∫ ξ : ℝ, Jχ ξ ∂dm = (∫ ξ in I.E_sub, Jχ ξ ∂dm) + ∫ ξ in Ioi 0 \ I.E_sub, Jχ ξ ∂dm := by
    intro dm hsupp hint_dm
    have h1 := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hint_dm
    have hcompl : ∫ ξ in (Ioi (0 : ℝ))ᶜ, Jχ ξ ∂dm = 0 := by
      rw [compl_Ioi, Measure.restrict_eq_zero.mpr hsupp, integral_zero_measure]
    rw [hcompl, add_zero] at h1
    have hE_union : I.E_sub ∪ (Ioi 0 \ I.E_sub) = Ioi 0 :=
      union_sdiff_cancel (I.hE_sub_sub.trans Ioo_subset_Ioi_self)
    have hE_disj : Disjoint I.E_sub (Ioi 0 \ I.E_sub) := disjoint_sdiff_self_right
    have h2 := setIntegral_union hE_disj (measurableSet_Ioi.diff I.hE_sub_meas)
      hint_dm.integrableOn hint_dm.integrableOn
    rw [hE_union] at h2
    rw [← h1, h2]
  have hgauss5_int : Integrable (fun τ : ℝ => (1 + |τ|) ^ (5 : ℝ) * Real.exp (-τ ^ 2)) :=
    integrable_one_add_abs_rpow_mul_exp_neg_sq (by norm_num)
  have hsub_pt : ∀ ξ ∈ I.E_sub, ‖Jχ ξ‖ ≤
      (1 / ζ₀.re) * P.C_a * I.c ^ (5 / 6 : ℝ) * C_gauss5 * Real.exp (-P.κ_sub * I.c) := by
    intro ξ hξ
    dsimp [Jχ, G]
    have hmaj : ∀ τ : ℝ, ‖g0 τ * I.K_edge τ ξ‖ ≤
        ((1 / ζ₀.re) * P.C_a * I.c ^ (5 / 6 : ℝ) * Real.exp (-P.κ_sub * I.c)) *
          ((1 + |τ|) ^ (5 : ℝ) * Real.exp (-τ ^ 2)) := fun τ => by
      rw [norm_mul]
      have hg := hg0_bd τ
      have hK := I.hK_sub ξ hξ τ
      calc ‖g0 τ‖ * ‖I.K_edge τ ξ‖
          ≤ ((1 / ζ₀.re) * I.c ^ (5 / 6 : ℝ) * ((1 + |τ|) ^ (5 : ℝ) * Real.exp (-τ ^ 2))) *
              (P.C_a * Real.exp (-P.κ_sub * I.c)) := by gcongr
        _ = _ := by ring
    have hdom_int := hgauss5_int.const_mul
      ((1 / ζ₀.re) * P.C_a * I.c ^ (5 / 6 : ℝ) * Real.exp (-P.κ_sub * I.c))
    have hGξ_int : Integrable (fun τ => g0 τ * I.K_edge τ ξ) := by
      have hmeas_τ : Measurable (fun τ => g0 τ * I.K_edge τ ξ) :=
        hg0_cont.measurable.mul (I.hK_meas.comp (measurable_id.prodMk measurable_const))
      exact hdom_int.mono' hmeas_τ.aestronglyMeasurable (ae_of_all _ hmaj)
    calc ‖∫ τ : ℝ, g0 τ * I.K_edge τ ξ‖
        ≤ ∫ τ : ℝ, ‖g0 τ * I.K_edge τ ξ‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ τ : ℝ, ((1 / ζ₀.re) * P.C_a * I.c ^ (5 / 6 : ℝ) * Real.exp (-P.κ_sub * I.c)) *
            ((1 + |τ|) ^ (5 : ℝ) * Real.exp (-τ ^ 2)) :=
          integral_mono hGξ_int.norm hdom_int hmaj
      _ = (1 / ζ₀.re) * P.C_a * I.c ^ (5 / 6 : ℝ) * C_gauss5 * Real.exp (-P.κ_sub * I.c) := by
          rw [integral_const_mul]; dsimp [C_gauss5]; ring
  have h_sub_bd : ∀ (dm : Measure ℝ), IsFiniteMeasure dm → Integrable Jχ dm →
      ‖∫ ξ in I.E_sub, Jχ ξ ∂dm‖ ≤
        (dm univ).toReal * ((1 / ζ₀.re) * P.C_a * I.c ^ (5 / 6 : ℝ) * C_gauss5 *
          Real.exp (-P.κ_sub * I.c)) := by
    intro dm hfin hint_dm
    have hconst : IntegrableOn (fun _ : ℝ =>
        (1 / ζ₀.re) * P.C_a * I.c ^ (5 / 6 : ℝ) * C_gauss5 * Real.exp (-P.κ_sub * I.c)) I.E_sub dm :=
      integrableOn_const (hs := (measure_lt_top dm I.E_sub).ne)
    calc ‖∫ ξ in I.E_sub, Jχ ξ ∂dm‖
        ≤ ∫ ξ in I.E_sub, ‖Jχ ξ‖ ∂dm := norm_integral_le_integral_norm _
      _ ≤ ∫ _ in I.E_sub,
            ((1 / ζ₀.re) * P.C_a * I.c ^ (5 / 6 : ℝ) * C_gauss5 * Real.exp (-P.κ_sub * I.c)) ∂dm :=
          setIntegral_mono_on hint_dm.integrableOn.norm hconst I.hE_sub_meas hsub_pt
      _ = (dm.real I.E_sub) *
            ((1 / ζ₀.re) * P.C_a * I.c ^ (5 / 6 : ℝ) * C_gauss5 * Real.exp (-P.κ_sub * I.c)) := by
          rw [setIntegral_const, smul_eq_mul]
      _ ≤ (dm univ).toReal *
            ((1 / ζ₀.re) * P.C_a * I.c ^ (5 / 6 : ℝ) * C_gauss5 * Real.exp (-P.κ_sub * I.c)) := by
          have hle : dm.real I.E_sub ≤ (dm univ).toReal :=
            ENNReal.toReal_mono (measure_ne_top dm univ) (measure_mono (subset_univ _))
          have hgauss_nn : 0 ≤ C_gauss5 :=
            integral_nonneg fun τ => mul_nonneg (Real.rpow_nonneg (by linarith [abs_nonneg τ]) _) (Real.exp_pos _).le
          have hCa_nn := P.hC_a.le
          gcongr
  have hsub_tot : ‖∫ ξ in I.E_sub, Jχ ξ ∂I.dmPos‖ + ‖∫ ξ in I.E_sub, Jχ ξ ∂I.dmNeg‖ ≤
      (P.C_a * C_gauss5 / P.κ_sub / ζ₀.re) * I.c ^ (5 / 6 : ℝ) * I.c⁻¹ := by
    have h1 := h_sub_bd I.dmPos I.hdmPos_fin hJ_pos_int
    have h2 := h_sub_bd I.dmNeg I.hdmNeg_fin hJ_neg_int
    have hsum_dm : (I.dmPos univ).toReal + (I.dmNeg univ).toReal ≤ 1 := I.hdm_tv
    have hexp_inv : Real.exp (-P.κ_sub * I.c) ≤ (1 / P.κ_sub) * I.c⁻¹ := by
      have hkx : P.κ_sub * I.c + 1 ≤ Real.exp (P.κ_sub * I.c) :=
        Real.add_one_le_exp (P.κ_sub * I.c)
      have hkx' : P.κ_sub * I.c ≤ Real.exp (P.κ_sub * I.c) := by linarith
      rw [neg_mul, Real.exp_neg, one_div]
      calc (Real.exp (P.κ_sub * I.c))⁻¹
          ≤ (P.κ_sub * I.c)⁻¹ := inv_anti₀ (mul_pos P.hκ_sub hc_pos) hkx'
        _ = P.κ_sub⁻¹ * I.c⁻¹ := mul_inv_rev P.κ_sub I.c |>.trans (mul_comm _ _)
    have hgauss_nn : 0 ≤ C_gauss5 :=
      integral_nonneg fun τ => mul_nonneg (Real.rpow_nonneg (by linarith [abs_nonneg τ]) _) (Real.exp_pos _).le
    have hcoeff_nn : 0 ≤ (1 / ζ₀.re) * P.C_a * I.c ^ (5 / 6 : ℝ) * C_gauss5 := by
      have := P.hC_a.le; positivity
    calc ‖∫ ξ in I.E_sub, Jχ ξ ∂I.dmPos‖ + ‖∫ ξ in I.E_sub, Jχ ξ ∂I.dmNeg‖
        ≤ ((I.dmPos univ).toReal + (I.dmNeg univ).toReal) *
            ((1 / ζ₀.re) * P.C_a * I.c ^ (5 / 6 : ℝ) * C_gauss5 * Real.exp (-P.κ_sub * I.c)) := by
          linarith
      _ ≤ 1 * ((1 / ζ₀.re) * P.C_a * I.c ^ (5 / 6 : ℝ) * C_gauss5 * ((1 / P.κ_sub) * I.c⁻¹)) := by
          gcongr
      _ = (P.C_a * C_gauss5 / P.κ_sub / ζ₀.re) * I.c ^ (5 / 6 : ℝ) * I.c⁻¹ := by ring
  have hJχ_eq : ∀ ξ ∈ Ioi 0 \ I.E_sub, Jχ ξ = ∫ τ : ℝ, (tebCutoff δ τ : ℂ) *
      (stripPoissonQ ζ₀.re ζ₀.im I.ε τ : ℂ) * tebAmp0 I.c τ * I.K_edge τ ξ := by
    intro ξ _; rfl
  let phi1 : ℝ → ℝ := (Icc I.T (I.Delta (-I.R))).indicator
    (fun t => P.C_τ * I.c ^ (-(7 / 6 : ℝ)) * (-I.u_tilde t))
  let phi2 : ℝ → ℝ := (Ici (I.Delta (-I.R))).indicator (fun _ => I.c ^ (-(1 / 2 : ℝ)))
  have hphi1_nn : ∀ ξ, 0 ≤ phi1 ξ := fun ξ => by
    dsimp [phi1]
    by_cases hξ : ξ ∈ Icc I.T (I.Delta (-I.R))
    · rw [Set.indicator_of_mem hξ]
      have h1 := I.hτ_0_band ξ hξ
      have h2 : 0 ≤ I.τ_0 ξ ^ 2 := sq_nonneg _
      have hc23 : 0 < P.C_τ * I.c ^ (-(2 / 3 : ℝ)) := mul_pos P.hC_τ (Real.rpow_pos_of_pos hc_pos _)
      have hu : 0 ≤ -I.u_tilde ξ := nonneg_of_mul_nonneg_right (h2.trans h1) hc23
      have := P.hC_τ; positivity
    · rw [Set.indicator_of_notMem hξ]
  have hphi2_nn : ∀ ξ, 0 ≤ phi2 ξ := fun ξ => by
    dsimp [phi2]
    by_cases hξ : ξ ∈ Ici (I.Delta (-I.R))
    · rw [Set.indicator_of_mem hξ]; positivity
    · rw [Set.indicator_of_notMem hξ]
  have hphi1_int : Integrable phi1 I.dmPos :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (IntegrableOn.congr_fun (I.hu_tilde_int.const_mul (P.C_τ * I.c ^ (-(7 / 6 : ℝ))))
        (fun ξ _ => by simp) measurableSet_Icc)
  have hphi2_int : Integrable phi2 I.dmPos :=
    (integrable_indicator_iff measurableSet_Ici).mpr
      (integrableOn_const (hs := (measure_lt_top I.dmPos _).ne))
  have hmain_pos_bd : ‖∫ ξ in Ioi 0 \ I.E_sub, Jχ ξ ∂I.dmPos‖ ≤
      (tebBandOscConst P / ζ₀.re) * I.c ^ (5 / 6 : ℝ) *
        (I.c⁻¹ + I.c ^ (-(1 / 2 : ℝ)) * max (P.C_τ * (P.b ^ 2 + 1)) 1 * (bandB1 I + bandB2 I)) := by
    have hpt_pos : ∀ ξ ∈ Ioi 0 \ I.E_sub, ‖Jχ ξ‖ ≤
        (tebBandOscConst P / ζ₀.re) * I.c ^ (5 / 6 : ℝ) * (I.c⁻¹ + phi1 ξ + phi2 ξ) := by
      intro ξ hξ
      have hosc := (jchi_osc_bound I hσ₀ hσ₀_le hξ).2
      rw [← hJχ_eq ξ hξ] at hosc
      refine hosc.trans ?_
      have hc_nn : 0 ≤ (tebBandOscConst P / ζ₀.re) * I.c ^ (5 / 6 : ℝ) := by
        have := tebBandOscConst_pos P; positivity
      refine mul_le_mul_of_nonneg_left ?_ hc_nn
      by_cases hT : ξ < I.T
      · have hτ_le : I.τ_0 ξ ≤ δ := I.hτ_0_below ξ ⟨hT, hξ.2⟩
        dsimp only [δ] at hτ_le
        simp only [not_lt.mpr hτ_le, ite_false, mul_zero, add_zero]
        linarith [hphi1_nn ξ, hphi2_nn ξ]
      · have hT' : I.T ≤ ξ := not_lt.mp hT
        rw [add_assoc]
        refine add_le_add le_rfl ?_
        have h_if : (if δ < I.τ_0 ξ then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
        have hmin_nn : 0 ≤ min (I.τ_0 ξ ^ 2) 1 := le_min (sq_nonneg _) zero_le_one
        have h_step : I.c ^ (-(1 / 2 : ℝ)) * min (I.τ_0 ξ ^ 2) 1 *
              (if δ < I.τ_0 ξ then 1 else 0) ≤
            I.c ^ (-(1 / 2 : ℝ)) * min (I.τ_0 ξ ^ 2) 1 :=
          mul_le_of_le_one_right (mul_nonneg (Real.rpow_nonneg hc_pos.le _) hmin_nn) h_if
        refine h_step.trans ?_
        rcases le_or_gt ξ (I.Delta (-I.R)) with hD | hD
        · have hmem : ξ ∈ Icc I.T (I.Delta (-I.R)) := ⟨hT', hD⟩
          dsimp [phi1]
          rw [Set.indicator_of_mem hmem]
          have hband := I.hτ_0_band ξ hmem
          have hcexp : I.c ^ (-(1 / 2 : ℝ)) * (P.C_τ * I.c ^ (-(2 / 3 : ℝ)) * (-I.u_tilde ξ)) =
              P.C_τ * I.c ^ (-(7 / 6 : ℝ)) * (-I.u_tilde ξ) := by
            have h1 : I.c ^ (-(1 / 2 : ℝ)) * I.c ^ (-(2 / 3 : ℝ)) = I.c ^ (-(7 / 6 : ℝ)) := by
              rw [← Real.rpow_add hc_pos]; norm_num
            calc I.c ^ (-(1 / 2 : ℝ)) * (P.C_τ * I.c ^ (-(2 / 3 : ℝ)) * (-I.u_tilde ξ))
                = P.C_τ * (I.c ^ (-(1 / 2 : ℝ)) * I.c ^ (-(2 / 3 : ℝ))) * (-I.u_tilde ξ) := by ring
              _ = P.C_τ * I.c ^ (-(7 / 6 : ℝ)) * (-I.u_tilde ξ) := by rw [h1]
          calc I.c ^ (-(1 / 2 : ℝ)) * min (I.τ_0 ξ ^ 2) 1
              ≤ I.c ^ (-(1 / 2 : ℝ)) * (I.τ_0 ξ ^ 2) :=
                mul_le_mul_of_nonneg_left (min_le_left _ _) (Real.rpow_nonneg hc_pos.le _)
            _ ≤ I.c ^ (-(1 / 2 : ℝ)) * (P.C_τ * I.c ^ (-(2 / 3 : ℝ)) * (-I.u_tilde ξ)) :=
                mul_le_mul_of_nonneg_left hband (Real.rpow_nonneg hc_pos.le _)
            _ = P.C_τ * I.c ^ (-(7 / 6 : ℝ)) * (-I.u_tilde ξ) := hcexp
            _ ≤ P.C_τ * I.c ^ (-(7 / 6 : ℝ)) * (-I.u_tilde ξ) + phi2 ξ := le_add_of_nonneg_right (hphi2_nn ξ)
        · have hmem : ξ ∈ Ici (I.Delta (-I.R)) := hD.le
          dsimp [phi2]
          rw [Set.indicator_of_mem hmem]
          calc I.c ^ (-(1 / 2 : ℝ)) * min (I.τ_0 ξ ^ 2) 1
              ≤ I.c ^ (-(1 / 2 : ℝ)) * 1 :=
                mul_le_mul_of_nonneg_left (min_le_right _ _) (Real.rpow_nonneg hc_pos.le _)
            _ = I.c ^ (-(1 / 2 : ℝ)) := mul_one _
            _ ≤ phi1 ξ + I.c ^ (-(1 / 2 : ℝ)) := le_add_of_nonneg_left (hphi1_nn ξ)
    let rhsFn : ℝ → ℝ := fun ξ =>
      (tebBandOscConst P / ζ₀.re) * I.c ^ (5 / 6 : ℝ) * (I.c⁻¹ + phi1 ξ + phi2 ξ)
    have hrhs_int : Integrable rhsFn I.dmPos :=
      (((integrable_const _).add hphi1_int).add hphi2_int).const_mul _
    have hmono : ∫ ξ in Ioi 0 \ I.E_sub, ‖Jχ ξ‖ ∂I.dmPos ≤ ∫ ξ in Ioi 0 \ I.E_sub, rhsFn ξ ∂I.dmPos :=
      setIntegral_mono_on hJ_pos_int.integrableOn.norm hrhs_int.integrableOn
        (measurableSet_Ioi.diff I.hE_sub_meas) hpt_pos
    have hrhs_nn : ∀ ξ, 0 ≤ rhsFn ξ := fun ξ => by
      have := tebBandOscConst_pos P
      have h1 := hphi1_nn ξ; have h2 := hphi2_nn ξ
      positivity
    have hsub_le_univ : ∫ ξ in Ioi 0 \ I.E_sub, rhsFn ξ ∂I.dmPos ≤ ∫ ξ : ℝ, rhsFn ξ ∂I.dmPos :=
      setIntegral_le_integral hrhs_int (ae_of_all _ hrhs_nn)
    have hphi1_eval : ∫ ξ : ℝ, phi1 ξ ∂I.dmPos = P.C_τ * I.c ^ (-(7 / 6 : ℝ)) * (I.R * bandB1 I) := by
      dsimp [phi1, bandB1]
      rw [integral_indicator measurableSet_Icc, integral_const_mul]
      field_simp [hR_pos.ne']
    have hphi2_eval : ∫ ξ : ℝ, phi2 ξ ∂I.dmPos = I.c ^ (-(1 / 2 : ℝ)) * bandB2 I := by
      dsimp [phi2, bandB2]
      rw [integral_indicator measurableSet_Ici, setIntegral_const, smul_eq_mul, mul_comm,
        Measure.real_def]
    have hrhs_eval : ∫ ξ : ℝ, rhsFn ξ ∂I.dmPos =
        (tebBandOscConst P / ζ₀.re) * I.c ^ (5 / 6 : ℝ) *
          (I.c⁻¹ * (I.dmPos univ).toReal +
            P.C_τ * I.c ^ (-(7 / 6 : ℝ)) * I.R * bandB1 I + I.c ^ (-(1 / 2 : ℝ)) * bandB2 I) := by
      dsimp [rhsFn]
      have h01 : Integrable (fun ξ : ℝ => I.c⁻¹ + phi1 ξ) I.dmPos :=
        (integrable_const I.c⁻¹).add hphi1_int
      rw [integral_const_mul, integral_add h01 hphi2_int,
        integral_add (integrable_const I.c⁻¹) hphi1_int,
        integral_const, smul_eq_mul, Measure.real_def, hphi1_eval, hphi2_eval]
      ring_nf
    have hdmPos_le : (I.dmPos univ).toReal ≤ 1 := by
      linarith [ENNReal.toReal_nonneg (a := I.dmNeg univ), I.hdm_tv]
    have hR_le : I.R ≤ (P.b ^ 2 + 1) * I.c ^ (2 / 3 : ℝ) := by
      have hc23 : 1 ≤ I.c ^ (2 / 3 : ℝ) := Real.one_le_rpow I.hc (by norm_num)
      linarith [I.hR_ub]
    have hB1_term : P.C_τ * I.c ^ (-(7 / 6 : ℝ)) * I.R * bandB1 I ≤
        I.c ^ (-(1 / 2 : ℝ)) * max (P.C_τ * (P.b ^ 2 + 1)) 1 * bandB1 I := by
      have hc_eq : I.c ^ (-(7 / 6 : ℝ)) * I.c ^ (2 / 3 : ℝ) = I.c ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_add hc_pos]; norm_num
      have hB1_nn := bandB1_nonneg I
      calc P.C_τ * I.c ^ (-(7 / 6 : ℝ)) * I.R * bandB1 I
          ≤ P.C_τ * I.c ^ (-(7 / 6 : ℝ)) * ((P.b ^ 2 + 1) * I.c ^ (2 / 3 : ℝ)) * bandB1 I := by
            gcongr; exact mul_nonneg P.hC_τ.le (Real.rpow_nonneg hc_pos.le _)
        _ = (P.C_τ * (P.b ^ 2 + 1)) * (I.c ^ (-(7 / 6 : ℝ)) * I.c ^ (2 / 3 : ℝ)) * bandB1 I := by ring
        _ = I.c ^ (-(1 / 2 : ℝ)) * (P.C_τ * (P.b ^ 2 + 1)) * bandB1 I := by rw [hc_eq]; ring
        _ ≤ I.c ^ (-(1 / 2 : ℝ)) * max (P.C_τ * (P.b ^ 2 + 1)) 1 * bandB1 I := by
            gcongr; exact le_max_left _ _
    have hB2_term : I.c ^ (-(1 / 2 : ℝ)) * bandB2 I ≤
        I.c ^ (-(1 / 2 : ℝ)) * max (P.C_τ * (P.b ^ 2 + 1)) 1 * bandB2 I := by
      have hB2_nn := bandB2_nonneg I
      have h1 : (1 : ℝ) ≤ max (P.C_τ * (P.b ^ 2 + 1)) 1 := le_max_right _ _
      calc I.c ^ (-(1 / 2 : ℝ)) * bandB2 I
          = I.c ^ (-(1 / 2 : ℝ)) * 1 * bandB2 I := by ring
        _ ≤ I.c ^ (-(1 / 2 : ℝ)) * max (P.C_τ * (P.b ^ 2 + 1)) 1 * bandB2 I := by gcongr
    have hc_osc_nn : 0 ≤ (tebBandOscConst P / ζ₀.re) * I.c ^ (5 / 6 : ℝ) := by
      have := tebBandOscConst_pos P; positivity
    calc ‖∫ ξ in Ioi 0 \ I.E_sub, Jχ ξ ∂I.dmPos‖
        ≤ ∫ ξ in Ioi 0 \ I.E_sub, ‖Jχ ξ‖ ∂I.dmPos := norm_integral_le_integral_norm _
      _ ≤ ∫ ξ in Ioi 0 \ I.E_sub, rhsFn ξ ∂I.dmPos := hmono
      _ ≤ ∫ ξ : ℝ, rhsFn ξ ∂I.dmPos := hsub_le_univ
      _ = (tebBandOscConst P / ζ₀.re) * I.c ^ (5 / 6 : ℝ) *
            (I.c⁻¹ * (I.dmPos univ).toReal +
              P.C_τ * I.c ^ (-(7 / 6 : ℝ)) * I.R * bandB1 I + I.c ^ (-(1 / 2 : ℝ)) * bandB2 I) := hrhs_eval
      _ ≤ (tebBandOscConst P / ζ₀.re) * I.c ^ (5 / 6 : ℝ) *
            (I.c⁻¹ + I.c ^ (-(1 / 2 : ℝ)) * max (P.C_τ * (P.b ^ 2 + 1)) 1 * (bandB1 I + bandB2 I)) := by
          refine mul_le_mul_of_nonneg_left ?_ hc_osc_nn
          have hinv_le : I.c⁻¹ * (I.dmPos univ).toReal ≤ I.c⁻¹ :=
            mul_le_of_le_one_right (by positivity) hdmPos_le
          linarith
  have hmain_neg_bd : ‖∫ ξ in Ioi 0 \ I.E_sub, Jχ ξ ∂I.dmNeg‖ ≤
      (tebBandOscConst P / ζ₀.re) * I.c ^ (5 / 6 : ℝ) * I.c⁻¹ := by
    have hae_bd : ∀ᵐ ξ ∂(I.dmNeg.restrict (Ioi 0 \ I.E_sub)),
        ‖Jχ ξ‖ ≤ (tebBandOscConst P / ζ₀.re) * I.c ^ (5 / 6 : ℝ) * I.c⁻¹ := by
      rw [ae_restrict_iff' (measurableSet_Ioi.diff I.hE_sub_meas)]
      have hneg_Ici : ∀ᵐ ξ ∂I.dmNeg, ξ < I.T := by
        rw [ae_iff]; simp only [not_lt]; exact I.hdm_nonneg_tail
      filter_upwards [hneg_Ici] with ξ hξ_lt hξ_mem
      have hosc := (jchi_osc_bound I hσ₀ hσ₀_le hξ_mem).2
      rw [← hJχ_eq ξ hξ_mem] at hosc
      simp only [not_lt.mpr (I.hτ_0_below ξ ⟨hξ_lt, hξ_mem.2⟩), ite_false, mul_zero,
        add_zero] at hosc
      exact hosc
    have hconst_int : IntegrableOn (fun _ : ℝ =>
        (tebBandOscConst P / ζ₀.re) * I.c ^ (5 / 6 : ℝ) * I.c⁻¹) (Ioi 0 \ I.E_sub) I.dmNeg :=
      integrableOn_const (hs := (measure_lt_top I.dmNeg _).ne)
    have hdmNeg_le : (I.dmNeg univ).toReal ≤ 1 := by
      linarith [ENNReal.toReal_nonneg (a := I.dmPos univ), I.hdm_tv]
    have h_meas_le : I.dmNeg.real (Ioi 0 \ I.E_sub) ≤ (I.dmNeg univ).toReal :=
      ENNReal.toReal_mono (measure_ne_top I.dmNeg univ) (measure_mono (subset_univ _))
    have hc_osc_nn : 0 ≤ (tebBandOscConst P / ζ₀.re) * I.c ^ (5 / 6 : ℝ) * I.c⁻¹ := by
      have := tebBandOscConst_pos P; positivity
    calc ‖∫ ξ in Ioi 0 \ I.E_sub, Jχ ξ ∂I.dmNeg‖
        ≤ ∫ ξ in Ioi 0 \ I.E_sub, ‖Jχ ξ‖ ∂I.dmNeg := norm_integral_le_integral_norm _
      _ ≤ ∫ _ in Ioi 0 \ I.E_sub,
            ((tebBandOscConst P / ζ₀.re) * I.c ^ (5 / 6 : ℝ) * I.c⁻¹) ∂I.dmNeg :=
          integral_mono_ae hJ_neg_int.integrableOn.norm hconst_int hae_bd
      _ = I.dmNeg.real (Ioi 0 \ I.E_sub) *
            ((tebBandOscConst P / ζ₀.re) * I.c ^ (5 / 6 : ℝ) * I.c⁻¹) := by
          rw [setIntegral_const, smul_eq_mul]
      _ ≤ 1 * ((tebBandOscConst P / ζ₀.re) * I.c ^ (5 / 6 : ℝ) * I.c⁻¹) := by
          gcongr; exact h_meas_le.trans hdmNeg_le
      _ = _ := one_mul _
  rw [htail_split_int, h_restrict_Ioi I.dmPos I.hdmPos_supp hJ_pos_int,
    h_restrict_Ioi I.dmNeg I.hdmNeg_supp hJ_neg_int]
  have htri : ‖((∫ ξ in I.E_sub, Jχ ξ ∂I.dmPos) + ∫ ξ in Ioi 0 \ I.E_sub, Jχ ξ ∂I.dmPos) -
        ((∫ ξ in I.E_sub, Jχ ξ ∂I.dmNeg) + ∫ ξ in Ioi 0 \ I.E_sub, Jχ ξ ∂I.dmNeg)‖ ≤
      (‖∫ ξ in I.E_sub, Jχ ξ ∂I.dmPos‖ + ‖∫ ξ in I.E_sub, Jχ ξ ∂I.dmNeg‖) +
      ‖∫ ξ in Ioi 0 \ I.E_sub, Jχ ξ ∂I.dmPos‖ + ‖∫ ξ in Ioi 0 \ I.E_sub, Jχ ξ ∂I.dmNeg‖ := by
    have h1 := norm_sub_le ((∫ ξ in I.E_sub, Jχ ξ ∂I.dmPos) + ∫ ξ in Ioi 0 \ I.E_sub, Jχ ξ ∂I.dmPos)
      ((∫ ξ in I.E_sub, Jχ ξ ∂I.dmNeg) + ∫ ξ in Ioi 0 \ I.E_sub, Jχ ξ ∂I.dmNeg)
    have h2 := norm_add_le (∫ ξ in I.E_sub, Jχ ξ ∂I.dmPos) (∫ ξ in Ioi 0 \ I.E_sub, Jχ ξ ∂I.dmPos)
    have h3 := norm_add_le (∫ ξ in I.E_sub, Jχ ξ ∂I.dmNeg) (∫ ξ in Ioi 0 \ I.E_sub, Jχ ξ ∂I.dmNeg)
    linarith
  refine htri.trans ((add_le_add (add_le_add hsub_tot hmain_pos_bd) hmain_neg_bd).trans_eq ?_)
  ring

/-- **Proposition TE.3(1), first form, on the whole sector** (`two_edge_bootstrap.tex` `teb:mellin`, `TE.9`; the top-scale case
`r = R_J` of `ct:Wbound`, `constant_terms_lower.tex` `ct:dyadic` (1) Step 1a): the band reduction
`‖W̃_c(ζ₀)‖ ≤ C_Y c^{-5/6}(c^{1/3}(B₁ + B₂) + c^{-1/6})/cos ψ` holds for every `ζ₀` of the annulus `ρ_R/3 ≤ ‖ζ₀‖ ≤ 2ρ_R` with
`cos ψ > 0` (that is, `σ₀ > 0`); no lower bound `cos ψ ≥ c^{-1/12}` is needed (it is only used for the second form of
`teb_band_reduction`). -/
theorem teb_band_reduction_pos {P : BandReductionParams} (I : BandReductionInstance P)
    {ζ₀ : ℂ} {ψ : ℝ}
    (hζ₀_lo : rhoR P I.c I.R / 3 ≤ ‖ζ₀‖)
    (hζ₀_hi : ‖ζ₀‖ ≤ 2 * rhoR P I.c I.R)
    (hcos_eq : ζ₀.re = ‖ζ₀‖ * Real.cos ψ)
    (hcos_pos : 0 < Real.cos ψ) :
    ‖I.W_tilde ζ₀‖ ≤ tebBandConst P * I.c ^ (-(5 / 6 : ℝ)) *
        (I.c ^ (1 / 3 : ℝ) * (bandB1 I + bandB2 I) + I.c ^ (-(1 / 6 : ℝ))) / Real.cos ψ := by
  have hc_pos : 0 < I.c := lt_of_lt_of_le zero_lt_one I.hc
  set ρ_min := P.κ_ζ * P.b / 3
  have hρ_min_pos : 0 < ρ_min := div_pos (mul_pos P.hκ_ζ P.hb) (by norm_num)
  have hR_pos : 0 < I.R := lt_of_lt_of_le (by have := P.hb; positivity) I.hR_lb
  have hsqrtR_lb : P.b * I.c ^ (1 / 3 : ℝ) ≤ √I.R := by
    have hsq : (P.b * I.c ^ (1 / 3 : ℝ)) ^ 2 ≤ I.R := by
      calc (P.b * I.c ^ (1 / 3 : ℝ)) ^ 2
          = P.b ^ 2 * (I.c ^ (1 / 3 : ℝ)) ^ 2 := by ring
        _ = P.b ^ 2 * I.c ^ (2 / 3 : ℝ) := by
            rw [← Real.rpow_natCast (I.c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc_pos.le]; norm_num
        _ ≤ I.R := I.hR_lb
    exact (Real.sqrt_le_sqrt hsq).trans_eq' (Real.sqrt_sq (by have := P.hb; positivity))
  have hρR_lb : P.κ_ζ * P.b ≤ rhoR P I.c I.R := by
    unfold rhoR
    have hc_cancel : I.c ^ (-(1 / 3 : ℝ)) * I.c ^ (1 / 3 : ℝ) = 1 := by
      rw [← Real.rpow_add hc_pos]; simp
    calc P.κ_ζ * P.b
        = P.κ_ζ * P.b * 1 := by ring
      _ = P.κ_ζ * P.b * (I.c ^ (-(1 / 3 : ℝ)) * I.c ^ (1 / 3 : ℝ)) := by rw [hc_cancel]
      _ = P.κ_ζ * (I.c ^ (-(1 / 3 : ℝ)) * (P.b * I.c ^ (1 / 3 : ℝ))) := by ring
      _ ≤ P.κ_ζ * (I.c ^ (-(1 / 3 : ℝ)) * √I.R) := by gcongr; exact P.hκ_ζ.le
      _ = P.κ_ζ * I.c ^ (-(1 / 3 : ℝ)) * √I.R := by ring
  have hζ₀_min : ρ_min ≤ ‖ζ₀‖ := by
    calc ρ_min = (P.κ_ζ * P.b) / 3 := rfl
      _ ≤ rhoR P I.c I.R / 3 := by linarith
      _ ≤ ‖ζ₀‖ := hζ₀_lo
  have hζ₀_max : ‖ζ₀‖ ≤ 0.035 := hζ₀_hi.trans I.hρR_ub
  have hσ₀ : 0 < ζ₀.re := by rw [hcos_eq]; exact mul_pos (lt_of_lt_of_le hρ_min_pos hζ₀_min) hcos_pos
  have hσ₀_le : ζ₀.re ≤ 0.04 := by
    calc ζ₀.re ≤ ‖ζ₀‖ := Complex.re_le_norm _
      _ ≤ 0.035 := hζ₀_max
      _ ≤ 0.04 := by norm_num
  have hσ₁ : ζ₀.re < 1 := by linarith
  -- Define H(ζ) = tebPrefactor c ζ * W̃_c(ζ) and apply Lemma TE.1(a)
  let H : ℂ → ℂ := fun ζ => tebPrefactor I.c ζ * I.W_tilde ζ
  have hH_cont : ContinuousOn H {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} :=
    (tebPrefactor_continuousOn I.c).mul I.hW_cont
  have hH_holo : DifferentiableOn ℂ H {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} :=
    (tebPrefactor_differentiableOn I.c).mul I.hW_holo
  have hH_symm : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → H (1 - ζ) = (I.ε : ℂ) * H ζ := fun ζ h0 h1 => by
    dsimp [H]
    rw [tebPrefactor_symm, I.hW_symm ζ h0 h1]
    ring
  obtain ⟨M_H, hH_bd'⟩ := teb_H_bounded I
  obtain ⟨hQH_int, hH_rep⟩ := stripPoisson_representation_symm hH_cont hH_holo hH_bd' hH_symm hσ₀ hσ₁
  set δ := P.A_0 * I.c ^ (-(1 / 3 : ℝ))
  let coreFn : ℝ → ℂ := fun τ => ((1 - tebCutoff δ τ : ℝ) : ℂ) *
    (stripPoissonQ ζ₀.re ζ₀.im I.ε τ : ℂ) * (tebAmp0 I.c τ * I.W_tilde ((τ : ℂ) * Complex.I))
  let tailFn : ℝ → ℂ := fun τ => (tebCutoff δ τ : ℂ) *
    (stripPoissonQ ζ₀.re ζ₀.im I.ε τ : ℂ) * (tebAmp0 I.c τ * I.W_tilde ((τ : ℂ) * Complex.I))
  have h_sum_fn : (fun τ => coreFn τ + tailFn τ) =
      fun τ => (stripPoissonQ ζ₀.re ζ₀.im I.ε τ : ℂ) * H ((τ : ℂ) * Complex.I) := by
    ext τ; dsimp [coreFn, tailFn, H, tebAmp0]; push_cast; ring
  have htail_int : Integrable tailFn := by
    have h1 := hQH_int.bdd_mul (Complex.continuous_ofReal.comp (tebCutoff_continuous δ)).aestronglyMeasurable
      (ae_of_all _ fun τ => by
        dsimp only [Function.comp_def]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [tebCutoff_nonneg δ τ], tebCutoff_le_one δ τ⟩)
    have heq : (fun τ => (Complex.ofReal ∘ tebCutoff δ) τ *
        ((stripPoissonQ ζ₀.re ζ₀.im I.ε τ : ℂ) * H ((τ : ℂ) * Complex.I))) = tailFn := by
      ext τ; dsimp [tailFn, H, tebAmp0, Function.comp_def]; ring
    rwa [heq] at h1
  have hcore_int : Integrable coreFn := by
    have hsub : coreFn = fun τ => (stripPoissonQ ζ₀.re ζ₀.im I.ε τ : ℂ) * H ((τ : ℂ) * Complex.I) - tailFn τ := by
      ext τ; dsimp [coreFn, tailFn, H, tebAmp0]; push_cast; ring
    rw [hsub]
    exact hQH_int.sub htail_int
  have h_split : H ζ₀ = (∫ τ : ℝ, coreFn τ) + ∫ τ : ℝ, tailFn τ := by
    rw [hH_rep, ← integral_add hcore_int htail_int, h_sum_fn]
  set C_gauss5 := ∫ τ : ℝ, (1 + |τ|) ^ (5 : ℝ) * Real.exp (-τ ^ 2)
  set C_core := 8 * P.A_0 * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (P.M + 5 / 2) * P.C_W
  have h_core_bd := teb_core_bound I hσ₀ hσ₀_le hcore_int
  have htail_bd := teb_tail_bound I hσ₀ hσ₀_le



  have hc_core_le : I.c ^ (-(1 / 3 : ℝ)) ≤ I.c ^ (5 / 6 : ℝ) * I.c⁻¹ := by
    have hc_eq : I.c ^ (5 / 6 : ℝ) * I.c⁻¹ = I.c ^ (-(1 / 6 : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hc_pos]; norm_num
    rw [hc_eq]
    exact Real.rpow_le_rpow_of_exponent_le I.hc (by norm_num)
  have hH_tot_bd : ‖H ζ₀‖ ≤
      ((C_core + P.C_a * C_gauss5 / P.κ_sub + 2 * tebBandOscConst P) / ζ₀.re) *
        I.c ^ (5 / 6 : ℝ) * I.c⁻¹ +
      (tebBandOscConst P * max (P.C_τ * (P.b ^ 2 + 1)) 1 / ζ₀.re) *
        I.c ^ (5 / 6 : ℝ) * I.c ^ (-(1 / 2 : ℝ)) * (bandB1 I + bandB2 I) := by
    have htri : ‖H ζ₀‖ ≤ ‖∫ τ : ℝ, coreFn τ‖ + ‖∫ τ : ℝ, tailFn τ‖ := by
      rw [h_split]; exact norm_add_le _ _
    have hcore_nn : 0 ≤ C_core / ζ₀.re := by dsimp [C_core]; have := P.hA_0; have := P.hC_W; positivity
    have hcore' : (C_core / ζ₀.re) * I.c ^ (-(1 / 3 : ℝ)) ≤
        (C_core / ζ₀.re) * (I.c ^ (5 / 6 : ℝ) * I.c⁻¹) :=
      mul_le_mul_of_nonneg_left hc_core_le hcore_nn
    dsimp only at htail_bd
    refine htri.trans ((add_le_add (h_core_bd.trans hcore') htail_bd).trans_eq ?_)
    dsimp [C_core, C_gauss5]
    ring
  -- Divide by ‖tebPrefactor I.c ζ₀‖ and use ‖ζ₀‖ ≥ ρ_min
  set C_pf := ρ_min ^ (5 / 2 : ℝ) * (0.965 : ℝ) ^ (5 / 2 : ℝ) * Real.exp (-0.04)
  have hC_pf_pos : 0 < C_pf := by positivity
  have hpf_lb : I.c ^ (5 / 6 : ℝ) * C_pf ≤ ‖tebPrefactor I.c ζ₀‖ :=
    norm_tebPrefactor_ge_on_annulus hc_pos hρ_min_pos hζ₀_min hζ₀_max
  have hσ₀_lb : ρ_min * Real.cos ψ ≤ ζ₀.re := by
    rw [hcos_eq]
    exact mul_le_mul_of_nonneg_right hζ₀_min hcos_pos.le
  have hinv_σ₀ : 1 / ζ₀.re ≤ 1 / (ρ_min * Real.cos ψ) :=
    one_div_le_one_div_of_le (mul_pos hρ_min_pos hcos_pos) hσ₀_lb
  set C_tail := C_core + P.C_a * C_gauss5 / P.κ_sub + 2 * tebBandOscConst P
  set C_band := tebBandOscConst P * max (P.C_τ * (P.b ^ 2 + 1)) 1
  have h_gauss_nn : 0 ≤ C_gauss5 :=
    integral_nonneg fun τ => mul_nonneg (Real.rpow_nonneg (by linarith [abs_nonneg τ]) _) (Real.exp_pos _).le
  have hC_tail_nn : 0 ≤ C_tail := by
    dsimp [C_tail, C_core]
    have := tebBandOscConst_pos P; have := P.hA_0; have := P.hC_W; have := P.hC_a; have := P.hκ_sub
    positivity
  have hC_band_nn : 0 ≤ C_band := by
    dsimp [C_band]; have := tebBandOscConst_pos P; positivity
  have hc56_pos : 0 < I.c ^ (5 / 6 : ℝ) := Real.rpow_pos_of_pos hc_pos _
  have hW_mul : I.c ^ (5 / 6 : ℝ) * C_pf * ‖I.W_tilde ζ₀‖ ≤ ‖H ζ₀‖ := by
    dsimp [H]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hpf_lb (norm_nonneg _)
  have hc_inv_split : I.c⁻¹ = I.c ^ (-(5 / 6 : ℝ)) * I.c ^ (-(1 / 6 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hc_pos]; norm_num
  have hc_half_split : I.c ^ (-(1 / 2 : ℝ)) = I.c ^ (-(5 / 6 : ℝ)) * I.c ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_add hc_pos]; norm_num
  have hbound1 : ‖I.W_tilde ζ₀‖ ≤ tebBandConst P * I.c ^ (-(5 / 6 : ℝ)) *
      (I.c ^ (1 / 3 : ℝ) * (bandB1 I + bandB2 I) + I.c ^ (-(1 / 6 : ℝ))) / Real.cos ψ := by
    have hM := max C_tail C_band
    have h1 : ‖H ζ₀‖ ≤ I.c ^ (5 / 6 : ℝ) * ((max C_tail C_band / (ρ_min * Real.cos ψ)) *
        (I.c ^ (-(1 / 2 : ℝ)) * (bandB1 I + bandB2 I) + I.c⁻¹)) := by
      have hB_nn : 0 ≤ bandB1 I + bandB2 I := add_nonneg (bandB1_nonneg I) (bandB2_nonneg I)
      have hinv_σ₀' : ζ₀.re⁻¹ ≤ (ρ_min * Real.cos ψ)⁻¹ := by
        simpa only [one_div] using hinv_σ₀
      have ht1 : C_tail / ζ₀.re ≤ max C_tail C_band / (ρ_min * Real.cos ψ) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul (le_max_left _ _) hinv_σ₀' (by positivity) (le_trans hC_tail_nn (le_max_left _ _))
      have ht2 : C_band / ζ₀.re ≤ max C_tail C_band / (ρ_min * Real.cos ψ) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul (le_max_right _ _) hinv_σ₀' (by positivity) (le_trans hC_band_nn (le_max_right _ _))
      calc ‖H ζ₀‖
          ≤ (C_tail / ζ₀.re) * I.c ^ (5 / 6 : ℝ) * I.c⁻¹ +
              (C_band / ζ₀.re) * I.c ^ (5 / 6 : ℝ) * I.c ^ (-(1 / 2 : ℝ)) * (bandB1 I + bandB2 I) :=
            hH_tot_bd
        _ ≤ (max C_tail C_band / (ρ_min * Real.cos ψ)) * I.c ^ (5 / 6 : ℝ) * I.c⁻¹ +
              (max C_tail C_band / (ρ_min * Real.cos ψ)) * I.c ^ (5 / 6 : ℝ) * I.c ^ (-(1 / 2 : ℝ)) *
                (bandB1 I + bandB2 I) := by gcongr
        _ = I.c ^ (5 / 6 : ℝ) * ((max C_tail C_band / (ρ_min * Real.cos ψ)) *
              (I.c ^ (-(1 / 2 : ℝ)) * (bandB1 I + bandB2 I) + I.c⁻¹)) := by ring
    have h2 : C_pf * ‖I.W_tilde ζ₀‖ ≤ (max C_tail C_band / (ρ_min * Real.cos ψ)) *
        (I.c ^ (-(1 / 2 : ℝ)) * (bandB1 I + bandB2 I) + I.c⁻¹) := by
      have htot : I.c ^ (5 / 6 : ℝ) * (C_pf * ‖I.W_tilde ζ₀‖) ≤
          I.c ^ (5 / 6 : ℝ) * ((max C_tail C_band / (ρ_min * Real.cos ψ)) *
            (I.c ^ (-(1 / 2 : ℝ)) * (bandB1 I + bandB2 I) + I.c⁻¹)) := by
        calc I.c ^ (5 / 6 : ℝ) * (C_pf * ‖I.W_tilde ζ₀‖)
            = I.c ^ (5 / 6 : ℝ) * C_pf * ‖I.W_tilde ζ₀‖ := by ring
          _ ≤ ‖H ζ₀‖ := hW_mul
          _ ≤ _ := h1
      exact le_of_mul_le_mul_left htot hc56_pos
    have h3 : ‖I.W_tilde ζ₀‖ ≤ (max C_tail C_band / (C_pf * ρ_min)) *
        (I.c ^ (-(1 / 2 : ℝ)) * (bandB1 I + bandB2 I) + I.c⁻¹) / Real.cos ψ := by
      have hdiv := (le_div_iff₀' hC_pf_pos).mpr h2
      refine hdiv.trans_eq ?_
      ring
    refine h3.trans_eq ?_
    have hC_Y : max C_tail C_band / (C_pf * ρ_min) = tebBandConst P := by
      unfold tebBandConst; rfl
    rw [hC_Y, hc_inv_split, hc_half_split]
    ring
  exact hbound1

/-- **Proposition TE.3(1)** (`two_edge_bootstrap.tex` `teb:mellin`, `TE.9`):
Unified strip band reduction from `(MS1)`–`(MS2)` and the `τ₀` bounds, valid on the sector `𝔖`. -/
theorem teb_band_reduction {P : BandReductionParams} (I : BandReductionInstance P)
    {ζ₀ : ℂ} {ψ : ℝ}
    (hζ₀_lo : rhoR P I.c I.R / 3 ≤ ‖ζ₀‖)
    (hζ₀_hi : ‖ζ₀‖ ≤ 2 * rhoR P I.c I.R)
    (hcos_eq : ζ₀.re = ‖ζ₀‖ * Real.cos ψ)
    (hcos_lb : I.c ^ (-(1 / 12 : ℝ)) ≤ Real.cos ψ) :
    ‖I.W_tilde ζ₀‖ ≤ tebBandConst P * I.c ^ (-(5 / 6 : ℝ)) *
        (I.c ^ (1 / 3 : ℝ) * (bandB1 I + bandB2 I) + I.c ^ (-(1 / 6 : ℝ))) / Real.cos ψ ∧
    ‖I.W_tilde ζ₀‖ ≤ tebBandConst P * I.c ^ (-(5 / 6 : ℝ)) *
        (I.c ^ (1 / 3 : ℝ) * (bandB1 I + bandB2 I) / Real.cos ψ + I.c ^ (-(1 / 12 : ℝ))) := by
  have hc_pos : 0 < I.c := lt_of_lt_of_le zero_lt_one I.hc
  have hc112_pos : 0 < I.c ^ (-(1 / 12 : ℝ)) := Real.rpow_pos_of_pos hc_pos _
  have hcos_pos : 0 < Real.cos ψ := lt_of_lt_of_le hc112_pos hcos_lb
  have hbound1 := teb_band_reduction_pos I hζ₀_lo hζ₀_hi hcos_eq hcos_pos
  refine ⟨hbound1, hbound1.trans ?_⟩
  have hcos_inv_le : I.c ^ (-(1 / 6 : ℝ)) / Real.cos ψ ≤ I.c ^ (-(1 / 12 : ℝ)) := by
    rw [div_le_iff₀ hcos_pos]
    calc I.c ^ (-(1 / 6 : ℝ))
        = I.c ^ (-(1 / 12 : ℝ)) * I.c ^ (-(1 / 12 : ℝ)) := by
          rw [← Real.rpow_add hc_pos]; norm_num
      _ ≤ I.c ^ (-(1 / 12 : ℝ)) * Real.cos ψ :=
          mul_le_mul_of_nonneg_left hcos_lb hc112_pos.le
  have hCY_nn : 0 ≤ tebBandConst P := (tebBandConst_pos P).le
  have hc56_nn : 0 ≤ I.c ^ (-(5 / 6 : ℝ)) := (Real.rpow_pos_of_pos hc_pos _).le
  have h_eq1 : tebBandConst P * I.c ^ (-(5 / 6 : ℝ)) *
        (I.c ^ (1 / 3 : ℝ) * (bandB1 I + bandB2 I) + I.c ^ (-(1 / 6 : ℝ))) / Real.cos ψ =
      tebBandConst P * I.c ^ (-(5 / 6 : ℝ)) *
        (I.c ^ (1 / 3 : ℝ) * (bandB1 I + bandB2 I) / Real.cos ψ + I.c ^ (-(1 / 6 : ℝ)) / Real.cos ψ) := by
    ring
  rw [h_eq1]
  gcongr

/-- Quantified large-`c` form of **Proposition TE.3(1)** (`TE.9`). -/
theorem teb_band_reduction_quantified (P : BandReductionParams) :
    ∃ C_Y > 0, ∀ (I : BandReductionInstance P) (ζ₀ : ℂ) (ψ : ℝ),
      rhoR P I.c I.R / 3 ≤ ‖ζ₀‖ → ‖ζ₀‖ ≤ 2 * rhoR P I.c I.R →
      ζ₀.re = ‖ζ₀‖ * Real.cos ψ → I.c ^ (-(1 / 12 : ℝ)) ≤ Real.cos ψ →
      ‖I.W_tilde ζ₀‖ ≤ C_Y * I.c ^ (-(5 / 6 : ℝ)) *
          (I.c ^ (1 / 3 : ℝ) * (bandB1 I + bandB2 I) + I.c ^ (-(1 / 6 : ℝ))) / Real.cos ψ ∧
      ‖I.W_tilde ζ₀‖ ≤ C_Y * I.c ^ (-(5 / 6 : ℝ)) *
          (I.c ^ (1 / 3 : ℝ) * (bandB1 I + bandB2 I) / Real.cos ψ + I.c ^ (-(1 / 12 : ℝ))) :=
  ⟨tebBandConst P, tebBandConst_pos P, fun I _ _ hlo hhi hcos_eq hcos_lb =>
    teb_band_reduction I hlo hhi hcos_eq hcos_lb⟩

/-- Non-vacuity witness showing `BandReductionParams`, `BandReductionInstance`, and the sector `𝔖`
hypotheses of `teb_band_reduction` are jointly satisfiable. -/
theorem bandReductionInstance_nonvacuous :
    ∃ (P : BandReductionParams) (I : BandReductionInstance P) (ζ₀ : ℂ) (ψ : ℝ),
      rhoR P I.c I.R / 3 ≤ ‖ζ₀‖ ∧ ‖ζ₀‖ ≤ 2 * rhoR P I.c I.R ∧
      ζ₀.re = ‖ζ₀‖ * Real.cos ψ ∧ I.c ^ (-(1 / 12 : ℝ)) ≤ Real.cos ψ := by
  let P : BandReductionParams :=
    { M := 0
      b := 0.01
      κ_ζ := 1
      A_0 := 1
      C_W := 1
      C_a := 1
      c_1 := 3 / 4
      c_2 := 2
      C_ν := 1
      κ_sub := 1
      C_τ := 1
      hM := le_rfl
      hb := by norm_num
      hκ_ζ := by norm_num
      hA_0 := by norm_num
      hC_W := by norm_num
      hC_a := by norm_num
      hc_1 := by norm_num
      hc_2 := by norm_num
      hC_ν := by norm_num
      hκ_sub := by norm_num
      hC_τ := by norm_num }
  let I : BandReductionInstance P :=
    { c := 1
      ε := 1
      R := 0.0001
      hc := le_rfl
      hε := Or.inl rfl
      hR_lb := by norm_num [P]
      hR_ub := by norm_num [P]
      hρR_ub := by
        unfold rhoR
        dsimp [P]
        have hrt : √(0.0001 : ℝ) = 0.01 := by
          rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]; norm_num
        rw [hrt]
        norm_num
      W_tilde := fun _ => 0
      hW_cont := continuousOn_const
      hW_holo := differentiableOn_const _
      hW_symm := fun _ _ _ => by simp
      hW_bound := fun _ _ _ => by simp [P]
      dmPos := 0
      dmNeg := 0
      hdmPos_fin := by infer_instance
      hdmNeg_fin := by infer_instance
      hdmPos_supp := by simp
      hdmNeg_supp := by simp
      hdm_tv := by simp
      T := 1
      hdm_nonneg_tail := by simp
      E_sub := ∅
      hE_sub_meas := MeasurableSet.empty
      hE_sub_sub := empty_subset _
      K_edge := fun _ _ => 0
      hK_meas := measurable_const
      hW_edge := fun _ => by simp
      hK_sub := fun _ h _ => absurd h (notMem_empty _)
      a_0 := fun _ => 0
      a_0' := fun _ => 0
      a_2 := fun _ => 0
      R_0 := fun _ _ => 0
      Phi := fun τ _ => -τ ^ 3 / 3
      hK_factor := fun _ _ _ => by simp
      ha_2_bd := fun _ _ => by simp [P]
      ha_0_deriv := fun _ => hasDerivAt_const _ _
      ha_0_bd := fun _ => by simp [P]
      hR_0_nonpos := fun _ _ _ => le_rfl
      hR_0_cont := fun _ _ => continuousOn_const
      hR_0_even := fun _ _ _ => rfl
      hR_0_unimodal := fun _ _ => ⟨0, fun _ _ _ _ _ => le_rfl, fun _ _ _ _ _ => le_rfl⟩
      hPhi_odd := fun _ _ τ => by ring
      ν := id
      ν' := fun _ => 1
      invNu' := fun _ => 0
      hν_deriv := fun τ _ => hasDerivAt_id τ
      hν'_cont := continuousOn_const
      hν'_inv_pos := fun _ _ => by norm_num [P]
      hν'_inv_deriv := fun τ _ => by
        simpa using (hasDerivAt_const τ (1 : ℝ))
      hinvNu'_cont := continuousOn_const
      hinvNu'_int := by simp [P]
      hinvNu'_integrable := integrableOn_zero
      μ := fun _ => 0
      m := fun τ => τ ^ 2
      m' := fun τ => 2 * τ
      hPhi_deriv := fun _ _ τ _ => by
        have h : HasDerivAt (fun t : ℝ => -t ^ 3 / 3) (-(τ ^ 2)) τ := by
          have hd := (hasDerivAt_pow 3 τ).neg.div_const (3 : ℝ)
          refine hd.congr_deriv ?_; ring
        refine h.congr_deriv ?_; ring
      hm_0 := by norm_num
      hm_cont := (continuous_pow 2).continuousOn
      hm_strictMono := fun x hx y hy hxy => by nlinarith [hx.out, hy.out]
      hm_deriv := fun τ _ => by
        simpa using hasDerivAt_pow 2 τ
      hm_step := fun τ hτ => by
        have h1 : min (τ ^ 2) 1 ≤ τ ^ 2 := min_le_left _ _
        dsimp [P]; linarith
      hm_slope := fun τ hτ => by
        have hden : 1 ≤ 1 + τ ^ 3 := by linarith [pow_nonneg hτ.le 3]
        have hle : τ / (1 + τ ^ 3) ≤ τ := div_le_self hτ.le hden
        dsimp [P]
        rw [div_one]
        calc 2 * τ / (1 + τ ^ 3) = 2 * (τ / (1 + τ ^ 3)) := by ring
          _ ≤ 2 * τ := by gcongr
      τ_0 := fun _ => 0
      hτ_0_nn := fun _ => le_rfl
      hτ_0_eq_zero := fun _ _ => rfl
      hτ_0_root := fun _ h => absurd h (lt_irrefl _)
      u_tilde := fun _ => 0
      Delta := fun _ => 0
      hτ_0_below := fun _ _ => by norm_num [P]
      hτ_0_band := fun _ _ => by norm_num
      hu_tilde_int := by simp }
  refine ⟨P, I, (0.01 : ℂ), 0, ?_, ?_, ?_, ?_⟩
  · unfold rhoR
    dsimp [P, I]
    have hrt : √(0.0001 : ℝ) = 0.01 := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]; norm_num
    rw [hrt]; norm_num
  · unfold rhoR
    dsimp [P, I]
    have hrt : √(0.0001 : ℝ) = 0.01 := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]; norm_num
    rw [hrt]; norm_num
  · simp [Real.cos_zero]
    rw [show (0.01 : ℂ) = ((0.01 : ℝ) : ℂ) by norm_num, Complex.norm_real,
      Real.norm_of_nonneg (by norm_num)]
  · simp [I, Real.cos_zero]

end MainProof

section AxiomChecks

/--
info: 'FormalResearch.ModularBootstrap.StripBand.teb_band_reduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.StripBand.teb_band_reduction

/--
info: 'FormalResearch.ModularBootstrap.StripBand.teb_band_reduction_quantified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.StripBand.teb_band_reduction_quantified

/--
info: 'FormalResearch.ModularBootstrap.StripBand.bandReductionInstance_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.StripBand.bandReductionInstance_nonvacuous

end AxiomChecks

end FormalResearch.ModularBootstrap.StripBand/-- info: 'FormalResearch.ModularBootstrap.StripBand.teb_band_reduction_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.StripBand.teb_band_reduction_pos


