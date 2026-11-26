module

public import FormalResearch.SignUncertainty.StripAdmiss
public import FormalResearch.SignUncertainty.CeGenOrigin
public import FormalResearch.CohnElkies.LobeSaddleBounds
public import FormalResearch.CohnElkies.MellinT3Taylor

/-!
# `uct:gen-preedge` (F2b leaf): generalised saddle-interval asymptotic and origin shift

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, Lemma `uct:gen-preedge`
(equations `(uct:gen-lobe)` and `(uct:gen-origin)`).

This module formalises the F2b pre-edge interface combining single-strip admissibility (`uct:admiss`,
`StripAdmiss`), the first-order total-multiplier lobe saddle asymptotic (`cel:total-saddle`,
`lobe_total_saddle`), and the origin Mellin shift (`cel:L3a` (2), `ceOrigin_shift_dini`).

Main results:
* `existsUnique_saddlePoint`: existence and uniqueness of `σ_+ ∈ (0, 1)` solving
  `stripGReal σ_+ = -log (π² ξ)` on the saddle interval `Δ ∈ [Δ₁, (c/π²) exp(-π² U c^{-2/3})]`.
* `StripM1.toTotalSaddleAmp`: packages `(A0')`–`(A2')` for a `StripM1` multiplier into
  `TotalSaddleAmp c σ_star`.
* `uct_gen_preedge_saddle_of_M1`: sharp-hypothesis form of `uct:gen-preedge` (1) (needs only
  `StripM1 W`, not `(M2)` or `(M3)`), with explicit constant `C_L2(M, Λ) = 8 M + 54 Λ + 109`.
* `uct_gen_preedge_pos_of_M1`: positivity corollary (`0 < admissF c W Δ` when the RHS of
  `(uct:gen-lobe)` is `< 1`), matching `fct:ce-preedge` Step 1.
* `uct_gen_preedge_origin_of_holder`: sharp-hypothesis form of `uct:gen-preedge` (2) (needs only
  `c ≥ 2`, `StripM1 W`, and endpoint `α`-Hölder continuity at `ζ = 1` for any `α ∈ (0, 1)`).
* `uct_gen_preedge`: the full paper statement of Lemma `uct:gen-preedge` under `c ≥ 60` and
  `StripAdmissFullData (1 / 2) W`.

Class: proved, unconditional.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- **Existence and uniqueness of the saddle point `σ_+ = σ_+(ξ) ∈ (0, 1)`** (`uct:gen-preedge` (1),
`cel:L4` (1)): for `Δ = c ξ ∈ [Δ₁, (c/π²) exp(-π² U c^{-2/3})]` with `Δ₁, U, c > 0`, there is a
unique `σ_+ ∈ (0, 1)` with `stripGReal σ_+ = -log (π² ξ)`. -/
theorem existsUnique_saddlePoint {Δ₁ U c Δ ξ : ℝ}
    (hΔ₁ : 0 < Δ₁) (hU : 0 < U) (hc : 0 < c)
    (hΔ_lo : Δ₁ ≤ Δ) (hΔ_hi : Δ ≤ (c / π ^ 2) * Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))))
    (hξ : ξ = Δ / c) :
    ∃! σ_star : ℝ, σ_star ∈ Ioo (0 : ℝ) 1 ∧ stripGReal σ_star = -Real.log (π ^ 2 * ξ) := by
  have hΔ_pos : 0 < Δ := lt_of_lt_of_le hΔ₁ hΔ_lo
  have hξ_pos : 0 < ξ := by rw [hξ]; exact div_pos hΔ_pos hc
  have hπ2ξ_pos : 0 < π ^ 2 * ξ := by positivity
  have hπ2ξ_le : π ^ 2 * ξ ≤ Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))) := by
    rw [hξ]
    have h1 : π ^ 2 * (Δ / c) = (π ^ 2 / c) * Δ := by ring
    rw [h1]
    have h2 : (π ^ 2 / c) * ((c / π ^ 2) * Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ))))) =
        Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))) := by field_simp [hc.ne', Real.pi_ne_zero]
    exact (mul_le_mul_of_nonneg_left hΔ_hi (by positivity)).trans_eq h2
  have hlog_le : Real.log (π ^ 2 * ξ) ≤ -(π ^ 2 * U * c ^ (-(2 / 3 : ℝ))) :=
    (Real.log_le_log hπ2ξ_pos hπ2ξ_le).trans_eq (Real.log_exp _)
  have hpos_rhs : 0 < -Real.log (π ^ 2 * ξ) := by
    have : 0 < π ^ 2 * U * c ^ (-(2 / 3 : ℝ)) := by positivity
    linarith
  obtain ⟨σ, hσ_mem, hσ_eq⟩ := stripGReal_bijOn.2.2 hpos_rhs
  exact ⟨σ, ⟨hσ_mem, hσ_eq⟩, fun σ' ⟨hσ'_mem, hσ'_eq⟩ =>
    stripGReal_bijOn.2.1 hσ'_mem hσ_mem (hσ'_eq.trans hσ_eq.symm)⟩

/-- Real-symmetry of `StripM1 W` implies `W (σ : ℂ)` is real for `σ ∈ [0, 1]`. -/
lemma StripM1.im_ofReal_eq_zero {W : ℂ → ℂ} (hW : StripM1 W) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    (W (σ : ℂ)).im = 0 := by
  have h := hW.real (σ : ℂ) (by simpa using hσ0) (by simpa using hσ1)
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- Package a `StripM1` multiplier satisfying `(A0')`–`(A2')` of `uct:gen-preedge` (1) into
`TotalSaddleAmp c σ_star` with amplitude budget `A = (W (σ_star : ℂ)).re`. -/
noncomputable def StripM1.toTotalSaddleAmp {c σ_star M Λ Λ_add : ℝ} {W : ℂ → ℂ}
    (hW : StripM1 W) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1)
    (hM : 1 ≤ M) (hΛ : 1 ≤ Λ) (hΛ_add : 0 ≤ Λ_add)
    (hA0 : 0 < (W (σ_star : ℂ)).re)
    (hA1 : ∀ τ : ℝ, |τ| ≤ min σ_star (1 - σ_star) / 4 →
      ‖W ((σ_star : ℂ) + (τ : ℂ) * Complex.I) - W (σ_star : ℂ)‖ ≤
        4 * M * (|τ| / min σ_star (1 - σ_star)) * (W (σ_star : ℂ)).re)
    (hA2 : ∀ τ : ℝ, ‖W ((σ_star : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      Λ * (W (σ_star : ℂ)).re +
        if (1 - σ_star) / 2 < |τ| then Λ_add * min (c ^ (1 / 6 : ℝ) * |τ| ^ (1 / 2 : ℝ)) 1 else 0)
    (hΛ_add_half : 0 < Λ_add → 1 / 2 < σ_star) :
    TotalSaddleAmp c σ_star where
  V := W
  A := (W (σ_star : ℂ)).re
  M := M
  Λ := Λ
  Λ_add := Λ_add
  hA := hA0
  hM := hM
  hΛ := hΛ
  hΛ_add := hΛ_add
  hV_meas := by
    have hcont : Continuous fun τ : ℝ => W ((σ_star : ℂ) + (τ : ℂ) * Complex.I) :=
      hW.cont.comp_continuous (by fun_prop) fun τ => by
        simp [hσ0.le, hσ1.le]
    exact hcont.aestronglyMeasurable
  hV_symm τ := by
    have hconj : (σ_star : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I =
        starRingEnd ℂ ((σ_star : ℂ) + (τ : ℂ) * Complex.I) := by
      simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [hconj]
    exact hW.real ((σ_star : ℂ) + (τ : ℂ) * Complex.I) (by simp [hσ0.le]) (by simp [hσ1.le])
  hV0_le := by
    have him : (W (σ_star : ℂ)).im = 0 := hW.im_ofReal_eq_zero hσ0.le hσ1.le
    have hW_eq : W (σ_star : ℂ) = (((W (σ_star : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl (by simp [him])
    conv_lhs => rw [hW_eq]
    rw [Complex.norm_real, Real.norm_of_nonneg hA0.le]
  hV_var τ hτ := by
    refine (hA1 τ hτ).trans_eq ?_
    ring
  hV_vert := hA2
  hΛ_add_half := hΛ_add_half

/-- **Lemma `uct:gen-preedge` (1) (sharp-hypothesis form, `constant_terms_upper.tex`, `(uct:gen-lobe)`):**
generalised saddle-interval asymptotic for a single-strip multiplier satisfying `(M1)` (`StripM1 W`)
and `(A0')`–`(A2')`.

Scope: neither `(M2)` (endpoint Hölder continuity) nor `(M3)` (edge `C²` regularity) is used in
part (1), and `c ≥ 60` follows automatically from `c ≥ max (20 Δ₁) (60 U^{3/2})` and `U ≥ 1`.
The constant `C_L2(M, Λ)` is realised explicitly as `8 * M + 54 * Λ + 109` (from `lobe_total_saddle`). -/
theorem uct_gen_preedge_saddle_of_M1 {M Λ Λ_add Δ₁ U c Δ ξ σ_star : ℝ} {W : ℂ → ℂ}
    (hW : StripM1 W)
    (hM : 1 ≤ M) (hΛ : 1 ≤ Λ) (hΛ_add : 0 ≤ Λ_add)
    (hΔ₁ : 1 ≤ Δ₁) (hU : 1 ≤ U) (hc : max (20 * Δ₁) (60 * U ^ (3 / 2 : ℝ)) ≤ c)
    (h_eps0 : max ((27 / 100 : ℝ) * U ^ (-(3 / 4 : ℝ))) (Δ₁ ^ (-(1 / 2 : ℝ))) ≤
      min (3 / 1000 : ℝ) ((4 * M) ^ (-(4 / 3 : ℝ))))
    (hΔ_lo : Δ₁ ≤ Δ) (hΔ_hi : Δ ≤ (c / π ^ 2) * Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))))
    (hξ : ξ = Δ / c) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1)
    (hσ_eq : stripGReal σ_star = -Real.log (π ^ 2 * ξ))
    (hA0 : 0 < (W (σ_star : ℂ)).re)
    (hA1 : ∀ τ : ℝ, |τ| ≤ min σ_star (1 - σ_star) / 4 →
      ‖W ((σ_star : ℂ) + (τ : ℂ) * Complex.I) - W (σ_star : ℂ)‖ ≤
        4 * M * (|τ| / min σ_star (1 - σ_star)) * (W (σ_star : ℂ)).re)
    (hA2 : ∀ τ : ℝ, ‖W ((σ_star : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      Λ * (W (σ_star : ℂ)).re +
        if (1 - σ_star) / 2 < |τ| then Λ_add * min (c ^ (1 / 6 : ℝ) * |τ| ^ (1 / 2 : ℝ)) 1 else 0)
    (hΛ_add_half : 0 < Λ_add → 1 / 2 < σ_star) :
    let K₀ := (mellinK0 c (σ_star : ℂ) ξ).re
    let W₀ := (W (σ_star : ℂ)).re
    let L_lead := (1 / (2 * π * ξ)) * K₀ * W₀ * Real.sqrt (2 * π / (c * stripGDerivReal σ_star))
    let E_lobe := (admissF c W (c * ξ) * hankelRho0 c (c * ξ) - L_lead) / L_lead
    let z_pos := c * (1 - σ_star)
    let ς := c ^ (-(1 / 3 : ℝ))
    (mellinK0 c (σ_star : ℂ) ξ).im = 0 ∧ 0 < K₀ ∧ (W (σ_star : ℂ)).im = 0 ∧ 0 < L_lead ∧
      admissF c W (c * ξ) * hankelRho0 c (c * ξ) = L_lead * (1 + E_lobe) ∧
      |E_lobe| ≤ (8 * M + 54 * Λ + 109) * saddleEpsL c σ_star +
        150 * Λ_add * (ς / W₀) * Real.exp (-(3 / 320 : ℝ) * z_pos) := by
  dsimp only
  have hc60 : 60 ≤ c := by
    have hU32 : 1 ≤ U ^ (3 / 2 : ℝ) := Real.one_le_rpow hU (by norm_num : (0 : ℝ) ≤ 3 / 2)
    linarith [(le_max_right (20 * Δ₁) (60 * U ^ (3 / 2 : ℝ))).trans hc]
  have hc1 : (1 : ℝ) ≤ c := by linarith
  have hc_pos : 0 < c := by linarith
  have hξ_pos : 0 < ξ := by rw [hξ]; exact div_pos (by linarith) hc_pos
  have hg'_pos : 0 < stripGDerivReal σ_star := stripGDerivReal_pos hσ0 hσ1
  let amp := hW.toTotalSaddleAmp hσ0 hσ1 hM hΛ hΛ_add hA0 hA1 hA2 hΛ_add_half
  obtain ⟨hK₀_im, hK₀_pos, hI_im, hW_im, htot⟩ :=
    lobe_total_saddle hΔ₁ hU hc hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq amp h_eps0
  -- Identify `(g ρ₀)(c ξ)` with `(totalSaddleIntegral W c ξ σ_star).re` via `admiss_vert_rep`
  have hrep := admiss_vert_rep hc1 hW hσ0.le hσ1 hξ_pos
  have hcξ_pos : 0 < c * ξ := mul_pos hc_pos hξ_pos
  have hg_eq : admissF c W (c * ξ) * hankelRho0 c (c * ξ) =
      (totalSaddleIntegral W c ξ σ_star).re := by
    have hF : admissF c W (c * ξ) = admissLift c W (c * ξ) := by simp [admissF, hcξ_pos.ne']
    rw [hF, mul_comm]
    have hre := congrArg Complex.re hrep
    simpa [totalSaddleIntegral] using hre
  let K₀ := (mellinK0 c (σ_star : ℂ) ξ).re
  let W₀ := (W (σ_star : ℂ)).re
  let τ_sd := (c * stripGDerivReal σ_star) ^ (-(1 / 2 : ℝ))
  let L_lead := (1 / (2 * π * ξ)) * K₀ * W₀ * Real.sqrt (2 * π / (c * stripGDerivReal σ_star))
  have hτsd_pos : 0 < τ_sd := Real.rpow_pos_of_pos (mul_pos hc_pos hg'_pos) _
  have h_sqrt_eq : Real.sqrt (2 * π / (c * stripGDerivReal σ_star)) = Real.sqrt (2 * π) * τ_sd := by
    rw [Real.sqrt_div (by positivity)]
    dsimp [τ_sd]
    rw [rpow_neg_half_eq_inv_sqrt (by positivity), div_eq_mul_inv]
  have hL_pos : 0 < L_lead := by
    dsimp [L_lead]; rw [h_sqrt_eq]; positivity
  refine ⟨hK₀_im, hK₀_pos, hW_im, hL_pos, ?_, ?_⟩
  · have hL_ne : L_lead ≠ 0 := hL_pos.ne'
    field_simp [hL_ne]
    ring
  · have h_lhs_eq : (admissF c W (c * ξ) * hankelRho0 c (c * ξ) - L_lead) / L_lead =
        ((2 * π * ξ * (totalSaddleIntegral W c ξ σ_star).re) / (K₀ * Real.sqrt (2 * π) * τ_sd) - W₀) / W₀ := by
      rw [hg_eq]
      dsimp [L_lead]; rw [h_sqrt_eq]
      have h1 : 2 * π * ξ ≠ 0 := by positivity
      have h2 : K₀ ≠ 0 := hK₀_pos.ne'
      have h3 : W₀ ≠ 0 := hA0.ne'
      have h4 : Real.sqrt (2 * π) * τ_sd ≠ 0 := by positivity
      field_simp [h1, h2, h3, h4]
    rw [h_lhs_eq, abs_div, abs_of_pos hA0]
    have hdiv := div_le_div_of_nonneg_right htot hA0.le
    refine hdiv.trans_eq ?_
    dsimp [amp, StripM1.toTotalSaddleAmp, W₀]
    field_simp [hA0.ne']

/-- **Positivity corollary of `uct:gen-preedge` (1)** (used in `fct:ce-preedge` Step 1):
if the right-hand side of `(uct:gen-lobe)` is strictly less than `1`, then `admissF c W Δ > 0`. -/
theorem uct_gen_preedge_pos_of_M1 {M Λ Λ_add Δ₁ U c Δ ξ σ_star : ℝ} {W : ℂ → ℂ}
    (hW : StripM1 W)
    (hM : 1 ≤ M) (hΛ : 1 ≤ Λ) (hΛ_add : 0 ≤ Λ_add)
    (hΔ₁ : 1 ≤ Δ₁) (hU : 1 ≤ U) (hc : max (20 * Δ₁) (60 * U ^ (3 / 2 : ℝ)) ≤ c)
    (h_eps0 : max ((27 / 100 : ℝ) * U ^ (-(3 / 4 : ℝ))) (Δ₁ ^ (-(1 / 2 : ℝ))) ≤
      min (3 / 1000 : ℝ) ((4 * M) ^ (-(4 / 3 : ℝ))))
    (hΔ_lo : Δ₁ ≤ Δ) (hΔ_hi : Δ ≤ (c / π ^ 2) * Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))))
    (hξ : ξ = Δ / c) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1)
    (hσ_eq : stripGReal σ_star = -Real.log (π ^ 2 * ξ))
    (hA0 : 0 < (W (σ_star : ℂ)).re)
    (hA1 : ∀ τ : ℝ, |τ| ≤ min σ_star (1 - σ_star) / 4 →
      ‖W ((σ_star : ℂ) + (τ : ℂ) * Complex.I) - W (σ_star : ℂ)‖ ≤
        4 * M * (|τ| / min σ_star (1 - σ_star)) * (W (σ_star : ℂ)).re)
    (hA2 : ∀ τ : ℝ, ‖W ((σ_star : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      Λ * (W (σ_star : ℂ)).re +
        if (1 - σ_star) / 2 < |τ| then Λ_add * min (c ^ (1 / 6 : ℝ) * |τ| ^ (1 / 2 : ℝ)) 1 else 0)
    (hΛ_add_half : 0 < Λ_add → 1 / 2 < σ_star)
    (h_err_lt_one : (8 * M + 54 * Λ + 109) * saddleEpsL c σ_star +
      150 * Λ_add * (c ^ (-(1 / 3 : ℝ)) / (W (σ_star : ℂ)).re) *
        Real.exp (-(3 / 320 : ℝ) * (c * (1 - σ_star))) < 1) :
    0 < admissF c W Δ := by
  have hc_pos : 0 < c := by linarith [(le_max_left (20 * Δ₁) (60 * U ^ (3 / 2 : ℝ))).trans hc]
  have hΔ_pos : 0 < Δ := by linarith
  obtain ⟨_, _, _, hL_pos, hprod, herr⟩ :=
    uct_gen_preedge_saddle_of_M1 hW hM hΛ hΛ_add hΔ₁ hU hc h_eps0 hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq
      hA0 hA1 hA2 hΛ_add_half
  have hcξ_eq : c * ξ = Δ := by rw [hξ]; field_simp [hc_pos.ne']
  rw [hcξ_eq] at hprod herr
  have h1E : 0 < 1 + (admissF c W Δ * hankelRho0 c Δ -
      (1 / (2 * π * ξ)) * (mellinK0 c (σ_star : ℂ) ξ).re * (W (σ_star : ℂ)).re *
        Real.sqrt (2 * π / (c * stripGDerivReal σ_star))) /
      ((1 / (2 * π * ξ)) * (mellinK0 c (σ_star : ℂ) ξ).re * (W (σ_star : ℂ)).re *
        Real.sqrt (2 * π / (c * stripGDerivReal σ_star))) := by
    have hlt := lt_of_le_of_lt herr h_err_lt_one
    linarith [(abs_lt.mp hlt).1]
  have hprod_pos : 0 < admissF c W Δ * hankelRho0 c Δ := by
    rw [hprod]; exact mul_pos hL_pos h1E
  have hρ_pos : 0 < hankelRho0 c Δ := by
    unfold hankelRho0
    have hG : 0 < Real.Gamma c := Real.Gamma_pos_of_pos hc_pos
    positivity
  exact pos_of_mul_pos_left hprod_pos hρ_pos.le

/-- **Lemma `uct:gen-preedge` (2) (sharp-hypothesis form, `constant_terms_upper.tex`, `(uct:gen-origin)`):**
origin Mellin shift for a single-strip multiplier `W̃` satisfying `(M1)` (`StripM1 W`) and
endpoint `α`-Hölder continuity at `ζ = 1` for any `α > 0` and `c ≥ 2`.

Scope: neither `(M2)` at `ζ = 0` nor `(M3)` (on either edge) is needed, `c ≥ 2` suffices (instead
of `c ≥ 60`), and any Hölder exponent `α > 0` (in fact any Dini modulus, see
`ceOrigin_shift_dini`) works. Also includes conjugation symmetry `G_c(-iy) = conj G_c(iy)` and the
uniform bound `sup_{Δ ≥ 0} |g(Δ) - g(0) e^{-4Δ}| ≤ π⁻¹ ∫₀^∞ |G_c(iy)| dy`. -/
theorem uct_gen_preedge_origin_of_holder {c α : ℝ} {W : ℂ → ℂ}
    (hc : 2 ≤ c) (hα0 : 0 < α) (hW : StripM1 W)
    (hH : ∃ CH : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖1 - ζ‖ ≤ 1 / 2 → ‖W ζ - W 1‖ ≤ CH * ‖1 - ζ‖ ^ α) :
    Integrable (ceOriginG c W) ∧
      (∀ y : ℝ, ceOriginG c W (-y) = starRingEnd ℂ (ceOriginG c W y)) ∧
      (∀ {Δ : ℝ}, 0 < Δ →
        ((admissF c W Δ - admissF c W 0 * Real.exp (-(4 * Δ)) : ℝ) : ℂ) =
          ((1 / (2 * π) : ℝ) : ℂ) * ∫ y : ℝ, ceOriginG c W y * (Δ : ℂ) ^ (-((y : ℂ) * Complex.I))) ∧
      (∀ {Δ : ℝ}, 0 ≤ Δ →
        |admissF c W Δ - admissF c W 0 * Real.exp (-(4 * Δ))| ≤
          (1 / π) * ∫ y in Ioi (0 : ℝ), ‖ceOriginG c W y‖) := by
  obtain ⟨CH, hCH⟩ := hH
  obtain ⟨hint, hconj, hshift, hsup⟩ := ceOrigin_shift_dini hc hW
    (IsDiniModulus.holder hα0 (by norm_num : (0 : ℝ) < 1 / 2) CH)
    (fun ζ h0 h1 hn => (hCH ζ h0 h1 hn).trans (mul_le_mul_of_nonneg_right (le_abs_self CH) (by positivity)))
  have hW1_im : (W 1).im = 0 := W_one_im hW
  have hW1_eq : W 1 = (((W 1).re : ℝ) : ℂ) := Complex.ext rfl (by simp [hW1_im])
  refine ⟨hint, hconj, ?_, ?_⟩
  · intro Δ hΔ
    have hFΔ : admissF c W Δ = admissLift c W Δ := by simp [admissF, hΔ.ne']
    have hF0 : admissF c W 0 = (W 1).re := by simp [admissF]
    rw [hFΔ, hF0]
    have h := hshift hΔ
    rw [hW1_eq] at h
    simpa [Complex.ofReal_sub, Complex.ofReal_mul] using h
  · intro Δ hΔ
    rcases hΔ.eq_or_lt with rfl | hpos
    · simp only [mul_zero, neg_zero, Real.exp_zero, mul_one, sub_self, abs_zero]
      exact mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun _ _ => norm_nonneg _)
    · have hFΔ : admissF c W Δ = admissLift c W Δ := by simp [admissF, hpos.ne']
      have hF0 : admissF c W 0 = (W 1).re := by simp [admissF]
      rw [hFΔ, hF0]
      exact hsup hpos

/-- **Lemma `uct:gen-preedge` (`CFT/sign_uncertainty/paper/constant_terms_upper.tex`):**
generalised saddle-interval asymptotic and origin shift for an admissible single-strip multiplier.

Fix `c ≥ 60` and `W̃` satisfying `uct:admiss` with `α = 1/2` (`StripAdmissFullData (1 / 2) W`).
With `g = admissF c W`:
* `g ∈ C[0, ∞) ∩ L¹((0, ∞), ρ₀ dΔ)` with `g(0) = W̃(1)` (real);
* **(1) (Saddle-interval asymptotic, `(uct:gen-lobe)`):** for any `M, Λ ≥ 1`, `Λ_add ≥ 0`,
  `Δ₁, U ≥ 1` with `max(0.27 U^{-3/4}, Δ₁^{-1/2}) ≤ min(3e-3, (4M)^{-4/3})` and
  `c ≥ max(20 Δ₁, 60 U^{3/2})`, any `Δ = c ξ ∈ [Δ₁, (c/π²) exp(-π² U c^{-2/3})]` with saddle point
  `σ_+ ∈ (0, 1)` (`stripGReal σ_+ = -log(π² ξ)`), under `(A0')`–`(A2')`,
  `(g ρ₀)(c ξ) = (2πξ)⁻¹ K₀(σ_+, ξ) W₀ √(2π / (c g_tan'(σ_+))) (1 + E_lobe)` with
  `|E_lobe| ≤ (8 M + 54 Λ + 109) ε_L(ξ, c) + 150 Λ_add (c^{-1/3} / W₀) exp(-3 c (1 - σ_+) / 320)`;
* **(2) (Origin Mellin shift, `(uct:gen-origin)`):** `G_c(iy) = 4^{-iy} Γ(iy)[E_c(iy) W̃(1 - iy/c) - W̃(1)]`
  is integrable on `ℝ`, satisfies `G_c(-iy) = conj G_c(iy)`, and for every `Δ > 0`,
  `g(Δ) - g(0) e^{-4Δ} = (2π)⁻¹ ∫ G_c(iy) Δ^{-iy} dy`, with
  `|g(Δ) - g(0) e^{-4Δ}| ≤ π⁻¹ ∫₀^∞ |G_c(iy)| dy` for all `Δ ≥ 0`.

Scope: matches `uct:gen-preedge` verbatim (with explicit `C_L2(M, Λ) = 8 M + 54 Λ + 109` and the
extra conjugation symmetry and `sup_{Δ ≥ 0}` bound in (2)). For weaker hypotheses, see
`uct_gen_preedge_saddle_of_M1` and `uct_gen_preedge_origin_of_holder`. -/
theorem uct_gen_preedge {c : ℝ} {W : ℂ → ℂ} (hc60 : 60 ≤ c) (hW : StripAdmissFullData (1 / 2) W) :
    -- Preamble (`uct:admiss` consequences)
    (ContinuousOn (admissF c W) (Ici 0) ∧
      IntegrableOn (fun Δ : ℝ => admissF c W Δ * hankelRho0 c Δ) (Ioi 0) ∧
      admissF c W 0 = (W 1).re ∧ (W 1).im = 0) ∧
    -- (1) Saddle-interval asymptotic `(uct:gen-lobe)`
    (∀ {M Λ Λ_add Δ₁ U Δ ξ σ_star : ℝ},
      1 ≤ M → 1 ≤ Λ → 0 ≤ Λ_add →
      1 ≤ Δ₁ → 1 ≤ U → max (20 * Δ₁) (60 * U ^ (3 / 2 : ℝ)) ≤ c →
      max ((27 / 100 : ℝ) * U ^ (-(3 / 4 : ℝ))) (Δ₁ ^ (-(1 / 2 : ℝ))) ≤
        min (3 / 1000 : ℝ) ((4 * M) ^ (-(4 / 3 : ℝ))) →
      Δ₁ ≤ Δ → Δ ≤ (c / π ^ 2) * Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))) →
      ξ = Δ / c → 0 < σ_star → σ_star < 1 → stripGReal σ_star = -Real.log (π ^ 2 * ξ) →
      0 < (W (σ_star : ℂ)).re →
      (∀ τ : ℝ, |τ| ≤ min σ_star (1 - σ_star) / 4 →
        ‖W ((σ_star : ℂ) + (τ : ℂ) * Complex.I) - W (σ_star : ℂ)‖ ≤
          4 * M * (|τ| / min σ_star (1 - σ_star)) * (W (σ_star : ℂ)).re) →
      (∀ τ : ℝ, ‖W ((σ_star : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
        Λ * (W (σ_star : ℂ)).re +
          if (1 - σ_star) / 2 < |τ| then Λ_add * min (c ^ (1 / 6 : ℝ) * |τ| ^ (1 / 2 : ℝ)) 1 else 0) →
      (0 < Λ_add → 1 / 2 < σ_star) →
      let K₀ := (mellinK0 c (σ_star : ℂ) ξ).re
      let W₀ := (W (σ_star : ℂ)).re
      let L_lead := (1 / (2 * π * ξ)) * K₀ * W₀ * Real.sqrt (2 * π / (c * stripGDerivReal σ_star))
      let E_lobe := (admissF c W (c * ξ) * hankelRho0 c (c * ξ) - L_lead) / L_lead
      let z_pos := c * (1 - σ_star)
      let ς := c ^ (-(1 / 3 : ℝ))
      (mellinK0 c (σ_star : ℂ) ξ).im = 0 ∧ 0 < K₀ ∧ (W (σ_star : ℂ)).im = 0 ∧ 0 < L_lead ∧
        admissF c W (c * ξ) * hankelRho0 c (c * ξ) = L_lead * (1 + E_lobe) ∧
        |E_lobe| ≤ (8 * M + 54 * Λ + 109) * saddleEpsL c σ_star +
          150 * Λ_add * (ς / W₀) * Real.exp (-(3 / 320 : ℝ) * z_pos)) ∧
    -- (2) Origin Mellin shift `(uct:gen-origin)`
    (Integrable (ceOriginG c W) ∧
      (∀ y : ℝ, ceOriginG c W (-y) = starRingEnd ℂ (ceOriginG c W y)) ∧
      (∀ {Δ : ℝ}, 0 < Δ →
        ((admissF c W Δ - admissF c W 0 * Real.exp (-(4 * Δ)) : ℝ) : ℂ) =
          ((1 / (2 * π) : ℝ) : ℂ) * ∫ y : ℝ, ceOriginG c W y * (Δ : ℂ) ^ (-((y : ℂ) * Complex.I))) ∧
      (∀ {Δ : ℝ}, 0 ≤ Δ →
        |admissF c W Δ - admissF c W 0 * Real.exp (-(4 * Δ))| ≤
          (1 / π) * ∫ y in Ioi (0 : ℝ), ‖ceOriginG c W y‖)) := by
  have hc2 : (2 : ℝ) ≤ c := by linarith
  have hα0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hα1 : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨⟨_, _, hcont, h0, hW1im⟩, ⟨_, _, hint, _⟩, _⟩ := uct_admiss_full hc2 hα0 hα1 hW
  refine ⟨⟨hcont, hint, h0, hW1im⟩, ?_,
    uct_gen_preedge_origin_of_holder hc2 hα0 hW.toStripM1 hW.holder1⟩
  intro M Λ Λ_add Δ₁ U Δ ξ σ_star hM hΛ hΛ_add hΔ₁ hU hc h_eps0 hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq
    hA0 hA1 hA2 hΛ_add_half
  exact uct_gen_preedge_saddle_of_M1 hW.toStripM1 hM hΛ hΛ_add hΔ₁ hU hc h_eps0 hΔ_lo hΔ_hi hξ
    hσ0 hσ1 hσ_eq hA0 hA1 hA2 hΛ_add_half

/-- info: 'FormalResearch.SignUncertainty.existsUnique_saddlePoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms existsUnique_saddlePoint

/-- info: 'FormalResearch.SignUncertainty.uct_gen_preedge_saddle_of_M1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_gen_preedge_saddle_of_M1

/-- info: 'FormalResearch.SignUncertainty.uct_gen_preedge_pos_of_M1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_gen_preedge_pos_of_M1

/-- info: 'FormalResearch.SignUncertainty.uct_gen_preedge_origin_of_holder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_gen_preedge_origin_of_holder

/-- info: 'FormalResearch.SignUncertainty.uct_gen_preedge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_gen_preedge

end FormalResearch.SignUncertainty
