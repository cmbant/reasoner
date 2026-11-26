module

public import Mathlib
public import FormalResearch.SignUncertainty.CtDyadicChartReal
public import FormalResearch.SignUncertainty.HankelLangerComparability
public import FormalResearch.SignUncertainty.HankelEdgePhase

/-!
# The Langer chart equals the CFU edge chart (`ct:cfu` (1), `gt:7.7b`, `u1cl:langer`)

The Lean Langer chart is `y(w) = (π²/12) M(K^{-1}(v))`, `v = -(12/π²) log(1+w)` (`chartY etaC`).  On the band
`w = e^L - 1`, `0 < L`, `e^L - 1 ≤ 5·10⁻⁴`, the point `u₀ = -τ₀(L)²` is a preimage `K(u₀) = v` (`g(iτ₀) = -m(τ₀) = -L`,
`gSer_imag`), hence `K^{-1}(v) = u₀`, and `M(u₀) = u₀ E(u₀)^{2/3}`.  The Hankel series identity
`S̃(ζ) - ζ g(ζ) = -(π²/18) ζ³ E(ζ²)` (`SSer_sub_mul_gSer`) at `ζ = iτ₀` is `Φ(τ₀; L) = (π²/18) τ₀³ E(-τ₀²)`, where
`Φ = edgePhi`; with `μ³ = π²/24` this is `Φ = (4/3)(κ g)^{3/2}`.

* `SSer_imag`: `S̃(iτ) = -i ∫₀^τ m` (`0 < τ ≤ 0.035`).
* `edgePhi_crit_eq_chartE`: `Φ(τ; m(τ)) = (π²/18) τ³ E(-τ²)`, `E` real.
* `chartKinv_band`: `K^{-1}(v(e^L - 1)) = -τ₀(L)²`.
* `ct_langer_edge` (`CtLangerEdge`): `edgePhi L (tau0 L) = (4/3)(κ g(L))^{3/2}`; **proved**, unconditional.
-/

@[expose] public section

open Complex Set Metric
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- `hankelEdgeM = langerMband`. -/
lemma hankelEdgeM_eq_langerMband (τ : ℝ) : hankelEdgeM τ = langerMband τ := rfl

/-- `Φ(τ; L) = Lτ - ∫₀^τ m`. -/
lemma edgePhi_eq_sub (τ L : ℝ) : edgePhi L τ = L * τ - ∫ u in (0 : ℝ)..τ, hankelEdgeM u := by
  unfold edgePhi
  have : ∀ u : ℝ, Real.log (Real.tanh (π * u / 2) / (π * u / 2)) = -hankelEdgeM u := by
    intro u
    unfold hankelEdgeM ceEll
    rw [← Real.log_inv, inv_div]
  simp only [this, intervalIntegral.integral_neg]
  ring

/-- **`S̃(iτ) = -i ∫₀^τ m`** (`0 < τ ≤ 0.035`; the series `SSer etaC` on the imaginary axis). -/
lemma SSer_imag {τ : ℝ} (hτ : 0 < τ) (hτn : τ ≤ 0.035) :
    SSer etaC ((τ : ℂ) * Complex.I) = -Complex.I * (((∫ u in (0 : ℝ)..τ, hankelEdgeM u : ℝ)) : ℂ) := by
  have hnorm : ∀ σ ∈ Set.uIcc (0 : ℝ) τ, ‖(σ : ℂ) * Complex.I‖ < 1 := by
    intro σ hσ
    rw [Set.uIcc_of_le hτ.le] at hσ
    rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_nonneg hσ.1]
    linarith [hσ.2]
  have hd : ∀ σ ∈ Set.uIcc (0 : ℝ) τ, HasDerivAt (fun σ : ℝ => SSer etaC ((σ : ℂ) * Complex.I))
      (gSer etaC ((σ : ℂ) * Complex.I) * Complex.I) σ := by
    intro σ hσ
    have hS := hasDerivAt_SSer langerEta_etaC (hnorm σ hσ)
    have hp : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) Complex.I σ := by
      simpa using ((hasDerivAt_id σ).ofReal_comp).mul_const Complex.I
    have := hS.scomp σ hp
    have e : (fun σ : ℝ => SSer etaC ((σ : ℂ) * Complex.I)) = SSer etaC ∘ fun s : ℝ => (s : ℂ) * Complex.I := rfl
    rw [e]
    convert this using 1
    simp [smul_eq_mul, mul_comm]
  have hcont : ContinuousOn (fun σ : ℝ => gSer etaC ((σ : ℂ) * Complex.I) * Complex.I) (Set.uIcc 0 τ) := by
    refine ContinuousOn.mul ?_ continuousOn_const
    exact differentiableOn_gSer.continuousOn.comp
      (by fun_prop : Continuous fun s : ℝ => (s : ℂ) * Complex.I).continuousOn
      (fun σ hσ => mem_ball_zero_iff.2 (hnorm σ hσ))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable
  simp only [Complex.ofReal_zero, zero_mul, SSer_zero, sub_zero] at hftc
  rw [← hftc]
  have hcongr : ∫ σ in (0 : ℝ)..τ, gSer etaC ((σ : ℂ) * Complex.I) * Complex.I =
      ∫ σ in (0 : ℝ)..τ, ((-(hankelEdgeM σ) : ℝ) : ℂ) * Complex.I := by
    refine intervalIntegral.integral_congr (fun σ hσ => ?_)
    rw [Set.uIcc_of_le hτ.le] at hσ
    show _ = _
    rcases hσ.1.eq_or_lt with h0 | hpos
    · rw [← h0]; simp [gSer_zero, hankelEdgeM_zero]
    · rw [gSer_imag hpos (hσ.2.trans hτn), hankelEdgeM_eq_langerMband]; push_cast; ring
  rw [hcongr, intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_neg]
  push_cast; ring

/-- **The critical value in the series**: for `0 < τ ≤ 0.035`, `Φ(τ; m(τ)) = (π²/18) τ³ E(-τ²)` (`E = chartE etaC`, real there). -/
lemma edgePhi_crit_eq_chartE {τ : ℝ} (hτ : 0 < τ) (hτn : τ ≤ 0.035) :
    ((edgePhi (hankelEdgeM τ) τ : ℝ) : ℂ) = ((π ^ 2 / 18 : ℝ) : ℂ) * (τ : ℂ) ^ 3 * chartE etaC (((τ : ℂ) * Complex.I) ^ 2) := by
  set ζ : ℂ := (τ : ℂ) * Complex.I with hζ
  have hn : ‖ζ‖ < 1 := by
    rw [hζ, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos hτ]; linarith
  have h := SSer_sub_mul_gSer langerEta_etaC hn
  rw [hζ, SSer_imag hτ hτn, gSer_imag hτ hτn, ← hankelEdgeM_eq_langerMband, ← hζ] at h
  have hΦ : ((edgePhi (hankelEdgeM τ) τ : ℝ) : ℂ) =
      (((hankelEdgeM τ * τ - ∫ u in (0 : ℝ)..τ, hankelEdgeM u : ℝ)) : ℂ) := by
    rw [edgePhi_eq_sub]
  have hζ3 : ζ ^ 3 = -Complex.I * (τ : ℂ) ^ 3 := by
    rw [hζ, mul_pow, Complex.I_pow_three]; ring
  rw [hζ3] at h
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  apply mul_left_cancel₀ hI
  rw [hΦ]
  push_cast at h ⊢
  linear_combination h

/-- `E(-τ²)` is real positive on the band: `chartE etaC (ζ²) = e` with `e = (18/π²) Φ/τ³`. -/
lemma chartE_band_real {τ : ℝ} (hτ : 0 < τ) (hτn : τ ≤ 0.035) :
    ∃ e : ℝ, 0 < e ∧ chartE etaC (((τ : ℂ) * Complex.I) ^ 2) = (e : ℂ) ∧
      edgePhi (hankelEdgeM τ) τ = π ^ 2 / 18 * τ ^ 3 * e := by
  have h := edgePhi_crit_eq_chartE hτ hτn
  have hτ0 : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hτ3 : (τ : ℂ) ^ 3 ≠ 0 := pow_ne_zero 3 hτ0
  have hp : ((π ^ 2 / 18 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < π ^ 2 / 18 := by positivity
    exact_mod_cast this.ne'
  set e : ℝ := 18 / π ^ 2 * edgePhi (hankelEdgeM τ) τ / τ ^ 3 with he
  have hE : chartE etaC (((τ : ℂ) * Complex.I) ^ 2) = (e : ℂ) := by
    have : chartE etaC (((τ : ℂ) * Complex.I) ^ 2) =
        ((edgePhi (hankelEdgeM τ) τ : ℝ) : ℂ) / (((π ^ 2 / 18 : ℝ) : ℂ) * (τ : ℂ) ^ 3) := by
      rw [h]; generalize chartE etaC (((τ : ℂ) * Complex.I) ^ 2) = X; field_simp
    rw [this, he]; push_cast; field_simp
  have hnorm : ‖((τ : ℂ) * Complex.I) ^ 2‖ < 1 := by
    rw [norm_pow, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos hτ]
    nlinarith
  have hb := norm_chartE_sub_one_le langerEta_etaC hnorm
  have hnr : ‖((τ : ℂ) * Complex.I) ^ 2‖ = τ ^ 2 := by
    rw [norm_pow, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos hτ]
  rw [hE, hnr] at hb
  have hpi : (9.8 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_d2]
  have hsmall : 36 / (5 * π ^ 2) * τ ^ 2 / (1 - τ ^ 2) < 1 := by
    have h1 : τ ^ 2 ≤ 0.035 ^ 2 := pow_le_pow_left₀ hτ.le hτn 2
    rw [div_lt_one (by nlinarith)]
    have : 36 / (5 * π ^ 2) ≤ 36 / (5 * 9.8) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    nlinarith [sq_nonneg τ]
  have hepos : 0 < e := by
    have : ‖(e : ℂ) - 1‖ < 1 := lt_of_le_of_lt hb hsmall
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at this
    have := (abs_lt.1 this).1
    linarith
  refine ⟨e, hepos, hE, ?_⟩
  rw [he]; field_simp

/-- The saddle on the chart disc: `0 < τ₀(L) ≤ 0.03` and `m(τ₀(L)) = L`. -/
lemma tau0_band {L : ℝ} (hL : 0 < L) (hL5 : Real.exp L - 1 ≤ 5e-4) :
    0 < tau0 L ∧ tau0 L ≤ 0.03 ∧ hankelEdgeM (tau0 L) = L := by
  have hLle : L ≤ 5e-4 := by linarith [Real.add_one_le_exp L]
  obtain ⟨-, hb, -⟩ := tau0_bounds hL (by linarith)
  refine ⟨tau0_pos hL, ?_, ceEll_tau0 hL⟩
  have hs : Real.sqrt L ≤ 0.0224 := by
    rw [Real.sqrt_le_iff]; refine ⟨by norm_num, ?_⟩; norm_num; linarith
  nlinarith [Real.sqrt_nonneg L]

/-- **`K^{-1}` on the band**: for `0 < L`, `e^L - 1 ≤ 5·10⁻⁴`, `chartKinv etaC (chartVofW (e^L - 1)) = (iτ₀(L))² = -τ₀(L)²`. -/
lemma chartKinv_band {L : ℝ} (hL : 0 < L) (hL5 : Real.exp L - 1 ≤ 5e-4) :
    chartKinv etaC (chartVofW (((Real.exp L - 1 : ℝ)) : ℂ)) = (((tau0 L : ℝ) : ℂ) * Complex.I) ^ 2 := by
  obtain ⟨hτ, hτ3, hm⟩ := tau0_band hL hL5
  set τ := tau0 L with hτdef
  have hw0 : 0 ≤ Real.exp L - 1 := by linarith [Real.one_le_exp hL.le]
  have hwn : ‖(((Real.exp L - 1 : ℝ)) : ℂ)‖ ≤ 1e-3 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]; linarith
  have hv := chartVofW_mem hwn
  have hlog : Complex.log (1 + (((Real.exp L - 1 : ℝ)) : ℂ)) = (L : ℂ) := by
    rw [show (1 : ℂ) + (((Real.exp L - 1 : ℝ)) : ℂ) = ((Real.exp L : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (Real.exp_pos L).le, Real.log_exp]
  have hu : (((τ : ℂ) * Complex.I) ^ 2) ∈ ball (0 : ℂ) (0.035 ^ 2) := by
    rw [mem_ball_zero_iff, norm_pow, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos hτ]
    nlinarith
  refine (chartKinv_eq_of (h := langerEta_etaC) hv hu ?_).symm.symm
  have h1 := gSer_eq_chartK etaC ((τ : ℂ) * Complex.I)
  rw [gSer_imag hτ (by linarith), ← hankelEdgeM_eq_langerMband, hm] at h1
  unfold chartVofW
  rw [hlog]
  have hp : ((π ^ 2 / 12 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < π ^ 2 / 12 := by positivity
    exact_mod_cast this.ne'
  apply mul_left_cancel₀ hp
  rw [← h1]
  push_cast
  field_simp

/-- **The Langer chart in the band**: for `0 < L`, `e^L - 1 ≤ 5·10⁻⁴`, with `τ₀ = τ₀(L)` and `E(-τ₀²) = e > 0`
(`chartE_band_real`), `g(L) = ctChartG L = (π²/12) τ₀² e^{2/3}` (`y = (π²/12) M(K^{-1}(v))`, `M(u) = u E(u)^{2/3}`). -/
lemma ctChartG_band {L : ℝ} (hL : 0 < L) (hL5 : Real.exp L - 1 ≤ 5e-4) :
    ∃ e : ℝ, 0 < e ∧ edgePhi L (tau0 L) = π ^ 2 / 18 * tau0 L ^ 3 * e ∧
      ctChartG L = π ^ 2 / 12 * tau0 L ^ 2 * e ^ (2 / 3 : ℝ) := by
  obtain ⟨hτ, hτ3, hm⟩ := tau0_band hL hL5
  set τ := tau0 L with hτdef
  obtain ⟨e, he, hE, hΦ⟩ := chartE_band_real hτ (by linarith)
  refine ⟨e, he, by rw [← hm]; exact hΦ, ?_⟩
  have hY : chartY etaC (((Real.exp L - 1 : ℝ)) : ℂ) =
      ((π ^ 2 / 12 : ℝ) : ℂ) * ((-(τ ^ 2) : ℝ) * (e ^ (2 / 3 : ℝ) : ℝ) : ℂ) := by
    unfold chartY chartXi
    rw [chartKinv_band hL hL5]
    unfold chartM powMapU
    have hE' : psW (aE etaC) (((τ : ℂ) * Complex.I) ^ 2) = (e : ℂ) := hE
    rw [hE', ← Complex.ofReal_cpow he.le]
    congr 2
    push_cast
    rw [mul_pow, Complex.I_sq]; ring
  unfold ctChartG ctYR
  rw [hY]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_zero]
  ring

/-- **`CtLangerEdge`** (`ct:cfu` (1), `gt:7.7b`; the paper's definition of the Langer chart by `cΦ_Ph(τ₀(ξ); ξ) = (4/3)(-ũ)^{3/2}`):
for `0 < L`, `e^L - 1 ≤ 5·10⁻⁴`, `Φ(τ₀(L); L) = (4/3)(κ g(L))^{3/2}`, where `Φ = edgePhi`, `τ₀ = CohnElkies.tau0`
(`m(τ₀(L)) = L`), `g = ctChartG` the series Langer chart (`-y(e^L - 1)`), `κ = 12μ²/π²`.  **Proved**, unconditional.  Proof:
`K(-τ₀²) = v` so `K^{-1}(v) = -τ₀²` (`chartKinv_band`), `g = (π²/12) τ₀² E^{2/3}`, `Φ = (π²/18) τ₀³ E`
(`edgePhi_crit_eq_chartE`, from `S̃ - ζ g = -(π²/18) ζ³ E`), and `μ³ = π²/24`. -/
theorem ct_langer_edge {L : ℝ} (hL : 0 < L) (hL5 : Real.exp L - 1 ≤ 5e-4) :
    edgePhi L (tau0 L) = 4 / 3 * (langerKappa * ctChartG L) ^ (3 / 2 : ℝ) := by
  obtain ⟨hτ, -, -⟩ := tau0_band hL hL5
  obtain ⟨e, he, hΦ, hg⟩ := ctChartG_band hL hL5
  set τ := tau0 L with hτdef
  set a : ℝ := e ^ (1 / 3 : ℝ) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos he _
  have ha3 : a ^ 3 = e := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul he.le]; norm_num
  have ha2 : e ^ (2 / 3 : ℝ) = a ^ 2 := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul he.le]; norm_num
  have hμ := langerMu_pos
  set x : ℝ := langerMu * τ * a with hx
  have hx0 : 0 < x := by positivity
  have hκg : langerKappa * ctChartG L = x ^ 2 := by
    rw [hg, ha2]; unfold langerKappa
    have : π ^ 2 ≠ 0 := by positivity
    rw [hx]; field_simp
  rw [hκg, ← Real.rpow_natCast x 2, ← Real.rpow_mul hx0.le]
  norm_num
  rw [hΦ, hx, mul_pow, mul_pow, langerMu_cube, ha3]
  ring

/-- info: 'FormalResearch.SignUncertainty.ct_langer_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_langer_edge

end FormalResearch.SignUncertainty
