module

public import FormalResearch.SignUncertainty.RadialKernelLimit
public import FormalResearch.SignUncertainty.RadialRigidity
public import FormalResearch.CohnElkies.LobeSaddleCore
public import FormalResearch.CohnElkies.MellinKernel
public import FormalResearch.CohnElkies.AiryTwistedLaplace

/-!
# The Laplace weight `W_c(y, Δ) = 1 / K₀(ζ_c, Δ/c)` (proof of Thm H.14, eq:ce-laplace-limit)

Statements 1-5 of the Laplace-weight brief. Results are classed as follows (all proved; the
non-elementary inputs `mellin_strip_kernel_eq`, `mellinK0_saddle_pos` and `radialK_tendsto` are used
as existing declarations, not restated).

* `laplaceCs_pos`, `laplaceCs_cube`, `laplaceCs_mul_hankelBeta1`, `laplaceCs_div_hankelBeta1`: proved
  (elementary algebra); `laplaceCs_eq_ceCs` records that `c_s` is the existing `ceCs`.
* `mellinK0_laplace_real`, `laplaceWeight_pos`: proved (from `mellinK0_saddle_pos` and the `ζ = 0` case).
* `laplaceWeight_gamma_form`, `laplaceWeight_scale`: proved (from `mellin_strip_kernel_eq`).
* `laplaceWeight_tendsto`, `laplaceWeight_tendsto_const`: proved (from `radialK_tendsto`; the limit is
  `exp(-y³/12 + y u)`).

Normalisation. `laplaceWeight` is the full reciprocal `1/K₀`, so it contains the prefactor
`e^{-c ℋ(ζ_c)} → e^{-y³/12}` of `eq:ce-laplace-limit` as well as the Gamma/power factor that tends to
`e^{y u}` on fixed windows. Hence the limit is `exp(-y³/12 + y u)`, not `exp(y u)`: the factor
`e^{-y³/12}` is the one in `airyLaplace` (`ShellLaplaceBase.lean`). At `y = 0` the weight is
identically `1`.
-/

@[expose] public section

open Complex Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- `c_s = (π²/3)^{1/3}`. -/
noncomputable def laplaceCs : ℝ := (Real.pi ^ 2 / 3) ^ (1 / 3 : ℝ)

lemma laplaceCs_eq_ceCs : laplaceCs = ceCs := rfl

/-- `ζ_c(y) = (y / c_s) c^{-1/3} = (y/c_s) * radialEps c`. -/
noncomputable def laplaceZeta (c y : ℝ) : ℝ := (y / laplaceCs) * radialEps c

/-- The Laplace weight, `Δ > 0`, `ξ = Δ / c`. -/
noncomputable def laplaceWeight (c y Δ : ℝ) : ℝ :=
  ((mellinK0 c (laplaceZeta c y : ℂ) (Δ / c))⁻¹).re

lemma laplaceCs_pos : 0 < laplaceCs := by
  unfold laplaceCs
  have : 0 < Real.pi ^ 2 / 3 := by positivity
  exact Real.rpow_pos_of_pos this _

lemma laplaceCs_cube : laplaceCs ^ 3 = Real.pi ^ 2 / 3 := by
  unfold laplaceCs
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

lemma hankelBeta1_cube : hankelBeta1 ^ 3 = (Real.pi ^ 2 * √3) ^ 2 := by
  unfold hankelBeta1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

/-- `c_s β₁ = π²`, i.e. `π² / (c_s β₁) = 1`. -/
lemma laplaceCs_mul_hankelBeta1 : laplaceCs * hankelBeta1 = Real.pi ^ 2 := by
  have hA : 0 < laplaceCs * hankelBeta1 := mul_pos laplaceCs_pos hankelBeta1_pos
  have hB : 0 < Real.pi ^ 2 := by positivity
  have h3 : (laplaceCs * hankelBeta1) ^ 3 = (Real.pi ^ 2) ^ 3 := by
    rw [mul_pow, laplaceCs_cube, hankelBeta1_cube, mul_pow, Real.sq_sqrt (by norm_num)]
    ring
  exact (pow_left_inj₀ hA.le hB.le (by norm_num)).mp h3

lemma laplaceCs_div_hankelBeta1 : Real.pi ^ 2 / (laplaceCs * hankelBeta1) = 1 := by
  rw [laplaceCs_mul_hankelBeta1, div_self (by positivity)]


/-- Statement 2 (reality and positivity). For `0 ≤ ζ < 1`, `K₀(ζ, Δ/c)` is real and positive.
The case `ζ = 0` is `K₀ = 1` (from `mellin_strip_kernel_eq`); the case `0 < ζ < 1` is
`mellinK0_saddle_pos`. -/
lemma mellinK0_laplace_real {c y Δ : ℝ} (hc : 0 < c) (hy : 0 ≤ y) (hζ : laplaceZeta c y < 1)
    (hΔ : 0 < Δ) :
    (mellinK0 c (laplaceZeta c y : ℂ) (Δ / c)).im = 0 ∧
      0 < (mellinK0 c (laplaceZeta c y : ℂ) (Δ / c)).re := by
  have hξ : 0 < Δ / c := div_pos hΔ hc
  have hζ0 : 0 ≤ laplaceZeta c y := by
    unfold laplaceZeta
    have h1 : 0 ≤ y / laplaceCs := div_nonneg hy laplaceCs_pos.le
    have h2 : 0 < radialEps c := radialEps_pos hc
    exact mul_nonneg h1 h2.le
  rcases eq_or_lt_of_le hζ0 with h0 | hpos
  · have hΓ : Complex.Gamma (c : ℂ) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by simpa using hc)
    have key : mellinK0 c 0 (Δ / c) = 1 := by
      rw [← mellin_strip_kernel_eq hc hξ (ζ := 0) (by simp) (by norm_num)]
      simp [stripH, hΓ]
    have hz : (laplaceZeta c y : ℂ) = 0 := by
      rw [← h0]; simp
    rw [hz, key]
    simp
  · exact mellinK0_saddle_pos hc hξ hpos hζ

/-- Statement 3 (Gamma form). For `0 ≤ ζ < 1` and `Δ > 0`, with `ζ = laplaceZeta c y`, the weight is
`exp(-c Re ℋ(ζ)) (2π)^{-cζ} Γ(c)/Γ(c(1-ζ)) Δ^{-cζ}`, where `ℋ = stripH` at the real point.
Proof: `K₀ = Γ-ratio · (2πΔ)^{cζ} · exp(c ℋ(ζ))` by `mellin_strip_kernel_eq` (note `2π c ξ = 2π Δ`),
`K₀` is real and positive by statement 2, so the weight is `1/K₀ = 1/‖K₀‖`. -/
lemma laplaceWeight_gamma_form {c y Δ : ℝ} (hc : 0 < c) (hy : 0 ≤ y)
    (hζ : laplaceZeta c y < 1) (hΔ : 0 < Δ) :
    laplaceWeight c y Δ =
      Real.exp (-c * (stripH (laplaceZeta c y : ℂ)).re) * (2 * Real.pi) ^ (-(c * laplaceZeta c y)) *
        Real.Gamma c / Real.Gamma (c * (1 - laplaceZeta c y)) * Δ ^ (-(c * laplaceZeta c y)) := by
  have hξ : 0 < Δ / c := div_pos hΔ hc
  have hζ0 : 0 ≤ laplaceZeta c y := by
    unfold laplaceZeta
    have h1 : 0 ≤ y / laplaceCs := div_nonneg hy laplaceCs_pos.le
    have h2 : 0 < radialEps c := radialEps_pos hc
    exact mul_nonneg h1 h2.le
  obtain ⟨him, hre⟩ := mellinK0_laplace_real hc hy hζ hΔ
  set ζ : ℝ := laplaceZeta c y with hζdef
  set K : ℂ := mellinK0 c (ζ : ℂ) (Δ / c) with hKdef
  have hKeq := mellin_strip_kernel_eq hc hξ (ζ := (ζ : ℂ)) (by simpa using hζ0)
    (by simpa using hζ)
  rw [← hKdef] at hKeq
  have hKnorm : K.re = ‖K‖ := by
    have hKreal : K = ((K.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    conv_rhs => rw [hKreal]
    rw [Complex.norm_real, Real.norm_of_nonneg hre.le]
  have hinv : laplaceWeight c y Δ = K.re⁻¹ := by
    unfold laplaceWeight
    rw [← hζdef, ← hKdef, Complex.inv_re, Complex.normSq_apply, him]
    have := hre.ne'
    field_simp
    ring
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hζ1 : (0 : ℝ) < c * (1 - ζ) := mul_pos hc (by linarith)
  have hΓc : 0 < Real.Gamma c := Real.Gamma_pos_of_pos hc
  have hΓ1 : 0 < Real.Gamma (c * (1 - ζ)) := Real.Gamma_pos_of_pos hζ1
  have hG : ‖Complex.Gamma ((c : ℂ) * (1 - (ζ : ℂ))) / Complex.Gamma (c : ℂ)‖ =
      Real.Gamma (c * (1 - ζ)) / Real.Gamma c := by
    have e1 : (c : ℂ) * (1 - (ζ : ℂ)) = ((c * (1 - ζ) : ℝ) : ℂ) := by push_cast; ring
    rw [e1, norm_div, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg hΓ1.le, Real.norm_of_nonneg hΓc.le]
  have hP : ‖(2 * (Real.pi : ℂ) * (c : ℂ) * ((Δ / c : ℝ) : ℂ)) ^ ((c : ℂ) * (ζ : ℂ))‖ =
      (2 * Real.pi) ^ (c * ζ) * Δ ^ (c * ζ) := by
    have e2 : (2 * (Real.pi : ℂ) * (c : ℂ) * ((Δ / c : ℝ) : ℂ)) = ((2 * Real.pi * Δ : ℝ) : ℂ) := by
      push_cast
      field_simp
    have e3 : (c : ℂ) * (ζ : ℂ) = ((c * ζ : ℝ) : ℂ) := by push_cast; ring
    have hpos : 0 < 2 * Real.pi * Δ := by positivity
    rw [e2, e3, Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.ofReal_re,
      Real.mul_rpow (by positivity) hΔ.le]
  have hE : ‖Complex.exp ((c : ℂ) * stripH (ζ : ℂ))‖ = Real.exp (c * (stripH (ζ : ℂ)).re) := by
    rw [Complex.norm_exp, Complex.re_ofReal_mul]
  have hnormK : ‖K‖ = Real.Gamma (c * (1 - ζ)) / Real.Gamma c * ((2 * Real.pi) ^ (c * ζ) * Δ ^ (c * ζ)) *
      Real.exp (c * (stripH (ζ : ℂ)).re) := by
    rw [← hKeq, norm_mul, norm_mul, hG, hP, hE]
  rw [hinv, hKnorm, hnormK]
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [Real.rpow_neg h2π, Real.rpow_neg hΔ.le, neg_mul, Real.exp_neg]
  field_simp

/-- Positivity of the weight: `0 < W_c(y, Δ)` for `c, Δ > 0`, `0 ≤ y`, `ζ_c(y) < 1`. -/
lemma laplaceWeight_pos {c y Δ : ℝ} (hc : 0 < c) (hy : 0 ≤ y)
    (hζ : laplaceZeta c y < 1) (hΔ : 0 < Δ) : 0 < laplaceWeight c y Δ := by
  have hζ0 : 0 ≤ laplaceZeta c y := by
    unfold laplaceZeta
    exact mul_nonneg (div_nonneg hy laplaceCs_pos.le) (radialEps_pos hc).le
  have hζ1 : (0 : ℝ) < c * (1 - laplaceZeta c y) := mul_pos hc (by linarith)
  rw [laplaceWeight_gamma_form hc hy hζ hΔ]
  have := Real.Gamma_pos_of_pos hc
  have := Real.Gamma_pos_of_pos hζ1
  positivity

/-- Statement 4 (exact scaling in `Δ`). Only the factor `(2πΔ)^{cζ}` of `K₀` depends on `Δ`. -/
lemma laplaceWeight_scale {c y Δ Δ' : ℝ} (hc : 0 < c) (hy : 0 ≤ y)
    (hζ : laplaceZeta c y < 1) (hΔ : 0 < Δ) (hΔ' : 0 < Δ') :
    laplaceWeight c y Δ' = laplaceWeight c y Δ * (Δ / Δ') ^ (c * laplaceZeta c y) := by
  rw [laplaceWeight_gamma_form hc hy hζ hΔ', laplaceWeight_gamma_form hc hy hζ hΔ,
    Real.div_rpow hΔ.le hΔ'.le, Real.rpow_neg hΔ.le, Real.rpow_neg hΔ'.le]
  have ha : Δ ^ (c * laplaceZeta c y) ≠ 0 := (Real.rpow_pos_of_pos hΔ _).ne'
  have hb : Δ' ^ (c * laplaceZeta c y) ≠ 0 := (Real.rpow_pos_of_pos hΔ' _).ne'
  field_simp

/-- `c^{1/3} = c ε_c²`, with `ε_c = radialEps c = c^{-1/3}`. -/
lemma rpow_third_eq_mul_radialEps_sq {c : ℝ} (hc : 0 < c) :
    c ^ (1 / 3 : ℝ) = c * radialEps c ^ 2 := by
  have h1 : c ^ (1 / 3 : ℝ) * radialEps c = 1 := by
    unfold radialEps
    rw [← Real.rpow_add hc]
    norm_num
  have h2 : c * radialEps c ^ 3 = 1 := radialEps_cube hc
  calc c ^ (1 / 3 : ℝ) = c ^ (1 / 3 : ℝ) * (c * radialEps c ^ 3) := by rw [h2, mul_one]
    _ = c * radialEps c ^ 2 * (c ^ (1 / 3 : ℝ) * radialEps c) := by ring
    _ = c * radialEps c ^ 2 := by rw [h1, mul_one]

/-- `Δ_c(u) / c = ξ_c(-u/β₁)`, where `Δ_c(u) = c/π² - (u/β₁) c^{1/3}`. -/
lemma delta_div_eq_radialXi {c u : ℝ} (hc : 0 < c) :
    (c / Real.pi ^ 2 - (u / hankelBeta1) * c ^ (1 / 3 : ℝ)) / c =
      radialXi c (-u / hankelBeta1) := by
  unfold radialXi
  rw [rpow_third_eq_mul_radialEps_sq hc]
  have hc' : c ≠ 0 := hc.ne'
  have hπ : Real.pi ^ 2 ≠ 0 := by positivity
  have hβ : hankelBeta1 ≠ 0 := hankelBeta1_pos.ne'
  field_simp
  ring

/-- Weight in terms of the rescaled kernel: `W_c(y, Δ) = re((radialK c (y/c_s) s)⁻¹)` when
`Δ / c = radialXi c s`. -/
lemma laplaceWeight_eq_radialK {c y Δ s : ℝ} (hΔ : Δ / c = radialXi c s) :
    laplaceWeight c y Δ = ((radialK c ((y / laplaceCs : ℝ) : ℂ) s)⁻¹).re := by
  have hz : (laplaceZeta c y : ℂ) = (radialEps c : ℂ) * ((y / laplaceCs : ℝ) : ℂ) := by
    unfold laplaceZeta; push_cast; ring
  unfold laplaceWeight radialK
  rw [hz, hΔ]

/-- The limit kernel evaluated at `w = y/c_s`, `s = -u₀/β₁`, is `exp(y³/12 - u₀ y)`. -/
lemma radialKlim_laplace (y u₀ : ℝ) :
    radialKlim ((y / laplaceCs : ℝ) : ℂ) (-u₀ / hankelBeta1) =
      Complex.exp ((((y ^ 3 / 12 - y * u₀ : ℝ)) : ℂ)) := by
  unfold radialKlim
  congr 1
  have hcs : laplaceCs ≠ 0 := laplaceCs_pos.ne'
  have hβ : hankelBeta1 ≠ 0 := hankelBeta1_pos.ne'
  have hP : Real.pi ^ 2 = laplaceCs * hankelBeta1 := laplaceCs_mul_hankelBeta1.symm
  have t1 : Real.pi ^ 2 / 36 * (y / laplaceCs) ^ 3 = y ^ 3 / 12 := by
    rw [div_pow, laplaceCs_cube]
    have hπ : Real.pi ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  have t2 : Real.pi ^ 2 * (-u₀ / hankelBeta1) * (y / laplaceCs) = -(u₀ * y) := by
    rw [hP]
    field_simp
  have hR : Real.pi ^ 2 / 36 * (y / laplaceCs) ^ 3 + Real.pi ^ 2 * (-u₀ / hankelBeta1) * (y / laplaceCs)
      = y ^ 3 / 12 - y * u₀ := by
    rw [t1, t2]; ring
  have hC : ((Real.pi : ℂ) ^ 2 / 36) * ((y / laplaceCs : ℝ) : ℂ) ^ 3
      + (Real.pi : ℂ) ^ 2 * ((-u₀ / hankelBeta1 : ℝ) : ℂ) * ((y / laplaceCs : ℝ) : ℂ)
      = ((y ^ 3 / 12 - y * u₀ : ℝ) : ℂ) := by
    rw [← hR]; push_cast; ring
  exact hC

/-- Statement 5 (limit). For `c i → ∞` and `u i → u₀`, with `Δ_i = c_i/π² - (u_i/β₁) c_i^{1/3}`,
`W_{c_i}(y, Δ_i) → exp(-y³/12 + y u₀)`. Holds for every real `y` (the brief's `y ≥ 0` is not needed).
Proof: `Δ/c = radialXi c (-u/β₁)` and `laplaceWeight = re ∘ inv ∘ radialK` (`laplaceWeight_eq_radialK`),
then `radialK_tendsto` with `w = y/c_s` and `radialKlim` evaluated by `radialKlim_laplace`. -/
theorem laplaceWeight_tendsto {ι : Type*} {l : Filter ι} {c u : ι → ℝ} {u₀ : ℝ} (y : ℝ)
    (hc : Tendsto c l atTop) (hu : Tendsto u l (𝓝 u₀)) :
    Tendsto (fun i => laplaceWeight (c i) y
        (c i / Real.pi ^ 2 - (u i / hankelBeta1) * c i ^ (1 / 3 : ℝ))) l
      (𝓝 (Real.exp (-(y ^ 3) / 12 + y * u₀))) := by
  have hcpos : ∀ᶠ i in l, 0 < c i := hc.eventually_gt_atTop 0
  have hs : Tendsto (fun i => -u i / hankelBeta1) l (𝓝 (-u₀ / hankelBeta1)) :=
    (hu.neg).div_const _
  have hK := radialK_tendsto hc hs ((y / laplaceCs : ℝ) : ℂ)
  have hne : radialKlim ((y / laplaceCs : ℝ) : ℂ) (-u₀ / hankelBeta1) ≠ 0 := by
    rw [radialKlim_laplace]; exact Complex.exp_ne_zero _
  have hT : Tendsto (fun i => ((radialK (c i) ((y / laplaceCs : ℝ) : ℂ) (-u i / hankelBeta1))⁻¹).re) l
      (𝓝 ((radialKlim ((y / laplaceCs : ℝ) : ℂ) (-u₀ / hankelBeta1))⁻¹).re) :=
    (Complex.continuous_re.tendsto _).comp (hK.inv₀ hne)
  have hval : ((radialKlim ((y / laplaceCs : ℝ) : ℂ) (-u₀ / hankelBeta1))⁻¹).re =
      Real.exp (-(y ^ 3) / 12 + y * u₀) := by
    rw [radialKlim_laplace, ← Complex.exp_neg, ← Complex.ofReal_neg, Complex.exp_ofReal_re]
    congr 1
    ring
  rw [hval] at hT
  refine hT.congr' ?_
  filter_upwards [hcpos] with i hi
  exact (laplaceWeight_eq_radialK (delta_div_eq_radialXi hi)).symm

/-- Statement 5 at fixed `u` (the form of `eq:ce-laplace-limit`). -/
theorem laplaceWeight_tendsto_const (y u : ℝ) :
    Tendsto (fun c : ℝ => laplaceWeight c y (c / Real.pi ^ 2 - (u / hankelBeta1) * c ^ (1 / 3 : ℝ)))
      atTop (𝓝 (Real.exp (-(y ^ 3) / 12 + y * u))) :=
  laplaceWeight_tendsto (l := atTop) (c := fun c : ℝ => c) (u := fun _ => u) y tendsto_id
    tendsto_const_nhds

/-- info: 'FormalResearch.SignUncertainty.laplaceCs_mul_hankelBeta1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.laplaceCs_mul_hankelBeta1

/-- info: 'FormalResearch.SignUncertainty.mellinK0_laplace_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.mellinK0_laplace_real

/-- info: 'FormalResearch.SignUncertainty.laplaceWeight_gamma_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.laplaceWeight_gamma_form

/-- info: 'FormalResearch.SignUncertainty.laplaceWeight_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.laplaceWeight_pos

/-- info: 'FormalResearch.SignUncertainty.laplaceWeight_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.laplaceWeight_scale

/-- info: 'FormalResearch.SignUncertainty.laplaceWeight_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.laplaceWeight_tendsto

/-- info: 'FormalResearch.SignUncertainty.laplaceWeight_tendsto_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.laplaceWeight_tendsto_const

end FormalResearch.SignUncertainty
