module

public import FormalResearch.SignUncertainty.CtChartQeps

/-!
# The value `Q_0 = Q_geo(0,0) = -(7/200)(18π²)^{1/3}` (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 2 (`Q_0 := Q_geo(0;0)`).  **Proved.**
`Q_geo(0,0) = ∂_y μ(0,0)` is computed along the slice `β = 0` from `Z'(0) = 1/d₀²`, `R(0,0) = -(7/50) d₀⁴`, `U'(0) = 7/50`,
`Σ'(0) = -(63/50) d₀³` (`Σ = U k(Z)/2`), `(√Σ)' = -(63/100) d₀²`, `T_s' = 21/50`, giving `-(21/100) d₀ = -(7/200)(18π²)^{1/3}`.
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.CtChart

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- `d₀` as a complex number. -/
noncomputable abbrev dd : ℂ := ((CtCfu.d0 : ℝ) : ℂ)

lemma dd_ne : dd ≠ 0 := by
  have := CtCfu.d0_pos
  exact Complex.ofReal_ne_zero.mpr this.ne'

lemma pi_sq_c : (π : ℂ) ^ 2 = 12 * dd ^ 3 := by
  have := CtCfu.d0_pi_sq
  have h := congrArg (fun x : ℝ => (x : ℂ)) this
  simpa using h

lemma pi_four_c : (π : ℂ) ^ 4 = 144 * dd ^ 6 := by
  have : (π : ℂ) ^ 4 = ((π : ℂ) ^ 2) ^ 2 := by ring
  rw [this, pi_sq_c]; ring

lemma pC2_zero_val : pC2 0 = -(7 * (π : ℂ) ^ 4 / 3600) := by
  have h := pC2_eq.self_of_nhds
  rw [h, hasDerivAt_nC_zero.deriv, hasDerivAt_ntC_zero.deriv]
  ring

lemma Hf_zero_val : Hf (0, 0) = 7 * (π : ℂ) ^ 4 / 7200 := by
  rw [Hf_diag, pC2_zero_val]; ring

lemma R0_val : Rf (0, 0) = -(7 / 50) * dd ^ 4 := by
  rw [Rf_zero]
  unfold R0
  rw [Hf_zero_val, pi_four_c]
  have := dd_ne
  field_simp
  ring

lemma Vz_zero_val : Vz (0, 0) = -(7 / 50) * dd ^ 4 := by
  rw [← R0_val]; exact Vz_diag.self_of_nhds

/-- Derivative along `y ↦ F(Z(y,0), 0)`. -/
lemma hasDerivAt_comp_Zs {F : ℂ × ℂ → ℂ} (hF : ContDiffAt ℂ ∞' F (0, 0)) :
    HasDerivAt (fun y : ℂ => F (Zf (y, 0), 0)) (dyF F (0, 0) * dyF Zf (0, 0)) 0 := by
  have hZ : HasDerivAt (fun y : ℂ => Zf (y, 0)) (dyF Zf (0, 0)) 0 :=
    hasDerivAt_slice1 (q := (0, 0)) (contDiffAt_Zf.differentiableAt (by simp))
  have h1 : HasDerivAt (fun z : ℂ => F (z, 0)) (dyF F (0, 0)) (Zf (0, 0)) := by
    rw [Zf_zero]; exact hasDerivAt_slice1 (q := (0, 0)) (hF.differentiableAt (by simp))
  have := HasDerivAt.comp (0 : ℂ) h1 hZ
  simpa [Function.comp_def, mul_comm] using this

lemma hasDerivAt_Zs : HasDerivAt (fun y : ℂ => Zf (y, 0)) (1 / dd ^ 2) 0 := by
  have hZ : HasDerivAt (fun y : ℂ => Zf (y, 0)) (dyF Zf (0, 0)) 0 :=
    hasDerivAt_slice1 (q := (0, 0)) (contDiffAt_Zf.differentiableAt (by simp))
  have hW := hasDerivAt_comp_Zs contDiffAt_Vf
  have hprod := hZ.mul (hW.pow 2)
  have hev : (fun y : ℂ => Zf (y, 0) * Vf (Zf (y, 0), 0) ^ 2) =ᶠ[𝓝 0] fun y => y := by
    have ht : Tendsto (fun y : ℂ => (y, (0 : ℂ))) (𝓝 0) (𝓝 ((0 : ℂ), (0 : ℂ))) :=
      (continuous_id.prodMk continuous_const).tendsto' 0 _ rfl
    filter_upwards [ht.eventually Zf_eq] with y hy
    exact hy
  have hid : HasDerivAt (fun y : ℂ => Zf (y, 0) * Vf (Zf (y, 0), 0) ^ 2) 1 0 :=
    (hasDerivAt_id' (0 : ℂ)).congr_of_eventuallyEq hev
  have hu := hid.unique hprod
  have hV0 : ((fun y : ℂ => Vf (Zf (y, 0), 0)) ^ 2) 0 = dd ^ 2 := by simp [Zf_zero, Vf_zero]
  simp only [Zf_zero, zero_mul, add_zero] at hu
  rw [hV0] at hu
  have hd := dd_ne
  have : dyF Zf (0, 0) = 1 / dd ^ 2 := by
    field_simp
    linear_combination -hu
  rw [← this]; exact hZ

lemma dyZ_val : dyF Zf (0, 0) = 1 / dd ^ 2 :=
  (hasDerivAt_slice1 (q := (0, 0)) (contDiffAt_Zf.differentiableAt (by simp))).unique hasDerivAt_Zs

lemma hasDerivAt_Vs : HasDerivAt (fun y : ℂ => Vf (Zf (y, 0), 0)) (-(7 / 50) * dd ^ 2) 0 := by
  have h := hasDerivAt_comp_Zs contDiffAt_Vf
  have e : dyF Vf (0, 0) * dyF Zf (0, 0) = -(7 / 50) * dd ^ 2 := by
    rw [dyZ_val]
    have : dyF Vf (0, 0) = -(7 / 50) * dd ^ 4 := Vz_zero_val
    rw [this]; have := dd_ne; field_simp
  rwa [e] at h

lemma hasDerivAt_Us : HasDerivAt (fun y : ℂ => Uf (y, 0)) (7 / 50) 0 := by
  have hne : Vf (Zf (0, 0), 0) ≠ 0 := by rw [Zf_zero, Vf_zero]; exact dd_ne
  have h := (hasDerivAt_const (0 : ℂ) (1 : ℂ)).div hasDerivAt_Vs hne
  have e : (0 * Vf (Zf (0, 0), 0) - 1 * (-(7 / 50) * dd ^ 2)) / Vf (Zf (0, 0), 0) ^ 2 = 7 / 50 := by
    rw [Zf_zero, Vf_zero]; have := dd_ne; field_simp; ring
  rw [e] at h
  exact h

lemma hasDerivAt_Ks : HasDerivAt (fun y : ℂ => kC (Zf (y, 0))) (-(14 / 5) * dd ^ 4) 0 := by
  have hZ : HasDerivAt (fun y : ℂ => Zf (y, 0)) (1 / dd ^ 2) 0 := hasDerivAt_Zs
  have hk : HasDerivAt kC (-(7 * (π : ℂ) ^ 4 / 360)) (Zf (0, 0)) := by rw [Zf_zero]; exact hasDerivAt_kC_zero
  have h := HasDerivAt.comp (0 : ℂ) hk hZ
  have e : -(7 * (π : ℂ) ^ 4 / 360) * (1 / dd ^ 2) = -(14 / 5) * dd ^ 4 := by
    rw [pi_four_c]; have := dd_ne; field_simp; ring
  rw [e] at h
  exact h

lemma hasDerivAt_csq {x : ℂ} (hx : x ∈ Complex.slitPlane) : HasDerivAt csq (csq x / (2 * x)) x := by
  have hx0 : x ≠ 0 := Complex.slitPlane_ne_zero hx
  have h := ((Complex.hasDerivAt_log hx).div_const 2).cexp
  have e : csq = fun x => Complex.exp (Complex.log x / 2) := rfl
  rw [e]
  convert h using 1
  simp only [csq]
  field_simp

lemma hasDerivAt_Sigma : HasDerivAt (fun y : ℂ => Uf (y, 0) * kC (Zf (y, 0)) / 2) (-(63 / 50) * dd ^ 3) 0 := by
  have h := (hasDerivAt_Us.mul hasDerivAt_Ks).div_const 2
  have e : (7 / 50 * kC (Zf (0, 0)) + Uf (0, 0) * (-(14 / 5) * dd ^ 4)) / 2 = -(63 / 50) * dd ^ 3 := by
    rw [Zf_zero, kC_zero, Uf_zero, pi_sq_c]; have := dd_ne; field_simp; ring
  rw [e] at h
  exact h

lemma hasDerivAt_Ds : HasDerivAt (fun y : ℂ => Vf (Zf (y, 0), 0) + 2 * Zf (y, 0) * Vz (Zf (y, 0), 0))
    (-(21 / 50) * dd ^ 2) 0 := by
  have hVzc := hasDerivAt_comp_Zs (F := Vz) contDiffAt_Vz
  have h := hasDerivAt_Vs.add (((hasDerivAt_Zs.const_mul 2).mul hVzc))
  have e : -(7 / 50) * dd ^ 2 + (2 * (1 / dd ^ 2) * Vz (Zf (0, 0), 0) +
      2 * Zf (0, 0) * (dyF Vz (0, 0) * dyF Zf (0, 0))) = -(21 / 50) * dd ^ 2 := by
    rw [Zf_zero, Vz_zero_val]; have := dd_ne; field_simp; ring
  rw [e] at h
  exact h

lemma hasDerivAt_Tsd : HasDerivAt (fun y : ℂ => Tsd (y, 0)) (21 / 50) 0 := by
  have hne : Vf (Zf (0, 0), 0) + 2 * Zf (0, 0) * Vz (Zf (0, 0), 0) ≠ 0 := by
    rw [Zf_zero, Vf_zero]; simpa using CtCfu.d0_pos.ne'
  have h := (hasDerivAt_const (0 : ℂ) (1 : ℂ)).div hasDerivAt_Ds hne
  have e : (0 * (Vf (Zf (0, 0), 0) + 2 * Zf (0, 0) * Vz (Zf (0, 0), 0)) - 1 * (-(21 / 50) * dd ^ 2)) /
      (Vf (Zf (0, 0), 0) + 2 * Zf (0, 0) * Vz (Zf (0, 0), 0)) ^ 2 = 21 / 50 := by
    have hD : Vf (Zf (0, 0), 0) + 2 * Zf (0, 0) * Vz (Zf (0, 0), 0) = dd := by rw [Zf_zero, Vf_zero]; ring
    rw [hD, div_eq_iff (pow_ne_zero 2 dd_ne)]; ring
  rw [e] at h
  exact h

/-- **`Q_0`**: `Q_geo(0,0) = -(21/100) d₀ = -(7/200)(18π²)^{1/3}`. -/
theorem Qgeo_zero : Qgeo (0, 0) = -(21 / 100) * dd := by
  have hSig := hasDerivAt_Sigma
  have hcs := HasDerivAt.comp (0 : ℂ) (hasDerivAt_csq slit_Sigma_zero) hSig
  have hmu := hcs.mul hasDerivAt_Tsd
  have h1 : HasDerivAt (fun y : ℂ => muf (y, 0)) (dyF muf (0, 0)) 0 :=
    hasDerivAt_slice1 (q := (0, 0)) (contDiffAt_muf.differentiableAt (by simp))
  have hs : (fun y : ℂ => muf (y, 0)) = (csq ∘ fun y : ℂ => Uf (y, 0) * kC (Zf (y, 0)) / 2) * fun y => Tsd (y, 0) := rfl
  rw [hs] at h1
  have hu := h1.unique hmu
  unfold Qgeo
  rw [hadY_zero, hu]
  simp only [Function.comp_apply]
  rw [Sigma_zero, csq_d0_sq]
  have e : Tsd (0, 0) = 1 / dd := Tsd_zero
  rw [e]
  have := dd_ne
  have h0 : CtCfu.d0 ≠ 0 := CtCfu.d0_pos.ne'
  field_simp
  ring

lemma eighteen_pi_sq_third : (18 * π ^ 2) ^ ((1 : ℝ) / 3) = 6 * CtCfu.d0 := by
  have h1 : 18 * π ^ 2 = (6 : ℝ) ^ 3 * (π ^ 2 / 12) := by ring
  rw [h1, Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  have : (1 : ℝ) / 3 = ((3 : ℕ) : ℝ)⁻¹ := by norm_num
  rw [this, Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]

/-- **`ct:cfu` (`Q_0`).** `Q_0 = Q_geo(0,0) = -(7/200)(18π²)^{1/3}` (real). -/
theorem Qgeo_zero_paper : Qgeo (0, 0) = ((-(7 / 200) * (18 * π ^ 2) ^ ((1 : ℝ) / 3) : ℝ) : ℂ) := by
  rw [Qgeo_zero, eighteen_pi_sq_third]
  push_cast
  ring

/-- info: 'FormalResearch.SignUncertainty.CtChart.Qgeo_zero_paper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Qgeo_zero_paper

end FormalResearch.SignUncertainty.CtChart
