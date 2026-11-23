module

public import FormalResearch.SignUncertainty.DeepLobeKernel
public import FormalResearch.SignUncertainty.StripGExpansion
public import FormalResearch.CohnElkies.HighBandEstimate

/-!
# The kernel `K₀(ε w, ξ)` on the strip `0 ≤ Re w ≤ 1` (`u1co:O5`(1))

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, proof of `u1co:O5`(1).  With `ε = c^{-1/3}`
(`c ε³ = 1`) and `log(π² ξ) = π² ε² S`:

* `norm_K0_strip_le`: `‖K₀(ε w, ξ)‖ ≤ 2 exp(1 + π² |S|)` on `0 ≤ Re w ≤ 1`;
* `norm_K0_line_le`: on `Re w = 1` the extra factor `exp(-(3/56) min(v², c ε))`;
* `K0_near_approx`: for `ε ‖w‖ ≤ 1/4` and `ε²(1+|v|)⁵ ≤ M`, on `Re w = 1`,
  `‖K₀(ε w, ξ) - exp(π² w³/36 + (π² S + ε/2) w)‖ ≤ C_M ε² (1+|v|)⁵ e^{-π² v²/12}`.

Status: proved, unconditional.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

lemma lobeU_nonneg (τ : ℝ) : 0 ≤ lobeU τ := by
  unfold lobeU
  have := le_max_left (0 : ℝ) (Real.log |τ|)
  positivity

lemma lobeU_ge_half_min_sq (τ : ℝ) : (1 / 2 : ℝ) * min (τ ^ 2) 1 ≤ lobeU τ := by
  unfold lobeU
  have := le_max_left (0 : ℝ) (Real.log |τ|)
  linarith

lemma eps_cube_inv {c ε : ℝ} (hε : 0 < ε) (hcube : c * ε ^ 3 = 1) : 0 < c := by
  by_contra h
  push Not at h
  nlinarith [pow_pos hε 3]

lemma eps_ge_eight {c ε : ℝ} (hε : 0 < ε) (hcube : c * ε ^ 3 = 1) (hε2 : ε ≤ 1 / 2) : 8 ≤ c := by
  have h3 : ε ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ hε.le hε2 3
  nlinarith [pow_pos hε 3]

/-- The scalar bound of `K₀` on the strip. -/
lemma norm_K0_strip_le {c ε ξ S σ v : ℝ} (hε : 0 < ε) (hcube : c * ε ^ 3 = 1) (hε2 : ε ≤ 1 / 2) (hξ : 0 < ξ)
    (hL : Real.log (Real.pi ^ 2 * ξ) = Real.pi ^ 2 * ε ^ 2 * S) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    ‖mellinK0 c ((ε : ℂ) * ((σ : ℂ) + (v : ℂ) * Complex.I)) ξ‖ ≤ 2 * Real.exp (1 + Real.pi ^ 2 * |S|) := by
  have hc := eps_cube_inv hε hcube
  have hc8 := eps_ge_eight hε hcube hε2
  have hpos : 0 < 2 * Real.exp (1 + Real.pi ^ 2 * |S|) := by positivity
  have hone : 1 ≤ 2 * Real.exp (1 + Real.pi ^ 2 * |S|) := by
    have : 1 ≤ Real.exp (1 + Real.pi ^ 2 * |S|) := Real.one_le_exp (by positivity)
    linarith
  rcases hσ0.eq_or_lt with h0 | hpos'
  · subst h0
    have harg : (ε : ℂ) * (((0 : ℝ) : ℂ) + (v : ℂ) * Complex.I) = ((ε * v : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [harg]
    refine ((norm_mellinK0_imag_le hc hξ (ε * v)).2).trans ?_
    refine le_trans ?_ hone
    exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg (ε * v)]) (by norm_num)
  · have hs0 : 0 < ε * σ := mul_pos hε hpos'
    have hs : ε * σ ≤ 1 / 2 := by nlinarith
    have harg : (ε : ℂ) * ((σ : ℂ) + (v : ℂ) * Complex.I) = ((ε * σ : ℝ) : ℂ) + ((ε * v : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg]
    refine (norm_mellinK0_vert_le hc hξ hs0 hs).trans ?_
    have hU := lobeU_nonneg (ε * v)
    have hexp2 : Real.exp (-(c * (2 * (3 / 56 : ℝ) * (ε * σ) * lobeU (ε * v)))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        have : 0 ≤ c * (2 * (3 / 56 : ℝ) * (ε * σ) * lobeU (ε * v)) := by positivity
        linarith)
    have hsum : 1 / (4 * c) + c * ((4 / 9 : ℝ) * (ε * σ) ^ 3 + ε * σ * Real.log (Real.pi ^ 2 * ξ)) ≤
        1 + Real.pi ^ 2 * |S| := by
      have h1 : 1 / (4 * c) ≤ 1 / 32 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      have h2 : c * ((4 / 9 : ℝ) * (ε * σ) ^ 3) ≤ 4 / 9 := by
        have : (ε * σ) ^ 3 ≤ ε ^ 3 := by
          rw [mul_pow]; exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ hpos'.le hσ1)
        nlinarith [mul_le_mul_of_nonneg_left this hc.le]
      have h3 : c * (ε * σ * Real.log (Real.pi ^ 2 * ξ)) ≤ Real.pi ^ 2 * |S| := by
        rw [hL]
        have : c * (ε * σ * (Real.pi ^ 2 * ε ^ 2 * S)) = (c * ε ^ 3) * (Real.pi ^ 2 * σ * S) := by ring
        rw [this, hcube, one_mul]
        calc Real.pi ^ 2 * σ * S ≤ Real.pi ^ 2 * σ * |S| := by gcongr; exact le_abs_self _
          _ ≤ Real.pi ^ 2 * 1 * |S| := by gcongr
          _ = _ := by ring
      nlinarith
    calc 2 * Real.exp (1 / (4 * c)) * Real.exp (c * ((4 / 9 : ℝ) * (ε * σ) ^ 3 + ε * σ * Real.log (Real.pi ^ 2 * ξ))) *
          Real.exp (-(c * (2 * (3 / 56 : ℝ) * (ε * σ) * lobeU (ε * v))))
        ≤ 2 * Real.exp (1 / (4 * c)) * Real.exp (c * ((4 / 9 : ℝ) * (ε * σ) ^ 3 + ε * σ * Real.log (Real.pi ^ 2 * ξ))) * 1 := by
          gcongr
      _ = 2 * Real.exp (1 / (4 * c) + c * ((4 / 9 : ℝ) * (ε * σ) ^ 3 + ε * σ * Real.log (Real.pi ^ 2 * ξ))) := by
          rw [Real.exp_add]; ring
      _ ≤ _ := by gcongr

/-- The Gaussian-type decay of `K₀` on `Re w = 1`. -/
lemma norm_K0_line_le {c ε ξ S v : ℝ} (hε : 0 < ε) (hcube : c * ε ^ 3 = 1) (hε2 : ε ≤ 1 / 2) (hξ : 0 < ξ)
    (hL : Real.log (Real.pi ^ 2 * ξ) = Real.pi ^ 2 * ε ^ 2 * S) :
    ‖mellinK0 c ((ε : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ‖ ≤
      2 * Real.exp (1 + Real.pi ^ 2 * |S|) * Real.exp (-((3 / 56 : ℝ) * min (v ^ 2) (c * ε))) := by
  have hc := eps_cube_inv hε hcube
  have hc8 := eps_ge_eight hε hcube hε2
  have hs0 : 0 < ε := hε
  have harg : (ε : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I) = ((ε : ℝ) : ℂ) + ((ε * v : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [harg]
  refine (norm_mellinK0_vert_le hc hξ hs0 hε2).trans ?_
  have hmin : (3 / 56 : ℝ) * min (v ^ 2) (c * ε) ≤ c * (2 * (3 / 56 : ℝ) * ε * lobeU (ε * v)) := by
    have h1 := lobeU_ge_half_min_sq (ε * v)
    have h2 : c * ε * min ((ε * v) ^ 2) 1 = min (v ^ 2) (c * ε) := by
      have : c * ε * ((ε * v) ^ 2) = v ^ 2 := by
        have : c * ε * ((ε * v) ^ 2) = (c * ε ^ 3) * v ^ 2 := by ring
        rw [this, hcube, one_mul]
      rw [← this, mul_min_of_nonneg _ _ (by positivity : 0 ≤ c * ε), mul_one]
    calc (3 / 56 : ℝ) * min (v ^ 2) (c * ε) = (3 / 56 : ℝ) * (c * ε * min ((ε * v) ^ 2) 1) := by rw [h2]
      _ = c * (2 * (3 / 56 : ℝ) * ε * ((1 / 2 : ℝ) * min ((ε * v) ^ 2) 1)) := by ring
      _ ≤ _ := by gcongr
  have hsum : 1 / (4 * c) + c * ((4 / 9 : ℝ) * ε ^ 3 + ε * Real.log (Real.pi ^ 2 * ξ)) ≤ 1 + Real.pi ^ 2 * |S| := by
    have h1 : 1 / (4 * c) ≤ 1 / 32 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have h2 : c * ((4 / 9 : ℝ) * ε ^ 3) = 4 / 9 := by
      have : c * ((4 / 9 : ℝ) * ε ^ 3) = (4 / 9) * (c * ε ^ 3) := by ring
      rw [this, hcube]; ring
    have h3 : c * (ε * Real.log (Real.pi ^ 2 * ξ)) ≤ Real.pi ^ 2 * |S| := by
      rw [hL]
      have : c * (ε * (Real.pi ^ 2 * ε ^ 2 * S)) = (c * ε ^ 3) * (Real.pi ^ 2 * S) := by ring
      rw [this, hcube, one_mul]
      gcongr; exact le_abs_self _
    nlinarith
  calc 2 * Real.exp (1 / (4 * c)) * Real.exp (c * ((4 / 9 : ℝ) * ε ^ 3 + ε * Real.log (Real.pi ^ 2 * ξ))) *
        Real.exp (-(c * (2 * (3 / 56 : ℝ) * ε * lobeU (ε * v))))
      ≤ 2 * Real.exp (1 / (4 * c)) * Real.exp (c * ((4 / 9 : ℝ) * ε ^ 3 + ε * Real.log (Real.pi ^ 2 * ξ))) *
        Real.exp (-((3 / 56 : ℝ) * min (v ^ 2) (c * ε))) := by
        gcongr
    _ = 2 * Real.exp (1 / (4 * c) + c * ((4 / 9 : ℝ) * ε ^ 3 + ε * Real.log (Real.pi ^ 2 * ξ))) *
        Real.exp (-((3 / 56 : ℝ) * min (v ^ 2) (c * ε))) := by rw [Real.exp_add]; ring
    _ ≤ _ := by gcongr

lemma re_one_add_I_cube (v : ℝ) : (((1 : ℂ) + (v : ℂ) * Complex.I) ^ 3).re = 1 - 3 * v ^ 2 := by
  simp [pow_succ, Complex.mul_re, Complex.mul_im]; ring

lemma norm_exp_sub_one_le_mul {x : ℂ} : ‖Complex.exp x - 1‖ ≤ ‖x‖ * Real.exp ‖x‖ := by
  have := Complex.norm_exp_sub_sum_le_norm_mul_exp x 1
  simpa using this

/-- The reference kernel on `Re w = 1`: `exp(π² w³/36 + (π² S + ε/2) w)`. -/
noncomputable def refKernel (S ε : ℝ) (w : ℂ) : ℂ :=
  Complex.exp ((Real.pi ^ 2 / 36 : ℂ) * w ^ 3 + ((Real.pi ^ 2 * S + ε / 2 : ℝ) : ℂ) * w)

lemma norm_refKernel_line (S ε v : ℝ) :
    ‖refKernel S ε ((1 : ℂ) + (v : ℂ) * Complex.I)‖ =
      Real.exp (Real.pi ^ 2 / 36 + Real.pi ^ 2 * S + ε / 2) * Real.exp (-(Real.pi ^ 2 * v ^ 2 / 12)) := by
  unfold refKernel
  rw [Complex.norm_exp, ← Real.exp_add]
  congr 1
  have h3 := re_one_add_I_cube v
  have : ((Real.pi ^ 2 / 36 : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I) ^ 3).re =
      Real.pi ^ 2 / 36 * (1 - 3 * v ^ 2) := by
    have : ((Real.pi ^ 2 / 36 : ℂ)) = ((Real.pi ^ 2 / 36 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.re_ofReal_mul, h3]
  rw [Complex.add_re, this, Complex.re_ofReal_mul]
  simp; ring

lemma K0_near_approx {c ε ξ S v M : ℝ} (hε : 0 < ε) (hcube : c * ε ^ 3 = 1) (hξ : 0 < ξ)
    (hL : Real.log (Real.pi ^ 2 * ξ) = Real.pi ^ 2 * ε ^ 2 * S)
    (hζ : ε * (1 + |v|) ≤ 1 / 4) (hM : ε ^ 2 * (1 + |v|) ^ 5 ≤ M) :
    ‖mellinK0 c ((ε : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ - refKernel S ε ((1 : ℂ) + (v : ℂ) * Complex.I)‖ ≤
      11 * Real.exp (11 * M) * (ε ^ 2 * (1 + |v|) ^ 5) *
        (Real.exp (Real.pi ^ 2 / 36 + Real.pi ^ 2 * S + ε / 2) * Real.exp (-(Real.pi ^ 2 * v ^ 2 / 12))) := by
  have hc := eps_cube_inv hε hcube
  set w : ℂ := (1 : ℂ) + (v : ℂ) * Complex.I with hw
  have hw1 : 1 ≤ ‖w‖ := by
    have : (1 : ℝ) ≤ w.re := by simp [hw]
    exact this.trans (Complex.re_le_norm _)
  have hwle : ‖w‖ ≤ 1 + |v| := by
    calc ‖w‖ ≤ ‖(1 : ℂ)‖ + ‖(v : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = 1 + |v| := by simp
  set ζ : ℂ := (ε : ℂ) * w with hζdef
  have hζn : ‖ζ‖ = ε * ‖w‖ := by rw [hζdef, norm_mul, Complex.norm_real, Real.norm_of_nonneg hε.le]
  have hζ4 : ‖ζ‖ ≤ 1 / 4 := by
    rw [hζn]; calc ε * ‖w‖ ≤ ε * (1 + |v|) := by gcongr
      _ ≤ _ := hζ
  have hε4 : ε ≤ 1 / 4 := by
    have : ε ≤ ε * (1 + |v|) := by nlinarith [abs_nonneg v]
    linarith
  have hre : ζ.re = ε := by simp [hζdef, hw]
  have h1z : 1 - ζ ≠ 0 := fun h => by
    have : (1 - ζ).re = 0 := by rw [h]; simp
    simp [hre] at this; linarith
  have hlogπ : Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ)) = (Real.log (Real.pi ^ 2 * ξ) : ℂ) := by
    rw [show (Real.pi : ℂ) ^ 2 * (ξ : ℂ) = ((Real.pi ^ 2 * ξ : ℝ) : ℂ) by push_cast; ring]
    exact (Complex.ofReal_log (by positivity)).symm
  have hcubeC : (c : ℂ) * (ε : ℂ) ^ 3 = 1 := by exact_mod_cast hcube
  have hLC : (Real.log (Real.pi ^ 2 * ξ) : ℂ) = (Real.pi : ℂ) ^ 2 * (ε : ℂ) ^ 2 * (S : ℂ) := by
    rw [hL]; push_cast; ring
  -- the exponent form of `K₀`
  set h₁ : ℂ := Complex.log (1 - ζ) * (-(1 / 2 : ℂ)) with hh₁
  set b : ℂ := FormalResearch.Asymptotics.binetDiff c ζ with hb
  set d : ℂ := (c : ℂ) * (stripS0Tilde ζ - (Real.pi ^ 2 / 36 : ℂ) * ζ ^ 3) with hd
  have hK : mellinK0 c ζ ξ = Complex.exp (h₁ + b + (c : ℂ) * (stripS0Tilde ζ + ζ * (Real.log (Real.pi ^ 2 * ξ) : ℂ))) := by
    unfold mellinK0 mellinPhi
    rw [Complex.cpow_def_of_ne_zero h1z, hlogπ, ← Complex.exp_add, ← Complex.exp_add]
  have hΔ : h₁ + b + (c : ℂ) * (stripS0Tilde ζ + ζ * (Real.log (Real.pi ^ 2 * ξ) : ℂ)) -
      ((Real.pi ^ 2 / 36 : ℂ) * w ^ 3 + ((Real.pi ^ 2 * S + ε / 2 : ℝ) : ℂ) * w) =
      (h₁ + ζ / 2 * (-1)) + b + d := by
    rw [hd, hLC, hζdef]
    push_cast
    linear_combination ((Real.pi : ℂ) ^ 2 * (S : ℂ) * w + (Real.pi : ℂ) ^ 2 / 36 * w ^ 3) * hcubeC
  have hrefeq : refKernel S ε w = Complex.exp ((Real.pi ^ 2 / 36 : ℂ) * w ^ 3 + ((Real.pi ^ 2 * S + ε / 2 : ℝ) : ℂ) * w) := rfl
  have hdiff : mellinK0 c ζ ξ - refKernel S ε w = refKernel S ε w * (Complex.exp ((h₁ + ζ / 2 * (-1)) + b + d) - 1) := by
    rw [← hΔ, hK, hrefeq, mul_sub, mul_one, ← Complex.exp_add]
    congr 2; ring
  -- bounds on the three pieces
  have hhb : ‖h₁ + ζ / 2 * (-1)‖ ≤ ‖ζ‖ ^ 2 / 3 := by
    have e : h₁ + ζ / 2 * (-1) = -(1 / 2 : ℂ) * (Complex.log (1 + (-ζ)) - (-ζ)) := by
      rw [hh₁]; ring_nf
    rw [e, norm_mul]
    have hn : ‖-ζ‖ < 1 := by rw [norm_neg]; linarith
    have := Complex.norm_log_one_add_sub_self_le hn
    rw [norm_neg] at this
    have h12 : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [h12]
    have hinv : (1 - ‖ζ‖)⁻¹ ≤ 4 / 3 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    calc 1 / 2 * ‖Complex.log (1 + -ζ) - -ζ‖ ≤ 1 / 2 * (‖ζ‖ ^ 2 * (1 - ‖ζ‖)⁻¹ / 2) := by gcongr
      _ ≤ 1 / 2 * (‖ζ‖ ^ 2 * (4 / 3) / 2) := by gcongr
      _ = ‖ζ‖ ^ 2 / 3 := by ring
  have hbn : ‖b‖ ≤ 7 / 36 * ε ^ 3 := by
    have := FormalResearch.Asymptotics.binetDiff_norm_le hc (ζ := ζ) (by rw [hre]; linarith)
    refine this.trans ?_
    rw [hre]
    have h1c : 1 / c = ε ^ 3 := by field_simp; linarith
    have h2 : 1 / (1 - ε) ≤ 4 / 3 := by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    calc 1 / (12 * c) * (1 / (1 - ε) + 1) ≤ 1 / (12 * c) * (4 / 3 + 1) := by gcongr
      _ = 7 / 36 * (1 / c) := by field_simp; ring
      _ = _ := by rw [h1c]
  have hdn : ‖d‖ ≤ 10 * ε ^ 2 * ‖w‖ ^ 5 := by
    have h5 := stripS0Tilde_sub_le hζ4
    rw [hd, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]
    calc c * ‖stripS0Tilde ζ - (Real.pi ^ 2 / 36 : ℂ) * ζ ^ 3‖ ≤ c * (10 * ‖ζ‖ ^ 5) := by gcongr
      _ = 10 * ε ^ 2 * ‖w‖ ^ 5 * (c * ε ^ 3) := by rw [hζn]; ring
      _ = _ := by rw [hcube, mul_one]
  have hε2w : ε ^ 2 * ‖w‖ ^ 5 ≤ ε ^ 2 * (1 + |v|) ^ 5 := by gcongr
  have hw5 : 1 ≤ ‖w‖ ^ 5 := one_le_pow₀ hw1
  have hΔn : ‖(h₁ + ζ / 2 * (-1)) + b + d‖ ≤ 11 * (ε ^ 2 * (1 + |v|) ^ 5) := by
    have h1 : ‖ζ‖ ^ 2 / 3 ≤ ε ^ 2 * ‖w‖ ^ 5 / 3 := by
      rw [hζn, mul_pow]
      have : ‖w‖ ^ 2 ≤ ‖w‖ ^ 5 := pow_le_pow_right₀ hw1 (by norm_num)
      have : ε ^ 2 * ‖w‖ ^ 2 ≤ ε ^ 2 * ‖w‖ ^ 5 := by gcongr
      linarith
    have h2 : 7 / 36 * ε ^ 3 ≤ ε ^ 2 * ‖w‖ ^ 5 := by
      have : ε ^ 3 ≤ ε ^ 2 := by nlinarith [sq_nonneg ε]
      have : ε ^ 2 ≤ ε ^ 2 * ‖w‖ ^ 5 := by nlinarith [sq_nonneg ε]
      nlinarith
    calc ‖(h₁ + ζ / 2 * (-1)) + b + d‖ ≤ ‖h₁ + ζ / 2 * (-1)‖ + ‖b‖ + ‖d‖ := norm_add₃_le
      _ ≤ ε ^ 2 * ‖w‖ ^ 5 / 3 + 7 / 36 * ε ^ 3 + 10 * ε ^ 2 * ‖w‖ ^ 5 := by linarith
      _ ≤ 11 * (ε ^ 2 * ‖w‖ ^ 5) := by nlinarith [sq_nonneg ε]
      _ ≤ 11 * (ε ^ 2 * (1 + |v|) ^ 5) := by gcongr
  have hexp : ‖Complex.exp ((h₁ + ζ / 2 * (-1)) + b + d) - 1‖ ≤ 11 * (ε ^ 2 * (1 + |v|) ^ 5) * Real.exp (11 * M) := by
    refine norm_exp_sub_one_le_mul.trans ?_
    have hm : 11 * (ε ^ 2 * (1 + |v|) ^ 5) ≤ 11 * M := by linarith
    gcongr
    exact hΔn.trans hm
  rw [hdiff, norm_mul, norm_refKernel_line]
  calc _ ≤ (Real.exp (Real.pi ^ 2 / 36 + Real.pi ^ 2 * S + ε / 2) * Real.exp (-(Real.pi ^ 2 * v ^ 2 / 12))) *
        (11 * (ε ^ 2 * (1 + |v|) ^ 5) * Real.exp (11 * M)) := by gcongr
    _ = _ := by ring

/-- info: 'FormalResearch.SignUncertainty.norm_K0_strip_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms norm_K0_strip_le
/-- info: 'FormalResearch.SignUncertainty.norm_K0_line_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms norm_K0_line_le
/-- info: 'FormalResearch.SignUncertainty.K0_near_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms K0_near_approx

end FormalResearch.SignUncertainty
