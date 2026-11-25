module

public import FormalResearch.SignUncertainty.CtOuterEntire
public import FormalResearch.SignUncertainty.HankelEdgePhase

/-!
# The amplitude `u_r` of `ct:outer`: definition, bounds and local holomorphic extensions

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Proposition `ct:outer` (the function
`u_r(t) = 1/2 log (6/π² · m'(|t|) / (|t| (1+t²)))`) and the first paragraph of its proof (1)-(2).
**Proved.**

* `mPrime t = 1/t - π / sinh (π t)`, the derivative of `m(t) = log ((π t/2)/tanh(π t/2))`
  (`mPrime_eq_hankelEdgeM'` identifies it with `hankelEdgeM'` for `t > 0`);
* `uR` (`u_r`, with `uR 0 = 0`): even, `uR t ≤ -log (1+t²) ≤ 0`
  (from `m2_bounds`, `mat:T4`(f)(M2)), and `|uR t| ≤ log (1+t²) + C₀`;
* local holomorphic extensions: for every real `y₀` there is a ball `B(y₀, r)` and a holomorphic `v`
  on it with `v t = uR t` for real `t` in the ball (`exists_holo_uR`), and on `B(0, 3/5)` at `y₀ = 0`
  (`exists_holo_uR_zero`): the paper's "analytic continuation at `0`" (the three factors
  `6(sinh πz - πz)/(πz)³`, `πz/sinh πz`, `1/(1+z²)` stay in `Re > 0`).  Hence `uR` is continuous (`continuous_uR`).
-/

@[expose] public section

open Complex Filter Topology Metric Set
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- `m'(t) = 1/t - π/sinh(π t)`, the derivative of `m(t) = log ((π t / 2)/tanh (π t / 2))`
(value `0` at `t = 0` by Lean's division convention; only used for `t ≠ 0`). -/
noncomputable def mPrime (t : ℝ) : ℝ := 1 / t - π / Real.sinh (π * t)

/-- `u_r(t) = 1/2 · log (6/π² · m'(|t|) / (|t| (1 + t²)))`, with `u_r(0) = 0`
(`ct:outer`, first line). -/
noncomputable def uR (t : ℝ) : ℝ :=
  if t = 0 then 0 else (1 / 2) * Real.log (6 / π ^ 2 * mPrime |t| / (|t| * (1 + t ^ 2)))

lemma mPrime_neg (t : ℝ) : mPrime (-t) = -mPrime t := by
  unfold mPrime
  rw [mul_neg, Real.sinh_neg, one_div, one_div, inv_neg, div_neg]
  ring

lemma mPrime_eq_neg_edgePhiDeriv2 {t : ℝ} (ht : 0 < t) :
    mPrime t = -FormalResearch.CohnElkies.edgePhiDeriv2 t := by
  unfold mPrime FormalResearch.CohnElkies.edgePhiDeriv2
  have hs : 0 < Real.sinh (π * t) := Real.sinh_pos_iff.mpr (by positivity)
  have hpi := Real.pi_pos
  field_simp

lemma mPrime_eq_hankelEdgeM' {t : ℝ} (ht : 0 < t) : mPrime t = hankelEdgeM' t :=
  mPrime_eq_neg_edgePhiDeriv2 ht

/-- `mat:T4`(f)(M2): `t/(1+t²) ≤ m'(t) ≤ (π²/6) t/(1+t²)` for `t > 0`. -/
lemma mPrime_bounds {t : ℝ} (ht : 0 < t) :
    t / (1 + t ^ 2) ≤ mPrime t ∧ mPrime t ≤ π ^ 2 / 6 * (t / (1 + t ^ 2)) := by
  rw [mPrime_eq_neg_edgePhiDeriv2 ht]
  have h := FormalResearch.CohnElkies.m2_bounds ht
  exact ⟨h.2.1, h.2.2⟩

/-- `6/π² · m'(t) / (t (1+t²))`, the argument of the logarithm in `u_r` (for `t ≠ 0`). -/
noncomputable def Freal (t : ℝ) : ℝ := 6 / π ^ 2 * mPrime t / (t * (1 + t ^ 2))

lemma Freal_neg (t : ℝ) : Freal (-t) = Freal t := by
  unfold Freal
  rw [mPrime_neg]
  have : (1 + (-t) ^ 2) = 1 + t ^ 2 := by ring
  rw [this]
  by_cases ht : t = 0
  · simp [ht]
  · field_simp

lemma Freal_bounds_pos {t : ℝ} (hpos : 0 < t) :
    6 / π ^ 2 / (1 + t ^ 2) ^ 2 ≤ Freal t ∧ Freal t ≤ 1 / (1 + t ^ 2) ^ 2 := by
  have hb := mPrime_bounds hpos
  have hpi := Real.pi_pos
  have h1 : 0 < 1 + t ^ 2 := by positivity
  have hden : 0 < t * (1 + t ^ 2) := by positivity
  unfold Freal
  constructor
  · rw [le_div_iff₀ hden]
    have e : 6 / π ^ 2 / (1 + t ^ 2) ^ 2 * (t * (1 + t ^ 2)) =
        6 / π ^ 2 * (t / (1 + t ^ 2)) := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hb.1 (by positivity)
  · rw [div_le_iff₀ hden]
    have : 6 / π ^ 2 * mPrime t ≤ 6 / π ^ 2 * (π ^ 2 / 6 * (t / (1 + t ^ 2))) :=
      mul_le_mul_of_nonneg_left hb.2 (by positivity)
    have e : 6 / π ^ 2 * (π ^ 2 / 6 * (t / (1 + t ^ 2))) = t / (1 + t ^ 2) := by field_simp
    have e2 : 1 / (1 + t ^ 2) ^ 2 * (t * (1 + t ^ 2)) = t / (1 + t ^ 2) := by field_simp
    rw [e2]
    linarith

lemma Freal_bounds {t : ℝ} (ht : t ≠ 0) :
    6 / π ^ 2 / (1 + t ^ 2) ^ 2 ≤ Freal t ∧ Freal t ≤ 1 / (1 + t ^ 2) ^ 2 := by
  rcases lt_or_gt_of_ne ht with h | h
  · have := Freal_bounds_pos (neg_pos.mpr h)
    rw [Freal_neg] at this
    simpa using this
  · exact Freal_bounds_pos h

lemma Freal_pos {t : ℝ} (ht : t ≠ 0) : 0 < Freal t :=
  lt_of_lt_of_le (by have := Real.pi_pos; positivity) (Freal_bounds ht).1

lemma uR_eq {t : ℝ} (ht : t ≠ 0) : uR t = (1 / 2) * Real.log (Freal t) := by
  simp only [uR, ht, ↓reduceIte]
  congr 2
  rcases lt_or_gt_of_ne ht with h | h
  · rw [abs_of_neg h]
    unfold Freal
    rw [mPrime_neg]
    field_simp
  · rw [abs_of_pos h]; rfl

lemma uR_zero : uR 0 = 0 := by simp [uR]

lemma uR_neg (t : ℝ) : uR (-t) = uR t := by
  by_cases ht : t = 0
  · simp [ht]
  · rw [uR_eq ht, uR_eq (neg_ne_zero.mpr ht), Freal_neg]

/-- `u_r(t) ≤ -log(1+t²) ≤ 0` (`ct:outer` (1), from `mat:T4`(f)(M2)). -/
lemma uR_le (t : ℝ) : uR t ≤ -Real.log (1 + t ^ 2) := by
  by_cases ht : t = 0
  · simp [ht, uR_zero]
  rw [uR_eq ht]
  have hF := Freal_pos ht
  have hb := (Freal_bounds ht).2
  have h1 : 0 < 1 + t ^ 2 := by positivity
  have := Real.log_le_log hF hb
  rw [one_div, Real.log_inv, Real.log_pow] at this
  push_cast at this
  linarith

lemma uR_nonpos (t : ℝ) : uR t ≤ 0 := by
  refine (uR_le t).trans ?_
  have : 0 ≤ Real.log (1 + t ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg t])
  linarith

lemma uR_ge (t : ℝ) : (1 / 2) * Real.log (6 / π ^ 2) - Real.log (1 + t ^ 2) ≤ uR t := by
  by_cases ht : t = 0
  · simp only [ht, uR_zero]
    have : Real.log (6 / π ^ 2) ≤ 0 := by
      apply Real.log_nonpos (by positivity)
      rw [div_le_one (by positivity)]
      nlinarith [Real.pi_gt_three]
    simp
    linarith
  rw [uR_eq ht]
  have hb := (Freal_bounds ht).1
  have h1 : 0 < 1 + t ^ 2 := by positivity
  have hpos : 0 < 6 / π ^ 2 / (1 + t ^ 2) ^ 2 := by
    have := Real.pi_pos; positivity
  have := Real.log_le_log hpos hb
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow] at this
  push_cast at this
  linarith

/-- `|u_r(t)| ≤ log(1+t²) + C₀` with `C₀ = |log(6/π²)|/2`. -/
lemma abs_uR_le (t : ℝ) : |uR t| ≤ Real.log (1 + t ^ 2) + |Real.log (6 / π ^ 2)| / 2 := by
  have h1 := uR_le t
  have h2 := uR_ge t
  have h0 : 0 ≤ Real.log (1 + t ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg t])
  have h3 : -|Real.log (6 / π ^ 2)| ≤ Real.log (6 / π ^ 2) := neg_abs_le _
  rw [abs_le]
  constructor <;> linarith

/-! ### Complex extension and local holomorphy -/

/-- Complex version of `6/π² · m'(z)/(z(1+z²))`. -/
noncomputable def Ftil (z : ℂ) : ℂ :=
  6 / (π : ℂ) ^ 2 * (1 / z - π / Complex.sinh (π * z)) / (z * (1 + z ^ 2))

lemma Ftil_ofReal (t : ℝ) : Ftil (t : ℂ) = (Freal t : ℂ) := by
  unfold Ftil Freal mPrime
  push_cast
  ring_nf

/-- The principal logarithm, halved. -/
noncomputable def utilde (z : ℂ) : ℂ := (1 / 2) * Complex.log (Ftil z)

lemma utilde_ofReal (t : ℝ) : utilde (t : ℂ) = (uR t : ℂ) := by
  by_cases ht : t = 0
  · subst ht; simp [utilde, Ftil, uR_zero]
  rw [utilde, Ftil_ofReal, uR_eq ht]
  push_cast
  rw [Complex.ofReal_log (Freal_pos ht).le]

/-- Local holomorphic extension of `u_r` near a nonzero real point. -/
lemma exists_holo_uR_ne {y₀ : ℝ} (hy : y₀ ≠ 0) :
    ∃ r > 0, DifferentiableOn ℂ utilde (ball (y₀ : ℂ) r) := by
  let V : Set ℂ := {z | z ≠ 0 ∧ Complex.sinh (π * z) ≠ 0 ∧ 1 + z ^ 2 ≠ 0}
  have hVopen : IsOpen V := by
    have h1 : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
    have h2 : IsOpen {z : ℂ | Complex.sinh (π * z) ≠ 0} :=
      isOpen_ne_fun (by fun_prop) continuous_const
    have h3 : IsOpen {z : ℂ | 1 + z ^ 2 ≠ 0} := isOpen_ne_fun (by fun_prop) continuous_const
    exact h1.inter (h2.inter h3)
  have hFd : ∀ z ∈ V, DifferentiableAt ℂ Ftil z := by
    rintro z ⟨h1, h2, h3⟩
    unfold Ftil
    have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have hs : DifferentiableAt ℂ (fun z : ℂ => Complex.sinh (π * z)) z := by fun_prop
    have hA : DifferentiableAt ℂ (fun z : ℂ => 1 / z - π / Complex.sinh (π * z)) z :=
      (differentiableAt_const _ |>.div differentiableAt_id h1).sub
        ((differentiableAt_const _).div hs h2)
    have hB : DifferentiableAt ℂ (fun z : ℂ => z * (1 + z ^ 2)) z := by fun_prop
    exact ((differentiableAt_const _).mul hA).div hB (mul_ne_zero h1 h3)
  have hFc : ContinuousOn Ftil V := fun z hz => (hFd z hz).continuousAt.continuousWithinAt
  have hW : IsOpen (V ∩ Ftil ⁻¹' slitPlane) := hFc.isOpen_inter_preimage hVopen isOpen_slitPlane
  have hy0 : (y₀ : ℂ) ∈ V ∩ Ftil ⁻¹' slitPlane := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · exact_mod_cast hy
    · have : (π : ℂ) * (y₀ : ℂ) = ((π * y₀ : ℝ) : ℂ) := by push_cast; ring
      rw [this, ← Complex.ofReal_sinh]
      exact_mod_cast (Real.sinh_eq_zero.not.mpr (mul_ne_zero Real.pi_pos.ne' hy))
    · have : 1 + (y₀ : ℂ) ^ 2 = ((1 + y₀ ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [this]
      exact_mod_cast (by positivity : (1 + y₀ ^ 2 : ℝ) ≠ 0)
    · show Ftil (y₀ : ℂ) ∈ slitPlane
      rw [Ftil_ofReal]
      exact Or.inl (by simpa using Freal_pos hy)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hW _ hy0
  refine ⟨r, hr, fun z hz => ?_⟩
  obtain ⟨hzV, hzs⟩ := hball hz
  exact ((hFd z hzV).clog hzs).const_mul (1 / 2) |>.differentiableWithinAt

/-- Holomorphic extension of `u_r` near `0`, as a sum of three principal logarithms of factors with
positive real part (`6(sinh πz - πz)/(πz)³`, `πz/sinh πz`, `1/(1+z²)`). -/
noncomputable def utilde0 (z : ℂ) : ℂ :=
  (1 / 2) * (Complex.log (6 * sinhT (π * z)) - Complex.log (sinhQ (π * z)) - Complex.log (1 + z ^ 2))

lemma norm_pi_mul_le {z : ℂ} (hz : ‖z‖ < 3 / 5) : ‖(π : ℂ) * z‖ ≤ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have := Real.pi_lt_d2
  nlinarith [norm_nonneg z]

lemma re_one_add_sq_pos {z : ℂ} (hz : ‖z‖ < 3 / 5) : 0 < (1 + z ^ 2).re := by
  have h1 : ‖z ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg z]
  have h2 : |(z ^ 2).re| ≤ ‖z ^ 2‖ := Complex.abs_re_le_norm _
  have := (abs_le.mp h2).1
  simp only [Complex.add_re, Complex.one_re]
  linarith

lemma differentiableOn_utilde0 : DifferentiableOn ℂ utilde0 (ball (0 : ℂ) (3 / 5)) := by
  intro z hz
  have hz' : ‖z‖ < 3 / 5 := mem_ball_zero_iff.mp hz
  have hw := norm_pi_mul_le hz'
  have h1 : (6 * sinhT (π * z)) ∈ slitPlane := Or.inl (re_six_sinhT_pos hw)
  have h2 : sinhQ (π * z) ∈ slitPlane := Or.inl (re_sinhQ_pos hw)
  have h3 : (1 + z ^ 2) ∈ slitPlane := Or.inl (re_one_add_sq_pos hz')
  have d1 : DifferentiableAt ℂ (fun z : ℂ => sinhT ((π : ℂ) * z)) z :=
    (differentiable_sinhT.differentiableAt).comp z (by fun_prop)
  have d2 : DifferentiableAt ℂ (fun z : ℂ => sinhQ ((π : ℂ) * z)) z :=
    (differentiable_sinhQ.differentiableAt).comp z (by fun_prop)
  have l1 := ((d1.const_mul (6 : ℂ)).clog h1)
  have l2 := d2.clog h2
  have l3 := ((by fun_prop : DifferentiableAt ℂ (fun z : ℂ => 1 + z ^ 2) z).clog h3)
  exact (((l1.sub l2).sub l3).const_mul (1 / 2)).differentiableWithinAt

/-- On the real points of `B(0, 3/5)`, `utilde0` is `u_r`. -/
lemma utilde0_ofReal {t : ℝ} (ht : |t| < 3 / 5) : utilde0 (t : ℂ) = (uR t : ℂ) := by
  wlog hpos : 0 ≤ t generalizing t
  · have h := this (t := -t) (by rwa [abs_neg]) (by linarith [not_le.mp hpos])
    have e : utilde0 ((-t : ℝ) : ℂ) = utilde0 (t : ℂ) := by
      unfold utilde0
      push_cast
      rw [mul_neg, sinhT_neg, sinhQ_neg, neg_sq]
    rw [e, uR_neg] at h
    exact h
  rcases hpos.eq_or_lt with h0 | hpos
  · subst h0
    simp [utilde0, sinhT_zero, sinhQ_zero, uR_zero]
  have hx : π * t ≠ 0 := by have := Real.pi_pos; positivity
  have hx0 : 0 < π * t := by have := Real.pi_pos; positivity
  have hQ := sinhQ_ofReal hx
  have hT := sinhT_ofReal hx
  have hS : 0 < Real.sinh (π * t) := Real.sinh_pos_iff.mpr hx0
  have hSx : π * t < Real.sinh (π * t) := FormalResearch.CohnElkies.sinh_gt_id hx0
  have hQpos : 0 < Real.sinh (π * t) / (π * t) := div_pos hS hx0
  have hTpos : 0 < (Real.sinh (π * t) - π * t) / (π * t) ^ 3 := div_pos (by linarith) (by positivity)
  have e : (π : ℂ) * (t : ℂ) = ((π * t : ℝ) : ℂ) := by push_cast; ring
  unfold utilde0
  rw [e, hQ, hT]
  have h1 : (6 : ℂ) * (((Real.sinh (π * t) - π * t) / (π * t) ^ 3 : ℝ) : ℂ) =
      ((6 * ((Real.sinh (π * t) - π * t) / (π * t) ^ 3) : ℝ) : ℂ) := by push_cast; ring
  have h2 : (1 : ℂ) + (t : ℂ) ^ 2 = ((1 + t ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, ← Complex.ofReal_log (by positivity), ← Complex.ofReal_log hQpos.le,
    ← Complex.ofReal_log (by positivity)]
  have hF : Freal t = 6 * ((Real.sinh (π * t) - π * t) / (π * t) ^ 3) /
      (Real.sinh (π * t) / (π * t) * (1 + t ^ 2)) := by
    unfold Freal mPrime
    have hpi := Real.pi_pos
    field_simp
  have key : uR t = 1 / 2 * (Real.log (6 * ((Real.sinh (π * t) - π * t) / (π * t) ^ 3)) -
      Real.log (Real.sinh (π * t) / (π * t)) - Real.log (1 + t ^ 2)) := by
    have hc : 0 < 1 + t ^ 2 := by positivity
    have ha : 0 < 6 * ((Real.sinh (π * t) - π * t) / (π * t) ^ 3) := by positivity
    rw [uR_eq hpos.ne', hF, Real.log_div ha.ne' (mul_pos hQpos hc).ne',
      Real.log_mul hQpos.ne' hc.ne']
    ring
  rw [key]
  push_cast
  ring

/-- Local holomorphic extension of `u_r` at every real point: there are a radius `r > 0` and a
holomorphic function `v` on `B(y₀, r)` with `v t = u_r(t)` for real `t` with `|t - y₀| < r`. -/
lemma exists_holo_uR (y₀ : ℝ) :
    ∃ r > 0, ∃ v : ℂ → ℂ, DifferentiableOn ℂ v (ball (y₀ : ℂ) r) ∧
      ∀ t : ℝ, |t - y₀| < r → v (t : ℂ) = (uR t : ℂ) := by
  by_cases hy : y₀ = 0
  · subst hy
    refine ⟨3 / 5, by norm_num, utilde0, by simpa using differentiableOn_utilde0, fun t ht => ?_⟩
    exact utilde0_ofReal (by simpa using ht)
  · obtain ⟨r, hr, hd⟩ := exists_holo_uR_ne hy
    exact ⟨r, hr, utilde, hd, fun t _ => utilde_ofReal t⟩

lemma continuous_uR : Continuous uR := by
  rw [continuous_iff_continuousAt]
  intro y₀
  obtain ⟨r, hr, v, hv, hvu⟩ := exists_holo_uR y₀
  have hc : ContinuousAt (fun t : ℝ => (v (t : ℂ)).re) y₀ := by
    have h1 : ContinuousAt v (y₀ : ℂ) :=
      (hv (y₀ : ℂ) (mem_ball_self hr)).continuousWithinAt.continuousAt (ball_mem_nhds _ hr)
    exact Complex.continuous_re.continuousAt.comp (h1.comp Complex.continuous_ofReal.continuousAt)
  refine hc.congr ?_
  have : ∀ᶠ t in 𝓝 y₀, |t - y₀| < r := by
    have := Metric.ball_mem_nhds y₀ hr
    filter_upwards [this] with t ht using by simpa [Real.dist_eq] using ht
  filter_upwards [this] with t ht
  simp [hvu t ht]

end FormalResearch.SignUncertainty.CtOuter
