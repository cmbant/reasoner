module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Lemma `O.4(2)`: the Banach contraction for the cubic normal form (`u1co:O4`)

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, proof of Lemma O.4(2), steps
"Reduction to a fixed point" and "Contraction".

The paper seeks `τ = σ₀ θ (1 + (θ² - θ₀²) η(θ))` solving `Φ_L(τ(θ)) = Φ_mod(θ)`; with
`p = θ² - θ₀²` and the even function `F(θ) = (Φ̂ - Φ_mod)/(θ (θ² - θ₀²)²)` the equation becomes
`η = 𝒯(η)` with
`𝒯(η) = (12/π²)(1 + pη)(1 + 2θ²η + θ²pη²)² F(θ(1 + pη)) - θ²η² - θ²pη³/3`.

**What is proved here (unconditional, abstract `F`).** `𝒯` acts pointwise in `θ` (it is `θ ↦ G(θ, η θ)`),
and for a holomorphic `F` on `D(0, 0.25)` with the named hypothesis `‖F‖ ≤ 0.13` there and
`0 ≤ θ₀² ≤ 0.00244`, `G(θ, ·)` maps `closedBall 0 (1/5)` into itself and is `1/2`-Lipschitz for every
`‖θ‖ < 0.22`. Banach's theorem gives a unique pointwise fixed point `η(θ)` of norm `≤ 1/5`; it is the
uniform limit of the Picard iterates, which are holomorphic, so `η` is holomorphic on `D(0, 0.22)`
(`o4_fixed_point`). The paper's sharper constants (`‖𝒯‖ < 0.168`, `λ < 0.127`, `‖η‖ < 0.181`) are not
needed: the weaker `1/5`, `1/2` suffice for `|H| ≤ 1/4`, see the docstring of `o4_fixed_point`.

**Not proved here.** The bound `M_F = sup |F| ≤ 0.13` (`[O4C (B)]`) is the hypothesis `hFb` of the abstract `F`; for the paper's `F`
it is proved separately (`SignUncertainty.o4QuotientBound`), and connecting `F` to the edge phase `Φ_L` (the removable singularities of
the quotient) is done in `CubicNormalFormBridge`.
-/

@[expose] public section

open Metric Set Filter Topology
open scoped Real

namespace FormalResearch.CohnElkies

/-- The pointwise map `G(θ, e)` of the fixed-point equation `η = 𝒯(η)` of `u1co:O4` (`θ0sq = θ₀²`). -/
noncomputable def o4G (θ0sq : ℝ) (F : ℂ → ℂ) (θ e : ℂ) : ℂ :=
  ((12 / π ^ 2 : ℝ) : ℂ) * ((1 + (θ ^ 2 - θ0sq) * e) *
      (1 + 2 * θ ^ 2 * e + θ ^ 2 * (θ ^ 2 - θ0sq) * e ^ 2) ^ 2 * F (θ * (1 + (θ ^ 2 - θ0sq) * e)))
    - θ ^ 2 * e ^ 2 - θ ^ 2 * (θ ^ 2 - θ0sq) * e ^ 3 / 3

section bounds

variable {θ0sq : ℝ} {θ e : ℂ}

/-- Norm bounds for the polynomial factors on `‖θ‖ < 0.22`, `‖e‖ ≤ 1/5`, `0 ≤ θ₀² ≤ 0.00244`. -/
lemma o4_bounds (h0 : 0 ≤ θ0sq) (h1 : θ0sq ≤ 0.00244) (hθ : ‖θ‖ < 0.22) (he : ‖e‖ ≤ 1 / 5) :
    ‖θ ^ 2‖ ≤ 0.0484 ∧ ‖θ ^ 2 - θ0sq‖ ≤ 0.0509 ∧ ‖1 + (θ ^ 2 - θ0sq) * e‖ ≤ 1.0102 ∧
      ‖1 + 2 * θ ^ 2 * e + θ ^ 2 * (θ ^ 2 - θ0sq) * e ^ 2‖ ≤ 1.0196 ∧
      ‖2 * θ ^ 2 + 2 * θ ^ 2 * (θ ^ 2 - θ0sq) * e‖ ≤ 0.0978 ∧
      ‖θ * (1 + (θ ^ 2 - θ0sq) * e)‖ ≤ 0.2223 := by
  have ha : 0 ≤ ‖θ‖ := norm_nonneg _
  have hE : 0 ≤ ‖e‖ := norm_nonneg _
  have h2 : ‖θ ^ 2‖ ≤ 0.0484 := by
    rw [norm_pow]; nlinarith
  have hp : ‖θ ^ 2 - θ0sq‖ ≤ 0.0509 := by
    calc ‖θ ^ 2 - θ0sq‖ ≤ ‖θ ^ 2‖ + ‖(θ0sq : ℂ)‖ := norm_sub_le _ _
      _ ≤ 0.0484 + 0.00244 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]; linarith
      _ ≤ 0.0509 := by norm_num
  have hpe : ‖(θ ^ 2 - θ0sq) * e‖ ≤ 0.0509 * (1 / 5) := by
    rw [norm_mul]; exact mul_le_mul hp he hE (by norm_num)
  have hq1 : ‖1 + (θ ^ 2 - θ0sq) * e‖ ≤ 1.0102 := by
    calc ‖1 + (θ ^ 2 - θ0sq) * e‖ ≤ ‖(1 : ℂ)‖ + ‖(θ ^ 2 - θ0sq) * e‖ := norm_add_le _ _
      _ ≤ 1 + 0.0509 * (1 / 5) := by rw [norm_one]; linarith
      _ ≤ 1.0102 := by norm_num
  have hQ : ‖1 + 2 * θ ^ 2 * e + θ ^ 2 * (θ ^ 2 - θ0sq) * e ^ 2‖ ≤ 1.0196 := by
    have t1 : ‖2 * θ ^ 2 * e‖ ≤ 2 * 0.0484 * (1 / 5) := by
      rw [norm_mul, norm_mul]
      have : ‖(2 : ℂ)‖ = 2 := by simp
      rw [this]; gcongr
    have t2 : ‖θ ^ 2 * (θ ^ 2 - θ0sq) * e ^ 2‖ ≤ 0.0484 * 0.0509 * (1 / 5) ^ 2 := by
      rw [norm_mul, norm_mul, norm_pow e]; gcongr
    calc ‖1 + 2 * θ ^ 2 * e + θ ^ 2 * (θ ^ 2 - θ0sq) * e ^ 2‖
        ≤ ‖1 + 2 * θ ^ 2 * e‖ + ‖θ ^ 2 * (θ ^ 2 - θ0sq) * e ^ 2‖ := norm_add_le _ _
      _ ≤ (‖(1 : ℂ)‖ + ‖2 * θ ^ 2 * e‖) + ‖θ ^ 2 * (θ ^ 2 - θ0sq) * e ^ 2‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ 1.0196 := by rw [norm_one]; nlinarith
  have hQ' : ‖2 * θ ^ 2 + 2 * θ ^ 2 * (θ ^ 2 - θ0sq) * e‖ ≤ 0.0978 := by
    have t1 : ‖2 * θ ^ 2‖ ≤ 2 * 0.0484 := by
      rw [norm_mul]; have : ‖(2 : ℂ)‖ = 2 := by simp
      rw [this]; gcongr
    have t2 : ‖2 * θ ^ 2 * (θ ^ 2 - θ0sq) * e‖ ≤ 2 * 0.0484 * (0.0509 * (1 / 5)) := by
      have : 2 * θ ^ 2 * (θ ^ 2 - θ0sq) * e = 2 * θ ^ 2 * ((θ ^ 2 - θ0sq) * e) := by ring
      rw [this, norm_mul, norm_mul]
      have h2' : ‖(2 : ℂ)‖ = 2 := by simp
      rw [h2']; gcongr
    calc _ ≤ ‖2 * θ ^ 2‖ + ‖2 * θ ^ 2 * (θ ^ 2 - θ0sq) * e‖ := norm_add_le _ _
      _ ≤ 0.0978 := by nlinarith
  have hw : ‖θ * (1 + (θ ^ 2 - θ0sq) * e)‖ ≤ 0.2223 := by
    rw [norm_mul]
    calc ‖θ‖ * ‖1 + (θ ^ 2 - θ0sq) * e‖ ≤ 0.22 * 1.0102 := mul_le_mul hθ.le hq1 (norm_nonneg _) (by norm_num)
      _ ≤ 0.2223 := by norm_num
  exact ⟨h2, hp, hq1, hQ, hQ', hw⟩

end bounds

section dynamics

variable {θ0sq : ℝ} {F : ℂ → ℂ} {θ e : ℂ}

lemma norm_twelve_div_pi_sq : ‖(((12 / π ^ 2 : ℝ)) : ℂ)‖ ≤ 1.22 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h : (3.14 : ℝ) < π := Real.pi_gt_d2
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- `G(θ, ·)` maps `closedBall 0 (1/5)` into itself (the paper's `‖𝒯(η)‖ < 0.168`, here `≤ 0.17`). -/
lemma o4G_norm_le (h0 : 0 ≤ θ0sq) (h1 : θ0sq ≤ 0.00244) (hθ : ‖θ‖ < 0.22) (he : ‖e‖ ≤ 1 / 5)
    (hFb : ∀ z ∈ ball (0 : ℂ) 0.25, ‖F z‖ ≤ 0.13) :
    ‖o4G θ0sq F θ e‖ ≤ 0.17 := by
  obtain ⟨h2, hp, hq1, hQ, hQ', hw⟩ := o4_bounds h0 h1 hθ he
  have hFw : ‖F (θ * (1 + (θ ^ 2 - θ0sq) * e))‖ ≤ 0.13 :=
    hFb _ (by rw [mem_ball_zero_iff]; linarith)
  have hc := norm_twelve_div_pi_sq
  unfold o4G
  have t1 : ‖((12 / π ^ 2 : ℝ) : ℂ) * ((1 + (θ ^ 2 - θ0sq) * e) *
      (1 + 2 * θ ^ 2 * e + θ ^ 2 * (θ ^ 2 - θ0sq) * e ^ 2) ^ 2 * F (θ * (1 + (θ ^ 2 - θ0sq) * e)))‖
      ≤ 1.22 * (1.0102 * 1.0196 ^ 2 * 0.13) := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow]
    gcongr
  have t2 : ‖θ ^ 2 * e ^ 2‖ ≤ 0.0484 * (1 / 5) ^ 2 := by
    rw [norm_mul, norm_pow e]; gcongr
  have t3 : ‖θ ^ 2 * (θ ^ 2 - θ0sq) * e ^ 3 / 3‖ ≤ 0.0484 * 0.0509 * (1 / 5) ^ 3 / 3 := by
    rw [norm_div, norm_mul, norm_mul, norm_pow e]
    have : ‖(3 : ℂ)‖ = 3 := by simp
    rw [this]; gcongr
  calc _ ≤ ‖((12 / π ^ 2 : ℝ) : ℂ) * ((1 + (θ ^ 2 - θ0sq) * e) *
      (1 + 2 * θ ^ 2 * e + θ ^ 2 * (θ ^ 2 - θ0sq) * e ^ 2) ^ 2 * F (θ * (1 + (θ ^ 2 - θ0sq) * e)))‖
      + ‖θ ^ 2 * e ^ 2‖ + ‖θ ^ 2 * (θ ^ 2 - θ0sq) * e ^ 3 / 3‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ 0.17 := by nlinarith

/-- Derivative of `e ↦ G(θ, e)` at a point where `F` is differentiable at `θ(1 + pe)`. -/
lemma o4G_hasDerivAt (hF : DifferentiableAt ℂ F (θ * (1 + (θ ^ 2 - θ0sq) * e))) :
    HasDerivAt (o4G θ0sq F θ)
      (((12 / π ^ 2 : ℝ) : ℂ) *
        ((θ ^ 2 - θ0sq) * (1 + 2 * θ ^ 2 * e + θ ^ 2 * (θ ^ 2 - θ0sq) * e ^ 2) ^ 2
            * F (θ * (1 + (θ ^ 2 - θ0sq) * e))
          + (1 + (θ ^ 2 - θ0sq) * e) * (2 * (1 + 2 * θ ^ 2 * e + θ ^ 2 * (θ ^ 2 - θ0sq) * e ^ 2)
              * (2 * θ ^ 2 + 2 * θ ^ 2 * (θ ^ 2 - θ0sq) * e)) * F (θ * (1 + (θ ^ 2 - θ0sq) * e))
          + (1 + (θ ^ 2 - θ0sq) * e) * (1 + 2 * θ ^ 2 * e + θ ^ 2 * (θ ^ 2 - θ0sq) * e ^ 2) ^ 2
              * (deriv F (θ * (1 + (θ ^ 2 - θ0sq) * e)) * (θ * (θ ^ 2 - θ0sq))))
        - 2 * θ ^ 2 * e - θ ^ 2 * (θ ^ 2 - θ0sq) * e ^ 2) e := by
  set p : ℂ := θ ^ 2 - θ0sq with hp
  have hid : HasDerivAt (fun x : ℂ => x) 1 e := hasDerivAt_id e
  have hA : HasDerivAt (fun x : ℂ => 1 + p * x) p e := by
    simpa using (hid.const_mul p).const_add 1
  have hQ : HasDerivAt (fun x : ℂ => 1 + 2 * θ ^ 2 * x + θ ^ 2 * p * x ^ 2)
      (2 * θ ^ 2 + 2 * θ ^ 2 * p * e) e := by
    have h1 : HasDerivAt (fun x : ℂ => 2 * θ ^ 2 * x) (2 * θ ^ 2) e := by
      simpa using hid.const_mul (2 * θ ^ 2)
    have h2 : HasDerivAt (fun x : ℂ => θ ^ 2 * p * x ^ 2) (θ ^ 2 * p * (2 * e)) e := by
      simpa using (hid.pow 2).const_mul (θ ^ 2 * p)
    convert (h1.const_add 1).add h2 using 1
    ring
  have hB := hQ.pow 2
  have hw : HasDerivAt (fun x : ℂ => θ * (1 + p * x)) (θ * p) e := by
    simpa using hA.const_mul θ
  have hFw : HasDerivAt (fun x : ℂ => F (θ * (1 + p * x))) (deriv F (θ * (1 + p * e)) * (θ * p)) e :=
    (hF.hasDerivAt).comp e hw
  have hP := ((hA.mul hB).mul hFw).const_mul (((12 / π ^ 2 : ℝ)) : ℂ)
  have hS1 : HasDerivAt (fun x : ℂ => θ ^ 2 * x ^ 2) (θ ^ 2 * (2 * e)) e := by
    simpa using (hid.pow 2).const_mul (θ ^ 2)
  have hS2 : HasDerivAt (fun x : ℂ => θ ^ 2 * p * x ^ 3 / 3) (θ ^ 2 * p * (3 * e ^ 2) / 3) e := by
    simpa using ((hid.pow 3).const_mul (θ ^ 2 * p)).div_const 3
  have := (hP.sub hS1).sub hS2
  unfold o4G
  convert this using 1
  simp only [Pi.pow_apply, Pi.mul_apply, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  ring

/-- Abstract norm bound for the derivative expression, in terms of its atoms. -/
lemma o4_deriv_atoms_le (c p t A Q Q' e θ FW D : ℂ) (hc : ‖c‖ ≤ 1.22) (hp : ‖p‖ ≤ 0.0509)
    (ht : ‖t‖ ≤ 0.0484) (hA : ‖A‖ ≤ 1.0102) (hQ : ‖Q‖ ≤ 1.0196) (hQ' : ‖Q'‖ ≤ 0.0978)
    (he : ‖e‖ ≤ 1 / 5) (hθ : ‖θ‖ ≤ 0.22) (hFW : ‖FW‖ ≤ 0.13) (hD : ‖D‖ ≤ 0.13 / 0.0275) :
    ‖c * (p * Q ^ 2 * FW + A * (2 * Q * Q') * FW + A * Q ^ 2 * (D * (θ * p)))
        - 2 * t * e - t * p * e ^ 2‖ ≤ 1 / 2 := by
  have h2' : ‖(2 : ℂ)‖ = 2 := by simp
  have u1 : ‖p * Q ^ 2 * FW‖ ≤ 0.0509 * 1.0196 ^ 2 * 0.13 := by
    rw [norm_mul, norm_mul, norm_pow]; gcongr
  have u2 : ‖A * (2 * Q * Q') * FW‖ ≤ 1.0102 * (2 * 1.0196 * 0.0978) * 0.13 := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, h2']; gcongr
  have u3 : ‖A * Q ^ 2 * (D * (θ * p))‖ ≤ 1.0102 * 1.0196 ^ 2 * (0.13 / 0.0275 * (0.22 * 0.0509)) := by
    rw [norm_mul, norm_mul, norm_pow, norm_mul, norm_mul]; gcongr
  have u4 : ‖2 * t * e‖ ≤ 2 * 0.0484 * (1 / 5) := by
    rw [norm_mul, norm_mul, h2']; gcongr
  have u5 : ‖t * p * e ^ 2‖ ≤ 0.0484 * 0.0509 * (1 / 5) ^ 2 := by
    rw [norm_mul, norm_mul, norm_pow e]; gcongr
  have hS : ‖p * Q ^ 2 * FW + A * (2 * Q * Q') * FW + A * Q ^ 2 * (D * (θ * p))‖
      ≤ 0.0509 * 1.0196 ^ 2 * 0.13 + 1.0102 * (2 * 1.0196 * 0.0978) * 0.13
        + 1.0102 * 1.0196 ^ 2 * (0.13 / 0.0275 * (0.22 * 0.0509)) :=
    ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add u1 u2)) u3))
  have hM : ‖c * (p * Q ^ 2 * FW + A * (2 * Q * Q') * FW + A * Q ^ 2 * (D * (θ * p)))‖
      ≤ 1.22 * (0.0509 * 1.0196 ^ 2 * 0.13 + 1.0102 * (2 * 1.0196 * 0.0978) * 0.13
        + 1.0102 * 1.0196 ^ 2 * (0.13 / 0.0275 * (0.22 * 0.0509))) := by
    rw [norm_mul]; exact mul_le_mul hc hS (norm_nonneg _) (by norm_num)
  calc _ ≤ ‖c * (p * Q ^ 2 * FW + A * (2 * Q * Q') * FW + A * Q ^ 2 * (D * (θ * p))) - 2 * t * e‖
        + ‖t * p * e ^ 2‖ := norm_sub_le _ _
    _ ≤ (‖c * (p * Q ^ 2 * FW + A * (2 * Q * Q') * FW + A * Q ^ 2 * (D * (θ * p)))‖ + ‖2 * t * e‖)
        + ‖t * p * e ^ 2‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ 1 / 2 := by nlinarith

/-- Norm bound of the derivative expression: `≤ 1/2` (the paper has `λ < 0.127`). -/
lemma o4_deriv_expr_le (h0 : 0 ≤ θ0sq) (h1 : θ0sq ≤ 0.00244) (hθ : ‖θ‖ < 0.22) (he : ‖e‖ ≤ 1 / 5)
    (FW D : ℂ) (hFW : ‖FW‖ ≤ 0.13) (hD : ‖D‖ ≤ 0.13 / 0.0275) :
    ‖((12 / π ^ 2 : ℝ) : ℂ) *
        ((θ ^ 2 - θ0sq) * (1 + 2 * θ ^ 2 * e + θ ^ 2 * (θ ^ 2 - θ0sq) * e ^ 2) ^ 2 * FW
          + (1 + (θ ^ 2 - θ0sq) * e) * (2 * (1 + 2 * θ ^ 2 * e + θ ^ 2 * (θ ^ 2 - θ0sq) * e ^ 2)
              * (2 * θ ^ 2 + 2 * θ ^ 2 * (θ ^ 2 - θ0sq) * e)) * FW
          + (1 + (θ ^ 2 - θ0sq) * e) * (1 + 2 * θ ^ 2 * e + θ ^ 2 * (θ ^ 2 - θ0sq) * e ^ 2) ^ 2
              * (D * (θ * (θ ^ 2 - θ0sq))))
        - 2 * θ ^ 2 * e - θ ^ 2 * (θ ^ 2 - θ0sq) * e ^ 2‖ ≤ 1 / 2 := by
  obtain ⟨h2, hp, hq1, hQ, hQ', hw⟩ := o4_bounds h0 h1 hθ he
  exact o4_deriv_atoms_le _ _ _ _ _ _ _ _ _ _ norm_twelve_div_pi_sq hp h2 hq1 hQ hQ' he hθ.le hFW hD

/-- Cauchy estimate for `F'` on `‖w‖ ≤ 0.2223` (radius `0.0275` stays inside `D(0, 0.25)`). -/
lemma o4_deriv_F_le (hFd : DifferentiableOn ℂ F (ball 0 0.25))
    (hFb : ∀ z ∈ ball (0 : ℂ) 0.25, ‖F z‖ ≤ 0.13) {w : ℂ} (hw : ‖w‖ ≤ 0.2223) :
    ‖deriv F w‖ ≤ 0.13 / 0.0275 := by
  have hsub : closedBall w 0.0275 ⊆ ball (0 : ℂ) 0.25 := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [mem_ball_zero_iff]
    calc ‖z‖ = ‖(z - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
      _ < 0.25 := by linarith
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num)
    (hFd.diffContOnCl_ball hsub) fun z hz => hFb z (hsub (sphere_subset_closedBall hz))

/-- `G(θ, ·)` is `1/2`-Lipschitz on `closedBall 0 (1/5)` (the paper has `λ < 0.127`). -/
lemma o4G_lip (h0 : 0 ≤ θ0sq) (h1 : θ0sq ≤ 0.00244) (hθ : ‖θ‖ < 0.22)
    (hFd : DifferentiableOn ℂ F (ball 0 0.25)) (hFb : ∀ z ∈ ball (0 : ℂ) 0.25, ‖F z‖ ≤ 0.13)
    {e₁ e₂ : ℂ} (h₁ : ‖e₁‖ ≤ 1 / 5) (h₂ : ‖e₂‖ ≤ 1 / 5) :
    ‖o4G θ0sq F θ e₁ - o4G θ0sq F θ e₂‖ ≤ 1 / 2 * ‖e₁ - e₂‖ := by
  have hmem : ∀ x ∈ closedBall (0 : ℂ) (1 / 5), ‖θ * (1 + (θ ^ 2 - θ0sq) * x)‖ ≤ 0.2223 := fun x hx =>
    (o4_bounds h0 h1 hθ (by simpa using hx)).2.2.2.2.2
  have key := (convex_closedBall (0 : ℂ) (1 / 5)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := o4G θ0sq F θ) (C := 1 / 2)
    (f' := fun x => ((12 / π ^ 2 : ℝ) : ℂ) *
        ((θ ^ 2 - θ0sq) * (1 + 2 * θ ^ 2 * x + θ ^ 2 * (θ ^ 2 - θ0sq) * x ^ 2) ^ 2
            * F (θ * (1 + (θ ^ 2 - θ0sq) * x))
          + (1 + (θ ^ 2 - θ0sq) * x) * (2 * (1 + 2 * θ ^ 2 * x + θ ^ 2 * (θ ^ 2 - θ0sq) * x ^ 2)
              * (2 * θ ^ 2 + 2 * θ ^ 2 * (θ ^ 2 - θ0sq) * x)) * F (θ * (1 + (θ ^ 2 - θ0sq) * x))
          + (1 + (θ ^ 2 - θ0sq) * x) * (1 + 2 * θ ^ 2 * x + θ ^ 2 * (θ ^ 2 - θ0sq) * x ^ 2) ^ 2
              * (deriv F (θ * (1 + (θ ^ 2 - θ0sq) * x)) * (θ * (θ ^ 2 - θ0sq))))
        - 2 * θ ^ 2 * x - θ ^ 2 * (θ ^ 2 - θ0sq) * x ^ 2)
    (fun x hx => (o4G_hasDerivAt (hFd.differentiableAt (isOpen_ball.mem_nhds
      (by rw [mem_ball_zero_iff]; linarith [hmem x hx])))).hasDerivWithinAt)
    (fun x hx => o4_deriv_expr_le h0 h1 hθ (by simpa using hx) _ _
      (hFb _ (by rw [mem_ball_zero_iff]; linarith [hmem x hx])) (o4_deriv_F_le hFd hFb (hmem x hx)))
    (x := e₂) (y := e₁) (by simpa using h₂) (by simpa using h₁)
  simpa using key

lemma differentiableOn_o4G (h0 : 0 ≤ θ0sq) (h1 : θ0sq ≤ 0.00244)
    (hFd : DifferentiableOn ℂ F (ball 0 0.25)) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 0.22)) (hgb : ∀ θ ∈ ball (0 : ℂ) 0.22, ‖g θ‖ ≤ 1 / 5) :
    DifferentiableOn ℂ (fun θ => o4G θ0sq F θ (g θ)) (ball 0 0.22) := by
  set Fc : ℂ → ℂ := fun θ => F (θ * (1 + (θ ^ 2 - θ0sq) * g θ)) with hFc
  have hF' : DifferentiableOn ℂ Fc (ball 0 0.22) :=
    hFd.comp (by fun_prop) fun θ hθ => by
      rw [mem_ball_zero_iff] at hθ ⊢
      linarith [(o4_bounds h0 h1 hθ (hgb θ (by rwa [mem_ball_zero_iff]))).2.2.2.2.2]
  set c : ℂ := ((12 / π ^ 2 : ℝ) : ℂ) with hc
  have hfun : (fun θ => o4G θ0sq F θ (g θ)) = fun θ => c * ((1 + (θ ^ 2 - θ0sq) * g θ) *
      (1 + 2 * θ ^ 2 * g θ + θ ^ 2 * (θ ^ 2 - θ0sq) * g θ ^ 2) ^ 2 * Fc θ)
      - θ ^ 2 * g θ ^ 2 - θ ^ 2 * (θ ^ 2 - θ0sq) * g θ ^ 3 / 3 := rfl
  rw [hfun]
  fun_prop

end dynamics

section fixedpoint

variable {θ0sq : ℝ} {F : ℂ → ℂ}

/-- Pointwise Banach fixed point of `G(θ, ·)` on `closedBall 0 (1/5)`. -/
lemma o4_pointwise_fixedPoint (h0 : 0 ≤ θ0sq) (h1 : θ0sq ≤ 0.00244)
    (hFd : DifferentiableOn ℂ F (ball 0 0.25)) (hFb : ∀ z ∈ ball (0 : ℂ) 0.25, ‖F z‖ ≤ 0.13)
    {θ : ℂ} (hθ : ‖θ‖ < 0.22) :
    ∃ y : ℂ, ‖y‖ ≤ 1 / 5 ∧ y = o4G θ0sq F θ y ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 / 5 → z = o4G θ0sq F θ z → z = y := by
  set s : Set ℂ := closedBall 0 (1 / 5) with hs
  have hmaps : MapsTo (o4G θ0sq F θ) s s := fun x hx => by
    rw [hs, mem_closedBall_zero_iff] at hx ⊢
    exact (o4G_norm_le h0 h1 hθ hx hFb).trans (by norm_num)
  have hcon : ContractingWith (1 / 2 : NNReal) (hmaps.restrict (o4G θ0sq F θ) s s) := by
    refine ⟨by rw [← NNReal.coe_lt_coe]; norm_num,
      LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    have hx : ‖(x : ℂ)‖ ≤ 1 / 5 := by simpa [hs] using x.2
    have hy : ‖(y : ℂ)‖ ≤ 1 / 5 := by simpa [hs] using y.2
    have := o4G_lip h0 h1 hθ hFd hFb hx hy
    simpa [dist_eq_norm, Subtype.dist_eq] using this
  obtain ⟨y, hy, hfix, -, -⟩ := ContractingWith.exists_fixedPoint' (isClosed_closedBall.isComplete)
    hmaps hcon (x := 0) (by simp [hs]) (edist_ne_top _ _)
  refine ⟨y, by simpa [hs] using hy, hfix.symm, fun z hz hzf => ?_⟩
  have hy' : ‖y‖ ≤ 1 / 5 := by simpa [hs] using hy
  have := o4G_lip h0 h1 hθ hFd hFb hz hy'
  rw [← hzf, ← show o4G θ0sq F θ y = y from hfix] at this
  have h2 : ‖z - y‖ ≤ 1 / 2 * ‖z - y‖ := by
    calc ‖z - y‖ = ‖o4G θ0sq F θ z - o4G θ0sq F θ y‖ := by rw [← hzf, hfix]
      _ ≤ _ := o4G_lip h0 h1 hθ hFd hFb hz hy'
  have : ‖z - y‖ = 0 := by linarith [norm_nonneg (z - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- **Lemma `O.4(2)`, fixed-point step (`u1co:O4`)**, for an abstract `F` with `‖F‖ ≤ 0.13` on `D(0, 0.25)`
(the paper's `M_F ≤ 0.13`, `[O4C (B)]`) and `0 ≤ θ₀² ≤ 0.00244`: there is a holomorphic `η` on `D(0, 0.22)`
with `‖η‖ ≤ 1/5`, `η = 𝒯(η)`, unique among functions of norm `≤ 1/5` pointwise.

With `‖η‖ ≤ 1/5` the paper's consequences still hold: `|τ|/σ₀ ≤ 0.22 (1 + 0.0509 / 5) < 0.2223`, and
`|H| ≤ σ₀ ‖η‖ (1 + 2θ₀²/0.0484) ≤ 1.0013 · 0.2 · 1.1008 < 1/4`. -/
theorem o4_fixed_point (h0 : 0 ≤ θ0sq) (h1 : θ0sq ≤ 0.00244)
    (hFd : DifferentiableOn ℂ F (ball 0 0.25)) (hFb : ∀ z ∈ ball (0 : ℂ) 0.25, ‖F z‖ ≤ 0.13) :
    ∃ η : ℂ → ℂ, DifferentiableOn ℂ η (ball 0 0.22) ∧
      (∀ θ ∈ ball (0 : ℂ) 0.22, ‖η θ‖ ≤ 1 / 5 ∧ η θ = o4G θ0sq F θ (η θ)) ∧
      ∀ θ ∈ ball (0 : ℂ) 0.22, ∀ z : ℂ, ‖z‖ ≤ 1 / 5 → z = o4G θ0sq F θ z → z = η θ := by
  have key : ∀ θ : ℂ, ∃ y : ℂ, ‖θ‖ < 0.22 → (‖y‖ ≤ 1 / 5 ∧ y = o4G θ0sq F θ y ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 / 5 → z = o4G θ0sq F θ z → z = y) := fun θ => by
    by_cases hθ : ‖θ‖ < 0.22
    · obtain ⟨y, hy⟩ := o4_pointwise_fixedPoint h0 h1 hFd hFb hθ
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => absurd h hθ⟩
  choose η hη using key
  have hη' : ∀ θ ∈ ball (0 : ℂ) 0.22, ‖η θ‖ ≤ 1 / 5 ∧ η θ = o4G θ0sq F θ (η θ) ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 / 5 → z = o4G θ0sq F θ z → z = η θ := fun θ hθ =>
    hη θ (by simpa using hθ)
  -- Picard iterates
  let ηn : ℕ → ℂ → ℂ := fun n θ => (o4G θ0sq F θ)^[n] 0
  have hiter_norm : ∀ n, ∀ θ ∈ ball (0 : ℂ) 0.22, ‖ηn n θ‖ ≤ 1 / 5 := by
    intro n
    induction n with
    | zero => intro θ _; simp [ηn]
    | succ n ih =>
        intro θ hθ
        have hθ' : ‖θ‖ < 0.22 := by simpa using hθ
        show ‖(o4G θ0sq F θ)^[n + 1] 0‖ ≤ 1 / 5
        rw [Function.iterate_succ_apply']
        exact (o4G_norm_le h0 h1 hθ' (ih θ hθ) hFb).trans (by norm_num)
  have hiter_diff : ∀ n, DifferentiableOn ℂ (ηn n) (ball 0 0.22) := by
    intro n
    induction n with
    | zero => simp [ηn]
    | succ n ih =>
        have := differentiableOn_o4G h0 h1 hFd ih (hiter_norm n)
        refine this.congr fun θ _ => ?_
        show (o4G θ0sq F θ)^[n + 1] 0 = o4G θ0sq F θ ((o4G θ0sq F θ)^[n] 0)
        rw [Function.iterate_succ_apply']
  have hiter_err : ∀ n, ∀ θ ∈ ball (0 : ℂ) 0.22, ‖ηn n θ - η θ‖ ≤ 1 / 5 * (1 / 2) ^ n := by
    intro n
    induction n with
    | zero =>
        intro θ hθ
        simp only [ηn, Function.iterate_zero, id, zero_sub, norm_neg, pow_zero, mul_one]
        exact (hη' θ hθ).1
    | succ n ih =>
        intro θ hθ
        have hθ' : ‖θ‖ < 0.22 := by simpa using hθ
        have e1 : ηn (n + 1) θ = o4G θ0sq F θ (ηn n θ) := by
          show (o4G θ0sq F θ)^[n + 1] 0 = _
          rw [Function.iterate_succ_apply']
        calc ‖ηn (n + 1) θ - η θ‖ = ‖o4G θ0sq F θ (ηn n θ) - o4G θ0sq F θ (η θ)‖ := by
              rw [e1, ← (hη' θ hθ).2.1]
          _ ≤ 1 / 2 * ‖ηn n θ - η θ‖ := o4G_lip h0 h1 hθ' hFd hFb (hiter_norm n θ hθ) (hη' θ hθ).1
          _ ≤ 1 / 2 * (1 / 5 * (1 / 2) ^ n) := by gcongr; exact ih θ hθ
          _ = 1 / 5 * (1 / 2) ^ (n + 1) := by ring
  have hconv : TendstoUniformlyOn ηn η atTop (ball 0 0.22) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < ε / 1) (by norm_num : (1 / 2 : ℝ) < 1)
    filter_upwards [eventually_ge_atTop N] with n hn θ hθ
    rw [dist_comm, dist_eq_norm]
    calc ‖ηn n θ - η θ‖ ≤ 1 / 5 * (1 / 2) ^ n := hiter_err n θ hθ
      _ ≤ 1 / 5 * (1 / 2) ^ N := by
          have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hn
          linarith
      _ < ε := by
          have : (1 / 2 : ℝ) ^ N < ε := by simpa using hN
          linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) N]
  refine ⟨η, hconv.tendstoLocallyUniformlyOn.differentiableOn (Eventually.of_forall hiter_diff) isOpen_ball,
    fun θ hθ => ⟨(hη' θ hθ).1, (hη' θ hθ).2.1⟩, fun θ hθ z hz hzf => (hη' θ hθ).2.2 z hz hzf⟩

end fixedpoint

section symmetry

variable {θ0sq : ℝ} {F : ℂ → ℂ}

/-- `G(-θ, e) = G(θ, e)` for even `F` (on the arguments that occur). -/
lemma o4G_neg (h0 : 0 ≤ θ0sq) (h1 : θ0sq ≤ 0.00244) {θ e : ℂ} (hθ : ‖θ‖ < 0.22) (he : ‖e‖ ≤ 1 / 5)
    (hFe : ∀ z ∈ ball (0 : ℂ) 0.25, F (-z) = F z) :
    o4G θ0sq F (-θ) e = o4G θ0sq F θ e := by
  have hw := (o4_bounds h0 h1 hθ he).2.2.2.2.2
  unfold o4G
  have : (-θ) * (1 + ((-θ) ^ 2 - θ0sq) * e) = -(θ * (1 + (θ ^ 2 - θ0sq) * e)) := by ring
  rw [this, hFe _ (by rw [mem_ball_zero_iff]; linarith)]
  simp only [neg_sq]

/-- **`η` is even** (uniqueness of the fixed point plus `G(-θ, ·) = G(θ, ·)`), for even `F`. -/
theorem o4_fixed_point_even (h0 : 0 ≤ θ0sq) (h1 : θ0sq ≤ 0.00244)
    (hFe : ∀ z ∈ ball (0 : ℂ) 0.25, F (-z) = F z) {η : ℂ → ℂ}
    (hfix : ∀ θ ∈ ball (0 : ℂ) 0.22, ‖η θ‖ ≤ 1 / 5 ∧ η θ = o4G θ0sq F θ (η θ))
    (huniq : ∀ θ ∈ ball (0 : ℂ) 0.22, ∀ z : ℂ, ‖z‖ ≤ 1 / 5 → z = o4G θ0sq F θ z → z = η θ) :
    ∀ θ ∈ ball (0 : ℂ) 0.22, η (-θ) = η θ := by
  intro θ hθ
  have hθ' : ‖θ‖ < 0.22 := by simpa using hθ
  have hmem : -θ ∈ ball (0 : ℂ) 0.22 := by simpa using hθ
  obtain ⟨hn, hf⟩ := hfix (-θ) hmem
  refine huniq θ hθ _ hn ?_
  rw [← o4G_neg h0 h1 hθ' hn hFe]; exact hf

/-- `G(θ, conj e) = conj G(θ, e)` for real `θ` and `F` real on the real-symmetric ball. -/
lemma o4G_conj {θ : ℝ} (e : ℂ) (hFr : ∀ z ∈ ball (0 : ℂ) 0.25, F ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F z))
    (h0 : 0 ≤ θ0sq) (h1 : θ0sq ≤ 0.00244) (hθ : |θ| < 0.22) (he : ‖e‖ ≤ 1 / 5) :
    o4G θ0sq F θ ((starRingEnd ℂ) e) = (starRingEnd ℂ) (o4G θ0sq F θ e) := by
  have hθ' : ‖(θ : ℂ)‖ < 0.22 := by simpa [Complex.norm_real] using hθ
  have hw := (o4_bounds h0 h1 hθ' he).2.2.2.2.2
  have hc : (starRingEnd ℂ) (θ * (1 + ((θ : ℂ) ^ 2 - θ0sq) * e)) = θ * (1 + ((θ : ℂ) ^ 2 - θ0sq) * (starRingEnd ℂ) e) := by
    simp [map_mul, map_add, map_sub, map_pow, Complex.conj_ofReal]
  unfold o4G
  have hF := hFr _ (show (θ : ℂ) * (1 + ((θ : ℂ) ^ 2 - θ0sq) * e) ∈ ball (0 : ℂ) 0.25 by
    rw [mem_ball_zero_iff]; linarith)
  rw [hc] at hF
  rw [hF]
  simp [map_mul, map_add, map_sub, map_pow, map_div₀, Complex.conj_ofReal, map_ofNat]

/-- **`η` is real on `ℝ`**, for `F` real on the real-symmetric ball. -/
theorem o4_fixed_point_real (h0 : 0 ≤ θ0sq) (h1 : θ0sq ≤ 0.00244)
    (hFr : ∀ z ∈ ball (0 : ℂ) 0.25, F ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F z)) {η : ℂ → ℂ}
    (hfix : ∀ θ ∈ ball (0 : ℂ) 0.22, ‖η θ‖ ≤ 1 / 5 ∧ η θ = o4G θ0sq F θ (η θ))
    (huniq : ∀ θ ∈ ball (0 : ℂ) 0.22, ∀ z : ℂ, ‖z‖ ≤ 1 / 5 → z = o4G θ0sq F θ z → z = η θ)
    {θ : ℝ} (hθ : |θ| < 0.22) : (starRingEnd ℂ) (η θ) = η θ := by
  have hmem : (θ : ℂ) ∈ ball (0 : ℂ) 0.22 := by simpa [Complex.norm_real] using hθ
  obtain ⟨hn, hf⟩ := hfix θ hmem
  refine huniq θ hmem _ (by simpa using hn) ?_
  rw [o4G_conj _ hFr h0 h1 hθ hn, ← hf]

end symmetry

/-- info: 'FormalResearch.CohnElkies.o4_fixed_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms o4_fixed_point


/-- info: 'FormalResearch.CohnElkies.o4_fixed_point_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms o4_fixed_point_even

/-- info: 'FormalResearch.CohnElkies.o4_fixed_point_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms o4_fixed_point_real

end FormalResearch.CohnElkies
