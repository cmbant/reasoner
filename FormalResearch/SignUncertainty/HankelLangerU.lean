module

public import FormalResearch.SignUncertainty.HankelLangerChart
public import FormalResearch.SignUncertainty.HankelCpowBounds
public import FormalResearch.SignUncertainty.NoshiroRouche

/-!
# The Langer chart in the variable `u = ζ²` (`gt:7.7b` (i)-(ii))

Since `h(ζ)² = K(ζ²)` and `𝗆(ζ)² = M(ζ²)` with
`K(u) = u G(u) = u (1 + ε(u))` and `M(u) = u E(u)^{2/3}`, the saddle equation `g(ζ) = s` reads
`K(ζ²) = 12 s/π²`.  The chart therefore needs only the two analytic maps `K`, `M` of `u` (no square roots of
the variable and no choice of sign of `ζ_+`):  `ζ_+² = K^{-1}(12 s/π²)` is analytic in `s`, and
`ũ = c^{2/3} λ M(K^{-1}(12 s/π²))`.  This module proves, on `‖u‖ ≤ q = 0.035²`:
`K`, `M` are holomorphic with `‖K' - 1‖ ≤ 1.5·10⁻³`, `‖M' - 1‖ ≤ 1.3·10⁻³`, `‖K u - u‖ ≤ q ε_h`;
both are injective on `closedBall 0 q` (Noshiro–Warschawski) and every `v` with `‖v‖ + q ε_h < q` has exactly
one preimage `K u = v` in `ball 0 q` (Rouché, `exists_unique_root_of_perturb`).
-/

@[expose] public section

open Complex Set Metric
open scoped Real

namespace FormalResearch.SignUncertainty

lemma div_one_sub_mono {r q : ℝ} (hr : 0 ≤ r) (hrq : r ≤ q) (hq : q < 1) :
    r / (1 - r) ≤ q / (1 - q) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- `k(u) = u F(u)^α`. -/
noncomputable def powMapU (F : ℂ → ℂ) (α : ℝ) (u : ℂ) : ℂ := u * F u ^ (α : ℂ)

/-- Its derivative `F^α + u α F^{α-1} F'`. -/
noncomputable def powMapUD (F F' : ℂ → ℂ) (α : ℝ) (u : ℂ) : ℂ :=
  F u ^ (α : ℂ) + u * ((α : ℂ) * F u ^ ((α : ℂ) - 1) * F' u)

lemma hasDerivAt_powMapU {F F' : ℂ → ℂ} {u : ℂ} (α : ℝ) (hF : HasDerivAt F (F' u) u)
    (hslit : F u ∈ slitPlane) : HasDerivAt (powMapU F α) (powMapUD F F' α u) u := by
  have hp := hF.cpow_const (c := (α : ℂ)) hslit
  have := (hasDerivAt_id u).mul hp
  have hfun : powMapU F α = (id * fun x : ℂ => F x ^ (α : ℂ)) := by
    funext x; simp [powMapU]
  rw [hfun]
  convert this using 1
  simp [powMapUD]

lemma norm_powMapUD_sub_one_le {F F' : ℂ → ℂ} {u : ℂ} {α τ D : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hτ : τ < 1) (hx : ‖F u - 1‖ ≤ τ) (hD : ‖F' u‖ ≤ D) :
    ‖powMapUD F F' α u - 1‖ ≤ α * τ / (1 - τ) + α * ‖u‖ * D / (1 - τ) := by
  have hτ0 : 0 ≤ τ := (norm_nonneg _).trans hx
  have h1 : 0 < 1 - τ := by linarith
  have hF : F u = 1 + (F u - 1) := by ring
  have hA := norm_one_add_cpow_sub_one_le hα hα1 hx hτ
  rw [← hF] at hA
  have hB := norm_one_add_cpow_neg_le (γ := 1 - α) (by linarith) (by linarith) hx hτ
  rw [← hF] at hB
  have e : (((-(1 - α) : ℝ)) : ℂ) = (α : ℂ) - 1 := by push_cast; ring
  rw [e] at hB
  unfold powMapUD
  have : F u ^ (α : ℂ) + u * ((α : ℂ) * F u ^ ((α : ℂ) - 1) * F' u) - 1
      = (F u ^ (α : ℂ) - 1) + u * ((α : ℂ) * F u ^ ((α : ℂ) - 1) * F' u) := by ring
  rw [this]
  refine (norm_add_le _ _).trans (add_le_add hA ?_)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα]
  calc ‖u‖ * (α * ‖F u ^ ((α : ℂ) - 1)‖ * ‖F' u‖) ≤ ‖u‖ * (α * (1 / (1 - τ)) * D) := by gcongr
    _ = α * ‖u‖ * D / (1 - τ) := by field_simp

section KM

variable {η : ℕ → ℝ}

/-- `K(u) = u G(u)`, `G = ∑ aG_j u^j`; `(π²/12) K(ζ²) = g(ζ)`. -/
noncomputable def chartK (η : ℕ → ℝ) (u : ℂ) : ℂ := u * psW (aG η) u

/-- `M(u) = u E(u)^{2/3}`; `𝗆(ζ)² = M(ζ²)`. -/
noncomputable def chartM (η : ℕ → ℝ) (u : ℂ) : ℂ := powMapU (psW (aE η)) (2 / 3) u

/-- Derivative of `K`. -/
noncomputable def chartKD (η : ℕ → ℝ) (u : ℂ) : ℂ := psW (aG η) u + u * psWD (aG η) u

/-- Derivative of `M`. -/
noncomputable def chartMD (η : ℕ → ℝ) (u : ℂ) : ℂ := powMapUD (psW (aE η)) (psWD (aE η)) (2 / 3) u

lemma hasDerivAt_chartK (h : LangerEta η) {u : ℂ} (hu : ‖u‖ < 1) :
    HasDerivAt (chartK η) (chartKD η u) u := by
  have hd := hasDerivAt_psW (B := 1) (abs_aG_le_one h) hu
  have := (hasDerivAt_id u).mul hd
  have hfun : chartK η = (id * psW (aG η)) := by funext x; simp [chartK]
  rw [hfun]
  convert this using 1
  simp [chartKD]

lemma norm_psW_aG_sub_one_u (h : LangerEta η) {u : ℂ} (hu : ‖u‖ ≤ 0.035 ^ 2) :
    ‖psW (aG η) u - 1‖ ≤ 7.46e-4 := by
  have h1 : ‖u‖ < 1 := lt_of_le_of_lt hu (by norm_num)
  have := norm_chartEps_le h h1
  unfold chartEps at this
  refine this.trans ?_
  have hm := div_one_sub_mono (norm_nonneg u) hu (by norm_num : (0.035 : ℝ) ^ 2 < 1)
  calc 6 / π ^ 2 * ‖u‖ / (1 - ‖u‖) = 6 / π ^ 2 * (‖u‖ / (1 - ‖u‖)) := by ring
    _ ≤ 6 / π ^ 2 * (0.035 ^ 2 / (1 - 0.035 ^ 2)) := by gcongr
    _ = 6 / π ^ 2 * (0.035 ^ 2) / (1 - 0.035 ^ 2) := by ring
    _ ≤ 7.46e-4 := chartEpsH_le

lemma norm_psW_aE_sub_one_u (h : LangerEta η) {u : ℂ} (hu : ‖u‖ ≤ 0.035 ^ 2) :
    ‖psW (aE η) u - 1‖ ≤ 8.95e-4 := by
  have h1 : ‖u‖ < 1 := lt_of_le_of_lt hu (by norm_num)
  have := norm_chartE_sub_one_le h h1
  unfold chartE at this
  refine this.trans ?_
  have hm := div_one_sub_mono (norm_nonneg u) hu (by norm_num : (0.035 : ℝ) ^ 2 < 1)
  calc 36 / (5 * π ^ 2) * ‖u‖ / (1 - ‖u‖) = 36 / (5 * π ^ 2) * (‖u‖ / (1 - ‖u‖)) := by ring
    _ ≤ 36 / (5 * π ^ 2) * (0.035 ^ 2 / (1 - 0.035 ^ 2)) := by gcongr
    _ = 36 / (5 * π ^ 2) * (0.035 ^ 2) / (1 - 0.035 ^ 2) := by ring
    _ ≤ 8.95e-4 := chartEpsE_le

private lemma pi_sq_gt : (9.869 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_d4]

private lemma norm_psWD_aG_le_u (h : LangerEta η) {u : ℂ} (hu : ‖u‖ ≤ 0.035 ^ 2) :
    ‖psWD (aG η) u‖ ≤ (6 / 9.869) / (1 - 0.035 ^ 2) ^ 2 := by
  have h1 : ‖u‖ < 1 := lt_of_le_of_lt hu (by norm_num)
  have hD0 := norm_deriv_chartEps_le h h1
  refine hD0.trans ?_
  have : (1 - 0.035 ^ 2 : ℝ) ≤ 1 - ‖u‖ := by linarith
  have h2 : (1 - 0.035 ^ 2 : ℝ) ^ 2 ≤ (1 - ‖u‖) ^ 2 := pow_le_pow_left₀ (by norm_num) this 2
  have hP : 6 / π ^ 2 ≤ 6 / 9.869 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) pi_sq_gt.le
  calc 6 / π ^ 2 / (1 - ‖u‖) ^ 2 ≤ 6 / π ^ 2 / (1 - 0.035 ^ 2) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) h2
    _ ≤ (6 / 9.869) / (1 - 0.035 ^ 2) ^ 2 := by gcongr

private lemma norm_psWD_aE_le_u (h : LangerEta η) {u : ℂ} (hu : ‖u‖ ≤ 0.035 ^ 2) :
    ‖psWD (aE η) u‖ ≤ (36 / (5 * 9.869)) / (1 - 0.035 ^ 2) ^ 2 := by
  have h1 : ‖u‖ < 1 := lt_of_le_of_lt hu (by norm_num)
  have hD0 := norm_deriv_chartE_le h h1
  refine hD0.trans ?_
  have : (1 - 0.035 ^ 2 : ℝ) ≤ 1 - ‖u‖ := by linarith
  have h2 : (1 - 0.035 ^ 2 : ℝ) ^ 2 ≤ (1 - ‖u‖) ^ 2 := pow_le_pow_left₀ (by norm_num) this 2
  have hP : 36 / (5 * π ^ 2) ≤ 36 / (5 * 9.869) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith [pi_sq_gt])
  calc 36 / (5 * π ^ 2) / (1 - ‖u‖) ^ 2 ≤ 36 / (5 * π ^ 2) / (1 - 0.035 ^ 2) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) h2
    _ ≤ (36 / (5 * 9.869)) / (1 - 0.035 ^ 2) ^ 2 := by gcongr

/-- `‖K' - 1‖ ≤ 1.5·10⁻³` on `‖u‖ ≤ q`. -/
lemma norm_chartKD_sub_one_le (h : LangerEta η) {u : ℂ} (hu : ‖u‖ ≤ 0.035 ^ 2) :
    ‖chartKD η u - 1‖ ≤ 1.5e-3 := by
  have h1 := norm_psW_aG_sub_one_u h hu
  have h2 := norm_psWD_aG_le_u h hu
  unfold chartKD
  have : psW (aG η) u + u * psWD (aG η) u - 1 = (psW (aG η) u - 1) + u * psWD (aG η) u := by ring
  rw [this]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have : ‖u‖ * ‖psWD (aG η) u‖ ≤ 0.035 ^ 2 * ((6 / 9.869) / (1 - 0.035 ^ 2) ^ 2) :=
    mul_le_mul hu h2 (norm_nonneg _) (by norm_num)
  linarith [show (0.035 : ℝ) ^ 2 * ((6 / 9.869) / (1 - 0.035 ^ 2) ^ 2) ≤ 7.5e-4 by norm_num]

lemma hasDerivAt_chartM (h : LangerEta η) {u : ℂ} (hu : ‖u‖ ≤ 0.035 ^ 2) :
    HasDerivAt (chartM η) (chartMD η u) u := by
  have h1 : ‖u‖ < 1 := lt_of_le_of_lt hu (by norm_num)
  have hd : HasDerivAt (psW (aE η)) (psWD (aE η) u) u := hasDerivAt_psW (B := 1) (abs_aE_le_one h) h1
  have hx := norm_psW_aE_sub_one_u h hu
  have hs : psW (aE η) u ∈ slitPlane := by
    have := one_add_mem_slitPlane_of_norm_lt (y := psW (aE η) u - 1) (lt_of_le_of_lt hx (by norm_num))
    simpa using this
  exact hasDerivAt_powMapU (F := psW (aE η)) (F' := psWD (aE η)) (2 / 3) hd hs

/-- `‖M' - 1‖ ≤ 1.3·10⁻³` on `‖u‖ ≤ q`. -/
lemma norm_chartMD_sub_one_le (h : LangerEta η) {u : ℂ} (hu : ‖u‖ ≤ 0.035 ^ 2) :
    ‖chartMD η u - 1‖ ≤ 1.3e-3 := by
  have hx := norm_psW_aE_sub_one_u h hu
  have hD := norm_psWD_aE_le_u h hu
  have := norm_powMapUD_sub_one_le (F := psW (aE η)) (F' := psWD (aE η)) (u := u) (α := 2 / 3)
    (τ := 8.95e-4) (D := (36 / (5 * 9.869)) / (1 - 0.035 ^ 2) ^ 2) (by norm_num) (by norm_num)
    (by norm_num) hx hD
  unfold chartMD
  refine this.trans ?_
  have : 2 / 3 * ‖u‖ * ((36 / (5 * 9.869)) / (1 - 0.035 ^ 2) ^ 2) / (1 - 8.95e-4)
      ≤ 2 / 3 * 0.035 ^ 2 * ((36 / (5 * 9.869)) / (1 - 0.035 ^ 2) ^ 2) / (1 - 8.95e-4) := by gcongr
  refine le_trans (add_le_add le_rfl this) ?_
  norm_num

lemma chartK_sub_self_le (h : LangerEta η) {u : ℂ} (hu : ‖u‖ ≤ 0.035 ^ 2) :
    ‖chartK η u - u‖ ≤ 0.035 ^ 2 * 7.46e-4 := by
  have : chartK η u - u = u * (psW (aG η) u - 1) := by unfold chartK; ring
  rw [this, norm_mul]
  exact mul_le_mul hu (norm_psW_aG_sub_one_u h hu) (norm_nonneg _) (by norm_num)


lemma re_chartKD_pos (h : LangerEta η) {u : ℂ} (hu : ‖u‖ ≤ 0.035 ^ 2) : 0 < (chartKD η u).re := by
  have := norm_chartKD_sub_one_le h hu
  have h2 : |(chartKD η u - 1).re| ≤ ‖chartKD η u - 1‖ := Complex.abs_re_le_norm _
  have h3 := abs_le.1 (h2.trans this)
  simp only [Complex.sub_re, Complex.one_re] at h3
  linarith [h3.1]

lemma re_chartMD_pos (h : LangerEta η) {u : ℂ} (hu : ‖u‖ ≤ 0.035 ^ 2) : 0 < (chartMD η u).re := by
  have := norm_chartMD_sub_one_le h hu
  have h2 : |(chartMD η u - 1).re| ≤ ‖chartMD η u - 1‖ := Complex.abs_re_le_norm _
  have h3 := abs_le.1 (h2.trans this)
  simp only [Complex.sub_re, Complex.one_re] at h3
  linarith [h3.1]

/-- `K` is injective on `closedBall 0 q` (Noshiro–Warschawski). -/
lemma injOn_chartK (h : LangerEta η) : Set.InjOn (chartK η) (closedBall (0 : ℂ) (0.035 ^ 2)) :=
  injOn_of_re_deriv_pos (convex_closedBall _ _) (f' := chartKD η)
    (fun u hu => hasDerivAt_chartK h (lt_of_le_of_lt (by simpa using mem_closedBall_zero_iff.1 hu)
      (by norm_num)))
    (fun u hu => re_chartKD_pos h (by simpa using mem_closedBall_zero_iff.1 hu))

/-- `M` is injective on `closedBall 0 q`. -/
lemma injOn_chartM (h : LangerEta η) : Set.InjOn (chartM η) (closedBall (0 : ℂ) (0.035 ^ 2)) :=
  injOn_of_re_deriv_pos (convex_closedBall _ _) (f' := chartMD η)
    (fun u hu => hasDerivAt_chartM h (by simpa using mem_closedBall_zero_iff.1 hu))
    (fun u hu => re_chartMD_pos h (by simpa using mem_closedBall_zero_iff.1 hu))

/-- **`gt:7.7b` (i), in the variable `u = ζ²`.** Every `v` with `‖v‖ + q ε_h < q` has exactly one
preimage `K u = v` in `ball 0 q`. -/
theorem exists_unique_chartK_root (h : LangerEta η) {v : ℂ} (hv : ‖v‖ + 0.035 ^ 2 * 7.46e-4 < 0.035 ^ 2) :
    ∃! u : ℂ, u ∈ ball (0 : ℂ) (0.035 ^ 2) ∧ chartK η u = v := by
  refine exists_unique_root_of_perturb (r := 0.035 ^ 2) (R := 1 / 2) (by norm_num) (by norm_num)
    (h := chartK η) ?_ (0.035 ^ 2 * 7.46e-4) ?_ hv ?_
  · intro u hu
    have : ‖u‖ < 1 := by
      have := mem_ball_zero_iff.1 hu; linarith
    exact (hasDerivAt_chartK h this).differentiableAt.differentiableWithinAt
  · intro z hz
    exact chartK_sub_self_le h hz.le
  · intro z hz
    have hz' : ‖z‖ ≤ 0.035 ^ 2 := by simpa using mem_closedBall_zero_iff.1 hz
    rw [(hasDerivAt_chartK h (lt_of_le_of_lt hz' (by norm_num))).deriv]
    exact re_chartKD_pos h hz'


open Classical in
/-- The chart-`K` inverse `K^{-1}` on the preimage disc (junk value `0` elsewhere). -/
noncomputable def chartKinv (η : ℕ → ℝ) (v : ℂ) : ℂ :=
  if hv : ∃ u : ℂ, u ∈ ball (0 : ℂ) (0.035 ^ 2) ∧ chartK η u = v then Classical.choose hv else 0

/-- The disc of admissible values `‖v‖ + q ε_h < q`. -/
noncomputable def chartVdisc : Set ℂ := ball (0 : ℂ) (0.035 ^ 2 - 0.035 ^ 2 * 7.46e-4)

lemma mem_chartVdisc {v : ℂ} : v ∈ chartVdisc ↔ ‖v‖ + 0.035 ^ 2 * 7.46e-4 < 0.035 ^ 2 := by
  unfold chartVdisc; rw [mem_ball_zero_iff]; constructor <;> intro h <;> linarith

lemma chartKinv_spec (h : LangerEta η) {v : ℂ} (hv : v ∈ chartVdisc) :
    chartKinv η v ∈ ball (0 : ℂ) (0.035 ^ 2) ∧ chartK η (chartKinv η v) = v := by
  obtain ⟨u, hu, _⟩ := exists_unique_chartK_root h (mem_chartVdisc.1 hv)
  have hex : ∃ u : ℂ, u ∈ ball (0 : ℂ) (0.035 ^ 2) ∧ chartK η u = v := ⟨u, hu⟩
  classical
  unfold chartKinv
  rw [dif_pos hex]
  exact Classical.choose_spec hex

lemma chartKinv_eq_of {h : LangerEta η} {v u : ℂ} (hv : v ∈ chartVdisc)
    (hu : u ∈ ball (0 : ℂ) (0.035 ^ 2)) (hK : chartK η u = v) : chartKinv η v = u := by
  obtain ⟨u0, _, huniq⟩ := exists_unique_chartK_root h (mem_chartVdisc.1 hv)
  have h1 := huniq _ (chartKinv_spec h hv)
  have h2 := huniq u ⟨hu, hK⟩
  rw [h1, h2]

lemma hasDerivAt_chartKinv (h : LangerEta η) {v0 : ℂ} (hv0 : v0 ∈ chartVdisc) :
    HasDerivAt (chartKinv η) ((chartKD η (chartKinv η v0))⁻¹) v0 := by
  obtain ⟨hu0, hKu0⟩ := chartKinv_spec h hv0
  set u0 := chartKinv η v0 with hu0def
  have hu0n : ‖u0‖ < 0.035 ^ 2 := mem_ball_zero_iff.1 hu0
  have hdiff : DifferentiableOn ℂ (chartK η) (ball (0 : ℂ) (1 / 2)) := fun u hu =>
    (hasDerivAt_chartK h (by have := mem_ball_zero_iff.1 hu; linarith)).differentiableAt.differentiableWithinAt
  have han : AnalyticAt ℂ (chartK η) u0 :=
    hdiff.analyticAt (isOpen_ball.mem_nhds (by rw [mem_ball_zero_iff]; linarith))
  have hstrict : HasStrictDerivAt (chartK η) (chartKD η u0) u0 := by
    have := (han.contDiffAt (n := 1)).hasStrictDerivAt_deriv (by norm_num)
    rwa [(hasDerivAt_chartK h (by linarith)).deriv] at this
  have hne : chartKD η u0 ≠ 0 := by
    intro h0
    have := re_chartKD_pos h hu0n.le
    rw [h0] at this; simp at this
  set g := hstrict.localInverse (chartK η) (chartKD η u0) u0 hne with hg
  have hgstrict : HasStrictDerivAt g (chartKD η u0)⁻¹ (chartK η u0) := hstrict.to_localInverse hne
  rw [hKu0] at hgstrict
  have hgv0 : g v0 = u0 := by
    have := hstrict.eventually_left_inverse hne
    have := this.self_of_nhds
    rwa [hKu0] at this
  have hright : ∀ᶠ v in nhds v0, chartK η (g v) = v := by
    have := hstrict.eventually_right_inverse hne
    rwa [hKu0] at this
  have hgcont : ContinuousAt g v0 := hgstrict.hasDerivAt.continuousAt
  have hball : ∀ᶠ v in nhds v0, g v ∈ ball (0 : ℂ) (0.035 ^ 2) :=
    hgcont.eventually (isOpen_ball.mem_nhds (by rw [hgv0]; exact hu0))
  have hV : ∀ᶠ v in nhds v0, v ∈ chartVdisc := isOpen_ball.mem_nhds hv0
  have heq : ∀ᶠ v in nhds v0, g v = chartKinv η v := by
    filter_upwards [hright, hball, hV] with v h1 h2 h3
    exact (chartKinv_eq_of (h := h) h3 h2 h1).symm
  have := hgstrict.hasDerivAt.congr_of_eventuallyEq (heq.mono fun v hv => hv.symm)
  exact this

end KM

/-- info: 'FormalResearch.SignUncertainty.exists_unique_chartK_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_unique_chartK_root

/-- info: 'FormalResearch.SignUncertainty.hasDerivAt_chartKinv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_chartKinv

/-- info: 'FormalResearch.SignUncertainty.injOn_chartK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms injOn_chartK

/-- info: 'FormalResearch.SignUncertainty.norm_chartMD_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_chartMD_sub_one_le

end FormalResearch.SignUncertainty
