module

public import FormalResearch.SignUncertainty.HankelWindowGeom
public import FormalResearch.SignUncertainty.HankelLangerPsi
public import FormalResearch.SignUncertainty.HankelLangerReal
public import FormalResearch.SignUncertainty.HankelStripSeries
public import FormalResearch.SignUncertainty.NoshiroRouche

/-!
# Chart comparability for the Langer coordinate (`u1cl:langer`, Lemma L.2)

Source: `CFT/sign_uncertainty/paper/langer_transport.tex`, Lemma L.2 (chart comparability), proved from
`gt:7.7b` (iv).  With `κ_ζ = 2/c_s`, `c_s = (π²/3)^{1/3}` the lemma says, for the saddle `ζ_+` of `g(ζ) = s`:

* `ζ_+ = κ_ζ c^{-1/3} √ũ q(ũ c^{-2/3})` with `q` analytic, real Taylor coefficients, `q(0) = 1` and
  `|q(w) - 1| ≤ C_q |w|` on `|w| ≤ ½ β₁ r₀`;
* `|ζ_+| = κ_ζ c^{-1/3} a'(1 + δ₁)`, `Re ζ_+ = κ_ζ c^{-1/3} a' sin φ' (1 + δ₂)`, `|δ_i| ≤ 10⁻³`, for
  `ũ = a'² e^{i(π - 2φ')}`;
* on the band `ũ = -vt < 0`: `ζ_+ = iτ₀`, `τ₀ = κ_ζ c^{-1/3} √vt q(-vt c^{-2/3})`, `m(τ₀) = log(π²ξ)`,
  `m(τ) = log((πτ/2)/tanh(πτ/2))`.

## Lean formulation

The chart is the actual Hankel chart (`etaC`, `langerUtilde`, `mMap`, `saddleRoot` of `HankelLangerRoot`).  The
saddle is a variable `ζ` with `‖ζ‖ ≤ 0.035` and `Re ζ > 0` (the paper's saddle satisfies `‖ζ_+‖ ≤ 0.03467`,
`Re ζ_+ > 0`; `chart_saddle_data` of `HankelLangerPsi` produces it from a chart point `y`), and
`ũ = langerUtilde etaC c (ζ²)`.  The hypothesis `|ũ| ≤ A_c² = ½ β₁ r₀ c^{2/3}` (`langerAc2`) is only used to place
`ũ c^{-2/3}` inside the domain of `q`.

* `q` is the explicit function `langerQ`: `q(w) = E(u(w))^{-1/3}` where `u(w)` inverts `u ↦ λ M(u)`,
  `λ = μ²`, `E`, `M` of `HankelLangerU`.  It is analytic with real Taylor coefficients on `|w| < 5·10⁻⁴`, which
  contains `|w| ≤ ½ β₁ r₀` for every `r₀ ≤ 10⁻⁴`.  The constant is `C_q = 1/2`.
* The `δ_i` constants are `10⁻³` as in the TeX (the underlying `hankel_saddle_geom` has `0.9991, 1.0009`;
  the chart derivative bound `‖𝗆' - 1‖ ≤ 9·10⁻⁴` of `gt:7.7b` (ii) is the same as the TeX).
* The band is `ζ = iτ₀`, `τ₀ ∈ (0, 0.035]`; the principal square root of `ũ = -vt` is `+i√vt`, i.e. the limit
  from `Im ũ > 0`; the identity `m(τ₀) = log(π²ξ)` is stated for a real `ξ > 0` with `g(iτ₀) = -log(π²ξ)`.
-/

@[expose] public section

open Complex Set Filter Topology Metric
open scoped Real ComplexConjugate

namespace FormalResearch.SignUncertainty

section Inverse

variable {η : ℕ → ℝ}

private lemma pi_sq_gt' : (9.869 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_d4]

/-- `chartM` is differentiable on the larger disc `‖u‖ < 1/10`. -/
lemma hasDerivAt_chartM_wide (h : LangerEta η) {u : ℂ} (hu : ‖u‖ < 1 / 10) :
    HasDerivAt (chartM η) (chartMD η u) u := by
  have h1 : ‖u‖ < 1 := by linarith
  have hd : HasDerivAt (psW (aE η)) (psWD (aE η) u) u := hasDerivAt_psW (B := 1) (abs_aE_le_one h) h1
  have hx := norm_chartE_sub_one_le h h1
  unfold chartE at hx
  have hx2 : ‖psW (aE η) u - 1‖ < 1 := by
    refine lt_of_le_of_lt hx ?_
    have hp := pi_sq_gt'
    have h2 : 36 / (5 * π ^ 2) ≤ 36 / (5 * 9.869) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    have h3 : ‖u‖ / (1 - ‖u‖) ≤ (1 / 10) / (1 - 1 / 10) := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith [norm_nonneg u]
    calc 36 / (5 * π ^ 2) * ‖u‖ / (1 - ‖u‖) = 36 / (5 * π ^ 2) * (‖u‖ / (1 - ‖u‖)) := by ring
      _ ≤ 36 / (5 * 9.869) * ((1 / 10) / (1 - 1 / 10)) := by gcongr
      _ < 1 := by norm_num
  have hs : psW (aE η) u ∈ slitPlane := by
    have := one_add_mem_slitPlane_of_norm_lt (y := psW (aE η) u - 1) hx2
    simpa using this
  exact hasDerivAt_powMapU (F := psW (aE η)) (F' := psWD (aE η)) (2 / 3) hd hs

lemma differentiableOn_chartM_wide (h : LangerEta η) : DifferentiableOn ℂ (chartM η) (ball 0 (1 / 10)) :=
  fun _ hu => (hasDerivAt_chartM_wide h (mem_ball_zero_iff.1 hu)).differentiableAt.differentiableWithinAt

/-- `‖M(u) - u‖ ≤ 2.1·10⁻³ ‖u‖` on `‖u‖ ≤ q`. -/
lemma norm_chartM_sub_self_le (h : LangerEta η) {u : ℂ} (hu : ‖u‖ ≤ 0.035 ^ 2) :
    ‖chartM η u - u‖ ≤ 2.1e-3 * ‖u‖ := by
  have h1 := norm_chartM_sub_chartK_le h hu
  have h2 := norm_psW_aG_sub_one_u h hu
  have e : chartK η u - u = u * (psW (aG η) u - 1) := by unfold chartK; ring
  have h3 : ‖chartK η u - u‖ ≤ ‖u‖ * 7.46e-4 := by
    rw [e, norm_mul]; exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  have e2 : chartM η u - u = (chartM η u - chartK η u) + (chartK η u - u) := by ring
  rw [e2]
  refine (norm_add_le _ _).trans ?_
  nlinarith [norm_nonneg u]

/-- Existence and uniqueness of the `M`-preimage on `ball 0 q` for `‖v‖ < 10⁻³`. -/
theorem exists_unique_chartM_root (h : LangerEta η) {v : ℂ} (hv : ‖v‖ < 1e-3) :
    ∃! u : ℂ, u ∈ ball (0 : ℂ) (0.035 ^ 2) ∧ chartM η u = v := by
  refine exists_unique_root_of_perturb (r := 0.035 ^ 2) (R := 1 / 10) (by norm_num) (by norm_num)
    (h := chartM η) (differentiableOn_chartM_wide h) (0.035 ^ 2 * 2.1e-3) ?_ (by nlinarith) ?_
  · intro z hz
    have := norm_chartM_sub_self_le h (u := z) hz.le
    rw [hz] at this; linarith
  · intro z hz
    have hz' : ‖z‖ ≤ 0.035 ^ 2 := by simpa using mem_closedBall_zero_iff.1 hz
    rw [(hasDerivAt_chartM h hz').deriv]
    exact re_chartMD_pos h hz'

open Classical in
/-- The inverse of `M` on `ball 0 q` (junk value `0` where there is no preimage). -/
noncomputable def chartMinv (η : ℕ → ℝ) (v : ℂ) : ℂ :=
  if hv : ∃ u : ℂ, u ∈ ball (0 : ℂ) (0.035 ^ 2) ∧ chartM η u = v then Classical.choose hv else 0

lemma chartMinv_spec_of_exists (η : ℕ → ℝ) {v : ℂ} (hv : ∃ u : ℂ, u ∈ ball (0 : ℂ) (0.035 ^ 2) ∧ chartM η u = v) :
    chartMinv η v ∈ ball (0 : ℂ) (0.035 ^ 2) ∧ chartM η (chartMinv η v) = v := by
  classical
  unfold chartMinv
  simp only [hv, dite_true]
  exact Classical.choose_spec hv

lemma chartMinv_spec (h : LangerEta η) {v : ℂ} (hv : ‖v‖ < 1e-3) :
    chartMinv η v ∈ ball (0 : ℂ) (0.035 ^ 2) ∧ chartM η (chartMinv η v) = v := by
  obtain ⟨u, hu, _⟩ := exists_unique_chartM_root h hv
  exact chartMinv_spec_of_exists η ⟨u, hu⟩

lemma chartMinv_eq_of (h : LangerEta η) {v u : ℂ} (hv : ‖v‖ < 1e-3) (hu : u ∈ ball (0 : ℂ) (0.035 ^ 2))
    (hM : chartM η u = v) : chartMinv η v = u := by
  obtain ⟨u0, _, huniq⟩ := exists_unique_chartM_root h hv
  rw [huniq _ (chartMinv_spec h hv), huniq u ⟨hu, hM⟩]

lemma chartMinv_zero (h : LangerEta η) : chartMinv η 0 = 0 := by
  refine chartMinv_eq_of h (by norm_num) (by rw [mem_ball_zero_iff]; norm_num) ?_
  unfold chartM powMapU; simp

/-- `chartMinv` is analytic at any `v = M(u₀)` with `u₀ ∈ ball 0 q`. -/
theorem analyticAt_chartMinv (h : LangerEta η) {v : ℂ} (hv : ‖v‖ < 1e-3) :
    AnalyticAt ℂ (chartMinv η) v ∧ HasDerivAt (chartMinv η) (chartMD η (chartMinv η v))⁻¹ v := by
  obtain ⟨hu0, hMu0⟩ := chartMinv_spec h hv
  set u0 := chartMinv η v
  have hU : IsOpen (ball (0 : ℂ) (0.035 ^ 2)) := isOpen_ball
  have hdiff : ∀ w ∈ ball (0 : ℂ) (0.035 ^ 2), HasDerivAt (chartM η) (chartMD η w) w := fun w hw =>
    hasDerivAt_chartM h (mem_ball_zero_iff.1 hw).le
  have hf : ∀ w ∈ ball (0 : ℂ) (0.035 ^ 2), AnalyticAt ℂ (chartM η) w := by
    intro w hw
    refine Complex.analyticAt_iff_eventually_differentiableAt.2 ?_
    filter_upwards [hU.mem_nhds hw] with z hz using (hdiff z hz).differentiableAt
  have hne : ∀ w ∈ ball (0 : ℂ) (0.035 ^ 2), deriv (chartM η) w ≠ 0 := by
    intro w hw
    rw [(hdiff w hw).deriv]
    intro h0
    have := re_chartMD_pos h (mem_ball_zero_iff.1 hw).le
    rw [h0] at this; simp at this
  have hinj : InjOn (chartM η) (ball (0 : ℂ) (0.035 ^ 2)) := (injOn_chartM h).mono ball_subset_closedBall
  have key := analyticAt_choiceInverse (g := chartMinv η) hU hf hinj hne
    (fun y hy => by
      obtain ⟨w, hw, hwy⟩ := hy
      exact chartMinv_spec_of_exists η ⟨w, hw, hwy⟩) hu0
  rw [hMu0] at key
  refine ⟨key.1, ?_⟩
  have := key.2
  rwa [(hdiff u0 hu0).deriv] at this

lemma chartMinv_conj (h : LangerEta η) {v : ℂ} (hv : ‖v‖ < 1e-3) :
    chartMinv η (conj v) = conj (chartMinv η v) := by
  obtain ⟨hu, hM⟩ := chartMinv_spec h hv
  have hun : ‖chartMinv η v‖ ≤ 0.035 ^ 2 := (mem_ball_zero_iff.1 hu).le
  refine chartMinv_eq_of h (by rwa [Complex.norm_conj]) ?_ ?_
  · rw [mem_ball_zero_iff, Complex.norm_conj]; exact mem_ball_zero_iff.1 hu
  · rw [chartM_conj h hun, hM]

/-- If `M(u) = v` with `‖u‖ ≤ q` and `‖v‖ < 10⁻³` then `‖u‖ ≤ 1.0021 ‖v‖`, in particular `u ∈ ball 0 q`. -/
lemma norm_le_of_chartM_eq (h : LangerEta η) {u v : ℂ} (hu : ‖u‖ ≤ 0.035 ^ 2) (hM : chartM η u = v) :
    ‖u‖ * (1 - 2.1e-3) ≤ ‖v‖ := by
  have h1 := norm_chartM_sub_self_le h hu
  have h4 := norm_sub_norm_le u (-(chartM η u - u))
  have e2 : u - -(chartM η u - u) = chartM η u := by ring
  rw [e2, norm_neg] at h4
  rw [hM] at h4 h1
  linarith

end Inverse

section RealTaylor

/-- A conjugation-symmetric function on a disc about `0` has real Taylor coefficients: all
`iteratedDeriv n f 0` are real. -/
lemma conj_iteratedDeriv_zero {R : ℝ} (hR : 0 < R) :
    ∀ (n : ℕ) (g : ℂ → ℂ), (∀ w ∈ ball (0 : ℂ) R, g (conj w) = conj (g w)) →
      conj (iteratedDeriv n g 0) = iteratedDeriv n g 0 := by
  intro n
  induction n with
  | zero =>
    intro g hg
    have := hg 0 (by simpa using hR)
    simpa using this.symm
  | succ n ih =>
    intro g hg
    rw [iteratedDeriv_succ']
    refine ih (deriv g) ?_
    intro x hx
    have hev : g =ᶠ[𝓝 x] (conj ∘ g ∘ conj) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      have hy' : conj y ∈ ball (0 : ℂ) R := by
        rwa [mem_ball_zero_iff, Complex.norm_conj, ← mem_ball_zero_iff]
      have := hg (conj y) hy'
      simp only [Function.comp, Complex.conj_conj] at this ⊢
      exact this
    have h1 : deriv g x = deriv (conj ∘ g ∘ conj) x := hev.deriv_eq
    rw [deriv_conj_conj] at h1
    simp only [Function.comp] at h1
    rw [h1, Complex.conj_conj]

/-- A holomorphic conjugation-symmetric function on `ball 0 R` is a power series with real coefficients. -/
theorem exists_real_taylor {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hconj : ∀ w ∈ ball (0 : ℂ) R, f (conj w) = conj (f w)) :
    ∃ a : ℕ → ℝ, ∀ w ∈ ball (0 : ℂ) R, HasSum (fun j : ℕ => (a j : ℂ) * w ^ j) (f w) := by
  have hreal : ∀ n : ℕ, ((n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0).im = 0 := by
    intro n
    have h1 := conj_iteratedDeriv_zero hR n f hconj
    have h2 := congrArg Complex.im h1
    simp only [Complex.conj_im] at h2
    have : (iteratedDeriv n f 0).im = 0 := by linarith
    have hfac : ((n.factorial : ℂ)⁻¹).im = 0 := by
      rw [show ((n.factorial : ℂ)⁻¹) = (((n.factorial : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl]
      exact Complex.ofReal_im _
    simp [Complex.mul_im, this, hfac]
  refine ⟨fun n => ((n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0).re, fun w hw => ?_⟩
  have := Complex.hasSum_taylorSeries_on_ball hf hw
  convert this using 2 with n
  have hc : (((n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0).re : ℂ) = (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0 := by
    apply Complex.ext <;> simp [hreal n]
  rw [hc]; simp only [sub_zero, smul_eq_mul]; ring

end RealTaylor

section Q

variable {η : ℕ → ℝ}

lemma psW_aE_zero (h : LangerEta η) : psW (aE η) 0 = 1 := by
  unfold psW
  rw [tsum_eq_single 0]
  · simp [aE_zero h]
  · intro j hj; simp [hj]

lemma psW_aE_mem_slitPlane (h : LangerEta η) {u : ℂ} (hu : ‖u‖ ≤ 0.035 ^ 2) :
    psW (aE η) u ∈ slitPlane := by
  have hx := norm_psW_aE_sub_one_u h hu
  have := one_add_mem_slitPlane_of_norm_lt (y := psW (aE η) u - 1) (lt_of_le_of_lt hx (by norm_num))
  simpa using this

lemma psW_aE_ne_zero (h : LangerEta η) {u : ℂ} (hu : ‖u‖ ≤ 0.035 ^ 2) : psW (aE η) u ≠ 0 :=
  Complex.slitPlane_ne_zero (psW_aE_mem_slitPlane h hu)

lemma cpow_third_ne_zero {x : ℂ} (hx : x ≠ 0) : x ^ ((1 / 3 : ℝ) : ℂ) ≠ 0 := by
  intro h0
  rw [Complex.cpow_eq_zero_iff] at h0
  exact hx h0.1

/-- `Q(v) = E(u)^{-1/3}` with `u = M^{-1}(v)`: the factor of `ζ = 𝗆(ζ) Q(M(ζ²))`. -/
noncomputable def chartQ (η : ℕ → ℝ) (v : ℂ) : ℂ :=
  ((psW (aE η) (chartMinv η v)) ^ ((1 / 3 : ℝ) : ℂ))⁻¹

lemma chartQ_zero (h : LangerEta η) : chartQ η 0 = 1 := by
  unfold chartQ
  rw [chartMinv_zero h, psW_aE_zero h]; simp

lemma chartQ_of_chartM (h : LangerEta η) {u : ℂ} (hu : ‖u‖ ≤ 0.035 ^ 2) (hv : ‖chartM η u‖ < 1e-3) :
    chartQ η (chartM η u) = ((psW (aE η) u) ^ ((1 / 3 : ℝ) : ℂ))⁻¹ := by
  have hu' : ‖u‖ < 0.035 ^ 2 := by
    have := norm_le_of_chartM_eq h hu rfl
    nlinarith [norm_nonneg u]
  have := chartMinv_eq_of h hv (by rwa [mem_ball_zero_iff]) rfl
  unfold chartQ; rw [this]

lemma differentiableAt_chartQ (h : LangerEta η) {v : ℂ} (hv : ‖v‖ < 1e-3) :
    DifferentiableAt ℂ (chartQ η) v := by
  obtain ⟨hu0, _⟩ := chartMinv_spec h hv
  have hu0n : ‖chartMinv η v‖ ≤ 0.035 ^ 2 := (mem_ball_zero_iff.1 hu0).le
  have h1 := (analyticAt_chartMinv h hv).2.differentiableAt
  have h2 : DifferentiableAt ℂ (psW (aE η)) (chartMinv η v) :=
    (hasDerivAt_psW (B := 1) (abs_aE_le_one h) (lt_of_le_of_lt hu0n (by norm_num))).differentiableAt
  have h3 : DifferentiableAt ℂ (fun x => psW (aE η) (chartMinv η x)) v := h2.comp v h1
  have h4 : DifferentiableAt ℂ (fun x => (psW (aE η) (chartMinv η x)) ^ ((1 / 3 : ℝ) : ℂ)) v :=
    h3.cpow_const (psW_aE_mem_slitPlane h hu0n)
  exact h4.inv (cpow_third_ne_zero (psW_aE_ne_zero h hu0n))

lemma chartQ_conj (h : LangerEta η) {v : ℂ} (hv : ‖v‖ < 1e-3) :
    chartQ η (conj v) = conj (chartQ η v) := by
  obtain ⟨hu0, _⟩ := chartMinv_spec h hv
  have hu0n : ‖chartMinv η v‖ ≤ 0.035 ^ 2 := (mem_ball_zero_iff.1 hu0).le
  have harg : (psW (aE η) (chartMinv η v)).arg ≠ π :=
    (Complex.mem_slitPlane_iff_arg.1 (psW_aE_mem_slitPlane h hu0n)).1
  unfold chartQ
  rw [chartMinv_conj h hv, psW_conj, map_inv₀, Complex.conj_cpow _ _ harg, Complex.conj_ofReal]

/-- `‖E - 1‖ ≤ 0.74 ‖u‖` for `‖u‖ ≤ 1.0022·10⁻³`. -/
lemma norm_psW_aE_sub_one_lin (h : LangerEta η) {u : ℂ} (hu : ‖u‖ ≤ 1.0022e-3) :
    ‖psW (aE η) u - 1‖ ≤ 0.74 * ‖u‖ := by
  have h1 : ‖u‖ < 1 := by linarith
  have hx := norm_chartE_sub_one_le h h1
  unfold chartE at hx
  refine hx.trans ?_
  have hp := pi_sq_gt'
  have h2 : 36 / (5 * π ^ 2) ≤ 36 / (5 * 9.869) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have h3 : 36 / (5 * π ^ 2) * ‖u‖ / (1 - ‖u‖) = (36 / (5 * π ^ 2) / (1 - ‖u‖)) * ‖u‖ := by ring
  rw [h3]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg u)
  rw [div_le_iff₀ (by linarith)]
  have : 36 / (5 * 9.869 : ℝ) ≤ 0.74 * (1 - 1.0022e-3) := by norm_num
  nlinarith

/-- `‖Q(v) - 1‖ ≤ 0.2476 ‖v‖` for `‖v‖ < 10⁻³`. -/
theorem norm_chartQ_sub_one_le (h : LangerEta η) {v : ℂ} (hv : ‖v‖ < 1e-3) :
    ‖chartQ η v - 1‖ ≤ 0.2476 * ‖v‖ := by
  obtain ⟨hu0, hM⟩ := chartMinv_spec h hv
  set u := chartMinv η v with hudef
  have hun : ‖u‖ ≤ 0.035 ^ 2 := (mem_ball_zero_iff.1 hu0).le
  have hnu := norm_le_of_chartM_eq h hun hM
  have hu1 : ‖u‖ ≤ 1.0022e-3 := by nlinarith [norm_nonneg u, norm_nonneg v]
  have hx := norm_psW_aE_sub_one_lin h hu1
  set E := psW (aE η) u with hE
  set t : ℝ := 0.74 * ‖u‖ with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 7.42e-4 := by rw [ht]; nlinarith [norm_nonneg u]
  have hA := norm_one_add_cpow_sub_one_le (α := 1 / 3) (by norm_num) (by norm_num) (x := E - 1) (t := t)
    hx (by linarith)
  rw [show 1 + (E - 1) = E by ring] at hA
  set F := E ^ ((1 / 3 : ℝ) : ℂ) with hF
  set s : ℝ := 1 / 3 * t / (1 - t) with hs
  have hs1 : s ≤ 0.2469 * ‖u‖ := by
    rw [hs, div_le_iff₀ (by linarith)]
    rw [ht]; nlinarith [norm_nonneg u]
  have hs0 : 0 ≤ s := by rw [hs]; exact div_nonneg (by positivity) (by linarith)
  have hs2 : s ≤ 2.5e-4 := by nlinarith [norm_nonneg u]
  have hFn : 1 - s ≤ ‖F‖ := by
    have := norm_sub_norm_le (1 : ℂ) (1 - F)
    simp only [sub_sub_cancel, norm_one] at this
    have h5 : ‖1 - F‖ ≤ s := by rw [norm_sub_rev]; exact hA
    linarith
  have hF0 : F ≠ 0 := cpow_third_ne_zero (psW_aE_ne_zero h hun)
  have e : chartQ η v - 1 = (1 - F) / F := by
    unfold chartQ; rw [← hudef, ← hE, ← hF]; field_simp
  rw [e, norm_div]
  have hFpos : 0 < ‖F‖ := norm_pos_iff.2 hF0
  rw [div_le_iff₀ hFpos]
  have h5 : ‖1 - F‖ ≤ s := by rw [norm_sub_rev]; exact hA
  have h6 : ‖u‖ ≤ ‖v‖ / (1 - 2.1e-3) := by rw [le_div_iff₀ (by norm_num)]; linarith
  have : s * (1 - 2.5e-4) ≤ 0.2469 * ‖u‖ := by nlinarith
  nlinarith [norm_nonneg u, norm_nonneg v]

end Q

section Headline

/-- `q`-function of `u1cl:langer`: `q(w) = E(u)^{-1/3}` where `λ M(u) = w`, `λ = μ²` (`ũ = c^{2/3} λ M(u)`). -/
noncomputable def langerQ (w : ℂ) : ℂ := chartQ etaC (w / ((langerMu ^ 2 : ℝ) : ℂ))

/-- `κ_ζ = 2/c_s`, `c_s = (π²/3)^{1/3}`. -/
noncomputable def langerKappaZeta : ℝ := 2 / (π ^ 2 / 3) ^ (1 / 3 : ℝ)

/-- `A_c² = ½ β₁ r₀ c^{2/3}`, the radius of the Langer disc. -/
noncomputable def langerAc2 (r0 c : ℝ) : ℝ := hankelBeta1 / 2 * r0 * c ^ (2 / 3 : ℝ)

/-- The band function `m(τ) = log((πτ/2)/tanh(πτ/2))`. -/
noncomputable def langerMband (τ : ℝ) : ℝ := Real.log ((π * τ / 2) / Real.tanh (π * τ / 2))

lemma langerKappaZeta_mul_mu : langerKappaZeta * langerMu = 1 := by
  have hpos : 0 < (π ^ 2 / 3 : ℝ) := by positivity
  have h8 : (1 / 8 : ℝ) ^ (1 / 3 : ℝ) = 1 / 2 := by
    have := Real.pow_rpow_inv_natCast (x := 1 / 2) (n := 3) (by norm_num) (by norm_num)
    rw [show ((3 : ℕ) : ℝ)⁻¹ = (1 / 3 : ℝ) by norm_num] at this
    rw [← this]; norm_num
  have hmu : langerMu = (π ^ 2 / 3) ^ (1 / 3 : ℝ) / 2 := by
    unfold langerMu
    rw [show (π ^ 2 / 24 : ℝ) = (π ^ 2 / 3) * (1 / 8) by ring, Real.mul_rpow hpos.le (by norm_num), h8]
    ring
  have hc : 0 < (π ^ 2 / 3 : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hpos _
  unfold langerKappaZeta
  rw [hmu]; field_simp

lemma langerKappaZeta_eq : langerKappaZeta = 2 * langerKappa := by
  have h1 := langerKappaZeta_mul_mu
  have h2 := langerKappa_mul_mu
  have hm := langerMu_pos
  have : langerKappaZeta * langerMu = (2 * langerKappa) * langerMu := by rw [h1, h2]
  exact mul_right_cancel₀ hm.ne' this

lemma kappaZeta_mul_rpow {c : ℝ} (hc : 0 < c) :
    langerKappaZeta * c ^ (-(1 / 3) : ℝ) = 1 / (c ^ (1 / 3 : ℝ) * langerMu) := by
  have hk : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  have hm := langerMu_pos
  rw [Real.rpow_neg hc.le]
  have h1 := langerKappaZeta_mul_mu
  field_simp
  linear_combination h1

lemma langerMu_sq_lt : langerMu ^ 2 < 5 / 6 := by
  by_contra hlt
  push Not at hlt
  have h3 : (5 / 6 : ℝ) ^ 3 ≤ (langerMu ^ 2) ^ 3 := pow_le_pow_left₀ (by norm_num) hlt 3
  have e : (langerMu ^ 2) ^ 3 = (π ^ 2 / 24) ^ 2 := by rw [← langerMu_cube]; ring
  rw [e] at h3
  have : π ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  nlinarith [Real.pi_pos]

/-- `½ β₁ r₀ < 5·10⁻⁴` for `r₀ ≤ 10⁻⁴`: the disc `|w| ≤ ½β₁r₀` lies in the domain of `langerQ`. -/
lemma langerAc2_radius_lt {r0 : ℝ} (hr0 : r0 ≤ 1e-4) : hankelBeta1 / 2 * r0 < 5e-4 := by
  rw [hankelBeta1_eq]
  have := langerMu_sq_lt
  have hr : 0 ≤ r0 ∨ r0 < 0 := le_or_gt 0 r0
  rcases hr with hr | hr
  · nlinarith
  · nlinarith [langerMu_pos]

lemma norm_div_lam_le (w : ℂ) : ‖w / ((langerMu ^ 2 : ℝ) : ℂ)‖ ≤ 2 * ‖w‖ := by
  have hm := langerMu_sq_ge
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [div_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg w]

lemma differentiableOn_langerQ : DifferentiableOn ℂ langerQ (ball 0 5e-4) := by
  intro w hw
  have hw' := mem_ball_zero_iff.1 hw
  have hv : ‖w / ((langerMu ^ 2 : ℝ) : ℂ)‖ < 1e-3 := by
    have := norm_div_lam_le w; linarith
  have h1 : DifferentiableAt ℂ (fun x : ℂ => x / ((langerMu ^ 2 : ℝ) : ℂ)) w :=
    (differentiableAt_id).div_const _
  exact ((differentiableAt_chartQ langerEta_etaC hv).comp w h1).differentiableWithinAt

lemma langerQ_conj {w : ℂ} (hw : w ∈ ball (0 : ℂ) 5e-4) : langerQ (conj w) = conj (langerQ w) := by
  have hw' := mem_ball_zero_iff.1 hw
  have hv : ‖w / ((langerMu ^ 2 : ℝ) : ℂ)‖ < 1e-3 := by
    have := norm_div_lam_le w; linarith
  unfold langerQ
  rw [← chartQ_conj langerEta_etaC hv, map_div₀, Complex.conj_ofReal]

lemma langerQ_zero : langerQ 0 = 1 := by
  unfold langerQ; rw [zero_div]; exact chartQ_zero langerEta_etaC

lemma norm_langerQ_sub_one_le {w : ℂ} (hw : w ∈ ball (0 : ℂ) 5e-4) : ‖langerQ w - 1‖ ≤ 1 / 2 * ‖w‖ := by
  have hw' := mem_ball_zero_iff.1 hw
  have h2 := norm_div_lam_le w
  have hv : ‖w / ((langerMu ^ 2 : ℝ) : ℂ)‖ < 1e-3 := by linarith
  have := norm_chartQ_sub_one_le langerEta_etaC hv
  unfold langerQ
  nlinarith [norm_nonneg w]

/-- `q` of `u1cl:langer`: analytic, real Taylor coefficients, `q(0) = 1`, `|q(w) - 1| ≤ |w|/2`
(`C_q = 1/2`) on `|w| < 5·10⁻⁴`, which contains `|w| ≤ ½ β₁ r₀` for every `r₀ ≤ 10⁻⁴`
(`langerAc2_radius_lt`). -/
theorem langerQ_properties :
    AnalyticOnNhd ℂ langerQ (ball (0 : ℂ) 5e-4) ∧
    (∃ a : ℕ → ℝ, ∀ w ∈ ball (0 : ℂ) 5e-4, HasSum (fun j : ℕ => (a j : ℂ) * w ^ j) (langerQ w)) ∧
    langerQ 0 = 1 ∧
    ∀ w ∈ ball (0 : ℂ) 5e-4, ‖langerQ w - 1‖ ≤ 1 / 2 * ‖w‖ :=
  ⟨differentiableOn_langerQ.analyticOnNhd isOpen_ball,
   exists_real_taylor (by norm_num) differentiableOn_langerQ (fun _ hw => langerQ_conj hw),
   langerQ_zero, fun _ hw => norm_langerQ_sub_one_le hw⟩

/-- `‖ũ‖ ≤ A_c²` puts `M(ζ²)` in the domain of the `M`-inverse. -/
lemma norm_chartM_lt_of_Ac2 {c r0 : ℝ} (hc : 0 < c) (hr0 : r0 ≤ 1e-4) {u : ℂ}
    (hA : ‖langerUtilde etaC c u‖ ≤ langerAc2 r0 c) : ‖chartM etaC u‖ < 1e-3 := by
  have hk : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  have hm := langerMu_sq_ge
  have hn : ‖langerUtilde etaC c u‖ = c ^ (2 / 3 : ℝ) * langerMu ^ 2 * ‖chartM etaC u‖ := by
    unfold langerUtilde
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hn] at hA
  unfold langerAc2 at hA
  rw [hankelBeta1_eq] at hA
  have h2 : c ^ (2 / 3 : ℝ) * (langerMu ^ 2 * ‖chartM etaC u‖) ≤ c ^ (2 / 3 : ℝ) * (6 * langerMu ^ 2 * r0) := by
    nlinarith
  have h3 := le_of_mul_le_mul_left h2 hk
  have h4 : ‖chartM etaC u‖ ≤ 6 * r0 := by
    have : langerMu ^ 2 * ‖chartM etaC u‖ ≤ langerMu ^ 2 * (6 * r0) := by nlinarith
    exact le_of_mul_le_mul_left this (by linarith)
  linarith

/-- `ζ = 𝗆(ζ) · q(λ M(ζ²))`. -/
lemma zeta_eq_mMap_mul_q {ζ : ℂ} (hζ : ‖ζ‖ ≤ 0.035) (hv : ‖chartM etaC (ζ ^ 2)‖ < 1e-3) :
    ζ = mMap etaC ζ * langerQ (((langerMu ^ 2 : ℝ) : ℂ) * chartM etaC (ζ ^ 2)) := by
  have hu : ‖ζ ^ 2‖ ≤ 0.035 ^ 2 := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hζ 2
  have hm : (langerMu ^ 2 : ℝ) ≠ 0 := (by have := langerMu_pos; positivity)
  have e : (((langerMu ^ 2 : ℝ) : ℂ) * chartM etaC (ζ ^ 2)) / ((langerMu ^ 2 : ℝ) : ℂ) = chartM etaC (ζ ^ 2) := by
    have : ((langerMu ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hm
    field_simp
  unfold langerQ
  rw [e, chartQ_of_chartM langerEta_etaC hu hv]
  have hF := cpow_third_ne_zero (psW_aE_ne_zero langerEta_etaC hu)
  unfold mMap powMap
  field_simp

end Headline

section Main

lemma sq_mem_slitPlane {ζ : ℂ} (hre : 0 < ζ.re) : ζ ^ 2 ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases him : ζ.im = 0
  · left; rw [sq, Complex.mul_re, him]; nlinarith
  · right; rw [sq, Complex.mul_im]; intro h0
    have : ζ.re * ζ.im + ζ.im * ζ.re = 2 * ζ.re * ζ.im := by ring
    have h2 : ζ.re * ζ.im = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h | h
    · linarith
    · exact him h

lemma saddleRoot_sq_of_re_pos {ζ : ℂ} (hre : 0 < ζ.re) : saddleRoot (ζ ^ 2) = ζ := by
  unfold saddleRoot; exact cpow_half_sq_of_re_pos hre

lemma langerUtilde_arg_eq {c : ℝ} (hc : 0 < c) (u : ℂ) :
    ((c ^ (-(2 / 3) : ℝ) : ℝ) : ℂ) * langerUtilde etaC c u =
      ((langerMu ^ 2 : ℝ) : ℂ) * chartM etaC u := by
  unfold langerUtilde
  rw [← mul_assoc, ← Complex.ofReal_mul]
  have : c ^ (-(2 / 3) : ℝ) * (c ^ (2 / 3 : ℝ) * langerMu ^ 2) = langerMu ^ 2 := by
    rw [← mul_assoc, ← Real.rpow_add hc]; simp
  rw [this]

/-- `√ũ = c^{1/3} μ 𝗆(ζ)` for the saddle `ζ` (`Re ζ > 0`). -/
lemma sqrt_langerUtilde_eq {c : ℝ} (hc : 0 < c) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 0.035) (hre : 0 < ζ.re) :
    (langerUtilde etaC c (ζ ^ 2)) ^ (1 / 2 : ℂ) = ((c ^ (1 / 3 : ℝ) * langerMu : ℝ) : ℂ) * mMap etaC ζ := by
  have hu : ‖ζ ^ 2‖ ≤ 0.035 ^ 2 := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hζ 2
  have := langerUtilde_sqrt langerEta_etaC hc (sq_mem_slitPlane hre) hu
  rwa [saddleRoot_sq_of_re_pos hre] at this

/-- **`u1cl:langer`, first display.**  For the saddle `ζ` (`‖ζ‖ ≤ 0.035`, `Re ζ > 0`) with `ũ = ũ(ζ²)` and
`|ũ| ≤ A_c²`: `ζ = κ_ζ c^{-1/3} √ũ q(ũ c^{-2/3})` (principal root). -/
theorem langer_zeta_eq {c r0 : ℝ} (hc : 0 < c) (hr0 : r0 ≤ 1e-4) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 0.035) (hre : 0 < ζ.re)
    (hA : ‖langerUtilde etaC c (ζ ^ 2)‖ ≤ langerAc2 r0 c) :
    ζ = ((langerKappaZeta * c ^ (-(1 / 3) : ℝ) : ℝ) : ℂ) * (langerUtilde etaC c (ζ ^ 2)) ^ (1 / 2 : ℂ) *
      langerQ (((c ^ (-(2 / 3) : ℝ) : ℝ) : ℂ) * langerUtilde etaC c (ζ ^ 2)) := by
  rw [langerUtilde_arg_eq hc, sqrt_langerUtilde_eq hc hζ hre]
  have hq := zeta_eq_mMap_mul_q hζ (norm_chartM_lt_of_Ac2 hc hr0 hA)
  have hk : (langerKappaZeta * c ^ (-(1 / 3) : ℝ)) * (c ^ (1 / 3 : ℝ) * langerMu) = 1 := by
    rw [kappaZeta_mul_rpow hc]
    have h1 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
    have h2 := langerMu_pos
    field_simp
  have hkc : (((langerKappaZeta * c ^ (-(1 / 3) : ℝ) : ℝ) : ℂ)) * (((c ^ (1 / 3 : ℝ) * langerMu : ℝ) : ℂ)) = 1 := by
    rw [← Complex.ofReal_mul, hk]; simp
  calc ζ = mMap etaC ζ * langerQ (((langerMu ^ 2 : ℝ) : ℂ) * chartM etaC (ζ ^ 2)) := hq
    _ = _ := by
      rw [← one_mul (mMap etaC ζ * _), ← hkc]; ring

/-- **`u1cl:langer`, angle comparability.**  For `ũ = a'² e^{i(π - 2φ')}`, `a' > 0`, `φ' ∈ (0, π/2]`:
`|ζ| = κ_ζ c^{-1/3} a' (1 + δ₁)`, `Re ζ = κ_ζ c^{-1/3} a' sin φ' (1 + δ₂)`, `|δ_i| ≤ 10⁻³`. -/
theorem langer_angles {c a φ : ℝ} (hc : 0 < c) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 0.035) (hre : 0 < ζ.re)
    (ha : 0 < a) (hφ : 0 < φ) (hφ' : φ ≤ π / 2)
    (hũ : langerUtilde etaC c (ζ ^ 2) = ((a ^ 2 : ℝ) : ℂ) * Complex.exp (((π - 2 * φ : ℝ) : ℂ) * Complex.I)) :
    ∃ δ₁ δ₂ : ℝ, |δ₁| ≤ 1e-3 ∧ |δ₂| ≤ 1e-3 ∧
      ‖ζ‖ = langerKappaZeta * c ^ (-(1 / 3) : ℝ) * a * (1 + δ₁) ∧
      ζ.re = langerKappaZeta * c ^ (-(1 / 3) : ℝ) * a * Real.sin φ * (1 + δ₂) := by
  have hu : ‖ζ ^ 2‖ ≤ 0.035 ^ 2 := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hζ 2
  have hgeo := hankel_saddle_geom hc (sq_mem_slitPlane hre) hu rfl
  rw [saddleRoot_sq_of_re_pos hre] at hgeo
  obtain ⟨g1, g2, g3, g4⟩ := hgeo
  set w : ℂ := ((a : ℝ) : ℂ) * Complex.exp (((π / 2 - φ : ℝ) : ℂ) * Complex.I) with hw
  have hsinpos : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ (by linarith [Real.pi_pos])
  have hwre : w.re = a * Real.sin φ := by
    rw [hw, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_two_sub]
  have hwsq : w ^ 2 = langerUtilde etaC c (ζ ^ 2) := by
    rw [hũ, hw, mul_pow, ← Complex.exp_nat_mul]
    congr 1
    · push_cast; ring
    · congr 1; push_cast; ring
  have hsqrt : (langerUtilde etaC c (ζ ^ 2)) ^ (1 / 2 : ℂ) = w := by
    rw [← hwsq]; exact cpow_half_sq_of_re_pos (by rw [hwre]; positivity)
  have hwn : ‖w‖ = a := by
    rw [hw, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    have : ‖Complex.exp (((π / 2 - φ : ℝ) : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    rw [this, mul_one]
  have hnorm : ‖langerUtilde etaC c (ζ ^ 2)‖ ^ (1 / 2 : ℝ) = a := by
    rw [← norm_saddleRoot]; unfold saddleRoot; rw [hsqrt, hwn]
  rw [hnorm] at g1 g2
  rw [hsqrt, hwre] at g3 g4
  set kμ := c ^ (1 / 3 : ℝ) * langerMu with hkμ
  have hk : 0 < kμ := mul_pos (Real.rpow_pos_of_pos hc _) langerMu_pos
  have hkz : langerKappaZeta * c ^ (-(1 / 3) : ℝ) = 1 / kμ := kappaZeta_mul_rpow hc
  rw [hkz]
  have hσ : 0 < ζ.re := hre
  have hζ0 : 0 < ‖ζ‖ := by
    have := Complex.abs_re_le_norm ζ
    rw [abs_of_pos hre] at this; linarith
  have hP : 0 < a * Real.sin φ := by positivity
  refine ⟨‖ζ‖ * kμ / a - 1, ζ.re * kμ / (a * Real.sin φ) - 1, ?_, ?_, ?_, ?_⟩
  · rw [abs_le]; constructor
    · have : 0.999 ≤ ‖ζ‖ * kμ / a := by
        rw [le_div_iff₀ ha]; nlinarith
      linarith
    · have : ‖ζ‖ * kμ / a ≤ 1.001 := by
        rw [div_le_iff₀ ha]; nlinarith
      linarith
  · rw [abs_le]; constructor
    · have : 0.999 ≤ ζ.re * kμ / (a * Real.sin φ) := by
        rw [le_div_iff₀ hP]; nlinarith
      linarith
    · have : ζ.re * kμ / (a * Real.sin φ) ≤ 1.001 := by
        rw [div_le_iff₀ hP]; nlinarith
      linarith
  · field_simp; ring
  · field_simp; ring

end Main

section Band

/-- The principal square root of `-s²` is `+ i s` (`s > 0`): the boundary value from `Im > 0`. -/
lemma cpow_half_sq_imag {s : ℝ} (hs : 0 < s) : (((s : ℂ) * Complex.I) ^ 2) ^ (1 / 2 : ℂ) = (s : ℂ) * Complex.I := by
  have hw0 : ((s : ℂ) * Complex.I) ≠ 0 := mul_ne_zero (by exact_mod_cast hs.ne') Complex.I_ne_zero
  have harg : Complex.arg ((s : ℂ) * Complex.I) = π / 2 := by
    rw [Complex.arg_real_mul _ hs, Complex.arg_I]
  have him : (Complex.log ((s : ℂ) * Complex.I) * (2 : ℂ)).im = π := by
    rw [Complex.mul_im, Complex.log_im, harg]; simp
  have hcm := Complex.cpow_mul (x := (s : ℂ) * Complex.I) (y := (2 : ℂ)) (z := (1 / 2 : ℂ))
    (by rw [him]; linarith [Real.pi_pos]) (by rw [him])
  rw [show (2 : ℂ) * (1 / 2) = 1 by norm_num, Complex.cpow_one] at hcm
  rw [Complex.cpow_two] at hcm
  exact hcm.symm

/-- On the imaginary axis `g(iτ) = -m(τ)` with `m(τ) = log((πτ/2)/tanh(πτ/2))` (`0 < τ ≤ 0.035`). -/
theorem gSer_imag {τ : ℝ} (hτ : 0 < τ) (hτn : τ ≤ 0.035) :
    gSer etaC ((τ : ℂ) * Complex.I) = -((langerMband τ : ℝ) : ℂ) := by
  set p : ℂ := (τ : ℂ) * Complex.I with hp
  set y : ℝ := π * τ / 2 with hy
  have hypos : 0 < y := by rw [hy]; positivity
  have hpn : ‖p‖ < 1 := by
    rw [hp, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos hτ]; linarith
  have hpn35 : ‖p‖ ≤ 0.035 := by
    rw [hp, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos hτ]; exact hτn
  have hπp : π * p / 2 = (y : ℂ) * Complex.I := by rw [hp, hy]; push_cast; ring
  have hcos : Complex.cos ((y : ℂ) * Complex.I) ≠ 0 := by
    rw [Complex.cos_mul_I, ← Complex.ofReal_cosh]
    exact_mod_cast (Real.cosh_pos y).ne'
  -- `G p = tanh y / y`
  have hG : Complex.tan (π * p / 2) / (π * p / 2) = ((Real.tanh y / y : ℝ) : ℂ) := by
    rw [hπp, Complex.tan_mul_I]
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hypos.ne'
    push_cast
    field_simp
  -- limit from the right half plane
  have hseq : Tendsto (fun n : ℕ => (((1 / ((n : ℝ) + 1) : ℝ)) : ℂ) + p) atTop (𝓝 p) := by
    have h1 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h2 := ((Complex.continuous_ofReal.tendsto 0).comp h1).add_const p
    simpa using h2
  have hFc : ContinuousAt (fun z => Complex.exp (gSer etaC z)) p :=
    ((hasDerivAt_gSer langerEta_etaC hpn).continuousAt).cexp
  have hπne : π * p / 2 ≠ 0 := by
    rw [hπp]; exact mul_ne_zero (by exact_mod_cast hypos.ne') Complex.I_ne_zero
  have hGc : ContinuousAt (fun z : ℂ => Complex.tan (π * z / 2) / (π * z / 2)) p := by
    have h1 : ContinuousAt (fun z : ℂ => π * z / 2) p := by fun_prop
    have h2 : ContinuousAt Complex.tan (π * p / 2) :=
      Complex.continuousAt_tan.2 (by rw [hπp]; exact hcos)
    exact (h2.comp (f := fun z : ℂ => π * z / 2) h1).div h1 hπne
  have hev : ∀ᶠ n : ℕ in atTop, Complex.exp (gSer etaC ((((1 / ((n : ℝ) + 1) : ℝ)) : ℂ) + p)) =
      Complex.tan (π * ((((1 / ((n : ℝ) + 1) : ℝ)) : ℂ) + p) / 2) / (π * ((((1 / ((n : ℝ) + 1) : ℝ)) : ℂ) + p) / 2) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hq : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hq2 : 1 / ((n : ℝ) + 1) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have hmem : (((1 / ((n : ℝ) + 1) : ℝ)) : ℂ) + p ∈ halfDisc := by
      refine ⟨?_, ?_⟩
      · calc ‖(((1 / ((n : ℝ) + 1) : ℝ)) : ℂ) + p‖ ≤ ‖(((1 / ((n : ℝ) + 1) : ℝ)) : ℂ)‖ + ‖p‖ := norm_add_le _ _
          _ < 1 := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]; linarith [hpn35]
      · rw [hp]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
        exact hq
    exact (langerU_eq_exp_gSer hmem).symm
  have hlim := tendsto_nhds_unique (hFc.tendsto.comp hseq)
    ((hGc.tendsto.comp hseq).congr' (hev.mono fun n hn => hn.symm))
  have hexp : Complex.exp (gSer etaC p) = ((Real.tanh y / y : ℝ) : ℂ) := by
    rw [← hG]; exact hlim
  -- `g(iτ)` is real
  have hsq : p ^ 2 = ((-(τ ^ 2) : ℝ) : ℂ) := by
    rw [hp, mul_pow, Complex.I_sq]; push_cast; ring
  have hreal : gSer etaC p = ((-(τ ^ 2) * ∑' j : ℕ, (etaC j / ((j : ℝ) + 1)) * (-(τ ^ 2)) ^ j : ℝ) : ℂ) := by
    unfold gSer
    rw [hsq, psW_ofReal]; push_cast; ring
  set r : ℝ := -(τ ^ 2) * ∑' j : ℕ, (etaC j / ((j : ℝ) + 1)) * (-(τ ^ 2)) ^ j with hr
  rw [hreal, ← Complex.ofReal_exp] at hexp
  have hexp' : Real.exp r = Real.tanh y / y := by exact_mod_cast hexp
  have htanh : 0 < Real.tanh y := by
    rw [Real.tanh_eq_sinh_div_cosh]; exact div_pos (Real.sinh_pos_iff.2 hypos) (Real.cosh_pos y)
  have hrlog : r = Real.log (Real.tanh y / y) := by
    rw [← hexp', Real.log_exp]
  have hm : langerMband τ = -r := by
    unfold langerMband
    rw [hrlog, ← Real.log_inv, inv_div]
  rw [hreal, hm]; push_cast; ring

/-- **`u1cl:langer`, band clause.**  On the band, `ζ_+ = iτ₀` with `τ₀ ∈ (0, 0.035]`, `ũ = -vt < 0`
(`vt = (c^{1/3} μ 𝗆(iτ₀)/i)²`) and `τ₀ = κ_ζ c^{-1/3} √vt q(-vt c^{-2/3}) = κ_ζ c^{-1/3} √vt (1 + δ₁)`,
`|δ₁| ≤ 10⁻³`; the principal square root of `-vt` is `+i√vt`, which is the limit from `Im ũ > 0`. -/
theorem langer_band {c r0 τ0 : ℝ} (hc : 0 < c) (hr0 : r0 ≤ 1e-4) (hτ : 0 < τ0) (hτn : τ0 ≤ 0.035)
    (hA : ‖langerUtilde etaC c (((τ0 : ℂ) * Complex.I) ^ 2)‖ ≤ langerAc2 r0 c) :
    ∃ vt : ℝ, 0 < vt ∧ langerUtilde etaC c (((τ0 : ℂ) * Complex.I) ^ 2) = -(vt : ℂ) ∧
      (-(vt : ℂ)) ^ (1 / 2 : ℂ) = (Real.sqrt vt : ℂ) * Complex.I ∧
      (τ0 : ℂ) = ((langerKappaZeta * c ^ (-(1 / 3) : ℝ) * Real.sqrt vt : ℝ) : ℂ) *
        langerQ (((-vt * c ^ (-(2 / 3) : ℝ) : ℝ) : ℂ)) ∧
      ∃ δ₁ : ℝ, |δ₁| ≤ 1e-3 ∧ τ0 = langerKappaZeta * c ^ (-(1 / 3) : ℝ) * Real.sqrt vt * (1 + δ₁) := by
  set ζ : ℂ := (τ0 : ℂ) * Complex.I with hζdef
  have hζn : ‖ζ‖ = τ0 := by
    rw [hζdef, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos hτ]
  have hζ : ‖ζ‖ ≤ 0.035 := by rw [hζn]; exact hτn
  have hv := norm_chartM_lt_of_Ac2 hc hr0 hA
  have hq := zeta_eq_mMap_mul_q hζ hv
  set m := mMap etaC ζ with hm
  have hre0 : m.re = 0 := re_mMap_imag langerEta_etaC (τ := τ0) (by rw [abs_of_pos hτ]; exact hτn)
  have hdist := norm_mMap_sub_le langerEta_etaC hζ
  rw [← hm, hζn] at hdist
  set t : ℝ := m.im with ht
  have hmt : m = (t : ℂ) * Complex.I := by apply Complex.ext <;> simp [hre0, ht]
  have hζim : ζ.im = τ0 := by rw [hζdef]; simp
  have him : |t - τ0| ≤ 9e-4 * τ0 := by
    have h1 : |(m - ζ).im| ≤ ‖m - ζ‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, hζim] at h1
    exact h1.trans hdist
  have hb := abs_le.1 him
  have htpos : 0 < t := by nlinarith
  have hk : 0 < c ^ (1 / 3 : ℝ) * langerMu := mul_pos (Real.rpow_pos_of_pos hc _) langerMu_pos
  set vt : ℝ := (c ^ (1 / 3 : ℝ) * langerMu * t) ^ 2 with hvt
  have hvtpos : 0 < vt := by rw [hvt]; positivity
  have hsq : Real.sqrt vt = c ^ (1 / 3 : ℝ) * langerMu * t := by
    rw [hvt]; exact Real.sqrt_sq (by positivity)
  have hũ : langerUtilde etaC c (ζ ^ 2) = -(vt : ℂ) := by
    have e1 : chartM etaC (ζ ^ 2) = m ^ 2 := (mMap_sq etaC ζ).symm
    unfold langerUtilde
    rw [e1, hmt, hvt]
    have : ((c ^ (2 / 3 : ℝ) * langerMu ^ 2 : ℝ) : ℂ) = (((c ^ (1 / 3 : ℝ) * langerMu : ℝ)) : ℂ) ^ 2 := by
      have h : (c ^ (1 / 3 : ℝ)) ^ 2 = c ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num
      rw [← Complex.ofReal_pow, mul_pow, h]
    rw [this]; push_cast
    linear_combination (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (langerMu : ℂ) * (t : ℂ)) ^ 2 * Complex.I_sq
  have harg : ((c ^ (-(2 / 3) : ℝ) : ℝ) : ℂ) * langerUtilde etaC c (ζ ^ 2) = (((-vt * c ^ (-(2 / 3) : ℝ) : ℝ)) : ℂ) := by
    rw [hũ]; push_cast; ring
  have hkz : langerKappaZeta * c ^ (-(1 / 3) : ℝ) * Real.sqrt vt = t := by
    rw [hsq, kappaZeta_mul_rpow hc]
    have h2 := langerMu_pos
    field_simp
  refine ⟨vt, hvtpos, hũ, ?_, ?_, ?_⟩
  · have hsq' : -(vt : ℂ) = (((Real.sqrt vt : ℝ) : ℂ) * Complex.I) ^ 2 := by
      rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt hvtpos.le]; ring
    rw [hsq']; exact cpow_half_sq_imag (Real.sqrt_pos.2 hvtpos)
  · have e := langerUtilde_arg_eq hc (ζ ^ 2)
    rw [hkz]
    have h3 : (ζ : ℂ) = (τ0 : ℂ) * Complex.I := hζdef
    have : (τ0 : ℂ) * Complex.I = (t : ℂ) * Complex.I * langerQ (((-vt * c ^ (-(2 / 3) : ℝ) : ℝ) : ℂ)) := by
      rw [← hmt, ← harg, e, ← h3]; exact hq
    exact mul_right_cancel₀ Complex.I_ne_zero (by rw [this]; ring)
  · refine ⟨τ0 / t - 1, ?_, ?_⟩
    · rw [abs_le]; constructor
      · have : 0.999 ≤ τ0 / t := by rw [le_div_iff₀ htpos]; nlinarith
        linarith
      · have : τ0 / t ≤ 1.001 := by rw [div_le_iff₀ htpos]; nlinarith
        linarith
    · rw [hkz]; field_simp; ring

/-- **`u1cl:langer`, band identity.**  If `g(iτ₀) = -log(π²ξ)` (the saddle equation `g(ζ_+) = s`,
`s = -log π²ξ`, at `ζ_+ = iτ₀`) then `m(τ₀) = log(π²ξ)`. -/
theorem langer_band_log {τ0 ξ : ℝ} (hτ : 0 < τ0) (hτn : τ0 ≤ 0.035)
    (hg : gSer etaC ((τ0 : ℂ) * Complex.I) = -((Real.log (π ^ 2 * ξ) : ℝ) : ℂ)) :
    langerMband τ0 = Real.log (π ^ 2 * ξ) := by
  rw [gSer_imag hτ hτn] at hg
  have := neg_inj.1 hg
  exact_mod_cast this

end Band

section Assembly

/-- **The paper's saddle feeds the lemma.**  For a chart point `y = y(w)`, `w = π²ξ - 1`, with
`‖y‖ ≤ π² r₀ / 2` (i.e. `|ũ| ≤ A_c²`; `ũ = c^{2/3} κ y`), the saddle `ζ_+ = saddleRoot u` of `chart_saddle_data`
satisfies `‖ζ_+‖ ≤ 0.035`, `Re ζ_+ > 0`, `-g(ζ_+) = log π²ξ` (`= log(1 + w)`), `ũ(ζ_+²) = c^{2/3} κ y`, and the
first display of `u1cl:langer` holds. -/
theorem langer_zeta_eq_chart {c r0 : ℝ} (hc : 0 < c) (hr0 : r0 ≤ 1e-4) {y : ℂ} (hy : ‖y‖ ≤ π ^ 2 * r0 / 2)
    (hcut : ¬ ((((c ^ (2 / 3 : ℝ) * langerKappa : ℝ) : ℂ) * y).im = 0 ∧
      (((c ^ (2 / 3 : ℝ) * langerKappa : ℝ) : ℂ) * y).re ≤ 0)) :
    ∃ ζ : ℂ, ‖ζ‖ ≤ 0.035 ∧ 0 < ζ.re ∧ -(gSer etaC ζ) = Complex.log (1 + chartYinv etaC y) ∧
      langerUtilde etaC c (ζ ^ 2) = ((c ^ (2 / 3 : ℝ) * langerKappa : ℝ) : ℂ) * y ∧
      ζ = ((langerKappaZeta * c ^ (-(1 / 3) : ℝ) : ℝ) : ℂ) * (langerUtilde etaC c (ζ ^ 2)) ^ (1 / 2 : ℂ) *
        langerQ (((c ^ (-(2 / 3) : ℝ) : ℝ) : ℂ) * langerUtilde etaC c (ζ ^ 2)) := by
  have hy' : ‖y‖ ≤ 4.94e-4 := by
    refine hy.trans ?_
    have h1 : π ^ 2 < 9.88 := by nlinarith [Real.pi_lt_d4, Real.pi_pos]
    have h2 : 0 ≤ r0 ∨ r0 < 0 := le_or_gt 0 r0
    rcases h2 with h2 | h2
    · nlinarith
    · nlinarith [Real.pi_pos]
  obtain ⟨u, hu, hun, hũ, hg⟩ := chart_saddle_data langerEta_etaC hc hy' hcut
  set ζ := saddleRoot u with hζ
  have hre : 0 < ζ.re := re_saddleRoot_pos hu
  have hζn : ‖ζ‖ ≤ 0.035 := norm_saddleRoot_le hun
  have hsq : ζ ^ 2 = u := saddleRoot_sq u
  have hũ' : langerUtilde etaC c (ζ ^ 2) = ((c ^ (2 / 3 : ℝ) * langerKappa : ℝ) : ℂ) * y := by
    rw [hsq]; exact hũ
  refine ⟨ζ, hζn, hre, hg, hũ', ?_⟩
  have hA : ‖langerUtilde etaC c (ζ ^ 2)‖ ≤ langerAc2 r0 c := by
    rw [hũ', norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (Real.rpow_pos_of_pos hc _) langerKappa_pos)]
    unfold langerAc2
    rw [hankelBeta1_eq_kappa]
    have hk := Real.rpow_pos_of_pos hc (2 / 3 : ℝ)
    have hκ := langerKappa_pos
    have : c ^ (2 / 3 : ℝ) * langerKappa * ‖y‖ ≤ c ^ (2 / 3 : ℝ) * langerKappa * (π ^ 2 * r0 / 2) :=
      mul_le_mul_of_nonneg_left hy (by positivity)
    nlinarith
  exact langer_zeta_eq hc hr0 hζn hre hA

/-- **`u1cl:langer` (Lemma L.2, chart comparability), packaged as in the paper.**  There is a function `q`
(`langerQ`), analytic with real Taylor coefficients on `|w| < 5·10⁻⁴`, `q(0) = 1`, `|q(w) - 1| ≤ C_q |w|`
(`C_q = 1/2`), such that for the saddle `ζ_+` (`‖ζ_+‖ ≤ 0.035`, `Re ζ_+ > 0`), `ũ = ũ(ζ_+²)`, `|ũ| ≤ A_c²`,
`c > 0`, `r₀ ≤ 10⁻⁴`: the first display (`ζ_+ = κ_ζ c^{-1/3} √ũ q(ũ c^{-2/3})`); the angle comparability for
`ũ = a'² e^{i(π - 2φ')}` (`|δ₁|, |δ₂| ≤ 10⁻³`); the band clause `ζ_+ = iτ₀`, `τ₀ = κ_ζ c^{-1/3} √ṽ q(-ṽ c^{-2/3})`
with `|δ₁| ≤ 10⁻³`; and `m(τ₀) = log(π²ξ)` whenever `g(iτ₀) = -log(π²ξ)`.

Scope: `κ_ζ = 2/c_s` literally (`langerKappaZeta`); the chart is the actual Dirichlet-eta chart `etaC`; the
`|δ_i| ≤ 10⁻³` and `‖𝗆' - 1‖ ≤ 9·10⁻⁴` are the TeX constants (`gt:7.7b` (ii) in Lean is `norm_mMapD_sub_one_le`
with the same `9·10⁻⁴`).  Limits: the saddle is a free variable with `‖ζ‖ ≤ 0.035` (the paper has
`≤ 0.03467`; see `langer_zeta_eq_chart` for the chart-point version), and the band `ũ = -ṽ` is formulated at
`ζ = iτ₀` (principal root `(-ṽ)^{1/2} = +i√ṽ`, `cpow_half_sq_imag`, i.e. the limit from `Im ũ > 0`), not as a
limit. -/
theorem u1cl_langer :
    ∃ q : ℂ → ℂ,
      AnalyticOnNhd ℂ q (ball (0 : ℂ) 5e-4) ∧
      (∃ a : ℕ → ℝ, ∀ w ∈ ball (0 : ℂ) 5e-4, HasSum (fun j : ℕ => (a j : ℂ) * w ^ j) (q w)) ∧
      q 0 = 1 ∧ (∀ w ∈ ball (0 : ℂ) 5e-4, ‖q w - 1‖ ≤ 1 / 2 * ‖w‖) ∧
      (∀ r0 : ℝ, r0 ≤ 1e-4 → hankelBeta1 / 2 * r0 < 5e-4) ∧
      (∀ (c r0 : ℝ), 0 < c → r0 ≤ 1e-4 → ∀ (ζ : ℂ), ‖ζ‖ ≤ 0.035 → 0 < ζ.re →
        ‖langerUtilde etaC c (ζ ^ 2)‖ ≤ langerAc2 r0 c →
        ζ = ((langerKappaZeta * c ^ (-(1 / 3) : ℝ) : ℝ) : ℂ) * (langerUtilde etaC c (ζ ^ 2)) ^ (1 / 2 : ℂ) *
          q (((c ^ (-(2 / 3) : ℝ) : ℝ) : ℂ) * langerUtilde etaC c (ζ ^ 2))) ∧
      (∀ (c a φ : ℝ), 0 < c → ∀ (ζ : ℂ), ‖ζ‖ ≤ 0.035 → 0 < ζ.re → 0 < a → 0 < φ → φ ≤ π / 2 →
        langerUtilde etaC c (ζ ^ 2) = ((a ^ 2 : ℝ) : ℂ) * Complex.exp (((π - 2 * φ : ℝ) : ℂ) * Complex.I) →
        ∃ δ₁ δ₂ : ℝ, |δ₁| ≤ 1e-3 ∧ |δ₂| ≤ 1e-3 ∧
          ‖ζ‖ = langerKappaZeta * c ^ (-(1 / 3) : ℝ) * a * (1 + δ₁) ∧
          ζ.re = langerKappaZeta * c ^ (-(1 / 3) : ℝ) * a * Real.sin φ * (1 + δ₂)) ∧
      (∀ (c r0 τ0 : ℝ), 0 < c → r0 ≤ 1e-4 → 0 < τ0 → τ0 ≤ 0.035 →
        ‖langerUtilde etaC c (((τ0 : ℂ) * Complex.I) ^ 2)‖ ≤ langerAc2 r0 c →
        ∃ vt : ℝ, 0 < vt ∧ langerUtilde etaC c (((τ0 : ℂ) * Complex.I) ^ 2) = -(vt : ℂ) ∧
          (-(vt : ℂ)) ^ (1 / 2 : ℂ) = (Real.sqrt vt : ℂ) * Complex.I ∧
          (τ0 : ℂ) = ((langerKappaZeta * c ^ (-(1 / 3) : ℝ) * Real.sqrt vt : ℝ) : ℂ) *
            q (((-vt * c ^ (-(2 / 3) : ℝ) : ℝ) : ℂ)) ∧
          ∃ δ₁ : ℝ, |δ₁| ≤ 1e-3 ∧ τ0 = langerKappaZeta * c ^ (-(1 / 3) : ℝ) * Real.sqrt vt * (1 + δ₁)) ∧
      (∀ (τ0 ξ : ℝ), 0 < τ0 → τ0 ≤ 0.035 →
        gSer etaC ((τ0 : ℂ) * Complex.I) = -((Real.log (π ^ 2 * ξ) : ℝ) : ℂ) →
        Real.log ((π * τ0 / 2) / Real.tanh (π * τ0 / 2)) = Real.log (π ^ 2 * ξ)) := by
  obtain ⟨h1, h2, h3, h4⟩ := langerQ_properties
  exact ⟨langerQ, h1, h2, h3, h4, fun _ hr => langerAc2_radius_lt hr,
    fun _ _ hc hr _ hζ hre hA => langer_zeta_eq hc hr hζ hre hA,
    fun _ _ _ hc _ hζ hre ha hφ hφ' hũ => langer_angles hc hζ hre ha hφ hφ' hũ,
    fun _ _ _ hc hr hτ hτn hA => langer_band hc hr hτ hτn hA,
    fun _ _ hτ hτn hg => langer_band_log hτ hτn hg⟩

end Assembly

/-- info: 'FormalResearch.SignUncertainty.exists_unique_chartM_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_unique_chartM_root

/-- info: 'FormalResearch.SignUncertainty.analyticAt_chartMinv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms analyticAt_chartMinv

/-- info: 'FormalResearch.SignUncertainty.exists_real_taylor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_real_taylor

/-- info: 'FormalResearch.SignUncertainty.norm_chartQ_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_chartQ_sub_one_le

/-- info: 'FormalResearch.SignUncertainty.langerQ_properties' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms langerQ_properties

/-- info: 'FormalResearch.SignUncertainty.langer_zeta_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms langer_zeta_eq

/-- info: 'FormalResearch.SignUncertainty.langer_angles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms langer_angles

/-- info: 'FormalResearch.SignUncertainty.gSer_imag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gSer_imag

/-- info: 'FormalResearch.SignUncertainty.langer_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms langer_band

/-- info: 'FormalResearch.SignUncertainty.langer_band_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms langer_band_log

/-- info: 'FormalResearch.SignUncertainty.langer_zeta_eq_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms langer_zeta_eq_chart

/-- info: 'FormalResearch.SignUncertainty.u1cl_langer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms u1cl_langer

end FormalResearch.SignUncertainty
