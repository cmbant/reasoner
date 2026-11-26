module

public import FormalResearch.SignUncertainty.MiddleBandPointwise

/-!
# GT.2a: scale-invariant cutoffs and the Leibniz bound for `cutoff × amplitude`

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, proof of `cegt:GT2a` ("each cutoff is smooth, with its first two derivatives included in the
corresponding bound").

* `cutoff_profile`: a fixed even `C³` profile `ϑ`, `ϑ = 1` on `|t| ≤ 1`, `ϑ = 0` on `|t| ≥ 2`, `0 ≤ ϑ ≤ 1`, with absolute bounds on `ϑ', ϑ''`.
* `IsCut ζ K0 K1 K2`: `ζ ∈ C²`, `|ζ| ≤ K0`, `|ζ'(u)||u| ≤ K1`, `|ζ''(u)|u² ≤ K2` for `u ≠ 0` (scale-invariant derivative bounds).
* `IsCut.scale`: `ϑ(·/R)` is a cutoff with constants `(1, 2K₁, 4K₂)`; `IsCut.sub`, `IsCut.comp_mul`: differences and dilates.
* `leibniz_cut`: if `‖g^{(r)}(x)‖ ≤ G |x|^{-s-r}` (`r ≤ 2`) at `x ≠ 0` and `ζ` is a cutoff, then `ζ g` satisfies the same with constants
  `K0`, `K1 + K0`, `K2 + 2K1 + K0`.

Status: proved, unconditional.
-/

@[expose] public section

open Set

namespace FormalResearch.SignUncertainty

/-- A fixed even smooth cutoff profile. -/
lemma cutoff_profile : ∃ ϑ : ℝ → ℝ, ContDiff ℝ 3 ϑ ∧ (∀ t, 0 ≤ ϑ t ∧ ϑ t ≤ 1) ∧ (∀ t, |t| ≤ 1 → ϑ t = 1) ∧
    (∀ t, 2 ≤ |t| → ϑ t = 0) ∧ ∃ K1 K2 : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧ (∀ t, |deriv ϑ t| ≤ K1) ∧ (∀ t, |deriv (deriv ϑ) t| ≤ K2) := by
  let bump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hc3 : ContDiff ℝ 3 bump := bump.contDiff
  have hcs : HasCompactSupport bump := bump.hasCompactSupport
  have hc2' : ContDiff ℝ (2 + 1) bump := hc3
  have hd1 : ContDiff ℝ 2 (deriv bump) := hc2'.deriv'
  have hd1c : Continuous (deriv bump) := hd1.continuous
  have hd2 : ContDiff ℝ 1 (deriv (deriv bump)) := hd1.deriv'
  have hd2c : Continuous (deriv (deriv bump)) := hd2.continuous
  obtain ⟨K1, hK1⟩ := hd1c.bounded_above_of_compact_support hcs.deriv
  obtain ⟨K2, hK2⟩ := hd2c.bounded_above_of_compact_support hcs.deriv.deriv
  refine ⟨bump, hc3, fun t => ⟨bump.nonneg, bump.le_one⟩, ?_, ?_, K1, K2,
    le_trans (norm_nonneg _) (hK1 0), le_trans (norm_nonneg _) (hK2 0), fun t => ?_, fun t => ?_⟩
  · intro t ht
    exact bump.one_of_mem_closedBall (by rw [Metric.mem_closedBall, Real.dist_0_eq_abs]; exact ht)
  · intro t ht
    exact bump.zero_of_le_dist (by rw [Real.dist_0_eq_abs]; exact ht)
  · rw [← Real.norm_eq_abs]; exact hK1 t
  · rw [← Real.norm_eq_abs]; exact hK2 t

/-- Scale-invariant cutoff class: `|ζ| ≤ K0`, `|ζ'(u)| |u| ≤ K1`, `|ζ''(u)| u² ≤ K2` (`u ≠ 0`), `ζ ∈ C²`. -/
structure IsCut (ζ : ℝ → ℝ) (K0 K1 K2 : ℝ) : Prop where
  contDiff : ContDiff ℝ 2 ζ
  bound0 : ∀ u, |ζ u| ≤ K0
  bound1 : ∀ u, u ≠ 0 → |deriv ζ u| * |u| ≤ K1
  bound2 : ∀ u, u ≠ 0 → |deriv (deriv ζ) u| * u ^ 2 ≤ K2

lemma IsCut.mono {ζ : ℝ → ℝ} {K0 K1 K2 K0' K1' K2' : ℝ} (h : IsCut ζ K0 K1 K2) (h0 : K0 ≤ K0') (h1 : K1 ≤ K1') (h2 : K2 ≤ K2') :
    IsCut ζ K0' K1' K2' :=
  ⟨h.contDiff, fun u => (h.bound0 u).trans h0, fun u hu => (h.bound1 u hu).trans h1, fun u hu => (h.bound2 u hu).trans h2⟩

lemma IsCut.sub {ζ η : ℝ → ℝ} {K0 K1 K2 L0 L1 L2 : ℝ} (hζ : IsCut ζ K0 K1 K2) (hη : IsCut η L0 L1 L2) :
    IsCut (fun u => ζ u - η u) (K0 + L0) (K1 + L1) (K2 + L2) := by
  have hζd : Differentiable ℝ ζ := hζ.contDiff.differentiable (by norm_num)
  have hηd : Differentiable ℝ η := hη.contDiff.differentiable (by norm_num)
  have hζ1' : ContDiff ℝ 1 (deriv ζ) := hζ.contDiff.deriv'
  have hη1' : ContDiff ℝ 1 (deriv η) := hη.contDiff.deriv'
  have hζ1 : Differentiable ℝ (deriv ζ) := hζ1'.differentiable (by norm_num)
  have hη1 : Differentiable ℝ (deriv η) := hη1'.differentiable (by norm_num)
  have e1 : deriv (fun u => ζ u - η u) = fun u => deriv ζ u - deriv η u := funext fun u => deriv_sub (hζd u) (hηd u)
  have e2 : deriv (deriv (fun u => ζ u - η u)) = fun u => deriv (deriv ζ) u - deriv (deriv η) u := by
    rw [e1]; exact funext fun u => deriv_sub (hζ1 u) (hη1 u)
  refine ⟨hζ.contDiff.sub hη.contDiff, fun u => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · exact (abs_sub _ _).trans (add_le_add (hζ.bound0 u) (hη.bound0 u))
  · rw [e1]
    have := hζ.bound1 u hu; have := hη.bound1 u hu
    calc |deriv ζ u - deriv η u| * |u| ≤ (|deriv ζ u| + |deriv η u|) * |u| := by gcongr; exact abs_sub _ _
      _ = |deriv ζ u| * |u| + |deriv η u| * |u| := by ring
      _ ≤ _ := by linarith
  · rw [e2]
    have := hζ.bound2 u hu; have := hη.bound2 u hu
    calc |deriv (deriv ζ) u - deriv (deriv η) u| * u ^ 2 ≤ (|deriv (deriv ζ) u| + |deriv (deriv η) u|) * u ^ 2 := by
          gcongr; exact abs_sub _ _
      _ = |deriv (deriv ζ) u| * u ^ 2 + |deriv (deriv η) u| * u ^ 2 := by ring
      _ ≤ _ := by linarith

/-- Dilation of the profile: `ϑ(u/R)` is a cutoff with constants `(1, 2K₁, 4K₂)` (`|u| ≤ 2R` on the support of the derivatives, so `1/R ≤ 2/|u|`
is not needed: `|u|/R ≤ 2`). -/
lemma cutoff_scale {ϑ : ℝ → ℝ} {K1 K2 : ℝ} (hϑ : ContDiff ℝ 3 ϑ) (h01 : ∀ t, 0 ≤ ϑ t ∧ ϑ t ≤ 1)
    (h2 : ∀ t, 2 ≤ |t| → ϑ t = 0) (hK1 : ∀ t, |deriv ϑ t| ≤ K1) (hK2 : ∀ t, |deriv (deriv ϑ) t| ≤ K2) {R : ℝ} (hR : 0 < R) :
    IsCut (fun u => ϑ (u / R)) 1 (2 * K1) (4 * K2) := by
  have hϑd : Differentiable ℝ ϑ := hϑ.differentiable (by norm_num)
  have hϑ1 : ContDiff ℝ 2 (deriv ϑ) := hϑ.deriv'
  have hϑ1d : Differentiable ℝ (deriv ϑ) := hϑ1.differentiable (by norm_num)
  have hK1n : 0 ≤ K1 := (abs_nonneg _).trans (hK1 0)
  have hK2n : 0 ≤ K2 := (abs_nonneg _).trans (hK2 0)
  have hd1 : ∀ u, deriv (fun u => ϑ (u / R)) u = deriv ϑ (u / R) * (1 / R) := fun u => by
    have := (hϑd (u / R)).hasDerivAt.comp u ((hasDerivAt_id' u).div_const R)
    have e : (fun u => ϑ (u / R)) = ϑ ∘ fun x => x / R := rfl
    rw [e, this.deriv]
  have hd1' : deriv (fun u => ϑ (u / R)) = fun u => deriv ϑ (u / R) * (1 / R) := funext hd1
  have hd2 : ∀ u, deriv (deriv (fun u => ϑ (u / R))) u = deriv (deriv ϑ) (u / R) * (1 / R) * (1 / R) := fun u => by
    rw [hd1']
    have := (hϑ1d (u / R)).hasDerivAt.comp u ((hasDerivAt_id' u).div_const R)
    have h2 := this.mul_const (1 / R)
    simpa using h2.deriv
  -- the profile and its derivatives vanish for `|t| > 2`
  have hz : ∀ t, 2 < |t| → deriv ϑ t = 0 ∧ deriv (deriv ϑ) t = 0 := fun t ht => by
    have hloc : ϑ =ᶠ[nhds t] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds ht] with s hs using h2 s hs.le
    have h1 : deriv ϑ =ᶠ[nhds t] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds ht] with s hs
      have hl : ϑ =ᶠ[nhds s] fun _ => (0 : ℝ) := by
        filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hs] with r hr using h2 r hr.le
      rw [hl.deriv_eq]; simp
    refine ⟨by rw [hloc.deriv_eq]; simp, by rw [h1.deriv_eq]; simp⟩
  refine ⟨(hϑ.of_le (by norm_num)).comp (contDiff_id.div_const R), fun u => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · rw [abs_of_nonneg (h01 _).1]; exact (h01 _).2
  · rw [hd1 u, abs_mul]
    by_cases hu2 : 2 < |u / R|
    · rw [(hz _ hu2).1]; simp [hK1n]
    · have hu2' : |u| ≤ 2 * R := by
        rw [abs_div, abs_of_pos hR] at hu2
        have := not_lt.mp hu2
        rwa [div_le_iff₀ hR] at this
      have e : |1 / R| = 1 / R := abs_of_pos (by positivity)
      rw [e]
      have a1 := hK1 (u / R)
      calc |deriv ϑ (u / R)| * (1 / R) * |u| ≤ K1 * (1 / R) * (2 * R) := by gcongr
        _ = 2 * K1 := by field_simp
  · rw [hd2 u, abs_mul, abs_mul]
    by_cases hu2 : 2 < |u / R|
    · rw [(hz _ hu2).2]; simp [hK2n]
    · have hu2' : |u| ≤ 2 * R := by
        rw [abs_div, abs_of_pos hR] at hu2
        have := not_lt.mp hu2
        rwa [div_le_iff₀ hR] at this
      have e : |1 / R| = 1 / R := abs_of_pos (by positivity)
      rw [e]
      have hu2sq : u ^ 2 ≤ (2 * R) ^ 2 := by
        rw [← sq_abs u]; exact pow_le_pow_left₀ (abs_nonneg u) hu2' 2
      have a2 := hK2 (u / R)
      calc |deriv (deriv ϑ) (u / R)| * (1 / R) * (1 / R) * u ^ 2 ≤ K2 * (1 / R) * (1 / R) * (2 * R) ^ 2 := by gcongr
        _ = 4 * K2 := by field_simp; ring

/-- info: 'FormalResearch.SignUncertainty.cutoff_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.cutoff_scale

/-- Derivatives of `ζ g` (a real cutoff times a complex function). -/
lemma deriv_cut_mul {ζ : ℝ → ℝ} {g : ℝ → ℂ} {x : ℝ} (hζ : ContDiff ℝ 2 ζ) (hg : ContDiffAt ℝ 2 g x) :
    deriv (fun y => (ζ y : ℂ) * g y) x = ((deriv ζ x : ℝ) : ℂ) * g x + (ζ x : ℂ) * deriv g x ∧
    deriv (deriv (fun y => (ζ y : ℂ) * g y)) x =
      ((deriv (deriv ζ) x : ℝ) : ℂ) * g x + 2 * ((deriv ζ x : ℝ) : ℂ) * deriv g x + (ζ x : ℂ) * deriv (deriv g) x := by
  have hζd : Differentiable ℝ ζ := hζ.differentiable (by norm_num)
  have hζ1' : ContDiff ℝ 1 (deriv ζ) := hζ.deriv'
  have hζ1 : Differentiable ℝ (deriv ζ) := hζ1'.differentiable (by norm_num)
  have hev : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 g y := hg.eventually (by simp)
  have hgd : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  have hg1 : DifferentiableAt ℝ (deriv g) x := by
    have h := hg.fderiv_right (m := 1) (by norm_num)
    have h2 : ContDiffAt ℝ 1 (fun y => fderiv ℝ g y 1) x := h.clm_apply contDiffAt_const
    exact h2.differentiableAt (by norm_num)
  have e1 : deriv (fun y => (ζ y : ℂ) * g y) =ᶠ[nhds x]
      fun y => ((deriv ζ y : ℝ) : ℂ) * g y + (ζ y : ℂ) * deriv g y := by
    filter_upwards [hev] with y hy
    have h1 : HasDerivAt (fun y => (ζ y : ℂ)) ((deriv ζ y : ℝ) : ℂ) y := (hζd y).hasDerivAt.ofReal_comp
    exact (h1.mul (hy.differentiableAt (by norm_num)).hasDerivAt).deriv
  refine ⟨?_, ?_⟩
  · rw [e1.self_of_nhds]
  · rw [e1.deriv_eq]
    have h1 : HasDerivAt (fun y => ((deriv ζ y : ℝ) : ℂ)) ((deriv (deriv ζ) x : ℝ) : ℂ) x := (hζ1 x).hasDerivAt.ofReal_comp
    have h0 : HasDerivAt (fun y => (ζ y : ℂ)) ((deriv ζ x : ℝ) : ℂ) x := (hζd x).hasDerivAt.ofReal_comp
    have := ((h1.mul hgd.hasDerivAt).add (h0.mul hg1.hasDerivAt)).deriv
    exact this.trans (by ring)

/-- **Leibniz bound for `cutoff × amplitude`** (orders `0, 1, 2`): `‖g^{(r)}(x)‖ ≤ G |x|^{-s-r}` implies
`‖(ζ g)^{(r)}(x)‖ ≤ K_r' G |x|^{-s-r}` with `K_0' = K0`, `K_1' = K1 + K0`, `K_2' = K2 + 2 K1 + K0`. -/
lemma leibniz_cut {ζ : ℝ → ℝ} {K0 K1 K2 : ℝ} (hζ : IsCut ζ K0 K1 K2) {g : ℝ → ℂ} {G s x : ℝ} (hg : ContDiffAt ℝ 2 g x)
    (_hG : 0 ≤ G) (hx : x ≠ 0) (hg0 : ‖g x‖ ≤ G * |x| ^ (-s)) (hg1 : ‖deriv g x‖ ≤ G * |x| ^ (-s - 1))
    (hg2 : ‖deriv (deriv g) x‖ ≤ G * |x| ^ (-s - 2)) :
    ‖(ζ x : ℂ) * g x‖ ≤ K0 * G * |x| ^ (-s) ∧
    ‖deriv (fun y => (ζ y : ℂ) * g y) x‖ ≤ (K1 + K0) * G * |x| ^ (-s - 1) ∧
    ‖deriv (deriv (fun y => (ζ y : ℂ) * g y)) x‖ ≤ (K2 + 2 * K1 + K0) * G * |x| ^ (-s - 2) := by
  obtain ⟨e1, e2⟩ := deriv_cut_mul (x := x) hζ.contDiff hg
  have hax : 0 < |x| := abs_pos.mpr hx
  have p1 : |x| ^ (-s - 1) * |x| = |x| ^ (-s) := by
    rw [show -s - 1 = -s + (-1) by ring, Real.rpow_add hax, Real.rpow_neg_one]; field_simp
  have p2 : |x| ^ (-s - 2) * |x| ^ 2 = |x| ^ (-s) := by
    rw [show -s - 2 = -s + (-2) by ring, Real.rpow_add hax]
    rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]; simp [zpow_neg]; field_simp
  have p21 : |x| ^ (-s - 2) * |x| = |x| ^ (-s - 1) := by
    rw [show -s - 2 = -s - 1 + (-1) by ring, Real.rpow_add hax, Real.rpow_neg_one]; field_simp
  have b1 := hζ.bound1 x hx
  have b2 := hζ.bound2 x hx
  have b0 := hζ.bound0 x
  have hq0 : 0 ≤ |x| ^ (-s) := Real.rpow_nonneg hax.le _
  have hq1 : 0 ≤ |x| ^ (-s - 1) := Real.rpow_nonneg hax.le _
  have hq2 : 0 ≤ |x| ^ (-s - 2) := Real.rpow_nonneg hax.le _
  have hK0 : 0 ≤ K0 := (abs_nonneg _).trans b0
  have hK1 : 0 ≤ K1 := (mul_nonneg (abs_nonneg _) (abs_nonneg _)).trans b1
  have hK2 : 0 ≤ K2 := (mul_nonneg (abs_nonneg _) (sq_nonneg _)).trans b2
  have hz1 : |deriv ζ x| ≤ K1 * |x| ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one, ← div_eq_mul_inv, le_div_iff₀ hax]; exact b1
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |ζ x| * ‖g x‖ ≤ K0 * (G * |x| ^ (-s)) := mul_le_mul b0 hg0 (norm_nonneg _) hK0
      _ = _ := by ring
  · rw [e1]
    have t1 : ‖((deriv ζ x : ℝ) : ℂ) * g x‖ ≤ K1 * G * |x| ^ (-s - 1) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hd : |deriv ζ x| ≤ K1 / |x| := by rw [le_div_iff₀ hax]; exact b1
      calc |deriv ζ x| * ‖g x‖ ≤ (K1 / |x|) * (G * |x| ^ (-s)) := mul_le_mul hd hg0 (norm_nonneg _) (by positivity)
        _ = K1 * G * (|x| ^ (-s) / |x|) := by ring
        _ = K1 * G * |x| ^ (-s - 1) := by rw [← p1]; field_simp
    have t2 : ‖(ζ x : ℂ) * deriv g x‖ ≤ K0 * G * |x| ^ (-s - 1) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |ζ x| * ‖deriv g x‖ ≤ K0 * (G * |x| ^ (-s - 1)) := mul_le_mul b0 hg1 (norm_nonneg _) hK0
        _ = _ := by ring
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ K1 * G * |x| ^ (-s - 1) + K0 * G * |x| ^ (-s - 1) := add_le_add t1 t2
      _ = _ := by ring
  · rw [e2]
    have t1 : ‖((deriv (deriv ζ) x : ℝ) : ℂ) * g x‖ ≤ K2 * G * |x| ^ (-s - 2) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hd : |deriv (deriv ζ) x| ≤ K2 / x ^ 2 := by rw [le_div_iff₀ (by positivity)]; exact b2
      calc |deriv (deriv ζ) x| * ‖g x‖ ≤ (K2 / x ^ 2) * (G * |x| ^ (-s)) := mul_le_mul hd hg0 (norm_nonneg _) (by positivity)
        _ = K2 * G * (|x| ^ (-s) / x ^ 2) := by ring
        _ = K2 * G * |x| ^ (-s - 2) := by rw [← p2, ← sq_abs x]; field_simp
    have t2 : ‖2 * ((deriv ζ x : ℝ) : ℂ) * deriv g x‖ ≤ 2 * K1 * G * |x| ^ (-s - 2) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      rw [h2]
      have hd : |deriv ζ x| ≤ K1 / |x| := by rw [le_div_iff₀ hax]; exact b1
      calc 2 * |deriv ζ x| * ‖deriv g x‖ ≤ 2 * (K1 / |x|) * (G * |x| ^ (-s - 1)) := by gcongr
        _ = 2 * K1 * G * (|x| ^ (-s - 1) / |x|) := by ring
        _ = 2 * K1 * G * |x| ^ (-s - 2) := by rw [← p21]; field_simp
    have t3 : ‖(ζ x : ℂ) * deriv (deriv g) x‖ ≤ K0 * G * |x| ^ (-s - 2) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |ζ x| * ‖deriv (deriv g) x‖ ≤ K0 * (G * |x| ^ (-s - 2)) := mul_le_mul b0 hg2 (norm_nonneg _) hK0
        _ = _ := by ring
    calc _ ≤ ‖((deriv (deriv ζ) x : ℝ) : ℂ) * g x + 2 * ((deriv ζ x : ℝ) : ℂ) * deriv g x‖ + ‖(ζ x : ℂ) * deriv (deriv g) x‖ := norm_add_le _ _
      _ ≤ (‖((deriv (deriv ζ) x : ℝ) : ℂ) * g x‖ + ‖2 * ((deriv ζ x : ℝ) : ℂ) * deriv g x‖) + ‖(ζ x : ℂ) * deriv (deriv g) x‖ := by
        gcongr; exact norm_add_le _ _
      _ ≤ (K2 * G * |x| ^ (-s - 2) + 2 * K1 * G * |x| ^ (-s - 2)) + K0 * G * |x| ^ (-s - 2) := add_le_add (add_le_add t1 t2) t3
      _ = _ := by ring

/-- info: 'FormalResearch.SignUncertainty.leibniz_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.leibniz_cut

end FormalResearch.SignUncertainty
