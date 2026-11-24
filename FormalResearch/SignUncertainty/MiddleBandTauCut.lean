module

public import FormalResearch.SignUncertainty.MiddleBandSmall

/-!
# GT.2a: the cutoff `ϑ(t(εu)/ρ)` in the variable `u`

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, proof of `cegt:GT2a`, "Outer pieces" and "Inner difference".

The inner/outer splitting of `I_main` is done in the variable `τ = εv` by a cutoff `η(τ) = ϑ(τ/ρ₀)`, `ρ₀ = 0.08`.  After the substitution `τ = t(εu)`
(`t = Re τ`, the normal-form map of `O.4`) the inner cutoff becomes `ζ(u) = ϑ(t(εu)/ρ₀)` (`tauCut`): no inverse function is needed.

* `trF_deriv_bounds`: `|t'| ≤ 2000`, `|t''| ≤ 9000` for `|θ| ≤ 0.18`.
* `tauCut_isCut`: `ζ` is a scale-invariant cutoff (`IsCut ζ 1 Z₁ Z₂`), equal to `1` for `ε|u| ≤ 0.075`, to `0` for `ε|u| ≥ 0.18`; `Z₁, Z₂` depend
  only on the profile constants.

Status: proved, unconditional given `O4NormalForm L τ` (which exists for every `0 < L ≤ 0.002` by `o4_normal_form` and `o4QuotientBound`).
-/

@[expose] public section

open Set Filter Topology Complex Function

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- `|t'| ≤ 2000` and `|t''| ≤ 9000` for `|θ| ≤ 0.18`. -/
lemma trF_deriv_bounds {L : ℝ} {τ : ℂ → ℂ} (h : O4NormalForm L τ) (hL0 : 0 < L) (hL2 : L ≤ 0.002) {θ : ℝ}
    (hθ : |θ| ≤ 0.18) : |trF τ 1 θ| ≤ 2000 ∧ |trF τ 2 θ| ≤ 9000 := by
  have hκ := edgeKappa0_bounds hL0 hL2
  obtain ⟨-, t1, t2⟩ := tau_taylor_bounds h hθ
  have hθ2 : θ ^ 2 ≤ 0.0324 := by nlinarith [sq_abs θ, abs_nonneg θ]
  constructor
  · have e1 : |trF τ 1 θ - edgeKappa0 L| ≤ 50000 * θ ^ 2 := by
      have := Complex.abs_re_le_norm (deriv τ (θ : ℂ) - (edgeKappa0 L : ℂ))
      simp only [Complex.sub_re, Complex.ofReal_re] at this
      rw [trF_one_eq]; exact this.trans t1
    have := abs_le.mp e1
    rw [abs_le]; constructor <;> nlinarith [hκ.1, hκ.2]
  · have := Complex.abs_re_le_norm (deriv (deriv τ) (θ : ℂ))
    have e : trF τ 2 θ = (deriv (deriv τ) (θ : ℂ)).re := by simp [trF, iteratedDeriv_succ]
    rw [e]
    refine this.trans (t2.trans ?_)
    nlinarith [abs_nonneg θ]

/-- The cutoff `ϑ(t(εu)/0.08)` (set to `0` for `|εu| ≥ 0.2`, where it vanishes anyway). -/
noncomputable def tauCut (ϑ : ℝ → ℝ) (τ : ℂ → ℂ) (ε : ℝ) (u : ℝ) : ℝ :=
  if |ε * u| < 0.2 then ϑ (trF τ 0 (ε * u) / 0.08) else 0

lemma tauCut_of_lt {ϑ : ℝ → ℝ} {τ : ℂ → ℂ} {ε u : ℝ} (h : |ε * u| < 0.2) :
    tauCut ϑ τ ε u = ϑ (trF τ 0 (ε * u) / 0.08) := by unfold tauCut; rw [if_pos h]

/-- First two derivatives of `s ↦ ϑ(t(εs)/ρ)`. -/
lemma tauCutAux_hasDerivAt {L : ℝ} {τ : ℂ → ℂ} (h : O4NormalForm L τ) {ϑ : ℝ → ℝ} (hϑ : ContDiff ℝ 3 ϑ) {ε ρ s : ℝ}
    (hs : |ε * s| < 0.22) :
    HasDerivAt (fun s => ϑ (trF τ 0 (ε * s) / ρ))
      (deriv ϑ (trF τ 0 (ε * s) / ρ) * (ε * trF τ 1 (ε * s) / ρ)) s ∧
    HasDerivAt (fun s => deriv ϑ (trF τ 0 (ε * s) / ρ) * (ε * trF τ 1 (ε * s) / ρ))
      (deriv (deriv ϑ) (trF τ 0 (ε * s) / ρ) * (ε * trF τ 1 (ε * s) / ρ) * (ε * trF τ 1 (ε * s) / ρ) +
        deriv ϑ (trF τ 0 (ε * s) / ρ) * (ε ^ 2 * trF τ 2 (ε * s) / ρ)) s := by
  have hϑd : Differentiable ℝ ϑ := hϑ.differentiable (by norm_num)
  have hϑ1 : ContDiff ℝ 2 (deriv ϑ) := hϑ.deriv'
  have hϑ1d : Differentiable ℝ (deriv ϑ) := hϑ1.differentiable (by norm_num)
  have t0 := hasDerivAt_dilate (trF_hasDerivAt h 0 hs)
  have t1 := hasDerivAt_dilate (trF_hasDerivAt h 1 hs)
  have a0 : HasDerivAt (fun s => trF τ 0 (ε * s) / ρ) (ε * trF τ 1 (ε * s) / ρ) s := by
    have := t0.div_const ρ
    refine this.congr_deriv ?_
    simp [smul_eq_mul]
  have a1 : HasDerivAt (fun s => ε * trF τ 1 (ε * s) / ρ) (ε ^ 2 * trF τ 2 (ε * s) / ρ) s := by
    have := (t1.const_mul ε).div_const ρ
    refine this.congr_deriv ?_
    simp [smul_eq_mul]; ring
  refine ⟨?_, ?_⟩
  · exact ((hϑd _).hasDerivAt.comp s a0)
  · have b1 := ((hϑ1d _).hasDerivAt.comp s a0).mul a1
    refine b1.congr_deriv ?_
    simp only [Function.comp_apply]

/-- `0.989 |θ| ≤ |t(θ)| ≤ 1.013 |θ|` for all `|θ| < 0.22` (including `θ = 0`). -/
lemma trF_abs_bounds {L : ℝ} {τ : ℂ → ℂ} (h : O4NormalForm L τ) (hL0 : 0 < L) (hL2 : L ≤ 0.002) {θ : ℝ}
    (hθ : |θ| < 0.22) : 0.989 * |θ| ≤ |trF τ 0 θ| ∧ |trF τ 0 θ| ≤ 1.013 * |θ| := by
  by_cases h0 : θ = 0
  · subst h0; simp [trF, h.zero]
  · exact trF_ratio h hL0 hL2 h0 hθ

/-- `ϑ(t(εu)/0.08)` as a cutoff: `1` for `ε|u| ≤ 0.075`, `0` for `ε|u| ≥ 0.18`, and `IsCut` with constants depending only on the profile. -/
theorem tauCut_isCut {ϑ : ℝ → ℝ} {K1 K2 : ℝ} (hϑ : Prof ϑ K1 K2) :
    ∃ Z1 Z2 : ℝ, 0 ≤ Z1 ∧ 0 ≤ Z2 ∧ ∀ {L : ℝ} {τ : ℂ → ℂ}, O4NormalForm L τ → 0 < L → L ≤ 0.002 → ∀ {ε : ℝ}, 0 < ε →
      IsCut (tauCut ϑ τ ε) 1 Z1 Z2 ∧ (∀ u, ε * |u| ≤ 0.075 → tauCut ϑ τ ε u = 1) ∧
        (∀ u, 0.18 ≤ ε * |u| → tauCut ϑ τ ε u = 0) := by
  have hk1 := hϑ.hK1
  have hk2 := hϑ.hK2
  refine ⟨5000 * K1, 2 * 10 ^ 7 * K2 + 3000 * K1, by positivity, by positivity, ?_⟩
  intro L τ h hL0 hL2 ε hε
  have hϑd : Differentiable ℝ ϑ := hϑ.contDiff.differentiable (by norm_num)
  -- vanishing of the profile derivatives outside `|t| ≤ 2`
  have hz : ∀ t, 2 < |t| → deriv ϑ t = 0 ∧ deriv (deriv ϑ) t = 0 := fun t ht => by
    have hloc : ϑ =ᶠ[nhds t] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds ht] with s hs using hϑ.zero s hs.le
    have h1 : deriv ϑ =ᶠ[nhds t] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds ht] with s hs
      have hl : ϑ =ᶠ[nhds s] fun _ => (0 : ℝ) := by
        filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hs] with r hr using hϑ.zero r hr.le
      rw [hl.deriv_eq]; simp
    refine ⟨by rw [hloc.deriv_eq]; simp, by rw [h1.deriv_eq]; simp⟩
  have hθabs : ∀ u : ℝ, |ε * u| = ε * |u| := fun u => by rw [abs_mul, abs_of_pos hε]
  -- the cutoff values
  have hone : ∀ u, ε * |u| ≤ 0.075 → tauCut ϑ τ ε u = 1 := by
    intro u hu
    have hθ : |ε * u| < 0.2 := by rw [hθabs]; linarith
    rw [tauCut_of_lt hθ]
    apply hϑ.one
    have := (trF_abs_bounds h hL0 hL2 (θ := ε * u) (by linarith)).2
    rw [hθabs] at this
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 0.08), div_le_one (by norm_num)]
    linarith
  have hzero : ∀ u, 0.18 ≤ ε * |u| → tauCut ϑ τ ε u = 0 := by
    intro u hu
    by_cases hθ : |ε * u| < 0.2
    · rw [tauCut_of_lt hθ]
      apply hϑ.zero
      have := (trF_abs_bounds h hL0 hL2 (θ := ε * u) (by linarith)).1
      rw [hθabs] at this
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 0.08), le_div_iff₀ (by norm_num)]
      linarith
    · unfold tauCut; rw [if_neg hθ]
  have hU : IsOpen {s : ℝ | |ε * s| < 0.2} :=
    isOpen_lt (continuous_abs.comp (continuous_const.mul continuous_id)) continuous_const
  have hU' : IsOpen {s : ℝ | 0.18 < ε * |s|} :=
    isOpen_lt continuous_const (continuous_const.mul continuous_abs)
  have hlin : ∀ u : ℝ, ContDiffAt ℝ 2 (fun s : ℝ => ε * s) u := fun u => (contDiff_const.mul contDiff_id).contDiffAt
  have hcdAux : ∀ u : ℝ, |ε * u| < 0.22 → ContDiffAt ℝ 2 (fun s => ϑ (trF τ 0 (ε * s) / 0.08)) u := by
    intro u hu
    have h0 : ContDiffAt ℝ 2 (fun s => trF τ 0 (ε * s)) u :=
      (by exact_mod_cast trF_contDiffAt h hu 2 0 : ContDiffAt ℝ 2 (trF τ 0) (ε * u)).comp u (hlin u)
    exact ((hϑ.contDiff.of_le (by norm_num)).contDiffAt).comp u (h0.div_const _)
  -- smoothness
  have hcd : ContDiff ℝ 2 (tauCut ϑ τ ε) := by
    rw [contDiff_iff_contDiffAt]
    intro u
    by_cases hu : |ε * u| < 0.2
    · have hev : tauCut ϑ τ ε =ᶠ[nhds u] fun s => ϑ (trF τ 0 (ε * s) / 0.08) := by
        filter_upwards [hU.mem_nhds hu] with s hs using tauCut_of_lt hs
      exact (hcdAux u (by linarith)).congr_of_eventuallyEq hev
    · have hu' : 0.18 < ε * |u| := by rw [← hθabs]; linarith [not_lt.mp hu]
      have hev : tauCut ϑ τ ε =ᶠ[nhds u] fun _ => (0 : ℝ) := by
        filter_upwards [hU'.mem_nhds hu'] with s hs using hzero s hs.le
      exact contDiffAt_const.congr_of_eventuallyEq hev
  -- vanishing derivatives far out
  have hfar : ∀ u, 0.18 < ε * |u| → deriv (tauCut ϑ τ ε) u = 0 ∧ deriv (deriv (tauCut ϑ τ ε)) u = 0 := by
    intro u hu
    have hev : tauCut ϑ τ ε =ᶠ[nhds u] fun _ => (0 : ℝ) := by
      filter_upwards [hU'.mem_nhds hu] with s hs using hzero s hs.le
    have hev1 : deriv (tauCut ϑ τ ε) =ᶠ[nhds u] fun _ => (0 : ℝ) := by
      filter_upwards [hU'.mem_nhds hu] with s hs
      have : tauCut ϑ τ ε =ᶠ[nhds s] fun _ => (0 : ℝ) := by
        filter_upwards [hU'.mem_nhds hs] with r hr using hzero r hr.le
      rw [this.deriv_eq]; simp
    exact ⟨by rw [hev.deriv_eq]; simp, by rw [hev1.deriv_eq]; simp⟩
  -- derivative formulas near the origin
  have hd1 : ∀ u, |ε * u| < 0.2 → deriv (tauCut ϑ τ ε) u =
      deriv ϑ (trF τ 0 (ε * u) / 0.08) * (ε * trF τ 1 (ε * u) / 0.08) := by
    intro u hu
    have hev : tauCut ϑ τ ε =ᶠ[nhds u] fun s => ϑ (trF τ 0 (ε * s) / 0.08) := by
      filter_upwards [hU.mem_nhds hu] with s hs using tauCut_of_lt hs
    rw [hev.deriv_eq]
    exact (tauCutAux_hasDerivAt h hϑ.contDiff (ρ := 0.08) (by linarith)).1.deriv
  have hd2 : ∀ u, |ε * u| < 0.2 → deriv (deriv (tauCut ϑ τ ε)) u =
      deriv (deriv ϑ) (trF τ 0 (ε * u) / 0.08) * (ε * trF τ 1 (ε * u) / 0.08) * (ε * trF τ 1 (ε * u) / 0.08) +
        deriv ϑ (trF τ 0 (ε * u) / 0.08) * (ε ^ 2 * trF τ 2 (ε * u) / 0.08) := by
    intro u hu
    have hev : deriv (tauCut ϑ τ ε) =ᶠ[nhds u]
        fun s => deriv ϑ (trF τ 0 (ε * s) / 0.08) * (ε * trF τ 1 (ε * s) / 0.08) := by
      filter_upwards [hU.mem_nhds hu] with s hs using hd1 s hs
    rw [hev.deriv_eq]
    exact (tauCutAux_hasDerivAt h hϑ.contDiff (ρ := 0.08) (by linarith)).2.deriv
  refine ⟨⟨hcd, fun u => ?_, fun u hu => ?_, fun u hu => ?_⟩, hone, hzero⟩
  · unfold tauCut
    split_ifs
    · rw [abs_of_nonneg (hϑ.range _).1]; exact (hϑ.range _).2
    · simp
  · by_cases hfa : 0.18 < ε * |u|
    · rw [(hfar u hfa).1]; simp [hk1]
    · have hfa' : ε * |u| ≤ 0.18 := not_lt.mp hfa
      have hθ : |ε * u| < 0.2 := by rw [hθabs]; linarith
      rw [hd1 u hθ]
      by_cases ht : 2 < |trF τ 0 (ε * u) / 0.08|
      · rw [(hz _ ht).1]; simp [hk1]
      · have ht' := not_lt.mp ht
        have hlow := (trF_abs_bounds h hL0 hL2 (θ := ε * u) (by linarith)).1
        rw [hθabs] at hlow
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 0.08), div_le_iff₀ (by norm_num)] at ht'
        have hεu : ε * |u| ≤ 0.1618 := by linarith
        obtain ⟨b1, -⟩ := trF_deriv_bounds h hL0 hL2 (θ := ε * u) (by rw [hθabs]; exact hfa')
        rw [abs_mul, abs_div, abs_mul, abs_of_pos hε, abs_of_pos (by norm_num : (0 : ℝ) < 0.08)]
        have hd := hϑ.d1 (trF τ 0 (ε * u) / 0.08)
        have e : |deriv ϑ (trF τ 0 (ε * u) / 0.08)| * (ε * |trF τ 1 (ε * u)| / 0.08) * |u| =
            |deriv ϑ (trF τ 0 (ε * u) / 0.08)| * (|trF τ 1 (ε * u)| * (ε * |u|) / 0.08) := by ring
        rw [e]
        have h2 : |trF τ 1 (ε * u)| * (ε * |u|) / 0.08 ≤ 2000 * 0.1618 / 0.08 := by
          rw [div_le_div_iff_of_pos_right (by norm_num)]
          exact mul_le_mul b1 hεu (by positivity) (by norm_num)
        calc _ ≤ K1 * (2000 * 0.1618 / 0.08) := mul_le_mul hd h2 (by positivity) hk1
          _ ≤ 5000 * K1 := by nlinarith
  · by_cases hfa : 0.18 < ε * |u|
    · rw [(hfar u hfa).2]; simp; positivity
    · have hfa' : ε * |u| ≤ 0.18 := not_lt.mp hfa
      have hθ : |ε * u| < 0.2 := by rw [hθabs]; linarith
      rw [hd2 u hθ]
      by_cases ht : 2 < |trF τ 0 (ε * u) / 0.08|
      · rw [(hz _ ht).1, (hz _ ht).2]; simp; positivity
      · have ht' := not_lt.mp ht
        have hlow := (trF_abs_bounds h hL0 hL2 (θ := ε * u) (by linarith)).1
        rw [hθabs] at hlow
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 0.08), div_le_iff₀ (by norm_num)] at ht'
        have hεu : ε * |u| ≤ 0.1618 := by linarith
        obtain ⟨b1, b2⟩ := trF_deriv_bounds h hL0 hL2 (θ := ε * u) (by rw [hθabs]; exact hfa')
        have hd1' := hϑ.d1 (trF τ 0 (ε * u) / 0.08)
        have hd2' := hϑ.d2 (trF τ 0 (ε * u) / 0.08)
        have hεu0 : 0 ≤ ε * |u| := by positivity
        set a : ℝ := |trF τ 1 (ε * u)| * (ε * |u|) / 0.08 with ha
        have ha0 : 0 ≤ a := by positivity
        have ha1 : a ≤ 2000 * 0.1618 / 0.08 := by
          rw [ha, div_le_div_iff_of_pos_right (by norm_num)]
          exact mul_le_mul b1 hεu hεu0 (by norm_num)
        set b : ℝ := |trF τ 2 (ε * u)| * (ε * |u|) ^ 2 / 0.08 with hb
        have hb0 : 0 ≤ b := by positivity
        have hb1 : b ≤ 9000 * 0.1618 ^ 2 / 0.08 := by
          rw [hb, div_le_div_iff_of_pos_right (by norm_num)]
          exact mul_le_mul b2 (pow_le_pow_left₀ hεu0 hεu 2) (by positivity) (by norm_num)
        have e : |deriv (deriv ϑ) (trF τ 0 (ε * u) / 0.08) * (ε * trF τ 1 (ε * u) / 0.08) * (ε * trF τ 1 (ε * u) / 0.08) +
            deriv ϑ (trF τ 0 (ε * u) / 0.08) * (ε ^ 2 * trF τ 2 (ε * u) / 0.08)| * u ^ 2 ≤
            |deriv (deriv ϑ) (trF τ 0 (ε * u) / 0.08)| * a ^ 2 + |deriv ϑ (trF τ 0 (ε * u) / 0.08)| * b := by
          refine (mul_le_mul_of_nonneg_right (abs_add_le _ _) (sq_nonneg u)).trans ?_
          have e1 : |deriv (deriv ϑ) (trF τ 0 (ε * u) / 0.08) * (ε * trF τ 1 (ε * u) / 0.08) * (ε * trF τ 1 (ε * u) / 0.08)| * u ^ 2 =
              |deriv (deriv ϑ) (trF τ 0 (ε * u) / 0.08)| * a ^ 2 := by
            rw [abs_mul, abs_mul, abs_div, abs_mul, abs_of_pos hε, abs_of_pos (by norm_num : (0 : ℝ) < 0.08), ha,
              ← sq_abs u]
            ring
          have e2 : |deriv ϑ (trF τ 0 (ε * u) / 0.08) * (ε ^ 2 * trF τ 2 (ε * u) / 0.08)| * u ^ 2 =
              |deriv ϑ (trF τ 0 (ε * u) / 0.08)| * b := by
            rw [abs_mul, abs_div, abs_mul, abs_of_pos (by positivity : 0 < ε ^ 2),
              abs_of_pos (by norm_num : (0 : ℝ) < 0.08), hb, ← sq_abs u]
            ring
          rw [add_mul, e1, e2]
        refine e.trans ?_
        calc _ ≤ K2 * (2000 * 0.1618 / 0.08) ^ 2 + K1 * (9000 * 0.1618 ^ 2 / 0.08) := by
              gcongr
          _ ≤ 2 * 10 ^ 7 * K2 + 3000 * K1 := by nlinarith

/-- info: 'FormalResearch.SignUncertainty.tauCut_isCut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.tauCut_isCut

end FormalResearch.SignUncertainty
