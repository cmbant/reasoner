module

public import FormalResearch.SignUncertainty.CtChartMap

/-!
# The derivative of the chart: `T_s = 1/(V + 2 Z V_z)` (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 3.  **Proved.**
`T(s;β)` is the inverse of `W(x) = x V(x²;β)`, so `∂_s T = 1/W'(T) = 1/(V(Z) + 2 Z V_z(Z))`, `Z = Z(s²;β)`.
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.CtChart

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma ev_cd1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {F : E → ℂ} {x : E}
    (h : ContDiffAt ℂ ∞' F x) : ∀ᶠ y in 𝓝 x, ContDiffAt ℂ 1 F y :=
  (h.of_le (by simp)).eventually (by simp)

lemma ev_diff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {F : E → ℂ} {x : E}
    (h : ContDiffAt ℂ ∞' F x) : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ F y :=
  (ev_cd1 h).mono fun y hy => hy.differentiableAt (by simp)

lemma hasDerivAt_slice1 {F : ℂ × ℂ → ℂ} {q : ℂ × ℂ} (h : DifferentiableAt ℂ F q) :
    HasDerivAt (fun y : ℂ => F (y, q.2)) (fderiv ℂ F q (1, 0)) q.1 := by
  have h1 : HasDerivAt (fun y : ℂ => (y, q.2)) ((1 : ℂ), (0 : ℂ)) q.1 :=
    (hasDerivAt_id' q.1).prodMk (hasDerivAt_const q.1 q.2)
  have := h.hasFDerivAt.comp_hasDerivAt q.1 (f := fun y : ℂ => (y, q.2)) (by simpa using h1)
  simpa [Function.comp_def] using this

/-- `∂_z V`. -/
noncomputable def Vz (q : ℂ × ℂ) : ℂ := fderiv ℂ Vf q (1, 0)

/-- `T_s` as a function of `(y, β)`: `1/(V(Z) + 2 Z V_z(Z))`. -/
noncomputable def Tsd (q : ℂ × ℂ) : ℂ := 1 / (Vf (Zf q, q.2) + 2 * Zf q * Vz (Zf q, q.2))

lemma contDiffAt_Vz : ContDiffAt ℂ ∞' Vz (0, 0) := by
  unfold Vz
  exact (contDiffAt_Vf.fderiv_right (m := ∞') (by exact le_of_eq (by rw [← WithTop.coe_one, ← WithTop.coe_add]; simp))).clm_apply
    contDiffAt_const

lemma contDiffAt_Tsd_den : ContDiffAt ℂ ∞' (fun q : ℂ × ℂ => Vf (Zf q, q.2) + 2 * Zf q * Vz (Zf q, q.2)) (0, 0) := by
  have h := contDiffAt_Zf
  have hq : ContDiffAt ℂ ∞' (fun q : ℂ × ℂ => (Zf q, q.2)) (0, 0) := h.prodMk contDiff_snd.contDiffAt
  have hVz : ContDiffAt ℂ ∞' (fun q : ℂ × ℂ => Vz (Zf q, q.2)) (0, 0) :=
    ContDiffAt.comp (g := Vz) (f := fun q : ℂ × ℂ => (Zf q, q.2)) (0, 0) (by simpa [Zf_zero] using contDiffAt_Vz) hq
  exact contDiffAt_VZ.add ((contDiffAt_const.mul h).mul hVz)

lemma Tsd_den_zero : Vf (Zf (0, 0), (0, 0).2) + 2 * Zf (0, 0) * Vz (Zf (0, 0), (0, 0).2) = ((CtCfu.d0 : ℝ) : ℂ) := by
  simp [Zf_zero, Vf_zero]

lemma contDiffAt_Tsd : ContDiffAt ℂ ∞' Tsd (0, 0) := by
  unfold Tsd
  refine contDiffAt_const.div contDiffAt_Tsd_den ?_
  simp only
  rw [Tsd_den_zero]; exact d0C_ne

lemma Tsd_zero : Tsd (0, 0) = 1 / ((CtCfu.d0 : ℝ) : ℂ) := by
  unfold Tsd; simp only; rw [Tsd_den_zero]

lemma Tsd_den_ne : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), Vf (Zf q, q.2) + 2 * Zf q * Vz (Zf q, q.2) ≠ 0 := by
  have hc := contDiffAt_Tsd_den.continuousAt
  refine hc.eventually_ne ?_
  simp only
  rw [Tsd_den_zero]; exact d0C_ne

/-- `ct:cfu` Step 2/3: `∂_s T(s; β) = T_s = 1/(V(Z) + 2 Z V_z(Z))`, `Z = Z(s²; β)`. -/
theorem hasDerivAt_Tf : ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)),
    HasDerivAt (fun s : ℂ => Tf (s, p.2)) (Tsd (p.1 ^ 2, p.2)) p.1 := by
  have hZd : ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)), DifferentiableAt ℂ Zf (p.1 ^ 2, p.2) :=
    tendsto_sq.eventually (ev_diff contDiffAt_Zf)
  have hVd : ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)), DifferentiableAt ℂ Vf (Zf (p.1 ^ 2, p.2), p.2) :=
    tendsto_Zq.eventually (ev_diff contDiffAt_Vf)
  have hEq : ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)), ∀ᶠ p' in 𝓝 p, Zf (p'.1 ^ 2, p'.2) * Vf (Zf (p'.1 ^ 2, p'.2), p'.2) ^ 2 = p'.1 ^ 2 :=
    (tendsto_sq.eventually Zf_eq).eventually_nhds
  have hDen : ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)), Vf (Zf (p.1 ^ 2, p.2), p.2) + 2 * Zf (p.1 ^ 2, p.2) * Vz (Zf (p.1 ^ 2, p.2), p.2) ≠ 0 :=
    tendsto_sq.eventually Tsd_den_ne
  have hV0 := tendsto_sq.eventually Vf_Zf_ne
  filter_upwards [hZd, hVd, hEq, hDen, hV0] with p hZ hV hE hD hV0
  obtain ⟨s, β⟩ := p
  simp only at hZ hV hE hD hV0 ⊢
  set Z := Zf (s ^ 2, β) with hZdef
  set W := Vf (Z, β) with hWdef
  -- derivative of s' ↦ Zf (s'^2, β)
  have hg : HasDerivAt (fun s' : ℂ => Zf (s' ^ 2, β)) (fderiv ℂ Zf (s ^ 2, β) (1, 0) * (2 * s)) s := by
    have h1 := hasDerivAt_slice1 hZ
    have h2 : HasDerivAt (fun s' : ℂ => s' ^ 2) (2 * s) s := by simpa using hasDerivAt_pow 2 s
    have := HasDerivAt.comp (h := fun s' : ℂ => s' ^ 2) s (by simpa using h1) h2
    simpa [Function.comp_def] using this
  set g' := fderiv ℂ Zf (s ^ 2, β) (1, 0) * (2 * s) with hg'
  -- derivative of s' ↦ Vf (Zf (s'^2, β), β)
  have hW : HasDerivAt (fun s' : ℂ => Vf (Zf (s' ^ 2, β), β)) (Vz (Z, β) * g') s := by
    have h1 := hasDerivAt_slice1 hV
    exact HasDerivAt.comp (h := fun s' : ℂ => Zf (s' ^ 2, β)) s (by simpa using h1) hg
  -- differentiate the equation
  have hlhs : HasDerivAt (fun s' : ℂ => Zf (s' ^ 2, β) * Vf (Zf (s' ^ 2, β), β) ^ 2)
      (g' * W ^ 2 + Z * (2 * W * (Vz (Z, β) * g'))) s := by
    have := hg.mul (hW.pow 2)
    refine this.congr_deriv ?_
    simp [hZdef, hWdef]
  have hrhs : HasDerivAt (fun s' : ℂ => s' ^ 2) (2 * s) s := by simpa using hasDerivAt_pow 2 s
  have hE' : (fun s' : ℂ => Zf (s' ^ 2, β) * Vf (Zf (s' ^ 2, β), β) ^ 2) =ᶠ[𝓝 s] fun s' => s' ^ 2 := by
    have : Tendsto (fun s' : ℂ => (s', β)) (𝓝 s) (𝓝 (s, β)) := (Continuous.prodMk_left β).continuousAt.tendsto
    exact this.eventually hE
  have hder := hlhs.unique (hrhs.congr_of_eventuallyEq hE')
  have hs2 : Z * W ^ 2 = s ^ 2 := hE.self_of_nhds
  have hW0 : W ≠ 0 := hV0
  have hD' : W + 2 * Z * Vz (Z, β) ≠ 0 := hD
  -- T = s / W
  have hTe : (fun s' : ℂ => Tf (s', β)) = fun s' => s' / Vf (Zf (s' ^ 2, β), β) := by
    funext s'; unfold Tf Uf; simp only; ring
  rw [hTe]
  have hT := (hasDerivAt_id' s).div hW hV0
  refine hT.congr_deriv ?_
  have key : W * ((1 * W - s * (Vz (Z, β) * g')) * (W + 2 * Z * Vz (Z, β)) - 1 * W ^ 2) = 0 := by
    linear_combination (2 * Vz (Z, β)) * hs2 - (s * Vz (Z, β)) * hder
  have key2 := (mul_eq_zero.mp key).resolve_left hW0
  unfold Tsd
  simp only
  rw [← hZdef, ← hWdef]
  rw [div_eq_div_iff (pow_ne_zero 2 hW0) hD']
  linear_combination key2

/-- info: 'FormalResearch.SignUncertainty.CtChart.hasDerivAt_Tf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_Tf

end FormalResearch.SignUncertainty.CtChart
