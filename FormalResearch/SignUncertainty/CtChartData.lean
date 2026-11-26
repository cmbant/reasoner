module

public import FormalResearch.SignUncertainty.CtChartGerm
public import FormalResearch.SignUncertainty.CtCfuInv
public import FormalResearch.SignUncertainty.CtChartIft
public import FormalResearch.SignUncertainty.CtChartTaylor
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# The CFU chart (`ct:cfu` Steps 2-3): the divided-difference equation, `V`, `Z`, `U`, `T`

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Steps 2-3.  **Proved.**
Parametrised by `β = b²` (not by `L` or `a`): `L(β) = β n(β)`, `d(β) = ((3/2)(n-ñ)(β))^{1/3}`, `a(β) = -d(β)² β`,
`p = z ñ`, `H(z;β) = -∫₀¹ (1-t) p''(β + t(z-β)) dt`, so that `(z-β)² H = -(p(z) - p(β) - p'(β)(z-β))`.
`R(z;β)` solves `d² R + d z R² + z(z-β)R³/3 + H = 0` (parametric scalar IFT), `V = d + (z-β)R`, and
`Z(y;β)` solves `Z V(Z;β)² = y`; `U = 1/V(Z;β)`, `T(s;β) = s U(s²;β)`.  Main identities:
`L(β) - p(z) = -a V - z V³/3` (`key_identity`), `Φ(T(s;β);β) = -(a s + s³/3)` (`chart_identity`), `Z(d²β; β) = β` (`saddle_Z`).
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.CtChart

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- `f = n - ñ`. -/
noncomputable def fC (β : ℂ) : ℂ := nC β - ntC β

/-- `d(β) = ((3/2) f(β))^{1/3}` (principal branch). -/
noncomputable def dC (β : ℂ) : ℂ := Complex.exp (Complex.log ((3 / 2) * fC β) / 3)

/-- `a(β) = -d(β)² β`. -/
noncomputable def aC (β : ℂ) : ℂ := -(dC β) ^ 2 * β

/-- `L(β) = β n(β)`. -/
noncomputable def LC (β : ℂ) : ℂ := β * nC β

/-- `p''`. -/
noncomputable def pC2 : ℂ → ℂ := deriv (deriv pC)

/-- `H(z;β) = -∫₀¹ (1-t) p''(β + t(z-β)) dt`, with `q = (z, β)`. -/
noncomputable def Hf (q : ℂ × ℂ) : ℂ := -∫ t in (0 : ℝ)..1, (1 - (t : ℂ)) * pC2 (q.2 + (t : ℂ) * (q.1 - q.2))

/-! ### Smoothness and symmetry of the data -/

lemma contDiffAt_deriv' {f : ℂ → ℂ} {x : ℂ} (h : ContDiffAt ℂ ∞' f x) : ContDiffAt ℂ ∞' (deriv f) x := by
  have := h.fderiv_right (m := ∞') (by exact le_of_eq (by rw [← WithTop.coe_one, ← WithTop.coe_add]; simp))
  have h2 : ContDiffAt ℂ ∞' (fun y => fderiv ℂ f y 1) x := this.clm_apply contDiffAt_const
  exact h2

lemma contDiffAt_pC2 : ContDiffAt ℂ ∞' pC2 0 :=
  contDiffAt_deriv' (contDiffAt_deriv' contDiffAt_pC)

lemma contDiffAt_Hf : ContDiffAt ℂ ∞' Hf (0, 0) := by
  unfold Hf
  refine ContDiffAt.neg ?_
  refine contDiffAt_segInt (F := fun (q : ℂ × ℂ) w => (1 - w) * pC2 (q.2 + w * (q.1 - q.2))) ?_
  intro t ht
  have h : ContDiffAt ℂ ∞' pC2 ((fun p : (ℂ × ℂ) × ℂ => p.1.2 + p.2 * (p.1.1 - p.1.2)) ((0, 0), (t : ℂ))) := by
    simpa using contDiffAt_pC2
  have h2 : ContDiffAt ℂ ∞' (fun p : (ℂ × ℂ) × ℂ => pC2 (p.1.2 + p.2 * (p.1.1 - p.1.2))) ((0, 0), (t : ℂ)) :=
    ContDiffAt.comp (g := pC2) (f := fun p : (ℂ × ℂ) × ℂ => p.1.2 + p.2 * (p.1.1 - p.1.2)) ((0, 0), (t : ℂ)) h
      (by fun_prop : ContDiff ℂ ∞' fun p : (ℂ × ℂ) × ℂ => p.1.2 + p.2 * (p.1.1 - p.1.2)).contDiffAt
  exact (contDiff_const.sub contDiff_snd).contDiffAt.mul h2

lemma fC_zero : fC 0 = (π : ℂ) ^ 2 / 18 := by
  unfold fC; rw [nC_zero, ntC_zero]; ring

lemma d0C_cube : ((CtCfu.d0 : ℝ) : ℂ) ^ 3 = (π : ℂ) ^ 2 / 12 := by
  have := CtCfu.d0_cube
  exact_mod_cast this

lemma three_half_fC_zero : (3 / 2) * fC 0 = ((CtCfu.d0 : ℝ) : ℂ) ^ 3 := by
  rw [fC_zero, d0C_cube]; ring

lemma slit_three_half_fC_zero : (3 / 2) * fC 0 ∈ Complex.slitPlane := by
  rw [three_half_fC_zero]
  have : (((CtCfu.d0 : ℝ) : ℂ)) ^ 3 = (((CtCfu.d0 ^ 3 : ℝ)) : ℂ) := by push_cast; ring
  rw [this]
  exact Complex.ofReal_mem_slitPlane.mpr (by have := CtCfu.d0_pos; positivity)

lemma contDiffAt_fC : ContDiffAt ℂ ∞' fC 0 := contDiffAt_nC.sub contDiffAt_ntC

lemma contDiffAt_dC : ContDiffAt ℂ ∞' dC 0 := by
  unfold dC
  refine Complex.contDiff_exp.contDiffAt.comp 0 ?_
  refine ContDiffAt.div_const ?_ _
  exact (Complex.contDiffAt_log slit_three_half_fC_zero).comp 0 (contDiffAt_const.mul contDiffAt_fC)

lemma dC_zero : dC 0 = ((CtCfu.d0 : ℝ) : ℂ) := by
  unfold dC
  rw [three_half_fC_zero]
  have hpos : (0 : ℝ) < CtCfu.d0 := CtCfu.d0_pos
  have : (((CtCfu.d0 : ℝ) : ℂ)) ^ 3 = (((CtCfu.d0 ^ 3 : ℝ)) : ℂ) := by push_cast; ring
  rw [this, ← Complex.ofReal_log (by positivity), Real.log_pow]
  have h3 : ((((3 : ℕ) : ℝ) * Real.log CtCfu.d0 : ℝ) : ℂ) / 3 = ((Real.log CtCfu.d0 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h3, ← Complex.ofReal_exp, Real.exp_log hpos]

/-- `d³ = (3/2) f` near `0`. -/
lemma dC_cube : ∀ᶠ β in 𝓝 (0 : ℂ), dC β ^ 3 = (3 / 2) * fC β := by
  have hc : ContinuousAt (fun β => (3 / 2 : ℂ) * fC β) 0 := (contDiffAt_const.mul contDiffAt_fC).continuousAt
  filter_upwards [hc.eventually_ne (by rw [three_half_fC_zero]; have := CtCfu.d0_pos; exact pow_ne_zero 3 (by exact_mod_cast this.ne'))] with β hβ
  unfold dC
  rw [← Complex.exp_nat_mul]
  have : (↑(3 : ℕ) : ℂ) * (Complex.log ((3 / 2) * fC β) / 3) = Complex.log ((3 / 2) * fC β) := by push_cast; ring
  rw [this, Complex.exp_log hβ]

lemma fC_conj (β : ℂ) : fC (starRingEnd ℂ β) = starRingEnd ℂ (fC β) := by
  unfold fC; rw [nC_conj, ntC_conj, map_sub]

lemma dC_conj : ∀ᶠ β in 𝓝 (0 : ℂ), dC (starRingEnd ℂ β) = starRingEnd ℂ (dC β) := by
  have hc : ContinuousAt (fun β => (3 / 2 : ℂ) * fC β) 0 := (contDiffAt_const.mul contDiffAt_fC).continuousAt
  have hs : ∀ᶠ β in 𝓝 (0 : ℂ), (3 / 2 : ℂ) * fC β ∈ Complex.slitPlane :=
    hc.eventually (Complex.isOpen_slitPlane.mem_nhds slit_three_half_fC_zero)
  filter_upwards [hs] with β hβ
  unfold dC
  have e1 : (3 / 2 : ℂ) * fC (starRingEnd ℂ β) = starRingEnd ℂ ((3 / 2 : ℂ) * fC β) := by
    rw [fC_conj, map_mul]; congr 1
    rw [map_div₀, map_ofNat, map_ofNat]
  rw [e1, Complex.log_conj _ (by simpa using (Complex.mem_slitPlane_iff_arg.mp hβ).1), ← Complex.exp_conj]
  congr 1
  rw [map_div₀, map_ofNat]

lemma pC2_conj (z : ℂ) : pC2 (starRingEnd ℂ z) = starRingEnd ℂ (pC2 z) := by
  unfold pC2
  have h1 : ∀ w, deriv pC (starRingEnd ℂ w) = starRingEnd ℂ (deriv pC w) := deriv_conj_symm pC_conj
  exact deriv_conj_symm h1 z

lemma Hf_conj (q : ℂ × ℂ) : Hf (conj2 q) = starRingEnd ℂ (Hf q) := by
  unfold Hf
  rw [map_neg, ← intInt_conj]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  show _ = _
  have e : (conj2 q).2 + (t : ℂ) * ((conj2 q).1 - (conj2 q).2) =
      starRingEnd ℂ (q.2 + (t : ℂ) * (q.1 - q.2)) := by simp [conj2]
  rw [e, pC2_conj, map_mul]
  simp

/-! ### The Taylor identity for `H` and the `p'` identity -/

lemma analytic_ball : ∃ r : ℝ, 0 < r ∧ ∀ w ∈ Metric.ball (0 : ℂ) r, AnalyticAt ℂ pC w :=
  Metric.eventually_nhds_iff_ball.mp analyticAt_pC.eventually_analyticAt

lemma deriv_pC_eq : ∀ᶠ β in 𝓝 (0 : ℂ), deriv pC β = (nC β - ntC β) / 2 := by
  filter_upwards [rel_n, analyticAt_ntC.eventually_analyticAt] with β hn ha
  have hd : HasDerivAt pC (ntC β + β * deriv ntC β) β := by
    have := (hasDerivAt_id' β).mul ha.differentiableAt.hasDerivAt
    exact this.congr_deriv (by simp)
  rw [hd.deriv]
  rw [hn]; ring

lemma Hf_taylor : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)),
    (q.1 - q.2) ^ 2 * Hf q = -(pC q.1 - pC q.2 - deriv pC q.2 * (q.1 - q.2)) := by
  obtain ⟨r, hr, hb⟩ := analytic_ball
  have h1 : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), q.1 ∈ Metric.ball (0 : ℂ) r ∧ q.2 ∈ Metric.ball (0 : ℂ) r := by
    have a1 : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), q.1 ∈ Metric.ball (0 : ℂ) r :=
      continuous_fst.continuousAt.eventually (Metric.ball_mem_nhds _ hr)
    have a2 : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), q.2 ∈ Metric.ball (0 : ℂ) r :=
      continuous_snd.continuousAt.eventually (Metric.ball_mem_nhds _ hr)
    exact a1.and a2
  filter_upwards [h1] with q ⟨hz, hβ⟩
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, q.2 + (t : ℂ) * (q.1 - q.2) ∈ Metric.ball (0 : ℂ) r := by
    intro t ht
    have hc := (convex_ball (0 : ℂ) r) hβ hz (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1 (by ring)
    convert hc using 1
    simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hHf : Hf q = -∫ t in (0 : ℝ)..1, (1 - (t : ℂ)) * pC2 (q.2 + (t : ℂ) * (q.1 - q.2)) := rfl
  have hT := taylor2_seg (p := pC) (p1 := deriv pC) (p2 := pC2) (z := q.1) (β := q.2)
    (fun t ht => ((hb _ (hseg t ht)).differentiableAt.hasDerivAt))
    (fun t ht => ((hb _ (hseg t ht)).deriv.differentiableAt.hasDerivAt))
    (by
      intro t ht
      have h2 : ContinuousAt pC2 ((fun s : ℝ => q.2 + (s : ℂ) * (q.1 - q.2)) t) :=
        (hb _ (hseg t ht)).deriv.deriv.continuousAt
      have h3 : ContinuousAt (fun s : ℝ => q.2 + (s : ℂ) * (q.1 - q.2)) t := by fun_prop
      exact (ContinuousAt.comp (g := pC2) (f := fun s : ℝ => q.2 + (s : ℂ) * (q.1 - q.2)) h2 h3).continuousWithinAt)
  rw [hHf, mul_neg, ← hT]

/-! ### The divided-difference equation for `R` -/

/-- The scalar equation `d² R + d z R² + z(z-β)R³/3 + H = 0` (`ct:cfu-div`), `p = (R, (z, β))`. -/
noncomputable def G1 (p : ℂ × (ℂ × ℂ)) : ℂ :=
  dC p.2.2 ^ 2 * p.1 + dC p.2.2 * p.2.1 * p.1 ^ 2 + (1 / 3) * p.2.1 * (p.2.1 - p.2.2) * p.1 ^ 3 + Hf p.2

/-- The base value `R(0,0) = -H(0,0)/d₀²`. -/
noncomputable def R0 : ℂ := -Hf (0, 0) / ((CtCfu.d0 : ℝ) : ℂ) ^ 2

lemma d0C_ne : ((CtCfu.d0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast CtCfu.d0_pos.ne'

lemma G1_base : G1 (R0, (0, 0)) = 0 := by
  unfold G1 R0
  simp only [dC_zero]
  have := d0C_ne
  field_simp
  ring

lemma contDiffAt_G1 : ContDiffAt ℂ ∞' G1 (R0, (0, 0)) := by
  unfold G1
  have hd : ContDiffAt ℂ ∞' (fun p : ℂ × (ℂ × ℂ) => dC p.2.2) (R0, (0, 0)) :=
    ContDiffAt.comp (g := dC) (f := fun p : ℂ × (ℂ × ℂ) => p.2.2) (R0, (0, 0)) (by simpa using contDiffAt_dC)
      (contDiff_snd.comp contDiff_snd).contDiffAt
  have hH : ContDiffAt ℂ ∞' (fun p : ℂ × (ℂ × ℂ) => Hf p.2) (R0, (0, 0)) :=
    ContDiffAt.comp (g := Hf) (f := fun p : ℂ × (ℂ × ℂ) => p.2) (R0, (0, 0)) (by simpa using contDiffAt_Hf)
      contDiff_snd.contDiffAt
  have hR : ContDiff ℂ ∞' (fun p : ℂ × (ℂ × ℂ) => p.1) := contDiff_fst
  have hz : ContDiff ℂ ∞' (fun p : ℂ × (ℂ × ℂ) => p.2.1) := contDiff_fst.comp contDiff_snd
  have hb : ContDiff ℂ ∞' (fun p : ℂ × (ℂ × ℂ) => p.2.2) := contDiff_snd.comp contDiff_snd
  exact ((((hd.pow 2).mul hR.contDiffAt).add ((hd.mul hz.contDiffAt).mul (hR.contDiffAt.pow 2))).add
    (((contDiffAt_const.mul hz.contDiffAt).mul (hz.sub hb).contDiffAt).mul (hR.contDiffAt.pow 3))).add hH

lemma hasDerivAt_G1_base : HasDerivAt (fun R : ℂ => G1 (R, (0, 0))) (((CtCfu.d0 : ℝ) : ℂ) ^ 2) R0 := by
  have h : (fun R : ℂ => G1 (R, (0, 0))) = fun R => ((CtCfu.d0 : ℝ) : ℂ) ^ 2 * R + Hf (0, 0) := by
    funext R; simp [G1, dC_zero]
  rw [h]
  exact ((hasDerivAt_id R0).const_mul _).add_const _ |>.congr_deriv (by simp)

lemma Hf_zero_real : starRingEnd ℂ (Hf (0, 0)) = Hf (0, 0) := by
  have := Hf_conj (0, 0)
  simpa [conj2] using this.symm

lemma conj_R0 : starRingEnd ℂ R0 = R0 := by
  unfold R0
  rw [map_div₀, map_neg, Hf_zero_real, map_pow, Complex.conj_ofReal]

lemma G1_sym : ∀ᶠ p in 𝓝 (R0, ((0 : ℂ), (0 : ℂ))),
    G1 (starRingEnd ℂ p.1, conj2 p.2) = starRingEnd ℂ (G1 p) := by
  have hb : Tendsto (fun p : ℂ × (ℂ × ℂ) => p.2.2) (𝓝 (R0, ((0 : ℂ), (0 : ℂ)))) (𝓝 0) :=
    (continuous_snd.comp continuous_snd).continuousAt.tendsto
  filter_upwards [hb.eventually dC_conj] with p hp
  unfold G1
  have hH := Hf_conj p.2
  simp only [conj2] at hH
  simp only [conj2, map_add, map_mul, map_pow, map_sub, hp, hH]
  have h3 : starRingEnd ℂ (1 / 3 : ℂ) = 1 / 3 := by rw [map_div₀, map_one, map_ofNat]
  rw [h3]

/-- The solution `R(z;β)` of the divided-difference equation. -/
theorem exists_Rf : ∃ R : ℂ × ℂ → ℂ, ContDiffAt ℂ ∞' R (0, 0) ∧ R (0, 0) = R0 ∧
    (∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), G1 (R q, q) = 0) ∧
    ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), R (conj2 q) = starRingEnd ℂ (R q) := by
  obtain ⟨ξ, h1, h2, h3, -, h5⟩ := scalar_ift_conj (g := G1) (x0 := R0) (q0 := ((0 : ℂ), (0 : ℂ)))
    (g1 := ((CtCfu.d0 : ℝ) : ℂ) ^ 2) contDiffAt_G1 G1_base hasDerivAt_G1_base
    (pow_ne_zero 2 d0C_ne) conj_R0 (by simp [conj2]) G1_sym
  exact ⟨ξ, h1, h2, h3, h5⟩

/-- `R(z;β)`. -/
noncomputable def Rf : ℂ × ℂ → ℂ := Classical.choose exists_Rf

lemma contDiffAt_Rf : ContDiffAt ℂ ∞' Rf (0, 0) := (Classical.choose_spec exists_Rf).1
lemma Rf_zero : Rf (0, 0) = R0 := (Classical.choose_spec exists_Rf).2.1
lemma Rf_eq : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), G1 (Rf q, q) = 0 := (Classical.choose_spec exists_Rf).2.2.1
lemma Rf_conj : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), Rf (conj2 q) = starRingEnd ℂ (Rf q) :=
  (Classical.choose_spec exists_Rf).2.2.2

/-- `V(z;β) = d(β) + (z-β) R(z;β)`; the inverse chart is `W(x) = x V(x²;β)`. -/
noncomputable def Vf (q : ℂ × ℂ) : ℂ := dC q.2 + (q.1 - q.2) * Rf q

lemma contDiffAt_Vf : ContDiffAt ℂ ∞' Vf (0, 0) := by
  unfold Vf
  have hd : ContDiffAt ℂ ∞' (fun q : ℂ × ℂ => dC q.2) (0, 0) :=
    ContDiffAt.comp (g := dC) (f := fun q : ℂ × ℂ => q.2) (0, 0) (by simpa using contDiffAt_dC) contDiff_snd.contDiffAt
  exact hd.add ((contDiff_fst.sub contDiff_snd).contDiffAt.mul contDiffAt_Rf)

lemma Vf_zero : Vf (0, 0) = ((CtCfu.d0 : ℝ) : ℂ) := by simp [Vf, dC_zero]

lemma Vf_diag (β : ℂ) : Vf (β, β) = dC β := by simp [Vf]

lemma Vf_conj : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)), Vf (conj2 q) = starRingEnd ℂ (Vf q) := by
  have hb : Tendsto (fun q : ℂ × ℂ => q.2) (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 0) := continuous_snd.continuousAt.tendsto
  filter_upwards [Rf_conj, hb.eventually dC_conj] with q hq hd
  unfold Vf
  simp only [conj2, map_add, map_mul, map_sub, hd]
  have : Rf (starRingEnd ℂ q.1, starRingEnd ℂ q.2) = starRingEnd ℂ (Rf q) := hq
  rw [this]

/-- **The key identity** `L(β) - p(z) = -a(β) V - z V³/3`. -/
theorem key_identity : ∀ᶠ q in 𝓝 ((0 : ℂ), (0 : ℂ)),
    LC q.2 - pC q.1 = -aC q.2 * Vf q - q.1 * Vf q ^ 3 / 3 := by
  have hb : Tendsto (fun q : ℂ × ℂ => q.2) (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 0) := continuous_snd.continuousAt.tendsto
  filter_upwards [Rf_eq, Hf_taylor, hb.eventually dC_cube, hb.eventually deriv_pC_eq] with q hE1 hE2 hE3 hE4
  obtain ⟨z, β⟩ := q
  simp only at hE3 hE4 hE2 ⊢
  unfold G1 at hE1
  simp only at hE1
  unfold Vf LC aC
  simp only
  unfold fC at hE3
  have hp : pC β = β * ntC β := rfl
  rw [hE4] at hE2
  rw [hp] at hE2
  linear_combination ((z - β) ^ 2) * hE1 - hE2 + (z / 3 - β) * hE3

end FormalResearch.SignUncertainty.CtChart
