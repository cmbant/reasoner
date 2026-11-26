module

public import FormalResearch.SignUncertainty.CtChartDeriv

/-!
# The geometric amplitude `μ(y;β)` of the CFU chart and its saddle normalisation `μ(d²β; β) = 1` (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 3 (`M(s;a) = √(m'(T)/(2s)) T_s`, `M(±√(-a); a) ≡ 1`).
**Proved.**  `μ(y;β) = √(U k(Z)/2) · T_s` with `T_s = 1/(V + 2 Z V_z)`.  At the saddle `Z = β`, `U = 1/d`, `V = d`, `V_z = R(β,β)`, and
`k(β) = 2 d (d + 2 β R(β,β))²` follows from the divided-difference equation at `z = β` and `k = 2n + 2z n'`, `n = 3ñ + 2z ñ'`.
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.CtChart

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Principal square root `exp(log x / 2)`. -/
noncomputable def csq (x : ℂ) : ℂ := Complex.exp (Complex.log x / 2)

lemma csq_sq {x : ℂ} (hx : x ≠ 0) : csq x ^ 2 = x := by
  unfold csq
  rw [← Complex.exp_nat_mul]
  have : (↑(2 : ℕ) : ℂ) * (Complex.log x / 2) = Complex.log x := by push_cast; ring
  rw [this, Complex.exp_log hx]

/-- The geometric amplitude `μ(y;β) = √(U k(Z)/2) · T_s`. -/
noncomputable def muf (q : ℂ × ℂ) : ℂ := csq (Uf q * kC (Zf q) / 2) * Tsd q

lemma Sigma_zero : Uf (0, 0) * kC (Zf (0, 0)) / 2 = ((CtCfu.d0 : ℝ) : ℂ) ^ 2 := by
  rw [Uf_zero, Zf_zero, kC_zero]
  have h3 := d0C_cube
  have h0 := d0C_ne
  have : (π : ℂ) ^ 2 = 12 * ((CtCfu.d0 : ℝ) : ℂ) ^ 3 := by rw [h3]; ring
  rw [this]
  field_simp
  ring

lemma csq_d0_sq : csq (((CtCfu.d0 : ℝ) : ℂ) ^ 2) = ((CtCfu.d0 : ℝ) : ℂ) := by
  have hpos : (0 : ℝ) < CtCfu.d0 := CtCfu.d0_pos
  have : ((CtCfu.d0 : ℝ) : ℂ) ^ 2 = ((CtCfu.d0 ^ 2 : ℝ) : ℂ) := by push_cast; ring
  unfold csq
  rw [this, ← Complex.ofReal_log (by positivity), Real.log_pow]
  have h3 : ((((2 : ℕ) : ℝ) * Real.log CtCfu.d0 : ℝ) : ℂ) / 2 = ((Real.log CtCfu.d0 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h3, ← Complex.ofReal_exp, Real.exp_log hpos]

lemma slit_Sigma_zero : Uf (0, 0) * kC (Zf (0, 0)) / 2 ∈ Complex.slitPlane := by
  rw [Sigma_zero]
  have : ((CtCfu.d0 : ℝ) : ℂ) ^ 2 = ((CtCfu.d0 ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this]
  exact Complex.ofReal_mem_slitPlane.mpr (by have := CtCfu.d0_pos; positivity)

lemma contDiffAt_kZ : ContDiffAt ℂ ∞' (fun q : ℂ × ℂ => kC (Zf q)) (0, 0) := by
  have hk : ContDiffAt ℂ ∞' kC (Zf (0, 0)) := by rw [Zf_zero]; exact contDiffAt_kC
  exact ContDiffAt.comp (g := kC) (f := Zf) (0, 0) hk contDiffAt_Zf

lemma contDiffAt_muf : ContDiffAt ℂ ∞' muf (0, 0) := by
  unfold muf
  have h1 : ContDiffAt ℂ ∞' (fun q : ℂ × ℂ => Uf q * kC (Zf q) / 2) (0, 0) :=
    (contDiffAt_Uf.mul contDiffAt_kZ).div_const _
  have h2 : ContDiffAt ℂ ∞' (fun q : ℂ × ℂ => csq (Uf q * kC (Zf q) / 2)) (0, 0) := by
    unfold csq
    refine Complex.contDiff_exp.contDiffAt.comp (0, 0) ?_
    exact ((Complex.contDiffAt_log slit_Sigma_zero).comp (0, 0) h1).div_const _
  exact h2.mul contDiffAt_Tsd

lemma muf_zero : muf (0, 0) = 1 := by
  unfold muf
  rw [Sigma_zero, csq_d0_sq, Tsd_zero]
  exact mul_one_div_cancel d0C_ne

/-! ### The saddle normalisation -/

lemma tendsto_diag : Tendsto (fun β : ℂ => (β, β)) (𝓝 0) (𝓝 ((0 : ℂ), (0 : ℂ))) := by
  have : ContinuousAt (fun β : ℂ => (β, β)) 0 := continuousAt_id.prodMk continuousAt_id
  simpa using this.tendsto

lemma Vz_diag : ∀ᶠ β in 𝓝 (0 : ℂ), Vz (β, β) = Rf (β, β) := by
  have hRd : ∀ᶠ β in 𝓝 (0 : ℂ), DifferentiableAt ℂ Rf (β, β) := tendsto_diag.eventually (ev_diff contDiffAt_Rf)
  have hVd : ∀ᶠ β in 𝓝 (0 : ℂ), DifferentiableAt ℂ Vf (β, β) := tendsto_diag.eventually (ev_diff contDiffAt_Vf)
  filter_upwards [hRd, hVd] with β hR hV
  have h1 := hasDerivAt_slice1 hV
  have h2 : HasDerivAt (fun z : ℂ => Vf (z, β)) (Rf (β, β)) β := by
    have hRs := hasDerivAt_slice1 hR
    have hs : HasDerivAt (fun z : ℂ => (z - β) * Rf (z, β)) (1 * Rf (β, β) + (β - β) * fderiv ℂ Rf (β, β) (1, 0)) β :=
      ((hasDerivAt_id' β).sub_const β).mul hRs
    have := hs.const_add (dC β)
    simpa [Vf] using this
  exact h1.unique h2

lemma pC2_eq : ∀ᶠ β in 𝓝 (0 : ℂ), pC2 β = (deriv nC β - deriv ntC β) / 2 := by
  have h1 : ∀ᶠ β in 𝓝 (0 : ℂ), ∀ᶠ z in 𝓝 β, deriv pC z = (nC z - ntC z) / 2 := deriv_pC_eq.eventually_nhds
  filter_upwards [h1, analyticAt_nC.eventually_analyticAt, analyticAt_ntC.eventually_analyticAt] with β hβ hn hnt
  unfold pC2
  have hβ' : deriv pC =ᶠ[𝓝 β] fun z => (nC z - ntC z) / 2 := hβ
  have := Filter.EventuallyEq.deriv_eq (𝕜 := ℂ) hβ'
  rw [this]
  exact (((hn.differentiableAt.hasDerivAt).sub hnt.differentiableAt.hasDerivAt).div_const 2).deriv

lemma Hf_diag (β : ℂ) : Hf (β, β) = -(pC2 β / 2) := by
  unfold Hf
  simp only [sub_self, mul_zero, add_zero]
  rw [intervalIntegral.integral_mul_const]
  have : ∫ t in (0 : ℝ)..1, (1 - (t : ℂ)) = 1 / 2 := by
    have h := intervalIntegral.integral_ofReal (μ := MeasureTheory.volume) (a := 0) (b := 1) (f := fun t : ℝ => 1 - t)
    have e : ∫ t in (0 : ℝ)..1, (1 - t) = 1 / 2 := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (by simp), integral_id]; simp; norm_num
    simp only [Complex.ofReal_sub, Complex.ofReal_one] at h
    rw [h, e]; push_cast; ring
  rw [this]; ring

/-- `k(β) = 2 d (d + 2 β R(β,β))²`. -/
lemma kC_diag : ∀ᶠ β in 𝓝 (0 : ℂ), kC β = 2 * dC β * (dC β + 2 * β * Rf (β, β)) ^ 2 := by
  have hG : ∀ᶠ β in 𝓝 (0 : ℂ), G1 (Rf (β, β), (β, β)) = 0 := tendsto_diag.eventually Rf_eq
  filter_upwards [hG, rel_k, rel_n, dC_cube, pC2_eq, analyticAt_nC.eventually_analyticAt] with β hG hk hn hd3 hp2 _
  unfold G1 at hG
  simp only [sub_self, mul_zero, zero_mul] at hG
  rw [Hf_diag] at hG
  unfold fC at hd3
  linear_combination hk - hn - 2 * hd3 - 4 * β * hp2 - 8 * β * hG

lemma tendsto_saddle : Tendsto (fun β : ℂ => (dC β ^ 2 * β, β)) (𝓝 0) (𝓝 ((0 : ℂ), (0 : ℂ))) := by
  have hc : ContinuousAt dC 0 := contDiffAt_dC.continuousAt
  have : ContinuousAt (fun β : ℂ => (dC β ^ 2 * β, β)) 0 := ((hc.pow 2).mul continuousAt_id).prodMk continuousAt_id
  simpa using this.tendsto

lemma dC_ne : ∀ᶠ β in 𝓝 (0 : ℂ), dC β ≠ 0 := by
  have hc : ContinuousAt dC 0 := contDiffAt_dC.continuousAt
  exact hc.eventually_ne (by rw [dC_zero]; exact d0C_ne)

/-- **Saddle normalisation** `μ(d(β)²β; β) = 1` (`M(±√(-a); a) ≡ 1`). -/
theorem saddle_mu : ∀ᶠ β in 𝓝 (0 : ℂ), muf (dC β ^ 2 * β, β) = 1 := by
  have hcont : ContinuousAt (fun β : ℂ => muf (dC β ^ 2 * β, β)) 0 := by
    have h1 : ContinuousAt muf ((fun β : ℂ => (dC β ^ 2 * β, β)) 0) := by
      have : (fun β : ℂ => (dC β ^ 2 * β, β)) 0 = (0, 0) := by simp
      rw [this]; exact contDiffAt_muf.continuousAt
    have h2 : ContinuousAt (fun β : ℂ => (dC β ^ 2 * β, β)) 0 :=
      (((contDiffAt_dC.continuousAt).pow 2).mul continuousAt_id).prodMk continuousAt_id
    exact ContinuousAt.comp (g := muf) (f := fun β : ℂ => (dC β ^ 2 * β, β)) h1 h2
  have h0 : muf (dC 0 ^ 2 * 0, 0) = 1 := by simpa using muf_zero
  have hnear : ∀ᶠ β in 𝓝 (0 : ℂ), ‖muf (dC β ^ 2 * β, β) - 1‖ < 1 := by
    have := hcont.eventually (Metric.ball_mem_nhds (muf (dC 0 ^ 2 * 0, 0)) (by norm_num : (0 : ℝ) < 1))
    refine this.mono fun β hβ => ?_
    rw [h0] at hβ
    simpa [Metric.mem_ball, dist_eq_norm] using hβ
  filter_upwards [hnear, saddle_Z, Uf_saddle, Vz_diag, kC_diag, dC_ne, tendsto_saddle.eventually Tsd_den_ne] with β hn hZ hU hV hk hd hD
  have hD' : dC β + 2 * β * Rf (β, β) ≠ 0 := by
    have := hD
    rw [hZ, Vf_diag, hV] at this
    exact this
  have hTs : Tsd (dC β ^ 2 * β, β) = 1 / (dC β + 2 * β * Rf (β, β)) := by
    unfold Tsd
    rw [hZ, Vf_diag, hV]
  have hmu : muf (dC β ^ 2 * β, β) = csq (1 / dC β * kC β / 2) * (1 / (dC β + 2 * β * Rf (β, β))) := by
    unfold muf
    rw [hU, hZ, hTs]
  have hX : 1 / dC β * kC β / 2 = (dC β + 2 * β * Rf (β, β)) ^ 2 := by
    rw [hk]; field_simp
  rw [hX] at hmu
  have hsq : csq ((dC β + 2 * β * Rf (β, β)) ^ 2) ^ 2 = (dC β + 2 * β * Rf (β, β)) ^ 2 :=
    csq_sq (pow_ne_zero 2 hD')
  set D := dC β + 2 * β * Rf (β, β) with hDdef
  set m := muf (dC β ^ 2 * β, β) with hm
  have hm2 : m ^ 2 = 1 := by
    rw [hmu, mul_pow, hsq]; field_simp
  have hprod : (m - 1) * (m + 1) = 0 := by linear_combination hm2
  have hne : m + 1 ≠ 0 := by
    intro h
    have : m - 1 = -2 := by linear_combination h
    rw [this] at hn
    norm_num at hn
  have := (mul_eq_zero.mp hprod).resolve_right hne
  linear_combination this

end FormalResearch.SignUncertainty.CtChart
