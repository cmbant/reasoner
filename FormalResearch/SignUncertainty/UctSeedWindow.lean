module

public import FormalResearch.SignUncertainty.UctSeedWindowQ
public import FormalResearch.SignUncertainty.UctSeedWindowRef
public import FormalResearch.SignUncertainty.UctSeedAdmiss

/-!
# `uct:seed-asymp` (1): the fixed Airy window of `W^seed` (F2a)

For `ε = ±1`, `0 ≤ δ ≤ 1`, `ξ > 0` with `|S_eff| ≤ S_w` (`S_eff = hbS c ξ = c^{2/3}L/π²`) and `c ≥ c₀(S_w)`, the normalised density
`h_norm^{seed} = (c^{1/3}/2π) ∫ K₀(iτ,ξ) W^{seed}(iτ) dτ` (`seedHnorm`) satisfies
`h_norm^{seed} = (k/c_s) F_{*,δ}(-β₁ S_eff + β₁ c₀^ε ς) + O_{S_w}(ς²)`, `ς = c^{-1/3}`, `c₀^ε = θ_ε'(0)/π²` (`seed_window`).

Proof: substitute `τ = ς v`, shift the line to `Re w = 1` (`strip_shift_weight`), compare `K₀` with `refKernel S ς`
(`main_line_diff_sym`), replace `W^{seed}(ς w) = Q(ς w) T(c_s w)` by `e^{-λ ς w} T(c_s w)` on `|v| ≤ V` and bound the tail by the Gaussian
decay of the reference kernel (`ref_symbol_diff`, `seedQ_expansion`), shift the reference integral back and evaluate it by the
Airy inversion identity (`airy_reference_identity`).

Class: proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

/-- The normalised density `h_norm^{seed}` of `(uct:hnorm)` for the seed `W^{seed,ε}`. -/
noncomputable def seedHnorm (ε δ c ξ : ℝ) : ℂ :=
  ((c ^ (1 / 3 : ℝ) / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ * seedW ε δ c ((τ : ℂ) * Complex.I)

lemma continuous_uctFstarDelta (δ : ℝ) : Continuous (uctFstarDelta δ) := by
  unfold uctFstarDelta
  exact continuous_ceF1.neg.sub (continuous_const.mul (continuous_ceG1 _))

lemma sq_mul_neg_rpow_le {t : ℝ} (ht : 1 ≤ t) : t ^ 2 * t ^ (-(5 / 2 : ℝ)) ≤ 1 := by
  have ht0 : 0 < t := by linarith
  have : t ^ 2 * t ^ (-(5 / 2 : ℝ)) = t ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht0]; norm_num
  rw [this]
  exact Real.rpow_le_one_of_one_le_of_nonpos ht (by norm_num)

lemma seedHnorm_eq {ε δ c ξ : ℝ} (hc : 0 < c) :
    seedHnorm ε δ c ξ = ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ v : ℝ,
      mellinK0 c ((liftEps c : ℂ) * ((v : ℂ) * Complex.I)) ξ *
        seedW ε δ c ((liftEps c : ℂ) * ((v : ℂ) * Complex.I)) := by
  set g : ℝ → ℂ := fun τ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * seedW ε δ c ((τ : ℂ) * Complex.I) with hg
  have hς := liftEps_pos hc
  have h1 := MeasureTheory.Measure.integral_comp_mul_left g (liftEps c)
  have h2 : (∫ v : ℝ, mellinK0 c ((liftEps c : ℂ) * ((v : ℂ) * Complex.I)) ξ *
      seedW ε δ c ((liftEps c : ℂ) * ((v : ℂ) * Complex.I))) = ∫ v : ℝ, g (liftEps c * v) := by
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    have : ((liftEps c * v : ℝ) : ℂ) * Complex.I = (liftEps c : ℂ) * ((v : ℂ) * Complex.I) := by push_cast; ring
    simp only [hg, this]
  have hinv : (liftEps c)⁻¹ = c ^ (1 / 3 : ℝ) := by
    unfold liftEps; rw [Real.rpow_neg hc.le, inv_inv]
  rw [h2, h1, abs_of_pos (inv_pos.mpr hς), Complex.real_smul, hinv]
  unfold seedHnorm
  rw [← hg]
  generalize (∫ τ : ℝ, g τ) = I
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

set_option maxHeartbeats 1600000 in
theorem seed_window {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (Sw : ℝ) :
    ∃ c0 C : ℝ, 0 < C ∧ ∀ {c δ ξ : ℝ}, c0 ≤ c → 0 ≤ δ → δ ≤ 1 → 0 < ξ → |hbS c ξ| ≤ Sw →
      ‖seedHnorm ε δ c ξ - ((ceK / ceCs * uctFstarDelta δ (-(ceBeta1 * hbS c ξ) +
          ceBeta1 * (deriv (outerTheta ε) 0 / Real.pi ^ 2) * liftEps c) : ℝ) : ℂ)‖ ≤ C * liftEps c ^ 2 := by
  obtain ⟨c1, CW, hc1, hCW, hSy⟩ := seedSy_bound ε
  obtain ⟨CT, hCT, hT⟩ := seedT_unif
  obtain ⟨c2, Cq, hc2, hCq, hQ⟩ := seedQ_expansion hε
  obtain ⟨Cm, hCm, hmain⟩ := main_line_diff_sym Sw CW hCW
  set lam : ℝ := seedLam ε with hlam
  set θ : ℝ := deriv (outerTheta ε) 0 with hθ
  have hlamθ : lam = θ + 1 / 2 := rfl
  set CE : ℝ := Real.exp |lam| * CT with hCE
  obtain ⟨Cr, hCr, href⟩ := ref_symbol_diff Sw (2 * Cq * CT) CW CE (by positivity) hCW.le (by positivity)
  refine ⟨max (max c1 c2) 32768, (Cm + Cr) / (2 * Real.pi), by positivity, fun {c δ ξ} hc hδ0 hδ1 hξ hS => ?_⟩
  have hcc1 : c1 ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc
  have hcc2 : c2 ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
  have hc32 : 32768 ≤ c := (le_max_right _ _).trans hc
  have hc0 : 0 < c := by linarith
  set ς : ℝ := liftEps c with hςdef
  have hς : 0 < ς := liftEps_pos hc0
  have hcube : c * ς ^ 3 = 1 := by have := liftEps_cube_mul hc0; linarith
  have hς1 : ς ≤ 1 / 32 := liftEps_le_of_large hc32
  have hς2 : ς ≤ 1 / 2 := by linarith
  set S : ℝ := hbS c ξ with hSdef
  have hL : Real.log (Real.pi ^ 2 * ξ) = Real.pi ^ 2 * ς ^ 2 * S := hb_L_eq hc0
  have hXU := hasU2_uctFstarDelta δ
  have hXc := continuous_uctFstarDelta δ
  have hpi : 9 < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  -- the symbol on the scaled strip
  set Sy : ℂ → ℂ := fun w => seedW ε δ c ((ς : ℂ) * w) with hSydef
  have hSyb : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 → ‖Sy w‖ ≤ CW * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) :=
    fun w h0 h1 => hSy c δ hcc1 hδ0 hδ1 w h0 h1
  have adm := seedW_stripAdmissFull hε hδ0 hδ1 hc0
  have hlin : Differentiable ℂ (fun w : ℂ => (ς : ℂ) * w) := (differentiable_const _).mul differentiable_id
  have hSyc : ContinuousOn Sy {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1} :=
    adm.cont.comp hlin.continuous.continuousOn (fun w hw => by
      simp only [Set.mem_ofPred_eq, re_mul_real]
      constructor <;> nlinarith [hw.1, hw.2])
  have hSyd : DifferentiableOn ℂ Sy {w : ℂ | 0 < w.re ∧ w.re < 1} :=
    adm.hol.comp hlin.differentiableOn (fun w hw => by
      simp only [Set.mem_ofPred_eq, re_mul_real]
      constructor <;> nlinarith [hw.1, hw.2])
  -- the exact kernel
  obtain ⟨hKc, hKd, hKb⟩ := K0_kernel_props (c := c) (S := S) hς hcube hς2 hξ hL
  set BK : ℝ := 2 * Real.exp (1 + Real.pi ^ 2 * |S|) with hBK
  have hBK0 : 0 ≤ BK := by positivity
  have hAb : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
      ‖mellinK0 c ((ς : ℂ) * w) ξ * Sy w‖ ≤ (BK * CW) * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by
    intro w h0 h1
    rw [norm_mul]
    calc ‖mellinK0 c ((ς : ℂ) * w) ξ‖ * ‖Sy w‖ ≤ BK * (CW * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) :=
          mul_le_mul (hKb w h0 h1) (hSyb w h0 h1) (norm_nonneg _) hBK0
      _ = _ := by ring
  have shA : ∫ v : ℝ, mellinK0 c ((ς : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ * Sy ((1 : ℂ) + (v : ℂ) * Complex.I) =
      ∫ v : ℝ, mellinK0 c ((ς : ℂ) * ((v : ℂ) * Complex.I)) ξ * Sy ((v : ℂ) * Complex.I) := by
    have := strip_shift_weight (H := fun w => mellinK0 c ((ς : ℂ) * w) ξ * Sy w) (B := BK * CW)
      (hKc.mul hSyc) (hKd.mul hSyd) hAb
    simpa using this
  -- reference kernels
  set Eref : ℝ := Real.exp (Real.pi ^ 2 / 36 + Real.pi ^ 2 * Sw + 1) with hEref
  have hEref0 : 0 < Eref := Real.exp_pos _
  have hRb : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 → ‖refKernel S ς w‖ ≤ Eref := by
    intro w h0 h1
    have := norm_refKernel_strip_le (S := S) (ε := ς) (σ := w.re) (v := w.im) (Sw := Sw) (by linarith) hS h0 h1
    rwa [Complex.re_add_im] at this
  have hRdiff : Differentiable ℂ (refKernel S ς) := by unfold refKernel; fun_prop
  have hRθdiff : Differentiable ℂ (refKernel S (-2 * θ * ς)) := by unfold refKernel; fun_prop
  -- the reference symbol
  set Ey : ℂ → ℂ := fun w => Complex.exp (-((lam : ℝ) : ℂ) * ((ς : ℂ) * w)) * seedT δ ((ceCs : ℂ) * w) with hEydef
  have hexpb : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 → ‖Complex.exp (-((lam : ℝ) : ℂ) * ((ς : ℂ) * w))‖ ≤ Real.exp |lam| := by
    intro w h0 h1
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have : (-((lam : ℝ) : ℂ) * ((ς : ℂ) * w)).re = -(lam * (ς * w.re)) := by
      simp [Complex.mul_re]
    rw [this]
    have h2 : ς * w.re ≤ 1 := by nlinarith
    have h3 : 0 ≤ ς * w.re := by positivity
    calc -(lam * (ς * w.re)) ≤ |lam * (ς * w.re)| := neg_le_abs _
      _ = |lam| * (ς * w.re) := by rw [abs_mul, abs_of_nonneg h3]
      _ ≤ |lam| * 1 := by gcongr
      _ = |lam| := mul_one _
  have hEyb : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 → ‖Ey w‖ ≤ CE * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by
    intro w h0 h1
    rw [hEydef]; show ‖Complex.exp _ * seedT δ ((ceCs : ℂ) * w)‖ ≤ _
    rw [norm_mul]
    calc _ ≤ Real.exp |lam| * (CT * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) :=
          mul_le_mul (hexpb w h0 h1) (hT δ hδ0 hδ1 w h0) (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [hCE]; ring
  have hTc : ContinuousOn (fun w : ℂ => seedT δ ((ceCs : ℂ) * w)) {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1} :=
    (seedT_continuousOn δ).comp (by fun_prop : Continuous fun w : ℂ => (ceCs : ℂ) * w).continuousOn
      (fun w hw => by
        simp only [Set.mem_ofPred_eq, re_mul_real]
        exact mul_nonneg ceCs_pos.le hw.1)
  have hEyc : ContinuousOn Ey {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1} := by
    refine ContinuousOn.mul ?_ hTc
    exact (by fun_prop : Continuous fun w : ℂ => Complex.exp (-((lam : ℝ) : ℂ) * ((ς : ℂ) * w))).continuousOn
  have hRc : ContinuousOn (refKernel S ς) {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1} := hRdiff.continuous.continuousOn
  have hRθc : ContinuousOn (refKernel S (-2 * θ * ς)) {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1} := hRθdiff.continuous.continuousOn
  -- Rθ = R * exp
  have hRθeq : ∀ w : ℂ, refKernel S (-2 * θ * ς) w = refKernel S ς w * Complex.exp (-((lam : ℝ) : ℂ) * ((ς : ℂ) * w)) := by
    intro w; rw [hlamθ, refKernel_mul_exp]
  have hRθb : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 → ‖refKernel S (-2 * θ * ς) w‖ ≤ Eref * Real.exp |lam| := by
    intro w h0 h1
    rw [hRθeq, norm_mul]
    exact mul_le_mul (hRb w h0 h1) (hexpb w h0 h1) (norm_nonneg _) hEref0.le
  -- near-window bound on Sy - Ey
  have hc23 : c ^ (-(2 / 3 : ℝ)) = ς ^ 2 := by
    rw [hςdef]; unfold liftEps
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hnear : ∀ v : ℝ, ς * (1 + |v|) ≤ 1 / 4 →
      ‖Sy ((1 : ℂ) + (v : ℂ) * Complex.I) - Ey ((1 : ℂ) + (v : ℂ) * Complex.I)‖ ≤ (2 * Cq * CT) * ς ^ 2 := by
    intro v hv
    set w : ℂ := (1 : ℂ) + (v : ℂ) * Complex.I with hw
    have hwre : w.re = 1 := by simp [hw]
    have hwim : w.im = v := by simp [hw]
    have hwn : ‖w‖ ≤ 1 + |v| := by
      refine (norm_add_le _ _).trans ?_
      simp
    set ζ : ℂ := (ς : ℂ) * w with hζ
    have hζn : ‖ζ‖ ≤ ς * (1 + |v|) := by
      rw [hζ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hς]
      exact mul_le_mul_of_nonneg_left hwn hς.le
    have hζ4 : ‖ζ‖ ≤ 1 / 4 := hζn.trans hv
    have hζstrip : ζ ∈ closedStrip := by
      refine ⟨?_, ?_⟩
      · simp only [hζ, re_mul_real, hwre]; positivity
      · simp only [hζ, re_mul_real, hwre]; linarith
    have hζball : ζ ∈ ball (0 : ℂ) (1 / 2) := by
      rw [Metric.mem_ball, dist_zero_right]; linarith
    have hscale : (seedScale c : ℂ) * ζ = (ceCs : ℂ) * w := by
      rw [hζ, ← mul_assoc, ← Complex.ofReal_mul, hςdef, seedScale_mul_liftEps hc0]
    have hSyw : Sy w = seedQ ε δ c ζ * seedT δ ((ceCs : ℂ) * w) := by
      show seedW ε δ c ζ = _
      rw [seedW_eq_Q_mul hζstrip hζball, hscale]
    have hdiff : Sy w - Ey w = (seedQ ε δ c ζ - Complex.exp (-((lam : ℝ) : ℂ) * ζ)) * seedT δ ((ceCs : ℂ) * w) := by
      rw [hSyw]; show _ = _; simp only [hEydef]; ring
    rw [hdiff, norm_mul]
    have hq := hQ c δ hcc2 hδ0 hδ1 ζ hζ4
    rw [hc23] at hq
    have ht : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
    have hTb := hT δ hδ0 hδ1 w (by rw [hwre]; norm_num)
    rw [hwim] at hTb
    have hς1' : ς ≤ 1 := by linarith
    have hq2 : ‖seedQ ε δ c ζ - Complex.exp (-((lam : ℝ) : ℂ) * ζ)‖ ≤ 2 * Cq * ς ^ 2 * (1 + |v|) ^ 2 := by
      refine hq.trans ?_
      have h1 : ς ^ 2 * ‖ζ‖ ≤ ς ^ 2 * (1 + |v|) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ‖ζ‖ ≤ ς * (1 + |v|) := hζn
          _ ≤ 1 * (1 + |v|) := by gcongr
          _ ≤ (1 + |v|) ^ 2 := by nlinarith
      have h2 : ‖ζ‖ ^ 2 ≤ ς ^ 2 * (1 + |v|) ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hζn 2
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add h1 h2) hCq]
    have hp0 : 0 ≤ (1 + |v|) ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
    have hsq := sq_mul_neg_rpow_le ht
    calc ‖seedQ ε δ c ζ - Complex.exp (-((lam : ℝ) : ℂ) * ζ)‖ * ‖seedT δ ((ceCs : ℂ) * w)‖
        ≤ (2 * Cq * ς ^ 2 * (1 + |v|) ^ 2) * (CT * (1 + |v|) ^ (-(5 / 2 : ℝ))) := by gcongr
      _ = (2 * Cq * CT) * ς ^ 2 * ((1 + |v|) ^ 2 * (1 + |v|) ^ (-(5 / 2 : ℝ))) := by ring
      _ ≤ (2 * Cq * CT) * ς ^ 2 * 1 := by gcongr
      _ = _ := by ring
  -- the three pieces on `Re w = 1`
  have hline : ∀ v : ℝ, ((1 : ℂ) + (v : ℂ) * Complex.I).re = 1 ∧ ((1 : ℂ) + (v : ℂ) * Complex.I).im = v := fun v => by simp
  have hJ1 := hmain (Sy := Sy) (fun {w} h0 h1 => hSyb w h0 h1) hς hcube hς1 hξ hL hS
  have hJ2 := href (Sy := Sy) (Ey := Ey) (S := S) hς hς1 hS
    (fun v => by
      have := hSyb ((1 : ℂ) + (v : ℂ) * Complex.I) (by simp) (by simp)
      rwa [(hline v).2] at this)
    (fun v => by
      have := hEyb ((1 : ℂ) + (v : ℂ) * Complex.I) (by simp) (by simp)
      rwa [(hline v).2] at this)
    hnear
  -- integrability
  have iA := integrable_line_weight (hKc.mul hSyc) hAb
  have i1 := integrable_line_weight (F := fun w => (mellinK0 c ((ς : ℂ) * w) ξ - refKernel S ς w) * Sy w)
    (B := (BK + Eref) * CW) ((hKc.sub hRc).mul hSyc) (fun w h0 h1 => by
      rw [norm_mul]
      calc ‖mellinK0 c ((ς : ℂ) * w) ξ - refKernel S ς w‖ * ‖Sy w‖ ≤ (BK + Eref) * (CW * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) :=
            mul_le_mul ((norm_sub_le _ _).trans (add_le_add (hKb w h0 h1) (hRb w h0 h1))) (hSyb w h0 h1)
              (norm_nonneg _) (by positivity)
        _ = _ := by ring)
  have i2 := integrable_line_weight (F := fun w => refKernel S ς w * (Sy w - Ey w))
    (B := Eref * (CW + CE)) (hRc.mul (hSyc.sub hEyc)) (fun w h0 h1 => by
      rw [norm_mul]
      calc ‖refKernel S ς w‖ * ‖Sy w - Ey w‖ ≤ Eref * ((CW + CE) * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) :=
            mul_le_mul (hRb w h0 h1) ((norm_sub_le _ _).trans (by
              have := hSyb w h0 h1
              have := hEyb w h0 h1
              linarith)) (norm_nonneg _) hEref0.le
        _ = _ := by ring)
  have i3 := integrable_line_weight (F := fun w => refKernel S (-2 * θ * ς) w * seedT δ ((ceCs : ℂ) * w))
    (B := Eref * Real.exp |lam| * CT) (hRθc.mul hTc) (fun w h0 h1 => by
      rw [norm_mul]
      calc ‖refKernel S (-2 * θ * ς) w‖ * ‖seedT δ ((ceCs : ℂ) * w)‖ ≤
            (Eref * Real.exp |lam|) * (CT * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) :=
            mul_le_mul (hRθb w h0 h1) (hT δ hδ0 hδ1 w h0) (norm_nonneg _) (by positivity)
        _ = _ := by ring)
  -- decomposition
  have hdec : ∀ v : ℝ, mellinK0 c ((ς : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ * Sy ((1 : ℂ) + (v : ℂ) * Complex.I) =
      (mellinK0 c ((ς : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ - refKernel S ς ((1 : ℂ) + (v : ℂ) * Complex.I)) *
          Sy ((1 : ℂ) + (v : ℂ) * Complex.I) +
        refKernel S ς ((1 : ℂ) + (v : ℂ) * Complex.I) * (Sy ((1 : ℂ) + (v : ℂ) * Complex.I) - Ey ((1 : ℂ) + (v : ℂ) * Complex.I)) +
        refKernel S (-2 * θ * ς) ((1 : ℂ) + (v : ℂ) * Complex.I) * seedT δ ((ceCs : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) := by
    intro v
    rw [hRθeq]
    simp only [hEydef]
    ring
  have hsplit : ∫ v : ℝ, mellinK0 c ((ς : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ * Sy ((1 : ℂ) + (v : ℂ) * Complex.I) =
      (∫ v : ℝ, (mellinK0 c ((ς : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ - refKernel S ς ((1 : ℂ) + (v : ℂ) * Complex.I)) *
          Sy ((1 : ℂ) + (v : ℂ) * Complex.I)) +
        (∫ v : ℝ, refKernel S ς ((1 : ℂ) + (v : ℂ) * Complex.I) * (Sy ((1 : ℂ) + (v : ℂ) * Complex.I) - Ey ((1 : ℂ) + (v : ℂ) * Complex.I))) +
        ∫ v : ℝ, refKernel S (-2 * θ * ς) ((1 : ℂ) + (v : ℂ) * Complex.I) * seedT δ ((ceCs : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) := by
    have i12 : Integrable fun v : ℝ => (mellinK0 c ((ς : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ -
          refKernel S ς ((1 : ℂ) + (v : ℂ) * Complex.I)) * Sy ((1 : ℂ) + (v : ℂ) * Complex.I) +
        refKernel S ς ((1 : ℂ) + (v : ℂ) * Complex.I) *
          (Sy ((1 : ℂ) + (v : ℂ) * Complex.I) - Ey ((1 : ℂ) + (v : ℂ) * Complex.I)) := i1.add i2
    rw [integral_congr_ae (ae_of_all _ hdec), integral_add i12 i3, integral_add i1 i2]
  -- the reference integral: shift back and Airy inversion
  have hW0 : ∀ {w : ℂ}, 0 ≤ w.re → ‖liftSymbol (uctFstarDelta δ) 0 0 w‖ ≤ CT * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by
    intro w hw
    rw [liftSymbol_zero_order]
    exact hT δ hδ0 hδ1 w hw
  have sh3 := shift_kernel_lift hXU (le_refl (0 : ℝ)) 0 (CW := CT) (BK := Eref * Real.exp |lam|) hW0
    hRθc hRθdiff.differentiableOn hRθb
  simp only [liftSymbol_zero_order] at sh3
  have href3 := airy_reference_identity hXU hXc (le_refl (0 : ℝ)) 0 (ξ := 1) one_pos
    (Real.pi ^ 2 * S + (-2 * θ * ς) / 2)
  have e3 : (∫ v : ℝ, liftSymbol (uctFstarDelta δ) 0 0 ((v : ℂ) * Complex.I) *
        Complex.exp (Complex.I * (((Real.pi ^ 2 * S + (-2 * θ * ς) / 2) * v - Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ))) =
      ∫ v : ℝ, refKernel S (-2 * θ * ς) ((v : ℂ) * Complex.I) * seedT δ ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) := by
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    beta_reduce
    rw [exp_matches, liftSymbol_zero_order]
    exact mul_comm _ _
  rw [e3] at href3
  have hwin : windowSmooth 0 0 (uctFstarDelta δ) = uctFstarDelta δ := by
    simp [windowSmooth]
  rw [hwin] at href3
  -- assemble
  have hcs := ceCs_pos
  have hcm := ceCs_mul_ceBeta1
  have hb := ceBeta1_pos
  have harg : -((Real.pi ^ 2 * S + (-2 * θ * ς) / 2) / ceCs) =
      -(ceBeta1 * S) + ceBeta1 * (θ / Real.pi ^ 2) * ς := by
    have : Real.pi ^ 2 = ceCs * ceBeta1 := hcm.symm
    rw [this]; field_simp; ring
  rw [harg] at href3
  have hπ0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hVal : ((ceK / ceCs * uctFstarDelta δ (-(ceBeta1 * S) + ceBeta1 * (θ / Real.pi ^ 2) * ς) : ℝ) : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, refKernel S (-2 * θ * ς) ((1 : ℂ) + (v : ℂ) * Complex.I) *
          seedT δ ((ceCs : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) := by
    have h1 : ∫ v : ℝ, refKernel S (-2 * θ * ς) ((1 : ℂ) + (v : ℂ) * Complex.I) *
          seedT δ ((ceCs : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) =
        ∫ v : ℝ, refKernel S (-2 * θ * ς) ((v : ℂ) * Complex.I) * seedT δ ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) := by
      exact sh3
    rw [h1]
    simp only [Complex.ofReal_one, mul_one] at href3
    rw [href3]
    push_cast
    ring
  have hmain' : seedHnorm ε δ c ξ - ((ceK / ceCs * uctFstarDelta δ (-(ceBeta1 * S) + ceBeta1 * (θ / Real.pi ^ 2) * ς) : ℝ) : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ((∫ v : ℝ, (mellinK0 c ((ς : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ -
          refKernel S ς ((1 : ℂ) + (v : ℂ) * Complex.I)) * Sy ((1 : ℂ) + (v : ℂ) * Complex.I)) +
        ∫ v : ℝ, refKernel S ς ((1 : ℂ) + (v : ℂ) * Complex.I) *
          (Sy ((1 : ℂ) + (v : ℂ) * Complex.I) - Ey ((1 : ℂ) + (v : ℂ) * Complex.I))) := by
    rw [hVal, seedHnorm_eq hc0]
    have hSyeq : (∫ v : ℝ, mellinK0 c ((liftEps c : ℂ) * ((v : ℂ) * Complex.I)) ξ *
        seedW ε δ c ((liftEps c : ℂ) * ((v : ℂ) * Complex.I))) =
        ∫ v : ℝ, mellinK0 c ((ς : ℂ) * ((v : ℂ) * Complex.I)) ξ * Sy ((v : ℂ) * Complex.I) := rfl
    rw [hSyeq, ← shA, hsplit]
    ring
  rw [hmain', norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hsum := (norm_add_le _ _).trans (add_le_add hJ1 hJ2)
  have hpi0 : 0 < 2 * Real.pi := by positivity
  calc (2 * Real.pi)⁻¹ * ‖(∫ v : ℝ, _) + ∫ v : ℝ, _‖ ≤ (2 * Real.pi)⁻¹ * (Cm * ς ^ 2 + Cr * ς ^ 2) := by
        gcongr
    _ = (Cm + Cr) / (2 * Real.pi) * ς ^ 2 := by field_simp

/-- info: 'FormalResearch.SignUncertainty.seed_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seed_window

end FormalResearch.SignUncertainty
