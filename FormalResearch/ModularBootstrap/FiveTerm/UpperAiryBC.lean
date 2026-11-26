module

public import FormalResearch.ModularBootstrap.FiveTerm.UpperAiryPrimitive
public import FormalResearch.Special.AiryPwsDeriv

/-!
# `cts:BC-id`: integration by parts against the Airy primitives

Source: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`, Lemma `cts:tip-shared` (c), label `cts:BC-id`.
With `B = airyPrimB` (`B(t) = ∫_{-∞}^t Ai - 1_{t>0}`) and `C = airyPrimC` (`C(t) = t B(t) - Ai'(t)`), for
`0 < h < X` and `w` twice differentiable on `(0,∞)` (first derivative `w1`, second derivative `w2`, continuous):

  `∫_0^∞ w(s) Ai(s-X) ds - w(X) = ∫_0^h w(s) Ai(s-X) ds - w(h) B(h-X) + w1(h) C(h-X) + ∫_h^∞ w2(s) C(s-X) ds`.

Hypotheses, stated honestly:
* `C²` on `(0,∞)` as `HasDerivAt w (w1 s) s`, `HasDerivAt w1 (w2 s) s` with `w2` continuous on `(0,∞)`;
* `w` interval integrable on `[0,h]`.  This is not implied by `C²` on `(0,∞)` (the paper's `w_1 = w_0'` blows up at
  `0` like `s^{-1/2}`), and it is automatic when `w` is bounded near `0`; the global form `airyBC_id_global` derives it;
* polynomial bounds for `w, w1, w2` on `[h,∞)` only (the paper's `w_0'` is not polynomially bounded near `0`).

Proof.  `P(t) = 2/3 + ∫_0^t Ai` is smooth with `P' = Ai` and `airyPrimB = P - 1_{t>0}`.  Put
`Cm(t) = t P(t) - Ai'(t)` (`Cm' = P`, equal to `airyPrimC` on `(-∞,0]`) and `Cp(t) = t (P(t)-1) - Ai'(t)`
(`Cp' = P - 1`, equal to `airyPrimC` on `(0,∞)`).  The jump of `B` at `0` is the jump `P(0) = 2/3` against
`P(0) - 1 = -1/3`: the piece on `[h,X]` uses `P, Cm`, the piece on `(X,∞)` uses `P - 1, Cp`.  Each piece is one
fundamental theorem of calculus, the tail by `integral_Ioi_of_hasDerivAt_of_tendsto`; the boundary terms at `∞`
vanish by the exponential decay `|Ai(t)| ≤ C e^{-2t/3}` and `|Ai'(t)| ≤ C(1+|t|) e^{-2t/3}` (`abs_airyAi_le_exp`,
`abs_airyD_le`).
-/

@[expose] public section

open Set MeasureTheory intervalIntegral Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.Special.AiryPrimNeg

/-- `P(t) = 2/3 + ∫_0^t Ai = 1 - ∫_{(t,∞)} Ai` (see `airyPrimB_eq_bcP`): smooth, `P' = Ai`, `P(0) = 2/3`. -/
private noncomputable def bcP (t : ℝ) : ℝ := 2 / 3 + ∫ x in (0 : ℝ)..t, airyAi x

/-- `Cm(t) = t P(t) - Ai'(t)`: smooth, `Cm' = P`; equal to `airyPrimC` on `(-∞,0]`. -/
private noncomputable def bcCm (t : ℝ) : ℝ := t * bcP t - airyAi' t

/-- `Cp(t) = t (P(t) - 1) - Ai'(t)`: smooth, `Cp' = P - 1`; equal to `airyPrimC` on `(0,∞)`. -/
private noncomputable def bcCp (t : ℝ) : ℝ := t * (bcP t - 1) - airyAi' t

private lemma bcP_hasDerivAt (t : ℝ) : HasDerivAt bcP (airyAi t) t := by
  unfold bcP
  exact ((continuous_airyAi.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add _

private lemma bcP_zero : bcP 0 = 2 / 3 := by simp [bcP]

private lemma bcCm_hasDerivAt (t : ℝ) : HasDerivAt bcCm (bcP t) t := by
  have h := ((hasDerivAt_id' t).mul (bcP_hasDerivAt t)).sub (hasDerivAt_airyAi' t)
  unfold bcCm
  convert h using 1
  ring

private lemma bcCp_hasDerivAt (t : ℝ) : HasDerivAt bcCp (bcP t - 1) t := by
  have h := ((hasDerivAt_id' t).mul ((bcP_hasDerivAt t).sub_const 1)).sub (hasDerivAt_airyAi' t)
  unfold bcCp
  convert h using 1
  ring

/-- The tail `∫_{(t,∞)} Ai = 1/3 - ∫_0^t Ai` for `t ≥ 0`. -/
private lemma tail_eq {t : ℝ} (ht : 0 ≤ t) :
    ∫ x in Ioi t, airyAi x = 1 / 3 - ∫ x in (0 : ℝ)..t, airyAi x := by
  have hI : IntegrableOn airyAi (Ioi 0) := integrableOn_airyAi_Ioi
  have hsplit : ∫ x in Ioc 0 t ∪ Ioi t, airyAi x =
      (∫ x in Ioc 0 t, airyAi x) + ∫ x in Ioi t, airyAi x :=
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hI.mono_set Ioc_subset_Ioi_self) (hI.mono_set (Ioi_subset_Ioi ht))
  rw [Ioc_union_Ioi_eq_Ioi ht, integral_Ioi_airyAi, ← intervalIntegral.integral_of_le ht] at hsplit
  linarith

/-- `airyPrimB t = P(t) - 1_{t>0}`. -/
private lemma airyPrimB_eq_bcP (t : ℝ) : airyPrimB t = bcP t - (if 0 < t then 1 else 0) := by
  rcases le_or_gt t 0 with ht | ht
  · rw [airyPrimB_eq ht]
    simp only [not_lt.2 ht, ↓reduceIte, sub_zero]
    unfold Bneg bcP
    rw [intervalIntegral.integral_symm 0 t]
    ring
  · unfold airyPrimB bcP
    simp only [ht, ↓reduceIte]
    rw [tail_eq ht.le]
    ring

/-- `airyPrimC = Cm` on `(-∞,0]`. -/
private lemma airyPrimC_eq_bcCm {t : ℝ} (ht : t ≤ 0) : airyPrimC t = bcCm t := by
  unfold airyPrimC bcCm
  rw [airyPrimB_eq_bcP]
  simp only [not_lt.2 ht, ↓reduceIte, sub_zero]

/-- `airyPrimC = Cp` on `(0,∞)`. -/
private lemma airyPrimC_eq_bcCp {t : ℝ} (ht : 0 < t) : airyPrimC t = bcCp t := by
  unfold airyPrimC bcCp
  rw [airyPrimB_eq_bcP]
  simp only [ht, ↓reduceIte]

/-- `airyPrimB = P - 1` on `(0,∞)`. -/
private lemma airyPrimB_eq_bcP_sub_one {t : ℝ} (ht : 0 < t) : airyPrimB t = bcP t - 1 := by
  rw [airyPrimB_eq_bcP]
  simp only [ht, ↓reduceIte]

private lemma bcCm_zero : bcCm 0 = bcCp 0 := by
  simp [bcCm, bcCp]

private lemma bcP_sub_self (X : ℝ) : bcP (X - X) = 2 / 3 := by
  rw [sub_self, bcP_zero]

/-- `|∫_{(t,∞)} Ai| ≤ (3/2) C₀ e^{-2t/3}` for `t ≥ 0`. -/
private lemma abs_tail_le {C0 : ℝ} (hC0 : ∀ s : ℝ, |airyAi s| ≤ C0 * Real.exp (-(2 / 3) * s)) (t : ℝ) :
    |∫ x in Ioi t, airyAi x| ≤ C0 * (3 / 2) * Real.exp (-(2 / 3) * t) := by
  have hI : Integrable (fun s : ℝ => C0 * Real.exp (-(2 / 3) * s)) (volume.restrict (Ioi t)) :=
    (exp_neg_integrableOn_Ioi t (by norm_num : (0 : ℝ) < 2 / 3)).const_mul C0
  have hb : ∀ᵐ s ∂(volume.restrict (Ioi t)), ‖airyAi s‖ ≤ C0 * Real.exp (-(2 / 3) * s) :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s _ => by
      rw [Real.norm_eq_abs]; exact hC0 s)
  have h := norm_integral_le_of_norm_le hI hb
  rw [MeasureTheory.integral_const_mul,
    integral_exp_mul_Ioi (by norm_num : (-(2 / 3) : ℝ) < 0) t, Real.norm_eq_abs] at h
  calc |∫ x in Ioi t, airyAi x| ≤ C0 * (-Real.exp (-(2 / 3) * t) / (-(2 / 3))) := h
    _ = C0 * (3 / 2) * Real.exp (-(2 / 3) * t) := by ring

/-- **`cts:tip-shared` (c), decay on `(0,∞)`**: exponential decay of the Airy primitives on `(0,∞)`: `|B(t)| ≤ K e^{-2t/3}` and `|C(t)| ≤ K(1+t)e^{-2t/3}`. -/
theorem airyBC_primDecay_pos :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t →
      |airyPrimB t| ≤ K * Real.exp (-(2 / 3) * t) ∧
        |airyPrimC t| ≤ K * (1 + t) * Real.exp (-(2 / 3) * t) := by
  obtain ⟨C0, hC0, hA⟩ := abs_airyAi_le_exp
  obtain ⟨C1, hC1, hA1⟩ := abs_airyD_le 1
  have hA' : ∀ s : ℝ, |airyAi' s| ≤ C1 * (1 + |s|) * Real.exp (-(2 / 3) * s) := fun s => by
    have h := hA1 s
    rwa [airyD_one, pow_one] at h
  refine ⟨C0 * (3 / 2) + C1, by positivity, fun t ht => ?_⟩
  have hexp : 0 ≤ Real.exp (-(2 / 3) * t) := (Real.exp_pos _).le
  have hB : |airyPrimB t| ≤ C0 * (3 / 2) * Real.exp (-(2 / 3) * t) := by
    have e : airyPrimB t = -∫ x in Ioi t, airyAi x := by
      unfold airyPrimB
      simp only [ht, ↓reduceIte]
      ring
    rw [e, abs_neg]
    exact abs_tail_le hA t
  have hK : 0 ≤ C0 * (3 / 2) * Real.exp (-(2 / 3) * t) := by positivity
  refine ⟨?_, ?_⟩
  · calc |airyPrimB t| ≤ C0 * (3 / 2) * Real.exp (-(2 / 3) * t) := hB
      _ ≤ (C0 * (3 / 2) + C1) * Real.exp (-(2 / 3) * t) := by
          apply mul_le_mul_of_nonneg_right _ hexp
          linarith
  · have hC : airyPrimC t = t * airyPrimB t - airyAi' t := rfl
    rw [hC]
    have h1 : |t * airyPrimB t - airyAi' t| ≤ |t * airyPrimB t| + |airyAi' t| := abs_sub _ _
    rw [abs_mul, abs_of_pos ht] at h1
    have h2 := hA' t
    rw [abs_of_pos ht] at h2
    have h3 : t * |airyPrimB t| ≤ t * (C0 * (3 / 2) * Real.exp (-(2 / 3) * t)) :=
      mul_le_mul_of_nonneg_left hB ht.le
    have key : (C0 * (3 / 2) + C1) * (1 + t) * Real.exp (-(2 / 3) * t) =
        t * (C0 * (3 / 2) * Real.exp (-(2 / 3) * t)) + C1 * (1 + t) * Real.exp (-(2 / 3) * t) +
          C0 * (3 / 2) * Real.exp (-(2 / 3) * t) := by ring
    nlinarith

/-- A polynomial-times-exponential bound on `(a,∞)` gives integrability there. -/
private lemma integrableOn_Ioi_of_bound {f : ℝ → ℝ} {a M : ℝ} {m : ℕ} (ha : 0 ≤ a)
    (hc : ContinuousOn f (Ioi a))
    (hb : ∀ s ∈ Ioi a, |f s| ≤ M * ((1 + s) ^ m * Real.exp (-(2 / 3) * s))) :
    IntegrableOn f (Ioi a) := by
  have hg : IntegrableOn (fun s : ℝ => M * ((1 + s) ^ m * Real.exp (-(2 / 3) * s))) (Ioi a) :=
    ((airyPws_integrableOn_pow_mul_exp m (by norm_num : (0 : ℝ) < 2 / 3)).mono_set
      (Ioi_subset_Ioi ha)).const_mul M
  refine Integrable.mono' hg (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => by
    rw [Real.norm_eq_abs]; exact hb s hs)

/-- `(1+s)^m e^{-2s/3} → 0` as `s → ∞`. -/
private lemma tendsto_poly_exp (m : ℕ) :
    Tendsto (fun s : ℝ => (1 + s) ^ m * Real.exp (-(2 / 3) * s)) atTop (𝓝 0) := by
  have hy : Tendsto (fun s : ℝ => (2 / 3 : ℝ) * (1 + s)) atTop atTop :=
    (tendsto_atTop_add_const_left _ 1 tendsto_id).const_mul_atTop (by norm_num)
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m).comp hy).const_mul
    ((3 / 2 : ℝ) ^ m * Real.exp (2 / 3))
  rw [mul_zero] at h
  refine h.congr (fun s => ?_)
  simp only [Function.comp]
  have h1 : ((2 / 3 : ℝ) * (1 + s)) ^ m * (3 / 2) ^ m = (1 + s) ^ m := by
    rw [← mul_pow]
    congr 1
    ring
  have h2 : Real.exp (-((2 / 3 : ℝ) * (1 + s))) * Real.exp (2 / 3) = Real.exp (-(2 / 3) * s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← h1, ← h2]
  ring

/-- A polynomial-times-exponential bound gives decay to `0` at `∞`. -/
private lemma tendsto_zero_of_bound {f : ℝ → ℝ} {a M : ℝ} {m : ℕ}
    (hb : ∀ s ∈ Ioi a, |f s| ≤ M * ((1 + s) ^ m * Real.exp (-(2 / 3) * s))) :
    Tendsto f atTop (𝓝 0) := by
  have h0 := (tendsto_poly_exp m).const_mul M
  rw [mul_zero] at h0
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [eventually_gt_atTop a] with s hs
  rw [Real.norm_eq_abs]
  exact hb s hs

private lemma exp_shift (X s : ℝ) :
    Real.exp (-(2 / 3) * (s - X)) = Real.exp (2 / 3 * X) * Real.exp (-(2 / 3) * s) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- Integrability of the tails `w Ai(· - X)` and `w2 · Cp(· - X)` on `(X,∞)`, from polynomial bounds for `s ≥ X`. -/
private lemma tail_integrable {X : ℝ} (hX : 0 < X) {w w2 : ℝ → ℝ}
    (hwc : ContinuousOn w (Ioi 0)) (hw2c : ContinuousOn w2 (Ioi 0)) {K : ℝ} {N : ℕ}
    (hw : ∀ s, X ≤ s → |w s| ≤ K * (1 + s) ^ N) (hw2 : ∀ s, X ≤ s → |w2 s| ≤ K * (1 + s) ^ N)
    {K0 : ℝ} (hK0 : 0 ≤ K0)
    (hC : ∀ t : ℝ, 0 < t → |bcCp t| ≤ K0 * (1 + t) * Real.exp (-(2 / 3) * t)) :
    IntegrableOn (fun s => w s * airyAi (s - X)) (Ioi X) ∧
      IntegrableOn (fun s => w2 s * bcCp (s - X)) (Ioi X) := by
  obtain ⟨C0, hC0, hA⟩ := abs_airyAi_le_exp
  have hX0 : 0 ≤ X := hX.le
  have hcA : ContinuousOn (fun s => w s * airyAi (s - X)) (Ioi X) := by
    have hsub : Ioi X ⊆ Ioi 0 := Ioi_subset_Ioi hX0
    exact (hwc.mono hsub).mul ((continuous_airyAi.comp (continuous_id.sub continuous_const)).continuousOn)
  have hcC : ContinuousOn (fun s => w2 s * bcCp (s - X)) (Ioi X) := by
    have hsub : Ioi X ⊆ Ioi 0 := Ioi_subset_Ioi hX0
    have hCc : Continuous fun s => bcCp (s - X) :=
      (continuous_iff_continuousAt.2 fun t => (bcCp_hasDerivAt t).continuousAt).comp
        (continuous_id.sub continuous_const)
    exact (hw2c.mono hsub).mul hCc.continuousOn
  constructor
  · refine integrableOn_Ioi_of_bound (M := K * (C0 * Real.exp (2 / 3 * X))) (m := N) hX0 hcA ?_
    intro s hs
    have hs' : X ≤ s := le_of_lt hs
    have h1 := hw s hs'
    have h2 := hA (s - X)
    calc |w s * airyAi (s - X)| = |w s| * |airyAi (s - X)| := abs_mul _ _
      _ ≤ (K * (1 + s) ^ N) * (C0 * Real.exp (-(2 / 3) * (s - X))) :=
          mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
      _ = (K * (C0 * Real.exp (2 / 3 * X))) * ((1 + s) ^ N * Real.exp (-(2 / 3) * s)) := by
          rw [exp_shift]
          ring
  · refine integrableOn_Ioi_of_bound (M := K * K0 * Real.exp (2 / 3 * X)) (m := N + 1) hX0 hcC ?_
    intro s hs
    have hs' : X ≤ s := le_of_lt hs
    have hsX : 0 < s - X := sub_pos.mpr hs
    have h1 := hw2 s hs'
    have h2 : |bcCp (s - X)| ≤ K0 * (1 + s) * (Real.exp (2 / 3 * X) * Real.exp (-(2 / 3) * s)) := by
      have h := hC (s - X) hsX
      have hle : K0 * (1 + (s - X)) ≤ K0 * (1 + s) :=
        mul_le_mul_of_nonneg_left (by linarith) hK0
      calc |bcCp (s - X)| ≤ K0 * (1 + (s - X)) * Real.exp (-(2 / 3) * (s - X)) := h
        _ ≤ K0 * (1 + s) * Real.exp (-(2 / 3) * (s - X)) :=
            mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
        _ = _ := by rw [exp_shift]
    calc |w2 s * bcCp (s - X)| = |w2 s| * |bcCp (s - X)| := abs_mul _ _
      _ ≤ (K * (1 + s) ^ N) * (K0 * (1 + s) * (Real.exp (2 / 3 * X) * Real.exp (-(2 / 3) * s))) :=
          mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
      _ = (K * K0 * Real.exp (2 / 3 * X)) * ((1 + s) ^ (N + 1) * Real.exp (-(2 / 3) * s)) := by
          rw [pow_succ]
          ring

/-- The first split: `∫_h^X w Ai(·-X) = Ψ(X) - Ψ(h) + ∫_h^X w2 Cm(·-X)`, with `Ψ = w P(·-X) - w1 Cm(·-X)`. -/
private lemma int_below {X h : ℝ} (hh : 0 < h) (hhX : h ≤ X) {w w1 w2 : ℝ → ℝ}
    (hw : ∀ s, 0 < s → HasDerivAt w (w1 s) s) (hw1 : ∀ s, 0 < s → HasDerivAt w1 (w2 s) s)
    (hw2 : ContinuousOn w2 (Ioi 0)) :
    ∫ s in h..X, w s * airyAi (s - X) =
      (w X * bcP (X - X) - w1 X * bcCm (X - X)) - (w h * bcP (h - X) - w1 h * bcCm (h - X)) +
        ∫ s in h..X, w2 s * bcCm (s - X) := by
  have hwc : ContinuousOn w (Ioi 0) := fun s hs => (hw s hs).continuousAt.continuousWithinAt
  have hw1c : ContinuousOn w1 (Ioi 0) := fun s hs => (hw1 s hs).continuousAt.continuousWithinAt
  have hsub : Icc h X ⊆ Ioi 0 := fun s hs => lt_of_lt_of_le hh hs.1
  have hΨ : ∀ s ∈ uIcc h X, HasDerivAt (fun s => w s * bcP (s - X) - w1 s * bcCm (s - X))
      (w s * airyAi (s - X) - w2 s * bcCm (s - X)) s := by
    intro s hs
    rw [uIcc_of_le hhX] at hs
    have hs0 : 0 < s := lt_of_lt_of_le hh hs.1
    have hP : HasDerivAt (fun s => bcP (s - X)) (airyAi (s - X)) s :=
      HasDerivAt.comp_sub_const s X (bcP_hasDerivAt (s - X))
    have hC : HasDerivAt (fun s => bcCm (s - X)) (bcP (s - X)) s :=
      HasDerivAt.comp_sub_const s X (bcCm_hasDerivAt (s - X))
    have := ((hw s hs0).mul hP).sub ((hw1 s hs0).mul hC)
    convert this using 1
    ring
  have hCm : Continuous fun s => bcCm (s - X) :=
    (continuous_iff_continuousAt.2 fun t => (bcCm_hasDerivAt t).continuousAt).comp
      (continuous_id.sub continuous_const)
  have hA : Continuous fun s => airyAi (s - X) :=
    continuous_airyAi.comp (continuous_id.sub continuous_const)
  have hIΨ : IntervalIntegrable (fun s => w s * airyAi (s - X) - w2 s * bcCm (s - X)) volume h X := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hhX]
    exact ((hwc.mono hsub).mul hA.continuousOn).sub ((hw2.mono hsub).mul hCm.continuousOn)
  have hIwA : IntervalIntegrable (fun s => w s * airyAi (s - X)) volume h X := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hhX]
    exact (hwc.mono hsub).mul hA.continuousOn
  have hIwC : IntervalIntegrable (fun s => w2 s * bcCm (s - X)) volume h X := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hhX]
    exact (hw2.mono hsub).mul hCm.continuousOn
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hΨ hIΨ
  have hsplit := intervalIntegral.integral_sub hIwA hIwC
  linarith [hFTC, hsplit]

/-- The tail identity: `∫_{(X,∞)} w Ai(·-X) = -Φ(X) + ∫_{(X,∞)} w2 Cp(·-X)`, with `Φ = w(P-1)(·-X) - w1 Cp(·-X)`. -/
private lemma int_above {X : ℝ} (hX : 0 < X) {w w1 w2 : ℝ → ℝ}
    (hw : ∀ s, 0 < s → HasDerivAt w (w1 s) s) (hw1 : ∀ s, 0 < s → HasDerivAt w1 (w2 s) s)
    {K : ℝ} {N : ℕ} (hw0 : ∀ s, X ≤ s → |w s| ≤ K * (1 + s) ^ N)
    (hw1b : ∀ s, X ≤ s → |w1 s| ≤ K * (1 + s) ^ N)
    (hw2 : ∀ s, X ≤ s → |w2 s| ≤ K * (1 + s) ^ N)
    (hw2c : ContinuousOn w2 (Ioi 0)) :
    ∫ s in Ioi X, w s * airyAi (s - X) =
      -(w X * (bcP (X - X) - 1) - w1 X * bcCp (X - X)) + ∫ s in Ioi X, w2 s * bcCp (s - X) := by
  obtain ⟨K0, hK0, hdec⟩ := airyBC_primDecay_pos
  have hB : ∀ t : ℝ, 0 < t → |bcP t - 1| ≤ K0 * Real.exp (-(2 / 3) * t) := fun t ht => by
    rw [← airyPrimB_eq_bcP_sub_one ht]
    exact (hdec t ht).1
  have hC : ∀ t : ℝ, 0 < t → |bcCp t| ≤ K0 * (1 + t) * Real.exp (-(2 / 3) * t) := fun t ht => by
    rw [← airyPrimC_eq_bcCp ht]
    exact (hdec t ht).2
  have hwc : ContinuousOn w (Ioi 0) := fun s hs => (hw s hs).continuousAt.continuousWithinAt
  obtain ⟨hIA, hIC⟩ := tail_integrable hX hwc hw2c hw0 hw2 hK0 hC
  -- the function Φ and its derivative
  have hΦ : ∀ s, 0 < s → HasDerivAt (fun s => w s * (bcP (s - X) - 1) - w1 s * bcCp (s - X))
      (w s * airyAi (s - X) - w2 s * bcCp (s - X)) s := by
    intro s hs0
    have hP : HasDerivAt (fun s => bcP (s - X) - 1) (airyAi (s - X)) s :=
      (HasDerivAt.comp_sub_const s X (bcP_hasDerivAt (s - X))).sub_const 1
    have hC' : HasDerivAt (fun s => bcCp (s - X)) (bcP (s - X) - 1) s :=
      HasDerivAt.comp_sub_const s X (bcCp_hasDerivAt (s - X))
    have := ((hw s hs0).mul hP).sub ((hw1 s hs0).mul hC')
    convert this using 1
    ring
  have hcont : ContinuousWithinAt (fun s => w s * (bcP (s - X) - 1) - w1 s * bcCp (s - X)) (Ici X) X :=
    (hΦ X hX).continuousAt.continuousWithinAt
  have hder : ∀ s ∈ Ioi X, HasDerivAt (fun s => w s * (bcP (s - X) - 1) - w1 s * bcCp (s - X))
      (w s * airyAi (s - X) - w2 s * bcCp (s - X)) s := fun s hs => hΦ s (hX.trans hs)
  have hint : IntegrableOn (fun s => w s * airyAi (s - X) - w2 s * bcCp (s - X)) (Ioi X) :=
    hIA.sub hIC
  -- decay of Φ at infinity
  have htend : Tendsto (fun s => w s * (bcP (s - X) - 1) - w1 s * bcCp (s - X)) atTop (𝓝 0) := by
    obtain ⟨C0, hC0, hA⟩ := abs_airyAi_le_exp
    have hΦ1 : ∀ s ∈ Ioi X, |w s * (bcP (s - X) - 1)| ≤
        (K * (K0 * Real.exp (2 / 3 * X))) * ((1 + s) ^ N * Real.exp (-(2 / 3) * s)) := by
      intro s hs
      have hsX : 0 < s - X := sub_pos.mpr hs
      have hs' : X ≤ s := le_of_lt hs
      calc |w s * (bcP (s - X) - 1)| = |w s| * |bcP (s - X) - 1| := abs_mul _ _
        _ ≤ (K * (1 + s) ^ N) * (K0 * Real.exp (-(2 / 3) * (s - X))) :=
            mul_le_mul (hw0 s hs') (hB (s - X) hsX) (abs_nonneg _) (le_trans (abs_nonneg _) (hw0 s hs'))
        _ = (K * (K0 * Real.exp (2 / 3 * X))) * ((1 + s) ^ N * Real.exp (-(2 / 3) * s)) := by
            rw [exp_shift]
            ring
    have hΦ2 : ∀ s ∈ Ioi X, |w1 s * bcCp (s - X)| ≤
        (K * K0 * Real.exp (2 / 3 * X)) * ((1 + s) ^ (N + 1) * Real.exp (-(2 / 3) * s)) := by
      intro s hs
      have hsX : 0 < s - X := sub_pos.mpr hs
      have hs' : X ≤ s := le_of_lt hs
      have h2 : |bcCp (s - X)| ≤ K0 * (1 + s) * (Real.exp (2 / 3 * X) * Real.exp (-(2 / 3) * s)) := by
        have h := hC (s - X) hsX
        have hle : K0 * (1 + (s - X)) ≤ K0 * (1 + s) :=
          mul_le_mul_of_nonneg_left (by linarith) hK0
        calc |bcCp (s - X)| ≤ K0 * (1 + (s - X)) * Real.exp (-(2 / 3) * (s - X)) := h
          _ ≤ K0 * (1 + s) * Real.exp (-(2 / 3) * (s - X)) :=
              mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
          _ = _ := by rw [exp_shift]
      calc |w1 s * bcCp (s - X)| = |w1 s| * |bcCp (s - X)| := abs_mul _ _
        _ ≤ (K * (1 + s) ^ N) * (K0 * (1 + s) * (Real.exp (2 / 3 * X) * Real.exp (-(2 / 3) * s))) :=
            mul_le_mul (hw1b s hs') h2 (abs_nonneg _) (le_trans (abs_nonneg _) (hw1b s hs'))
        _ = (K * K0 * Real.exp (2 / 3 * X)) * ((1 + s) ^ (N + 1) * Real.exp (-(2 / 3) * s)) := by
            rw [pow_succ]
            ring
    have ha := tendsto_zero_of_bound (a := X) (m := N) hΦ1
    have hb := tendsto_zero_of_bound (a := X) (m := N + 1) hΦ2
    have := ha.sub hb
    rw [sub_zero] at this
    refine this.congr (fun s => ?_)
    ring
  have hfin := integral_Ioi_of_hasDerivAt_of_tendsto hcont hder hint htend
  -- split the integrand: w Ai = (w Ai - w2 Cp) + w2 Cp
  have hsplit := MeasureTheory.integral_sub hIA hIC
  linarith [hfin, hsplit]

private lemma bcCm_continuous : Continuous bcCm :=
  continuous_iff_continuousAt.2 fun t => (bcCm_hasDerivAt t).continuousAt

private lemma bcCp_continuous : Continuous bcCp :=
  continuous_iff_continuousAt.2 fun t => (bcCp_hasDerivAt t).continuousAt

private lemma airyPrimB_eq_bcP_neg {t : ℝ} (ht : t ≤ 0) : airyPrimB t = bcP t := by
  rw [airyPrimB_eq_bcP]
  simp only [not_lt.2 ht, ↓reduceIte, sub_zero]

/-- The decay constants of the primitives, in the `bcP`/`bcCp` form used below. -/
private lemma bcP_decay : ∃ K0 : ℝ, 0 ≤ K0 ∧
    (∀ t : ℝ, 0 < t → |bcP t - 1| ≤ K0 * Real.exp (-(2 / 3) * t)) ∧
    (∀ t : ℝ, 0 < t → |bcCp t| ≤ K0 * (1 + t) * Real.exp (-(2 / 3) * t)) := by
  obtain ⟨K0, hK0, hdec⟩ := airyBC_primDecay_pos
  refine ⟨K0, hK0, fun t ht => ?_, fun t ht => ?_⟩
  · rw [← airyPrimB_eq_bcP_sub_one ht]
    exact (hdec t ht).1
  · rw [← airyPrimC_eq_bcCp ht]
    exact (hdec t ht).2

/-- **`cts:BC-id`** (Lemma `cts:tip-shared` (c), identity): for `0 < h < X`, with `w` of class `C²` on `(0,∞)`
(`w1 = w'`, `w2 = w''` continuous), `w` interval integrable on `[0,h]`, and polynomial bounds for `w, w', w''`
on `[h,∞)`:
`∫_0^∞ w Ai(·-X) - w(X) = ∫_0^h w Ai(·-X) - w(h) B(h-X) + w'(h) C(h-X) + ∫_h^∞ w'' C(·-X)`. -/
theorem airyBC_id {X h : ℝ} (hh : 0 < h) (hhX : h < X) {w w1 w2 : ℝ → ℝ}
    (hw : ∀ s, 0 < s → HasDerivAt w (w1 s) s) (hw1 : ∀ s, 0 < s → HasDerivAt w1 (w2 s) s)
    (hw2 : ContinuousOn w2 (Ioi 0)) (hwint : IntervalIntegrable w volume 0 h)
    (hpoly : ∃ (K : ℝ) (N : ℕ), ∀ s, h ≤ s →
      |w s| ≤ K * (1 + s) ^ N ∧ |w1 s| ≤ K * (1 + s) ^ N ∧ |w2 s| ≤ K * (1 + s) ^ N) :
    (∫ s in Ioi 0, w s * airyAi (s - X)) - w X =
      (∫ s in (0 : ℝ)..h, w s * airyAi (s - X)) - w h * airyPrimB (h - X) +
        w1 h * airyPrimC (h - X) + ∫ s in Ioi h, w2 s * airyPrimC (s - X) := by
  obtain ⟨K, N, hK⟩ := hpoly
  obtain ⟨K0, hK0, hB, hC⟩ := bcP_decay
  have hX : 0 < X := lt_trans hh hhX
  have hwc : ContinuousOn w (Ioi 0) := fun s hs => (hw s hs).continuousAt.continuousWithinAt
  have hw1c : ContinuousOn w1 (Ioi 0) := fun s hs => (hw1 s hs).continuousAt.continuousWithinAt
  have hA : Continuous fun s => airyAi (s - X) :=
    continuous_airyAi.comp (continuous_id.sub continuous_const)
  have hCm : Continuous fun s => bcCm (s - X) := bcCm_continuous.comp (continuous_id.sub continuous_const)
  have hsubH : Icc h X ⊆ Ioi 0 := fun s hs => lt_of_lt_of_le hh hs.1
  have hXw : ∀ s, X ≤ s → |w s| ≤ K * (1 + s) ^ N := fun s hs => (hK s (hhX.le.trans hs)).1
  have hXw1 : ∀ s, X ≤ s → |w1 s| ≤ K * (1 + s) ^ N := fun s hs => (hK s (hhX.le.trans hs)).2.1
  have hXw2 : ∀ s, X ≤ s → |w2 s| ≤ K * (1 + s) ^ N := fun s hs => (hK s (hhX.le.trans hs)).2.2
  -- integrability of `w Ai(· - X)`
  have hIA0 : IntervalIntegrable (fun s => w s * airyAi (s - X)) volume 0 h :=
    hwint.mul_continuousOn hA.continuousOn
  have hIAc : IntegrableOn (fun s => w s * airyAi (s - X)) (Ioc h X) :=
    ((hwc.mono hsubH).mul hA.continuousOn).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hIAX : IntegrableOn (fun s => w s * airyAi (s - X)) (Ioi X) :=
    (tail_integrable hX hwc hw2 hXw hXw2 hK0 hC).1
  have hIAh : IntegrableOn (fun s => w s * airyAi (s - X)) (Ioi h) := by
    rw [← Ioc_union_Ioi_eq_Ioi hhX.le]
    exact hIAc.union hIAX
  -- integrability of `w2 C(· - X)`
  have hGc0 : IntegrableOn (fun s => w2 s * bcCm (s - X)) (Ioc h X) :=
    (((hw2.mono hsubH).mul hCm.continuousOn).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hGc : IntegrableOn (fun s => w2 s * airyPrimC (s - X)) (Ioc h X) :=
    hGc0.congr_fun (fun s hs => by
      rw [airyPrimC_eq_bcCm (by linarith [hs.2])]) measurableSet_Ioc
  have hGX0 : IntegrableOn (fun s => w2 s * bcCp (s - X)) (Ioi X) :=
    (tail_integrable hX hwc hw2 hXw hXw2 hK0 hC).2
  have hGX : IntegrableOn (fun s => w2 s * airyPrimC (s - X)) (Ioi X) :=
    hGX0.congr_fun (fun s hs => by
      rw [airyPrimC_eq_bcCp (sub_pos.mpr hs)]) measurableSet_Ioi
  -- splitting of the integration domains
  have hIA_Ioc0 : IntegrableOn (fun s => w s * airyAi (s - X)) (Ioc 0 h) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hh.le).1 hIA0
  have e0 : ∫ s in Ioi 0, w s * airyAi (s - X) =
      (∫ s in Ioc 0 h, w s * airyAi (s - X)) + ∫ s in Ioi h, w s * airyAi (s - X) := by
    have := setIntegral_union (Ioc_disjoint_Ioi (le_refl h)) measurableSet_Ioi hIA_Ioc0 hIAh
    rwa [Ioc_union_Ioi_eq_Ioi hh.le] at this
  have e1 : ∫ s in (0 : ℝ)..h, w s * airyAi (s - X) = ∫ s in Ioc 0 h, w s * airyAi (s - X) :=
    intervalIntegral.integral_of_le hh.le
  have e2 : ∫ s in Ioi h, w s * airyAi (s - X) =
      (∫ s in Ioc h X, w s * airyAi (s - X)) + ∫ s in Ioi X, w s * airyAi (s - X) := by
    have := setIntegral_union (Ioc_disjoint_Ioi (le_refl X)) measurableSet_Ioi hIAc hIAX
    rwa [Ioc_union_Ioi_eq_Ioi hhX.le] at this
  have e3 : ∫ s in Ioc h X, w s * airyAi (s - X) = ∫ s in h..X, w s * airyAi (s - X) :=
    (intervalIntegral.integral_of_le hhX.le).symm
  have e4 : ∫ s in Ioi h, w2 s * airyPrimC (s - X) =
      (∫ s in Ioc h X, w2 s * airyPrimC (s - X)) + ∫ s in Ioi X, w2 s * airyPrimC (s - X) := by
    have := setIntegral_union (Ioc_disjoint_Ioi (le_refl X)) measurableSet_Ioi hGc hGX
    rwa [Ioc_union_Ioi_eq_Ioi hhX.le] at this
  have e5 : ∫ s in Ioc h X, w2 s * airyPrimC (s - X) = ∫ s in h..X, w2 s * bcCm (s - X) := by
    rw [intervalIntegral.integral_of_le hhX.le]
    exact setIntegral_congr_fun measurableSet_Ioc (fun s hs => by
      rw [airyPrimC_eq_bcCm (by linarith [hs.2])])
  have e6 : ∫ s in Ioi X, w2 s * airyPrimC (s - X) = ∫ s in Ioi X, w2 s * bcCp (s - X) :=
    setIntegral_congr_fun measurableSet_Ioi (fun s hs => by
      rw [airyPrimC_eq_bcCp (sub_pos.mpr hs)])
  -- the two one-sided fundamental theorems and the jump at `s = X`
  have hbelow := int_below hh hhX.le hw hw1 hw2
  have habove := int_above hX hw hw1 hXw hXw1 hXw2 hw2
  have hPsi : (w X * bcP (X - X) - w1 X * bcCm (X - X)) -
      (w X * (bcP (X - X) - 1) - w1 X * bcCp (X - X)) = w X := by
    rw [sub_self, bcCm_zero, bcP_zero]
    ring
  have hB' : airyPrimB (h - X) = bcP (h - X) := airyPrimB_eq_bcP_neg (by linarith)
  have hC' : airyPrimC (h - X) = bcCm (h - X) := airyPrimC_eq_bcCm (by linarith)
  rw [hB', hC']
  linarith [e0, e1, e2, e3, e4, e5, e6, hbelow, habove, hPsi]

/-- **`cts:BC-id` with the stated hypotheses**: `w` of class `C²` on `(0,∞)` and `w, w', w''` polynomially bounded
on `(0,∞)`.  The integrability of `w` on `(0,h]` is then automatic, since `w` is continuous there and bounded. -/
theorem airyBC_id_global {X h : ℝ} (hh : 0 < h) (hhX : h < X) {w w1 w2 : ℝ → ℝ}
    (hw : ∀ s, 0 < s → HasDerivAt w (w1 s) s) (hw1 : ∀ s, 0 < s → HasDerivAt w1 (w2 s) s)
    (hw2 : ContinuousOn w2 (Ioi 0))
    (hpoly : ∃ (K : ℝ) (N : ℕ), ∀ s, 0 < s →
      |w s| ≤ K * (1 + s) ^ N ∧ |w1 s| ≤ K * (1 + s) ^ N ∧ |w2 s| ≤ K * (1 + s) ^ N) :
    (∫ s in Ioi 0, w s * airyAi (s - X)) - w X =
      (∫ s in (0 : ℝ)..h, w s * airyAi (s - X)) - w h * airyPrimB (h - X) +
        w1 h * airyPrimC (h - X) + ∫ s in Ioi h, w2 s * airyPrimC (s - X) := by
  obtain ⟨K, N, hK⟩ := hpoly
  have hwc : ContinuousOn w (Ioi 0) := fun s hs => (hw s hs).continuousAt.continuousWithinAt
  have hK0 : 0 ≤ K := by
    have h1 := (hK h hh).1
    have hpos : 0 < (1 + h) ^ N := pow_pos (by linarith) N
    have h2 : 0 ≤ K * (1 + h) ^ N := le_trans (abs_nonneg _) h1
    exact nonneg_of_mul_nonneg_left h2 hpos
  have hwint : IntervalIntegrable w volume 0 h := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hh.le]
    have hc : IntegrableOn (fun _ : ℝ => K * (1 + h) ^ N) (Ioc 0 h) :=
      integrableOn_const (by simp)
    refine Integrable.mono' hc ((hwc.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
    rw [Real.norm_eq_abs]
    refine (hK s hs.1).1.trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [hs.1]) (by linarith [hs.2]) N) hK0
  exact airyBC_id hh hhX hw hw1 hw2 hwint ⟨K, N, fun s hs => by
    have h0 : 0 < s := lt_of_lt_of_le hh hs
    exact hK s h0⟩

/-- Integrability of `|w2| |C(· - X)|` on `(h,∞)` (the last term of the bound in `cts:BC-bnds`): `w2` continuous on
`(0,∞)` and polynomially bounded on `[h,∞)`; `C` is continuous and exponentially decaying on `(0,∞)`. -/
theorem airyBC_integrableOn_abs {X h : ℝ} (hh : 0 < h) (hhX : h < X) {w2 : ℝ → ℝ}
    (hw2 : ContinuousOn w2 (Ioi 0)) {K : ℝ} {N : ℕ} (hK : ∀ s, h ≤ s → |w2 s| ≤ K * (1 + s) ^ N) :
    IntegrableOn (fun s => |w2 s| * |airyPrimC (s - X)|) (Ioi h) := by
  have hX : 0 < X := lt_trans hh hhX
  obtain ⟨K0, hK0, -, hC⟩ := bcP_decay
  have hsubH : Icc h X ⊆ Ioi 0 := fun s hs => lt_of_lt_of_le hh hs.1
  have hc1 : IntegrableOn (fun s => |w2 s| * |airyPrimC (s - X)|) (Ioc h X) := by
    have hcont : ContinuousOn (fun s => |w2 s| * |bcCm (s - X)|) (Icc h X) :=
      ((hw2.mono hsubH).abs).mul
        ((bcCm_continuous.comp (continuous_id.sub continuous_const)).abs.continuousOn)
    refine IntegrableOn.congr_fun ((hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self) ?_
      measurableSet_Ioc
    intro s hs
    simp only
    rw [airyPrimC_eq_bcCm (by linarith [hs.2])]
  have hbd : ∀ s ∈ Ioi X, |(fun s => |w2 s| * |bcCp (s - X)|) s| ≤
      (K * K0 * Real.exp (2 / 3 * X)) * ((1 + s) ^ (N + 1) * Real.exp (-(2 / 3) * s)) := by
    intro s hs
    have hsX : 0 < s - X := sub_pos.mpr hs
    have hs' : X ≤ s := le_of_lt hs
    have h1 := hK s (hhX.le.trans hs')
    have h2 : |bcCp (s - X)| ≤ K0 * (1 + s) * (Real.exp (2 / 3 * X) * Real.exp (-(2 / 3) * s)) := by
      have h := hC (s - X) hsX
      have hle : K0 * (1 + (s - X)) ≤ K0 * (1 + s) :=
        mul_le_mul_of_nonneg_left (by linarith) hK0
      calc |bcCp (s - X)| ≤ K0 * (1 + (s - X)) * Real.exp (-(2 / 3) * (s - X)) := h
        _ ≤ K0 * (1 + s) * Real.exp (-(2 / 3) * (s - X)) :=
            mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
        _ = _ := by rw [exp_shift]
    show |(|w2 s| * |bcCp (s - X)|)| ≤ _
    rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
    calc |w2 s| * |bcCp (s - X)| ≤ (K * (1 + s) ^ N) * (K0 * (1 + s) * (Real.exp (2 / 3 * X) *
          Real.exp (-(2 / 3) * s))) :=
          mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
      _ = (K * K0 * Real.exp (2 / 3 * X)) * ((1 + s) ^ (N + 1) * Real.exp (-(2 / 3) * s)) := by
          rw [pow_succ]
          ring
  have hcont2 : ContinuousOn (fun s => |w2 s| * |bcCp (s - X)|) (Ioi X) :=
    ((hw2.mono (Ioi_subset_Ioi hX.le)).abs).mul
      ((bcCp_continuous.comp (continuous_id.sub continuous_const)).abs.continuousOn)
  have hc2' := integrableOn_Ioi_of_bound (f := fun s => |w2 s| * |bcCp (s - X)|)
    (M := K * K0 * Real.exp (2 / 3 * X)) (m := N + 1) hX.le hcont2 hbd
  have hc2 : IntegrableOn (fun s => |w2 s| * |airyPrimC (s - X)|) (Ioi X) := by
    refine IntegrableOn.congr_fun hc2' ?_ measurableSet_Ioi
    intro s hs
    simp only
    rw [airyPrimC_eq_bcCp (sub_pos.mpr hs)]
  rw [← Ioc_union_Ioi_eq_Ioi hhX.le]
  exact hc1.union hc2

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.airyBC_primDecay_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyBC_primDecay_pos

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.airyBC_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyBC_id

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.airyBC_id_global' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyBC_id_global

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.airyBC_integrableOn_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyBC_integrableOn_abs

/-- **Step 1 (derivative of `B`)**: for `t ≠ 0`, `B' = Ai`, where `B = airyPrimB`. -/
theorem airyPrimB_hasDerivAt {t : ℝ} (ht : t ≠ 0) : HasDerivAt airyPrimB (airyAi t) t := by
  rcases lt_or_gt_of_ne ht with h | h
  · have hev : ∀ᶠ s in nhds t, airyPrimB s = bcP s :=
      Filter.eventually_of_mem (Iio_mem_nhds h) fun s hs => airyPrimB_eq_bcP_neg (le_of_lt hs)
    exact (bcP_hasDerivAt t).congr_of_eventuallyEq hev
  · have hev : ∀ᶠ s in nhds t, airyPrimB s = bcP s - 1 :=
      Filter.eventually_of_mem (Ioi_mem_nhds h) fun s hs => airyPrimB_eq_bcP_sub_one (Set.mem_Ioi.1 hs)
    exact ((bcP_hasDerivAt t).sub_const 1).congr_of_eventuallyEq hev

/-- **Step 1 (derivative of `C`)**: for `t ≠ 0`, `C' = B` (`C` is not differentiable at `0`: `B` jumps there). -/
theorem airyPrimC_hasDerivAt {t : ℝ} (ht : t ≠ 0) : HasDerivAt airyPrimC (airyPrimB t) t := by
  rcases lt_or_gt_of_ne ht with h | h
  · have hev : ∀ᶠ s in nhds t, airyPrimC s = bcCm s :=
      Filter.eventually_of_mem (Iio_mem_nhds h) fun s hs => airyPrimC_eq_bcCm (le_of_lt hs)
    have hB : airyPrimB t = bcP t := airyPrimB_eq_bcP_neg (le_of_lt h)
    rw [hB]
    exact (bcCm_hasDerivAt t).congr_of_eventuallyEq hev
  · have hev : ∀ᶠ s in nhds t, airyPrimC s = bcCp s :=
      Filter.eventually_of_mem (Ioi_mem_nhds h) fun s hs => airyPrimC_eq_bcCp (Set.mem_Ioi.1 hs)
    have hB : airyPrimB t = bcP t - 1 := airyPrimB_eq_bcP_sub_one h
    rw [hB]
    exact (bcCp_hasDerivAt t).congr_of_eventuallyEq hev

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.airyPrimB_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyPrimB_hasDerivAt

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.airyPrimC_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyPrimC_hasDerivAt

/-- `C = airyPrimC` is measurable (piecewise continuous: `bcCm` on `(-∞,0]`, `bcCp` on `(0,∞)`). -/
theorem airyPrimC_measurable : Measurable airyPrimC := by
  have h : airyPrimC = fun t => if 0 < t then bcCp t else bcCm t := by
    funext t
    rcases le_or_gt t 0 with ht | ht
    · rw [airyPrimC_eq_bcCm ht]
      simp only [not_lt.2 ht, ↓reduceIte]
    · rw [airyPrimC_eq_bcCp ht]
      simp only [ht, ↓reduceIte]
  rw [h]
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    bcCp_continuous.measurable bcCm_continuous.measurable

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.airyPrimC_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyPrimC_measurable

end FormalResearch.ModularBootstrap.FiveTerm
