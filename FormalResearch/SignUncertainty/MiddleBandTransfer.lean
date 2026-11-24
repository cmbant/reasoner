module

public import FormalResearch.SignUncertainty.MiddleBandAssembly
public import FormalResearch.SignUncertainty.O4QuotientBound
public import FormalResearch.CohnElkies.HighBandEstimate
public import FormalResearch.CohnElkies.AiryWindowInversion

/-!
# GT.2a: the middle transfer for the lift of an Airy seed

Source: `CFT/sign_uncertainty/paper/mellin_airy_toolkit.tex`, `cegt:GT2a`; proof in `u1c_estimate_proofs.tex`.

* `iMainIntegrand_eq`: `K₀(iεv, ξ) W(v) = k_c(εv) e^{icΦ(εv; L)} W(v)`, `L = log(π²ξ)`, `W(v) = W_X(iv)`.
* `middle_transfer`: for a seed `X` with the `U.2` package whose symbol `W(v) = M_ψ(iv) X̃(i c_s v)` satisfies the `GT.1` bounds,
  `|ξ I_main[X](ξ) - (k/c_s) F_ψ(-(a₀ + ε/(2)) / c_s)| ≤ C (S^{-3/2} L + c^{-5/2})`
  for `S = hbS c ξ ≥ 100`, `0 < L ≤ 0.002`, `a₀ = c ε α̃(L) = κ₀ π² S`, given the normal form `O4NormalForm L τ` of `O.4`.

* `gt1_hyp`, `middle_transfer_gt1`: the same with the `GT.1` bounds in their stated form (`|∂^j W| ≤ C|v|^{1/2-j}` for `0 < |v| ≤ 1`, `j ≥ 1`;
  `|∂^j W| ≤ C|v|^{-5/2-j}` for `|v| ≥ 1`; `W(0) = O(1)`, `W - W(0) = O(|v|^{1/2})`) and the normal form obtained from the proved
  quotient bound `o4QuotientBound` (`o4_normal_form`).

Status: proved; `middle_transfer` is conditional on `O4NormalForm L τ` (the existence of the `O.4` normal map) and on the `GT.1`
symbol bounds, which are hypotheses; `middle_transfer_gt1` is conditional only on the `GT.1` bounds (the normal form comes from `o4QuotientBound`).  Not formalised: the verification of the `GT.1` bounds for the spline-multiplied seeds.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- The symbol `W(v) = W_X(iv)` of the lift on the imaginary axis. -/
noncomputable def liftW (X : ℝ → ℝ) (δ₀ : ℝ) (m : ℕ) (v : ℝ) : ℂ := liftSymbol X δ₀ m ((v : ℂ) * Complex.I)

/-- `iMainIntegrand` in terms of `k_c` and the edge phase. -/
theorem iMainIntegrand_eq (X : ℝ → ℝ) (δ₀ : ℝ) (m : ℕ) {c ξ : ℝ} (hξ : 0 < ξ) (v : ℝ) :
    iMainIntegrand X δ₀ m c ξ v =
      outerK c (liftEps c * v) * Complex.exp (Complex.I * ((c * edgePhi (Real.log (Real.pi ^ 2 * ξ)) (liftEps c * v) : ℝ) : ℂ)) *
        liftW X δ₀ m v := by
  unfold iMainIntegrand liftW
  rw [mellinK0_imag_eq c ξ _ hξ, ← outerK_eq, edgePhi_eq_cubic_add_ceHth]
  have hmul : ((liftEps c * v : ℝ) : ℂ) * Complex.I = Complex.I * ((liftEps c * v : ℝ) : ℂ) := mul_comm _ _
  rw [hmul]
  unfold edgeR
  push_cast
  ring_nf

lemma liftEps_rpow_15 {c : ℝ} (hc : 0 < c) : liftEps c ^ (15 / 2 : ℝ) = c ^ (-(5 / 2 : ℝ)) := by
  unfold liftEps
  rw [← Real.rpow_mul hc.le]; norm_num

set_option maxHeartbeats 1600000 in
/-- **`GT.2a` (`cegt:GT2a`), the middle transfer for the lift of an Airy seed.** -/
theorem middle_transfer {ϑ : ℝ → ℝ} {K1 K2 : ℝ} (hϑ : Prof ϑ K1 K2) (AW : ℝ) (hAW : 1 ≤ AW) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X : ℝ → ℝ} {δ₀ : ℝ} {m : ℕ} {c ξ L : ℝ} {τ : ℂ → ℂ} {W1 W2 W3 : ℝ → ℂ},
      HasU2 X → Continuous X → 0 ≤ δ₀ → 2 ≤ c → 0 < ξ → L = Real.log (Real.pi ^ 2 * ξ) →
      O4NormalForm L τ → 0 < L → L ≤ 0.002 → 100 ≤ hbS c ξ →
      (∀ s, s ≠ 0 → HasDerivAt (liftW X δ₀ m) (W1 s) s ∧ HasDerivAt W1 (W2 s) s ∧ HasDerivAt W2 (W3 s) s) →
      (∀ s, 1 / 2 ≤ |s| → ‖liftW X δ₀ m s‖ ≤ AW * |s| ^ (-(5 / 2 : ℝ)) ∧ ‖W1 s‖ ≤ AW * |s| ^ (-(7 / 2 : ℝ)) ∧
        ‖W2 s‖ ≤ AW * |s| ^ (-(9 / 2 : ℝ)) ∧ ‖W3 s‖ ≤ AW * |s| ^ (-(11 / 2 : ℝ))) →
      ‖liftW X δ₀ m 0‖ ≤ AW →
      (∀ s : ℝ, 0 < |s| → |s| ≤ 9 → ‖liftW X δ₀ m s - liftW X δ₀ m 0‖ ≤ AW * |s| ^ (1 / 2 : ℝ) ∧
        ‖W1 s‖ ≤ AW * |s| ^ (-(1 / 2) : ℝ) ∧ ‖W2 s‖ ≤ AW * |s| ^ (-(3 / 2) : ℝ) ∧ ‖W3 s‖ ≤ AW * |s| ^ (-(5 / 2) : ℝ)) →
      ‖(ξ : ℂ) * iMain X δ₀ m c ξ - ((ceK : ℂ) / (ceCs : ℂ)) *
          ((windowSmooth δ₀ m X (-((c * liftEps c * edgeAlphaTilde L + liftEps c / 2) / ceCs)) : ℝ) : ℂ)‖ ≤
        C * (hbS c ξ ^ (-(3 / 2 : ℝ)) * L + c ^ (-(5 / 2 : ℝ))) := by
  obtain ⟨C0, hC0, hM⟩ := middle_transfer_abstract hϑ AW hAW
  refine ⟨C0, hC0, ?_⟩
  intro X δ₀ m c ξ L τ W1 W2 W3 hX hXc hδ hc hξ hLdef hτ hL0 hL2 hS100 hWd hWb hW0 hSm
  have hc0 : 0 < c := by linarith
  have hε := liftEps_pos hc0
  set ε : ℝ := liftEps c with hεdef
  have hcε : c * ε ^ 3 = 1 := by have := liftEps_cube_mul hc0; linarith
  set S : ℝ := hbS c ξ with hSdef
  have hSe : S = L / (Real.pi ^ 2 * ε ^ 2) := by
    rw [hSdef, hbS, ← hLdef]
  have hS : L = Real.pi ^ 2 * ε ^ 2 * S := by
    rw [hSe]; field_simp
  have hGint : Integrable (fun v : ℝ => outerK c (ε * v) * Complex.exp (Complex.I * ((c * edgePhi L (ε * v) : ℝ) : ℂ)) * liftW X δ₀ m v) := by
    refine (hX.integrable_iMainIntegrand hδ m hc0 hξ).congr (Eventually.of_forall fun v => ?_)
    rw [iMainIntegrand_eq X δ₀ m hξ v, hLdef]
  have hbd := hM hτ hL0 hL2 hc hε hcε hS hS100 hWd hWb hW0 hSm hGint
  set a : ℝ := c * ε * edgeAlphaTilde L + ε / 2 with ha
  have hRid := airy_reference_identity hX hXc hδ m hξ a
  have hJ : (∫ v : ℝ, iMainIntegrand X δ₀ m c ξ v) =
      ∫ v : ℝ, outerK c (ε * v) * Complex.exp (Complex.I * ((c * edgePhi L (ε * v) : ℝ) : ℂ)) * liftW X δ₀ m v := by
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only []
    rw [iMainIntegrand_eq X δ₀ m hξ v, hLdef]
  have hξ' : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hξ.ne'
  have hcs : (ceCs : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ceCs_pos.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  set R : ℂ := ∫ u : ℝ, liftW X δ₀ m u * Complex.exp (Complex.I * (((c * ε * edgeAlphaTilde L + ε / 2) * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ)) with hR
  have hRid' : ((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * R = ((ceK : ℂ) / ((ceCs : ℂ) * (ξ : ℂ))) *
      ((windowSmooth δ₀ m X (-(a / ceCs)) : ℝ) : ℂ) := hRid
  have key : (ξ : ℂ) * iMain X δ₀ m c ξ - ((ceK : ℂ) / (ceCs : ℂ)) *
      ((windowSmooth δ₀ m X (-(a / ceCs)) : ℝ) : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ((∫ v : ℝ, outerK c (ε * v) * Complex.exp (Complex.I * ((c * edgePhi L (ε * v) : ℝ) : ℂ)) * liftW X δ₀ m v) - R) := by
    have h1 : ((ceK : ℂ) / (ceCs : ℂ)) * ((windowSmooth δ₀ m X (-(a / ceCs)) : ℝ) : ℂ) =
        (ξ : ℂ) * (((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * R) := by
      rw [hRid']; field_simp
    rw [h1]
    unfold iMain
    rw [hJ]
    push_cast
    field_simp
  rw [key, norm_mul]
  have hn : ‖((2 * Real.pi : ℝ) : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    apply inv_le_one_of_one_le₀
    nlinarith [Real.pi_gt_three]
  have hrpow := liftEps_rpow_15 hc0
  calc ‖((2 * Real.pi : ℝ) : ℂ)⁻¹‖ * ‖(∫ v : ℝ, outerK c (ε * v) * Complex.exp (Complex.I * ((c * edgePhi L (ε * v) : ℝ) : ℂ)) * liftW X δ₀ m v) - R‖
      ≤ 1 * (C0 * (S ^ (-(3 / 2 : ℝ)) * L + ε ^ (15 / 2 : ℝ))) := by gcongr
    _ = C0 * (S ^ (-(3 / 2 : ℝ)) * L + c ^ (-(5 / 2 : ℝ))) := by rw [one_mul, hεdef, hrpow]

lemma rpow_le_rpow_of_le_one_neg {s a b : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hab : a ≤ b) : s ^ (-a) ≤ s ^ (-b) :=
  Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith)

/-- The `GT.1` bounds (`(cegt:eqGT1)`: `|∂^j W| ≤ C|v|^{1/2-j}` for `0 < |v| ≤ 1`, `j ≥ 1`, and `|∂^j W| ≤ C|v|^{-5/2-j}` for
`|v| ≥ 1`; `W(0) = O(1)`, `W - W(0) = O(|v|^{1/2})`) imply the hypotheses of `middle_transfer` with `A_W = max 1 (2C)`. -/
lemma gt1_hyp {C : ℝ} (hC : 0 ≤ C) {W W1 W2 W3 : ℝ → ℂ}
    (hA : ∀ s : ℝ, 0 < |s| → |s| ≤ 1 → ‖W1 s‖ ≤ C * |s| ^ (-(1 / 2) : ℝ) ∧ ‖W2 s‖ ≤ C * |s| ^ (-(3 / 2) : ℝ) ∧
      ‖W3 s‖ ≤ C * |s| ^ (-(5 / 2) : ℝ))
    (hB : ∀ s : ℝ, 1 ≤ |s| → ‖W s‖ ≤ C * |s| ^ (-(5 / 2) : ℝ) ∧ ‖W1 s‖ ≤ C * |s| ^ (-(7 / 2) : ℝ) ∧
      ‖W2 s‖ ≤ C * |s| ^ (-(9 / 2) : ℝ) ∧ ‖W3 s‖ ≤ C * |s| ^ (-(11 / 2) : ℝ))
    (hW0 : ‖W 0‖ ≤ C) (hH : ∀ s : ℝ, 0 < |s| → |s| ≤ 1 → ‖W s - W 0‖ ≤ C * |s| ^ (1 / 2 : ℝ)) :
    (∀ s : ℝ, 1 / 2 ≤ |s| → ‖W s‖ ≤ max 1 (2 * C) * |s| ^ (-(5 / 2 : ℝ)) ∧ ‖W1 s‖ ≤ max 1 (2 * C) * |s| ^ (-(7 / 2 : ℝ)) ∧
      ‖W2 s‖ ≤ max 1 (2 * C) * |s| ^ (-(9 / 2 : ℝ)) ∧ ‖W3 s‖ ≤ max 1 (2 * C) * |s| ^ (-(11 / 2 : ℝ))) ∧
    ‖W 0‖ ≤ max 1 (2 * C) ∧
    (∀ s : ℝ, 0 < |s| → |s| ≤ 9 → ‖W s - W 0‖ ≤ max 1 (2 * C) * |s| ^ (1 / 2 : ℝ) ∧
      ‖W1 s‖ ≤ max 1 (2 * C) * |s| ^ (-(1 / 2) : ℝ) ∧ ‖W2 s‖ ≤ max 1 (2 * C) * |s| ^ (-(3 / 2) : ℝ) ∧
      ‖W3 s‖ ≤ max 1 (2 * C) * |s| ^ (-(5 / 2) : ℝ)) := by
  set A : ℝ := max 1 (2 * C) with hAdef
  have hA2 : 2 * C ≤ A := le_max_right _ _
  have hAC : C ≤ A := by linarith
  have hA0 : 0 ≤ A := by linarith [le_max_left (1 : ℝ) (2 * C)]
  refine ⟨?_, hW0.trans hAC, ?_⟩
  · intro s hs
    have hs0 : 0 < |s| := by linarith
    by_cases h1 : 1 ≤ |s|
    · obtain ⟨b0, b1, b2, b3⟩ := hB s h1
      refine ⟨b0.trans ?_, b1.trans ?_, b2.trans ?_, b3.trans ?_⟩ <;> gcongr
    · rw [not_le] at h1
      obtain ⟨a1, a2, a3⟩ := hA s hs0 h1.le
      refine ⟨?_, a1.trans ?_, a2.trans ?_, a3.trans ?_⟩
      · have hh := hH s hs0 h1.le
        have hr : |s| ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one (abs_nonneg _) h1.le (by norm_num)
        have hp : 1 ≤ |s| ^ (-(5 / 2 : ℝ)) := by
          rw [Real.rpow_neg hs0.le]
          exact (one_le_inv₀ (Real.rpow_pos_of_pos hs0 _)).2 (Real.rpow_le_one (abs_nonneg _) h1.le (by norm_num))
        have h2 : ‖W s‖ ≤ ‖W 0‖ + ‖W s - W 0‖ := norm_le_insert' _ _
        have : ‖W s‖ ≤ 2 * C := by nlinarith
        nlinarith
      · exact mul_le_mul hAC (rpow_le_rpow_of_le_one_neg (a := 1 / 2) (b := 7 / 2) hs0 h1.le (by norm_num)) (by positivity) hA0
      · exact mul_le_mul hAC (rpow_le_rpow_of_le_one_neg (a := 3 / 2) (b := 9 / 2) hs0 h1.le (by norm_num)) (by positivity) hA0
      · exact mul_le_mul hAC (rpow_le_rpow_of_le_one_neg (a := 5 / 2) (b := 11 / 2) hs0 h1.le (by norm_num)) (by positivity) hA0
  · intro s hs0 hs9
    by_cases h1 : |s| ≤ 1
    · obtain ⟨a1, a2, a3⟩ := hA s hs0 h1
      exact ⟨(hH s hs0 h1).trans (by gcongr), a1.trans (by gcongr), a2.trans (by gcongr), a3.trans (by gcongr)⟩
    · rw [not_le] at h1
      obtain ⟨b0, b1, b2, b3⟩ := hB s h1.le
      have hq : ∀ t : ℝ, t ≤ 0 → |s| ^ t ≤ 1 := fun t ht => Real.rpow_le_one_of_one_le_of_nonpos h1.le ht
      have hge : 1 ≤ |s| ^ (1 / 2 : ℝ) := Real.one_le_rpow h1.le (by norm_num)
      have hmono : ∀ a b : ℝ, a ≤ b → |s| ^ a ≤ |s| ^ b := fun a b hab => Real.rpow_le_rpow_of_exponent_le h1.le hab
      refine ⟨?_, b1.trans ?_, b2.trans ?_, b3.trans ?_⟩
      · have h2 : ‖W s - W 0‖ ≤ ‖W s‖ + ‖W 0‖ := norm_sub_le _ _
        have h5 := hq (-(5 / 2)) (by norm_num)
        have : ‖W s‖ ≤ C := by nlinarith
        nlinarith
      · exact mul_le_mul hAC (hmono _ _ (by norm_num)) (by positivity) hA0
      · exact mul_le_mul hAC (hmono _ _ (by norm_num)) (by positivity) hA0
      · exact mul_le_mul hAC (hmono _ _ (by norm_num)) (by positivity) hA0

/-- **The `GT.1` bounds for a symbol `W`** (`(cegt:eqGT1)`): there are derivatives `W1 = ∂W`, `W2 = ∂²W`, `W3 = ∂³W` off `0` with
`|∂^j W| ≤ A|v|^{1/2-j}` for `0 < |v| ≤ 1`, `j = 1, 2, 3`; `|∂^j W| ≤ A|v|^{-5/2-j}` for `|v| ≥ 1`, `j = 0, …, 3`;
`|W(0)| ≤ A` and `|W(v) - W(0)| ≤ A|v|^{1/2}` for `0 < |v| ≤ 1`.  This is the single named input of the middle band (`middle_transfer_gt1`,
`o5_e6`, `o6`, `o9p_m1`): discharging it for the spline-multiplied seeds (task `gt1_plan.md`) changes no downstream statement. -/
def Gt1Bounds (A : ℝ) (W : ℝ → ℂ) : Prop :=
  ∃ W1 W2 W3 : ℝ → ℂ,
    (∀ s, s ≠ 0 → HasDerivAt W (W1 s) s ∧ HasDerivAt W1 (W2 s) s ∧ HasDerivAt W2 (W3 s) s) ∧
    (∀ s : ℝ, 0 < |s| → |s| ≤ 1 → ‖W1 s‖ ≤ A * |s| ^ (-(1 / 2) : ℝ) ∧ ‖W2 s‖ ≤ A * |s| ^ (-(3 / 2) : ℝ) ∧
      ‖W3 s‖ ≤ A * |s| ^ (-(5 / 2) : ℝ)) ∧
    (∀ s : ℝ, 1 ≤ |s| → ‖W s‖ ≤ A * |s| ^ (-(5 / 2) : ℝ) ∧ ‖W1 s‖ ≤ A * |s| ^ (-(7 / 2) : ℝ) ∧
      ‖W2 s‖ ≤ A * |s| ^ (-(9 / 2) : ℝ) ∧ ‖W3 s‖ ≤ A * |s| ^ (-(11 / 2) : ℝ)) ∧
    ‖W 0‖ ≤ A ∧ (∀ s : ℝ, 0 < |s| → |s| ≤ 1 → ‖W s - W 0‖ ≤ A * |s| ^ (1 / 2 : ℝ))

/-- Non-vacuity of `Gt1Bounds`: the zero symbol satisfies it for every `A ≥ 0`. -/
theorem gt1Bounds_zero {A : ℝ} (hA : 0 ≤ A) : Gt1Bounds A (fun _ => 0) := by
  refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun s _ => ⟨hasDerivAt_const s _, hasDerivAt_const s _, hasDerivAt_const s _⟩,
    fun s _ _ => ?_, fun s _ => ?_, by simpa using hA, fun s _ _ => ?_⟩
  · simp only [norm_zero]; refine ⟨?_, ?_, ?_⟩ <;> positivity
  · simp only [norm_zero]; refine ⟨?_, ?_, ?_, ?_⟩ <;> positivity
  · simp only [sub_self, norm_zero]; positivity

/-- **`GT.2a` from the `GT.1` bounds and the quotient bound `O.4(1)`.** -/
theorem middle_transfer_gt1 {ϑ : ℝ → ℝ} {K1 K2 : ℝ} (hϑ : Prof ϑ K1 K2) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X : ℝ → ℝ} {δ₀ : ℝ} {m : ℕ} {c ξ L : ℝ},
      HasU2 X → Continuous X → 0 ≤ δ₀ → 2 ≤ c → 0 < ξ → L = Real.log (Real.pi ^ 2 * ξ) →
      0 < L → L ≤ 0.002 → 100 ≤ hbS c ξ → Gt1Bounds A (liftW X δ₀ m) →
      ‖(ξ : ℂ) * iMain X δ₀ m c ξ - ((ceK : ℂ) / (ceCs : ℂ)) *
          ((windowSmooth δ₀ m X (-((c * liftEps c * edgeAlphaTilde L + liftEps c / 2) / ceCs)) : ℝ) : ℂ)‖ ≤
        C * (hbS c ξ ^ (-(3 / 2 : ℝ)) * L + c ^ (-(5 / 2 : ℝ))) := by
  obtain ⟨C0, hC0, hM⟩ := middle_transfer hϑ (max 1 (2 * A)) (le_max_left _ _)
  refine ⟨C0, hC0, ?_⟩
  intro X δ₀ m c ξ L hX hXc hδ hc hξ hLdef hL0 hL2 hS100 hG
  obtain ⟨W1, W2, W3, hWd, hA', hB', hW0, hH⟩ := hG
  obtain ⟨τ, hτ⟩ := o4_normal_form hL0 hL2 (o4QuotientBound hL0 hL2)
  obtain ⟨h1, h2, h3⟩ := gt1_hyp hA hA' hB' hW0 hH
  exact hM hX hXc hδ hc hξ hLdef hτ hL0 hL2 hS100 hWd h1 h2 h3

/-- info: 'FormalResearch.SignUncertainty.iMainIntegrand_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms iMainIntegrand_eq

/-- info: 'FormalResearch.SignUncertainty.middle_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms middle_transfer

/-- info: 'FormalResearch.SignUncertainty.gt1_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gt1_hyp

/-- info: 'FormalResearch.SignUncertainty.middle_transfer_gt1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms middle_transfer_gt1

/-- info: 'FormalResearch.SignUncertainty.gt1Bounds_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gt1Bounds_zero

end FormalResearch.SignUncertainty
