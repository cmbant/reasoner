module

public import FormalResearch.CohnElkies.MellinLiftIntegrals
public import FormalResearch.CohnElkies.FresnelBranch

/-!
# Exact decomposition of the cut-off main term `I_C` and its branch leg

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, proof of `u1c:U3`(3), Step 1, Piece C, used in
`O.3(2)` (`u1co:O3`, `(e4)`). With `ε = c^{-1/3}`, `L = log(π² ξ)`, `A = c ε L`:

* `iMainIntegrand_eq_pc`: `K₀(iεv, ξ) W_X(iv) = g(v) e^{iψ(v)} X̃(i c_s v)` with `g = (1 - iεv)^{-1/2} e^{B_c(iεv)} M_ψ(iv)`
  and `ψ(v) = A v - π² v³/36 + c R(εv)` (uses `c ε³ = 1`);
* `iMainIntegrand_eq_smooth_add_branch`: for any `γ₀`, `χ₁`, with `G_sm = X̃(i c_s v) + γ₀ (iv)^{1/2} e^{iπ² v³/36} χ₁(v)`,
  `K₀ W = g e^{iψ} G_sm - γ₀ H_c(v) (iv)^{1/2} χ₁(v) e^{iAv}`, `H_c = g e^{icR(εv)}`;
* `pieceC_main_term`: conditional assembly. Under the named hypotheses (a) `φ = χ₁ H_c` is a `C²` amplitude supported in `[-1,1]`
  with bounded derivatives (paper: `|H_c| + |H_c'| + |H_c''| ≤ C`), (b) the smooth part `∫ χ₀ g e^{iψ} G_sm` is `O(A^{-2})`
  (paper: two integrations by parts, `G_sm` regularity from `u1c:U1`/`(e27)`; the variable-phase inequality is queued), and (c)
  integrability of the two pieces, `I_C = γ₀/(2√π ξ) A^{-3/2} + O(ξ^{-1} A^{-2})`, the branch leg being `fresnel_branch`.

Status: proved; `pieceC_main_term` is conditional on (a)-(c).
-/

@[expose] public section

open MeasureTheory Complex Set
open scoped Real

namespace FormalResearch.CohnElkies

/-- The amplitude `g(v) = (1 - iεv)^{-1/2} e^{B_c(iεv)} M_ψ(iv)`. -/
noncomputable def pcAmp (δ₀ : ℝ) (m : ℕ) (c v : ℝ) : ℂ :=
  (1 - (((liftEps c * v : ℝ) : ℂ) * Complex.I)) ^ (-(1 / 2 : ℂ)) *
    Complex.exp (FormalResearch.Asymptotics.binetDiff c (((liftEps c * v : ℝ) : ℂ) * Complex.I)) *
      liftMultiplier δ₀ m ((v : ℂ) * Complex.I)

/-- The phase `ψ(v) = A v - π² v³/36 + c R(εv)`, `A = c ε log(π² ξ)`. -/
noncomputable def pcPhase (c ξ v : ℝ) : ℝ :=
  (c * liftEps c * Real.log (Real.pi ^ 2 * ξ)) * v - Real.pi ^ 2 / 36 * v ^ 3 + c * edgeR (liftEps c * v)

/-- `H_c(v) = g(v) e^{icR(εv)}`. -/
noncomputable def pcH (δ₀ : ℝ) (m : ℕ) (c v : ℝ) : ℂ :=
  pcAmp δ₀ m c v * Complex.exp (Complex.I * ((c * edgeR (liftEps c * v) : ℝ) : ℂ))

lemma liftEps_cube {c : ℝ} (hc : 0 < c) : c * liftEps c ^ 3 = 1 := by
  unfold liftEps
  rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]
  have : (-(1 / 3 : ℝ)) * ((3 : ℕ) : ℝ) = -1 := by norm_num
  rw [this, Real.rpow_neg_one]
  field_simp

theorem iMainIntegrand_eq_pc (X : ℝ → ℝ) (δ₀ : ℝ) (m : ℕ) {c : ℝ} (hc : 0 < c) {ξ : ℝ} (hξ : 0 < ξ) (v : ℝ) :
    iMainIntegrand X δ₀ m c ξ v = pcAmp δ₀ m c v * Complex.exp (Complex.I * (pcPhase c ξ v : ℝ)) *
      airyTwistedLaplaceC X ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) := by
  have hε3 : (c : ℂ) * (liftEps c : ℂ) ^ 3 = 1 := by exact_mod_cast liftEps_cube hc
  unfold iMainIntegrand liftSymbol
  rw [mellinK0_imag_eq c ξ _ hξ]
  have hexp : Complex.I * (c : ℂ) * ((Real.log (Real.pi ^ 2 * ξ) * (liftEps c * v) - Real.pi ^ 2 / 36 * (liftEps c * v) ^ 3 +
      edgeR (liftEps c * v) : ℝ) : ℂ) = Complex.I * (pcPhase c ξ v : ℝ) := by
    unfold pcPhase
    push_cast
    linear_combination (-(Complex.I * (Real.pi : ℂ) ^ 2 / 36 * (v : ℂ) ^ 3)) * hε3
  rw [hexp]
  unfold pcAmp
  ring

theorem iMainIntegrand_eq_smooth_add_branch (X : ℝ → ℝ) (δ₀ : ℝ) (m : ℕ) {c : ℝ} (hc : 0 < c) {ξ : ℝ} (hξ : 0 < ξ)
    (γ₀ : ℝ) (χ₁ : ℝ → ℝ) (v : ℝ) :
    iMainIntegrand X δ₀ m c ξ v =
      pcAmp δ₀ m c v * Complex.exp (Complex.I * (pcPhase c ξ v : ℝ)) *
          (airyTwistedLaplaceC X ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) +
            (γ₀ : ℂ) * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) * Complex.exp (Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) * (χ₁ v : ℂ)) -
        (γ₀ : ℂ) * pcH δ₀ m c v * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) * (χ₁ v : ℂ) *
          Complex.exp (Complex.I * ((c * liftEps c * Real.log (Real.pi ^ 2 * ξ) : ℝ) : ℂ) * (v : ℂ)) := by
  rw [iMainIntegrand_eq_pc X δ₀ m hc hξ v]
  have hE : Complex.exp (Complex.I * (pcPhase c ξ v : ℝ)) * Complex.exp (Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((c * edgeR (liftEps c * v) : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((c * liftEps c * Real.log (Real.pi ^ 2 * ξ) : ℝ) : ℂ) * (v : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    unfold pcPhase
    push_cast
    ring
  unfold pcH
  linear_combination (-((γ₀ : ℂ) * pcAmp δ₀ m c v * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) * (χ₁ v : ℂ))) * hE

lemma pcH_zero (δ₀ : ℝ) (m : ℕ) (c : ℝ) : pcH δ₀ m c 0 = 1 := by
  simp [pcH, pcAmp, liftMultiplier, FormalResearch.Asymptotics.binetDiff, edgeR]


/-- **Piece C, conditional assembly.** Hypotheses: `φ = χ₁ H_c` is a `C²` amplitude supported in `[-1,1]` with `‖φ‖, ‖φ'‖, ‖φ''‖ ≤ M`
(`b0`-`b2`), `χ₀(·/v_*) = 1` where `χ₁ ≠ 0`, `χ₁(0) = 1`, `A = c ε log(π² ξ) ≥ 1`, the smooth part is `O(A^{-2})`
(`hsmooth`, the output of two integrations by parts against `e^{iψ}`), and the two pieces are integrable. Then
`(2πξ)⁻¹ ∫ χ₀(v/v_*) K₀ W dv = γ₀ √π A^{-3/2}/(2πξ) + O((C_s + |γ₀|(12D+2)M)/(ξ A²))`. -/
theorem pieceC_main_term (X : ℝ → ℝ) (δ₀ : ℝ) (m : ℕ) {c : ℝ} (hc : 0 < c) {ξ : ℝ} (hξ : 0 < ξ)
    (γ₀ : ℝ) (χ₀ χ₁ : ℝ → ℝ) (vs : ℝ) (hχ0 : ∀ v, χ₁ v ≠ 0 → χ₀ (v / vs) = 1) (hχ1_0 : χ₁ 0 = 1)
    (hsupp : ∀ v : ℝ, 1 < |v| → χ₁ v = 0)
    (hφ : ContDiff ℝ 2 (fun v : ℝ => (χ₁ v : ℂ) * pcH δ₀ m c v)) {M : ℝ}
    (b0 : ∀ v, ‖(χ₁ v : ℂ) * pcH δ₀ m c v‖ ≤ M)
    (b1 : ∀ v, ‖deriv (fun v : ℝ => (χ₁ v : ℂ) * pcH δ₀ m c v) v‖ ≤ M)
    (b2 : ∀ v, ‖deriv (deriv (fun v : ℝ => (χ₁ v : ℂ) * pcH δ₀ m c v)) v‖ ≤ M)
    {A : ℝ} (hAdef : A = c * liftEps c * Real.log (Real.pi ^ 2 * ξ)) (hA : 1 ≤ A)
    (hint_s : Integrable fun v : ℝ => (χ₀ (v / vs) : ℂ) * (pcAmp δ₀ m c v * Complex.exp (Complex.I * (pcPhase c ξ v : ℝ)) *
      (airyTwistedLaplaceC X ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) +
        (γ₀ : ℂ) * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) * Complex.exp (Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) * (χ₁ v : ℂ))))
    (hint_b : Integrable fun v : ℝ => (χ₀ (v / vs) : ℂ) * ((γ₀ : ℂ) * pcH δ₀ m c v * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) * (χ₁ v : ℂ) *
      Complex.exp (Complex.I * ((c * liftEps c * Real.log (Real.pi ^ 2 * ξ) : ℝ) : ℂ) * (v : ℂ))))
    {Cs : ℝ} (hsmooth : ‖∫ v : ℝ, (χ₀ (v / vs) : ℂ) * (pcAmp δ₀ m c v * Complex.exp (Complex.I * (pcPhase c ξ v : ℝ)) *
      (airyTwistedLaplaceC X ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) +
        (γ₀ : ℂ) * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) * Complex.exp (Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) * (χ₁ v : ℂ)))‖ ≤ Cs / A ^ 2) :
    ‖((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * (∫ v : ℝ, (χ₀ (v / vs) : ℂ) * iMainIntegrand X δ₀ m c ξ v) -
        ((γ₀ * Real.sqrt Real.pi * A ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) : ℝ) : ℂ)‖ ≤
      (Cs + |γ₀| * ((12 * (∫ t in Ioi (0 : ℝ), fresnelDom t) + 2) * M)) / (2 * Real.pi * ξ * A ^ 2) := by
  have hAp : 0 < A := by linarith
  have hpi : 0 < 2 * Real.pi * ξ := by positivity
  set φ : ℝ → ℂ := fun v => (χ₁ v : ℂ) * pcH δ₀ m c v with hφdef
  have hfr := fresnel_branch (φ := φ) hφ (fun v hv => by simp [hφdef, hsupp v hv]) b0 b1 b2 hA
  have hφ0 : φ 0 = 1 := by simp [hφdef, hχ1_0, pcH_zero]
  rw [hφ0, mul_one] at hfr
  set D := ∫ t in Ioi (0 : ℝ), fresnelDom t
  set E : ℂ := (∫ v : ℝ, φ v * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) * Complex.exp (Complex.I * A * v)) +
    ((Real.sqrt Real.pi * A ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) with hE
  -- pointwise decomposition
  have hpt : ∀ v : ℝ, (χ₀ (v / vs) : ℂ) * iMainIntegrand X δ₀ m c ξ v =
      (χ₀ (v / vs) : ℂ) * (pcAmp δ₀ m c v * Complex.exp (Complex.I * (pcPhase c ξ v : ℝ)) *
        (airyTwistedLaplaceC X ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) +
          (γ₀ : ℂ) * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) * Complex.exp (Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) * (χ₁ v : ℂ))) -
      (χ₀ (v / vs) : ℂ) * ((γ₀ : ℂ) * pcH δ₀ m c v * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) * (χ₁ v : ℂ) *
        Complex.exp (Complex.I * ((c * liftEps c * Real.log (Real.pi ^ 2 * ξ) : ℝ) : ℂ) * (v : ℂ))) := fun v => by
    rw [iMainIntegrand_eq_smooth_add_branch X δ₀ m hc hξ γ₀ χ₁ v]; ring
  have hbr : ∀ v : ℝ, (χ₀ (v / vs) : ℂ) * ((γ₀ : ℂ) * pcH δ₀ m c v * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) * (χ₁ v : ℂ) *
        Complex.exp (Complex.I * ((c * liftEps c * Real.log (Real.pi ^ 2 * ξ) : ℝ) : ℂ) * (v : ℂ))) =
      (γ₀ : ℂ) * (φ v * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) * Complex.exp (Complex.I * A * v)) := fun v => by
    by_cases h1 : χ₁ v = 0
    · simp [hφdef, h1]
    · rw [hχ0 v h1, ← hAdef]; simp only [hφdef]; push_cast; ring
  have hint : ∫ v : ℝ, (χ₀ (v / vs) : ℂ) * iMainIntegrand X δ₀ m c ξ v =
      (∫ v : ℝ, (χ₀ (v / vs) : ℂ) * (pcAmp δ₀ m c v * Complex.exp (Complex.I * (pcPhase c ξ v : ℝ)) *
        (airyTwistedLaplaceC X ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) +
          (γ₀ : ℂ) * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) * Complex.exp (Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) * (χ₁ v : ℂ)))) -
      (γ₀ : ℂ) * ∫ v : ℝ, φ v * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) * Complex.exp (Complex.I * A * v) := by
    rw [integral_congr_ae (ae_of_all _ hpt), integral_sub hint_s hint_b, integral_congr_ae (ae_of_all _ hbr), integral_const_mul]
  set S : ℂ := ∫ v : ℝ, (χ₀ (v / vs) : ℂ) * (pcAmp δ₀ m c v * Complex.exp (Complex.I * (pcPhase c ξ v : ℝ)) *
    (airyTwistedLaplaceC X ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) +
      (γ₀ : ℂ) * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) * Complex.exp (Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) * (χ₁ v : ℂ))) with hS
  have hpi' : ((2 * Real.pi * ξ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
  have hEdef : (∫ v : ℝ, φ v * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) * Complex.exp (Complex.I * A * v)) =
      E - ((Real.sqrt Real.pi * A ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) := by rw [hE]; ring
  rw [hint, hEdef]
  have hid : ((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * (S - (γ₀ : ℂ) * (E - ((Real.sqrt Real.pi * A ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ))) -
      ((γ₀ * Real.sqrt Real.pi * A ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) : ℝ) : ℂ) =
      ((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * (S - (γ₀ : ℂ) * E) := by
    push_cast
    field_simp
    ring
  rw [hid, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hpi.le]
  have hE' : ‖E‖ ≤ (12 * D + 2) * M / A ^ 2 := hfr
  have h1 : ‖S - (γ₀ : ℂ) * E‖ ≤ Cs / A ^ 2 + |γ₀| * ((12 * D + 2) * M / A ^ 2) := by
    refine (norm_sub_le _ _).trans (add_le_add hsmooth ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hE' (abs_nonneg _)
  calc (2 * Real.pi * ξ)⁻¹ * ‖S - (γ₀ : ℂ) * E‖ ≤ (2 * Real.pi * ξ)⁻¹ * (Cs / A ^ 2 + |γ₀| * ((12 * D + 2) * M / A ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hpi.le)
    _ = _ := by field_simp

/-- info: 'FormalResearch.CohnElkies.iMainIntegrand_eq_pc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.iMainIntegrand_eq_pc
/-- info: 'FormalResearch.CohnElkies.iMainIntegrand_eq_smooth_add_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.iMainIntegrand_eq_smooth_add_branch
/-- info: 'FormalResearch.CohnElkies.pieceC_main_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.pieceC_main_term

end FormalResearch.CohnElkies
