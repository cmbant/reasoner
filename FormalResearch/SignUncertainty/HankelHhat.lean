module

public import FormalResearch.SignUncertainty.HankelEdgeRep

/-!
# `ct:hhat-strip`: analytic continuation of `ĥ` to the strip (`u1cl:rep`, weighted-Mellin clause)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:boas` Step 2, equation `ct:hhat-strip`,
and `langer_transport.tex`, `u1cl:weighted-mellin`.  For `c > 3/2`, `f ∈ 𝒜_c^ε` (`IsHankelEigenfn`), the
log-density `h = hankelHL c f` of `dm(ξ) = c (fρ₀)(cξ) dξ` in `L = log π²ξ` and
`ĥ(ζ) = ∫_ℝ e^{-cζL} h(L) dL` (`hankelHhat`; the paper's `ĥ(-icζ)`):

* `hankelHhat_eq_mel`: `ĥ(ζ) = ∫_0^∞ (π²ξ)^{-cζ} dm(ξ)` (substitution `ξ = e^L/π²`);
* `hankelHhat_formula` (`ct:hhat-strip`, first half): for `0 ≤ Re ζ < 1`,
  `ĥ(ζ) = (1-ζ)^{-1/2} e^{B_c(ζ)} e^{c S̃₀(ζ)} W̃_c(ζ)`;
* `hankelHhat_bound` (`ct:hhat-strip`, second half): for `0 ≤ σ ≤ 1/4`,
  `‖ĥ(σ+iτ)‖ ≤ 3 M[f] e^{c Re S̃₀(σ+iτ)}`.

**Proved**, for general `f ∈ 𝒜_c^ε` (no normalisation, feasibility or sign data), `c > 3/2`, `ε = ±1`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Asymptotics

/-- Log-density `h(L)` of `dm(ξ) = c (fρ₀)(cξ) dξ` in `L = log π²ξ` (`ξ = e^L/π²`, `dξ = ξ dL`). -/
noncomputable def hankelHL (c : ℝ) (f : ℝ → ℝ) (L : ℝ) : ℝ :=
  c * (f (c * (Real.exp L / π ^ 2)) * hankelRho0 c (c * (Real.exp L / π ^ 2))) * (Real.exp L / π ^ 2)

/-- `ĥ(ζ) = ∫_ℝ e^{-cζL} h(L) dL` (the paper's `ĥ(-icζ)`). -/
noncomputable def hankelHhat (c : ℝ) (f : ℝ → ℝ) (ζ : ℂ) : ℂ :=
  ∫ L : ℝ, Complex.exp (-((c : ℂ) * ζ * (L : ℂ))) * (hankelHL c f L : ℂ)

/-- Substitution `ξ = e^L/π²`: `ĥ(ζ) = ∫_0^∞ (π²ξ)^{-cζ} c (fρ₀)(cξ) dξ`. -/
theorem hankelHhat_eq_mel (c : ℝ) (f : ℝ → ℝ) (ζ : ℂ) :
    hankelHhat c f ζ = ∫ ξ in Ioi (0 : ℝ),
      Complex.exp (-((c : ℂ) * ζ * Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ)))) *
        ((c * (f (c * ξ) * hankelRho0 c (c * ξ)) : ℝ) : ℂ) := by
  have hpi : (0 : ℝ) < π ^ 2 := by positivity
  set φ : ℝ → ℝ := fun L => Real.exp L / π ^ 2 with hφ
  have himg : φ '' univ = Ioi 0 := by
    ext ξ
    simp only [mem_image, mem_univ, true_and, mem_Ioi, hφ]
    constructor
    · rintro ⟨L, rfl⟩; positivity
    · intro hξ
      refine ⟨Real.log (π ^ 2 * ξ), ?_⟩
      rw [Real.exp_log (by positivity)]; field_simp
  have hd : ∀ L ∈ (univ : Set ℝ), HasDerivWithinAt φ (Real.exp L / π ^ 2) univ L :=
    fun L _ => ((Real.hasDerivAt_exp L).div_const _).hasDerivWithinAt
  have hinj : InjOn φ univ := by
    intro a _ b _ hab
    simp only [hφ] at hab
    have := (div_left_inj' hpi.ne').1 hab
    exact Real.exp_injective this
  rw [← himg, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd hinj, setIntegral_univ]
  unfold hankelHhat
  refine integral_congr_ae (Filter.Eventually.of_forall fun L => ?_)
  have hp : 0 ≤ Real.exp L / π ^ 2 := by positivity
  dsimp only
  rw [abs_of_nonneg hp]
  have hlog : Complex.log ((Real.pi : ℂ) ^ 2 * ((φ L : ℝ) : ℂ)) = (L : ℂ) := by
    have : (Real.pi : ℂ) ^ 2 * ((φ L : ℝ) : ℂ) = ((Real.exp L : ℝ) : ℂ) := by
      simp only [hφ]; push_cast; field_simp
    rw [this, ← Complex.ofReal_log (Real.exp_pos L).le, Real.log_exp]
  rw [hlog, Complex.real_smul]
  simp only [hankelHL, hφ]
  push_cast
  ring

/-- Inverted Mellin kernel at a general point of the closed strip:
`K₀(ζ, ξ)⁻¹ = (1-ζ)^{1/2} e^{-B_c(ζ)} e^{-c S̃₀(ζ)} (π²ξ)^{-cζ}`, for `Re ζ < 1`. -/
theorem hankelKernel_inv_eq (c : ℝ) {ζ : ℂ} (h1 : ζ.re < 1) (ξ : ℝ) :
    (mellinK0 c ζ ξ)⁻¹ =
      (1 - ζ) ^ (1 / 2 : ℂ) * Complex.exp (-(binetDiff c ζ)) * Complex.exp (-((c : ℂ) * stripS0Tilde ζ)) *
        Complex.exp (-((c : ℂ) * ζ * Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ)))) := by
  have hne : (1 - ζ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  unfold mellinK0 mellinPhi
  rw [Complex.cpow_neg, mul_inv, mul_inv, inv_inv, ← Complex.exp_neg, ← Complex.exp_neg]
  have : -((c : ℂ) * (stripS0Tilde ζ + ζ * Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ)))) =
      -((c : ℂ) * stripS0Tilde ζ) + -((c : ℂ) * ζ * Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ))) := by ring
  push_cast
  rw [this, Complex.exp_add]
  ring

/-- **`ct:hhat-strip`** (first half). For `c > 3/2`, `f ∈ 𝒜_c^ε`, `0 ≤ Re ζ < 1`:
`ĥ(ζ) = (1-ζ)^{-1/2} e^{B_c(ζ)} e^{c S̃₀(ζ)} W̃_c(ζ)`. -/
theorem hankelHhat_formula {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re < 1) :
    hankelHhat c f ζ = (1 - ζ) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c ζ) *
      Complex.exp ((c : ℂ) * stripS0Tilde ζ) * hankelWtS c ε f ζ := by
  have hne : (1 - ζ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  set K : ℂ := (1 - ζ) ^ (1 / 2 : ℂ) * Complex.exp (-(binetDiff c ζ)) *
    Complex.exp (-((c : ℂ) * stripS0Tilde ζ)) with hK
  have hW : hankelWtS c ε f ζ = K * hankelHhat c f ζ := by
    rw [hankelWtS_mel_eq hc hf h0 h1, hankelHhat_eq_mel, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun ξ _ => ?_
    simp only [hankelKernel_inv_eq c h1 ξ, hK]
    ring
  have hKne : K ≠ 0 := by
    simp only [hK]
    have hc0 : (1 - ζ) ^ (1 / 2 : ℂ) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; simp [hne]
    exact mul_ne_zero (mul_ne_zero hc0 (Complex.exp_ne_zero _)) (Complex.exp_ne_zero _)
  have hA : (1 - ζ) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c ζ) * Complex.exp ((c : ℂ) * stripS0Tilde ζ) = K⁻¹ := by
    simp only [hK]
    rw [Complex.cpow_neg, mul_inv, mul_inv, ← Complex.exp_neg, ← Complex.exp_neg, neg_neg, neg_neg]
  rw [hA, hW, ← mul_assoc, inv_mul_cancel₀ hKne, one_mul]

/-- Elementary bracket: `|1-ζ|^{-1/2} (1+|ζ|)^{1/2} ≤ 2` for `0 ≤ Re ζ ≤ 1/4`. -/
lemma bracket_le_two {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 4) :
    ‖1 - ζ‖ ^ (-(1 / 2 : ℝ)) * (1 + ‖ζ‖) ^ (1 / 2 : ℝ) ≤ 2 := by
  have hm1 : 3 / 4 ≤ ‖1 - ζ‖ := by
    have := Complex.re_le_norm (1 - ζ); simp at this; linarith
  have hm2 : |ζ.im| ≤ ‖1 - ζ‖ := by
    have := Complex.abs_im_le_norm (1 - ζ); simpa using this
  have hz : ‖ζ‖ ≤ 1 / 4 + |ζ.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im ζ
    rw [abs_of_nonneg h0] at h; linarith
  have hr : (1 + ‖ζ‖) ≤ 4 * ‖1 - ζ‖ := by linarith [abs_nonneg ζ.im]
  have hmpos : 0 < ‖1 - ζ‖ := by linarith
  rw [Real.rpow_neg hmpos.le, ← div_eq_inv_mul, ← Real.div_rpow (by positivity) hmpos.le]
  have hq : (1 + ‖ζ‖) / ‖1 - ζ‖ ≤ 4 := by rw [div_le_iff₀ hmpos]; linarith
  calc ((1 + ‖ζ‖) / ‖1 - ζ‖) ^ (1 / 2 : ℝ) ≤ 4 ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hq (by norm_num)
    _ = 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num

/-- **`ct:hhat-strip`** (second half): for `c > 3/2`, `f ∈ 𝒜_c^ε`, `ε = ±1`, `0 ≤ σ ≤ 1/4` and real `τ`,
`‖ĥ(σ+iτ)‖ ≤ 3 M[f] e^{c Re S̃₀(σ+iτ)}` (the paper's `|ĥ(-ic(σ+iτ))| ≤ C e^{c Re S̃₀(σ+iτ)}`, `M[f] = 1`). -/
theorem hankelHhat_bound {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1 / 4) (τ : ℝ) :
    ‖hankelHhat c f ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      3 * hankelMass c f * Real.exp (c * (stripS0Tilde ((σ : ℂ) + (τ : ℂ) * Complex.I)).re) := by
  set ζ : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I with hζ
  have hre : ζ.re = σ := by simp [hζ]
  have h0 : 0 ≤ ζ.re := by rw [hre]; exact hσ0
  have h1' : ζ.re ≤ 1 / 4 := by rw [hre]; exact hσ1
  have h1 : ζ.re < 1 := by linarith
  have hc0 : 0 < c := by linarith
  have hne : (1 - ζ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [hankelHhat_formula hc hf h0 h1, norm_mul, norm_mul, norm_mul]
  have n1 : ‖(1 - ζ) ^ (-(1 / 2 : ℂ))‖ = ‖1 - ζ‖ ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.norm_cpow_of_ne_zero hne]
    have : (-(1 / 2 : ℂ)).im = 0 := by simp
    rw [this, mul_zero, Real.exp_zero, div_one]
    congr 1; simp
  have n2 : ‖Complex.exp (binetDiff c ζ)‖ ≤ Real.exp (7 / (36 * c)) := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.2 ((Complex.re_le_norm _).trans ?_)
    refine (binetDiff_norm_le hc0 h1).trans ?_
    have : 1 / (1 - ζ.re) ≤ 4 / 3 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    calc 1 / (12 * c) * (1 / (1 - ζ.re) + 1) ≤ 1 / (12 * c) * (4 / 3 + 1) := by gcongr
      _ = 7 / (36 * c) := by field_simp; norm_num
  have n3 : ‖Complex.exp ((c : ℂ) * stripS0Tilde ζ)‖ = Real.exp (c * (stripS0Tilde ζ).re) := by
    rw [Complex.norm_exp]; simp
  have n4 := hankelWtS_norm_le hc hf hε h0 (by linarith : ζ.re ≤ 1)
  have hb := bracket_le_two h0 h1'
  have hM := hankelMass_nonneg hc0 f
  have hexp : Real.exp (7 / (36 * c)) * Real.exp (1 / (6 * c)) ≤ 3 / 2 := by
    rw [← Real.exp_add]
    have hx : 7 / (36 * c) + 1 / (6 * c) ≤ 13 / 54 := by
      rw [show 7 / (36 * c) + 1 / (6 * c) = 13 / (36 * c) by field_simp; norm_num,
        div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hy := Real.add_one_le_exp (-(7 / (36 * c) + 1 / (6 * c)))
    have hpos := Real.exp_pos (7 / (36 * c) + 1 / (6 * c))
    have hprod : Real.exp (-(7 / (36 * c) + 1 / (6 * c))) * Real.exp (7 / (36 * c) + 1 / (6 * c)) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith
  have hE := Real.exp_pos (c * (stripS0Tilde ζ).re)
  rw [n1, n3]
  have hP : (0 : ℝ) ≤ (1 + ‖ζ‖) ^ (1 / 2 : ℝ) := by positivity
  calc ‖1 - ζ‖ ^ (-(1 / 2 : ℝ)) * ‖Complex.exp (binetDiff c ζ)‖ * Real.exp (c * (stripS0Tilde ζ).re) *
        ‖hankelWtS c ε f ζ‖
      ≤ ‖1 - ζ‖ ^ (-(1 / 2 : ℝ)) * Real.exp (7 / (36 * c)) * Real.exp (c * (stripS0Tilde ζ).re) *
        (hankelMass c f * Real.exp (1 / (6 * c)) * (1 + ‖ζ‖) ^ (1 / 2 : ℝ)) := by
        gcongr
    _ = (‖1 - ζ‖ ^ (-(1 / 2 : ℝ)) * (1 + ‖ζ‖) ^ (1 / 2 : ℝ)) *
        (Real.exp (7 / (36 * c)) * Real.exp (1 / (6 * c))) * hankelMass c f *
        Real.exp (c * (stripS0Tilde ζ).re) := by ring
    _ ≤ 2 * (3 / 2) * hankelMass c f * Real.exp (c * (stripS0Tilde ζ).re) := by
        gcongr
    _ = 3 * hankelMass c f * Real.exp (c * (stripS0Tilde ζ).re) := by ring

/-- info: 'FormalResearch.SignUncertainty.hankelHhat_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelHhat_formula

/-- info: 'FormalResearch.SignUncertainty.hankelHhat_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelHhat_bound

end FormalResearch.SignUncertainty
