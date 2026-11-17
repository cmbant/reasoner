module

public import FormalResearch.Special.AiryTransformBasis
public import FormalResearch.Special.AiryCftQUnc

/-!
# Parseval at the Airy zeros via the Airy quadrature (Theorem Q)

Let `PW = A L²(0,∞)` (`AiryTransformProj`).  For `φ, ψ ∈ L²(ℝ)` the functions `Ψφ`, `Ψψ` are entire with
`‖Ψφ(z)‖² ≤ 23 ‖φ‖² (1+|z|) e(z)` (`AiryTransformEval`), so `f(z) = Ψφ(z) \overline{Ψψ(\bar z)}` is entire with
`‖f(z)‖ ≤ 23 ‖φ‖‖ψ‖ (1+|z|) e(z)` and `f ∈ L¹(ℝ)`.  The Airy quadrature `airyQ_hasSum_unc` (Theorem Q, CFT/PR240
`AIRY_POISSON` Cor. D1: `∫ f = Σ f(a_n)/Ai'(a_n)²` for entire `f` with growth `(1+|u|)^ν e(u)`, any real `ν`) gives

* `airy_parseval_psi`: `Σ_{n≥1} Ψφ(a_n) \overline{Ψψ(a_n)}/Ai'(a_n)² = ⟨Pψ, Pφ⟩` (`HasSum`, absolutely convergent);
* `airyPW_parseval`: `⟨G,F⟩ = Σ_n ⟨e_n, F⟩ \overline{⟨e_n, G⟩}` for `F, G ∈ PW`, `e_n = K(·,a_n)/|Ai'(a_n)|`
  (`AiryTransformBasis`), with `⟨e_n, Aφ⟩ = Ψφ(a_n)/|Ai'(a_n)|`;
* `airyPW_eq_zero_of_inner`: completeness of `{e_n}` in `PW` (apply Parseval to `F ⟂ all e_n`).

This proof of completeness/Parseval **depends on Theorem Q** (`AiryCftQQuad`, which uses the Fejér–Riesz/Hardy arc bound);
`AiryTransformLiouville` gives an independent proof of completeness (good circles + a removable-singularity/Liouville
argument), from which `AiryTransformHilbert` builds the Hilbert basis and the Parseval identity without Theorem Q.

Numerical check (scipy, Gauss–Legendre on `[0,40]`, `a_n` for `n ≤ 40`): `‖Ai(a_n+·)1_{t>0}‖²/Ai'(a_n)² = 1` to `10⁻¹²`, and for
`φ(t) = t e^{-t}` on `(0,∞)` (`‖φ‖² = 1/4`) the partial sums `Σ_{n ≤ N} (∫ φ(t) Ai(a_n+t) dt)²/Ai'(a_n)²` for
`N = 1, 5, 10, 20, 40` are `0.24283, 0.24843, 0.24940, 0.24979, 0.24993`, converging to `0.25`.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set
open scoped ComplexInnerProductSpace Real

namespace FormalResearch.Special

lemma differentiable_conj_comp {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    Differentiable ℂ (fun z => (starRingEnd ℂ) (g ((starRingEnd ℂ) z))) := by
  intro z
  have := (hg ((starRingEnd ℂ) z)).conj_conj
  simpa [Function.comp_def] using this

/-- The product `f(z) = Ψφ(z) \overline{Ψψ(\bar z)}` is entire. -/
lemma differentiable_airyPsiC_prod (φ ψ : AiryL2) :
    Differentiable ℂ (fun z : ℂ => airyPsiC φ z * (starRingEnd ℂ) (airyPsiC ψ ((starRingEnd ℂ) z))) :=
  (differentiable_airyPsiC φ).mul (differentiable_conj_comp (differentiable_airyPsiC ψ))

lemma norm_airyPsiC_prod_le (φ ψ : AiryL2) (u : ℂ) :
    ‖airyPsiC φ u * (starRingEnd ℂ) (airyPsiC ψ ((starRingEnd ℂ) u))‖ ≤
      (23 * ‖φ‖ * ‖ψ‖) * (1 + ‖u‖) ^ (1 : ℝ) * airyEnv u := by
  have h1 := norm_airyPsiC_sq_le φ u
  have h2 := norm_airyPsiC_sq_le ψ ((starRingEnd ℂ) u)
  rw [airyEnv_conj, Complex.norm_conj] at h2
  rw [norm_mul, Complex.norm_conj, Real.rpow_one]
  set a := ‖airyPsiC φ u‖
  set b := ‖airyPsiC ψ ((starRingEnd ℂ) u)‖
  have he := airyEnv_pos u
  have hX : 0 ≤ (23 * ‖φ‖ * ‖ψ‖) * (1 + ‖u‖) * airyEnv u := by positivity
  have hsq : (a * b) ^ 2 ≤ ((23 * ‖φ‖ * ‖ψ‖) * (1 + ‖u‖) * airyEnv u) ^ 2 := by
    have h3 : (a * b) ^ 2 = a ^ 2 * b ^ 2 := by ring
    rw [h3]
    calc a ^ 2 * b ^ 2 ≤ (23 * ‖φ‖ ^ 2 * (1 + ‖u‖) * airyEnv u) * (23 * ‖ψ‖ ^ 2 * (1 + ‖u‖) * airyEnv u) :=
          mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
      _ = _ := by ring
  have := abs_le_of_sq_le_sq hsq hX
  exact (le_abs_self _).trans this

/-- **Parseval at the Airy zeros, function form**: for `φ, ψ ∈ L²(ℝ)`,
`Σ_{n} Ψφ(a_n) \overline{Ψψ(a_n)}/Ai'(a_n)² = ⟨Pψ, Pφ⟩`. -/
theorem airy_parseval_psi (φ ψ : AiryL2) :
    HasSum (fun n : ℕ => airyPsi φ (airyZ n) * (starRingEnd ℂ) (airyPsi ψ (airyZ n)) /
        (((airyAi' (airyZ n)) ^ 2 : ℝ) : ℂ))
      (inner ℂ (airyPL ψ) (airyPL φ)) := by
  set f : ℂ → ℂ := fun z => airyPsiC φ z * (starRingEnd ℂ) (airyPsiC ψ ((starRingEnd ℂ) z)) with hf
  have hreal : ∀ x : ℝ, f (x : ℂ) = airyPsi φ x * (starRingEnd ℂ) (airyPsi ψ x) := by
    intro x
    simp only [hf, Complex.conj_ofReal, airyPsiC_ofReal]
  -- integrability and the integral
  have hAφ := airyA_indProj_ae φ
  have hAψ := airyA_indProj_ae ψ
  have hint_ae : (fun x : ℝ => f (x : ℂ)) =ᵐ[volume]
      fun x => inner ℂ (airyA (airyPL ψ) x) (airyA (airyPL φ) x) := by
    filter_upwards [hAφ, hAψ] with x h1 h2
    rw [hreal, RCLike.inner_apply, airyPL_apply, airyPL_apply, h1, h2]
  have hfi : Integrable (fun x : ℝ => f (x : ℂ)) volume :=
    (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (airyA (airyPL ψ)) (airyA (airyPL φ))).congr
      hint_ae.symm
  have hQ := airyQ_hasSum_unc (differentiable_airyPsiC_prod φ ψ) hfi
    (C := 23 * ‖φ‖ * ‖ψ‖) (ν := 1) (by positivity) (norm_airyPsiC_prod_le φ ψ)
  have hint : ∫ x : ℝ, f (x : ℂ) = inner ℂ (airyPL ψ) (airyPL φ) := by
    rw [integral_congr_ae hint_ae, ← MeasureTheory.L2.inner_def, airyA_inner]
  rw [hint] at hQ
  have hfun : (fun n : ℕ => airyPsi φ (airyZ n) * (starRingEnd ℂ) (airyPsi ψ (airyZ n)) /
        (((airyAi' (airyZ n)) ^ 2 : ℝ) : ℂ)) =
      fun n : ℕ => f (airyZero (n + 1) : ℂ) / (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2 := by
    funext n
    rw [deriv_airyAiC_ofReal]
    have := hreal (airyZero (n + 1))
    simp only [airyZ] at this ⊢
    rw [this]
    push_cast
    rfl
  rw [hfun]
  exact hQ

/-- **Parseval on `PW` at the zeros of `Ai`**:
`⟨G, F⟩ = Σ_n ⟨e_n, F⟩ \overline{⟨e_n, G⟩}` for `F, G ∈ PW`. -/
theorem airyPW_parseval {F G : AiryL2} (hF : F ∈ airyPW) (hG : G ∈ airyPW) :
    HasSum (fun n : ℕ => inner ℂ (airyBasisVec n) F * (starRingEnd ℂ) (inner ℂ (airyBasisVec n) G))
      (inner ℂ G F) := by
  obtain ⟨φ, hφ, rfl⟩ := (mem_airyPW_iff_exists F).mp hF
  obtain ⟨ψ, hψ, rfl⟩ := (mem_airyPW_iff_exists G).mp hG
  have h := airy_parseval_psi φ ψ
  rw [hψ, hφ] at h
  rw [airyA_inner]
  convert h using 2 with n
  rw [inner_airyBasisVec_airyA, inner_airyBasisVec_airyA]
  have hn := airyAi'_airyZ_ne_zero n
  have h1 : ((1 / |airyAi' (airyZ n)| : ℝ) : ℂ) * ((1 / |airyAi' (airyZ n)| : ℝ) : ℂ) =
      1 / (((airyAi' (airyZ n)) ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_div]
    congr 1
    have := sq_abs (airyAi' (airyZ n))
    field_simp
    rw [this]
  rw [map_mul, Complex.conj_ofReal]
  calc _ = (((1 / |airyAi' (airyZ n)| : ℝ) : ℂ) * ((1 / |airyAi' (airyZ n)| : ℝ) : ℂ)) *
        (airyPsi φ (airyZ n) * (starRingEnd ℂ) (airyPsi ψ (airyZ n))) := by ring
    _ = _ := by rw [h1]; ring

/-- **Completeness**: `F ∈ PW` orthogonal to every `e_n` is zero. -/
theorem airyPW_eq_zero_of_inner {F : AiryL2} (hF : F ∈ airyPW)
    (h : ∀ n, inner ℂ (airyBasisVec n) F = 0) : F = 0 := by
  have h1 := airyPW_parseval hF hF
  simp only [h, map_zero, mul_zero] at h1
  have h2 : inner ℂ F F = 0 := (hasSum_zero.unique h1).symm
  exact inner_self_eq_zero.mp h2

/-- info: 'FormalResearch.Special.airy_parseval_psi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_parseval_psi

/-- info: 'FormalResearch.Special.airyPW_parseval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPW_parseval

/-- info: 'FormalResearch.Special.airyPW_eq_zero_of_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPW_eq_zero_of_inner

end FormalResearch.Special
