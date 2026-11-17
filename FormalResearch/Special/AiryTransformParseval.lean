module

public import FormalResearch.Special.AiryTransformEval
public import FormalResearch.Special.AiryCftQUnc
public import FormalResearch.Special.AiryCftZeros
public import FormalResearch.Special.AiryZeroOrder

/-!
# Parseval at the Airy zeros: `⟨G, F⟩ = Σ_n F(a_n) \overline{G(a_n)} / Ai'(a_n)²` on the Airy Paley–Wiener space

Let `PW = A L²(0,∞)` (`AiryTransformProj`).  For `φ, ψ ∈ L²(ℝ)` the functions `Ψφ`, `Ψψ` are entire with
`‖Ψφ(z)‖² ≤ 23 ‖φ‖² (1+|z|) e(z)` (`AiryTransformEval`), so `f(z) = Ψφ(z) \overline{Ψψ(\bar z)}` is entire with
`‖f(z)‖ ≤ 23 ‖φ‖‖ψ‖ (1+|z|) e(z)` and `f ∈ L¹(ℝ)`.  The Airy quadrature `airyQ_hasSum_unc` (Theorem Q, CFT/PR240
`AIRY_POISSON` Cor. D1: `∫ f = Σ f(a_n)/Ai'(a_n)²` for entire `f` with growth `(1+|u|)^ν e(u)`, any real `ν`) gives

* `airy_parseval_psi`: `Σ_{n≥1} Ψφ(a_n) \overline{Ψψ(a_n)}/Ai'(a_n)² = ⟨Pψ, Pφ⟩` (`HasSum`, absolutely convergent);
* `airyBasisVec n = K(·, a_n)/|Ai'(a_n)| = A(1_{t>0} Ai(a_n+·))/|Ai'(a_n)|`, an **orthonormal** family in `PW` (the Gram
  matrix is `K(a_n,a_m) = δ_{nm} Ai'(a_n)²`, by `K = (Ai Ai' - Ai' Ai)/(x-y)`) which is **complete** in `PW`
  (`airyPW_hilbertBasis : HilbertBasis ℕ ℂ airyPW`): the Parseval identity applied to `F ⟂ all e_n` gives `‖F‖ = 0`;
* `airyPW_parseval`: `⟨G,F⟩ = Σ_n ⟨G, e_n⟩⟨e_n, F⟩` and `⟨e_n, F⟩ = Ψφ(a_n)/|Ai'(a_n)|` for `F = Aφ`.

This is the ONB `{K(·,a_n)/|Ai'(a_n)|}` and the Parseval sum `Σ F G(a_n)/Ai'(a_n)²` of `LOCAL_AIRY_MODEL` Lemma Q2 (de
Branges orthogonal sampling at the zeros of `Ai`); the completeness here uses the Clark/Theorem-Q quadrature, not an
independent good-circle + Liouville argument.

Numerical check (scipy, Gauss–Legendre on `[0,40]`, `a_n` for `n ≤ 40`): `‖Ai(a_n+·)1_{t>0}‖²/Ai'(a_n)² = 1` to `10⁻¹²`, and for
`φ(t) = t e^{-t}` on `(0,∞)` (`‖φ‖² = 1/4`) the partial sums `Σ_{n ≤ N} (∫ φ(t) Ai(a_n+t) dt)²/Ai'(a_n)²` for
`N = 1, 5, 10, 20, 40` are `0.24283, 0.24843, 0.24940, 0.24979, 0.24993`, converging to `0.25`.

**Not formalised:** the description of `PW` as an entire-function space with intrinsic growth characterisation
(Paley–Wiener–Schwartz converse, survey T7).
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set
open scoped ComplexInnerProductSpace Real

namespace FormalResearch.Special

/-- The zeros `a_n`, `n ≥ 0` (shifted index: `airyZ n = a_{n+1}`). -/
noncomputable def airyZ (n : ℕ) : ℝ := airyZero (n + 1)

lemma airyAi_airyZ (n : ℕ) : airyAi (airyZ n) = 0 := airyAi_airyZero (n + 1)

lemma airyAi'_airyZ_ne_zero (n : ℕ) : airyAi' (airyZ n) ≠ 0 := by
  have h := airyZero_deriv_ne_zero (n + 1)
  rw [airyZ]
  intro h0
  apply h
  rw [deriv_airyAiC_ofReal, h0]; simp

lemma airyZ_injective : Function.Injective airyZ := by
  intro n m h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := airyZero_lt_of_lt (n := n + 1) (m := m + 1) (by omega) (by omega)
    simp only [airyZ] at h; linarith
  · have := airyZero_lt_of_lt (n := m + 1) (m := n + 1) (by omega) (by omega)
    simp only [airyZ] at h; linarith

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

/-! ### The orthonormal basis `K(·, a_n)/|Ai'(a_n)|` -/

lemma airyKerL2_mem (u : ℝ) : airyKerL2 u ∈ airyPW :=
  (mem_airyPW_iff_exists _).mpr ⟨airyHalf u, airyPL_airyHalf u, rfl⟩

lemma inner_airyKerL2_airyKerL2 (u v : ℝ) :
    inner ℂ (airyKerL2 u) (airyKerL2 v) = (airyKer u v : ℂ) := by
  unfold airyKerL2
  rw [airyA_inner, inner_airyHalf_airyHalf]

lemma airyKer_airyZ (n m : ℕ) :
    airyKer (airyZ n) (airyZ m) = if n = m then airyAi' (airyZ n) ^ 2 else 0 := by
  by_cases h : n = m
  · subst h
    simp [airyKer_self, airyAi_airyZ]
  · have hne : airyZ n ≠ airyZ m := fun h' => h (airyZ_injective h')
    rw [airyKer_of_ne hne]
    simp [h, airyKernelAi, airyAi_airyZ]

/-- `e_n = K(·, a_n)/|Ai'(a_n)| ∈ PW`. -/
noncomputable def airyBasisVec (n : ℕ) : AiryL2 :=
  (((1 / |airyAi' (airyZ n)| : ℝ) : ℂ)) • airyKerL2 (airyZ n)

lemma airyBasisVec_mem (n : ℕ) : airyBasisVec n ∈ airyPW :=
  Submodule.smul_mem _ _ (airyKerL2_mem _)

/-- **Orthonormality**: `⟨e_n, e_m⟩ = δ_{nm}`. -/
theorem airyBasisVec_orthonormal : Orthonormal ℂ airyBasisVec := by
  rw [orthonormal_iff_ite]
  intro n m
  unfold airyBasisVec
  rw [inner_smul_left, inner_smul_right, inner_airyKerL2_airyKerL2, airyKer_airyZ]
  have hn := airyAi'_airyZ_ne_zero n
  have hpos : 0 < |airyAi' (airyZ n)| := abs_pos.mpr hn
  by_cases h : n = m
  · subst h
    simp only [↓reduceIte, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    have : (1 / |airyAi' (airyZ n)|) * ((1 / |airyAi' (airyZ n)|) * airyAi' (airyZ n) ^ 2) = 1 := by
      have := sq_abs (airyAi' (airyZ n))
      field_simp
      rw [this]
    rw [this]; simp
  · simp [h]

/-- `⟨e_n, A φ⟩ = Ψφ(a_n)/|Ai'(a_n)|`. -/
lemma inner_airyBasisVec_airyA (n : ℕ) (φ : AiryL2) :
    inner ℂ (airyBasisVec n) (airyA φ) =
      (((1 / |airyAi' (airyZ n)| : ℝ) : ℂ)) * airyPsi φ (airyZ n) := by
  unfold airyBasisVec airyKerL2
  rw [inner_smul_left, Complex.conj_ofReal, airyA_inner, airyPsi_eq_inner]

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

/-- `e_n` as an element of the Hilbert space `PW`. -/
noncomputable def airyBasisVecPW (n : ℕ) : airyPW := ⟨airyBasisVec n, airyBasisVec_mem n⟩

theorem airyBasisVecPW_orthonormal : Orthonormal ℂ airyBasisVecPW := by
  rw [orthonormal_iff_ite]
  intro n m
  have := (orthonormal_iff_ite.mp airyBasisVec_orthonormal) n m
  simpa [airyBasisVecPW, Submodule.coe_inner] using this

instance : CompleteSpace airyPW := isClosed_airyPW.completeSpace_coe

/-- **`{K(·, a_n)/|Ai'(a_n)|}_{n ≥ 1}` is an orthonormal basis of the Airy Paley–Wiener space `PW`.** -/
noncomputable def airyPW_hilbertBasis : HilbertBasis ℕ ℂ airyPW :=
  HilbertBasis.mkOfOrthogonalEqBot airyBasisVecPW_orthonormal (by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx' : ∀ n, inner ℂ (airyBasisVecPW n) x = 0 := fun n =>
      (Submodule.mem_orthogonal _ _).mp hx _ (Submodule.subset_span ⟨n, rfl⟩)
    have : (x : AiryL2) = 0 := airyPW_eq_zero_of_inner x.2 fun n => by
      have := hx' n
      simpa [airyBasisVecPW, Submodule.coe_inner] using this
    exact Subtype.ext this)

theorem coe_airyPW_hilbertBasis : ⇑airyPW_hilbertBasis = airyBasisVecPW :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- **Parseval for the Hilbert basis**: `⟨G,F⟩ = Σ_n ⟨G, e_n⟩⟨e_n, F⟩`. -/
theorem airyPW_hasSum_inner (F G : airyPW) :
    HasSum (fun n : ℕ => inner ℂ G (airyBasisVecPW n) * inner ℂ (airyBasisVecPW n) F) (inner ℂ G F) := by
  have := airyPW_hilbertBasis.hasSum_inner_mul_inner G F
  rwa [coe_airyPW_hilbertBasis] at this

/-- info: 'FormalResearch.Special.airy_parseval_psi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_parseval_psi

/-- info: 'FormalResearch.Special.airyBasisVec_orthonormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyBasisVec_orthonormal

/-- info: 'FormalResearch.Special.airyPW_parseval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPW_parseval

/-- info: 'FormalResearch.Special.airyPW_eq_zero_of_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPW_eq_zero_of_inner

/-- info: 'FormalResearch.Special.airyPW_hilbertBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPW_hilbertBasis

end FormalResearch.Special
