module

public import FormalResearch.Special.AiryTransformEval
public import FormalResearch.Special.AiryCftZeros
public import FormalResearch.Special.AiryZeroOrder

/-!
# The orthonormal system `K(·, a_n)/|Ai'(a_n)|` in the Airy Paley–Wiener space

`airyZ n = a_{n+1}` are the zeros of `Ai`.  `airyKerL2 a_n = A(1_{t>0} Ai(a_n+·)) = K(·,a_n) ∈ PW` and
`airyBasisVec n = K(·,a_n)/|Ai'(a_n)|` satisfy

* `airyBasisVec_orthonormal`: `⟨e_n, e_m⟩ = δ_{nm}` (the Gram matrix is `K(a_n,a_m) = δ_{nm} Ai'(a_n)²`, since
  `K(x,y) = (Ai(x) Ai'(y) - Ai'(x) Ai(y))/(x-y)` and `Ai(a_n) = 0`);
* `inner_airyBasisVec_airyA`: `⟨e_n, A φ⟩ = Ψφ(a_n)/|Ai'(a_n)|`, i.e. the Fourier coefficient of `F = Aφ` along `e_n` is
  the value `F(a_n)/|Ai'(a_n)|` (reproducing property at the zeros).

Numerical check (scipy, Gauss–Legendre on `[0,40]`): `‖Ai(a_n+·)1_{t>0}‖²/Ai'(a_n)² = 1` to `10⁻¹²` for `n ≤ 4`.

Completeness of the system in `PW` and the Parseval identity are in `AiryTransformLiouville` / `AiryTransformHilbert`
(a proof that does not use Hardy-space estimates) and `AiryTransformParseval` (via the Airy quadrature, Theorem Q).
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


/-- info: 'FormalResearch.Special.airyBasisVec_orthonormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyBasisVec_orthonormal

end FormalResearch.Special
