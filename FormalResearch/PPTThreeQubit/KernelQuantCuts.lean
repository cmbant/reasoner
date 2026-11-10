module

public import FormalResearch.PPTThreeQubit.KernelQuantMatrix
public import FormalResearch.PPTThreeQubit.Basic

/-!
# `prop:ppt3-kernel-quant` for the cut-product vectors

For the cut `c` and a unit `a ∈ ℂ²` let `cutEmb c a : ℂ⁴ → ℂ⁸` be `b ↦ U_c†(a ⊗ b)`, i.e.
`(cutEmb c a b)(i) = a(bit_c i) · b(rest_c i)` with the index maps of `IsProdA`, `IsProdB`, `IsProdC`.
It is an isometry (`cutEmb_isometry`), its range over unit `a` and all `b` is the set of normalised
cut-product vectors (`isCutProduct_iff`), and so `kernel_quant_matrix` gives
`kernel_quant_cutProduct`: for `λ = (L + L²/α)/μ` the lifted witness `W = W₀ + λ KᴴK` is non-negative
on every cut-product vector, under the hypotheses of `prop:ppt3-kernel-quant` (uniform in `a`, `c`).
-/

@[expose] public section

namespace FormalResearch.PPTThreeQubit

open Matrix
open scoped ComplexOrder

noncomputable section

/-- The index of the qubit `c` in the basis index `i` of `ℂ⁸`. -/
def bitOf (c : Fin 3) (i : Fin 8) : Fin 2 :=
  match c with
  | 0 => ⟨i.val / 4, by omega⟩
  | 1 => ⟨i.val / 2 % 2, by omega⟩
  | 2 => ⟨i.val % 2, by omega⟩

/-- The index of the other two qubits in the basis index `i` (as in `IsProdA/B/C`). -/
def restOf (c : Fin 3) (i : Fin 8) : Fin 4 :=
  match c with
  | 0 => ⟨i.val % 4, by omega⟩
  | 1 => ⟨2 * (i.val / 4) + i.val % 2, by omega⟩
  | 2 => ⟨i.val / 2, by omega⟩

/-- The embedding `b ↦ a ⊗ b` across the cut `c`. -/
def cutEmb (c : Fin 3) (a : Fin 2 → ℂ) : Matrix (Fin 8) (Fin 4) ℂ :=
  Matrix.of fun i k => a (bitOf c i) * (if restOf c i = k then 1 else 0)

theorem cutEmb_mulVec (c : Fin 3) (a : Fin 2 → ℂ) (b : Fin 4 → ℂ) (i : Fin 8) :
    (cutEmb c a *ᵥ b) i = a (bitOf c i) * b (restOf c i) := by
  simp only [cutEmb, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_eq_single (restOf c i)]
  · simp
  · intro k _ hk; rw [if_neg (Ne.symm hk)]; simp
  · simp

theorem star_dotProduct_self_real' {ι : Type*} [Fintype ι] (a : ι → ℂ) :
    star a ⬝ᵥ a = ((nsq a : ℝ) : ℂ) := by
  apply Complex.ext
  · rfl
  · simp only [dotProduct, Complex.im_sum, Pi.star_apply, Complex.star_def, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_im]
    refine Finset.sum_eq_zero fun i _ => ?_
    ring

theorem star_dotProduct_self_real (a : Fin 2 → ℂ) :
    star a ⬝ᵥ a = ((nsq a : ℝ) : ℂ) := star_dotProduct_self_real' a

theorem cutEmb_isometry (c : Fin 3) {a : Fin 2 → ℂ} (ha : nsq a = 1) : (cutEmb c a)ᴴ * cutEmb c a = 1 := by
  have h : star a ⬝ᵥ a = 1 := by rw [star_dotProduct_self_real, ha]; simp
  simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply, Complex.star_def] at h
  ext k l
  fin_cases c <;> fin_cases k <;> fin_cases l <;>
    simp [cutEmb, bitOf, restOf, Matrix.mul_apply, Fin.sum_univ_succ, Complex.star_def,
      Matrix.one_apply] <;> exact h

theorem nsq_eq_sum {ι : Type*} [Fintype ι] (v : ι → ℂ) : nsq v = ∑ i, Complex.normSq (v i) := by
  unfold nsq
  simp only [dotProduct, Complex.re_sum, Pi.star_apply, Complex.star_def, Complex.normSq_apply,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem eq_zero_of_nsq_eq_zero {ι : Type*} [Fintype ι] {v : ι → ℂ} (h : nsq v = 0) : v = 0 := by
  rw [nsq_eq_sum] at h
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (v i))).1 h
  ext i
  simpa using this i (Finset.mem_univ i)

theorem nsq_real_smul {ι : Type*} [Fintype ι] (s : ℝ) (v : ι → ℂ) :
    nsq ((s : ℂ) • v) = s ^ 2 * nsq v := by
  simp only [nsq_eq_sum, Pi.smul_apply, smul_eq_mul, map_mul, Complex.normSq_ofReal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem cutEmb_smul (c : Fin 3) (s : ℂ) (a : Fin 2 → ℂ) : cutEmb c (s • a) = s • cutEmb c a := by
  ext i k
  simp [cutEmb, mul_assoc]

theorem exists_cutEmb {x : Fin 8 → ℂ} (hx : IsCutProduct x) :
    ∃ (c : Fin 3) (a : Fin 2 → ℂ) (b : Fin 4 → ℂ), x = cutEmb c a *ᵥ b := by
  rcases hx with ⟨α, μ, h⟩ | ⟨α, μ, h⟩ | ⟨α, μ, h⟩
  · exact ⟨0, α, μ, funext fun i => by rw [cutEmb_mulVec]; exact h i⟩
  · exact ⟨1, α, μ, funext fun i => by rw [cutEmb_mulVec]; exact h i⟩
  · exact ⟨2, α, μ, funext fun i => by rw [cutEmb_mulVec]; exact h i⟩

/-- **`prop:ppt3-kernel-quant`** (explicit form).  Let `W₀` be Hermitian with
`|⟨p, W₀ q⟩| ≤ L ‖p‖‖q‖` (that is, `‖W₀‖∞ ≤ L`), and `K` any matrix.  Suppose, uniformly in the cut `c`
and the unit `a ∈ ℂ²`, with `M = K ∘ cutEmb c a` and `Ω = (a† ⊗ I) W₀ (a ⊗ I)` (compressed along
`cutEmb c a`): `Ω ≥ α` on `ker M`, and `‖M v‖² ≥ μ ‖v‖²` for `v ⊥ ker M`.  Then for
`λ = (L + L²/α)/μ` the lifted witness `W = W₀ + λ KᴴK` is non-negative on every cut-product vector. -/
theorem kernel_quant_cutProduct {ν : Type*} [Fintype ν] [DecidableEq ν]
    (W₀ : Matrix (Fin 8) (Fin 8) ℂ) (K : Matrix ν (Fin 8) ℂ) (hW : W₀.IsHermitian)
    {α L μ lam : ℝ} (hα : 0 < α) (hL0 : 0 ≤ L) (hμ : 0 < μ) (hlam : lam = (L + L ^ 2 / α) / μ)
    (hL : ∀ p q : Fin 8 → ℂ, |(star p ⬝ᵥ W₀ *ᵥ q).re| ≤ L * Real.sqrt (nsq p) * Real.sqrt (nsq q))
    (hker : ∀ (c : Fin 3) (a : Fin 2 → ℂ), nsq a = 1 → ∀ u : Fin 4 → ℂ,
      K *ᵥ (cutEmb c a *ᵥ u) = 0 →
        α * nsq u ≤ (star (cutEmb c a *ᵥ u) ⬝ᵥ W₀ *ᵥ (cutEmb c a *ᵥ u)).re)
    (hperp : ∀ (c : Fin 3) (a : Fin 2 → ℂ), nsq a = 1 → ∀ v : Fin 4 → ℂ,
      (∀ u, K *ᵥ (cutEmb c a *ᵥ u) = 0 → star u ⬝ᵥ v = 0) →
        μ * nsq v ≤ nsq (K *ᵥ (cutEmb c a *ᵥ v)))
    {x : Fin 8 → ℂ} (hx : IsCutProduct x) :
    0 ≤ (star x ⬝ᵥ (W₀ + (lam : ℂ) • (Kᴴ * K)) *ᵥ x).re := by
  obtain ⟨c, a, b, rfl⟩ := exists_cutEmb hx
  by_cases h0 : nsq a = 0
  · have : a = 0 := eq_zero_of_nsq_eq_zero h0
    subst this
    have : cutEmb c 0 = 0 := by ext i k; simp [cutEmb]
    simp [this]
  · have hpos : 0 < nsq a := lt_of_le_of_ne (nsq_nonneg a) (Ne.symm h0)
    set r : ℝ := Real.sqrt (nsq a) with hr
    have hrpos : 0 < r := Real.sqrt_pos.2 hpos
    have hr2 : r ^ 2 = nsq a := Real.sq_sqrt hpos.le
    set a' : Fin 2 → ℂ := ((r⁻¹ : ℝ) : ℂ) • a with ha'
    have hna' : nsq a' = 1 := by
      rw [ha', nsq_real_smul, ← hr2]; field_simp
    have hJ : cutEmb c a = (r : ℂ) • cutEmb c a' := by
      rw [ha', cutEmb_smul, smul_smul]
      have : (r : ℂ) * ((r⁻¹ : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul]; rw [mul_inv_cancel₀ hrpos.ne']; simp
      rw [this, one_smul]
    have key := kernel_quant_matrix W₀ K (cutEmb c a') (cutEmb_isometry c hna') hW hα hL0 hμ hlam hL
      (hker c a' hna') (hperp c a' hna') b
    rw [hJ, Matrix.smul_mulVec]
    set y := cutEmb c a' *ᵥ b
    have e : (star ((r : ℂ) • y) ⬝ᵥ (W₀ + (lam : ℂ) • (Kᴴ * K)) *ᵥ ((r : ℂ) • y)).re =
        r ^ 2 * (star y ⬝ᵥ (W₀ + (lam : ℂ) • (Kᴴ * K)) *ᵥ y).re := by
      rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul]
      simp only [smul_eq_mul]
      have : star (r : ℂ) * (r * (star y ⬝ᵥ (W₀ + (lam : ℂ) • (Kᴴ * K)) *ᵥ y)) =
          ((r ^ 2 : ℝ) : ℂ) * (star y ⬝ᵥ (W₀ + (lam : ℂ) • (Kᴴ * K)) *ᵥ y) := by
        simp [Complex.star_def, pow_two, mul_assoc]
      rw [this, Complex.re_ofReal_mul]
    rw [e]
    exact mul_nonneg (sq_nonneg r) key

/-- info: 'FormalResearch.PPTThreeQubit.kernel_quant_cutProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kernel_quant_cutProduct

/-- `‖W₀‖∞ ≤ L` in the form `|⟨p, W₀ q⟩| ≤ L‖p‖‖q‖` gives `-L ≤ W₀ ≤ L`. -/
theorem psd_of_bound {W₀ : Matrix (Fin 8) (Fin 8) ℂ} (hW : W₀.IsHermitian) {L : ℝ}
    (hL : ∀ p q : Fin 8 → ℂ, |(star p ⬝ᵥ W₀ *ᵥ q).re| ≤ L * Real.sqrt (nsq p) * Real.sqrt (nsq q)) :
    (W₀ + (L : ℂ) • (1 : Matrix (Fin 8) (Fin 8) ℂ)).PosSemidef ∧
      ((L : ℂ) • (1 : Matrix (Fin 8) (Fin 8) ℂ) - W₀).PosSemidef := by
  have hLh : ((L : ℂ) • (1 : Matrix (Fin 8) (Fin 8) ℂ)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_smul, conjTranspose_one]; simp
  have hsq : ∀ x : Fin 8 → ℂ, Real.sqrt (nsq x) * Real.sqrt (nsq x) = nsq x := fun x =>
    Real.mul_self_sqrt (nsq_nonneg x)
  have hx : ∀ x : Fin 8 → ℂ, star x ⬝ᵥ ((L : ℂ) • (1 : Matrix (Fin 8) (Fin 8) ℂ)) *ᵥ x =
      ((L * nsq x : ℝ) : ℂ) := by
    intro x
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, star_dotProduct_self_real' x]
    simp
  refine ⟨Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨hW.add hLh, fun x => ?_⟩,
    Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨hLh.sub hW, fun x => ?_⟩⟩
  · rw [Matrix.add_mulVec, dotProduct_add, hx]
    have him := hW.im_star_dotProduct_mulVec_self x
    have h := (abs_le.mp (hL x x)).1
    rw [mul_assoc, hsq] at h
    refine Complex.nonneg_iff.2 ⟨?_, ?_⟩
    · simp only [Complex.add_re, Complex.ofReal_re]; linarith
    · simp only [Complex.add_im, Complex.ofReal_im]; simpa using him.symm
  · rw [Matrix.sub_mulVec, dotProduct_sub, hx]
    have him := hW.im_star_dotProduct_mulVec_self x
    have h := (abs_le.mp (hL x x)).2
    rw [mul_assoc, hsq] at h
    refine Complex.nonneg_iff.2 ⟨?_, ?_⟩
    · simp only [Complex.sub_re, Complex.ofReal_re]; linarith
    · simp only [Complex.sub_im, Complex.ofReal_im]; simpa using him

/-- The expectation of a biseparable operator against a non-negative-on-cut-products witness is
non-negative. -/
theorem trace_mul_nonneg_of_biseparable {W σ : Matrix (Fin 8) (Fin 8) ℂ}
    (hW : ∀ x, IsCutProduct x → 0 ≤ (star x ⬝ᵥ W *ᵥ x).re) (hσ : IsBiseparable σ) :
    0 ≤ (W * σ).trace.re := by
  obtain ⟨n, φ, hφ, rfl⟩ := hσ
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
  exact hW _ (hφ i)

theorem isHermitian_of_biseparable {σ : Matrix (Fin 8) (Fin 8) ℂ} (hσ : IsBiseparable σ) :
    σ.IsHermitian := by
  obtain ⟨n, φ, -, rfl⟩ := hσ
  unfold Matrix.IsHermitian
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjTranspose_vecMulVec, star_star]

/-- **`prop:ppt3-kernel-quant`, distance bound `eq:ppt3-dist-lift`.**  Under the hypotheses of
`kernel_quant_cutProduct`, with additionally `KᴴK ≤ β`, a density matrix `ρ` with `Kρ = 0` and
`tr(W₀ρ) = -g`, the distance to the biseparable states satisfies `D(ρ, BS) ≥ g/(2L + λβ)`. -/
theorem kernel_quant_distance {ν : Type*} [Fintype ν] [DecidableEq ν]
    (W₀ : Matrix (Fin 8) (Fin 8) ℂ) (K : Matrix ν (Fin 8) ℂ) (hW : W₀.IsHermitian)
    {α L μ lam β g : ℝ} (hα : 0 < α) (hL0 : 0 ≤ L) (hμ : 0 < μ) (hlam : lam = (L + L ^ 2 / α) / μ)
    (hL : ∀ p q : Fin 8 → ℂ, |(star p ⬝ᵥ W₀ *ᵥ q).re| ≤ L * Real.sqrt (nsq p) * Real.sqrt (nsq q))
    (hker : ∀ (c : Fin 3) (a : Fin 2 → ℂ), nsq a = 1 → ∀ u : Fin 4 → ℂ,
      K *ᵥ (cutEmb c a *ᵥ u) = 0 →
        α * nsq u ≤ (star (cutEmb c a *ᵥ u) ⬝ᵥ W₀ *ᵥ (cutEmb c a *ᵥ u)).re)
    (hperp : ∀ (c : Fin 3) (a : Fin 2 → ℂ), nsq a = 1 → ∀ v : Fin 4 → ℂ,
      (∀ u, K *ᵥ (cutEmb c a *ᵥ u) = 0 → star u ⬝ᵥ v = 0) →
        μ * nsq v ≤ nsq (K *ᵥ (cutEmb c a *ᵥ v)))
    (hβ : 0 ≤ β) (hK : ((β : ℂ) • (1 : Matrix (Fin 8) (Fin 8) ℂ) - Kᴴ * K).PosSemidef)
    (hLβ : 0 < 2 * L + lam * β)
    {ρ : Matrix (Fin 8) (Fin 8) ℂ} (hρ : ρ.IsHermitian) (hρt : ρ.trace.re = 1) (hKρ : K * ρ = 0)
    (hρW : (W₀ * ρ).trace.re = -g) :
    g / (2 * L + lam * β) ≤ bsDist ρ := by
  have hlam0 : 0 ≤ lam := by rw [hlam]; positivity
  obtain ⟨hlo, hhi⟩ := psd_of_bound hW hL
  refine le_bsDist fun σ hσ hσt => ?_
  have hnn := fun x (hx : IsCutProduct x) =>
    kernel_quant_cutProduct W₀ K hW hα hL0 hμ hlam hL hker hperp hx
  have hσW := trace_mul_nonneg_of_biseparable hnn hσ
  have hρW' : ((W₀ + (lam : ℂ) • (Kᴴ * K)) * ρ).trace.re = -g := by
    rw [Matrix.add_mul, Matrix.trace_add, Complex.add_re, Matrix.smul_mul, Matrix.mul_assoc,
      hKρ, Matrix.mul_zero, smul_zero, Matrix.trace_zero, Complex.zero_re, add_zero, hρW]
  have := kernel_lift_distance (K := K) hL0 hlam0 hβ hLβ hlo hhi hK hρ (isHermitian_of_biseparable hσ)
    hρt (by rw [hσt]; simp) hρW' hσW
  exact this

/-- info: 'FormalResearch.PPTThreeQubit.kernel_quant_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kernel_quant_distance

end

end FormalResearch.PPTThreeQubit
