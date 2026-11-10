module

public import Mathlib
public import FormalResearch.PPTThreeQubit.PartialTranspose

/-!
# The supported-face extremality criterion

Source: `QI/hidden_entanglement/ppt_three_qubit/appendix_family.tex` (proof of `cor:ppt3-extreme6`)
and `appendix_surface.tex` (proof of `cor:ppt3-extreme5`), where extremality in the set of
fully-PPT states is decided by the supported-face criterion of Garberg--Irgens--Myrheim.

For a finite index type `ι`, a finite family of cuts `T c : Matrix ι ι ℂ →ₗ[ℝ] Matrix ι ι ℂ`
(for three qubits the three partial transposes) and `σ` a state with all `T c σ` positive
semidefinite, a *face direction* at `σ` is a Hermitian `D` with `ker σ ⊆ ker D` and
`ker (T c σ) ⊆ ker (T c D)` for every cut `c`.

* `mem_extremePoints_of_faceDirection`: if every face direction is a multiple of `σ`, then `σ` is an
  extreme point of the set `fullyPPT T` of unit-trace `ρ ≥ 0` with all `T c ρ ≥ 0`.
* `exists_posSemidef_add_smul`: a face direction can be added to `σ` with either sign, with a small
  coefficient, without leaving the cone (the converse input).
* `isFaceDirection_of_mem_extremePoints`, `mem_extremePoints_iff_faceDirection`: the converse, so
  that extremality is equivalent to the face-direction space being `ℝ σ` (when every `T c` preserves
  Hermiticity).
* `mem_extremePoints_of_sandwich`: the form used in the paper: for `σ = B X B†` with `B` injective,
  if the only Hermitian `Y` with `T c (B Y B†) k = 0` for the kernel vectors `k` of each `T c σ`
  are the multiples of `X`, then `σ` is extreme.
-/

@[expose] public section

namespace FormalResearch.PPTThreeQubit

open Matrix
open scoped ComplexOrder

noncomputable section

namespace ExtremeCriterion

set_option linter.unusedSectionVars false

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- The set of unit-trace operators that are positive semidefinite and stay so under every cut map
`T c` (for three qubits: the fully-PPT states). -/
def fullyPPT (T : κ → Matrix ι ι ℂ →ₗ[ℝ] Matrix ι ι ℂ) : Set (Matrix ι ι ℂ) :=
  {ρ | ρ.PosSemidef ∧ ρ.trace = 1 ∧ ∀ c, (T c ρ).PosSemidef}

/-- A face direction at `σ`: a Hermitian `D` with `ran D ⊆ ran σ` (as `ker σ ⊆ ker D`) and
`ker (T c σ) ⊆ ker (T c D)` for every cut `c`. -/
def IsFaceDirection (T : κ → Matrix ι ι ℂ →ₗ[ℝ] Matrix ι ι ℂ) (σ D : Matrix ι ι ℂ) : Prop :=
  D.IsHermitian ∧ (∀ k, σ *ᵥ k = 0 → D *ᵥ k = 0) ∧
    ∀ c k, (T c σ) *ᵥ k = 0 → (T c D) *ᵥ k = 0

theorem mulVec_eq_zero_of_add {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {k : ι → ℂ} (h : (A + B) *ᵥ k = 0) : A *ᵥ k = 0 := by
  have h0 : star k ⬝ᵥ (A + B) *ᵥ k = 0 := by rw [h]; simp
  rw [add_mulVec, dotProduct_add] at h0
  have h1 := hA.dotProduct_mulVec_nonneg k
  have h2 := hB.dotProduct_mulVec_nonneg k
  have : star k ⬝ᵥ A *ᵥ k = 0 := le_antisymm (by rw [← h0]; exact le_add_of_nonneg_right h2) h1
  exact (hA.dotProduct_mulVec_zero_iff).mp this

theorem mulVec_eq_zero_of_convex {A B σ : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hσ : a • A + b • B = σ) {k : ι → ℂ}
    (hk : σ *ᵥ k = 0) : A *ᵥ k = 0 := by
  have h := mulVec_eq_zero_of_add (hA.smul ha.le) (hB.smul hb.le) (k := k) (hσ ▸ hk)
  have h' : ((a : ℂ) • A) *ᵥ k = 0 := by
    simpa [Complex.coe_smul] using h
  rw [smul_mulVec] at h'
  exact (smul_eq_zero.mp h').resolve_left (by exact_mod_cast ha.ne')

/-- If every face direction is a multiple of `σ`, then `σ` is extreme. -/
theorem mem_extremePoints_of_faceDirection (T : κ → Matrix ι ι ℂ →ₗ[ℝ] Matrix ι ι ℂ)
    {σ : Matrix ι ι ℂ} (hσ : σ ∈ fullyPPT T)
    (h : ∀ D, IsFaceDirection T σ D → ∃ a : ℂ, D = a • σ) :
    σ ∈ (fullyPPT T).extremePoints ℝ := by
  have key : ∀ ⦃x y : Matrix ι ι ℂ⦄, x ∈ fullyPPT T → y ∈ fullyPPT T → ∀ {a b : ℝ}, 0 < a → 0 < b →
      a • x + b • y = σ → x = σ := by
    intro x y hx hy a b ha hb hab
    have hD : IsFaceDirection T σ (x - σ) := by
      refine ⟨hx.1.isHermitian.sub hσ.1.isHermitian, ?_, ?_⟩
      · intro k hk
        rw [sub_mulVec, hk, mulVec_eq_zero_of_convex hx.1 hy.1 ha hb hab hk, sub_zero]
      · intro c k hk
        have hTσ : a • T c x + b • T c y = T c σ := by rw [← hab, map_add, map_smul, map_smul]
        rw [map_sub, sub_mulVec, hk, mulVec_eq_zero_of_convex (hx.2.2 c) (hy.2.2 c) ha hb hTσ hk,
          sub_zero]
    obtain ⟨a₀, ha₀⟩ := h (x - σ) hD
    · have htr : x.trace = 1 := hx.2.1
      have : (1 : ℂ) = (1 + a₀) * 1 := by
        have := congrArg Matrix.trace (show x = (1 + a₀) • σ by
          rw [add_smul, one_smul, ← ha₀]; abel)
        rw [trace_smul, hσ.2.1, htr] at this
        simpa using this
      have ha0 : a₀ = 0 := by linear_combination -this
      rw [ha0, zero_smul] at ha₀
      exact sub_eq_zero.mp ha₀
  refine ⟨hσ, ?_⟩
  rintro x hx y hy ⟨a, b, ha, hb, hab, hxy⟩
  exact key hx hy ha hb hxy

/-- The real quadratic form `x ↦ Re (x† M x)`. -/
def qf (M : Matrix ι ι ℂ) (x : ι → ℂ) : ℝ := (star x ⬝ᵥ M *ᵥ x).re

theorem qf_continuous (M : Matrix ι ι ℂ) : Continuous (qf M) := by
  unfold qf
  simp only [dotProduct, mulVec, Pi.star_apply]
  fun_prop

theorem qf_smul (M : Matrix ι ι ℂ) (r : ℝ) (x : ι → ℂ) : qf M (r • x) = r ^ 2 * qf M x := by
  unfold qf
  have : star (r • x) ⬝ᵥ M *ᵥ (r • x) = ((r : ℂ) ^ 2) * (star x ⬝ᵥ M *ᵥ x) := by
    rw [show (r • x) = (r : ℂ) • x from (Complex.coe_smul r x).symm, star_smul, mulVec_smul,
      smul_dotProduct, dotProduct_smul]
    simp [Complex.conj_ofReal]
    ring
  rw [this]
  simp [pow_two, Complex.mul_re]

theorem qf_add_ker {M : Matrix ι ι ℂ} (hM : M.IsHermitian) {v : ι → ℂ} (hv : M *ᵥ v = 0)
    (w : ι → ℂ) : qf M (v + w) = qf M w := by
  unfold qf
  have h1 : star v ⬝ᵥ M *ᵥ w = 0 := by
    rw [dotProduct_mulVec]
    have : star v ᵥ* M = 0 := by
      have := star_mulVec M v
      rw [hM.eq, hv] at this
      simpa using this.symm
    rw [this]; simp
  rw [star_add, mulVec_add, hv, zero_add, add_dotProduct, h1]
  simp

/-- A quadratic form `qf D` is dominated by a multiple of `qf A` when `A ≥ 0` and `ker A ⊆ ker D`. -/
theorem exists_ratio_bound {A D : Matrix ι ι ℂ} (hA : A.PosSemidef) (hD : D.IsHermitian)
    (hker : ∀ k, A *ᵥ k = 0 → D *ᵥ k = 0) : ∃ C : ℝ, 0 < C ∧ ∀ x, qf D x ≤ C * qf A x := by
  obtain ⟨W, hW⟩ :=
    Submodule.exists_isCompl ((LinearMap.ker (Matrix.mulVecLin A)).restrictScalars ℝ)
  have hpos : ∀ x, 0 ≤ qf A x := fun x => by
    have := hA.dotProduct_mulVec_nonneg x
    exact (Complex.nonneg_iff.mp this).1
  have hzero : ∀ x, qf A x = 0 → A *ᵥ x = 0 := fun x hx => by
    refine (hA.dotProduct_mulVec_zero_iff).mp ?_
    have him : (star x ⬝ᵥ A *ᵥ x).im = 0 := (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg x)).2.symm
    exact Complex.ext hx him
  set S : Set (ι → ℂ) := (W : Set (ι → ℂ)) ∩ Metric.sphere 0 1 with hS
  have hSc : IsCompact S :=
    (isCompact_sphere (0 : ι → ℂ) 1).inter_left (Submodule.closed_of_finiteDimensional W)
  have hfpos : ∀ u ∈ S, qf A u ≠ 0 := by
    intro u ⟨huW, hu1⟩ h0
    have hAu := hzero u h0
    have huK : u ∈ (LinearMap.ker (Matrix.mulVecLin A)).restrictScalars ℝ := by
      simpa using hAu
    have : u = 0 := by
      have := hW.disjoint.le_bot ⟨huK, huW⟩
      simpa using this
    simp [this] at hu1
  have hcont : ContinuousOn (fun u => qf D u / qf A u) S :=
    ((qf_continuous D).continuousOn).div (qf_continuous A).continuousOn hfpos
  obtain ⟨M, hM⟩ := (hSc.bddAbove_image hcont)
  have hbound : ∀ u ∈ S, qf D u ≤ (|M| + 1) * qf A u := by
    intro u hu
    have h1 : qf D u / qf A u ≤ M := hM ⟨u, hu, rfl⟩
    have hfp : 0 < qf A u := lt_of_le_of_ne (hpos u) (Ne.symm (hfpos u hu))
    have : qf D u ≤ M * qf A u := by rwa [div_le_iff₀ hfp] at h1
    nlinarith [le_abs_self M, hfp]
  refine ⟨|M| + 1, by positivity, fun x => ?_⟩
  obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp (hW.sup_eq_top ▸ Submodule.mem_top : x ∈ _)
  have hv' : A *ᵥ v = 0 := by simpa using hv
  rw [qf_add_ker hA.isHermitian hv', qf_add_ker hD (hker v hv')]
  by_cases hw0 : w = 0
  · simp [hw0, qf]
  · have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have huS : (‖w‖⁻¹ • w) ∈ S := by
      refine ⟨Submodule.smul_mem W _ hw, ?_⟩
      simp [norm_smul, hn.ne']
    have := hbound _ huS
    rw [qf_smul, qf_smul] at this
    have hsq : 0 < (‖w‖⁻¹) ^ 2 := by positivity
    have := (mul_le_mul_iff_of_pos_left hsq).mp (by linarith : (‖w‖⁻¹) ^ 2 * qf D w ≤
      (‖w‖⁻¹) ^ 2 * ((|M| + 1) * qf A w))
    exact this

theorem qf_add_smul (A D : Matrix ι ι ℂ) (t : ℝ) (x : ι → ℂ) :
    qf (A + t • D) x = qf A x + t * qf D x := by
  unfold qf
  rw [add_mulVec, dotProduct_add, Complex.add_re, show t • D = (t : ℂ) • D from
    (Complex.coe_smul t D).symm, smul_mulVec, dotProduct_smul]
  simp

theorem qf_neg (D : Matrix ι ι ℂ) (x : ι → ℂ) : qf (-D) x = - qf D x := by
  simp [qf, neg_mulVec, dotProduct_neg]

theorem isHermitian_add_smul {A D : Matrix ι ι ℂ} (hA : A.IsHermitian) (hD : D.IsHermitian)
    (t : ℝ) : (A + t • D).IsHermitian := by
  show (A + t • D)ᴴ = A + t • D
  rw [conjTranspose_add, conjTranspose_smul, hA.eq, hD.eq]
  simp

/-- A face direction can be added to `A` with either sign and a small coefficient. -/
theorem exists_posSemidef_add_smul {A D : Matrix ι ι ℂ} (hA : A.PosSemidef) (hD : D.IsHermitian)
    (hker : ∀ k, A *ᵥ k = 0 → D *ᵥ k = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, |t| * C ≤ 1 → (A + t • D).PosSemidef := by
  obtain ⟨C₁, h₁, b₁⟩ := exists_ratio_bound hA hD hker
  obtain ⟨C₂, h₂, b₂⟩ := exists_ratio_bound hA (hD.neg)
    (fun k hk => by simp [neg_mulVec, hker k hk])
  have hpos : ∀ x, 0 ≤ qf A x := fun x =>
    (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg x)).1
  refine ⟨max C₁ C₂, lt_max_of_lt_left h₁, fun t ht => ?_⟩
  refine PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_add_smul hA.isHermitian hD t)
    fun x => ?_
  have him := (isHermitian_add_smul hA.isHermitian hD t).im_star_dotProduct_mulVec_self x
  refine Complex.nonneg_iff.mpr ⟨?_, by simpa using him.symm⟩
  show 0 ≤ qf (A + t • D) x
  rw [qf_add_smul]
  have hx := hpos x
  have e1 := b₁ x
  have e2 := b₂ x
  rw [qf_neg] at e2
  have hm1 : C₁ ≤ max C₁ C₂ := le_max_left _ _
  have hm2 : C₂ ≤ max C₁ C₂ := le_max_right _ _
  rcases le_total 0 t with h0 | h0
  · rw [abs_of_nonneg h0] at ht
    have : t * C₂ ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hm2 h0) ht
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr e2), mul_nonneg hx (sub_nonneg.mpr this)]
  · rw [abs_of_nonpos h0] at ht
    have : -t * C₁ ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hm1 (by linarith)) ht
    nlinarith [mul_nonneg (neg_nonneg.mpr h0) (sub_nonneg.mpr e1), mul_nonneg hx (sub_nonneg.mpr this)]

theorem trace_im_eq_zero {D : Matrix ι ι ℂ} (hD : D.IsHermitian) : D.trace.im = 0 := by
  simp only [Matrix.trace, Complex.im_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  have := hD.apply i i
  simpa [Complex.conj_eq_iff_im] using this

/-- **Converse of `mem_extremePoints_of_faceDirection`.**  If `σ` is an extreme point of the
fully-PPT set (every cut map preserving Hermiticity), every face direction at `σ` is a real
multiple of `σ`. -/
theorem eq_smul_of_isFaceDirection (T : κ → Matrix ι ι ℂ →ₗ[ℝ] Matrix ι ι ℂ)
    (hT : ∀ c ρ, ρ.IsHermitian → (T c ρ).IsHermitian) {σ : Matrix ι ι ℂ}
    (hσ : σ ∈ (fullyPPT T).extremePoints ℝ) {D : Matrix ι ι ℂ} (hD : IsFaceDirection T σ D) :
    ∃ r : ℝ, D = r • σ := by
  obtain ⟨hσC, hext⟩ := hσ
  set r : ℝ := D.trace.re with hr
  set D' : Matrix ι ι ℂ := D - r • σ with hD'
  have hD'h : D'.IsHermitian := by
    have : (r • σ).IsHermitian := by
      show (r • σ)ᴴ = r • σ
      rw [conjTranspose_smul, hσC.1.isHermitian.eq]
      simp
    exact hD.1.sub this
  have hD'k : ∀ k, σ *ᵥ k = 0 → D' *ᵥ k = 0 := by
    intro k hk
    rw [hD', sub_mulVec, hD.2.1 k hk, show r • σ = (r : ℂ) • σ from (Complex.coe_smul r σ).symm,
      smul_mulVec, hk]
    simp
  have hD'c : ∀ c k, (T c σ) *ᵥ k = 0 → (T c D') *ᵥ k = 0 := by
    intro c k hk
    rw [hD', map_sub, map_smul, sub_mulVec,
      show r • T c σ = (r : ℂ) • T c σ from (Complex.coe_smul r _).symm, smul_mulVec, hk,
      hD.2.2 c k hk]
    simp
  have hD'tr : D'.trace = 0 := by
    rw [hD', trace_sub, trace_smul, hσC.2.1]
    apply Complex.ext
    · simp [hr]
    · simp [trace_im_eq_zero hD.1]
  obtain ⟨C₀, h₀, hC₀⟩ := exists_posSemidef_add_smul hσC.1 hD'h hD'k
  choose Cc hCc hCcm using fun c => exists_posSemidef_add_smul (hσC.2.2 c)
    (hT c D' hD'h) (hD'c c) (A := T c σ) (D := T c D') |>.imp fun _ h => h
  set total : ℝ := C₀ + ∑ c, Cc c with htot
  have htot_pos : 0 < total := by
    have : 0 ≤ ∑ c, Cc c := Finset.sum_nonneg fun c _ => (hCc c).le
    linarith
  set ε : ℝ := 1 / total with hε
  have hεpos : 0 < ε := by positivity
  have hmem : ∀ s : ℝ, |s| = ε → σ + s • D' ∈ fullyPPT T := by
    intro s hs
    have hle : ∀ C, 0 < C → C ≤ total → |s| * C ≤ 1 := by
      intro C hC hCt
      rw [hs, hε]
      rw [one_div, inv_mul_le_iff₀ htot_pos]; linarith
    refine ⟨hC₀ s (hle C₀ h₀ (by
      have : 0 ≤ ∑ c, Cc c := Finset.sum_nonneg fun c _ => (hCc c).le
      linarith)), ?_, fun c => ?_⟩
    · rw [trace_add, trace_smul, hD'tr, hσC.2.1]; simp
    · rw [map_add, map_smul]
      exact hCcm c s (hle (Cc c) (hCc c) (by
        have := Finset.single_le_sum (f := Cc) (fun c _ => (hCc c).le) (Finset.mem_univ c)
        linarith))
  have hplus := hmem ε (abs_of_pos hεpos)
  have hminus := hmem (-ε) (by rw [abs_neg, abs_of_pos hεpos])
  have hseg : σ ∈ openSegment ℝ (σ + ε • D') (σ + (-ε) • D') := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i j
    simp
    ring
  have := hext hplus hminus hseg
  have h0 : ε • D' = 0 := by simpa using this
  have : D' = 0 := by
    rcases smul_eq_zero.mp h0 with h | h
    · exact absurd h hεpos.ne'
    · exact h
  exact ⟨r, sub_eq_zero.mp this⟩

/-- **The supported-face criterion** (`[GIM]` as used in `cor:ppt3-extreme5` and
`cor:ppt3-extreme6`).  For `σ` in the fully-PPT set (every cut map real-linear and
Hermiticity-preserving), `σ` is extreme iff every face direction is a multiple of `σ`. -/
theorem mem_extremePoints_iff_faceDirection (T : κ → Matrix ι ι ℂ →ₗ[ℝ] Matrix ι ι ℂ)
    (hT : ∀ c ρ, ρ.IsHermitian → (T c ρ).IsHermitian) {σ : Matrix ι ι ℂ}
    (hσ : σ ∈ fullyPPT T) :
    σ ∈ (fullyPPT T).extremePoints ℝ ↔ ∀ D, IsFaceDirection T σ D → ∃ a : ℂ, D = a • σ :=
  ⟨fun h D hD => by
    obtain ⟨r, hr⟩ := eq_smul_of_isFaceDirection T hT h hD
    exact ⟨r, by rw [hr, Complex.coe_smul]⟩, mem_extremePoints_of_faceDirection T hσ⟩

section Sandwich

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- If `ker B† ⊆ ker D` with `D` Hermitian and `B` injective, then `D = B Y B†` with `Y` Hermitian. -/
theorem exists_sandwich_of_ker {B : Matrix ι m ℂ} (hB : Function.Injective B.mulVec)
    {D : Matrix ι ι ℂ} (hD : D.IsHermitian) (hker : ∀ k, Bᴴ *ᵥ k = 0 → D *ᵥ k = 0) :
    ∃ Y : Matrix m m ℂ, Y.IsHermitian ∧ D = B * Y * Bᴴ := by
  have hG : (Bᴴ * B).PosDef := Matrix.PosDef.conjTranspose_mul_self B hB
  have hdet : IsUnit (Bᴴ * B).det := (Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit
  set G : Matrix m m ℂ := Bᴴ * B with hGdef
  have hGh : G.IsHermitian := hG.isHermitian
  have h1 : Bᴴ * (1 - B * G⁻¹ * Bᴴ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hGdef,
      Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul, sub_self]
  have h2 : D * (1 - B * G⁻¹ * Bᴴ) = 0 := by
    ext i j
    have hv : Bᴴ *ᵥ ((1 - B * G⁻¹ * Bᴴ) *ᵥ Pi.single j 1) = 0 := by
      rw [mulVec_mulVec, h1, zero_mulVec]
    have := hker _ hv
    rw [mulVec_mulVec] at this
    have e := congrFun this i
    simp only [mulVec_single_one, Pi.zero_apply] at e
    simpa using e
  have h3 : D = D * (B * G⁻¹ * Bᴴ) := by
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h2; exact h2
  have hP : (B * G⁻¹ * Bᴴ).IsHermitian := by
    show (B * G⁻¹ * Bᴴ)ᴴ = B * G⁻¹ * Bᴴ
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hGh.inv.eq,
      Matrix.mul_assoc]
  have h4 : D = (B * G⁻¹ * Bᴴ) * D := by
    conv_lhs => rw [← hD.eq, h3]
    rw [conjTranspose_mul, hD.eq, hP.eq]
  refine ⟨G⁻¹ * Bᴴ * D * B * G⁻¹, ?_, ?_⟩
  · show (G⁻¹ * Bᴴ * D * B * G⁻¹)ᴴ = _
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hD.eq, hGh.inv.eq]
    simp only [Matrix.mul_assoc]
  · conv_lhs => rw [h4]; rw [h3]
    simp only [Matrix.mul_assoc]

/-- **The criterion in the form used in the paper.**  Let `σ = B X B†` with `B` injective (its
columns span `ran σ`), and let `S c` be vectors in `ker (T c σ)`.  If the only Hermitian `Y` with
`(T c (B Y B†)) k = 0` for all `c` and `k ∈ S c` are the multiples of `X`, then `σ` is extreme. -/
theorem mem_extremePoints_of_sandwich (T : κ → Matrix ι ι ℂ →ₗ[ℝ] Matrix ι ι ℂ)
    {σ : Matrix ι ι ℂ} (hσ : σ ∈ fullyPPT T) (B : Matrix ι m ℂ) (X : Matrix m m ℂ)
    (hσB : σ = B * X * Bᴴ) (hB : Function.Injective B.mulVec)
    (S : κ → Set (ι → ℂ)) (hS : ∀ c, ∀ k ∈ S c, (T c σ) *ᵥ k = 0)
    (hnull : ∀ Y : Matrix m m ℂ, Y.IsHermitian →
      (∀ c, ∀ k ∈ S c, (T c (B * Y * Bᴴ)) *ᵥ k = 0) → ∃ a : ℂ, Y = a • X) :
    σ ∈ (fullyPPT T).extremePoints ℝ := by
  refine mem_extremePoints_of_faceDirection T hσ fun D hD => ?_
  obtain ⟨Y, hY, hDY⟩ := exists_sandwich_of_ker hB hD.1 (fun k hk => by
    apply hD.2.1
    rw [hσB, Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, hk]; simp)
  obtain ⟨a, ha⟩ := hnull Y hY (fun c k hk => by rw [← hDY]; exact hD.2.2 c k (hS c k hk))
  exact ⟨a, by rw [hDY, ha, hσB]; simp [Matrix.mul_smul, Matrix.smul_mul]⟩

end Sandwich

/-! ### Three qubits -/

/-- The three single-qubit partial transposes `T_A, T_B, T_C` as real-linear maps. -/
def cutPT : Fin 3 → Matrix (Fin 8) (Fin 8) ℂ →ₗ[ℝ] Matrix (Fin 8) (Fin 8) ℂ :=
  ![{ toFun := ptA, map_add' := fun _ _ => by ext; rfl, map_smul' := fun _ _ => by ext; rfl },
    { toFun := ptB, map_add' := fun _ _ => by ext; rfl, map_smul' := fun _ _ => by ext; rfl },
    { toFun := ptC, map_add' := fun _ _ => by ext; rfl, map_smul' := fun _ _ => by ext; rfl }]

/-- The set of three-qubit fully-PPT states: `ρ ≥ 0`, `tr ρ = 1`, `ρ^{T_c} ≥ 0` for `c = A, B, C`. -/
def fullyPPT3 : Set (Matrix (Fin 8) (Fin 8) ℂ) := fullyPPT cutPT

theorem mem_fullyPPT3_iff (ρ : Matrix (Fin 8) (Fin 8) ℂ) :
    ρ ∈ fullyPPT3 ↔
      ρ.PosSemidef ∧ ρ.trace = 1 ∧ (ptA ρ).PosSemidef ∧ (ptB ρ).PosSemidef ∧ (ptC ρ).PosSemidef := by
  unfold fullyPPT3 fullyPPT
  simp only [Set.mem_ofPred_eq, Fin.forall_fin_succ, Fin.isValue]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, -⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, h5, fun i => i.elim0⟩

theorem cutPT_isHermitian (c : Fin 3) (ρ : Matrix (Fin 8) (Fin 8) ℂ) (h : ρ.IsHermitian) :
    (cutPT c ρ).IsHermitian := by
  fin_cases c
  · show (ptA ρ)ᴴ = ptA ρ
    ext i j
    have := congrFun (congrFun h.eq (⟨4 * (j.val / 4) + i.val % 4, by omega⟩ : Fin 8))
      (⟨4 * (i.val / 4) + j.val % 4, by omega⟩ : Fin 8)
    simpa [ptA, conjTranspose_apply] using this
  · show (ptB ρ)ᴴ = ptB ρ
    ext i j
    have := congrFun (congrFun h.eq
      (⟨4 * (i.val / 4) + 2 * (j.val / 2 % 2) + i.val % 2, by omega⟩ : Fin 8))
      (⟨4 * (j.val / 4) + 2 * (i.val / 2 % 2) + j.val % 2, by omega⟩ : Fin 8)
    simpa [ptB, conjTranspose_apply] using this
  · show (ptC ρ)ᴴ = ptC ρ
    ext i j
    have := congrFun (congrFun h.eq (⟨2 * (i.val / 2) + j.val % 2, by omega⟩ : Fin 8))
      (⟨2 * (j.val / 2) + i.val % 2, by omega⟩ : Fin 8)
    simpa [ptC, conjTranspose_apply] using this

/-- **Supported-face criterion for three qubits.**  A fully-PPT three-qubit state `σ` is an extreme
point of the fully-PPT set iff every Hermitian `D` with `ker σ ⊆ ker D` and
`ker σ^{T_c} ⊆ ker D^{T_c}` (`c = A, B, C`) is a multiple of `σ`. -/
theorem ppt3_extreme_iff {σ : Matrix (Fin 8) (Fin 8) ℂ} (hσ : σ ∈ fullyPPT3) :
    σ ∈ fullyPPT3.extremePoints ℝ ↔
      ∀ D : Matrix (Fin 8) (Fin 8) ℂ, D.IsHermitian → (∀ k, σ *ᵥ k = 0 → D *ᵥ k = 0) →
        (∀ k, (ptA σ) *ᵥ k = 0 → (ptA D) *ᵥ k = 0) →
        (∀ k, (ptB σ) *ᵥ k = 0 → (ptB D) *ᵥ k = 0) →
        (∀ k, (ptC σ) *ᵥ k = 0 → (ptC D) *ᵥ k = 0) → ∃ a : ℂ, D = a • σ := by
  rw [fullyPPT3, mem_extremePoints_iff_faceDirection cutPT cutPT_isHermitian hσ]
  constructor
  · intro h D hD h0 hA hB hC
    refine h D ⟨hD, h0, fun c => ?_⟩
    fin_cases c
    · exact hA
    · exact hB
    · exact hC
  · intro h D ⟨hD, h0, hc⟩
    exact h D hD h0 (hc 0) (hc 1) (hc 2)

/-- `[GIM]` for three qubits in the form used for `cor:ppt3-extreme6` and `cor:ppt3-extreme5`:
`σ = B X B†` with `B : 8 × m` injective; `S_A, S_B, S_C` vectors in the kernels of the three partial
transposes of `σ`.  If the only Hermitian `Y` with `(B Y B†)^{T_c} k = 0` for `k ∈ S_c`
(`c = A, B, C`) are multiples of `X`, then `σ` is an extreme fully-PPT state. -/
theorem ppt3_extreme_of_sandwich {m : Type*} [Fintype m] [DecidableEq m]
    {σ : Matrix (Fin 8) (Fin 8) ℂ} (hσ : σ ∈ fullyPPT3) (B : Matrix (Fin 8) m ℂ)
    (X : Matrix m m ℂ) (hσB : σ = B * X * Bᴴ) (hB : Function.Injective B.mulVec)
    (SA SB SC : Set (Fin 8 → ℂ))
    (hSA : ∀ k ∈ SA, (ptA σ) *ᵥ k = 0) (hSB : ∀ k ∈ SB, (ptB σ) *ᵥ k = 0)
    (hSC : ∀ k ∈ SC, (ptC σ) *ᵥ k = 0)
    (hnull : ∀ Y : Matrix m m ℂ, Y.IsHermitian →
      (∀ k ∈ SA, (ptA (B * Y * Bᴴ)) *ᵥ k = 0) → (∀ k ∈ SB, (ptB (B * Y * Bᴴ)) *ᵥ k = 0) →
      (∀ k ∈ SC, (ptC (B * Y * Bᴴ)) *ᵥ k = 0) → ∃ a : ℂ, Y = a • X) :
    σ ∈ fullyPPT3.extremePoints ℝ := by
  refine mem_extremePoints_of_sandwich cutPT hσ B X hσB hB ![SA, SB, SC] ?_ ?_
  · intro c; fin_cases c
    · exact hSA
    · exact hSB
    · exact hSC
  · intro Y hY h
    exact hnull Y hY (h 0) (h 1) (h 2)

end ExtremeCriterion

/-- info: 'FormalResearch.PPTThreeQubit.ExtremeCriterion.mem_extremePoints_iff_faceDirection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeCriterion.mem_extremePoints_iff_faceDirection

/-- info: 'FormalResearch.PPTThreeQubit.ExtremeCriterion.mem_extremePoints_of_sandwich' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeCriterion.mem_extremePoints_of_sandwich

/-- info: 'FormalResearch.PPTThreeQubit.ExtremeCriterion.ppt3_extreme_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeCriterion.ppt3_extreme_iff

/-- info: 'FormalResearch.PPTThreeQubit.ExtremeCriterion.ppt3_extreme_of_sandwich' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ExtremeCriterion.ppt3_extreme_of_sandwich

end

end FormalResearch.PPTThreeQubit
