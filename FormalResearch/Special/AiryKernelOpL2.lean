module

public import FormalResearch.Special.AiryKernelOpOperator

/-!
# The Airy kernel operator `K_u` on `L²(u, ∞)`: norm bound and symmetry at the level of functions

Mathlib has no Hilbert–Schmidt / integral-operator API (checked: no `HilbertSchmidt`, no integral operator
on `Lp`), and this file does **not** build `K_u` as a `ContinuousLinearMap` on `Lp ℝ 2`.  What is proved is
the function-level content of "`K_u` is a bounded self-adjoint operator on `L²(u,∞)`".  Write
`(K_u f)(x) = ∫_u^∞ K(x,y) f(y) dy` (`airyKerOp u f x`) and `μ_u = vol|_{(u,∞)}`.  For `f` measurable with
`∫_u^∞ f² < ∞`:

* `airyKerOp_sq_le`: for **every** `x`, `(K_u f)(x)² ≤ (∫_u^∞ K(x,y)² dy) · ∫_u^∞ f²` (Cauchy–Schwarz;
  `K(x,·) ∈ L²(u,∞)` for every `x` because `K(x,y)² ≤ K(x,x)K(y,y)`);
* `integral_airyKerOp_sq_le`: `K_u f ∈ L²(u,∞)` and **`‖K_u f‖² ≤ N_Ai(u)² ‖f‖²`**, `N_Ai(u) = Tr K_u`
  (Hilbert–Schmidt bound `∫∫K² ≤ N_Ai(u)²` of `AiryKernelOpOperator`);
* `airyKerForm_abs_le`, `airyKerForm_comm`: the bilinear form `B_u(g,f) = ∫_u^∞∫_u^∞ g(x) K(x,y) f(y) dy dx` is
  absolutely convergent for `g, f ∈ L²(u,∞)`, `|B_u(g,f)| ≤ N_Ai(u) ‖g‖ ‖f‖` (via `|K(x,y)| ≤ √(K(x,x)K(y,y))`,
  trace bound), and **symmetric** `B_u(g,f) = B_u(f,g)` (self-adjointness of `K_u`).

Positivity `⟨f, K_u f⟩ ≥ 0` for all `f ∈ L²` is `airyKerForm_self_nonneg` (continuity of `B_u` in `L²` plus the
existing compact-support case `airyKer_quadForm_nonneg_Ioi`).

**Not formalised:** `K_u` as an element of `Lp ℝ 2 →L[ℝ] Lp ℝ 2`, the factorisation `K_u = A_u A_u^*`,
eigenvalues/Fredholm determinant.
-/

@[expose] public section

open Filter Topology MeasureTheory Set

namespace FormalResearch.Special

/-! ### Cauchy–Schwarz on a general measure space -/

lemma airyCS {α : Type*} [MeasurableSpace α] {μ : Measure α} {g f : α → ℝ} (hg : Measurable g)
    (hf : Measurable f) (hg2 : Integrable (fun x => g x ^ 2) μ) (hf2 : Integrable (fun x => f x ^ 2) μ) :
    Integrable (fun x => g x * f x) μ ∧
      (∫ x, g x * f x ∂μ) ^ 2 ≤ (∫ x, g x ^ 2 ∂μ) * ∫ x, f x ^ 2 ∂μ := by
  have hgf : Integrable (fun x => g x * f x) μ := by
    refine Integrable.mono' ((hg2.add hf2).div_const 2) (hg.mul hf).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_le]
    simp only [Pi.add_apply]
    constructor <;> nlinarith [sq_nonneg (g x + f x), sq_nonneg (g x - f x)]
  refine ⟨hgf, ?_⟩
  have hq : ∀ t : ℝ, 0 ≤ (∫ x, g x ^ 2 ∂μ) * (t * t) + (2 * ∫ x, g x * f x ∂μ) * t +
      ∫ x, f x ^ 2 ∂μ := by
    intro t
    have h1 : Integrable (fun x => t ^ 2 * g x ^ 2) μ := hg2.const_mul _
    have h2 : Integrable (fun x => 2 * t * (g x * f x)) μ := hgf.const_mul _
    have heq : ∫ x, (t * g x + f x) ^ 2 ∂μ = (∫ x, g x ^ 2 ∂μ) * (t * t) +
        (2 * ∫ x, g x * f x ∂μ) * t + ∫ x, f x ^ 2 ∂μ := by
      have : ∀ x, (t * g x + f x) ^ 2 = (t ^ 2 * g x ^ 2 + 2 * t * (g x * f x)) + f x ^ 2 := by
        intro x; ring
      simp_rw [this]
      rw [integral_add (f := fun x => t ^ 2 * g x ^ 2 + 2 * t * (g x * f x)) (h1.add h2) hf2,
        integral_add h1 h2, integral_const_mul, integral_const_mul]
      ring
    rw [← heq]
    exact integral_nonneg fun x => sq_nonneg _
  have := discrim_le_zero hq
  unfold discrim at this
  nlinarith

/-! ### The operator and its norm bound -/

/-- `(K_u f)(x) = ∫_u^∞ K(x,y) f(y) dy`. -/
noncomputable def airyKerOp (u : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in Ioi u, airyKer x y * f y

lemma measurable_airyKer_left (x : ℝ) : Measurable (fun y => airyKer x y) :=
  measurable_airyKer.comp (measurable_const.prodMk measurable_id)

lemma integrableOn_airyKer_sq_left (u x : ℝ) :
    IntegrableOn (fun y => airyKer x y ^ 2) (Ioi u) := by
  have hd := (integrableOn_Ioi_airyKer_diag u).const_mul (airyKer x x)
  refine hd.mono' ((measurable_airyKer_left x).pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact airyKer_sq_le x y

/-- **Cauchy–Schwarz for `K_u`**: for every `x`, `(K_u f)(x)² ≤ (∫_u^∞ K(x,y)² dy) ∫_u^∞ f²`. -/
theorem airyKerOp_sq_le (u : ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (hf2 : IntegrableOn (fun y => f y ^ 2) (Ioi u)) (x : ℝ) :
    airyKerOp u f x ^ 2 ≤ (∫ y in Ioi u, airyKer x y ^ 2) * ∫ y in Ioi u, f y ^ 2 :=
  (airyCS (μ := volume.restrict (Ioi u)) (measurable_airyKer_left x) hf
    (integrableOn_airyKer_sq_left u x) hf2).2

lemma measurable_airyKerOp (u : ℝ) {f : ℝ → ℝ} (hf : Measurable f) : Measurable (airyKerOp u f) := by
  have h : Measurable (fun p : ℝ × ℝ => airyKer p.1 p.2 * f p.2) :=
    measurable_airyKer.mul (hf.comp measurable_snd)
  exact (h.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi u))).measurable

/-- **`K_u` is bounded on `L²(u,∞)` with norm `≤ N_Ai(u)`**: `K_u f` is square integrable and
`∫_u^∞ (K_u f)² ≤ N_Ai(u)² ∫_u^∞ f²`. -/
theorem integral_airyKerOp_sq_le (u : ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (hf2 : IntegrableOn (fun y => f y ^ 2) (Ioi u)) :
    IntegrableOn (fun x => airyKerOp u f x ^ 2) (Ioi u) ∧
      ∫ x in Ioi u, airyKerOp u f x ^ 2 ≤ airyN u ^ 2 * ∫ y in Ioi u, f y ^ 2 := by
  set F := ∫ y in Ioi u, f y ^ 2 with hF
  have hF0 : 0 ≤ F := integral_nonneg fun y => sq_nonneg _
  have hk : Integrable (fun x => ∫ y in Ioi u, airyKer x y ^ 2) (volume.restrict (Ioi u)) :=
    (integrable_airyKer_sq u).integral_prod_left
  have hkF : Integrable (fun x => (∫ y in Ioi u, airyKer x y ^ 2) * F) (volume.restrict (Ioi u)) :=
    hk.mul_const F
  have hle : ∀ x, airyKerOp u f x ^ 2 ≤ (∫ y in Ioi u, airyKer x y ^ 2) * F :=
    fun x => airyKerOp_sq_le u hf hf2 x
  have hint : IntegrableOn (fun x => airyKerOp u f x ^ 2) (Ioi u) :=
    hkF.mono' ((measurable_airyKerOp u hf).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hle x)
  refine ⟨hint, ?_⟩
  calc ∫ x in Ioi u, airyKerOp u f x ^ 2
      ≤ ∫ x in Ioi u, (∫ y in Ioi u, airyKer x y ^ 2) * F := integral_mono hint hkF hle
    _ = (∫ x in Ioi u, ∫ y in Ioi u, airyKer x y ^ 2) * F := integral_mul_const _ _
    _ ≤ airyN u ^ 2 * F := mul_le_mul_of_nonneg_right (integral_integral_airyKer_sq_le u) hF0

/-! ### The bilinear form: absolute convergence, bound, symmetry -/

/-- `B_u(g,f) = ∫_u^∞ ∫_u^∞ g(x) K(x,y) f(y) dy dx` (`= ⟨g, K_u f⟩`). -/
noncomputable def airyKerForm (u : ℝ) (g f : ℝ → ℝ) : ℝ :=
  ∫ x in Ioi u, ∫ y in Ioi u, g x * airyKer x y * f y

/-- `a(x) = √K(x,x)`, so that `|K(x,y)| ≤ a(x) a(y)`. -/
noncomputable def airyDiagRoot (x : ℝ) : ℝ := √(airyKer x x)

lemma measurable_airyDiagRoot : Measurable airyDiagRoot :=
  (measurable_airyKer.comp (measurable_id.prodMk measurable_id)).sqrt

lemma airyDiagRoot_sq (x : ℝ) : airyDiagRoot x ^ 2 = airyKer x x :=
  Real.sq_sqrt (airyKer_diag_nonneg x)

lemma abs_airyKer_le_root (x y : ℝ) : |airyKer x y| ≤ airyDiagRoot x * airyDiagRoot y := by
  refine abs_le_of_sq_le_sq ?_ (by unfold airyDiagRoot; positivity)
  rw [mul_pow, airyDiagRoot_sq, airyDiagRoot_sq]
  exact airyKer_sq_le x y

/-- `|g| a` is integrable on `(u,∞)` for `g ∈ L²(u,∞)`. -/
lemma integrableOn_abs_mul_root (u : ℝ) {g : ℝ → ℝ} (hg : Measurable g)
    (hg2 : IntegrableOn (fun y => g y ^ 2) (Ioi u)) :
    IntegrableOn (fun x => |g x| * airyDiagRoot x) (Ioi u) := by
  have hd := (hg2.add (integrableOn_Ioi_airyKer_diag u)).div_const 2
  refine hd.mono' (hg.abs.mul measurable_airyDiagRoot).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold airyDiagRoot; positivity)]
  have := airyDiagRoot_sq x
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (|g x| - airyDiagRoot x), sq_abs (g x)]

lemma integrable_airyKerForm (u : ℝ) {g f : ℝ → ℝ} (hg : Measurable g) (hf : Measurable f)
    (hg2 : IntegrableOn (fun y => g y ^ 2) (Ioi u)) (hf2 : IntegrableOn (fun y => f y ^ 2) (Ioi u)) :
    Integrable (fun p : ℝ × ℝ => g p.1 * airyKer p.1 p.2 * f p.2)
      ((volume.restrict (Ioi u)).prod (volume.restrict (Ioi u))) := by
  have hG := integrableOn_abs_mul_root u hg hg2
  have hF := integrableOn_abs_mul_root u hf hf2
  refine (hG.mul_prod hF).mono' ?_ (Eventually.of_forall fun p => ?_)
  · exact ((hg.comp measurable_fst).mul measurable_airyKer |>.mul (hf.comp measurable_snd)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have h := abs_airyKer_le_root p.1 p.2
    have h1 := abs_nonneg (g p.1)
    have h2 := abs_nonneg (f p.2)
    calc |g p.1| * |airyKer p.1 p.2| * |f p.2|
        ≤ |g p.1| * (airyDiagRoot p.1 * airyDiagRoot p.2) * |f p.2| := by gcongr
      _ = _ := by ring

lemma airyKerForm_eq_prod (u : ℝ) {g f : ℝ → ℝ} (hg : Measurable g) (hf : Measurable f)
    (hg2 : IntegrableOn (fun y => g y ^ 2) (Ioi u)) (hf2 : IntegrableOn (fun y => f y ^ 2) (Ioi u)) :
    airyKerForm u g f = ∫ p : ℝ × ℝ, g p.1 * airyKer p.1 p.2 * f p.2
      ∂((volume.restrict (Ioi u)).prod (volume.restrict (Ioi u))) :=
  (integral_prod _ (integrable_airyKerForm u hg hf hg2 hf2)).symm

/-- **Bound for the form**: `B_u(g,f)² ≤ N_Ai(u)² ∫g² ∫f²`. -/
theorem airyKerForm_sq_le (u : ℝ) {g f : ℝ → ℝ} (hg : Measurable g) (hf : Measurable f)
    (hg2 : IntegrableOn (fun y => g y ^ 2) (Ioi u)) (hf2 : IntegrableOn (fun y => f y ^ 2) (Ioi u)) :
    airyKerForm u g f ^ 2 ≤ airyN u ^ 2 * (∫ y in Ioi u, g y ^ 2) * ∫ y in Ioi u, f y ^ 2 := by
  have hG := integrableOn_abs_mul_root u hg hg2
  have hF := integrableOn_abs_mul_root u hf hf2
  set P := ∫ x in Ioi u, |g x| * airyDiagRoot x with hP
  set Q := ∫ x in Ioi u, |f x| * airyDiagRoot x with hQ
  have hP0 : 0 ≤ P := integral_nonneg fun x => by unfold airyDiagRoot; positivity
  have hQ0 : 0 ≤ Q := integral_nonneg fun x => by unfold airyDiagRoot; positivity
  have hB : |airyKerForm u g f| ≤ P * Q := by
    rw [airyKerForm_eq_prod u hg hf hg2 hf2, ← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hm : ∫ p : ℝ × ℝ, |g p.1| * airyDiagRoot p.1 * (|f p.2| * airyDiagRoot p.2)
        ∂((volume.restrict (Ioi u)).prod (volume.restrict (Ioi u))) = P * Q :=
      integral_prod_mul (μ := volume.restrict (Ioi u)) (ν := volume.restrict (Ioi u))
        (fun x => |g x| * airyDiagRoot x) (fun x => |f x| * airyDiagRoot x)
    rw [← hm]
    refine integral_mono (integrable_airyKerForm u hg hf hg2 hf2).norm (hG.mul_prod hF) fun p => ?_
    simp only [Real.norm_eq_abs, abs_mul]
    have h := abs_airyKer_le_root p.1 p.2
    have h1 := abs_nonneg (g p.1)
    have h2 := abs_nonneg (f p.2)
    calc |g p.1| * |airyKer p.1 p.2| * |f p.2|
        ≤ |g p.1| * (airyDiagRoot p.1 * airyDiagRoot p.2) * |f p.2| := by gcongr
      _ = _ := by ring
  have hPsq : P ^ 2 ≤ (∫ y in Ioi u, g y ^ 2) * airyN u := by
    have := (airyCS (μ := volume.restrict (Ioi u)) hg.abs measurable_airyDiagRoot
      (by simp only [sq_abs]; exact hg2 : Integrable (fun x => |g x| ^ 2) (volume.restrict (Ioi u)))
      (by simp only [airyDiagRoot_sq]; exact integrableOn_Ioi_airyKer_diag u :
        Integrable (fun x => airyDiagRoot x ^ 2) (volume.restrict (Ioi u)))).2
    simpa [sq_abs, airyDiagRoot_sq, integral_Ioi_airyKer_diag] using this
  have hQsq : Q ^ 2 ≤ (∫ y in Ioi u, f y ^ 2) * airyN u := by
    have := (airyCS (μ := volume.restrict (Ioi u)) hf.abs measurable_airyDiagRoot
      (by simp only [sq_abs]; exact hf2 : Integrable (fun x => |f x| ^ 2) (volume.restrict (Ioi u)))
      (by simp only [airyDiagRoot_sq]; exact integrableOn_Ioi_airyKer_diag u :
        Integrable (fun x => airyDiagRoot x ^ 2) (volume.restrict (Ioi u)))).2
    simpa [sq_abs, airyDiagRoot_sq, integral_Ioi_airyKer_diag] using this
  have h1 : airyKerForm u g f ^ 2 ≤ (P * Q) ^ 2 := by
    rw [← sq_abs (airyKerForm u g f)]
    exact pow_le_pow_left₀ (abs_nonneg _) hB 2
  calc airyKerForm u g f ^ 2 ≤ (P * Q) ^ 2 := h1
    _ = P ^ 2 * Q ^ 2 := by ring
    _ ≤ ((∫ y in Ioi u, g y ^ 2) * airyN u) * ((∫ y in Ioi u, f y ^ 2) * airyN u) :=
        mul_le_mul hPsq hQsq (sq_nonneg _) (mul_nonneg (integral_nonneg fun y => sq_nonneg _) (airyN_nonneg u))
    _ = _ := by ring

/-- **Self-adjointness of `K_u`**: `B_u(g,f) = B_u(f,g)`, i.e. `⟨g, K_u f⟩ = ⟨K_u g, f⟩`. -/
theorem airyKerForm_comm (u : ℝ) {g f : ℝ → ℝ} (hg : Measurable g) (hf : Measurable f)
    (hg2 : IntegrableOn (fun y => g y ^ 2) (Ioi u)) (hf2 : IntegrableOn (fun y => f y ^ 2) (Ioi u)) :
    airyKerForm u g f = airyKerForm u f g := by
  rw [airyKerForm_eq_prod u hg hf hg2 hf2, airyKerForm_eq_prod u hf hg hf2 hg2,
    ← integral_prod_swap]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [airyKer_comm p.2 p.1]; ring

/-! ### Positivity on all of `L²(u,∞)` -/

lemma airyKerForm_sub_left (u : ℝ) {g₁ g₂ f : ℝ → ℝ} (hg₁ : Measurable g₁) (hg₂ : Measurable g₂)
    (hf : Measurable f) (hg₁2 : IntegrableOn (fun y => g₁ y ^ 2) (Ioi u))
    (hg₂2 : IntegrableOn (fun y => g₂ y ^ 2) (Ioi u)) (hf2 : IntegrableOn (fun y => f y ^ 2) (Ioi u))
    (hd2 : IntegrableOn (fun y => (g₁ y - g₂ y) ^ 2) (Ioi u)) :
    airyKerForm u (fun x => g₁ x - g₂ x) f = airyKerForm u g₁ f - airyKerForm u g₂ f := by
  rw [airyKerForm_eq_prod u (show Measurable (fun x => g₁ x - g₂ x) from hg₁.sub hg₂) hf hd2 hf2, airyKerForm_eq_prod u hg₁ hf hg₁2 hf2,
    airyKerForm_eq_prod u hg₂ hf hg₂2 hf2,
    ← integral_sub (integrable_airyKerForm u hg₁ hf hg₁2 hf2) (integrable_airyKerForm u hg₂ hf hg₂2 hf2)]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only; ring

lemma airyKerForm_sub_right (u : ℝ) {g f₁ f₂ : ℝ → ℝ} (hg : Measurable g) (hf₁ : Measurable f₁)
    (hf₂ : Measurable f₂) (hg2 : IntegrableOn (fun y => g y ^ 2) (Ioi u))
    (hf₁2 : IntegrableOn (fun y => f₁ y ^ 2) (Ioi u)) (hf₂2 : IntegrableOn (fun y => f₂ y ^ 2) (Ioi u))
    (hd2 : IntegrableOn (fun y => (f₁ y - f₂ y) ^ 2) (Ioi u)) :
    airyKerForm u g (fun x => f₁ x - f₂ x) = airyKerForm u g f₁ - airyKerForm u g f₂ := by
  rw [airyKerForm_eq_prod u hg (show Measurable (fun x => f₁ x - f₂ x) from hf₁.sub hf₂) hg2 hd2, airyKerForm_eq_prod u hg hf₁ hg2 hf₁2,
    airyKerForm_eq_prod u hg hf₂ hg2 hf₂2,
    ← integral_sub (integrable_airyKerForm u hg hf₁ hg2 hf₁2) (integrable_airyKerForm u hg hf₂ hg2 hf₂2)]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only; ring

lemma airyL2_sub_sq {u : ℝ} {g f : ℝ → ℝ} (hg : Measurable g) (hf : Measurable f)
    (hg2 : IntegrableOn (fun y => g y ^ 2) (Ioi u)) (hf2 : IntegrableOn (fun y => f y ^ 2) (Ioi u)) :
    IntegrableOn (fun y => (f y - g y) ^ 2) (Ioi u) := by
  refine ((hf2.const_mul 2).add (hg2.const_mul 2)).mono' ((hf.sub hg).pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (f y + g y)]

/-- The truncation `f · 1_{(u,n] ∩ {|f| ≤ n}}`. -/
private noncomputable def airyTrunc (u : ℝ) (f : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  {x | x ∈ Ioc u (n : ℝ) ∧ |f x| ≤ n}.indicator f

private lemma airyTrunc_of_mem {u : ℝ} {f : ℝ → ℝ} {n : ℕ} {x : ℝ}
    (hx : x ∈ {x | x ∈ Ioc u (n : ℝ) ∧ |f x| ≤ n}) : airyTrunc u f n x = f x :=
  indicator_of_mem hx f

private lemma airyTrunc_of_notMem {u : ℝ} {f : ℝ → ℝ} {n : ℕ} {x : ℝ}
    (hx : x ∉ {x | x ∈ Ioc u (n : ℝ) ∧ |f x| ≤ n}) : airyTrunc u f n x = 0 :=
  indicator_of_notMem hx f

private lemma measurableSet_airyTrunc {u : ℝ} {f : ℝ → ℝ} (hf : Measurable f) (n : ℕ) :
    MeasurableSet {x | x ∈ Ioc u (n : ℝ) ∧ |f x| ≤ n} :=
  measurableSet_Ioc.inter (measurableSet_le hf.abs measurable_const)

/-- **Positive semidefiniteness of `K_u` on all of `L²(u,∞)`**: `⟨f, K_u f⟩ ≥ 0`. -/
theorem airyKerForm_self_nonneg (u : ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (hf2 : IntegrableOn (fun y => f y ^ 2) (Ioi u)) : 0 ≤ airyKerForm u f f := by
  set g := airyTrunc u f with hgdef
  have hgm : ∀ n, Measurable (g n) := fun n => hf.indicator (measurableSet_airyTrunc hf n)
  have hgsq : ∀ n x, g n x ^ 2 ≤ f x ^ 2 := by
    intro n x
    by_cases hx : x ∈ {x | x ∈ Ioc u (n : ℝ) ∧ |f x| ≤ n}
    · rw [hgdef, airyTrunc_of_mem hx]
    · rw [hgdef, airyTrunc_of_notMem hx]; simpa using sq_nonneg (f x)
  have hg2 : ∀ n, IntegrableOn (fun y => g n y ^ 2) (Ioi u) := fun n =>
    hf2.mono' ((hgm n).pow_const 2).aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hgsq n x)
  have hdsq : ∀ n x, (f x - g n x) ^ 2 ≤ f x ^ 2 := by
    intro n x
    by_cases hx : x ∈ {x | x ∈ Ioc u (n : ℝ) ∧ |f x| ≤ n}
    · rw [hgdef, airyTrunc_of_mem hx]; simpa using sq_nonneg (f x)
    · rw [hgdef, airyTrunc_of_notMem hx]; simp
  -- positivity of the truncations
  have hpos : ∀ n, 0 ≤ airyKerForm u (g n) (g n) := by
    intro n
    have hM : ∀ x, |g n x| ≤ n := by
      intro x
      by_cases hx : x ∈ {x | x ∈ Ioc u (n : ℝ) ∧ |f x| ≤ n}
      · rw [hgdef, airyTrunc_of_mem hx]; exact hx.2
      · rw [hgdef, airyTrunc_of_notMem hx]; simp
    have hsupp : ∀ x, x ∉ Icc u (n : ℝ) → g n x = 0 := by
      intro x hx
      have : x ∉ {x | x ∈ Ioc u (n : ℝ) ∧ |f x| ≤ n} := fun h => hx ⟨h.1.1.le, h.1.2⟩
      rw [hgdef, airyTrunc_of_notMem this]
    have hzero : ∀ x, x ∉ Ioi u → g n x = 0 := by
      intro x hx
      have : x ∉ {x | x ∈ Ioc u (n : ℝ) ∧ |f x| ≤ n} := fun h => hx h.1.1
      rw [hgdef, airyTrunc_of_notMem this]
    have h := airyKer_quadForm_nonneg (hgm n) hM hsupp
    have e1 : ∀ x, ∫ y, g n x * airyKer x y * g n y = ∫ y in Ioi u, g n x * airyKer x y * g n y := by
      intro x
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by simp [hzero y hy]).symm
    simp_rw [e1] at h
    have e2 := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (s := Ioi u)
      (f := fun x => ∫ y in Ioi u, g n x * airyKer x y * g n y) (fun x hx => by simp [hzero x hx])
    unfold airyKerForm
    rw [e2]; exact h
  -- convergence of the defect
  have hD : Tendsto (fun n => ∫ y in Ioi u, (f y - g n y) ^ 2) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioi u))
      (F := fun n y => (f y - g n y) ^ 2) (f := fun _ => (0 : ℝ)) (fun y => f y ^ 2)
      (fun n => ((hf.sub (hgm n)).pow_const 2).aestronglyMeasurable) hf2
      (fun n => Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hdsq n y)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        obtain ⟨N, hN⟩ := exists_nat_ge (max y |f y|)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop N] with n hn
        have hmem : y ∈ {x | x ∈ Ioc u (n : ℝ) ∧ |f x| ≤ n} :=
          ⟨⟨hy, le_trans (le_max_left _ _) (hN.trans (by exact_mod_cast hn))⟩,
            le_trans (le_max_right _ _) (hN.trans (by exact_mod_cast hn))⟩
        rw [hgdef, airyTrunc_of_mem hmem]; simp)
    simpa using this
  by_contra hneg
  push Not at hneg
  set c := airyKerForm u f f with hc
  set A := ∫ y in Ioi u, f y ^ 2 with hA
  have hA0 : 0 ≤ A := integral_nonneg fun y => sq_nonneg _
  have hN2 : 0 ≤ airyN u ^ 2 := sq_nonneg _
  have hbound : ∀ n, (c - airyKerForm u (g n) (g n)) ^ 2 ≤
      4 * airyN u ^ 2 * A * ∫ y in Ioi u, (f y - g n y) ^ 2 := by
    intro n
    have hd := airyL2_sub_sq (hgm n) hf (hg2 n) hf2
    have hsplit : c - airyKerForm u (g n) (g n) =
        airyKerForm u (fun x => f x - g n x) f + airyKerForm u (g n) (fun x => f x - g n x) := by
      rw [airyKerForm_sub_left u hf (hgm n) hf hf2 (hg2 n) hf2 hd,
        airyKerForm_sub_right u (hgm n) hf (hgm n) (hg2 n) hf2 (hg2 n) hd, hc]
      ring
    have hX := airyKerForm_sq_le u (hf.sub (hgm n)) hf hd hf2
    have hY := airyKerForm_sq_le u (hgm n) (hf.sub (hgm n)) (hg2 n) hd
    have hAg : ∫ y in Ioi u, g n y ^ 2 ≤ A :=
      integral_mono (hg2 n) hf2 (fun y => hgsq n y)
    have hD0 : 0 ≤ ∫ y in Ioi u, (f y - g n y) ^ 2 := integral_nonneg fun y => sq_nonneg _
    rw [hsplit]
    set D := ∫ y in Ioi u, (f y - g n y) ^ 2
    set X := airyKerForm u (fun x => f x - g n x) f
    set Y := airyKerForm u (g n) (fun x => f x - g n x)
    have hY' : Y ^ 2 ≤ airyN u ^ 2 * A * D := by
      calc Y ^ 2 ≤ airyN u ^ 2 * (∫ y in Ioi u, g n y ^ 2) * D := hY
        _ ≤ airyN u ^ 2 * A * D := by gcongr
    have hX' : X ^ 2 ≤ airyN u ^ 2 * A * D := by
      calc X ^ 2 ≤ airyN u ^ 2 * D * A := hX
        _ = _ := by ring
    nlinarith [sq_nonneg (X - Y)]
  have hc2 : 0 < c ^ 2 := by have := mul_pos_of_neg_of_neg hneg hneg; nlinarith
  have hlim : Tendsto (fun n => 4 * airyN u ^ 2 * A * ∫ y in Ioi u, (f y - g n y) ^ 2) atTop (𝓝 0) := by
    simpa using hD.const_mul (4 * airyN u ^ 2 * A)
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hc2)).exists
  have h1 := hbound n
  have h2 := hpos n
  nlinarith

/-- info: 'FormalResearch.Special.airyKerForm_self_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyKerForm_self_nonneg

/-- info: 'FormalResearch.Special.integral_airyKerOp_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.integral_airyKerOp_sq_le

/-- info: 'FormalResearch.Special.airyKerForm_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyKerForm_comm

/-- info: 'FormalResearch.Special.airyKerForm_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyKerForm_sq_le

end FormalResearch.Special
