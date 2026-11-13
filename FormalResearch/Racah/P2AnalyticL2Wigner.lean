module

public import FormalResearch.Wigner.WignerDOrth
public import FormalResearch.Wigner.WignerDODE

/-!
# The `L²(-1,1)` layer for Wigner `d`-functions in the variable `x = cos θ` (Weyl P2)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`: `eq:continuummass` (`rem:normmatch`), the modes
`u_L(x) = √((2L+1)/2) d^L_{Mσ}(arccos x)` of `prop:SN` / `prop:6jRacahTransmutation`, and the
differential operator `𝖧₀` of `eq:H0`.

## What is proved

* `integral_wignerSmallDx_mul`: for `L, L'` with `L ± M, L ± σ ∈ ℕ` (and the same for `L'`),
  `∫_{-1}^{1} d^L_{Mσ}(arccos x) d^{L'}_{Mσ}(arccos x) dx = 2/(2L+1) δ_{LL'}`; in particular
  `integral_wignerSmallDx_sq`: `∫_{-1}^{1} (d^L_{Mσ}(x))² dx = 2/(2L+1)` (`eq:continuummass`).  This
  is `wignerSmallD_orthogonal` transported by `integral_cos_substitution`.
* `uWig L M σ x = √((2L+1)/2) d^L_{Mσ}(arccos x)` and its orthonormality `integral_uWig_mul`.
* `L2cont f` is the class in `L²([-1,1])` (`Lp ℝ 2 (volume.restrict (Icc (-1) 1))`) of a continuous
  function; `inner_L2cont`: `⟪[f],[g]⟫ = ∫_{-1}^{1} f g`, so `L2cont (uWig ·)` is an orthonormal family
  in the genuine Hilbert space `L²(-1,1)` (`L2uWig_orthonormal`).
* `H0diff M σ f x`, the differential expression of `eq:H0`, and the eigen-equation
  `H0diff_uWig`: `𝖧₀ u_L = L(L+1) u_L` on `(-1,1)` (`wignerSmallDx_ode`), together with its
  linear extension to finite combinations `H0diff_sum`.

Not formalised: `L²` completeness of `{u_L}` (density of the Wigner modes), and the identification of
`𝖧₀` as a self-adjoint operator with its domain.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner FormalResearch.Special MeasureTheory

/-- Admissibility of a rank `L` for the labels `(M, σ)` in `d^L_{Mσ}`: `L ± M` and `L ± σ` are
natural numbers. -/
def DAdm (L M σ : ℚ) : Prop := IsNat (L + M) ∧ IsNat (L - M) ∧ IsNat (L + σ) ∧ IsNat (L - σ)

lemma DAdm.nonneg {L M σ : ℚ} (h : DAdm L M σ) : 0 ≤ L := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩, -, -⟩ := h
  have : (0 : ℚ) ≤ p + q := by positivity
  linarith

lemma wignerSmallDx_continuous (j m' m : ℚ) : Continuous (wignerSmallDx j m' m) :=
  (wignerSmallD_contDiff j m' m (n := 0)).continuous.comp Real.continuous_arccos

/-- **`eq:continuummass`, general form**: orthogonality of `d^L_{Mσ}(arccos x)` in `L²(-1,1)`:
`∫_{-1}^1 d^L d^{L'} dx = 2/(2L+1) δ_{LL'}`. -/
theorem integral_wignerSmallDx_mul {L L' M σ : ℚ} (h : DAdm L M σ) (h' : DAdm L' M σ) :
    ∫ x in (-1 : ℝ)..1, wignerSmallDx L M σ x * wignerSmallDx L' M σ x =
      if L = L' then 2 / (2 * (L : ℝ) + 1) else 0 := by
  have hc : Continuous (fun x => wignerSmallDx L M σ x * wignerSmallDx L' M σ x) :=
    (wignerSmallDx_continuous _ _ _).mul (wignerSmallDx_continuous _ _ _)
  rw [← integral_cos_substitution _ hc]
  have e : ∫ θ in (0 : ℝ)..Real.pi, wignerSmallD L M σ θ * wignerSmallD L' M σ θ * Real.sin θ =
      ∫ θ in (0 : ℝ)..Real.pi,
        (fun x => wignerSmallDx L M σ x * wignerSmallDx L' M σ x) (Real.cos θ) * Real.sin θ := by
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [Set.uIcc_of_le Real.pi_pos.le] at hθ
    simp only [wignerSmallDx, Real.arccos_cos hθ.1 hθ.2]
  rw [← e]
  exact wignerSmallD_orthogonal h.1 h.2.1 h.2.2.1 h.2.2.2 h'.1 h'.2.1 h'.2.2.1 h'.2.2.2

/-- **`eq:continuummass`**: `∫_{-1}^{1} (d^L_{Mσ}(arccos x))² dx = 2/(2L+1)`. -/
theorem integral_wignerSmallDx_sq {L M σ : ℚ} (h : DAdm L M σ) :
    ∫ x in (-1 : ℝ)..1, (wignerSmallDx L M σ x) ^ 2 = 2 / (2 * (L : ℝ) + 1) := by
  have := integral_wignerSmallDx_mul h h
  simpa only [↓reduceIte, sq] using this

/-- The normalised Wigner mode `u_L(x) = √((2L+1)/2) d^L_{Mσ}(arccos x)`. -/
noncomputable def uWig (L M σ : ℚ) (x : ℝ) : ℝ :=
  Real.sqrt ((2 * (L : ℝ) + 1) / 2) * wignerSmallDx L M σ x

lemma uWig_continuous (L M σ : ℚ) : Continuous (uWig L M σ) :=
  continuous_const.mul (wignerSmallDx_continuous L M σ)

/-- Orthonormality of the modes `u_L` in `L²(-1,1)`. -/
theorem integral_uWig_mul {L L' M σ : ℚ} (h : DAdm L M σ) (h' : DAdm L' M σ) :
    ∫ x in (-1 : ℝ)..1, uWig L M σ x * uWig L' M σ x = if L = L' then 1 else 0 := by
  have hL : (0 : ℝ) ≤ (2 * (L : ℝ) + 1) / 2 := by
    have : (0 : ℝ) ≤ L := by exact_mod_cast h.nonneg
    linarith
  have hL' : (0 : ℝ) ≤ (2 * (L' : ℝ) + 1) / 2 := by
    have : (0 : ℝ) ≤ L' := by exact_mod_cast h'.nonneg
    linarith
  have e : ∀ x, uWig L M σ x * uWig L' M σ x =
      (Real.sqrt ((2 * (L : ℝ) + 1) / 2) * Real.sqrt ((2 * (L' : ℝ) + 1) / 2)) *
        (wignerSmallDx L M σ x * wignerSmallDx L' M σ x) := fun x => by
    unfold uWig; ring
  simp only [e]
  rw [intervalIntegral.integral_const_mul, integral_wignerSmallDx_mul h h']
  by_cases hLL : L = L'
  · subst hLL
    simp only [↓reduceIte]
    rw [Real.mul_self_sqrt hL]
    have : (2 * (L : ℝ) + 1) ≠ 0 := by
      have : (0 : ℝ) ≤ L := by exact_mod_cast h.nonneg
      linarith
    field_simp
  · simp [hLL]

/-! ### The Hilbert space `L²(-1,1)` -/

/-- Lebesgue measure on `[-1,1]`. -/
noncomputable abbrev mu11 : Measure ℝ := volume.restrict (Set.Icc (-1 : ℝ) 1)

/-- `L²(-1,1)`. -/
abbrev L2m11 : Type := Lp ℝ 2 mu11

lemma memLp_of_continuous {f : ℝ → ℝ} (hf : Continuous f) : MemLp f 2 mu11 := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hf.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  exact Filter.Eventually.of_forall fun x hx => hC x hx

/-- The class in `L²(-1,1)` of a continuous function. -/
noncomputable def L2cont (f : ℝ → ℝ) (hf : Continuous f) : L2m11 :=
  (memLp_of_continuous hf).toLp f

/-- `⟪[f],[g]⟫_{L²(-1,1)} = ∫_{-1}^1 f g`. -/
theorem inner_L2cont {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    inner ℝ (L2cont f hf) (L2cont g hg) = ∫ x in (-1 : ℝ)..1, f x * g x := by
  unfold L2cont
  rw [MeasureTheory.L2.inner_def]
  have h1 := (memLp_of_continuous hf).coeFn_toLp
  have h2 := (memLp_of_continuous hg).coeFn_toLp
  have : ∫ a, inner ℝ ((memLp_of_continuous hf).toLp f a) ((memLp_of_continuous hg).toLp g a)
      ∂mu11 = ∫ a, f a * g a ∂mu11 := by
    refine integral_congr_ae ?_
    filter_upwards [h1, h2] with a ha hb
    rw [ha, hb]
    simp [mul_comm]
  rw [this, intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]

/-- The normalised Wigner modes `u_L` as elements of `L²(-1,1)`. -/
noncomputable def L2uWig (L M σ : ℚ) : L2m11 := L2cont (uWig L M σ) (uWig_continuous L M σ)

/-- The classes `[u_L]` (for admissible distinct ranks) are orthonormal in `L²(-1,1)`. -/
theorem inner_L2uWig {L L' M σ : ℚ} (h : DAdm L M σ) (h' : DAdm L' M σ) :
    inner ℝ (L2uWig L M σ) (L2uWig L' M σ) = if L = L' then 1 else 0 := by
  unfold L2uWig
  rw [inner_L2cont, integral_uWig_mul h h']

/-- Any family `L : ι → ℚ` of distinct admissible ranks gives an orthonormal family of
`L²(-1,1)`. -/
theorem L2uWig_orthonormal {ι : Type*} [DecidableEq ι] (L : ι → ℚ) (hinj : Function.Injective L) (M σ : ℚ)
    (hadm : ∀ i, DAdm (L i) M σ) : Orthonormal ℝ (fun i => L2uWig (L i) M σ) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_L2uWig (hadm i) (hadm j)]
  by_cases hij : i = j
  · simp [hij]
  · have : L i ≠ L j := fun e => hij (hinj e)
    simp [hij, this]

/-! ### The differential operator `𝖧₀` of `eq:H0` -/

/-- The differential expression `𝖧₀ f = -((1-x²) f')' + (Σ - 2τx)/(1-x²) f`, `Σ = M²+σ²`,
`τ = Mσ` (`eq:H0`), written with `-((1-x²) f')' = -(1-x²) f'' + 2x f'`; only its values on
`(-1,1)` are meaningful. -/
noncomputable def H0diff (M σ : ℚ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  -((1 - x ^ 2) * deriv (deriv f) x - 2 * x * deriv f x) +
    (((M : ℝ) ^ 2 + (σ : ℝ) ^ 2) - 2 * ((M : ℝ) * σ) * x) / (1 - x ^ 2) * f x

lemma wignerSmallDx_differentiableAt (j m' m : ℚ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    DifferentiableAt ℝ (wignerSmallDx j m' m) x :=
  (hasDerivAt_wignerSmallDx j m' m hx).differentiableAt

lemma wignerSmallDx_deriv_differentiableAt (j m' m : ℚ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    DifferentiableAt ℝ (deriv (wignerSmallDx j m' m)) x := by
  have hS := sin_arccos_pos hx
  have hA : DifferentiableAt ℝ Real.arccos x :=
    Real.differentiableAt_arccos.2 ⟨hx.1.ne', hx.2.ne⟩
  have h1 : DifferentiableAt ℝ (fun y => -(deriv (wignerSmallD j m' m) (Real.arccos y)) /
      Real.sin (Real.arccos y)) x := by
    refine DifferentiableAt.div ?_ ?_ hS.ne'
    · exact ((wignerSmallD_deriv_differentiable j m' m (Real.arccos x)).comp x hA).neg
    · exact (Real.differentiableAt_sin).comp x hA
  have h2 := deriv_comp_arccos_eventually (wignerSmallD_differentiable j m' m) hx
  rw [wignerSmallDx_eq]
  exact h1.congr_of_eventuallyEq h2

lemma deriv_cmul (c : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    deriv (fun y => c * g y) x = c * deriv g x :=
  congrFun (deriv_const_mul_field' (v := g) c) x

/-- **`𝖧₀ u_L = L(L+1) u_L` on `(-1,1)`** for `f = d^L_{Mσ}(arccos ·)`: the Wigner equation
`wignerSmallDx_ode` in the form of `eq:H0`. -/
theorem H0diff_wignerSmallDx (L M σ : ℚ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    H0diff M σ (wignerSmallDx L M σ) x = ((L : ℝ) * (L + 1)) * wignerSmallDx L M σ x := by
  have h := wignerSmallDx_ode L M σ hx
  have hx2 : (1 - x ^ 2) ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold H0diff
  generalize deriv (deriv (wignerSmallDx L M σ)) x = D2 at h ⊢
  generalize deriv (wignerSmallDx L M σ) x = D1 at h ⊢
  generalize wignerSmallDx L M σ x = d0 at h ⊢
  field_simp at h ⊢
  linear_combination -h

/-- `𝖧₀ u_L = L(L+1) u_L` on `(-1,1)` for the normalised modes. -/
theorem H0diff_uWig (L M σ : ℚ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    H0diff M σ (uWig L M σ) x = ((L : ℝ) * (L + 1)) * uWig L M σ x := by
  have e1 : deriv (uWig L M σ) = fun y => Real.sqrt ((2 * (L : ℝ) + 1) / 2) *
      deriv (wignerSmallDx L M σ) y := by
    funext y; unfold uWig; exact deriv_cmul _ _ _
  have e2 : deriv (deriv (uWig L M σ)) x = Real.sqrt ((2 * (L : ℝ) + 1) / 2) *
      deriv (deriv (wignerSmallDx L M σ)) x := by
    rw [e1]; exact deriv_cmul _ _ _
  have h := H0diff_wignerSmallDx L M σ hx
  unfold H0diff at h ⊢
  rw [e2, e1]
  unfold uWig
  generalize Real.sqrt ((2 * (L : ℝ) + 1) / 2) = c
  linear_combination c * h

/-- Linearity of `𝖧₀` on finite combinations of functions that are twice differentiable on
`(-1,1)`. -/
theorem H0diff_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → ℝ → ℝ) (M σ : ℚ)
    (hf : ∀ i ∈ s, ∀ y ∈ Set.Ioo (-1 : ℝ) 1, DifferentiableAt ℝ (f i) y)
    (hf' : ∀ i ∈ s, ∀ y ∈ Set.Ioo (-1 : ℝ) 1, DifferentiableAt ℝ (deriv (f i)) y)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    H0diff M σ (fun y => ∑ i ∈ s, c i * f i y) x = ∑ i ∈ s, c i * H0diff M σ (f i) x := by
  have hd : ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
      deriv (fun y => ∑ i ∈ s, c i * f i y) y = ∑ i ∈ s, c i * deriv (f i) y := by
    intro y hy
    rw [deriv_fun_sum (fun i hi => (hf i hi y hy).const_mul (c i))]
    exact Finset.sum_congr rfl fun i hi => deriv_cmul _ _ _
  have hev : deriv (fun y => ∑ i ∈ s, c i * f i y) =ᶠ[nhds x]
      fun y => ∑ i ∈ s, c i * deriv (f i) y := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy using hd y hy
  have hdd : deriv (deriv (fun y => ∑ i ∈ s, c i * f i y)) x =
      ∑ i ∈ s, c i * deriv (deriv (f i)) x := by
    rw [hev.deriv_eq, deriv_fun_sum (fun i hi => (hf' i hi x hx).const_mul (c i))]
    exact Finset.sum_congr rfl fun i hi => deriv_cmul _ _ _
  unfold H0diff
  rw [hdd, hd x hx]
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- info: 'FormalResearch.Racah.integral_wignerSmallDx_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_wignerSmallDx_mul

/-- info: 'FormalResearch.Racah.integral_wignerSmallDx_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_wignerSmallDx_sq

/-- info: 'FormalResearch.Racah.integral_uWig_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_uWig_mul

/-- info: 'FormalResearch.Racah.inner_L2cont' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inner_L2cont

/-- info: 'FormalResearch.Racah.L2uWig_orthonormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms L2uWig_orthonormal

/-- info: 'FormalResearch.Racah.H0diff_wignerSmallDx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms H0diff_wignerSmallDx

/-- info: 'FormalResearch.Racah.H0diff_uWig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms H0diff_uWig

/-- info: 'FormalResearch.Racah.H0diff_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms H0diff_sum

end FormalResearch.Racah
