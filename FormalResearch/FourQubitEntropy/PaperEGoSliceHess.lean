import FormalResearch.FourQubitEntropy.PaperEGoSliceConstr
import FormalResearch.FourQubitEntropy.PaperEGoSliceGen

/-!
# `thm:fqe-global-overlap`, layer (c): the height Hessian `H ⪰ 0`

`frameHess : FrameHess`: at a closest-point frame the ten-generator height Hessian `H(v)` of
`eq:fqe-height-matrix` is positive semidefinite.

Proof.  For a direction `w ∈ ℝ¹⁰` let `L, R` be the skew matrices and `p` the phase rate it defines.  The
curve `s ↦ (exp(sL), exp(sR), phase e^{i√3 p s})` lies in `O(4) × O(4) × U(1)`, so by `height_ineqG`
the real height `F(s) = cos(θ s) u(s) + √3 sin(θ s) v(s)`, `θ = √3 p`, is `≤ F(0)`, with
`u, v` built from the entries of `exp(-sL) X exp(sR)`, `exp(-sL) Y exp(sR)`.  Then `F'(0) = 0` and
`F''(0) ≤ 0` (`max_second_order`, from Mathlib's second-derivative test) and `-F''(0) = wᵀ H w` is a
polynomial identity (`frameHess`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 6400000

open scoped ComplexConjugate Matrix Kronecker
open scoped Matrix.Norms.Operator

namespace FormalResearch.FourQubitEntropy.GO
open CO OD PaperECritical

noncomputable section

/-! ### An abstract second-order condition -/

theorem max_second_order {u u1 u2 v v1 v2 : ℝ → ℝ} (θ : ℝ)
    (hu : ∀ s, HasDerivAt u (u1 s) s) (hu1 : ∀ s, HasDerivAt u1 (u2 s) s)
    (hv : ∀ s, HasDerivAt v (v1 s) s) (hv1 : ∀ s, HasDerivAt v1 (v2 s) s)
    (hmax : ∀ s, Real.cos (θ * s) * u s + Real.sqrt 3 * Real.sin (θ * s) * v s ≤ u 0) :
    -θ ^ 2 * u 0 + u2 0 + 2 * Real.sqrt 3 * θ * v1 0 ≤ 0 := by
  have hcs : ∀ s, HasDerivAt (fun s => Real.cos (θ * s)) (-Real.sin (θ * s) * (θ * 1)) s :=
    fun s => ((hasDerivAt_id' s).const_mul θ).cos
  have hsn : ∀ s, HasDerivAt (fun s => Real.sin (θ * s)) (Real.cos (θ * s) * (θ * 1)) s :=
    fun s => ((hasDerivAt_id' s).const_mul θ).sin
  obtain ⟨F, hFd⟩ : ∃ F : ℝ → ℝ, F = fun s =>
      Real.cos (θ * s) * u s + Real.sqrt 3 * Real.sin (θ * s) * v s := ⟨_, rfl⟩
  obtain ⟨F1, hF1d⟩ : ∃ F1 : ℝ → ℝ, F1 = fun s =>
      -θ * Real.sin (θ * s) * u s + Real.cos (θ * s) * u1 s +
        Real.sqrt 3 * θ * Real.cos (θ * s) * v s + Real.sqrt 3 * Real.sin (θ * s) * v1 s :=
    ⟨_, rfl⟩
  obtain ⟨F2, hF2d⟩ : ∃ F2 : ℝ → ℝ, F2 = fun s =>
      -θ ^ 2 * Real.cos (θ * s) * u s - 2 * θ * Real.sin (θ * s) * u1 s +
        Real.cos (θ * s) * u2 s - Real.sqrt 3 * θ ^ 2 * Real.sin (θ * s) * v s +
        2 * Real.sqrt 3 * θ * Real.cos (θ * s) * v1 s + Real.sqrt 3 * Real.sin (θ * s) * v2 s :=
    ⟨_, rfl⟩
  have hF : ∀ s, HasDerivAt F (F1 s) s := by
    intro s
    have := ((hcs s).mul (hu s)).add (((hsn s).const_mul (Real.sqrt 3)).mul (hv s))
    rw [hFd, hF1d]
    refine this.congr_deriv ?_
    ring
  have hF1 : ∀ s, HasDerivAt F1 (F2 s) s := by
    intro s
    have h1 := ((hsn s).const_mul (-θ)).mul (hu s)
    have h2 := (hcs s).mul (hu1 s)
    have h3 := ((hcs s).const_mul (Real.sqrt 3 * θ)).mul (hv s)
    have h4 := ((hsn s).const_mul (Real.sqrt 3)).mul (hv1 s)
    have := ((h1.add h2).add h3).add h4
    rw [hF1d, hF2d]
    refine this.congr_deriv ?_
    ring
  have hF0 : F 0 = u 0 := by simp [hFd]
  have hmaxloc : IsLocalMax F 0 :=
    Filter.Eventually.of_forall fun s => by rw [hF0, hFd]; exact hmax s
  have hd0 : F1 0 = 0 := hmaxloc.hasDerivAt_eq_zero (hF 0)
  have hV : F2 0 = -θ ^ 2 * u 0 + u2 0 + 2 * Real.sqrt 3 * θ * v1 0 := by simp [hF2d]
  rw [← hV]
  by_contra hcon
  push_neg at hcon
  have hdF : deriv F = F1 := funext fun s => (hF s).deriv
  have hdd : deriv (deriv F) 0 = F2 0 := by rw [hdF]; exact (hF1 0).deriv
  have hmin : IsLocalMin F 0 :=
    isLocalMin_of_deriv_deriv_pos (by rw [hdd]; exact hcon) (by rw [hdF]; exact hd0)
      (hF 0).continuousAt
  have hconst : F =ᶠ[nhds 0] fun _ => F 0 := by
    filter_upwards [hmin, hmaxloc] with x h1 h2 using le_antisymm h2 h1
  have h1z : F1 =ᶠ[nhds 0] fun _ => (0 : ℝ) := by
    have := hconst.deriv
    rw [hdF] at this
    simpa using this
  have h2 := (hF1 0).congr_of_eventuallyEq h1z.symm
  have := h2.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  linarith

/-! ### The orthogonal curves -/

theorem exp_orth {L : M4R} (hL : Lᵀ = -L) (s : ℝ) :
    (NormedSpace.exp (s • L))ᵀ * NormedSpace.exp (s • L) = 1 := by
  have hc : Commute (s • -L) (s • L) := by
    rw [smul_neg]; exact (Commute.refl (s • L)).neg_left
  rw [← Matrix.exp_transpose, Matrix.transpose_smul, hL, ← Matrix.exp_add_of_commute _ _ hc,
    smul_neg, neg_add_cancel, NormedSpace.exp_zero]

theorem exp_transpose_neg {L : M4R} (hL : Lᵀ = -L) (s : ℝ) :
    (NormedSpace.exp (s • L))ᵀ = NormedSpace.exp (s • -L) := by
  rw [← Matrix.exp_transpose, Matrix.transpose_smul, hL]

/-- `s ↦ exp(-sL) X exp(sR)`. -/
def Acurve (L R X : M4R) (s : ℝ) : M4R :=
  NormedSpace.exp (s • -L) * X * NormedSpace.exp (s • R)

/-- The generator `M ↦ -L M + M R`. -/
def Tm (L R : M4R) : M4R →ₗ[ℝ] M4R := LinearMap.mulLeft ℝ (-L) + LinearMap.mulRight ℝ R

theorem Tm_apply (L R M : M4R) : Tm L R M = -L * M + M * R := by
  simp [Tm]

theorem Acurve_zero (L R X : M4R) : Acurve L R X 0 = X := by
  simp [Acurve]

theorem hasDerivAt_Acurve (L R X : M4R) (s : ℝ) :
    HasDerivAt (Acurve L R X) (Tm L R (Acurve L R X s)) s := by
  have h1 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-L) s
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) R s
  have := (h1.mul_const X).mul h2
  rw [Tm_apply]
  refine this.congr_deriv ?_
  simp only [Acurve, mul_assoc, neg_mul]
  abel

theorem hasDerivAt_lin (L R X : M4R) (ℓ : M4R →ₗ[ℝ] ℝ) (s : ℝ) :
    HasDerivAt (fun s => ℓ (Acurve L R X s)) (ℓ (Tm L R (Acurve L R X s))) s := by
  have h := (LinearMap.toContinuousLinearMap ℓ).hasFDerivAt.comp_hasDerivAt s
    (hasDerivAt_Acurve L R X s)
  exact h

theorem hasDerivAt_entry0 (L R X : M4R) (i j : Fin 4) (s : ℝ) :
    HasDerivAt (fun s => Acurve L R X s i j) ((Tm L R (Acurve L R X s)) i j) s := by
  simpa using hasDerivAt_lin L R X (Matrix.entryLinearMap ℝ ℝ i j) s

theorem hasDerivAt_entry1 (L R X : M4R) (i j : Fin 4) (s : ℝ) :
    HasDerivAt (fun s => (Tm L R (Acurve L R X s)) i j)
      ((Tm L R (Tm L R (Acurve L R X s))) i j) s := by
  simpa using hasDerivAt_lin L R X ((Matrix.entryLinearMap ℝ ℝ i j).comp (Tm L R)) s

/-! ### The Hessian along a group curve -/

theorem hess_gen {φ : Psi} {h : ℝ} (hf : IsFrame φ h) {X Y : M4R} (hφ : CoordIs φ X Y)
    (L R : M4R) (hL : Lᵀ = -L) (hR : Rᵀ = -R) (p : ℝ) :
    -3 * p ^ 2 * hgt X Y +
      (3 * (Tm L R (Tm L R X)) 0 0 + ∑ k : Fin 3, (Tm L R (Tm L R Y)) k.succ k.succ) +
      6 * p * ((Tm L R Y) 0 0 - ∑ k : Fin 3, (Tm L R X) k.succ k.succ) ≤ 0 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h3p : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = Real.sqrt 3 * p := ⟨_, rfl⟩
  obtain ⟨u, hud⟩ : ∃ u : ℝ → ℝ, u = fun s =>
    3 * Acurve L R X s 0 0 + ∑ k : Fin 3, Acurve L R Y s k.succ k.succ := ⟨_, rfl⟩
  obtain ⟨u1, hu1d⟩ : ∃ u1 : ℝ → ℝ, u1 = fun s =>
    3 * (Tm L R (Acurve L R X s)) 0 0 + ∑ k : Fin 3, (Tm L R (Acurve L R Y s)) k.succ k.succ :=
    ⟨_, rfl⟩
  obtain ⟨u2, hu2d⟩ : ∃ u2 : ℝ → ℝ, u2 = fun s =>
    3 * (Tm L R (Tm L R (Acurve L R X s))) 0 0 +
      ∑ k : Fin 3, (Tm L R (Tm L R (Acurve L R Y s))) k.succ k.succ := ⟨_, rfl⟩
  obtain ⟨v, hvd⟩ : ∃ v : ℝ → ℝ, v = fun s =>
    Acurve L R Y s 0 0 - ∑ k : Fin 3, Acurve L R X s k.succ k.succ := ⟨_, rfl⟩
  obtain ⟨v1, hv1d⟩ : ∃ v1 : ℝ → ℝ, v1 = fun s =>
    (Tm L R (Acurve L R Y s)) 0 0 - ∑ k : Fin 3, (Tm L R (Acurve L R X s)) k.succ k.succ :=
    ⟨_, rfl⟩
  obtain ⟨v2, hv2d⟩ : ∃ v2 : ℝ → ℝ, v2 = fun s =>
    (Tm L R (Tm L R (Acurve L R Y s))) 0 0 -
      ∑ k : Fin 3, (Tm L R (Tm L R (Acurve L R X s))) k.succ k.succ := ⟨_, rfl⟩
  have hu : ∀ s, HasDerivAt u (u1 s) s := by
    intro s
    rw [hud, hu1d]
    exact ((hasDerivAt_entry0 L R X 0 0 s).const_mul 3).add
      (HasDerivAt.fun_sum fun k _ => hasDerivAt_entry0 L R Y k.succ k.succ s)
  have hu1 : ∀ s, HasDerivAt u1 (u2 s) s := by
    intro s
    rw [hu2d, hu1d]
    exact ((hasDerivAt_entry1 L R X 0 0 s).const_mul 3).add
      (HasDerivAt.fun_sum fun k _ => hasDerivAt_entry1 L R Y k.succ k.succ s)
  have hv : ∀ s, HasDerivAt v (v1 s) s := by
    intro s
    rw [hvd, hv1d]
    exact (hasDerivAt_entry0 L R Y 0 0 s).sub
      (HasDerivAt.fun_sum fun k _ => hasDerivAt_entry0 L R X k.succ k.succ s)
  have hv1 : ∀ s, HasDerivAt v1 (v2 s) s := by
    intro s
    rw [hv2d, hv1d]
    exact (hasDerivAt_entry1 L R Y 0 0 s).sub
      (HasDerivAt.fun_sum fun k _ => hasDerivAt_entry1 L R X k.succ k.succ s)
  have hu0 : u 0 = hgt X Y := by simp [hud, Acurve_zero, hgt]
  have hmax : ∀ s, Real.cos (θ * s) * u s + Real.sqrt 3 * Real.sin (θ * s) * v s ≤ u 0 := by
    intro s
    have hcs : Real.cos (θ * s) ^ 2 + 3 * (Real.sin (θ * s) / Real.sqrt 3) ^ 2 = 1 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
      have := Real.sin_sq_add_cos_sq (θ * s)
      field_simp
      linarith
    have := height_ineqG hf hφ (NormedSpace.exp (s • L)) (NormedSpace.exp (s • R))
      (exp_orth hL s) (exp_orth hR s) (Real.cos (θ * s)) (Real.sin (θ * s) / Real.sqrt 3) hcs
    rw [exp_transpose_neg hL s] at this
    have e : 3 * (Real.sin (θ * s) / Real.sqrt 3) = Real.sqrt 3 * Real.sin (θ * s) := by
      field_simp
      rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
      ring
    rw [e] at this
    rw [hu0, hud, hvd]
    exact this
  have key := max_second_order θ hu hu1 hv hv1 hmax
  have e1 : θ ^ 2 = 3 * p ^ 2 := by rw [hθ, mul_pow, Real.sq_sqrt (by norm_num)]
  have e2 : 2 * Real.sqrt 3 * θ = 6 * p := by rw [hθ]; linear_combination (2 * p) * h3
  rw [e1, e2, hu0] at key
  simp only [hu2d, hv1d, Acurve_zero] at key
  linarith [key]


/-! ### The ten-generator Hessian -/

/-- `sHess` written out: the `10 × 10` matrix of rational linear forms in the 19 slice coordinates
(identical to `height_hessian()` of `orbit_certificate_polynomials.py`). -/
def sHessExp (v : SV) : Fin 10 → Fin 10 → ℝ := ![
  ![(4 : ℝ) * v 0 + (1 : ℝ) * v 4, (-4 : ℝ) * v 1 + (-1 : ℝ) * v 2 + (-1 : ℝ) * v 3, (-1/2 : ℝ) * v 7, (-3 : ℝ) * v 7 + (-3 : ℝ) * v 10, (-1/2 : ℝ) * v 8, (-3 : ℝ) * v 8 + (-3 : ℝ) * v 11, (-1 : ℝ) * v 17, (-1 : ℝ) * v 18, 0, (12 : ℝ) * v 13],
  ![(-4 : ℝ) * v 1 + (-1 : ℝ) * v 2 + (-1 : ℝ) * v 3, (4 : ℝ) * v 0 + (1 : ℝ) * v 4, (-3 : ℝ) * v 7 + (3 : ℝ) * v 10, (-1/2 : ℝ) * v 7, (-3 : ℝ) * v 8 + (3 : ℝ) * v 11, (-1/2 : ℝ) * v 8, (3 : ℝ) * v 14, (3 : ℝ) * v 15, 0, (4 : ℝ) * v 16],
  ![(-1/2 : ℝ) * v 7, (-3 : ℝ) * v 7 + (3 : ℝ) * v 10, (4 : ℝ) * v 0 + (1 : ℝ) * v 5, (-1 : ℝ) * v 1 + (-4 : ℝ) * v 2 + (-1 : ℝ) * v 3, (-1/2 : ℝ) * v 9, (-3 : ℝ) * v 9 + (-3 : ℝ) * v 12, (1 : ℝ) * v 16, 0, (-1 : ℝ) * v 18, (12 : ℝ) * v 14],
  ![(-3 : ℝ) * v 7 + (-3 : ℝ) * v 10, (-1/2 : ℝ) * v 7, (-1 : ℝ) * v 1 + (-4 : ℝ) * v 2 + (-1 : ℝ) * v 3, (4 : ℝ) * v 0 + (1 : ℝ) * v 5, (-3 : ℝ) * v 9 + (3 : ℝ) * v 12, (-1/2 : ℝ) * v 9, (-3 : ℝ) * v 13, 0, (3 : ℝ) * v 15, (4 : ℝ) * v 17],
  ![(-1/2 : ℝ) * v 8, (-3 : ℝ) * v 8 + (3 : ℝ) * v 11, (-1/2 : ℝ) * v 9, (-3 : ℝ) * v 9 + (3 : ℝ) * v 12, (4 : ℝ) * v 0 + (1 : ℝ) * v 6, (-1 : ℝ) * v 1 + (-1 : ℝ) * v 2 + (-4 : ℝ) * v 3, 0, (1 : ℝ) * v 16, (1 : ℝ) * v 17, (12 : ℝ) * v 15],
  ![(-3 : ℝ) * v 8 + (-3 : ℝ) * v 11, (-1/2 : ℝ) * v 8, (-3 : ℝ) * v 9 + (-3 : ℝ) * v 12, (-1/2 : ℝ) * v 9, (-1 : ℝ) * v 1 + (-1 : ℝ) * v 2 + (-4 : ℝ) * v 3, (4 : ℝ) * v 0 + (1 : ℝ) * v 6, 0, (-3 : ℝ) * v 13, (-3 : ℝ) * v 14, (4 : ℝ) * v 18],
  ![(-1 : ℝ) * v 17, (3 : ℝ) * v 14, (1 : ℝ) * v 16, (-3 : ℝ) * v 13, 0, 0, (2 : ℝ) * v 0 + (1 : ℝ) * v 4 + (1 : ℝ) * v 5, (-1/2 : ℝ) * v 9, (1/2 : ℝ) * v 8, (6 : ℝ) * v 10],
  ![(-1 : ℝ) * v 18, (3 : ℝ) * v 15, 0, 0, (1 : ℝ) * v 16, (-3 : ℝ) * v 13, (-1/2 : ℝ) * v 9, (2 : ℝ) * v 0 + (1 : ℝ) * v 4 + (1 : ℝ) * v 6, (-1/2 : ℝ) * v 7, (6 : ℝ) * v 11],
  ![0, 0, (-1 : ℝ) * v 18, (3 : ℝ) * v 15, (1 : ℝ) * v 17, (-3 : ℝ) * v 14, (1/2 : ℝ) * v 8, (-1/2 : ℝ) * v 7, (2 : ℝ) * v 0 + (1 : ℝ) * v 5 + (1 : ℝ) * v 6, (6 : ℝ) * v 12],
  ![(12 : ℝ) * v 13, (4 : ℝ) * v 16, (12 : ℝ) * v 14, (4 : ℝ) * v 17, (12 : ℝ) * v 15, (4 : ℝ) * v 18, (6 : ℝ) * v 10, (6 : ℝ) * v 11, (6 : ℝ) * v 12, (18 : ℝ) * v 0 + (3 : ℝ) * v 4 + (3 : ℝ) * v 5 + (3 : ℝ) * v 6]]

theorem sHess_eq_exp (v : SV) : sHess v = sHessExp v := by
  funext l m
  fin_cases l <;> fin_cases m <;>
    simp [sHess, gens, Gen.act, cStar, skewG, sX, sY, Matrix.mul_apply, Fin.sum_univ_four,
      sHessExp] <;> ring

/-! ### Axiom audit -/

/-- info: 'FormalResearch.FourQubitEntropy.GO.max_second_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms max_second_order

/-- info: 'FormalResearch.FourQubitEntropy.GO.hess_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hess_gen

/-- info: 'FormalResearch.FourQubitEntropy.GO.sHess_eq_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sHess_eq_exp

end

end FormalResearch.FourQubitEntropy.GO
