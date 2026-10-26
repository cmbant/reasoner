import FormalResearch.FourQubitEntropy.Rigidity

/-!
# Cubic spectral majorants

For a function `f : ℝ → ℝ` put `E_f(ψ) = ⅓ Σ_{j=2}^{4} tr f(ρ_{1j})` (`meanSpec f ψ`, with
`tr f(ρ) = Σ_i f(λ_i)` over the eigenvalues of the reduced matrix).

If a cubic `h(x) = a x³ + b x² + c x + d` majorizes `f` on `[0,1]`, agrees with `f` at `1/6`
and `1/2`, and `a ≥ 0`, `b + 17a/12 ≤ 0`, then `E_f(ψ) ≤ E_f(M₄)` for every unit vector
(`majorant_le`). The gap identity (SF) of the paper is `majorant_gap`.

Paper: `prop:fqe-majorant` (spectral_corollaries.tex).

**Equality.** The paper obtains the equality classification (for `a, α > 0`) from the equality
classification `P = 1 ∧ F = 0` of the sextic inequality, which is not formalized here. We prove
the equality case under the additional hypothesis that `h > f` off the two nodes (this is the
situation for every Hermite majorant with `f⁗ < 0`, e.g. the entropy and Tsallis cases):
`majorant_eq_iff`.
-/

open scoped ComplexConjugate Matrix ComplexOrder

namespace FormalResearch.FourQubitEntropy

/-- `tr f(R)` for a Hermitian `R`, from its eigenvalues. -/
noncomputable def cutSum (f : ℝ → ℝ) {R : Mat4} (hR : R.IsHermitian) : ℝ :=
  ∑ i, f (hR.eigenvalues i)

/-- `E_f(ψ) = ⅓ Σ_{j=2}^4 tr f(ρ_{1j})`, for a unit vector `ψ` (the `R_{1j}` are the reduced
matrices). -/
noncomputable def meanSpec (f : ℝ → ℝ) (ψ : Psi) : ℝ :=
  (cutSum f (red12_herm ψ) + cutSum f (red13_herm ψ) + cutSum f (red14_herm ψ)) / 3

/-- A cubic polynomial. -/
def cubicPoly (a b c d x : ℝ) : ℝ := a * x ^ 3 + b * x ^ 2 + c * x + d

theorem sum_eigenvalues_eq_trace {R : Mat4} (hR : R.IsHermitian) :
    ∑ i, hR.eigenvalues i = (Matrix.trace R).re := by
  simpa using sum_eigenvalues_pow hR 1

/-- The eigenvalues of a PSD matrix of trace `1` lie in `[0,1]`. -/
theorem eigenvalue_mem_Icc {R : Mat4} (hR : R.IsHermitian) (hp : R.PosSemidef)
    (htr : (Matrix.trace R).re = 1) (i : Fin 2 × Fin 2) : hR.eigenvalues i ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨hp.eigenvalues_nonneg i, ?_⟩
  rw [← htr, ← sum_eigenvalues_eq_trace hR]
  exact Finset.single_le_sum (f := hR.eigenvalues) (fun j _ => hp.eigenvalues_nonneg j)
    (Finset.mem_univ i)

/-- A cubic summed over a cut's spectrum. -/
theorem cutSum_cubicPoly {R : Mat4} (hR : R.IsHermitian) (a b c d : ℝ) :
    cutSum (cubicPoly a b c d) hR
      = a * (Matrix.trace (R * R * R)).re + b * (Matrix.trace (R * R)).re
        + c * (Matrix.trace R).re + 4 * d := by
  have e3 : ∑ i, hR.eigenvalues i ^ 3 = (Matrix.trace (R * R * R)).re := by
    rw [sum_eigenvalues_pow hR 3, pow_succ, pow_two]
  have e2 : ∑ i, hR.eigenvalues i ^ 2 = (Matrix.trace (R * R)).re := by
    rw [sum_eigenvalues_pow hR 2, pow_two]
  have e1 := sum_eigenvalues_eq_trace hR
  simp only [cutSum, cubicPoly, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [e3, e2, e1]
  simp

/-- On a spectrum in `{1/6, 1/2}` with trace `1` (i.e. `(1/2, 1/6, 1/6, 1/6)`), `tr f(R)` is
`f(1/2) + 3 f(1/6)`. -/
theorem cutSum_of_quadratic (f : ℝ → ℝ) {R : Mat4} (hR : R.IsHermitian)
    (h : (R - (1 / 6 : ℂ) • 1) * (R - (1 / 2 : ℂ) • 1) = 0) (htr : (Matrix.trace R).re = 1) :
    cutSum f hR = f (1 / 2) + 3 * f (1 / 6) := by
  set β := 3 * (f (1 / 2) - f (1 / 6))
  set α := f (1 / 6) - β / 6
  have hf : ∀ i, f (hR.eigenvalues i) = α + β * hR.eigenvalues i := by
    intro i
    rcases eigenvalue_of_quadratic hR h i with h1 | h1 <;> rw [h1]
    · simp only [α, β]; ring
    · simp only [α, β]; ring
  have hs : ∑ i, hR.eigenvalues i = 1 := by rw [sum_eigenvalues_eq_trace, htr]
  unfold cutSum
  simp only [hf, Finset.sum_add_distrib, ← Finset.mul_sum, hs]
  simp only [α, β]
  simp
  ring

theorem meanSpec_of_quadratics (f : ℝ → ℝ) {ψ : Psi} (hψ : normSqPsi ψ = 1) (hq : CutQuadratics ψ) :
    meanSpec f ψ = f (1 / 2) + 3 * f (1 / 6) := by
  have t12 : (Matrix.trace (red12 ψ)).re = 1 := by rw [trace_red12, hψ]; simp
  have t13 : (Matrix.trace (red13 ψ)).re = 1 := by rw [trace_red13, hψ]; simp
  have t14 : (Matrix.trace (red14 ψ)).re = 1 := by rw [trace_red14, hψ]; simp
  unfold meanSpec
  rw [cutSum_of_quadratic f _ hq.q12 t12, cutSum_of_quadratic f _ hq.q13 t13,
    cutSum_of_quadratic f _ hq.q14 t14]
  ring

/-- `E_f(M₄) = f(1/2) + 3 f(1/6)`. -/
theorem meanSpec_M4 (f : ℝ → ℝ) : meanSpec f M4 = f (1 / 2) + 3 * f (1 / 6) :=
  meanSpec_of_quadratics f M4_unit M4_cutQuadratics

/-- The hypotheses of the cubic-majorant criterion on `(f; a, b, c, d)`. -/
structure Majorant (f : ℝ → ℝ) (a b c d : ℝ) : Prop where
  ge : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x ≤ cubicPoly a b c d x
  node_sixth : cubicPoly a b c d (1 / 6) = f (1 / 6)
  node_half : cubicPoly a b c d (1 / 2) = f (1 / 2)

/-- The sum of the majorant's slack over all twelve eigenvalues. -/
noncomputable def majorantSlack (f : ℝ → ℝ) (a b c d : ℝ) (ψ : Psi) : ℝ :=
  ∑ i, (cubicPoly a b c d (((red12_herm ψ).eigenvalues i)) - f ((red12_herm ψ).eigenvalues i))
  + ∑ i, (cubicPoly a b c d (((red13_herm ψ).eigenvalues i)) - f ((red13_herm ψ).eigenvalues i))
  + ∑ i, (cubicPoly a b c d (((red14_herm ψ).eigenvalues i)) - f ((red14_herm ψ).eigenvalues i))

theorem majorantSlack_nonneg {f : ℝ → ℝ} {a b c d : ℝ} (hM : Majorant f a b c d) (ψ : Psi)
    (hψ : normSqPsi ψ = 1) : 0 ≤ majorantSlack f a b c d ψ := by
  have t12 : (Matrix.trace (red12 ψ)).re = 1 := by rw [trace_red12, hψ]; simp
  have t13 : (Matrix.trace (red13 ψ)).re = 1 := by rw [trace_red13, hψ]; simp
  have t14 : (Matrix.trace (red14 ψ)).re = 1 := by rw [trace_red14, hψ]; simp
  have key : ∀ {R : Mat4} (hR : R.IsHermitian), R.PosSemidef → (Matrix.trace R).re = 1 →
      0 ≤ ∑ i, (cubicPoly a b c d (hR.eigenvalues i) - f (hR.eigenvalues i)) := by
    intro R hR hp htr
    exact Finset.sum_nonneg fun i _ =>
      sub_nonneg.2 (hM.ge _ (eigenvalue_mem_Icc hR hp htr i))
  unfold majorantSlack
  have := key (red12_herm ψ) (red12_psd ψ) t12
  have := key (red13_herm ψ) (red13_psd ψ) t13
  have := key (red14_herm ψ) (red14_psd ψ) t14
  linarith

/-- **The gap identity (SF).**
`3 (E_f(M₄) - E_f(ψ)) = α (P - 1) + (a/12) F + Δ_f` with `α = -b - 17a/12`. -/
theorem majorant_gap {f : ℝ → ℝ} {a b c d : ℝ} (hM : Majorant f a b c d) (ψ : Psi)
    (hψ : normSqPsi ψ = 1) :
    3 * (meanSpec f M4 - meanSpec f ψ)
      = (-b - 17 * a / 12) * (purity ψ - 1) + a / 12 * sexticF ψ + majorantSlack f a b c d ψ := by
  have t12 : (Matrix.trace (red12 ψ)).re = 1 := by rw [trace_red12, hψ]; simp
  have t13 : (Matrix.trace (red13 ψ)).re = 1 := by rw [trace_red13, hψ]; simp
  have t14 : (Matrix.trace (red14 ψ)).re = 1 := by rw [trace_red14, hψ]; simp
  have c12 := cutSum_cubicPoly (red12_herm ψ) a b c d
  have c13 := cutSum_cubicPoly (red13_herm ψ) a b c d
  have c14 := cutSum_cubicPoly (red14_herm ψ) a b c d
  rw [t12] at c12
  rw [t13] at c13
  rw [t14] at c14
  have hs : majorantSlack f a b c d ψ
      = cutSum (cubicPoly a b c d) (red12_herm ψ) + cutSum (cubicPoly a b c d) (red13_herm ψ)
        + cutSum (cubicPoly a b c d) (red14_herm ψ)
        - (3 * meanSpec f ψ) := by
    unfold majorantSlack meanSpec cutSum
    simp only [Finset.sum_sub_distrib]
    ring
  have hT : sexticF ψ = 17 * purity ψ - 12 * cubicMoment ψ - 12 := by
    unfold sexticF; rw [hψ]; ring
  have n1 := hM.node_half
  have n2 := hM.node_sixth
  simp only [cubicPoly] at n1 n2
  have hf1 : f (1 / 2) + 3 * f (1 / 6) = 5 * a / 36 + b / 3 + c + 4 * d := by
    rw [← n1, ← n2]; ring
  have hsum : cutSum (cubicPoly a b c d) (red12_herm ψ) + cutSum (cubicPoly a b c d) (red13_herm ψ)
      + cutSum (cubicPoly a b c d) (red14_herm ψ)
      = a * cubicMoment ψ + b * purity ψ + 3 * c + 12 * d := by
    rw [c12, c13, c14]
    unfold cubicMoment purity
    ring
  rw [hs, meanSpec_M4, hf1]
  linear_combination (-1 : ℝ) * hsum - (a / 12) * hT

/-- **Cubic spectral majorants** (`prop:fqe-majorant`, inequality). If the cubic
`h = a x³ + b x² + c x + d` majorizes `f` on `[0,1]`, agrees with `f` at `1/6` and `1/2`, and
`a ≥ 0`, `b + 17a/12 ≤ 0`, then `E_f(ψ) ≤ E_f(M₄)` for every unit four-qubit vector. -/
theorem majorant_le {f : ℝ → ℝ} {a b c d : ℝ} (hM : Majorant f a b c d) (ha : 0 ≤ a)
    (hb : b + 17 * a / 12 ≤ 0) (ψ : Psi) (hψ : normSqPsi ψ = 1) :
    meanSpec f ψ ≤ meanSpec f M4 := by
  have g := majorant_gap hM ψ hψ
  have hP := purity_ge ψ
  rw [hψ] at hP
  have hF := sexticF_nonneg ψ
  have hs := majorantSlack_nonneg hM ψ hψ
  have k1 : 0 ≤ (-b - 17 * a / 12) * (purity ψ - 1) := mul_nonneg (by linarith) (by nlinarith)
  have k2 : 0 ≤ a / 12 * sexticF ψ := mul_nonneg (by linarith) hF
  linarith

/-- A local-unitary image of a vector with the cut quadratics has `E_f = f(1/2) + 3 f(1/6)`. -/
theorem meanSpec_of_LU (f : ℝ → ℝ) {φ ψ : Psi} (hφ : normSqPsi φ = 1) (hq : CutQuadratics φ)
    (h : LUEquiv φ ψ) : meanSpec f ψ = f (1 / 2) + 3 * f (1 / 6) := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
  exact meanSpec_of_quadratics f (by rw [normSqPsi_localApply ha hb hc hd, hφ])
    (hq.localApply ha hb hc hd)

/-- **Cubic spectral majorants, equality** (`prop:fqe-majorant`). Suppose in addition
`b + 17a/12 < 0` and that `h > f` on `[0,1]` away from the two nodes. Then `E_f(ψ) = E_f(M₄)`
exactly when `ψ` is local-unitarily equivalent to `M₄` or `conj M₄`.

(The paper needs no strict majorization, using instead the classification of the vectors with
`P = 1`, `F = 0`; that classification is not formalized.) -/
theorem majorant_eq_iff {f : ℝ → ℝ} {a b c d : ℝ} (hM : Majorant f a b c d) (ha : 0 ≤ a)
    (hb : b + 17 * a / 12 < 0)
    (hstrict : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≠ 1 / 6 → x ≠ 1 / 2 → f x < cubicPoly a b c d x)
    (ψ : Psi) (hψ : normSqPsi ψ = 1) :
    meanSpec f ψ = meanSpec f M4 ↔ LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ := by
  constructor
  · intro heq
    have g := majorant_gap hM ψ hψ
    have hP := purity_ge ψ
    rw [hψ] at hP
    have hF := sexticF_nonneg ψ
    have hs := majorantSlack_nonneg hM ψ hψ
    have k1 : 0 ≤ (-b - 17 * a / 12) * (purity ψ - 1) := mul_nonneg (by linarith) (by nlinarith)
    have k2 : 0 ≤ a / 12 * sexticF ψ := mul_nonneg (by linarith) hF
    rw [heq] at g
    have hP1 : purity ψ = 1 := by
      have : (-b - 17 * a / 12) * (purity ψ - 1) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (by linarith)
      · linarith
    have hs0 : majorantSlack f a b c d ψ = 0 := by linarith
    -- the slack on cut 12 vanishes
    have t12 : (Matrix.trace (red12 ψ)).re = 1 := by rw [trace_red12, hψ]; simp
    have t13 : (Matrix.trace (red13 ψ)).re = 1 := by rw [trace_red13, hψ]; simp
    have t14 : (Matrix.trace (red14 ψ)).re = 1 := by rw [trace_red14, hψ]; simp
    have key : ∀ {R : Mat4} (hR : R.IsHermitian), R.PosSemidef → (Matrix.trace R).re = 1 →
        0 ≤ ∑ i, (cubicPoly a b c d (hR.eigenvalues i) - f (hR.eigenvalues i)) := by
      intro R hR hp htr
      exact Finset.sum_nonneg fun i _ => sub_nonneg.2 (hM.ge _ (eigenvalue_mem_Icc hR hp htr i))
    have n12 := key (red12_herm ψ) (red12_psd ψ) t12
    have n13 := key (red13_herm ψ) (red13_psd ψ) t13
    have n14 := key (red14_herm ψ) (red14_psd ψ) t14
    unfold majorantSlack at hs0
    have z12 : ∑ i, (cubicPoly a b c d ((red12_herm ψ).eigenvalues i)
        - f ((red12_herm ψ).eigenvalues i)) = 0 := by linarith
    have hq : (red12 ψ - (1 / 6 : ℂ) • 1) * (red12 ψ - (1 / 2 : ℂ) • 1) = 0 := by
      apply quadratic_of_eigenvalues (red12_herm ψ)
      intro i
      have hterm : ∀ j ∈ Finset.univ, 0 ≤ cubicPoly a b c d ((red12_herm ψ).eigenvalues j)
          - f ((red12_herm ψ).eigenvalues j) := fun j _ =>
        sub_nonneg.2 (hM.ge _ (eigenvalue_mem_Icc _ (red12_psd ψ) t12 j))
      have hi := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 z12 i (Finset.mem_univ i)
      by_contra hne
      push_neg at hne
      have := hstrict _ (eigenvalue_mem_Icc _ (red12_psd ψ) t12 i) hne.1 hne.2
      linarith
    exact one_cut_rigidity_12 ψ hψ hP1 hq
  · rintro (h | h)
    · rw [meanSpec_of_LU f M4_unit M4_cutQuadratics h, meanSpec_M4]
    · rw [meanSpec_of_LU f (by rw [normSqPsi_conj]; exact M4_unit) M4_cutQuadratics.conj h,
        meanSpec_M4]

/-- info: 'FormalResearch.FourQubitEntropy.majorant_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sexticDefect_check._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms majorant_le

/-- info: 'FormalResearch.FourQubitEntropy.majorant_eq_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sexticDefect_check._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms majorant_eq_iff

end FormalResearch.FourQubitEntropy
