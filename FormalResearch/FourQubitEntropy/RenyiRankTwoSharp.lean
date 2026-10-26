import FormalResearch.FourQubitEntropy.RenyiRankTwo
import FormalResearch.FourQubitEntropy.TsallisSharp

/-!
# Sharpness of the rank-two Rényi envelope: the cluster-to-Bell family

The critical normal-form vectors `G(v)`, `v = (√a, i√(1-a), 0, 0)`, i.e.
`ψ_{x,y} = ½ Σ (x [a=b][c=d] − i y [a≠b][c≠d]) |abcd⟩` with `x² + y² = 1`, have balanced cut
spectra `(x², y², 0, 0)`, `(1/4)⁴`, `(1/4)⁴`; this family joins the cluster state (`x² = 1/2`) to
the product of two Bell pairs (`x = 1`). They attain the bound of `prop:fqe-renyi-rank-two`
(renyi_above_one.tex, `eq:fqe-quadratic-family`) for every `a ∈ [0,1]` and every order `q > 0`.
-/

open scoped ComplexConjugate Matrix ComplexOrder

namespace FormalResearch.FourQubitEntropy

open Real

/-- A Hermitian `R` with `R (R - α)(R - β) = 0` has all eigenvalues in `{0, α, β}`. -/
theorem eigenvalue_of_cubic {R : Mat4} (hR : R.IsHermitian) {α β : ℝ}
    (h : R * (R - (α : ℂ) • 1) * (R - (β : ℂ) • 1) = 0) (i : Fin 2 × Fin 2) :
    hR.eigenvalues i = 0 ∨ hR.eigenvalues i = α ∨ hR.eigenvalues i = β := by
  have hv0 := hR.mulVec_eigenvectorBasis i
  set v : Fin 2 × Fin 2 → ℂ := ⇑(hR.eigenvectorBasis i) with hvdef
  have hv : R *ᵥ v = ((hR.eigenvalues i : ℝ) : ℂ) • v := by
    rw [hv0]; exact (Complex.coe_smul _ _).symm
  have hne : v ≠ 0 := by
    have := hR.eigenvectorBasis.orthonormal.ne_zero i
    intro h0; apply this; ext j; exact congrFun h0 j
  set μ : ℂ := ((hR.eigenvalues i : ℝ) : ℂ) with hμ
  have key : (μ * (μ - α) * (μ - β)) • v = 0 := by
    have e1 : (R - (β : ℂ) • 1) *ᵥ v = (μ - β) • v := by
      rw [Matrix.sub_mulVec, hv, Matrix.smul_mulVec, Matrix.one_mulVec]; module
    have e2 : (R - (α : ℂ) • 1) *ᵥ ((μ - β) • v) = ((μ - α) * (μ - β)) • v := by
      rw [Matrix.mulVec_smul, Matrix.sub_mulVec, hv, Matrix.smul_mulVec, Matrix.one_mulVec]
      module
    have e3 : R *ᵥ (((μ - α) * (μ - β)) • v) = (μ * ((μ - α) * (μ - β))) • v := by
      rw [Matrix.mulVec_smul, hv, smul_smul]; ring_nf
    have : (R * (R - (α : ℂ) • 1) * (R - (β : ℂ) • 1)) *ᵥ v = 0 := by rw [h, Matrix.zero_mulVec]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e1, e2, e3] at this
    rw [show μ * (μ - α) * (μ - β) = μ * ((μ - α) * (μ - β)) by ring]; exact this
  rcases smul_eq_zero.mp key with hz | hz
  · rcases mul_eq_zero.mp hz with h12 | h3
    · rcases mul_eq_zero.mp h12 with h1 | h2
      · left
        have h' : ((hR.eigenvalues i : ℝ) : ℂ) = 0 := h1
        exact_mod_cast h'
      · right; left
        have h' : ((hR.eigenvalues i : ℝ) : ℂ) = (α : ℂ) := sub_eq_zero.mp h2
        exact_mod_cast h'
    · right; right
      have h' : ((hR.eigenvalues i : ℝ) : ℂ) = (β : ℂ) := sub_eq_zero.mp h3
      exact_mod_cast h'
  · exact absurd hz hne

/-- **Spectral sum on a rank-two cut.** If `R` is Hermitian with `R (R-a)(R-b) = 0`,
`tr R = 1 = a + b` and `tr R² = a² + b²` (`a, b ≥ 0`), then for every `f` with `f 0 = 0`,
`Σ_i f(λ_i) = f(a) + f(b)`. -/
theorem cutSum_rank_two {R : Mat4} (hR : R.IsHermitian) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (h : R * (R - (a : ℂ) • 1) * (R - (b : ℂ) • 1) = 0)
    (htr : (Matrix.trace R).re = 1) (htr2 : (Matrix.trace (R * R)).re = a ^ 2 + b ^ 2)
    (f : ℝ → ℝ) (hf : f 0 = 0) : ∑ i, f (hR.eigenvalues i) = f a + f b := by
  have hs1 : ∑ i, hR.eigenvalues i = 1 := by rw [sum_eigenvalues_eq_trace, htr]
  have hs2 : ∑ i, hR.eigenvalues i ^ 2 = a ^ 2 + b ^ 2 := by
    rw [sum_eigenvalues_pow hR 2, pow_two, htr2]
  have hmem := eigenvalue_of_cubic hR h
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    subst hb0; subst ha1
    have : ∀ i, f (hR.eigenvalues i) = f 1 * hR.eigenvalues i := by
      intro i; rcases hmem i with h | h | h <;> rw [h] <;> simp [hf]
    simp only [this, ← Finset.mul_sum, hs1]; simp [hf]
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    subst ha0; subst hb1
    have : ∀ i, f (hR.eigenvalues i) = f 1 * hR.eigenvalues i := by
      intro i; rcases hmem i with h | h | h <;> rw [h] <;> simp [hf]
    simp only [this, ← Finset.mul_sum, hs1]; simp [hf]
  by_cases hab' : a = b
  · have ha2 : a = 1 / 2 := by linarith
    subst hab'
    have : ∀ i, f (hR.eigenvalues i) = 2 * f a * hR.eigenvalues i := by
      intro i
      rcases hmem i with h | h | h <;> rw [h]
      · simp [hf]
      · rw [ha2]; ring
      · rw [ha2]; ring
    simp only [this, ← Finset.mul_sum, hs1]; ring
  have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hsub : a - b ≠ 0 := sub_ne_zero.2 hab'
  obtain ⟨u, hu⟩ : ∃ u, u * a = f a := ⟨f a / a, by field_simp⟩
  obtain ⟨v, hv⟩ : ∃ v, v * b = f b := ⟨f b / b, by field_simp⟩
  obtain ⟨B, hB⟩ : ∃ B, B * (a - b) = u - v := ⟨(u - v) / (a - b), by field_simp⟩
  have key : ∀ i, f (hR.eigenvalues i) = (u - B * a) * hR.eigenvalues i + B * hR.eigenvalues i ^ 2 := by
    intro i
    rcases hmem i with h | h | h <;> rw [h]
    · simp [hf]
    · linear_combination (-1 : ℝ) * hu
    · linear_combination b * hB - hv
  simp only [key, Finset.sum_add_distrib, ← Finset.mul_sum, hs1, hs2]
  have hb' : a = 1 - b := by linarith
  subst hb'
  linear_combination (-b) * hB + hu + hv

/-! ### The family -/

/-- The cluster-to-Bell family `ψ_{x,y} = ½ Σ (x [a=b][c=d] − i y [a≠b][c≠d]) |abcd⟩`. -/
noncomputable def quadFam (x y : ℝ) : Psi := fun a b c d =>
  (if a = b ∧ c = d then (x : ℂ) / 2 else 0) + (if a ≠ b ∧ c ≠ d then -(Complex.I * y) / 2 else 0)

theorem normSqPsi_quadFam (x y : ℝ) : normSqPsi (quadFam x y) = x ^ 2 + y ^ 2 := by
  simp [normSqPsi, quadFam, Fin.sum_univ_two, Complex.normSq_apply]
  ring

theorem red12_quadFam (x y : ℝ) : red12 (quadFam x y) = Matrix.of fun i j =>
    (if i.1 = i.2 ∧ j.1 = j.2 then ((x : ℂ) ^ 2) / 2 else 0)
      + (if i.1 ≠ i.2 ∧ j.1 ≠ j.2 then ((y : ℂ) ^ 2) / 2 else 0) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp [red12, quadFam, Fin.sum_univ_two, map_ofNat, map_neg, map_div₀] <;> (try ring_nf) <;> (try simp) <;> (try ring)

theorem red13_quadFam (x y : ℝ) :
    red13 (quadFam x y) = ((((x ^ 2 + y ^ 2) / 4 : ℝ)) : ℂ) • (1 : Mat4) := by
  ext ⟨a, c⟩ ⟨a', c'⟩
  fin_cases a <;> fin_cases c <;> fin_cases a' <;> fin_cases c' <;>
    simp [red13, quadFam, Fin.sum_univ_two, Matrix.one_apply, map_ofNat, map_neg, map_div₀] <;> (try ring_nf) <;> (try simp) <;> (try ring)

theorem red14_quadFam (x y : ℝ) :
    red14 (quadFam x y) = ((((x ^ 2 + y ^ 2) / 4 : ℝ)) : ℂ) • (1 : Mat4) := by
  ext ⟨a, d⟩ ⟨a', d'⟩
  fin_cases a <;> fin_cases d <;> fin_cases a' <;> fin_cases d' <;>
    simp [red14, quadFam, Fin.sum_univ_two, Matrix.one_apply, map_ofNat, map_neg, map_div₀] <;> (try ring_nf) <;> (try simp) <;> (try ring)

theorem red12_quadFam_cubic (x y : ℝ) :
    red12 (quadFam x y) * (red12 (quadFam x y) - ((x ^ 2 : ℝ) : ℂ) • 1)
      * (red12 (quadFam x y) - ((y ^ 2 : ℝ) : ℂ) • 1) = 0 := by
  rw [red12_quadFam]
  ext ⟨a, b⟩ ⟨a', b'⟩
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two] <;> (try ring_nf) <;> (try simp) <;> (try ring)

theorem trace_red12_quadFam (x y : ℝ) : Matrix.trace (red12 (quadFam x y)) = ((x ^ 2 + y ^ 2 : ℝ) : ℂ) := by
  rw [trace_red12, normSqPsi_quadFam]

theorem trace_sq_red12_quadFam (x y : ℝ) :
    (Matrix.trace (red12 (quadFam x y) * red12 (quadFam x y))).re = (x ^ 2) ^ 2 + (y ^ 2) ^ 2 := by
  rw [red12_quadFam]
  simp [Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring_nf
  rw [show ((x : ℂ) ^ 2) = ((x ^ 2 : ℝ) : ℂ) by push_cast; ring,
    show ((y : ℂ) ^ 2) = ((y ^ 2 : ℝ) : ℂ) by push_cast; ring]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem eigenvalues_of_scalar {R : Mat4} (hR : R.IsHermitian) (h : R = (((1 / 4 : ℝ)) : ℂ) • (1 : Mat4)) :
    ∀ i, hR.eigenvalues i = 1 / 4 := by
  have hq : (R - (((1 / 4 : ℝ)) : ℂ) • 1) * (R - (((1 / 4 : ℝ)) : ℂ) • 1) = 0 := by
    rw [h]; simp
  intro i
  rcases eigenvalue_of_quadratic' hR hq i with h | h <;> exact h

theorem quadFam_unit {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1) : normSqPsi (quadFam x y) = 1 := by
  rw [normSqPsi_quadFam, hxy]

theorem quadFam_eig13 {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1) :
    ∀ i, (red13_herm (quadFam x y)).eigenvalues i = 1 / 4 :=
  eigenvalues_of_scalar _ (by rw [red13_quadFam, hxy])

theorem quadFam_eig14 {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1) :
    ∀ i, (red14_herm (quadFam x y)).eigenvalues i = 1 / 4 :=
  eigenvalues_of_scalar _ (by rw [red14_quadFam, hxy])

/-- On the family the first cut has `Σ f(λ) = f(x²) + f(y²)` for every `f` with `f 0 = 0`. -/
theorem quadFam_cutSum12 {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1) (f : ℝ → ℝ) (hf : f 0 = 0) :
    ∑ i, f ((red12_herm (quadFam x y)).eigenvalues i) = f (x ^ 2) + f (y ^ 2) := by
  refine cutSum_rank_two (red12_herm (quadFam x y)) (sq_nonneg x) (sq_nonneg y) hxy
    (red12_quadFam_cubic x y) ?_ (trace_sq_red12_quadFam x y) f hf
  rw [trace_red12_quadFam, hxy]; simp

/-- **Sharpness of `prop:fqe-renyi-rank-two`** (`eq:fqe-quadratic-family`): for every `a = x² ∈ [0,1]`
and every order `q > 0`, `q ≠ 1`, the family vector `ψ_{x,y}` (cut spectra `(a, 1-a, 0, 0)`, `(1/4)⁴`,
`(1/4)⁴`) attains `E_q = 4/3 + H_q(a, 1-a)/3`. -/
theorem renyi_rank_two_sharp {q x y : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) (hxy : x ^ 2 + y ^ 2 = 1) :
    normSqPsi (quadFam x y) = 1 ∧
    meanRenyi q (quadFam x y) = 4 / 3 + renyiBin q (x ^ 2) / 3 := by
  have hy : y ^ 2 = 1 - x ^ 2 := by linarith
  have h12 : renyiSpec q (red12_herm (quadFam x y)).eigenvalues = renyiBin q (x ^ 2) := by
    rw [renyiBin_eq]; unfold renyiSpec
    rw [quadFam_cutSum12 hxy (fun t => t ^ q) (Real.zero_rpow hq0.ne'), hy]
  have h13 : renyiSpec q (red13_herm (quadFam x y)).eigenvalues = 2 :=
    (renyiSpec_eq_two_iff hq0 hq1 (isProb13 (quadFam_unit hxy))).2 (quadFam_eig13 hxy)
  have h14 : renyiSpec q (red14_herm (quadFam x y)).eigenvalues = 2 :=
    (renyiSpec_eq_two_iff hq0 hq1 (isProb14 (quadFam_unit hxy))).2 (quadFam_eig14 hxy)
  refine ⟨quadFam_unit hxy, ?_⟩
  simp only [meanRenyi, renyiCut_eq_renyiSpec, h12, h13, h14]; ring

/-- The von Neumann case of the sharpness. -/
theorem entropy_rank_two_sharp {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1) :
    meanEntropy (quadFam x y) = 4 / 3 + entBin (x ^ 2) / 3 := by
  have hy : y ^ 2 = 1 - x ^ 2 := by linarith
  have h12 : entSpec (red12_herm (quadFam x y)).eigenvalues = entBin (x ^ 2) := by
    rw [entBin_eq]; unfold entSpec
    rw [quadFam_cutSum12 hxy Real.negMulLog Real.negMulLog_zero, hy]
  have h13 : entSpec (red13_herm (quadFam x y)).eigenvalues = 2 :=
    (entSpec_eq_two_iff (isProb13 (quadFam_unit hxy))).2 (quadFam_eig13 hxy)
  have h14 : entSpec (red14_herm (quadFam x y)).eigenvalues = 2 :=
    (entSpec_eq_two_iff (isProb14 (quadFam_unit hxy))).2 (quadFam_eig14 hxy)
  simp only [meanEntropy, vnEntropy_eq_entSpec, h12, h13, h14]; ring

/-- info: 'FormalResearch.FourQubitEntropy.renyi_rank_two_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms renyi_rank_two_sharp

/-- info: 'FormalResearch.FourQubitEntropy.entropy_rank_two_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entropy_rank_two_sharp

end FormalResearch.FourQubitEntropy
