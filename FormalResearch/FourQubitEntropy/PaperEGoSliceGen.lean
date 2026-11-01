import FormalResearch.FourQubitEntropy.PaperEGoSliceOrbit

/-!
# `thm:fqe-global-overlap`, layer (b): the height inequality for an arbitrary frame

`PaperEGoSliceConstr` states the height inequality on the slice.  Here the same inequality is proved for an
arbitrary state `φ` whose magic coordinates are `√3 X + i Y` (`CoordIs φ X Y`) with `X, Y` any real `4 × 4`
matrices, so that it can be applied before the slice normal form is reached:

* `ip_orbitG`, `re_ip_orbitG`: the overlap with `e · P Z_* Qᵀ` in real form;
* `IsFrame.hgt_eq`: `3 X₀₀ + Σ_{k≥1} Y_kk = √6 h`;
* `height_ineqG`: `c (3 A₀₀ + Σ B_kk) + 3 s (B₀₀ - Σ A_kk) ≤ 3 X₀₀ + Σ Y_kk`, `A = Pᵀ X Q`, `B = Pᵀ Y Q`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.GO
open CO OD PaperECritical

noncomputable section

abbrev M4R := Matrix (Fin 4) (Fin 4) ℝ

/-- The complex entry `√3 X_ij + i Y_ij`. -/
def ZcG (X Y : M4R) (i j : Fin 4) : ℂ :=
  ((Real.sqrt 3 * X i j : ℝ) : ℂ) + Complex.I * ((Y i j : ℝ) : ℂ)

/-- The magic coordinates of `φ` are `√3 X + i Y`. -/
def CoordIs (φ : Psi) (X Y : M4R) : Prop :=
  ∀ p q : Fin 2 × Fin 2, magicCoord (zmat φ) p q = ZcG X Y (pairIdx p) (pairIdx q)

/-- `3 X₀₀ + Σ_{k≥1} Y_kk`, the real height of `Z_*` (`= h₀` on the slice). -/
def hgt (X Y : M4R) : ℝ := 3 * X 0 0 + ∑ k : Fin 3, Y k.succ k.succ

theorem etaC0_0' : etaC 0 0 = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by
  have e0 : epsOf 0 = ![0, 1, 1, 1] := rfl
  simp [etaC, idxI, e0]

theorem etaC0_pos (j : Fin 4) (hj : j ≠ 0) :
    etaC 0 j = Complex.I * ((1 / Real.sqrt 6 : ℝ) : ℂ) := by
  have e0 : epsOf 0 = ![0, 1, 1, 1] := rfl
  fin_cases j
  · exact absurd rfl hj
  all_goals simp [etaC, idxI, e0]

theorem sqrt_factsG : Real.sqrt 6 * (1 / Real.sqrt 2) = Real.sqrt 3 ∧
    Real.sqrt 6 * (1 / Real.sqrt 6) = 1 ∧ Real.sqrt 3 * Real.sqrt 3 = 3 := by
  have h6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have h6p : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  refine ⟨?_, ?_, Real.mul_self_sqrt (by norm_num)⟩
  · rw [h6]; field_simp
  · field_simp

theorem ip_orbitG (φ : Psi) (X Y : M4R) (hφ : CoordIs φ X Y) (P Q : M4R) (e : ℂ) (χ : Psi)
    (hc : ∀ p q : Fin 2 × Fin 2, magicCoord (zmat χ) p q =
      e * ∑ k : Fin 4, (P (pairIdx p) k : ℂ) * etaC 0 k * (Q (pairIdx q) k : ℂ)) :
    ip χ φ = (starRingEnd ℂ) e * ∑ k : Fin 4, (starRingEnd ℂ) (etaC 0 k) *
      (((Real.sqrt 3 * (Pᵀ * X * Q) k k : ℝ) : ℂ) +
        Complex.I * (((Pᵀ * Y * Q) k k : ℝ) : ℂ)) := by
  rw [ip_coord]
  set F : Fin 4 → Fin 4 → ℂ := fun i j =>
    (starRingEnd ℂ) (e * ∑ k : Fin 4, (P i k : ℂ) * etaC 0 k * (Q j k : ℂ)) * ZcG X Y i j with hF
  have e1 : ∀ p q : Fin 2 × Fin 2, (starRingEnd ℂ) (magicCoord (zmat χ) p q) *
      magicCoord (zmat φ) p q = F (pairIdx p) (pairIdx q) := by
    intro p q
    rw [hc, hφ]
  simp only [e1]
  have hS : ∑ p : Fin 2 × Fin 2, ∑ q : Fin 2 × Fin 2, F (pairIdx p) (pairIdx q) =
      ∑ i, ∑ j, F i j := by
    rw [← sum_pairG (fun i => ∑ j, F i j)]
    exact Finset.sum_congr rfl fun p _ => sum_pairG (F (pairIdx p))
  rw [hS]
  simp only [hF, ZcG, Fin.sum_univ_four, map_mul, map_add, Matrix.mul_apply, Matrix.transpose_apply,
    Complex.conj_ofReal]
  push_cast
  ring

theorem re_ip_orbitG (φ : Psi) (X Y : M4R) (hφ : CoordIs φ X Y) (P Q : M4R) (c s : ℝ) (χ : Psi)
    (hc : ∀ p q : Fin 2 × Fin 2, magicCoord (zmat χ) p q =
      ((c : ℂ) + ((Real.sqrt 3 * s : ℝ) : ℂ) * Complex.I) *
        ∑ k : Fin 4, (P (pairIdx p) k : ℂ) * etaC 0 k * (Q (pairIdx q) k : ℂ)) :
    Real.sqrt 6 * (ip χ φ).re =
      c * (3 * (Pᵀ * X * Q) 0 0 + ∑ k : Fin 3, (Pᵀ * Y * Q) k.succ k.succ) +
        3 * s * ((Pᵀ * Y * Q) 0 0 - ∑ k : Fin 3, (Pᵀ * X * Q) k.succ k.succ) := by
  obtain ⟨hk2, hk6, hk3⟩ := sqrt_factsG
  rw [← Complex.re_ofReal_mul, ip_orbitG φ X Y hφ P Q _ χ hc]
  have hk0 : ((Real.sqrt 6 : ℝ) : ℂ) * (starRingEnd ℂ) (etaC 0 0) = ((Real.sqrt 3 : ℝ) : ℂ) := by
    rw [etaC0_0', Complex.conj_ofReal]; exact_mod_cast hk2
  have hk1 : ∀ j : Fin 4, j ≠ 0 → ((Real.sqrt 6 : ℝ) : ℂ) * (starRingEnd ℂ) (etaC 0 j) =
      -Complex.I := by
    intro j hj
    rw [etaC0_pos j hj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    have h6 : ((Real.sqrt 6 : ℝ) : ℂ) * ((1 / Real.sqrt 6 : ℝ) : ℂ) = 1 := by exact_mod_cast hk6
    linear_combination (-Complex.I) * h6
  set T : Fin 4 → ℂ := fun k => ((Real.sqrt 3 * (Pᵀ * X * Q) k k : ℝ) : ℂ) +
        Complex.I * (((Pᵀ * Y * Q) k k : ℝ) : ℂ) with hT
  have key : ((Real.sqrt 6 : ℝ) : ℂ) * ((starRingEnd ℂ) ((c : ℂ) + ((Real.sqrt 3 * s : ℝ) : ℂ) * Complex.I) *
      ∑ k : Fin 4, (starRingEnd ℂ) (etaC 0 k) * T k) =
      (starRingEnd ℂ) ((c : ℂ) + ((Real.sqrt 3 * s : ℝ) : ℂ) * Complex.I) *
        (((Real.sqrt 3 : ℝ) : ℂ) * T 0 - Complex.I * (T 1 + T 2 + T 3)) := by
    simp only [Fin.sum_univ_four]
    have h1 := hk1 1 (by decide)
    have h2 := hk1 2 (by decide)
    have h3 := hk1 3 (by decide)
    linear_combination ((starRingEnd ℂ) ((c : ℂ) + ((Real.sqrt 3 * s : ℝ) : ℂ) * Complex.I)) *
      (T 0 * hk0 + T 1 * h1 + T 2 * h2 + T 3 * h3)
  rw [key]
  simp only [hT, Fin.sum_univ_three, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    show ((2 : Fin 3).succ : Fin 4) = 3 from rfl, map_add, map_mul, Complex.conj_ofReal,
    Complex.conj_I, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  linear_combination (c * (Pᵀ * X * Q) 0 0 + s * ((Pᵀ * Y * Q) 0 0 -
    ((Pᵀ * X * Q) 1 1 + (Pᵀ * X * Q) 2 2 + (Pᵀ * X * Q) 3 3))) * hk3

/-- `⟨Z_*, φ⟩ = h` gives `3 X₀₀ + Σ Y_kk = √6 h`. -/
theorem IsFrame.hgt_eq {φ : Psi} {h : ℝ} (hf : IsFrame φ h) {X Y : M4R} (hφ : CoordIs φ X Y) :
    hgt X Y = Real.sqrt 6 * h := by
  obtain ⟨-, -, hip, -⟩ := hf
  have hc : ∀ p q : Fin 2 × Fin 2, magicCoord (zmat (Gv (etaV 0))) p q =
      (((1 : ℝ) : ℂ) + ((Real.sqrt 3 * 0 : ℝ) : ℂ) * Complex.I) *
        ∑ k : Fin 4, ((1 : M4R) (pairIdx p) k : ℂ) * etaC 0 k * ((1 : M4R) (pairIdx q) k : ℂ) := by
    intro p q
    rw [coord_of_eq (zmat_Gv (etaV 0))]
    have hs : ∑ k : Fin 4, ((1 : M4R) (pairIdx p) k : ℂ) * etaC 0 k *
        ((1 : M4R) (pairIdx q) k : ℂ) = if p = q then etaC 0 (pairIdx p) else 0 := by
      by_cases hpq : p = q
      · subst hpq
        rw [Finset.sum_eq_single (pairIdx p)]
        · simp
        · intro k _ hk; simp [Matrix.one_apply, Ne.symm hk]
        · simp
      · have hne : pairIdx p ≠ pairIdx q := fun h => hpq (pairIdx_bij.1 h)
        refine (Finset.sum_eq_zero fun k _ => ?_).trans (by simp [hpq])
        by_cases h1 : pairIdx p = k
        · subst h1; simp [Matrix.one_apply, Ne.symm hne]
        · simp [Matrix.one_apply, h1]
    rw [hs]
    simp [Matrix.diagonal_apply, etaV_zero_eq]
  have := re_ip_orbitG φ X Y hφ 1 1 1 0 (Gv (etaV 0)) (by simpa using hc)
  rw [hip] at this
  simp only [Complex.ofReal_re, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at this
  simp only [hgt]
  simp at this ⊢
  linarith

theorem height_ineqG {φ : Psi} {h : ℝ} (hf : IsFrame φ h) {X Y : M4R} (hφ : CoordIs φ X Y)
    (P Q : M4R) (hP : Pᵀ * P = 1) (hQ : Qᵀ * Q = 1) (c s : ℝ)
    (hcs : c ^ 2 + 3 * s ^ 2 = 1) :
    c * (3 * (Pᵀ * X * Q) 0 0 + ∑ k : Fin 3, (Pᵀ * Y * Q) k.succ k.succ) +
      3 * s * ((Pᵀ * Y * Q) 0 0 - ∑ k : Fin 3, (Pᵀ * X * Q) k.succ k.succ) ≤ hgt X Y := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have he : Complex.normSq ((c : ℂ) + ((Real.sqrt 3 * s : ℝ) : ℂ) * Complex.I) = 1 := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    nlinarith [h3]
  obtain ⟨χ, hχ, hc⟩ := orbit_mem4 P Q hP hQ _ he
  have h1 := hf.re_le hχ
  have h2 := re_ip_orbitG φ X Y hφ P Q c s χ hc
  rw [hf.hgt_eq hφ]
  have h6 : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  rw [← h2]
  exact mul_le_mul_of_nonneg_left h1 h6.le

/-! ### Axiom audit -/

/-- info: 'FormalResearch.FourQubitEntropy.GO.height_ineqG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms height_ineqG

end

end FormalResearch.FourQubitEntropy.GO
