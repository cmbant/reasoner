import Mathlib
import FormalResearch.QIB.TwoQubitsGroup

/-!
# Direction `L2`: the algebra of `Lc H₁, Lc E₁, Lc F₁` contains the collective `SU(2)` in its bicommutant

Namespace `FormalResearch.QIB.TwoQubits`.  Claim class: **proved** (finite linear algebra).

* `su2_decomp`: every `u ∈ SU(2)` is `V diag(z, z⁻¹) W` with `V W = 1 = W V` (explicit eigenvectors; the
  repeated-eigenvalue case is excluded by unitarity);
* `commGroup_of_commute_Lc` (`L2`): a matrix commuting with `Lc H₁, Lc E₁, Lc F₁` commutes with `rotK d u`
  for every `u ∈ SU(2)`.  Proof: conjugate by `rotK V`; the weight operator `Lc H₁` is diagonal, and a
  matrix commuting with a diagonal operator commutes with every function of it, in particular with
  `rotK d (diag(z, z⁻¹))`.  No exponentials or analysis.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Matrix
open FormalResearch.FrameFree.NQubit (SU2 Op1)
open FormalResearch.FrameFree.Helstrom

namespace FormalResearch.QIB.TwoQubits

theorem su2_entries {u : Op1} (hu : SU2 u) :
    u 1 1 = (starRingEnd ℂ) (u 0 0) ∧ u 0 1 = -(starRingEnd ℂ) (u 1 0) ∧
    (starRingEnd ℂ) (u 0 0) * u 0 0 + (starRingEnd ℂ) (u 1 0) * u 1 0 = 1 := by
  obtain ⟨h1, h2⟩ := hu
  have hdet : u 0 0 * u 1 1 - u 0 1 * u 1 0 = 1 := by rw [← h2, Matrix.det_fin_two]
  have e : ∀ i j, (uᴴ * u) i j = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := fun i j => by rw [h1]
  have e00 := e 0 0
  have e01 := e 0 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, conjTranspose_apply, Matrix.one_apply] at e00 e01
  simp at e00 e01
  generalize u 0 0 = p at *
  generalize u 0 1 = q at *
  generalize u 1 0 = r at *
  generalize u 1 1 = s at *
  refine ⟨?_, ?_, e00⟩
  · linear_combination (-s) * e00 + ((starRingEnd ℂ) p) * hdet + r * e01
  · linear_combination (-(starRingEnd ℂ) r) * hdet + p * e01 - q * e00

theorem eig_mat (p q r s z z' : ℂ) (hdet : p * s - q * r = 1) (hsum : z + z' = p + s)
    (hprod : z * z' = 1) :
    (!![p, q; r, s] : Matrix (Fin 2) (Fin 2) ℂ) * !![q, q; z - p, z' - p]
      = !![q, q; z - p, z' - p] * !![z, 0; 0, z'] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ring
  · ring
  · linear_combination (-1 : ℂ) * hdet - z * hsum + hprod
  · linear_combination (-1 : ℂ) * hdet - z' * hsum + hprod

theorem su2_trace_sq_ne {u : Op1} (hu : SU2 u) (hr : u 1 0 ≠ 0) :
    (u 0 0 + u 1 1) * (u 0 0 + u 1 1) - 4 ≠ 0 := by
  obtain ⟨hs, hq, hn⟩ := su2_entries hu
  intro h
  rw [hs] at h
  have h1 : (u 0 0 + (starRingEnd ℂ) (u 0 0)) = ((2 * (u 0 0).re : ℝ) : ℂ) := by
    rw [Complex.add_conj]
  rw [h1] at h
  have h2 : (2 * (u 0 0).re) * (2 * (u 0 0).re) = 4 := by
    have : (((2 * (u 0 0).re) * (2 * (u 0 0).re) : ℝ) : ℂ) = ((4 : ℝ) : ℂ) := by
      push_cast at h ⊢; linear_combination h
    exact_mod_cast this
  have h3 : Complex.normSq (u 0 0) + Complex.normSq (u 1 0) = 1 := by
    have : ((Complex.normSq (u 0 0) + Complex.normSq (u 1 0) : ℝ) : ℂ) = 1 := by
      push_cast
      rw [← Complex.mul_conj, ← Complex.mul_conj, mul_comm (u 0 0), mul_comm (u 1 0)]
      exact hn
    exact_mod_cast this
  have h4 : 0 < Complex.normSq (u 1 0) := Complex.normSq_pos.2 hr
  have h5 := Complex.normSq_apply (u 0 0)
  nlinarith [sq_nonneg (u 0 0).im]

theorem su2_decomp {u : Op1} (hu : SU2 u) :
    ∃ V W : Op1, ∃ z : ℂ, V * W = 1 ∧ W * V = 1 ∧ z ≠ 0 ∧ u = V * Dz z * W := by
  have hdet : u 0 0 * u 1 1 - u 0 1 * u 1 0 = 1 := by rw [← hu.2, Matrix.det_fin_two]
  obtain ⟨hs, hq, hn⟩ := su2_entries hu
  by_cases hr : u 1 0 = 0
  · have hq0 : u 0 1 = 0 := by rw [hq, hr]; simp
    have hps : u 0 0 * u 1 1 = 1 := by rw [hq0, hr] at hdet; simpa using hdet
    have hp : u 0 0 ≠ 0 := by intro h; rw [h] at hps; simp at hps
    refine ⟨1, 1, u 0 0, by simp, by simp, hp, ?_⟩
    have h1 : u 1 1 = (u 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hps
    rw [Matrix.one_mul, Matrix.mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Dz, hq0, hr, h1]
  · have hq0 : u 0 1 ≠ 0 := by rw [hq]; simpa using hr
    obtain ⟨σ, hσ⟩ := IsAlgClosed.exists_pow_nat_eq ((u 0 0 + u 1 1) * (u 0 0 + u 1 1) - 4) (n := 2)
      (by norm_num)
    have hσ0 : σ ≠ 0 := by
      rintro rfl
      exact su2_trace_sq_ne hu hr (by simpa using hσ.symm)
    obtain ⟨z, z', hsum, hprod, hne⟩ : ∃ z z' : ℂ, z + z' = u 0 0 + u 1 1 ∧ z * z' = 1 ∧ z' - z = -σ := by
      refine ⟨((u 0 0 + u 1 1) + σ) / 2, ((u 0 0 + u 1 1) - σ) / 2, by ring, ?_, by ring⟩
      linear_combination (-1 / 4 : ℂ) * hσ
    have hz0 : z ≠ 0 := by rintro rfl; simp at hprod
    have hz' : z' = z⁻¹ := eq_inv_of_mul_eq_one_right hprod
    set V : Op1 := !![u 0 1, u 0 1; z - u 0 0, z' - u 0 0] with hV
    have hdV : V.det = u 0 1 * (-σ) := by
      rw [hV, Matrix.det_fin_two]; simp; linear_combination (u 0 1) * hne
    have hVu : IsUnit V.det := by
      rw [hdV]; exact (mul_ne_zero hq0 (neg_ne_zero.2 hσ0)).isUnit
    refine ⟨V, V⁻¹, z, Matrix.mul_nonsing_inv V hVu, Matrix.nonsing_inv_mul V hVu, hz0, ?_⟩
    have hm := eig_mat (u 0 0) (u 0 1) (u 1 0) (u 1 1) z z' hdet hsum hprod
    rw [← Matrix.eta_fin_two u] at hm
    have hD : Dz z = !![z, 0; 0, z'] := by rw [hz']; rfl
    rw [hD]
    calc u = u * (V * V⁻¹) := by rw [Matrix.mul_nonsing_inv V hVu, Matrix.mul_one]
      _ = (u * V) * V⁻¹ := by rw [Matrix.mul_assoc]
      _ = V * !![z, 0; 0, z'] * V⁻¹ := by rw [hV, hm]

section L2

variable {d : ℕ}

theorem rotK_one : rotK d (fun _ : Fin 2 => (1 : Op1)) = 1 := by
  simp only [rotK, kron_one]

theorem rotK_mul_const (V W : Op1) :
    rotK d (fun _ : Fin 2 => V) * rotK d (fun _ : Fin 2 => W) = rotK d (fun _ : Fin 2 => V * W) :=
  rotK_mul d _ _

theorem commute_conj_fwd {ι : Type*} [Fintype ι] [DecidableEq ι] {M X RV RW : Matrix ι ι ℂ}
    (h1 : RV * RW = 1) (h : Commute M X) : Commute (RW * M * RV) (RW * X * RV) := by
  have e : ∀ A B : Matrix ι ι ℂ, (RW * A * RV) * (RW * B * RV) = RW * (A * B) * RV := by
    intro A B
    calc (RW * A * RV) * (RW * B * RV) = RW * A * (RV * RW) * B * RV := by
          simp only [Matrix.mul_assoc]
      _ = RW * (A * B) * RV := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  show (RW * M * RV) * (RW * X * RV) = (RW * X * RV) * (RW * M * RV)
  rw [e, e, h.eq]

theorem commute_conj_bwd {ι : Type*} [Fintype ι] [DecidableEq ι] {M D RV RW : Matrix ι ι ℂ}
    (h1 : RV * RW = 1) (h2 : RW * RV = 1) (h : Commute (RW * M * RV) D) :
    Commute M (RV * D * RW) := by
  have e : ∀ A B : Matrix ι ι ℂ, (RV * A * RW) * (RV * B * RW) = RV * (A * B) * RW := by
    intro A B
    calc (RV * A * RW) * (RV * B * RW) = RV * A * (RW * RV) * B * RW := by
          simp only [Matrix.mul_assoc]
      _ = RV * (A * B) * RW := by rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hM : RV * (RW * M * RV) * RW = M := by
    calc RV * (RW * M * RV) * RW = (RV * RW) * M * (RV * RW) := by simp only [Matrix.mul_assoc]
      _ = M := by rw [h1, Matrix.one_mul, Matrix.mul_one]
  rw [← hM]
  show (RV * (RW * M * RV) * RW) * (RV * D * RW) = (RV * D * RW) * (RV * (RW * M * RV) * RW)
  rw [e, e, h.eq]

/-- **`L2`.**  A matrix commuting with `Lc H₁`, `Lc E₁`, `Lc F₁` commutes with the collective
`SU(2)`. -/
theorem commGroup_of_commute_Lc {M : Matrix (Copies 2 d) (Copies 2 d) ℂ}
    (h1 : Commute M (Lc d H1)) (h2 : Commute M (Lc d E1)) (h3 : Commute M (Lc d F1)) :
    CommGroup d M := by
  intro u hu
  obtain ⟨V, W, z, hVW, hWV, hz, rfl⟩ := su2_decomp hu
  have hsl : ∀ A : Matrix (Fin 2) (Fin 2) ℂ, A 0 0 + A 1 1 = 0 → Commute M (Lc d A) := by
    intro A hA
    have e : A = A 0 0 • H1 + A 0 1 • E1 + A 1 0 • F1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [H1, E1, F1]
      linear_combination hA
    rw [e, Lc_add, Lc_add, Lc_smul, Lc_smul, Lc_smul]
    exact ((h1.smul_right _).add_right (h2.smul_right _)).add_right (h3.smul_right _)
  have hRVW : rotK d (fun _ : Fin 2 => V) * rotK d (fun _ : Fin 2 => W) = 1 := by
    rw [rotK_mul_const, hVW, rotK_one]
  have hRWV : rotK d (fun _ : Fin 2 => W) * rotK d (fun _ : Fin 2 => V) = 1 := by
    rw [rotK_mul_const, hWV, rotK_one]
  have hA : Commute M (Lc d (V * H1 * W)) := by
    apply hsl
    have := Matrix.trace_fin_two (V * H1 * W)
    rw [← this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hWV, Matrix.one_mul]
    simp [Matrix.trace_fin_two, H1]
  have e : rotK d (fun _ : Fin 2 => W) * Lc d (V * H1 * W) * rotK d (fun _ : Fin 2 => V)
      = Lc d H1 := by
    rw [← Lc_conj V W H1 hVW]
    calc rotK d (fun _ : Fin 2 => W) * (rotK d (fun _ : Fin 2 => V) * Lc d H1 *
          rotK d (fun _ : Fin 2 => W)) * rotK d (fun _ : Fin 2 => V)
        = (rotK d (fun _ : Fin 2 => W) * rotK d (fun _ : Fin 2 => V)) * Lc d H1 *
          (rotK d (fun _ : Fin 2 => W) * rotK d (fun _ : Fin 2 => V)) := by
          simp only [Matrix.mul_assoc]
      _ = Lc d H1 := by rw [hRWV, Matrix.one_mul, Matrix.mul_one]
  have hN : Commute (rotK d (fun _ : Fin 2 => W) * M * rotK d (fun _ : Fin 2 => V)) (Lc d H1) := by
    have := commute_conj_fwd hRVW hA
    rwa [e] at this
  rw [Lc_H1] at hN
  have hD : Commute (rotK d (fun _ : Fin 2 => W) * M * rotK d (fun _ : Fin 2 => V))
      (rotK d (fun _ : Fin 2 => Dz z)) := by
    rw [rotK_Dz z hz]
    exact comm_diagonal_of_level _ _ _
      (fun x y hxy => by
        have : wt x = wt y := by exact_mod_cast hxy
        rw [this]) hN.eq
  have := commute_conj_bwd hRVW hRWV hD
  rwa [rotK_mul_const, rotK_mul_const] at this

end L2

end FormalResearch.QIB.TwoQubits
