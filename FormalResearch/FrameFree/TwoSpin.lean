import Mathlib

/-!
# Two spins are chiral exactly from spin 1: the algebraic core

Theorem `thm:spinj` of `ResearchNotes/QI/antiunitary_occupation/paper/long/app_c_critical.tex`
(section *Two spins*). With `d = 2j + 1`, a two-spin state is a `d × d` complex matrix `M`, with
`J_{a,b} = (-1)^a` if `a + b = d - 1` and `0` otherwise, frames `M ↦ D₁ M D₂ᵀ` (here `Dᵀ J D = J`,
`det D = 1`, the complexified spin representation) and time reversal `Θ(M) = J M̄ Jᵀ`. The ratio
`I(M) = Tr(J Mᵀ J M)^d / (det M)^2` is formalized as `spinInv`.

Formalized here (all proved):
* `spinInv_frame`, `spinInv_phase`: `I` is invariant under frames and global phases (a);
* `spinInv_theta`: `I(Θ M) = conj (I M)`, for every `M` (b);
* `not_frame_equiv_of_im_ne`: if `I(M)` is not real then `Θ M ≠ e^{iα} D₁ M D₂ᵀ` for all frames (c);
* `spinInv_exM`, `spinInv_exM_real_iff`: for `M = diag(1,…,1,1+i)` and `d ≥ 2`,
  `I(M) = (d+2i)^d/(2i)`, real iff `d = 2` (Niven's theorem enters through `re_pow_ne_zero`) (d);
* `exM_chiral`: for `d ≥ 3` this `M` is chiral in the algebraic sense of (c) (e).

NOT formalized: (i) that the spin-`j` representation of `SU(2)` satisfies `Dᵀ J D = J` and `det D = 1`
(the hypotheses `IsFrame` are taken as given); (ii) the compactness/limit step turning "`FK = 1` or
`FC = 1`" into `Θ M = e^{iα} D₁ M D₂ᵀ` (resp. its closure); (iii) the paper's final claim that the
chiral states form an open dense set (real-analyticity of `Im I` on `{det M ≠ 0}` and the identity
theorem). Only the algebraic core is proved here.
-/

open scoped ComplexConjugate Matrix
open Matrix

namespace FormalResearch.FrameFree

/-- The antidiagonal sign matrix `J_{a,b} = (-1)^a` if `a + b = d - 1`, else `0`. -/
def Jmat (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun a b => if b = Fin.rev a then (-1 : ℂ) ^ (a : ℕ) else 0

theorem Jmat_apply_nat (d : ℕ) (a b : Fin d) :
    Jmat d a b = if (a : ℕ) + b + 1 = d then (-1 : ℂ) ^ (a : ℕ) else 0 := by
  simp only [Jmat, Matrix.of_apply, Fin.ext_iff, Fin.val_rev]
  have := a.isLt
  have := b.isLt
  congr 1
  apply propext
  omega

theorem Jmat_map_conj (d : ℕ) : (Jmat d).map conj = Jmat d := by
  ext a b
  simp only [Matrix.map_apply, Jmat, Matrix.of_apply]
  split_ifs <;> simp

theorem Jmat_transpose_mul (d : ℕ) : (Jmat d)ᵀ * Jmat d = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Jmat, Matrix.of_apply]
  rw [Finset.sum_eq_single (Fin.rev a)]
  · by_cases h : a = b
    · subst h; simp [← pow_add, ← two_mul, pow_mul]
    · have : b ≠ a := fun e => h e.symm
      simp [this, h]
  · intro c _ hc
    have : a ≠ Fin.rev c := fun h => hc (by rw [h]; simp)
    simp [this]
  · simp


section General

set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Frame invariance of the trace form. -/
theorem trace_frame (J M D₁ D₂ : Matrix n n ℂ)
    (h₁ : D₁ᵀ * J * D₁ = J) (h₂ : D₂ᵀ * J * D₂ = J) :
    trace (J * (D₁ * M * D₂ᵀ)ᵀ * J * (D₁ * M * D₂ᵀ)) = trace (J * Mᵀ * J * M) := by
  have e : J * (D₁ * M * D₂ᵀ)ᵀ * J * (D₁ * M * D₂ᵀ)
      = J * D₂ * Mᵀ * (D₁ᵀ * J * D₁) * M * D₂ᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [e, h₁]
  have e2 : J * D₂ * Mᵀ * J * M * D₂ᵀ = (J * D₂) * (Mᵀ * J * M) * D₂ᵀ := by
    simp only [Matrix.mul_assoc]
  rw [e2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  have e3 : D₂ᵀ * (J * D₂) = J := by rw [← Matrix.mul_assoc]; exact h₂
  rw [e3]
  simp only [Matrix.mul_assoc]

theorem trace_map_conj (A : Matrix n n ℂ) : trace (A.map conj) = conj (trace A) := by
  simp [Matrix.trace, map_sum]

theorem det_map_conj (A : Matrix n n ℂ) : det (A.map conj) = conj (det A) := by
  have := (starRingEnd ℂ).map_det A
  simpa [RingHom.mapMatrix_apply] using this.symm

/-- Time reversal conjugates the trace form (real orthogonal `J`). -/
theorem trace_theta (J M : Matrix n n ℂ) (hc : J.map conj = J) (ho : Jᵀ * J = 1) :
    trace (J * (J * M.map conj * Jᵀ)ᵀ * J * (J * M.map conj * Jᵀ))
      = conj (trace (J * Mᵀ * J * M)) := by
  have e : J * (J * M.map conj * Jᵀ)ᵀ * J * (J * M.map conj * Jᵀ)
      = (J * J * (M.map conj)ᵀ * (Jᵀ * J) * J * M.map conj) * Jᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [e, ho, Matrix.trace_mul_comm]
  have e2 : Jᵀ * (J * J * (M.map conj)ᵀ * 1 * J * M.map conj)
      = (Jᵀ * J) * J * (M.map conj)ᵀ * J * M.map conj := by
    simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [e2, ho, Matrix.one_mul, ← trace_map_conj]
  congr 1
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hc, Matrix.transpose_map]

theorem det_theta (J M : Matrix n n ℂ) (ho : Jᵀ * J = 1) :
    det (J * M.map conj * Jᵀ) = conj (det M) := by
  have h : det Jᵀ * det J = 1 := by rw [← Matrix.det_mul, ho, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul, det_map_conj]
  linear_combination (conj (det M)) * h

end General


/-- The time-reversal map `Θ(M) = J \bar M Jᵀ`. -/
noncomputable def theta (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Jmat d * M.map conj * (Jmat d)ᵀ

/-- Numerator of the invariant: `Tr(J Mᵀ J M)`. -/
def invNum (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) : ℂ := trace (Jmat d * Mᵀ * Jmat d * M)

/-- The frame invariant `I(M) = Tr(J Mᵀ J M)^d / (det M)^2`. -/
noncomputable def spinInv (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  (invNum d M) ^ d / (det M) ^ 2

/-- Frame condition `Dᵀ J D = J` (the complexified spin representation preserves `J`). -/
def IsFrame (d : ℕ) (D : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  Dᵀ * Jmat d * D = Jmat d ∧ det D = 1

section Invariance
variable {d : ℕ}

/-- (a) frame invariance of the numerator and the determinant. -/
theorem invNum_frame {D₁ D₂ : Matrix (Fin d) (Fin d) ℂ} (h₁ : IsFrame d D₁) (h₂ : IsFrame d D₂)
    (M : Matrix (Fin d) (Fin d) ℂ) :
    invNum d (D₁ * M * D₂ᵀ) = invNum d M ∧ det (D₁ * M * D₂ᵀ) = det M := by
  refine ⟨trace_frame _ _ _ _ h₁.1 h₂.1, ?_⟩
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h₁.2, h₂.2]
  ring

/-- (a) frame invariance of `I`. -/
theorem spinInv_frame {D₁ D₂ : Matrix (Fin d) (Fin d) ℂ} (h₁ : IsFrame d D₁) (h₂ : IsFrame d D₂)
    (M : Matrix (Fin d) (Fin d) ℂ) : spinInv d (D₁ * M * D₂ᵀ) = spinInv d M := by
  obtain ⟨h, h'⟩ := invNum_frame h₁ h₂ M
  simp only [spinInv, h, h']

/-- (a) a nonzero global scalar multiplies numerator and determinant. -/
theorem invNum_smul (c : ℂ) (M : Matrix (Fin d) (Fin d) ℂ) :
    invNum d (c • M) = c ^ 2 * invNum d M ∧ det (c • M) = c ^ d * det M := by
  refine ⟨?_, by simp⟩
  simp only [invNum, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    Matrix.trace_smul, smul_eq_mul]
  ring

/-- (a) invariance under a nonzero global scalar, in particular a phase. -/
theorem spinInv_smul {c : ℂ} (hc : c ≠ 0) (M : Matrix (Fin d) (Fin d) ℂ) :
    spinInv d (c • M) = spinInv d M := by
  obtain ⟨h, h'⟩ := invNum_smul c M
  simp only [spinInv, h, h', mul_pow, ← pow_mul]
  have : c ^ (2 * d) ≠ 0 := pow_ne_zero _ hc
  rw [mul_comm d 2, mul_div_mul_left _ _ this]

/-- (a) invariance under a global phase `e^{iα}`. -/
theorem spinInv_phase (α : ℝ) (M : Matrix (Fin d) (Fin d) ℂ) :
    spinInv d (Complex.exp (α * Complex.I) • M) = spinInv d M :=
  spinInv_smul (Complex.exp_ne_zero _) M

/-- (b) time reversal conjugates the numerator (no nondegeneracy needed). -/
theorem invNum_theta (M : Matrix (Fin d) (Fin d) ℂ) : invNum d (theta d M) = conj (invNum d M) := by
  unfold invNum theta
  rw [← trace_theta (Jmat d) M (Jmat_map_conj d) (Jmat_transpose_mul d)]

/-- (b) time reversal conjugates the determinant. -/
theorem det_theta' (M : Matrix (Fin d) (Fin d) ℂ) : det (theta d M) = conj (det M) :=
  det_theta _ M (Jmat_transpose_mul d)

/-- (b) `I(Θ M) = conj (I M)`; this holds for every `M` (division by zero gives `0` on both sides). -/
theorem spinInv_theta (M : Matrix (Fin d) (Fin d) ℂ) : spinInv d (theta d M) = conj (spinInv d M) := by
  simp only [spinInv, invNum_theta, det_theta', map_div₀, map_pow]

/-- (c) If `I(M)` is not real then `Θ M` is not a phase times a complexified frame image of `M`
(the algebraic core of chirality). -/
theorem not_frame_equiv_of_im_ne {M : Matrix (Fin d) (Fin d) ℂ} (h : (spinInv d M).im ≠ 0) :
    ¬ ∃ (D₁ D₂ : Matrix (Fin d) (Fin d) ℂ) (α : ℝ), IsFrame d D₁ ∧ IsFrame d D₂ ∧
      theta d M = Complex.exp (α * Complex.I) • (D₁ * M * D₂ᵀ) := by
  rintro ⟨D₁, D₂, α, h₁, h₂, he⟩
  have h1 : spinInv d (theta d M) = spinInv d M := by
    rw [he, spinInv_phase, spinInv_frame h₁ h₂]
  rw [spinInv_theta] at h1
  apply h
  have := congrArg Complex.im h1
  simp only [Complex.conj_im] at this
  linarith

end Invariance


section Example

theorem trace_J_diag (d : ℕ) (D : Fin d → ℂ) :
    trace (Jmat d * diagonal D * Jmat d * diagonal D)
      = ∑ a, (-1 : ℂ) ^ (d - 1) * (D a * D (Fin.rev a)) := by
  simp only [Matrix.trace, Matrix.diag_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Jmat, Matrix.of_apply]
  rw [Finset.sum_eq_single (Fin.rev a)]
  · have h1 : (-1 : ℂ) ^ (a : ℕ) * (-1 : ℂ) ^ ((Fin.rev a : Fin d) : ℕ) = (-1) ^ (d - 1) := by
      rw [← pow_add, Fin.val_rev]
      congr 1
      have := a.isLt
      omega
    simp only [ite_true, Fin.rev_rev]
    linear_combination (D a * D (Fin.rev a)) * h1
  · intro c _ hc
    have : c ≠ Fin.rev a := hc
    simp [this]
  · simp

/-- The example state `diag(1,…,1,1+i)`. -/
noncomputable def exM (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun a => if (a : ℕ) + 1 = d then 1 + Complex.I else 1

theorem exM_det {d : ℕ} (hd : 1 ≤ d) : det (exM d) = 1 + Complex.I := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have : ∀ a : Fin (n + 1), ((a : ℕ) + 1 = n + 1) ↔ a = Fin.last n := by
    intro a; rw [Fin.ext_iff]; simp
  have hf : (fun a : Fin (n + 1) => if (a : ℕ) + 1 = n + 1 then (1 + Complex.I) else 1)
      = fun a => if a = Fin.last n then 1 + Complex.I else 1 := by
    funext a; simp only [this a]
  rw [exM, Matrix.det_diagonal, hf]
  simp [Finset.prod_ite_eq']

theorem exM_trace {d : ℕ} (hd : 2 ≤ d) :
    invNum d (exM d) = (-1) ^ (d - 1) * ((d : ℂ) + 2 * Complex.I) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
  unfold invNum exM
  rw [Matrix.diagonal_transpose, trace_J_diag, ← Finset.mul_sum]
  congr 1
  have h : ∀ a : Fin (n + 2), ((if (a : ℕ) + 1 = n + 2 then 1 + Complex.I else 1)
      * (if ((Fin.rev a : Fin (n + 2)) : ℕ) + 1 = n + 2 then 1 + Complex.I else 1))
      = 1 + (if a = Fin.last (n + 1) then Complex.I else 0) + (if a = 0 then Complex.I else 0) := by
    intro a
    have h1 : ((a : ℕ) + 1 = n + 2) ↔ a = Fin.last (n + 1) := by rw [Fin.ext_iff]; simp
    have h2 : (((Fin.rev a : Fin (n + 2)) : ℕ) + 1 = n + 2) ↔ a = 0 := by
      have := a.isLt
      rw [Fin.ext_iff, Fin.val_rev, Fin.val_zero]; omega
    simp only [h1, h2]
    by_cases e1 : a = Fin.last (n + 1)
    · simp [e1]
    · by_cases e2 : a = 0
      · simp [e2]
      · simp [e1, e2]
  simp only [h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  push_cast
  simp
  ring

end Example


section Arithmetic

/-- Niven step: `Re (d + 2i)^d ≠ 0` for `d ≥ 3`. If it vanished then `((d+2i)/(d-2i))^(2d) = 1`,
so `(d²-4)/(d²+4) = cos (kπ/d)` is rational at a rational multiple of `π`, which Niven's theorem
excludes. -/
theorem re_pow_ne_zero {d : ℕ} (hd : 3 ≤ d) :
    (((d : ℂ) + 2 * Complex.I) ^ d).re ≠ 0 := by
  intro hre
  set w : ℂ := (d : ℂ) + 2 * Complex.I with hw
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hwb : conj w ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [hw] at this
    omega
  have h1 : w ^ d = - (conj w) ^ d := by
    have : conj (w ^ d) = - w ^ d := by
      apply Complex.ext
      · simp only [Complex.conj_re, Complex.neg_re, hre, neg_zero]
      · simp only [Complex.conj_im, Complex.neg_im]
    rw [map_pow] at this
    linear_combination this
  set z : ℂ := w / conj w with hz
  have hzd : z ^ d = -1 := by
    rw [hz, div_pow, h1, neg_div, div_self (pow_ne_zero _ hwb)]
  have hz2 : z ^ (2 * d) = 1 := by
    rw [mul_comm, pow_mul, hzd]; norm_num
  have : NeZero (2 * d) := ⟨by omega⟩
  obtain ⟨i, -, hi⟩ := (Complex.isPrimitiveRoot_exp (2 * d) (by omega)).eq_pow_of_pow_eq_one hz2
  have hzre : z.re = ((d : ℝ) ^ 2 - 4) / ((d : ℝ) ^ 2 + 4) := by
    have hpos : (d : ℝ) ^ 2 + 4 ≠ 0 := by positivity
    simp only [hz, hw, Complex.div_re, Complex.normSq_apply]
    simp
    field_simp
    ring
  have hexp : Complex.exp (2 * Real.pi * Complex.I / ((2 * d : ℕ) : ℂ)) ^ i
      = Complex.exp (((i * Real.pi / d : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    have : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    push_cast
    field_simp
  rw [hexp] at hi
  have hi := congrArg Complex.re hi
  rw [Complex.exp_ofReal_mul_I_re] at hi
  have hc : Real.cos (i * Real.pi / d) = ((d : ℝ) ^ 2 - 4) / ((d : ℝ) ^ 2 + 4) := by
    rw [← hzre, ← hi]
  have hn := niven (θ := i * Real.pi / d) ⟨(i : ℚ) / d, by push_cast; ring⟩
    ⟨((d : ℚ) ^ 2 - 4) / ((d : ℚ) ^ 2 + 4), by rw [hc]; push_cast; rfl⟩
  rw [hc] at hn
  have hpos : (d : ℝ) ^ 2 + 4 ≠ 0 := by positivity
  have hsq : (9 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with h | h | h | h | h
  · field_simp at h; nlinarith
  · field_simp at h; nlinarith
  · field_simp at h; nlinarith
  · field_simp at h
    have h12 : d * d = 12 := by
      have : (d : ℝ) * d = 12 := by nlinarith
      exact_mod_cast this
    have : d ≤ 4 := by nlinarith
    interval_cases d <;> omega
  · field_simp at h; nlinarith

end Arithmetic


section ExampleResult

theorem spinInv_exM {d : ℕ} (hd : 2 ≤ d) :
    spinInv d (exM d) = ((d : ℂ) + 2 * Complex.I) ^ d / (2 * Complex.I) := by
  unfold spinInv
  rw [exM_trace hd, exM_det (by omega), mul_pow, ← pow_mul]
  have : (-1 : ℂ) ^ ((d - 1) * d) = 1 := by
    apply Even.neg_one_pow
    rw [mul_comm]
    exact Nat.even_mul_pred_self d
  rw [this, one_mul]
  congr 1
  rw [sq]
  apply Complex.ext <;> norm_num

theorem div_two_I_im (x : ℂ) : (x / (2 * Complex.I)).im = - x.re / 2 := by
  simp [Complex.div_im]
  ring

/-- `I(M) = 4` for `d = 2`, in particular real. -/
theorem spinInv_exM_two : spinInv 2 (exM 2) = 4 := by
  rw [spinInv_exM le_rfl]
  apply Complex.ext
  · simp [pow_two, Complex.div_re]; norm_num
  · simp [pow_two, Complex.div_im]

/-- (d) For `d ≥ 2`, `I(diag(1,…,1,1+i))` is real iff `d = 2`. -/
theorem spinInv_exM_real_iff {d : ℕ} (hd : 2 ≤ d) : (spinInv d (exM d)).im = 0 ↔ d = 2 := by
  constructor
  · intro h
    by_contra hne
    rw [spinInv_exM hd, div_two_I_im] at h
    exact re_pow_ne_zero (d := d) (by omega) (by linarith)
  · rintro rfl
    rw [spinInv_exM_two]
    simp

/-- (e) For `d ≥ 3` the matrix `diag(1,…,1,1+i)` is not related to its time reversal by a phase
and complexified frames: it is chiral in the algebraic sense. -/
theorem exM_chiral {d : ℕ} (hd : 3 ≤ d) :
    ¬ ∃ (D₁ D₂ : Matrix (Fin d) (Fin d) ℂ) (α : ℝ), IsFrame d D₁ ∧ IsFrame d D₂ ∧
      theta d (exM d) = Complex.exp (α * Complex.I) • (D₁ * exM d * D₂ᵀ) :=
  not_frame_equiv_of_im_ne (fun h => by
    have := (spinInv_exM_real_iff (d := d) (by omega)).mp h
    omega)

end ExampleResult

end FormalResearch.FrameFree

