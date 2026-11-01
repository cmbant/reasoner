import FormalResearch.FourQubitEntropy.PaperEGoSliceOrbit

/-!
# `thm:fqe-global-overlap`, layer (d): the positive constraints at a closest point

Proved from `IsFrame` (a closest point of `𝓜` at `Z_*`): the height inequality `height_ineq` of
`PaperEGoSliceOrbit` gives

* `K₀, K₁ ⪰ 0` (one-factor Procrustes, `K0_psd`, `K1_psd`: reflections `I - 2 w wᵀ/|w|²`),
* every lower-frame matrix `L_{σ₀,σ,c,s} ⪰ 0` (`L_psd`: the Householder-rotated HS matrices of the
  paper, with the completeness of the Householder frame replacing explicit coordinates),
* `h₀ ≥ 0`, `e ≥ 0`, the rays `g_η ≥ 0` (`SliceConstraints.rays`),
* `B₀ ⪰ 0` from the fidelity floor `fidelity_floor` (`B0_psd`).

The height Hessian `H ⪰ 0` is **not** proved here: `FrameHess` is the named hypothesis, and
`frame_constraints` assembles `SliceConstraints` from it.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.GO
open CO OD PaperECritical

noncomputable section

/-! ### The slice matrix entries -/

def Zc (v : SV) (i j : Fin 4) : ℂ :=
  ((Real.sqrt 3 * sX v i j : ℝ) : ℂ) + Complex.I * ((sY v i j : ℝ) : ℂ)

theorem sZ_eq (v : SV) (p q : Fin 2 × Fin 2) : sZ v p q = Zc v (pairIdx p) (pairIdx q) := rfl

theorem etaC0_0 : etaC 0 0 = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by
  have e0 : epsOf 0 = ![0, 1, 1, 1] := rfl
  simp [etaC, idxI, e0]

theorem etaC0_1 : etaC 0 1 = Complex.I * ((1 / Real.sqrt 6 : ℝ) : ℂ) := by
  have e0 : epsOf 0 = ![0, 1, 1, 1] := rfl
  simp [etaC, idxI, e0]

theorem etaC0_2 : etaC 0 2 = Complex.I * ((1 / Real.sqrt 6 : ℝ) : ℂ) := by
  have e0 : epsOf 0 = ![0, 1, 1, 1] := rfl
  simp [etaC, idxI, e0]

theorem etaC0_3 : etaC 0 3 = Complex.I * ((1 / Real.sqrt 6 : ℝ) : ℂ) := by
  have e0 : epsOf 0 = ![0, 1, 1, 1] := rfl
  simp [etaC, idxI, e0]

theorem sqrt_facts : Real.sqrt 6 * (1 / Real.sqrt 2) = Real.sqrt 3 ∧
    Real.sqrt 6 * (1 / Real.sqrt 6) = 1 ∧ Real.sqrt 3 * Real.sqrt 3 = 3 := by
  have h6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have h6p : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  refine ⟨?_, ?_, Real.mul_self_sqrt (by norm_num)⟩
  · rw [h6]; field_simp
  · field_simp

/-! ### Overlaps with an orbit element, in real form -/

theorem ip_orbit (v : SV) (P Q : Matrix (Fin 4) (Fin 4) ℝ) (e : ℂ) (χ : Psi)
    (hc : ∀ p q : Fin 2 × Fin 2, magicCoord (zmat χ) p q =
      e * ∑ k : Fin 4, (P (pairIdx p) k : ℂ) * etaC 0 k * (Q (pairIdx q) k : ℂ)) :
    ip χ (sState v) = (starRingEnd ℂ) e * ∑ k : Fin 4, (starRingEnd ℂ) (etaC 0 k) *
      (((Real.sqrt 3 * (Pᵀ * sX v * Q) k k : ℝ) : ℂ) +
        Complex.I * (((Pᵀ * sY v * Q) k k : ℝ) : ℂ)) := by
  rw [ip_coord]
  set F : Fin 4 → Fin 4 → ℂ := fun i j =>
    (starRingEnd ℂ) (e * ∑ k : Fin 4, (P i k : ℂ) * etaC 0 k * (Q j k : ℂ)) * Zc v i j with hF
  have e1 : ∀ p q : Fin 2 × Fin 2, (starRingEnd ℂ) (magicCoord (zmat χ) p q) *
      magicCoord (zmat (sState v)) p q = F (pairIdx p) (pairIdx q) := by
    intro p q
    rw [hc, magicCoord_sState]
    rfl
  simp only [e1]
  have hS : ∑ p : Fin 2 × Fin 2, ∑ q : Fin 2 × Fin 2, F (pairIdx p) (pairIdx q) =
      ∑ i, ∑ j, F i j := by
    rw [← sum_pairG (fun i => ∑ j, F i j)]
    exact Finset.sum_congr rfl fun p _ => sum_pairG (F (pairIdx p))
  rw [hS]
  simp only [hF, Zc, Fin.sum_univ_four, map_mul, map_add, Matrix.mul_apply, Matrix.transpose_apply,
    Complex.conj_ofReal]
  push_cast
  ring

theorem re_ip_orbit (v : SV) (P Q : Matrix (Fin 4) (Fin 4) ℝ) (c s : ℝ) (χ : Psi)
    (hc : ∀ p q : Fin 2 × Fin 2, magicCoord (zmat χ) p q =
      ((c : ℂ) + ((Real.sqrt 3 * s : ℝ) : ℂ) * Complex.I) *
        ∑ k : Fin 4, (P (pairIdx p) k : ℂ) * etaC 0 k * (Q (pairIdx q) k : ℂ)) :
    Real.sqrt 6 * (ip χ (sState v)).re =
      c * (3 * (Pᵀ * sX v * Q) 0 0 + ∑ k : Fin 3, (Pᵀ * sY v * Q) k.succ k.succ) +
        3 * s * ((Pᵀ * sY v * Q) 0 0 - ∑ k : Fin 3, (Pᵀ * sX v * Q) k.succ k.succ) := by
  obtain ⟨hk2, hk6, hk3⟩ := sqrt_facts
  rw [← Complex.re_ofReal_mul, ip_orbit v P Q _ χ hc]
  have hk0 : ((Real.sqrt 6 : ℝ) : ℂ) * (starRingEnd ℂ) (etaC 0 0) = ((Real.sqrt 3 : ℝ) : ℂ) := by
    rw [etaC0_0, Complex.conj_ofReal]; exact_mod_cast hk2
  have hk1 : ∀ j : Fin 4, j ≠ 0 → ((Real.sqrt 6 : ℝ) : ℂ) * (starRingEnd ℂ) (etaC 0 j) =
      -Complex.I := by
    intro j hj
    have : etaC 0 j = Complex.I * ((1 / Real.sqrt 6 : ℝ) : ℂ) := by
      fin_cases j
      · exact absurd rfl hj
      · exact etaC0_1
      · exact etaC0_2
      · exact etaC0_3
    rw [this, map_mul, Complex.conj_ofReal, Complex.conj_I]
    have h6 : ((Real.sqrt 6 : ℝ) : ℂ) * ((1 / Real.sqrt 6 : ℝ) : ℂ) = 1 := by exact_mod_cast hk6
    linear_combination (-Complex.I) * h6
  set T : Fin 4 → ℂ := fun k => ((Real.sqrt 3 * (Pᵀ * sX v * Q) k k : ℝ) : ℂ) +
        Complex.I * (((Pᵀ * sY v * Q) k k : ℝ) : ℂ) with hT
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
  linear_combination (c * (Pᵀ * sX v * Q) 0 0 + s * ((Pᵀ * sY v * Q) 0 0 -
    ((Pᵀ * sX v * Q) 1 1 + (Pᵀ * sX v * Q) 2 2 + (Pᵀ * sX v * Q) 3 3))) * hk3


/-! ### The height inequality on the slice -/

/-- `⟨Z_*, φ⟩ = h` gives `h₀ = √6 h`. -/
theorem IsFrame.sH0_eq {v : SV} {h : ℝ} (hf : IsFrame (sState v) h) :
    sH0 v = Real.sqrt 6 * h := by
  obtain ⟨-, -, hip, -⟩ := hf
  have hc : ∀ p q : Fin 2 × Fin 2, magicCoord (zmat (Gv (etaV 0))) p q =
      (((1 : ℝ) : ℂ) + ((Real.sqrt 3 * 0 : ℝ) : ℂ) * Complex.I) *
        ∑ k : Fin 4, ((1 : Matrix (Fin 4) (Fin 4) ℝ) (pairIdx p) k : ℂ) * etaC 0 k *
          ((1 : Matrix (Fin 4) (Fin 4) ℝ) (pairIdx q) k : ℂ) := by
    intro p q
    rw [coord_of_eq (zmat_Gv (etaV 0))]
    have hs : ∑ k : Fin 4, ((1 : Matrix (Fin 4) (Fin 4) ℝ) (pairIdx p) k : ℂ) * etaC 0 k *
        ((1 : Matrix (Fin 4) (Fin 4) ℝ) (pairIdx q) k : ℂ) =
        if p = q then etaC 0 (pairIdx p) else 0 := by
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
  have := re_ip_orbit v 1 1 1 0 (Gv (etaV 0)) (by simpa using hc)
  rw [hip] at this
  simp only [Complex.ofReal_re, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at this
  simp [sH0, sX, sY, Fin.sum_univ_three] at this ⊢
  linarith

theorem height_ineq {v : SV} {h : ℝ} (hf : IsFrame (sState v) h)
    (P Q : Matrix (Fin 4) (Fin 4) ℝ) (hP : Pᵀ * P = 1) (hQ : Qᵀ * Q = 1) (c s : ℝ)
    (hcs : c ^ 2 + 3 * s ^ 2 = 1) :
    c * (3 * (Pᵀ * sX v * Q) 0 0 + ∑ k : Fin 3, (Pᵀ * sY v * Q) k.succ k.succ) +
      3 * s * ((Pᵀ * sY v * Q) 0 0 - ∑ k : Fin 3, (Pᵀ * sX v * Q) k.succ k.succ) ≤ sH0 v := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have he : Complex.normSq ((c : ℂ) + ((Real.sqrt 3 * s : ℝ) : ℂ) * Complex.I) = 1 := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    nlinarith [h3]
  obtain ⟨χ, hχ, hc⟩ := orbit_mem4 P Q hP hQ _ he
  have h1 := hf.re_le hχ
  have h2 := re_ip_orbit v P Q c s χ hc
  rw [hf.sH0_eq]
  have h6 : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  rw [← h2]
  exact mul_le_mul_of_nonneg_left h1 h6.le

/-! ### Reflections: `K₀` and `K₁` -/

/-- The reflection `I - 2 w wᵀ/|w|²`. -/
def reflMat (w : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => (if i = j then 1 else 0) - 2 * w i * w j / (∑ k, w k ^ 2)

theorem reflMat_orth {w : Fin 4 → ℝ} (hN : ∑ k, w k ^ 2 ≠ 0) :
    (reflMat w)ᵀ * reflMat w = 1 := by
  simp only [Fin.sum_univ_four] at hN
  ext i j
  simp only [reflMat, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Fin.sum_univ_four, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

theorem sum_sq_zero {m : ℕ} {w : Fin m → ℝ} (h : ∑ k, w k ^ 2 = 0) : ∀ k, w k = 0 := by
  intro k
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (w i))).1 h k (Finset.mem_univ k)
  exact pow_eq_zero_iff (two_ne_zero) |>.1 this

theorem nonneg_of_pos_mul {N S : ℝ} (hN : 0 < N) (h : 0 ≤ 2 / N * S) : 0 ≤ S := by
  by_contra hneg
  push_neg at hneg
  have : 2 / N * S < 0 := mul_neg_of_pos_of_neg (by positivity) hneg
  linarith

theorem K0_psd {v : SV} {h : ℝ} (hf : IsFrame (sState v) h) : QF (sK0 v) := by
  intro w
  by_cases hN : ∑ k, w k ^ 2 = 0
  · have := sum_sq_zero hN
    simp [this]
  · have hpos : 0 < ∑ k, w k ^ 2 := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _)
      (Ne.symm hN)
    have hI := height_ineq hf (reflMat w) 1 (reflMat_orth hN) (by simp) 1 0 (by norm_num)
    have key : sH0 v - (1 * (3 * ((reflMat w)ᵀ * sX v * (1 : Matrix (Fin 4) (Fin 4) ℝ)) 0 0 +
        ∑ k : Fin 3, ((reflMat w)ᵀ * sY v * (1 : Matrix (Fin 4) (Fin 4) ℝ)) k.succ k.succ) +
        3 * 0 * (((reflMat w)ᵀ * sY v * (1 : Matrix (Fin 4) (Fin 4) ℝ)) 0 0 -
          ∑ k : Fin 3, ((reflMat w)ᵀ * sX v * (1 : Matrix (Fin 4) (Fin 4) ℝ)) k.succ k.succ))
        = 2 / (∑ k, w k ^ 2) * (∑ i, ∑ j, w i * sK0 v i j * w j) := by
      have hN' : (∑ k, w k ^ 2) ≠ 0 := hN
      simp only [Fin.sum_univ_four] at hN'
      simp only [Matrix.mul_one]
      simp [reflMat, sK0, sX, sY, sH0, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]
      field_simp
      ring
    exact nonneg_of_pos_mul hpos (by linarith)

theorem K1_psd {v : SV} {h : ℝ} (hf : IsFrame (sState v) h) : QF (sK1 v) := by
  intro w
  by_cases hN : ∑ k, w k ^ 2 = 0
  · have := sum_sq_zero hN
    simp [this]
  · have hpos : 0 < ∑ k, w k ^ 2 := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _)
      (Ne.symm hN)
    have hI := height_ineq hf 1 (reflMat w) (by simp) (reflMat_orth hN) 1 0 (by norm_num)
    have key : sH0 v - (1 * (3 * ((1 : Matrix (Fin 4) (Fin 4) ℝ)ᵀ * sX v * reflMat w) 0 0 +
        ∑ k : Fin 3, ((1 : Matrix (Fin 4) (Fin 4) ℝ)ᵀ * sY v * reflMat w) k.succ k.succ) +
        3 * 0 * (((1 : Matrix (Fin 4) (Fin 4) ℝ)ᵀ * sY v * reflMat w) 0 0 -
          ∑ k : Fin 3, ((1 : Matrix (Fin 4) (Fin 4) ℝ)ᵀ * sX v * reflMat w) k.succ k.succ))
        = 2 / (∑ k, w k ^ 2) * (∑ i, ∑ j, w i * sK1 v i j * w j) := by
      have hN' : (∑ k, w k ^ 2) ≠ 0 := hN
      simp only [Fin.sum_univ_four] at hN'
      simp only [Matrix.transpose_one, Matrix.one_mul]
      simp [reflMat, sK1, sX, sY, sH0, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]
      field_simp
      ring
    exact nonneg_of_pos_mul hpos (by linarith)

/-! ### The lower-frame matrices -/

def swap01 : Matrix (Fin 4) (Fin 4) ℝ := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

def sgD (σ₀ σ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1, σ₀, σ, σ]

theorem swap01_orth : swap01ᵀ * swap01 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swap01, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem sgD_orth {σ₀ σ : ℝ} (h0 : σ₀ * σ₀ = 1) (h1 : σ * σ = 1) :
    (sgD σ₀ σ)ᵀ * sgD σ₀ σ = 1 := by
  unfold sgD
  rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, h0, h1]

theorem diag_swap (σ₀ σ : ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    (swap01ᵀ * M * swap01 * sgD σ₀ σ) 0 0 = M 1 1 ∧
    (swap01ᵀ * M * swap01 * sgD σ₀ σ) 1 1 = σ₀ * M 0 0 ∧
    (swap01ᵀ * M * swap01 * sgD σ₀ σ) 2 2 = σ * M 2 2 ∧
    (swap01ᵀ * M * swap01 * sgD σ₀ σ) 3 3 = σ * M 3 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [swap01, sgD, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply] <;> ring

/-- A Householder-completed frame: an orthogonal `G` with first column `e₀` and second column
`(0, u)`. -/
theorem exists_frame_G (u : Fin 3 → ℝ) (hu : ∑ k, u k ^ 2 = 1) :
    ∃ G : Matrix (Fin 4) (Fin 4) ℝ, Gᵀ * G = 1 ∧ (∀ a, G a 0 = if a = 0 then 1 else 0) ∧
      (∀ a, G a 1 = ![0, u 0, u 1, u 2] a) := by
  simp only [Fin.sum_univ_three] at hu
  by_cases h : u 0 = 1
  · have h1 : u 1 = 0 := by nlinarith [sq_nonneg (u 1), sq_nonneg (u 2)]
    have h2 : u 2 = 0 := by nlinarith [sq_nonneg (u 1), sq_nonneg (u 2)]
    refine ⟨1, by simp, fun a => ?_, fun a => ?_⟩
    · simp [Matrix.one_apply]
    · fin_cases a <;> simp [Matrix.one_apply, h, h1, h2]
  · have hN2 : ∑ k, (![0, 1 - u 0, -u 1, -u 2] : Fin 4 → ℝ) k ^ 2 = 2 - 2 * u 0 := by
      simp [Fin.sum_univ_four]; nlinarith
    have hne : (2 - 2 * u 0) ≠ 0 := by intro h'; apply h; linarith
    refine ⟨reflMat ![0, 1 - u 0, -u 1, -u 2], reflMat_orth (by rw [hN2]; exact hne),
      fun a => ?_, fun a => ?_⟩
    · fin_cases a <;> simp [reflMat]
    · fin_cases a <;> simp [reflMat, hN2] <;> field_simp <;> ring

theorem psd2 {a b c x y : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hb : b ^ 2 ≤ a * c) :
    0 ≤ a * x ^ 2 + 2 * b * x * y + c * y ^ 2 := by
  by_cases ha0 : a = 0
  · subst ha0
    have hb0 : b = 0 := by nlinarith [sq_nonneg b]
    subst hb0
    nlinarith [sq_nonneg y]
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    by_contra hneg
    push_neg at hneg
    nlinarith [sq_nonneg (a * x + b * y), sq_nonneg y, mul_nonneg ha (sq_nonneg y)]

theorem L_unit_psd {v : SV} {h : ℝ} (hf : IsFrame (sState v) h) {σ₀ σ c s : ℝ}
    (hσ₀ : σ₀ = 1 ∨ σ₀ = -1) (hσ : σ = 1 ∨ σ = -1) (hcs : c ^ 2 + 3 * s ^ 2 = 1)
    (u : Fin 3 → ℝ) (hu : ∑ k, u k ^ 2 = 1) :
    0 ≤ ∑ j, ∑ k, u j * sL v σ₀ σ c s j k * u k := by
  obtain ⟨G, hG, hG0, hG1⟩ := exists_frame_G u hu
  have hGG : G * Gᵀ = 1 := mul_eq_one_comm.1 hG
  have h0 : σ₀ * σ₀ = 1 := by rcases hσ₀ with h | h <;> simp [h]
  have h1 : σ * σ = 1 := by rcases hσ with h | h <;> simp [h]
  have hP : (G * swap01)ᵀ * (G * swap01) = 1 := by
    rw [Matrix.transpose_mul]
    calc swap01ᵀ * Gᵀ * (G * swap01) = swap01ᵀ * (Gᵀ * G) * swap01 := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hG, Matrix.mul_one, swap01_orth]
  have hQ : (G * swap01 * sgD σ₀ σ)ᵀ * (G * swap01 * sgD σ₀ σ) = 1 := by
    rw [Matrix.transpose_mul]
    calc (sgD σ₀ σ)ᵀ * (G * swap01)ᵀ * (G * swap01 * sgD σ₀ σ)
        = (sgD σ₀ σ)ᵀ * ((G * swap01)ᵀ * (G * swap01)) * sgD σ₀ σ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hP, Matrix.mul_one, sgD_orth h0 h1]
  have hI := height_ineq hf (G * swap01) (G * swap01 * sgD σ₀ σ) hP hQ c s hcs
  have eX : (G * swap01)ᵀ * sX v * (G * swap01 * sgD σ₀ σ) =
      swap01ᵀ * (Gᵀ * sX v * G) * swap01 * sgD σ₀ σ := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  have eY : (G * swap01)ᵀ * sY v * (G * swap01 * sgD σ₀ σ) =
      swap01ᵀ * (Gᵀ * sY v * G) * swap01 * sgD σ₀ σ := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [eX, eY] at hI
  obtain ⟨x0, x1, x2, x3⟩ := diag_swap σ₀ σ (Gᵀ * sX v * G)
  obtain ⟨y0, y1, y2, y3⟩ := diag_swap σ₀ σ (Gᵀ * sY v * G)
  simp only [Fin.sum_univ_three, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    show ((2 : Fin 3).succ : Fin 4) = 3 from rfl] at hI
  rw [x0, x1, x2, x3, y0, y1, y2, y3] at hI
  -- trace identities
  have trX : (Gᵀ * sX v * G) 0 0 + (Gᵀ * sX v * G) 1 1 + (Gᵀ * sX v * G) 2 2 +
      (Gᵀ * sX v * G) 3 3 = sX v 0 0 + sX v 1 1 + sX v 2 2 + sX v 3 3 := by
    have := Matrix.trace_mul_comm (Gᵀ * sX v) G
    have e : Matrix.trace (Gᵀ * sX v * G) = Matrix.trace (sX v) := by
      rw [this, ← Matrix.mul_assoc, hGG, Matrix.one_mul]
    simpa [Matrix.trace, Fin.sum_univ_four] using e
  have trY : (Gᵀ * sY v * G) 0 0 + (Gᵀ * sY v * G) 1 1 + (Gᵀ * sY v * G) 2 2 +
      (Gᵀ * sY v * G) 3 3 = sY v 0 0 + sY v 1 1 + sY v 2 2 + sY v 3 3 := by
    have := Matrix.trace_mul_comm (Gᵀ * sY v) G
    have e : Matrix.trace (Gᵀ * sY v * G) = Matrix.trace (sY v) := by
      rw [this, ← Matrix.mul_assoc, hGG, Matrix.one_mul]
    simpa [Matrix.trace, Fin.sum_univ_four] using e
  have gx0 : (Gᵀ * sX v * G) 0 0 = sX v 0 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, hG0]
  have gy0 : (Gᵀ * sY v * G) 0 0 = sY v 0 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, hG0]
  have gx1 : (Gᵀ * sX v * G) 1 1 = ∑ a : Fin 3, ∑ b : Fin 3, u a * sX v a.succ b.succ * u b := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three, hG1]
    ring
  have gy1 : (Gᵀ * sY v * G) 1 1 = ∑ a : Fin 3, ∑ b : Fin 3, u a * sY v a.succ b.succ * u b := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three, hG1]
    ring
  have key : ∑ j, ∑ k, u j * sL v σ₀ σ c s j k * u k = sH0 v -
      (c * (3 * (Gᵀ * sX v * G) 1 1 + σ₀ * (Gᵀ * sY v * G) 0 0 +
        σ * ((Gᵀ * sY v * G) 2 2 + (Gᵀ * sY v * G) 3 3)) +
       3 * s * ((Gᵀ * sY v * G) 1 1 - σ₀ * (Gᵀ * sX v * G) 0 0 -
        σ * ((Gᵀ * sX v * G) 2 2 + (Gᵀ * sX v * G) 3 3))) := by
    have e2 : (Gᵀ * sX v * G) 2 2 + (Gᵀ * sX v * G) 3 3 =
        sX v 0 0 + sX v 1 1 + sX v 2 2 + sX v 3 3 - (Gᵀ * sX v * G) 0 0 - (Gᵀ * sX v * G) 1 1 := by
      linarith
    have e3 : (Gᵀ * sY v * G) 2 2 + (Gᵀ * sY v * G) 3 3 =
        sY v 0 0 + sY v 1 1 + sY v 2 2 + sY v 3 3 - (Gᵀ * sY v * G) 0 0 - (Gᵀ * sY v * G) 1 1 := by
      linarith
    rw [e2, e3, gx0, gy0, gx1, gy1]
    simp only [sL, sS, sY3, Fin.sum_univ_three, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
      show ((2 : Fin 3).succ : Fin 4) = 3 from rfl]
    simp only [Fin.sum_univ_three] at hu
    simp [Fin.sum_univ_three]
    linear_combination (sH0 v - c * (σ₀ * sY v 0 0 + σ * (sY v 1 1 + sY v 2 2 + sY v 3 3)) -
      3 * s * (-σ₀ * sX v 0 0 - σ * (sX v 1 1 + sX v 2 2 + sX v 3 3))) * hu
  rw [key]
  linarith

theorem L_psd {v : SV} {h : ℝ} (hf : IsFrame (sState v) h) {σ₀ σ c s : ℝ}
    (hσ₀ : σ₀ = 1 ∨ σ₀ = -1) (hσ : σ = 1 ∨ σ = -1) (hcs : c ^ 2 + 3 * s ^ 2 = 1) :
    QF (sL v σ₀ σ c s) := by
  intro w
  by_cases hN : ∑ k, w k ^ 2 = 0
  · have := sum_sq_zero hN
    simp [this]
  · have hpos : 0 < ∑ k, w k ^ 2 := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _)
      (Ne.symm hN)
    set r := Real.sqrt (∑ k, w k ^ 2) with hr
    have hr2 : r ^ 2 = ∑ k, w k ^ 2 := Real.sq_sqrt hpos.le
    have hrpos : 0 < r := Real.sqrt_pos.2 hpos
    have hu : ∑ k, (fun k => w k / r) k ^ 2 = 1 := by
      simp only [div_pow]
      rw [← Finset.sum_div, ← hr2]
      exact div_self (pow_ne_zero 2 hrpos.ne')
    have := L_unit_psd hf hσ₀ hσ hcs (fun k => w k / r) hu
    have e : ∑ j, ∑ k, w j * sL v σ₀ σ c s j k * w k =
        r ^ 2 * ∑ j, ∑ k, (fun k => w k / r) j * sL v σ₀ σ c s j k * (fun k => w k / r) k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      field_simp
    rw [e]
    positivity

/-! ### The fidelity-floor matrix -/

theorem trace_tmul_self (A : Matrix (Fin 4) (Fin 4) ℝ) : Matrix.trace (Aᵀ * A) = fn4 A := by
  unfold fn4
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, sq]
  rw [Finset.sum_comm]

theorem sR_eq (v : SV) : sR v = 3 * fn4 (sX v) - fn4 (sY v) := by
  unfold sR sC
  rw [Matrix.trace_sub, Matrix.trace_smul, trace_tmul_self, trace_tmul_self]
  simp

theorem spin_slice (v : SV) :
    (spinFlipForm (sState v)).re = sR v ∧
      (spinFlipForm (sState v)).im = Real.sqrt 3 * sI v := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hsum : spinFlipForm (sState v) = ∑ i, ∑ j, Zc v i j ^ 2 := by
    rw [spin_sq_sum, magicCoord_sState]
    have e1 : ∀ p q : Fin 2 × Fin 2, sZ v p q ^ 2 =
        (fun i j => Zc v i j ^ 2) (pairIdx p) (pairIdx q) := fun p q => rfl
    simp only [e1]
    rw [← sum_pairG (fun i => ∑ j, (fun i j => Zc v i j ^ 2) i j)]
    exact Finset.sum_congr rfl fun p _ => sum_pairG ((fun i j => Zc v i j ^ 2) (pairIdx p))
  have tre : ∀ i j, (Zc v i j ^ 2).re = 3 * sX v i j ^ 2 - sY v i j ^ 2 := by
    intro i j
    simp only [Zc, sq, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    linear_combination (sX v i j ^ 2) * h3
  have tim : ∀ i j, (Zc v i j ^ 2).im = Real.sqrt 3 * (2 * (sX v i j * sY v i j)) := by
    intro i j
    simp only [Zc, sq, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hsum]
  constructor
  · simp only [Complex.re_sum, tre, Finset.sum_sub_distrib, ← Finset.mul_sum, sR_eq, fn4]
  · simp only [Complex.im_sum, tim, sI, ← Finset.mul_sum]

theorem B0_psd {v : SV} {h : ℝ} (hf : IsFrame (sState v) h) : QF (sB0 v) := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hn : sN v = 1 := by rw [← normSqPsi_sState]; exact hf.1
  have hPhi := hf.Phi_eq
  have hff := fidelity_floor hf.1
  have hns : Complex.normSq (spinFlipForm (sState v)) = sR v ^ 2 + 3 * sI v ^ 2 := by
    rw [Complex.normSq_apply, (spin_slice v).1, (spin_slice v).2]
    linear_combination (sI v ^ 2) * h3
  rw [hPhi, hns] at hff
  have h6 : sH0 v ^ 2 = 6 * h ^ 2 := by
    rw [hf.sH0_eq, mul_pow, Real.sq_sqrt (by norm_num)]
  set ρ := Real.sqrt (sR v ^ 2 + 3 * sI v ^ 2) with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ2 : ρ ^ 2 = sR v ^ 2 + 3 * sI v ^ 2 := Real.sq_sqrt (by positivity)
  have hℓ : ρ ≤ sH0 v ^ 2 - sN v := by rw [hn, h6]; linarith
  have habs : |sR v| ≤ ρ := Real.abs_le_sqrt (by nlinarith [sq_nonneg (sI v)])
  have ha : 0 ≤ sH0 v ^ 2 - sN v + sR v := by
    have := neg_abs_le (sR v); linarith
  have hc : 0 ≤ (sH0 v ^ 2 - sN v - sR v) / 3 := by
    have := le_abs_self (sR v); linarith
  have hb : sI v ^ 2 ≤ (sH0 v ^ 2 - sN v + sR v) * ((sH0 v ^ 2 - sN v - sR v) / 3) := by
    have : ρ ^ 2 ≤ (sH0 v ^ 2 - sN v) ^ 2 := pow_le_pow_left₀ hρ0 hℓ 2
    nlinarith
  intro w
  have := psd2 (x := w 0) (y := w 1) ha hc hb
  simp [sB0, Fin.sum_univ_two]
  nlinarith [this]

theorem IsFrame.e_nonneg {v : SV} {h : ℝ} (hf : IsFrame (sState v) h) : 0 ≤ sE v := by
  have hn : sN v = 1 := by rw [← normSqPsi_sState]; exact hf.1
  have h6 : sH0 v ^ 2 = 6 * h ^ 2 := by
    rw [hf.sH0_eq, mul_pow, Real.sq_sqrt (by norm_num)]
  have hP := Phi_le_one hf.1
  rw [hf.Phi_eq] at hP
  unfold sE
  rw [hn, h6]
  linarith

theorem IsFrame.rays {v : SV} {h : ℝ} (hf : IsFrame (sState v) h) :
    ∀ χ : Psi, InOrbit χ → Complex.normSq (ip χ (sState v)) ≤ sH0 v ^ 2 / 6 := by
  intro χ hχ
  have h6 : sH0 v ^ 2 = 6 * h ^ 2 := by
    rw [hf.sH0_eq, mul_pow, Real.sq_sqrt (by norm_num)]
  rw [h6]
  have := hf.2.2.2 χ hχ
  linarith

/-- **Named hypothesis (open):** the height Hessian `H(v) ⪰ 0` at a closest point
(`eq:fqe-height-matrix`; second-order condition for the maximum of `Re ⟨g Z_*, φ⟩` over the group). -/
def FrameHess : Prop := ∀ (v : SV) (h : ℝ), IsFrame (sState v) h → QF (sHess v)

/-- All positive constraints at a closest-point frame, from the Hessian hypothesis. -/
theorem frame_constraints (hH : FrameHess) {v : SV} {h : ℝ} (hf : IsFrame (sState v) h) :
    SliceConstraints v where
  h0_nonneg := by rw [hf.sH0_eq]; exact mul_nonneg (Real.sqrt_nonneg _) hf.2.1
  e_nonneg := hf.e_nonneg
  K0 := K0_psd hf
  K1 := K1_psd hf
  Hess := hH v h hf
  lower := fun σ₀ σ c s a b d => L_psd hf a b d
  B0 := B0_psd hf
  rays := hf.rays

/-! ### Axiom audit -/

/-- info: 'FormalResearch.FourQubitEntropy.GO.K0_psd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms K0_psd

/-- info: 'FormalResearch.FourQubitEntropy.GO.K1_psd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms K1_psd

/-- info: 'FormalResearch.FourQubitEntropy.GO.L_psd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms L_psd

/-- info: 'FormalResearch.FourQubitEntropy.GO.B0_psd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms B0_psd

/-- info: 'FormalResearch.FourQubitEntropy.GO.frame_constraints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms frame_constraints

end

end FormalResearch.FourQubitEntropy.GO
