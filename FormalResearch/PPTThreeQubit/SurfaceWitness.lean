import FormalResearch.PPTThreeQubit.Criterion

/-!
# The `τ`-independent supported witness `H_0`, and local filters

Source: `ResearchNotes/QI/finite_copy_invariant_inference/ppt_three_qubit/rank_five_surface.tex`,
`lem:ppt3-h0` (with `eq:ppt3-h0`), and the filter reduction of `thm:ppt3-orbit`(b).

`H_0` is the Hermitian form on `ℂ⁵` in the basis `(u, v, w, e, o)` with diagonal
`(-24-8√3, 1, 9, 12+4√3, 12+12√3)` and `(H_0)_{vw} = (H_0)_{wv} = -ν`, `ν = 7+4√3`.  Covered:
* `formH0_qs_identity`: the identity `eq:ppt3-h0` for `r · q_1† H_0 q_1`;
* `formH0_nonneg_of_cutProduct`: `H_0` is nonnegative on every cut-product vector of
  `R = R_1` across all three cuts (the cyclic phases fix the `v, w` coordinates, so the off-diagonal
  entry is untouched);
* `trace_nonneg_of_biseparable`: the support criterion for an arbitrary `5 × 5` matrix `H`
  (generalising `trace_Hs_nonneg_of_biseparable`, whose argument it reproduces), and
  `trace_H0_nonneg_of_biseparable`: `tr(H_0 X) ≥ 0` whenever `B_1 X B_1†` is biseparable;
* local filters: for a diagonal product filter `d(a,b,c) = f(a) g(b) h(c)` with nonvanishing
  factors, `d ρ d†` is biseparable iff `ρ` is (`isBiseparable_conj_localDiag_iff`).  This is the
  general form of the invertible-local-filter step in `thm:ppt3-orbit`(b); only diagonal filters
  are treated (the filters `diag(1, λ)^{⊗3}` of the paper are of this form).
-/

namespace FormalResearch.PPTThreeQubit

open Matrix

noncomputable section

/-! ### The witness `H_0` -/

/-- `ν = 7 + 4√3`, minus the `vw` entry of `H_0`. -/
def nuH : ℝ := 7 + 4 * Real.sqrt 3

/-- The diagonal of `H_0` in the basis `(u, v, w, e, o)` (`lem:ppt3-h0`). -/
def h0Diag : Fin 5 → ℝ :=
  ![-24 - 8 * Real.sqrt 3, 1, 9, 12 + 4 * Real.sqrt 3, 12 + 12 * Real.sqrt 3]

/-- The Hermitian form `H_0` of `lem:ppt3-h0`: diagonal `h0Diag`, `(H_0)_{vw} = (H_0)_{wv} = -ν`. -/
def H0 : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.of fun a b => ((if a = b then h0Diag a
    else if (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) then -nuH else 0 : ℝ) : ℂ)

/-- The real quadratic form `re(c† H_0 c) = ∑ₐ h_a |c_a|² - 2ν re(c̄_v c_w)`. -/
def formH0 (c : Fin 5 → ℂ) : ℝ :=
  ∑ a, h0Diag a * Complex.normSq (c a) -
    2 * nuH * ((c 1).re * (c 2).re + (c 1).im * (c 2).im)

theorem trace_H0_vecMulVec_re (c : Fin 5 → ℂ) :
    (H0 * vecMulVec c (star c)).trace.re = formH0 c := by
  simp [H0, formH0, trace, diag, mul_apply, vecMulVec_apply, Fin.sum_univ_five, h0Diag,
    Complex.normSq_apply, Matrix.of_apply]
  ring

private lemma rt3_sq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)

/-- **`eq:ppt3-h0`** (`lem:ppt3-h0`): with `z = x + iy`, `ξ = x²`, `ζ = y²`, `r = ξ + ζ`,
`y_1 = 3 + 2√3`, `x_0 = 2√3 - 3`, `p = 26 + 16√3`, `q = ν²`,
`r · q_1† H_0 q_1 = ζ (r-1)² (r-y_1)² + ξ (r-x_0)² (r² + p r + q) + 16 ν ξ ζ r`. -/
theorem formH0_qs_identity (z : ℂ) :
    Complex.normSq z * formH0 (qs 1 z) =
      z.im ^ 2 * (Complex.normSq z - 1) ^ 2 * (Complex.normSq z - (3 + 2 * Real.sqrt 3)) ^ 2 +
      z.re ^ 2 * (Complex.normSq z - (2 * Real.sqrt 3 - 3)) ^ 2 *
        (Complex.normSq z ^ 2 + (26 + 16 * Real.sqrt 3) * Complex.normSq z + nuH ^ 2) +
      16 * nuH * z.re ^ 2 * z.im ^ 2 * Complex.normSq z := by
  simp only [formH0, Fin.sum_univ_five, h0Diag, qs, nuH]
  simp [Complex.normSq_apply, sq]
  linear_combination (4 * (-16 * Real.sqrt 3 ^ 2 * z.re ^ 2 - 8 * Real.sqrt 3 * z.re ^ 2
    + 11 * z.re ^ 6 + 21 * z.re ^ 4 * z.im ^ 2 + 54 * z.re ^ 4 + 9 * z.re ^ 2 * z.im ^ 4
    + 56 * z.re ^ 2 * z.im ^ 2 + 35 * z.re ^ 2 - z.im ^ 6 + 2 * z.im ^ 4 - z.im ^ 2)) *
    (rt3_sq : Real.sqrt 3 * Real.sqrt 3 = 3)

/-- `H_0` is nonnegative on the curve `q_1` (`eq:ppt3-h0`; the case `z = 0` is checked directly,
which is the continuity step of the paper). -/
theorem formH0_qs_nonneg (z : ℂ) : 0 ≤ formH0 (qs 1 z) := by
  have h3 : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  by_cases hz : z = 0
  · subst hz
    simp [formH0, Fin.sum_univ_five, h0Diag, qs]
    positivity
  · have hr : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
    have hid := formH0_qs_identity z
    have hrhs : 0 ≤ z.im ^ 2 * (Complex.normSq z - 1) ^ 2 *
          (Complex.normSq z - (3 + 2 * Real.sqrt 3)) ^ 2 +
        z.re ^ 2 * (Complex.normSq z - (2 * Real.sqrt 3 - 3)) ^ 2 *
          (Complex.normSq z ^ 2 + (26 + 16 * Real.sqrt 3) * Complex.normSq z + nuH ^ 2) +
        16 * nuH * z.re ^ 2 * z.im ^ 2 * Complex.normSq z := by
      unfold nuH
      positivity
    rw [← hid] at hrhs
    have := nonneg_of_mul_nonneg_right hrhs hr
    simpa using this

/-- The `v`-coordinate vector has `(H_0)_{vv} = 1` and is orthogonal to the off-diagonal entry. -/
theorem formH0_single_v (l : ℂ) : formH0 (l • (Pi.single 1 1 : Fin 5 → ℂ)) = Complex.normSq l := by
  simp [formH0, Fin.sum_univ_five, h0Diag, Pi.single_apply]

theorem formH0_smul (l : ℂ) (c : Fin 5 → ℂ) :
    formH0 (l • c) = Complex.normSq l * formH0 c := by
  unfold formH0
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  · simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
    ring

theorem formH0_phase (d c : Fin 5 → ℂ) (hd : ∀ a, Complex.normSq (d a) = 1) (h1 : d 1 = 1)
    (h2 : d 2 = 1) : formH0 (fun a => d a * c a) = formH0 c := by
  simp only [formH0, map_mul, hd, one_mul, h1]
  simp [h2]

/-- At the cut `A|BC`: if `B_1 c` is an `A|BC`-product then `re(c† H_0 c) ≥ 0`. -/
theorem formH0_nonneg_of_prodA {c : Fin 5 → ℂ} (h : IsProdA (Bs 1 *ᵥ c)) : 0 ≤ formH0 c := by
  rcases prodA_classification one_pos c h with ⟨z, l, rfl⟩ | ⟨l, rfl⟩
  · rw [formH0_smul]; exact mul_nonneg (Complex.normSq_nonneg _) (formH0_qs_nonneg z)
  · rw [formH0_single_v]; exact Complex.normSq_nonneg _

/-- **`lem:ppt3-h0`, nonnegativity on all cut-product vectors.**  If `B_1 c` is a product across
any of the three single-qubit cuts then `re(c† H_0 c) ≥ 0`.  The cyclic shifts act on the
coordinates by diagonal phases which fix the `v` and `w` coordinates (`phaseB`, `phaseC` are `1`
there), so the form is invariant and `B|AC`, `C|AB` reduce to `A|BC`. -/
theorem formH0_nonneg_of_cutProduct {c : Fin 5 → ℂ} (h : IsCutProduct (Bs 1 *ᵥ c)) :
    0 ≤ formH0 c := by
  rcases h with h | h | h
  · exact formH0_nonneg_of_prodA h
  · have h' := prodB_cyc h
    rw [Bs_cycB] at h'
    have := formH0_nonneg_of_prodA h'
    rwa [formH0_phase phaseB c (by
      intro a; fin_cases a <;> simp [phaseB, normSq_ω]) (by simp [phaseB]) (by simp [phaseB])]
      at this
  · have h' := prodC_cyc h
    rw [Bs_cycC] at h'
    have := formH0_nonneg_of_prodA h'
    rwa [formH0_phase phaseC c (by
      intro a; fin_cases a <;> simp [phaseC, normSq_ω_sq]) (by simp [phaseC]) (by simp [phaseC])]
      at this

/-! ### The support criterion for a general matrix `H` -/

/-- **Support criterion for an arbitrary `5 × 5` matrix `H`** (the argument of
`trace_Hs_nonneg_of_biseparable`, with the witness left abstract).  If `re tr(H |c⟩⟨c|) ≥ 0`
whenever `B_s c` is a cut-product, and `B_s X B_s†` is biseparable, then `re tr(H X) ≥ 0`. -/
theorem trace_nonneg_of_biseparable (s : ℝ) (H : Matrix (Fin 5) (Fin 5) ℂ)
    (hH : ∀ c : Fin 5 → ℂ, IsCutProduct (Bs s *ᵥ c) → 0 ≤ (H * vecMulVec c (star c)).trace.re)
    (X : Matrix (Fin 5) (Fin 5) ℂ) (h : IsBiseparable (Bs s * X * (Bs s)ᴴ)) :
    0 ≤ (H * X).trace.re := by
  obtain ⟨n, φ, hprod, hρ⟩ := h
  have hker : ∀ i, Bs s *ᵥ (Lmat *ᵥ φ i) = φ i := fun i =>
    Bs_Lmat_of_ker s (φ i)
      (dot_eq_zero_of_range (Bs s) X φ hρ eVec (eVec_dot_Bs s) i)
      (dot_eq_zero_of_range (Bs s) X φ hρ oVec (oVec_dot_Bs s) i)
      (dot_eq_zero_of_range (Bs s) X φ hρ (k2 s) (k2_dot_Bs s) i)
  have hX : X = ∑ i, vecMulVec (Lmat *ᵥ φ i) (star (Lmat *ᵥ φ i)) := by
    have h1 : Lmat * (Bs s * X * (Bs s)ᴴ) * Lmatᴴ = X := by
      have : Lmat * (Bs s * X * (Bs s)ᴴ) * Lmatᴴ = (Lmat * Bs s) * X * (Lmat * Bs s)ᴴ := by
        simp [Matrix.mul_assoc, conjTranspose_mul]
      rw [this, Lmat_mul_Bs]; simp
    rw [← h1, hρ, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_vecMulVec, vecMulVec_mul, star_mulVec]
  rw [hX, Finset.mul_sum, trace_sum, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => hH _ ?_
  rw [hker i]
  exact hprod i

/-- **`lem:ppt3-h0`, support consequence.**  If `B_1 X B_1†` is biseparable then `tr(H_0 X) ≥ 0`. -/
theorem trace_H0_nonneg_of_biseparable (X : Matrix (Fin 5) (Fin 5) ℂ)
    (h : IsBiseparable (Bs 1 * X * (Bs 1)ᴴ)) : 0 ≤ (H0 * X).trace.re :=
  trace_nonneg_of_biseparable 1 H0 (fun c hc => by
    rw [trace_H0_vecMulVec_re]; exact formH0_nonneg_of_cutProduct hc) X h

/-! ### Diagonal local filters preserve biseparability -/

/-- A diagonal product filter `d(a,b,c) = f(a) g(b) h(c)` on three qubits (index `4a + 2b + c`). -/
def IsLocalDiag (d : Fin 8 → ℂ) : Prop :=
  ∃ f g h : Fin 2 → ℂ, ∀ i : Fin 8,
    d i = f ⟨i.val / 4, by omega⟩ * g ⟨i.val / 2 % 2, by omega⟩ * h ⟨i.val % 2, by omega⟩

/-- A diagonal product filter maps cut-products to cut-products. -/
theorem isCutProduct_localDiag {d : Fin 8 → ℂ} (hd : IsLocalDiag d) {x : Fin 8 → ℂ}
    (hx : IsCutProduct x) : IsCutProduct (fun i => d i * x i) := by
  obtain ⟨f, g, h, hd⟩ := hd
  rcases hx with ⟨α, μ, hx⟩ | ⟨β, μ, hx⟩ | ⟨γ, μ, hx⟩
  · refine Or.inl ⟨fun a => f a * α a,
      fun j => g ⟨j.val / 2, by omega⟩ * h ⟨j.val % 2, by omega⟩ * μ j, fun i => ?_⟩
    beta_reduce
    rw [hd i, hx i]
    fin_cases i <;> simp <;> ring
  · refine Or.inr (Or.inl ⟨fun b => g b * β b,
      fun j => f ⟨j.val / 2, by omega⟩ * h ⟨j.val % 2, by omega⟩ * μ j, fun i => ?_⟩)
    beta_reduce
    rw [hd i, hx i]
    fin_cases i <;> simp <;> ring
  · refine Or.inr (Or.inr ⟨fun c => h c * γ c,
      fun j => f ⟨j.val / 2, by omega⟩ * g ⟨j.val % 2, by omega⟩ * μ j, fun i => ?_⟩)
    beta_reduce
    rw [hd i, hx i]
    fin_cases i <;> simp <;> ring

/-- Conjugation by a diagonal product filter preserves biseparability. -/
theorem isBiseparable_conj_localDiag {d : Fin 8 → ℂ} (hd : IsLocalDiag d)
    {ρ : Matrix (Fin 8) (Fin 8) ℂ} (h : IsBiseparable ρ) :
    IsBiseparable (diagonal d * ρ * (diagonal d)ᴴ) := by
  obtain ⟨n, φ, hprod, hρ⟩ := h
  refine ⟨n, fun i j => d j * φ i j, fun i => isCutProduct_localDiag hd (hprod i), ?_⟩
  rw [hρ, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (fun j => d j * φ i j) = diagonal d *ᵥ φ i := by
    ext j; simp [mulVec_diagonal]
  beta_reduce
  rw [this, mul_vecMulVec, vecMulVec_mul, star_mulVec]

/-- **Invertible diagonal local filters** preserve and reflect biseparability: if every factor of
`d` is nonzero, `d ρ d†` is biseparable iff `ρ` is. -/
theorem isBiseparable_conj_localDiag_iff {d : Fin 8 → ℂ} (hd : IsLocalDiag d)
    (hne : ∀ i, d i ≠ 0) (ρ : Matrix (Fin 8) (Fin 8) ℂ) :
    IsBiseparable (diagonal d * ρ * (diagonal d)ᴴ) ↔ IsBiseparable ρ := by
  refine ⟨fun h => ?_, isBiseparable_conj_localDiag hd⟩
  have hinv : IsLocalDiag (fun i => (d i)⁻¹) := by
    obtain ⟨f, g, h, hd⟩ := hd
    exact ⟨fun a => (f a)⁻¹, fun a => (g a)⁻¹, fun a => (h a)⁻¹, fun i => by
      beta_reduce; rw [hd i]; simp; ring⟩
  have h' := isBiseparable_conj_localDiag hinv h
  have e : diagonal (fun i => (d i)⁻¹) * (diagonal d * ρ * (diagonal d)ᴴ) *
      (diagonal (fun i => (d i)⁻¹))ᴴ = ρ := by
    have h1 : diagonal (fun i => (d i)⁻¹) * diagonal d = 1 := by
      rw [diagonal_mul_diagonal]
      have : (fun i => (d i)⁻¹ * d i) = fun _ => (1 : ℂ) := funext fun i => inv_mul_cancel₀ (hne i)
      rw [this, diagonal_one]
    have h2 : (diagonal d)ᴴ * (diagonal (fun i => (d i)⁻¹))ᴴ = 1 := by
      rw [← conjTranspose_mul, h1, conjTranspose_one]
    calc _ = (diagonal (fun i => (d i)⁻¹) * diagonal d) * ρ *
          ((diagonal d)ᴴ * (diagonal (fun i => (d i)⁻¹))ᴴ) := by simp only [Matrix.mul_assoc]
      _ = ρ := by rw [h1, h2]; simp
  rwa [e] at h'

end

/-- info: 'FormalResearch.PPTThreeQubit.formH0_qs_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms formH0_qs_identity

/-- info: 'FormalResearch.PPTThreeQubit.formH0_nonneg_of_cutProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms formH0_nonneg_of_cutProduct

/-- info: 'FormalResearch.PPTThreeQubit.trace_nonneg_of_biseparable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trace_nonneg_of_biseparable

/-- info: 'FormalResearch.PPTThreeQubit.trace_H0_nonneg_of_biseparable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trace_H0_nonneg_of_biseparable

/-- info: 'FormalResearch.PPTThreeQubit.isBiseparable_conj_localDiag_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isBiseparable_conj_localDiag_iff

end FormalResearch.PPTThreeQubit
