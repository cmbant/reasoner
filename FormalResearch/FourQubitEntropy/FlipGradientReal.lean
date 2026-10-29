import FormalResearch.FourQubitEntropy.FlipGradient
import FormalResearch.FourQubitEntropy.FlipPsi

/-!
# `lem:fqe-flip-gradient`: the derivative of `H` along the spin-flip pencil

`Hval ψ = 4 F - 3 n W₁ = 4 (F - (3/4) n W₁)` is four times the polarization remainder of
`thm:fqe-moment`, and `flipGradient` is the identity (FG) of `sextic_identity.tex`:
`d/ds Hval(ψ + s ψ̃)|₀ = (1/4) Re Σᵢ Yᵢ + Re s · (16 n² + 14 W₁ - 16 |s|²)`,
`s = ψᵀ ε^{⊗4} ψ`, with `Yᵢ = Σ_{idx} sgn(idx) Rᵢ(idx) Rᵢ(1 - idx)` and `Rᵢ = 6 (Vᵢ - 8Uᵢ)`.
Equivalently `d/dt H(z + t z̃) = (9/4) Re Σ Xᵢᵀ ε^{⊗6} Xᵢ + Re s (4 n² - 4 |s|² + (7/2) W₁)`,
`Xᵢ = Rᵢ/6`, which is `eq:fqe-flip-gradient`. Here `ψ + s ψ̃` is the real pencil.

The identity is the polynomial identity of `FlipGradient.lean` (`8 · H4dual = Rg z w + Rg w z`,
kernel-checked in pieces), differentiated by `hasDerivAt_generic`; `Rg w z` is the complex conjugate
of `Rg z w` at `w = z̄`, so the derivative is the real part.
-/

open scoped ComplexConjugate
open scoped FormalResearch.FourQubitEntropy.GenericOps

namespace FormalResearch.FourQubitEntropy

/-- `4 F - 3 n W₁`, four times the polarization remainder `H = F - (3/4) n W₁`. -/
noncomputable def Hval (ψ : Psi) : ℝ := 4 * sexticF ψ - 3 * (normSqPsi ψ * blochSq ψ)

theorem H4gen_conj (ψ : Psi) : H4gen ψ ψ.conj = (Hval ψ : ℂ) := by
  simp only [H4gen, toAdd_complex, toMul_complex, toSub_complex, lit_complex, Fgen_eq, normG_eq,
    W1gen_eq, Hval]
  push_cast
  ring

theorem Rg_conj (ψ : Psi) : Rg ψ.conj ψ = conj (Rg ψ ψ.conj) := by
  have h := opsHom_conj.Rg ψ ψ.conj
  have e1 : State.map (starRingEnd ℂ) ψ = ψ.conj := rfl
  have e2 : State.map (starRingEnd ℂ) ψ.conj = ψ := by
    funext a b c d; simp [State.map, Psi.conj]
  rw [e1, e2] at h
  exact h.symm

theorem pencil_conj (x : Psi) (s : ℝ) :
    (fun a b c d => x.conj a b c d + (s : ℂ) * ztilS x a b c d) = Psi.conj (x + s • spinFlipPsi x) := by
  funext a b c d
  simp [Psi.conj, spinFlipPsi_apply, ztilS, ztil, mul_comm]

/-- The derivative of `Hval` along the pencil, before simplification. -/
theorem hasDerivAt_Hval_pencil (x : Psi) :
    HasDerivAt (fun s : ℝ => Hval (x + s • spinFlipPsi x))
      (((8 : ℂ)⁻¹ * (Rg x x.conj + Rg x.conj x)).re) 0 := by
  have h := hasDerivAt_generic (fun {α} [RingOps α] z w => H4gen z w)
    (fun hf z w => hf.H4gen z w) x x.conj (ztilS x.conj) (ztilS x)
  have hd : (H4gen (dualState x (ztilS x.conj)) (dualState x.conj (ztilS x))).b
      = H4dual x x.conj := rfl
  have hdef := flipGradDefect_zero x x.conj
  simp only [flipGradDefect, toSub_complex, toMul_complex, toAdd_complex, lit_complex] at hdef
  have hD : H4dual x x.conj = (8 : ℂ)⁻¹ * (Rg x x.conj + Rg x.conj x) := by
    have h8 : (8 : ℂ) * H4dual x x.conj = Rg x x.conj + Rg x.conj x := by
      have := sub_eq_zero.mp hdef
      simpa using this
    rw [← h8]; field_simp
  rw [hd, hD] at h
  have h' : HasDerivAt (fun σ : ℂ => H4gen (fun a b c d => x a b c d + σ * ztilS x.conj a b c d)
      (fun a b c d => x.conj a b c d + σ * ztilS x a b c d)) ((8 : ℂ)⁻¹ * (Rg x x.conj + Rg x.conj x))
      ((0 : ℝ) : ℂ) := by simpa using h
  have h'' := h'.real_of_complex
  refine h''.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  have e1 : (fun a b c d => x a b c d + (s : ℂ) * ztilS x.conj a b c d) = x + s • spinFlipPsi x := by
    funext a b c d
    simp [spinFlipPsi, ztilS, mul_comm]
  have e2 := pencil_conj x s
  beta_reduce
  rw [e1, e2, H4gen_conj, Complex.ofReal_re]

/-- **`lem:fqe-flip-gradient`, (FG)**: `d/ds Hval(ψ + s ψ̃)|₀
= (1/4) Re Ysum + Re s · (16 n² + 14 W₁ - 16 |s|²)`. -/
theorem flipGradient (x : Psi) :
    HasDerivAt (fun s : ℝ => Hval (x + s • spinFlipPsi x))
      ((Ysum x x.conj).re / 4 + (spinFlipForm x).re *
        (16 * normSqPsi x ^ 2 + 14 * blochSq x - 16 * Complex.normSq (spinFlipForm x))) 0 := by
  convert hasDerivAt_Hval_pencil x using 1
  rw [Rg_conj]
  have hS : Spart x x.conj = spinFlipForm x *
      ((64 * normSqPsi x ^ 2 + 56 * blochSq x - 64 * Complex.normSq (spinFlipForm x) : ℝ) : ℂ) := by
    simp only [Spart, toAdd_complex, toMul_complex, toSub_complex, lit_complex, normG_eq, W1gen_eq,
      spinFlipForm_conj, Complex.mul_conj]
    push_cast
    ring
  have hR : Rg x x.conj = Ysum x x.conj + spinFlipForm x *
      ((64 * normSqPsi x ^ 2 + 56 * blochSq x - 64 * Complex.normSq (spinFlipForm x) : ℝ) : ℂ) := by
    rw [← hS]; rfl
  rw [hR]
  simp only [Complex.re_ofReal_mul, Complex.mul_re, Complex.add_re, Complex.conj_re, Complex.add_im,
    Complex.mul_im, Complex.conj_im, Complex.inv_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat]
  norm_num
  ring

end FormalResearch.FourQubitEntropy
