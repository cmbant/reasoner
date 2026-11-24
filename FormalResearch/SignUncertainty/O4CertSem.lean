module

public import FormalResearch.SignUncertainty.O4CertSound
public import Mathlib.Analysis.Complex.Basic

/-!
# The real-valued meaning of the box evaluator

`CP.toC` identifies a pair of reals with a complex number and commutes with the pair operations, so that `boxEval` evaluated at `ℝ` is
the complex numerator `(L s - a) θ - (π²/36)(s³ - 1) θ³ + ρ₁₃(s θ) + (er + i ei)` and denominator `θ (θ² - 12 a/π²)²` at
`θ = (1/4)(1 - t² + 2 i t)/(1 + t²)` (`numV_toC`, `denV_toC`), where `ρ₁₃(τ) = π⁻¹ w (w²)² P(w²)`, `w = π τ`, and `P` is the Horner polynomial of `csReal`
(`rho13`).

Status: proved.
-/

@[expose] public section

namespace FormalResearch.SignUncertainty.O4Cert

open Complex

/-- The complex number of a pair. -/
noncomputable def CP.toC (z : CP ℝ) : ℂ := (z.re : ℂ) + (z.im : ℂ) * Complex.I

theorem toC_add (a b : CP ℝ) : (CP.add a b).toC = a.toC + b.toC := by
  apply Complex.ext <;> simp [CP.add, CP.toC]

theorem toC_neg (a : CP ℝ) : (CP.neg a).toC = -a.toC := by
  apply Complex.ext <;> simp [CP.neg, CP.toC]

theorem toC_sub (a b : CP ℝ) : (CP.sub a b).toC = a.toC - b.toC := by
  unfold CP.sub; rw [toC_add, toC_neg]; ring

theorem toC_mul (a b : CP ℝ) : (CP.mul a b).toC = a.toC * b.toC := by
  apply Complex.ext <;> simp [CP.mul, CP.toC] <;> ring

theorem toC_smul (k : ℝ) (a : CP ℝ) : (CP.smul k a).toC = (k : ℂ) * a.toC := by
  apply Complex.ext <;> simp [CP.smul, CP.toC]

theorem toC_ofRe (x : ℝ) : (CP.ofRe x).toC = (x : ℂ) := by
  apply Complex.ext <;> simp [CP.ofRe, CP.toC, ic]

theorem toC_zero : (⟨ic 0, ic 0⟩ : CP ℝ).toC = 0 := by
  apply Complex.ext <;> simp [CP.toC, ic]

theorem toC_horner (X : CP ℝ) (cs : List ℝ) :
    ∀ acc : CP ℝ, (horner X cs acc).toC = cs.foldl (fun (A : ℂ) (c : ℝ) => A * X.toC + (c : ℂ)) acc.toC := by
  induction cs with
  | nil => intro acc; rfl
  | cons c cs ih =>
    intro acc
    simp only [horner, List.foldl_cons]
    rw [ih, toC_add, toC_mul, toC_ofRe]

/-- The truncated series `ρ₁₃(τ) = π⁻¹ w (w²)² P(w²)`, `w = π τ`. -/
noncomputable def rho13 (τ : ℂ) : ℂ :=
  (Real.pi : ℂ)⁻¹ * (((Real.pi : ℂ) * τ) * ((((Real.pi : ℂ) * τ) * ((Real.pi : ℂ) * τ)) * (((Real.pi : ℂ) * τ) * ((Real.pi : ℂ) * τ)))) *
    csReal.foldl (fun (A : ℂ) (c : ℝ) => A * (((Real.pi : ℂ) * τ) * ((Real.pi : ℂ) * τ)) + (c : ℂ)) 0

/-- The point of the arc. -/
noncomputable def thC (t : ℝ) : ℂ :=
  ((1 / 4 : ℝ) : ℂ) * (((1 - t ^ 2 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) / ((1 + t ^ 2 : ℝ) : ℂ)

theorem thC_eq (t : ℝ) :
    thC t = (((1 / 4 : ℝ) * (1 + t ^ 2)⁻¹ : ℝ) : ℂ) * (((1 - t ^ 2 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) := by
  unfold thC
  push_cast
  ring

theorem thV_toC (L s a t er ei : ℝ) : (thV (realInp L s a t er ei)).toC = thC t := by
  rw [thC_eq]
  apply Complex.ext
  · simp only [thV, realInp, CP.toC, ic, Complex.re_ofReal_mul, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.add_im, Complex.mul_im]
    push_cast
    ring
  · simp only [thV, realInp, CP.toC, ic, Complex.re_ofReal_mul, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.add_im, Complex.mul_im]
    push_cast
    ring

theorem toC_addR (z : CP ℝ) (er ei : ℝ) :
    (⟨z.re + er, z.im + ei⟩ : CP ℝ).toC = z.toC + ((er : ℂ) + (ei : ℂ) * Complex.I) := by
  apply Complex.ext <;> simp [CP.toC]

/-- The numerator of the box at real inputs. -/
theorem numV_toC (L s a t er ei : ℝ) :
    (numV (realInp L s a t er ei)).toC =
      ((L * s + -a : ℝ) : ℂ) * thC t -
        (((Real.pi * Real.pi) * ((1 : ℤ) / (36 : ℕ) : ℝ) * ((s * s) * s + -1) : ℝ) : ℂ) * (thC t * thC t * thC t) +
      rho13 ((s : ℂ) * thC t) + ((er : ℂ) + (ei : ℂ) * Complex.I) := by
  have hth := thV_toC L s a t er ei
  simp only [numV, k1V, k2V, th3V, th2V, rhoV, rho0V, wV, xV, accV, toC_add, toC_sub, toC_smul, toC_mul,
    toC_horner, toC_zero, hth, toC_addR]
  simp only [realInp, ic, rho13]
  push_cast
  ring

theorem toC_re0 (x : ℝ) : (⟨x, ic 0⟩ : CP ℝ).toC = (x : ℂ) := toC_ofRe x

/-- The denominator of the box at real inputs. -/
theorem denV_toC (L s a t er ei : ℝ) :
    (denV (realInp L s a t er ei)).toC =
      thC t * ((thC t * thC t - (((12 : ℤ) * a * (Real.pi * Real.pi)⁻¹ : ℝ) : ℂ)) *
        (thC t * thC t - (((12 : ℤ) * a * (Real.pi * Real.pi)⁻¹ : ℝ) : ℂ))) := by
  have hth := thV_toC L s a t er ei
  simp only [denV, d1V, th2V, toC_mul, toC_sub, hth, toC_re0]
  simp only [th02V, realInp, ic]

theorem toC_normSq (z : CP ℝ) : ‖z.toC‖ ^ 2 = z.re * z.re + z.im * z.im := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [CP.toC]

/-- **The box test, in complex form**: if `checkBox i j = true` and the real parameters lie in the box, then `|N| ≤ 0.13 |D|` and `D ≠ 0`
for the complex numerator and denominator of the quotient. -/
theorem box_quot_bound {i j : ℕ} (h : checkBox i j = true) {L s a t er ei : ℝ}
    (hL1 : 2 * (i : ℝ) / (1000 * NL) ≤ L) (hL2 : L ≤ 2 * ((i : ℝ) + 1) / (1000 * NL))
    (hs1 : (4000 * (NL : ℝ) - ((i : ℝ) + 1)) / (4000 * NL) ≤ s)
    (hs2 : s ≤ (500000 * (NL : ℝ) + 606 * ((i : ℝ) + 1)) / (500000 * NL))
    (ha1 : 2 * (i : ℝ) / (1000 * NL) ≤ a)
    (ha2 : a ≤ ((i : ℝ) + 1) * (2000 * (NL : ℝ) + ((i : ℝ) + 1)) / (1000000 * NL * NL))
    (ht1 : (j : ℝ) / NT ≤ t) (ht2 : t ≤ ((j : ℝ) + 1) / NT)
    (her : |er| ≤ (tailR : ℝ) / SC) (hei : |ei| ≤ (tailR : ℝ) / SC) :
    ‖(numV (realInp L s a t er ei)).toC‖ ≤ 13 / 100 * ‖(denV (realInp L s a t er ei)).toC‖ ∧
      (denV (realInp L s a t er ei)).toC ≠ 0 := by
  obtain ⟨h1, h2⟩ := box_sound h hL1 hL2 hs1 hs2 ha1 ha2 ht1 ht2 her hei
  simp only [boxEval, boxSq, ic] at h1 h2
  have e1 := toC_normSq (numV (realInp L s a t er ei))
  have e2 := toC_normSq (denV (realInp L s a t er ei))
  set N := (numV (realInp L s a t er ei)).toC
  set D := (denV (realInp L s a t er ei)).toC
  have hD : 0 < ‖D‖ ^ 2 := by rw [e2]; push_cast at h2; linarith
  have hD0 : D ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hD; norm_num at hD
  refine ⟨?_, hD0⟩
  have hsq : ‖N‖ ^ 2 ≤ (13 / 100 * ‖D‖) ^ 2 := by
    rw [mul_pow, e1, e2]; push_cast at h1; nlinarith
  exact le_of_sq_le_sq (by simpa using hsq) (by positivity)

end FormalResearch.SignUncertainty.O4Cert
