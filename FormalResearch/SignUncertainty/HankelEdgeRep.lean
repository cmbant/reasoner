module

public import FormalResearch.SignUncertainty.HankelStripData
public import FormalResearch.CohnElkies.AirySeedFloors

/-!
# Edge representation of `W̃_c` on `Re ζ = 0` (`u1cl:rep`, M5-S5)

For `c > 3/2`, `f ∈ 𝒜_c^ε` and `τ ∈ ℝ`:

`W̃_c(iτ) = ∫_0^∞ K₀(iτ, ξ)⁻¹ · c (f ρ₀)(cξ) dξ`        (`hankelWtS_edge_eq`),

and the kernel factorises as `K₀(iτ, ξ)⁻¹ = (1 - iτ)^{1/2} e^{-B_c(iτ)} e^{-i c Φ(τ; log π²ξ)}`, with the edge
phase `Φ(τ; L) = edgePhi L τ = Lτ - ∫_0^τ m` and `m(u) = log((πu/2)/tanh(πu/2))`
(`hankelEdge_kernel_inv_eq`).  The first identity is `(e33)` (`mellin_strip_kernel_eq`) inverted, together
with the Mellin integral at `Re z = c`, which converges absolutely for `f ∈ 𝒜_c^ε`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Asymptotics

/-- Pointwise form of the inverted kernel identity: for `0 ≤ Re ζ < 1`, `Δ > 0`, `z = c(1-ζ)`,
`K₀(ζ, Δ/c)⁻¹ ρ₀(Δ) = e^{-cℋ(ζ)} (2π)^z Γ(z)⁻¹ Δ^{z-1}`. -/
theorem hankelEdge_kernel_pt {c Δ : ℝ} (hc : 0 < c) (hΔ : 0 < Δ) {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re < 1) :
    (mellinK0 c ζ (Δ / c))⁻¹ * (hankelRho0 c Δ : ℂ) =
      Complex.exp (-((c : ℂ) * stripH ζ)) * (((2 * Real.pi : ℝ) : ℂ) ^ ((c : ℂ) * (1 - ζ)) /
        Complex.Gamma ((c : ℂ) * (1 - ζ)) * (Δ : ℂ) ^ ((c : ℂ) * (1 - ζ) - 1)) := by
  have hξ : 0 < Δ / c := div_pos hΔ hc
  have hk := mellin_strip_kernel_eq (c := c) (ξ := Δ / c) hc hξ h0 h1
  rw [← hk]
  set z : ℂ := (c : ℂ) * (1 - ζ) with hz
  set A : ℂ := ((2 * Real.pi : ℝ) : ℂ) with hA
  set D : ℂ := (Δ : ℂ) with hD
  have hApos : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hA0 : A ≠ 0 := by rw [hA]; exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have hD0 : D ≠ 0 := by rw [hD]; exact_mod_cast hΔ.ne'
  have hX : (2 * (Real.pi : ℂ) * (c : ℂ) * ((Δ / c : ℝ) : ℂ)) = A * D := by
    have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    rw [hA, hD]; push_cast; field_simp
  have hX2 : (A * D) ^ ((c : ℂ) * ζ) = A ^ ((c : ℂ) * ζ) * D ^ ((c : ℂ) * ζ) := by
    rw [hA, hD]
    exact Complex.mul_cpow_ofReal_nonneg hApos hΔ.le _
  have hρ : (hankelRho0 c Δ : ℂ) = A ^ (c : ℂ) / Complex.Gamma (c : ℂ) * D ^ ((c : ℂ) - 1) := by
    have e1 : (((2 * Real.pi) ^ c : ℝ) : ℂ) = A ^ (c : ℂ) := Complex.ofReal_cpow hApos c
    have e2 : ((Δ ^ (c - 1) : ℝ) : ℂ) = D ^ (((c - 1 : ℝ)) : ℂ) := Complex.ofReal_cpow hΔ.le (c - 1)
    have e3 : ((Real.Gamma c : ℝ) : ℂ) = Complex.Gamma (c : ℂ) := (Complex.Gamma_ofReal c).symm
    unfold hankelRho0
    rw [Complex.ofReal_mul, Complex.ofReal_div, e1, e2, e3, Complex.ofReal_sub, Complex.ofReal_one]
  have hA1 : A ^ (c : ℂ) = A ^ z * A ^ ((c : ℂ) * ζ) := by
    rw [← Complex.cpow_add _ _ hA0]; congr 1; rw [hz]; ring
  have hD1 : D ^ ((c : ℂ) - 1) = D ^ (z - 1) * D ^ ((c : ℂ) * ζ) := by
    rw [← Complex.cpow_add _ _ hD0]; congr 1; rw [hz]; ring
  have hGc : Complex.Gamma (c : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hc)
  have hGz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
    rw [hz]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.one_re,
      zero_mul, sub_zero]
    exact mul_pos hc (sub_pos.mpr h1))
  have hAc : A ^ ((c : ℂ) * ζ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hA0)
  have hDc : D ^ ((c : ℂ) * ζ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hD0)
  have hE : Complex.exp ((c : ℂ) * stripH ζ) ≠ 0 := Complex.exp_ne_zero _
  rw [hX, hX2, hρ, hA1, hD1, Complex.exp_neg]
  field_simp

/-- **`u1cl:rep`, edge representation**: `W̃_c(iτ) = ∫_0^∞ K₀(iτ, ξ)⁻¹ c (f ρ₀)(cξ) dξ`. -/
theorem hankelWtS_edge_eq {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (_hf : IsHankelEigenfn c ε f) (τ : ℝ) :
    hankelWtS c ε f ((τ : ℂ) * Complex.I) =
      ∫ ξ in Ioi (0 : ℝ), (mellinK0 c ((τ : ℂ) * Complex.I) ξ)⁻¹ *
        ((c * (f (c * ξ) * hankelRho0 c (c * ξ)) : ℝ) : ℂ) := by
  have hc0 : 0 < c := by linarith
  set ζ : ℂ := (τ : ℂ) * Complex.I with hζ
  have hre : ζ.re = 0 := by simp [hζ]
  have hH : hInt ζ = stripH ζ := hInt_eq_stripH (by rw [hre]) (by rw [hre]; norm_num)
  have hW : hankelWtS c ε f ζ =
      Complex.exp (-((c : ℂ) * stripH ζ)) * mellinStrip f ((c : ℂ) * (1 - ζ)) := by
    unfold hankelWtS mellinFm
    rw [if_pos (by rw [hre]; norm_num), hH]
  set G : ℝ → ℂ := fun Δ => (mellinK0 c ζ (Δ / c))⁻¹ * ((f Δ * hankelRho0 c Δ : ℝ) : ℂ) with hG
  have hper : ∀ ξ : ℝ, (mellinK0 c ζ ξ)⁻¹ * ((c * (f (c * ξ) * hankelRho0 c (c * ξ)) : ℝ) : ℂ) =
      (c : ℂ) * G (c * ξ) := by
    intro ξ
    simp only [hG]
    rw [mul_div_cancel_left₀ ξ hc0.ne']
    push_cast; ring
  simp_rw [hper]
  rw [integral_const_mul, MeasureTheory.integral_comp_mul_left_Ioi G 0 hc0, mul_zero]
  rw [Complex.real_smul]
  have hcc : (c : ℂ) * ((c⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hc0.ne']; simp
  rw [← mul_assoc, hcc, one_mul]
  have hG' : ∀ Δ ∈ Ioi (0 : ℝ), G Δ =
      Complex.exp (-((c : ℂ) * stripH ζ)) * (((2 * Real.pi : ℝ) : ℂ) ^ ((c : ℂ) * (1 - ζ)) /
        Complex.Gamma ((c : ℂ) * (1 - ζ)) * ((f Δ : ℂ) * (Δ : ℂ) ^ ((c : ℂ) * (1 - ζ) - 1))) := by
    intro Δ hΔ
    have := hankelEdge_kernel_pt hc0 (Set.mem_Ioi.mp hΔ) (ζ := ζ) (by rw [hre]) (by rw [hre]; norm_num)
    simp only [hG]
    push_cast
    calc (mellinK0 c ζ (Δ / c))⁻¹ * ((f Δ : ℂ) * (hankelRho0 c Δ : ℂ))
        = (f Δ : ℂ) * ((mellinK0 c ζ (Δ / c))⁻¹ * (hankelRho0 c Δ : ℂ)) := by ring
      _ = _ := by rw [this]; push_cast; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hG', hW]
  unfold mellinStrip mellinRaw
  rw [← integral_const_mul, ← integral_const_mul]

/-- The inverted kernel on `Re ζ = 0`: `K₀(iτ, ξ)⁻¹ = (1-iτ)^{1/2} e^{-B_c(iτ)} e^{-i c Φ(τ; log π²ξ)}`. -/
theorem hankelEdge_kernel_inv_eq (c τ ξ : ℝ) (hξ : 0 < ξ) :
    (mellinK0 c ((τ : ℂ) * Complex.I) ξ)⁻¹ =
      (1 - (τ : ℂ) * Complex.I) ^ (1 / 2 : ℂ) * Complex.exp (-(binetDiff c ((τ : ℂ) * Complex.I))) *
        Complex.exp (-(Complex.I * (c : ℂ) * (edgePhi (Real.log (Real.pi ^ 2 * ξ)) τ : ℂ))) := by
  have hlog : Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ)) = (Real.log (Real.pi ^ 2 * ξ) : ℂ) := by
    rw [show (Real.pi : ℂ) ^ 2 * (ξ : ℂ) = ((Real.pi ^ 2 * ξ : ℝ) : ℂ) by push_cast; ring]
    exact (Complex.ofReal_log (by positivity)).symm
  have hphase : (c : ℂ) * mellinPhi ((τ : ℂ) * Complex.I) ξ =
      Complex.I * (c : ℂ) * (edgePhi (Real.log (Real.pi ^ 2 * ξ)) τ : ℂ) := by
    unfold mellinPhi
    rw [stripS0Tilde_imag, hlog]
    unfold edgePhi
    push_cast
    ring
  have hK : mellinK0 c ((τ : ℂ) * Complex.I) ξ =
      ((1 - (τ : ℂ) * Complex.I) ^ (1 / 2 : ℂ))⁻¹ * Complex.exp (binetDiff c ((τ : ℂ) * Complex.I)) *
        Complex.exp (Complex.I * (c : ℂ) * (edgePhi (Real.log (Real.pi ^ 2 * ξ)) τ : ℂ)) := by
    unfold mellinK0
    rw [hphase, Complex.cpow_neg]
  rw [hK, mul_inv, mul_inv, inv_inv, ← Complex.exp_neg, ← Complex.exp_neg]

/-- info: 'FormalResearch.SignUncertainty.hankelWtS_edge_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelWtS_edge_eq

/-- info: 'FormalResearch.SignUncertainty.hankelEdge_kernel_inv_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelEdge_kernel_inv_eq

end FormalResearch.SignUncertainty
