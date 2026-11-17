module

public import FormalResearch.Special.LatticeII

/-!
# The Gamma phase is a calibrated phase

`gammaPhase nc ℓ θ₀ s = (θ₀ + s ℓ - nc·arg Γ(½+is))/π` is `G/π` of `lem:latticesum`
(`ℓ = ℓ_Σ`, `nc = ϰ`).  `calPhase_gamma` shows it satisfies the hypotheses of `CalPhase` with the
window `X`, strip `1/4`, slopes `m ≤ τ₀' ≤ M`, provided

* `nc (log(X+2) + 5) + π m ≤ ℓ` (the paper's `ℓ_i - Re ψ ≥ ½ log L`, from `Re ψ(z) ≤ log(1+|z|)+C`,
  here `re_phaseDeriv_le`), and
* `ℓ + 3 nc ≤ π M` (the paper's `Re ψ(½+is) ≥ ψ(½) > -2`, here `re_phaseDeriv_ge`);
* `K = 16 nc ∑k⁻²/π` bounds `|τ₀''|`.
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex Barnes

/-- `G/π`, `G(s) = θ₀ + sℓ - nc·argΓ(½ + is)`. -/
noncomputable def gammaPhase (nc : ℕ) (ℓ θ0 : ℝ) (s : ℂ) : ℂ :=
  ((θ0 : ℂ) + s * ℓ - nc * argGammaHalf s) / Real.pi

lemma hasDerivAt_gammaPhase (nc : ℕ) (ℓ θ0 : ℝ) {s : ℂ} (hs : |s.im| < 1 / 2) :
    HasDerivAt (gammaPhase nc ℓ θ0) (((ℓ : ℂ) - nc * phaseDeriv s) / Real.pi) s := by
  have h1 : HasDerivAt (fun s : ℂ => (θ0 : ℂ) + s * ℓ - nc * argGammaHalf s)
      ((ℓ : ℂ) - nc * phaseDeriv s) s := by
    have := (((hasDerivAt_id s).mul_const (ℓ : ℂ)).const_add (θ0 : ℂ)).sub
      ((hasDerivAt_argGammaHalf' hs).const_mul (nc : ℂ))
    refine HasDerivAt.congr_deriv ?_ (by simp : (1 : ℂ) * ℓ - nc * phaseDeriv s = (ℓ : ℂ) - nc * phaseDeriv s)
    exact this
  exact h1.div_const _

lemma deriv_gammaPhase (nc : ℕ) (ℓ θ0 : ℝ) {s : ℂ} (hs : |s.im| < 1 / 2) :
    deriv (gammaPhase nc ℓ θ0) s = ((ℓ : ℂ) - nc * phaseDeriv s) / Real.pi :=
  (hasDerivAt_gammaPhase nc ℓ θ0 hs).deriv

lemma hasDerivAt_deriv_gammaPhase (nc : ℕ) (ℓ θ0 : ℝ) {s : ℂ} (hs : |s.im| < 1 / 2) :
    HasDerivAt (deriv (gammaPhase nc ℓ θ0)) (-(nc : ℂ) * (∑' k : ℕ, phTermDeriv2 k s) / Real.pi) s := by
  have hev : deriv (gammaPhase nc ℓ θ0) =ᶠ[𝓝 s] fun w => ((ℓ : ℂ) - nc * phaseDeriv w) / Real.pi := by
    filter_upwards [isOpen_halfStrip.mem_nhds (show s ∈ halfStrip from hs)] with w hw
    exact deriv_gammaPhase nc ℓ θ0 hw
  have h2 := (((hasDerivAt_phaseDeriv hs).const_mul (nc : ℂ)).const_sub (ℓ : ℂ)).div_const (Real.pi : ℂ)
  refine (h2.congr_deriv ?_).congr_of_eventuallyEq hev
  ring

theorem calPhase_gamma (nc : ℕ) (ℓ θ0 X m M : ℝ) (hX : 0 < X) (hm : 0 < m)
    (hℓ1 : nc * (Real.log (X + 2) + 5) + Real.pi * m ≤ ℓ) (hℓ2 : ℓ + 3 * nc ≤ Real.pi * M) :
    CalPhase (gammaPhase nc ℓ θ0) X (1 / 4) m M (nc * (16 * invSqSum) / Real.pi) where
  hX := hX
  hy0 := by norm_num
  hm := hm
  ana := by
    intro s hs
    have hd : DifferentiableOn ℂ (gammaPhase nc ℓ θ0) halfStrip := fun z hz =>
      (hasDerivAt_gammaPhase nc ℓ θ0 hz).differentiableAt.differentiableWithinAt
    exact hd.analyticOnNhd isOpen_halfStrip s (by show |s.im| < 1 / 2; have := hs.2; linarith)
  real := by
    intro x
    unfold gammaPhase
    have := argGammaHalf_real x
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [Complex.div_ofReal_im]
    simp [this]
  ge := by
    intro s hs
    have hs' : |s.im| < 1 / 2 := by have := hs.2; linarith
    rw [deriv_gammaPhase nc ℓ θ0 hs', Complex.div_ofReal_re]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero, Complex.mul_im]
    have hp := re_phaseDeriv_le (s := s) hs.2
    have hre : |s.re| ≤ X + 1 := hs.1
    have hlog : Real.log (1 + |s.re|) ≤ Real.log (X + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [le_div_iff₀ Real.pi_pos]
    have : (nc : ℝ) * (phaseDeriv s).re ≤ nc * (Real.log (X + 2) + 5) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    nlinarith
  le := by
    intro x hx
    rw [deriv_gammaPhase nc ℓ θ0 (by simp), Complex.div_ofReal_re]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero]
    have hp := re_phaseDeriv_ge x
    rw [div_le_iff₀ Real.pi_pos]
    have : -(3 * (nc : ℝ)) ≤ nc * (phaseDeriv (x : ℂ)).re := by nlinarith [Nat.cast_nonneg (α := ℝ) nc]
    nlinarith
  dd := by
    intro s hs
    have hs' : |s.im| < 1 / 2 := by have := hs.2; linarith
    rw [(hasDerivAt_deriv_gammaPhase nc ℓ θ0 hs').deriv]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    apply div_le_div_of_nonneg_right _ Real.pi_pos.le
    rw [norm_mul, norm_neg, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (norm_phaseDeriv2_le hs.2) (Nat.cast_nonneg _)

end FormalResearch.Special.Lattice
