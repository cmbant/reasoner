module

public import FormalResearch.CohnElkies.DualPhaseAndO3
public import FormalResearch.CohnElkies.PieceCPhase

/-!
# `O.3(2)`, the `(1 - χ_ξ)` part of `I_main` (`(e4)`): the van der Corput outer bound

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, proof of `u1co:O3`(2), the `(1 - χ_ξ)`-part. On `|τ| ≥ τ_*/2` the
multiplier is expanded as `E₁(iκτ)^m = (iκτ)^{-m} Σ_j (-1)^j C(m,j) e^{-ijκτ}`, which turns each term into
`e^{icΦ(τ; L - jκ/c)}`, and the core dual-phase bound `dual_phase_oscillatory_bound` is applied to each term.

Status: proved, unconditional (the amplitude bounds on `h = (iκτ)^{-m} (1-χ_ξ) F̃` are a hypothesis, supplied by `(e27)`).
-/

@[expose] public section

open MeasureTheory Set
open scoped Real

namespace FormalResearch.CohnElkies

open FormalResearch.Asymptotics

lemma bsplineE1_mul_self_eq (z : ℂ) : bsplineE1 z * z = 1 - Complex.exp (-z) := by
  unfold bsplineE1
  by_cases hz : z = 0
  · simp [hz]
  · simp [hz]

/-- `E₁(iκτ)^m (iκτ)^m = (1 - e^{-iκτ})^m` expanded binomially. -/
lemma bsplineImag_mul_pow_eq (κ : ℝ) (m : ℕ) (τ : ℝ) :
    bsplineImag κ m τ * (Complex.I * (κ : ℂ) * (τ : ℂ)) ^ m =
      ∑ j ∈ Finset.range (m + 1), (-1 : ℂ) ^ j * (m.choose j : ℂ) * Complex.exp (-(Complex.I * ((j : ℝ) * κ : ℂ) * (τ : ℂ))) := by
  unfold bsplineImag
  rw [← mul_pow, bsplineE1_mul_self_eq, show (1 : ℂ) - Complex.exp (-(Complex.I * (κ : ℂ) * (τ : ℂ))) =
    -Complex.exp (-(Complex.I * (κ : ℂ) * (τ : ℂ))) + 1 by ring, add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [neg_pow, one_pow, mul_one, ← Complex.exp_nat_mul]
  rw [show (j : ℂ) * -(Complex.I * (κ : ℂ) * (τ : ℂ)) = -(Complex.I * ((j : ℝ) * κ : ℂ) * (τ : ℂ)) by push_cast; ring]
  ring

lemma edgePhi_sub_linear (L d τ : ℝ) : edgePhi (L - d) τ = edgePhi L τ - d * τ := by
  unfold edgePhi; ring

lemma half_rpow_le {L p : ℝ} (hL : 0 < L) (hp : -(3 / 2 : ℝ) ≤ p) (_hp0 : p ≤ 0) : (L / 2) ^ p ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * L ^ p := by
  rw [div_eq_mul_inv, Real.mul_rpow hL.le (by norm_num), Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), mul_comm]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)) (by positivity)

/-- **Binomial reduction of the outer integral.** For `h` with every `g_j = k h e^{icΦ(τ; L - jκ/c)}` integrable and
`‖∫ k h e^{icΦ(τ; L - jκ/c)}‖ ≤ B` (`0 ≤ j ≤ m`), the outer integral
`∫ (1-iτ)^{-1/2} e^{B_c(iτ)} E₁(iκτ)^m (iκτ)^m h(τ) e^{icΦ(τ;L)} dτ` has norm `≤ 2^m B`. -/
theorem outer_decomp_bound {m : ℕ} {κ c L B : ℝ} {h : ℝ → ℂ} (hc : 2 ≤ c)
    (hint : ∀ j ∈ Finset.range (m + 1), Integrable (fun τ : ℝ => ((1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) *
      Complex.exp (binetDiff c (Complex.I * (τ : ℂ))) * h τ) * Complex.exp (Complex.I * (c : ℂ) * (edgePhi (L - (j : ℝ) * κ / c) τ : ℂ))))
    (hbd : ∀ j ∈ Finset.range (m + 1), ‖∫ τ : ℝ, ((1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) *
      Complex.exp (binetDiff c (Complex.I * (τ : ℂ))) * h τ) * Complex.exp (Complex.I * (c : ℂ) * (edgePhi (L - (j : ℝ) * κ / c) τ : ℂ))‖ ≤ B) :
    ‖∫ τ : ℝ, ((1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c (Complex.I * (τ : ℂ))) *
          (bsplineImag κ m τ * ((Complex.I * (κ : ℂ) * (τ : ℂ)) ^ m * h τ))) *
            Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))‖ ≤ 2 ^ m * B := by
  have hc_pos : 0 < c := by linarith
  let g : ℝ → ℂ := fun τ => (1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c (Complex.I * (τ : ℂ))) * h τ
  let s_of : ℕ → ℂ := fun j => (-1 : ℂ) ^ j * (m.choose j : ℂ)
  let Lj : ℕ → ℝ := fun j => L - (j : ℝ) * κ / c
  let term : ℕ → ℝ → ℂ := fun j τ => s_of j * g τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi (Lj j) τ : ℂ))
  have hdecomp : ∀ τ : ℝ, ((1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c (Complex.I * (τ : ℂ))) *
      (bsplineImag κ m τ * ((Complex.I * (κ : ℂ) * (τ : ℂ)) ^ m * h τ))) * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)) =
      ∑ j ∈ Finset.range (m + 1), term j τ := fun τ => by
    have hbin := bsplineImag_mul_pow_eq κ m τ
    have : (1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c (Complex.I * (τ : ℂ))) *
        (bsplineImag κ m τ * ((Complex.I * (κ : ℂ) * (τ : ℂ)) ^ m * h τ)) * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)) =
        g τ * ((bsplineImag κ m τ * (Complex.I * (κ : ℂ) * (τ : ℂ)) ^ m) * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))) := by
      simp only [g]; ring
    rw [this, hbin, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hphi : Complex.exp (-(Complex.I * ((j : ℝ) * κ : ℂ) * (τ : ℂ))) * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ)) =
        Complex.exp (Complex.I * (c : ℂ) * (edgePhi (Lj j) τ : ℂ)) := by
      rw [← Complex.exp_add]; congr 1
      simp only [Lj]
      rw [edgePhi_sub_linear]; push_cast; field_simp [hc_pos.ne']; ring
    simp only [term, s_of]
    rw [← hphi]; ring
  have hterm_bd : ∀ j ∈ Finset.range (m + 1), ‖∫ τ : ℝ, term j τ‖ ≤ (m.choose j : ℝ) * B := fun j hj => by
    have hsj : ‖s_of j‖ = (m.choose j : ℝ) := by simp [s_of]
    rw [show ∫ τ : ℝ, term j τ = s_of j * ∫ τ : ℝ, g τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi (Lj j) τ : ℂ)) from by
      simpa [term, mul_assoc] using integral_const_mul (s_of j) _, norm_mul, hsj]
    exact mul_le_mul_of_nonneg_left (hbd j hj) (Nat.cast_nonneg _)
  have hterm_int : ∀ j ∈ Finset.range (m + 1), Integrable (term j) := fun j hj =>
    ((hint j hj).const_mul (s_of j)).congr (ae_of_all _ fun τ => by dsimp [term, g, Lj]; ring)
  rw [show (fun τ : ℝ => _) = fun τ => ∑ j ∈ Finset.range (m + 1), term j τ from funext hdecomp, integral_finsetSum _ hterm_int]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm_bd).trans_eq ?_)
  rw [← Finset.sum_mul, show (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ)) = (2 : ℝ) ^ m by exact_mod_cast Nat.sum_range_choose m]

/-- **Outer part of `I_main` in the variable `τ = εv`.** For `κ > 0`, `m ≥ 1`, `c ≥ 2`, `L > 0` with `mκ ≤ cL/2` and `c (L/2)^{3/2} ≥ 1`,
and a `C²` amplitude `h` with `‖h^{(r)}‖ ≤ A_h (1+τ²)^{-5/4}` (`r ≤ 2`) (here `h = (iκτ)^{-m} (1-χ_ξ) F̃`),
`‖∫ (1-iτ)^{-1/2} e^{B_c(iτ)} E₁(iκτ)^m (iκτ)^m h(τ) e^{icΦ(τ;L)} dτ‖ ≤ C 2^m A_h c^{-1/2} min(L^{-1/4}, L^{-3/2})`, with `C` absolute. -/
theorem main_outer_phase_bound :
    ∃ C > 0, ∀ {m : ℕ}, 1 ≤ m → ∀ {κ c L A_h : ℝ} {h : ℝ → ℂ}, 0 < κ → 2 ≤ c → 0 < L → (m : ℝ) * κ ≤ c * L / 2 →
      1 ≤ c * (L / 2) ^ (3 / 2 : ℝ) → 0 ≤ A_h → ContDiff ℝ 2 h →
      (∀ r ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv r h τ‖ ≤ A_h * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ))) →
      ‖∫ τ : ℝ, ((1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c (Complex.I * (τ : ℂ))) *
          (bsplineImag κ m τ * ((Complex.I * (κ : ℂ) * (τ : ℂ)) ^ m * h τ))) *
            Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))‖ ≤
        C * 2 ^ m * A_h * c ^ (-(1 / 2 : ℝ)) * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨C_osc, hC_osc, hosc⟩ := dual_phase_oscillatory_bound
  have hμ : (0 : ℝ) < 1 / 2 := by norm_num
  let C_K : ℝ := 8 * (2 ^ (1 / 2 : ℝ) * Real.exp 1); have hC_K : 0 < C_K := by positivity
  let C_amp : ℝ := 4 * C_K; have hC_amp : 0 < C_amp := by positivity
  refine ⟨C_osc * C_amp * (2 : ℝ) ^ (3 / 2 : ℝ), by positivity, fun {m} hm {κ c L A_h} {h} hκ hc hL hmκ hcL hA hh_cd hh_bd => ?_⟩
  have hc_pos : 0 < c := by linarith
  obtain ⟨hk_cd, hk_bd⟩ := cpow_mul_binet_deriv_bound hμ hc
  let k : ℝ → ℂ := fun τ => (1 - Complex.I * (τ : ℂ)) ^ (-((1 / 2 : ℝ) : ℂ)) * Complex.exp (binetDiff c (Complex.I * (τ : ℂ)))
  have hk_cast : ∀ τ : ℝ, (1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) = (1 - Complex.I * (τ : ℂ)) ^ (-((1 / 2 : ℝ) : ℂ)) := fun τ => by push_cast; rfl
  have hk_54 : ∀ r ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv r k τ‖ ≤ C_K * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := fun r hr τ => by
    refine (hk_bd r hr τ).trans (le_of_eq ?_)
    simp only [C_K]; norm_num
  let g : ℝ → ℂ := fun τ => k τ * h τ
  have hg_cd : ContDiff ℝ 2 g := (hk_cd.of_le (by simp)).mul hh_cd
  have hg_bd : ∀ r ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv r g τ‖ ≤ C_amp * A_h * (1 + τ ^ 2) ^ (-(3 / 2 : ℝ)) := fun r hr τ =>
    (norm_iteratedDeriv_mul_le (by positivity : 0 ≤ C_K * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ))) (by positivity : 0 ≤ A_h * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ)))
      hr (hk_cd.of_le (by simp)) hh_cd (fun i hi => hk_54 i (hi.trans hr) τ) (fun i hi => hh_bd i (hi.trans hr) τ)).trans_eq
      (by rw [show (2 : ℝ) ^ 2 * (C_K * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ))) * (A_h * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ))) =
          C_amp * A_h * ((1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ))) by dsimp [C_amp]; ring, ← Real.rpow_add (by linarith [sq_nonneg τ])]; norm_num)
  let Lj : ℕ → ℝ := fun j => L - (j : ℝ) * κ / c
  have hk_eq : ∀ τ : ℝ, (1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c (Complex.I * (τ : ℂ))) * h τ = g τ := fun τ => by
    simp only [g, k]; rw [hk_cast τ]
  have hLj : ∀ j ∈ Finset.range (m + 1), L / 2 ≤ Lj j := fun j hj => by
    have hjm : (j : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    simp only [Lj]
    have : (j : ℝ) * κ / c ≤ L / 2 := by
      rw [div_le_iff₀ hc_pos]; nlinarith [mul_le_mul_of_nonneg_right hjm hκ.le]
    linarith
  have hmain := outer_decomp_bound (m := m) (κ := κ) (L := L) (h := h) (B := C_osc * (C_amp * A_h) * c ^ (-(1 / 2 : ℝ)) *
    ((2 : ℝ) ^ (3 / 2 : ℝ) * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))))) hc
    (fun j hj => by
      simp only [hk_eq]
      exact (dual_phase_integrable (c := c) (L := Lj j) hg_cd (by positivity : 0 ≤ C_amp * A_h) hg_bd).2)
    (fun j hj => by
      simp only [hk_eq]
      have hLj2 := hLj j hj
      have hLjpos : 0 < Lj j := by linarith
      have hosc_j := hosc (L := Lj j) hg_cd (by positivity : 0 ≤ C_amp * A_h) hg_bd hc hLjpos
        (hcL.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hLj2 (by norm_num)) hc_pos.le))
      have hmin : min ((Lj j) ^ (-(1 / 4 : ℝ))) ((Lj j) ^ (-(3 / 2 : ℝ))) ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) := by
        refine (min_rpow_antitone (by positivity : 0 < L / 2) hLj2).trans ?_
        rw [mul_min_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (3 / 2 : ℝ))]
        exact min_le_min (half_rpow_le hL (by norm_num) (by norm_num)) (half_rpow_le hL (by norm_num) (by norm_num))
      exact hosc_j.trans (mul_le_mul_of_nonneg_left hmin (by positivity)) |>.trans_eq (by ring))
  refine hmain.trans (le_of_eq ?_)
  ring

lemma liftEps_inv {c : ℝ} (hc : 0 < c) : (liftEps c)⁻¹ = c ^ (1 / 3 : ℝ) := by
  unfold liftEps; rw [Real.rpow_neg hc.le, inv_inv]

/-- **Reduction of the outer part of `I_main` to the `τ`-integral.** In the notation of `iMainIntegrand`, with `ε = c^{-1/3}`, `κ = c_s δ₀ /(m ε)`,
`L = log(π² ξ)` and a cut-off `χ_o(τ)` with `χ_o(τ) G(τ/ε) = (iκτ)^m h(τ)` (`G(v) = X̃(i c_s · iv)`), the outer part
`(2πξ)^{-1} ∫ χ_o(εv) K₀ W dv` equals `(2πξ)^{-1} c^{1/3}` times the `τ`-integral `∫ (1-iτ)^{-1/2} e^{B_c(iτ)} E₁(iκτ)^m (iκτ)^m h e^{icΦ(τ;L)}`. -/
theorem iMain_outer_eq {m : ℕ} (hm : 1 ≤ m) (X : ℝ → ℝ) {δ₀ c ξ : ℝ} (χo : ℝ → ℝ) {h : ℝ → ℂ} (hc : 2 ≤ c) (hξ : 0 < ξ)
    (hrel : ∀ τ : ℝ, (χo τ : ℂ) * airyTwistedLaplaceC X ((ceCs : ℂ) * (((τ / liftEps c : ℝ) : ℂ) * Complex.I)) =
        (Complex.I * ((ceCs * δ₀ / m / liftEps c : ℝ) : ℂ) * (τ : ℂ)) ^ m * h τ) :
    ‖((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, (χo (liftEps c * v) : ℂ) * iMainIntegrand X δ₀ m c ξ v‖ =
      (2 * Real.pi * ξ)⁻¹ * c ^ (1 / 3 : ℝ) * ‖∫ τ : ℝ, ((1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) *
        Complex.exp (binetDiff c (Complex.I * (τ : ℂ))) * (bsplineImag (ceCs * δ₀ / m / liftEps c) m τ *
          ((Complex.I * ((ceCs * δ₀ / m / liftEps c : ℝ) : ℂ) * (τ : ℂ)) ^ m * h τ))) *
            Complex.exp (Complex.I * (c : ℂ) * (edgePhi (Real.log (Real.pi ^ 2 * ξ)) τ : ℂ))‖ := by
  have hc0 : 0 < c := by linarith
  have hε := liftEps_pos hc0
  set ε := liftEps c with hεdef
  set κ : ℝ := ceCs * δ₀ / m / ε with hκdef
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  set L := Real.log (Real.pi ^ 2 * ξ) with hLdef
  have hmult : ∀ v : ℝ, liftMultiplier δ₀ m ((v : ℂ) * Complex.I) = bsplineImag κ m (ε * v) := fun v => by
    unfold liftMultiplier bsplineImag; congr 2
    have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
    have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
    simp only [hκdef]; push_cast; field_simp
  let Fs : ℝ → ℂ := fun τ => ((1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c (Complex.I * (τ : ℂ))) *
        (bsplineImag κ m τ * ((Complex.I * (κ : ℂ) * (τ : ℂ)) ^ m * h τ))) * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))
  have hF : ∀ v : ℝ, (χo (ε * v) : ℂ) * iMainIntegrand X δ₀ m c ξ v = Fs (ε * v) := fun v => by
    rw [iMainIntegrand_eq_pc X δ₀ m hc0 hξ v]
    have h1 := hrel (ε * v)
    rw [show ε * v / ε = v from by field_simp] at h1
    have hexp : Complex.exp (Complex.I * (pcPhase c ξ v : ℝ)) = Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (ε * v) : ℂ)) := by
      rw [pcPhase_eq hc0]; congr 1; push_cast; ring
    have e : (((liftEps c * v : ℝ) : ℂ) * Complex.I) = Complex.I * ((ε * v : ℝ) : ℂ) := mul_comm _ _
    unfold pcAmp
    rw [hmult v, hexp, e]
    simp only [Fs]
    linear_combination ((1 - Complex.I * ((ε * v : ℝ) : ℂ)) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c (Complex.I * ((ε * v : ℝ) : ℂ))) *
      bsplineImag κ m (ε * v) * Complex.exp (Complex.I * (c : ℂ) * (edgePhi L (ε * v) : ℂ))) * h1
  have hint : ∫ v : ℝ, (χo (ε * v) : ℂ) * iMainIntegrand X δ₀ m c ξ v = |ε⁻¹| • ∫ τ : ℝ, Fs τ := by
    rw [integral_congr_ae (ae_of_all _ hF)]
    exact Measure.integral_comp_mul_left Fs ε
  have hεinv : ε⁻¹ = c ^ (1 / 3 : ℝ) := liftEps_inv hc0
  rw [hint, norm_mul, norm_smul, Real.norm_eq_abs, abs_abs, hεinv]
  rw [show ‖(((2 * Real.pi * ξ : ℝ) : ℂ))⁻¹‖ = (2 * Real.pi * ξ)⁻¹ by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]]
  rw [abs_of_pos (by positivity : 0 < c ^ (1 / 3 : ℝ))]
  ring

/-- **`O.3(2)`, the `(1 - χ_ξ)`-part of `I_main` (`(e4)`), from the sup-norm amplitude bounds.** If the amplitude
`h(τ) = (iκτ)^{-m} χ_o(τ) G(τ/ε)` is `C²` with `‖h^{(r)}‖ ≤ A_h (1+τ²)^{-5/4}`, `r ≤ 2`, and `mκ ≤ cL/2`, `c (L/2)^{3/2} ≥ 1`, then
`|(2πξ)^{-1} ∫ χ_o(εv) K₀ W dv| ≤ (2πξ)^{-1} c^{1/3} C 2^m A_h c^{-1/2} min(L^{-1/4}, L^{-3/2})`. -/
theorem iMain_outer_bound :
    ∃ C > 0, ∀ {m : ℕ}, 1 ≤ m → ∀ (X : ℝ → ℝ) {δ₀ c ξ A_h : ℝ} (χo : ℝ → ℝ) {h : ℝ → ℂ}, 0 < δ₀ → 2 ≤ c → 0 < ξ →
      0 < Real.log (Real.pi ^ 2 * ξ) →
      (m : ℝ) * (ceCs * δ₀ / m / liftEps c) ≤ c * Real.log (Real.pi ^ 2 * ξ) / 2 →
      1 ≤ c * (Real.log (Real.pi ^ 2 * ξ) / 2) ^ (3 / 2 : ℝ) → 0 ≤ A_h → ContDiff ℝ 2 h →
      (∀ r ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv r h τ‖ ≤ A_h * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ))) →
      (∀ τ : ℝ, (χo τ : ℂ) * airyTwistedLaplaceC X ((ceCs : ℂ) * (((τ / liftEps c : ℝ) : ℂ) * Complex.I)) =
        (Complex.I * ((ceCs * δ₀ / m / liftEps c : ℝ) : ℂ) * (τ : ℂ)) ^ m * h τ) →
      ‖((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, (χo (liftEps c * v) : ℂ) * iMainIntegrand X δ₀ m c ξ v‖ ≤
        (2 * Real.pi * ξ)⁻¹ * c ^ (1 / 3 : ℝ) * (C * 2 ^ m * A_h * c ^ (-(1 / 2 : ℝ)) *
          min (Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ))) (Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)))) := by
  obtain ⟨C, hC, hmain⟩ := main_outer_phase_bound
  refine ⟨C, hC, fun {m} hm X {δ₀ c ξ A_h} χo {h} hδ hc hξ hL hmκ hcL hA hh_cd hh_bd hrel => ?_⟩
  rw [iMain_outer_eq hm X χo hc hξ hrel]
  have hc0 : 0 < c := by linarith
  have hκ : 0 < ceCs * δ₀ / m / liftEps c := by
    have := ceCs_pos; have := liftEps_pos hc0
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    positivity
  have h2 := hmain hm hκ hc hL hmκ hcL hA hh_cd hh_bd
  gcongr

/-- info: 'FormalResearch.CohnElkies.bsplineImag_mul_pow_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.bsplineImag_mul_pow_eq
/-- info: 'FormalResearch.CohnElkies.main_outer_phase_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.main_outer_phase_bound
/-- info: 'FormalResearch.CohnElkies.iMain_outer_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.iMain_outer_bound

/-- info: 'FormalResearch.CohnElkies.iMain_outer_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.iMain_outer_eq
/-- info: 'FormalResearch.CohnElkies.outer_decomp_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.outer_decomp_bound

end FormalResearch.CohnElkies
