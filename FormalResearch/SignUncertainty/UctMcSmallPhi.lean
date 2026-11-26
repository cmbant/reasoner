module

public import FormalResearch.SignUncertainty.UctMcSmallBd
public import FormalResearch.SignUncertainty.UctAiryTransPhi
public import FormalResearch.SignUncertainty.UctSeedW

/-!
# `SmallBd` for `φ_{c,δ}(1-iτ)/φ_{c,δ}(1)` (F2a, `uct:Mc-small`)

For `c ≥ c₀` and `0 ≤ δ ≤ 1`: `τ ↦ φ_{c,δ}(1-iτ)/φ_{c,δ}(1)` satisfies `SmallBd · c^{-2/3} K` (`smallBd_phiQuot`), from the derivative
bounds `(uct:phicd-bnds)` of `uct_airy_trans_phi` (`r ≤ 3`) along the vertical line `Re w = 1`.
-/

@[expose] public section

open Complex Filter Topology Metric Set

namespace FormalResearch.SignUncertainty

/-- Derivatives of a holomorphic function along an affine line (all in the open set `U`), up to order 3. -/
lemma line_deriv3 {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) {c₀ d : ℂ}
    (hℓ : ∀ τ : ℝ, c₀ + d * (τ : ℂ) ∈ U) :
    ContDiff ℝ 3 (fun τ : ℝ => F (c₀ + d * (τ : ℂ))) ∧
    (∀ τ : ℝ, deriv (fun τ : ℝ => F (c₀ + d * (τ : ℂ))) τ = d * deriv F (c₀ + d * (τ : ℂ))) ∧
    (∀ τ : ℝ, deriv (deriv (fun τ : ℝ => F (c₀ + d * (τ : ℂ)))) τ = d * (d * deriv (deriv F) (c₀ + d * (τ : ℂ)))) ∧
    (∀ τ : ℝ, deriv (deriv (deriv (fun τ : ℝ => F (c₀ + d * (τ : ℂ))))) τ =
      d * (d * (d * deriv (deriv (deriv F)) (c₀ + d * (τ : ℂ))))) := by
  set ℓ : ℝ → ℂ := fun τ => c₀ + d * (τ : ℂ) with hℓdef
  have hℓd : ∀ τ : ℝ, HasDerivAt ℓ d τ := fun τ => by
    have := ((hasDerivAt_id τ).ofReal_comp.const_mul d).const_add c₀
    exact this.congr_deriv (by simp)
  have hder : ∀ (G : ℂ → ℂ), DifferentiableOn ℂ G U → ∀ τ : ℝ,
      HasDerivAt (fun τ : ℝ => G (ℓ τ)) (d * deriv G (ℓ τ)) τ := by
    intro G hG τ
    have h1 : HasDerivAt G (deriv G (ℓ τ)) (ℓ τ) := (hG.differentiableAt (hU.mem_nhds (hℓ τ))).hasDerivAt
    have := h1.scomp τ (hℓd τ)
    exact this.congr_deriv (by simp [smul_eq_mul])
  have hF1 : DifferentiableOn ℂ (deriv F) U := hF.deriv hU
  have hF2 : DifferentiableOn ℂ (deriv (deriv F)) U := hF1.deriv hU
  have hF3 : DifferentiableOn ℂ (deriv (deriv (deriv F))) U := hF2.deriv hU
  have hd1 : deriv (fun τ : ℝ => F (ℓ τ)) = fun τ => d * deriv F (ℓ τ) := by
    funext τ; exact (hder F hF τ).deriv
  have hd2 : deriv (deriv (fun τ : ℝ => F (ℓ τ))) = fun τ => d * (d * deriv (deriv F) (ℓ τ)) := by
    rw [hd1]; funext τ; exact ((hder (deriv F) hF1 τ).const_mul d).deriv
  have hd3 : deriv (deriv (deriv (fun τ : ℝ => F (ℓ τ)))) =
      fun τ => d * (d * (d * deriv (deriv (deriv F)) (ℓ τ))) := by
    rw [hd2]; funext τ; exact (((hder (deriv (deriv F)) hF2 τ).const_mul d).const_mul d).deriv
  have hcd : ContDiff ℝ 3 (fun τ : ℝ => F (ℓ τ)) := by
    have hFc : ContDiffOn ℝ 3 F U := ((hF.contDiffOn hU).restrict_scalars ℝ).of_le (by exact_mod_cast le_top)
    have hℓc : ContDiff ℝ 3 ℓ := by
      simp only [hℓdef]
      exact contDiff_const.add (contDiff_const.mul Complex.ofRealCLM.contDiff)
    exact hFc.comp_contDiff hℓc hℓ
  exact ⟨hcd, fun τ => by rw [hd1], fun τ => by rw [hd2], fun τ => by rw [hd3]⟩

lemma differentiableOn_uctPhi {c : ℝ} (hc : 0 < c) (δ : ℝ) : DifferentiableOn ℂ (uctPhi c δ) {w : ℂ | 0 < w.re} := by
  intro w hw
  have hws : w ∈ Complex.slitPlane := Or.inl hw
  have h1 : DifferentiableAt ℂ (fun w : ℂ => w ^ (5 / 2 : ℂ)) w := differentiableAt_id.cpow_const hws
  have h2 : DifferentiableAt ℂ (fun w : ℂ => seedT δ ((seedScale c : ℂ) * w)) w := by
    have hre : 0 < ((seedScale c : ℂ) * w).re := by
      rw [re_mul_real]; exact mul_pos (seedScale_pos hc) hw
    exact ((seedT_differentiableOn δ).differentiableAt (isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hre)).comp w
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => (seedScale c : ℂ) * w) w)
  exact (differentiableWithinAt_const _ |>.mul h1.differentiableWithinAt |>.mul h2.differentiableWithinAt)


lemma two_le_rpow_third {c : ℝ} (hc : 8 ≤ c) : 2 ≤ c ^ (1 / 3 : ℝ) := by
  have h8 : (8 : ℝ) ^ (1 / 3 : ℝ) = 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
  rw [← h8]
  exact Real.rpow_le_rpow (by norm_num) hc (by norm_num)

lemma phi_iter_bound {c δ : ℝ} (hc : 8 ≤ c) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (r : ℕ) {C : ℝ}
    (hC : ∀ c δ : ℝ, 0 < c → 0 ≤ δ → δ ≤ 1 → ∀ w : ℂ, 0 ≤ w.re → 2 * c ^ (-(1 / 3 : ℝ)) ≤ ‖w‖ →
      ‖iteratedDerivWithin r (fun w : ℂ => uctPhi c δ w - 1) {w : ℂ | 0 ≤ w.re} w‖ ≤
        C * c ^ (-(2 / 3 : ℝ)) * ‖w‖ ^ (-((2 : ℝ) + r))) (hC0 : 0 ≤ C) (τ : ℝ) :
    ‖iteratedDeriv r (fun w : ℂ => uctPhi c δ w - 1) (1 + (-Complex.I) * (τ : ℂ))‖ ≤ C * c ^ (-(2 / 3 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  set w : ℂ := 1 + (-Complex.I) * (τ : ℂ) with hw
  have hre : w.re = 1 := by simp [hw]
  have hw1 : 1 ≤ ‖w‖ := by
    have := Complex.abs_re_le_norm w
    rw [hre] at this; simpa using this
  have h13 : c ^ (-(1 / 3 : ℝ)) ≤ 1 / 2 := by
    rw [Real.rpow_neg hc0.le]
    have := two_le_rpow_third hc
    have hp : 0 < c ^ (1 / 3 : ℝ) := by linarith
    rw [inv_le_comm₀ hp (by norm_num)]
    simpa using this
  have h := hC c δ hc0 hδ0 hδ1 w (by rw [hre]; norm_num) (by linarith)
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hF : DifferentiableOn ℂ (fun w : ℂ => uctPhi c δ w - 1) {w : ℂ | 0 < w.re} :=
    (differentiableOn_uctPhi hc0 δ).sub_const 1
  have hcd : ContDiffAt ℂ r (fun w : ℂ => uctPhi c δ w - 1) w :=
    ((hF.contDiffOn hU).contDiffAt (hU.mem_nhds (show 0 < w.re by rw [hre]; norm_num))).of_le (by exact_mod_cast le_top)
  rw [← iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_halfplane hcd (show 0 ≤ w.re by rw [hre]; norm_num)]
  refine h.trans ?_
  have : ‖w‖ ^ (-((2 : ℝ) + r)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hw1 (by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)])
  have hp0 : 0 ≤ c ^ (-(2 / 3 : ℝ)) := (Real.rpow_pos_of_pos hc0 _).le
  nlinarith [mul_nonneg hC0 hp0]


theorem smallBd_phiQuot : ∃ c0 K : ℝ, 0 ≤ K ∧ ∀ c δ : ℝ, c0 ≤ c → 0 ≤ δ → δ ≤ 1 →
    SmallBd (fun τ : ℝ => uctPhi c δ (1 - (τ : ℂ) * Complex.I) / uctPhi c δ 1) (c ^ (-(2 / 3 : ℝ))) K := by
  obtain ⟨C0, hC0, h0⟩ := uct_airy_trans_phi 0
  obtain ⟨C1, hC1, h1⟩ := uct_airy_trans_phi 1
  obtain ⟨C2, hC2, h2⟩ := uct_airy_trans_phi 2
  obtain ⟨C3, hC3, h3⟩ := uct_airy_trans_phi 3
  set x : ℝ := 2 * C0 + 1 with hx
  have hx1 : 1 ≤ x := by rw [hx]; linarith
  refine ⟨max 8 (x ^ 3), 2 * (C1 + C2 + C3), by positivity, fun c δ hc hδ0 hδ1 => ?_⟩
  have hc8 : 8 ≤ c := (le_max_left _ _).trans hc
  have hcx : x ^ 3 ≤ c := (le_max_right _ _).trans hc
  have hc0 : 0 < c := by linarith
  set p : ℝ := c ^ (-(2 / 3 : ℝ)) with hp
  have hp0 : 0 ≤ p := (Real.rpow_pos_of_pos hc0 _).le
  have hp1 : p ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hpx : p * x ≤ 1 := by
    have h23 : x ≤ c ^ (2 / 3 : ℝ) := by
      have : (x ^ 3) ^ (2 / 3 : ℝ) ≤ c ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) hcx (by norm_num)
      have e : (x ^ 3) ^ (2 / 3 : ℝ) = x ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
      rw [e] at this; nlinarith
    rw [hp, Real.rpow_neg hc0.le]
    have : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    rw [inv_mul_le_iff₀ this]; linarith
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  set F : ℂ → ℂ := fun w => uctPhi c δ w - 1 with hF
  have hFd : DifferentiableOn ℂ F {w : ℂ | 0 < w.re} := (differentiableOn_uctPhi hc0 δ).sub_const 1
  have hℓ : ∀ τ : ℝ, (1 : ℂ) + (-Complex.I) * (τ : ℂ) ∈ {w : ℂ | 0 < w.re} := fun τ => by simp
  obtain ⟨hGc, g1, g2, g3⟩ := line_deriv3 hU hFd hℓ
  set G : ℝ → ℂ := fun τ => F ((1 : ℂ) + (-Complex.I) * (τ : ℂ)) with hG
  have hnd : ‖(-Complex.I)‖ = 1 := by simp
  have b0 : ∀ τ : ℝ, ‖F (1 + (-Complex.I) * (τ : ℂ))‖ ≤ C0 * p := fun τ => by
    have := phi_iter_bound hc8 hδ0 hδ1 0 h0 hC0 τ
    simpa using this
  have b1 : ∀ τ : ℝ, ‖deriv G τ‖ ≤ C1 * p := fun τ => by
    rw [g1, norm_mul, hnd, one_mul]
    have := phi_iter_bound hc8 hδ0 hδ1 1 h1 hC1 τ
    rw [iteratedDeriv_one] at this
    exact this
  have b2 : ∀ τ : ℝ, ‖deriv (deriv G) τ‖ ≤ C2 * p := fun τ => by
    rw [g2, norm_mul, norm_mul, hnd, one_mul, one_mul]
    have := phi_iter_bound hc8 hδ0 hδ1 2 h2 hC2 τ
    rw [iteratedDeriv_succ, iteratedDeriv_one] at this
    exact this
  have b3 : ∀ τ : ℝ, ‖deriv (deriv (deriv G)) τ‖ ≤ C3 * p := fun τ => by
    rw [g3, norm_mul, norm_mul, norm_mul, hnd, one_mul, one_mul, one_mul]
    have := phi_iter_bound hc8 hδ0 hδ1 3 h3 hC3 τ
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one] at this
    exact this
  -- lower bound for φ(1)
  set φ1 : ℂ := uctPhi c δ 1 with hφ1
  have hφ1e : φ1 = 1 + G 0 := by simp [hφ1, hG, hF]
  have hG0 : ‖G 0‖ ≤ 1 / 2 := by
    have := b0 0
    simp only [hG]
    refine this.trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hpx hC0, hp0]
  have hφn : 1 / 2 ≤ ‖φ1‖ := by
    rw [hφ1e]
    have := norm_sub_norm_le (1 : ℂ) (-(G 0))
    rw [sub_neg_eq_add, norm_neg, norm_one] at this
    linarith
  have hφ0 : φ1 ≠ 0 := fun h => by rw [h, norm_zero] at hφn; linarith
  have hinv : ‖φ1⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have hpos : 0 < ‖φ1‖ := by linarith
    rw [inv_le_comm₀ hpos (by norm_num)]; linarith
  have hQ : (fun τ : ℝ => uctPhi c δ (1 - (τ : ℂ) * Complex.I) / uctPhi c δ 1) = fun τ => φ1⁻¹ * (1 + G τ) := by
    funext τ
    simp only [hG, hF, hφ1]
    rw [div_eq_inv_mul]
    congr 2
    have : (1 : ℂ) + (-Complex.I) * (τ : ℂ) = 1 - (τ : ℂ) * Complex.I := by ring
    rw [this]; ring
  rw [hQ]
  have hd1 : deriv (fun τ : ℝ => φ1⁻¹ * (1 + G τ)) = fun τ => φ1⁻¹ * deriv G τ := by
    funext τ
    rw [deriv_const_mul_field, deriv_const_add]
  have hd2 : deriv (deriv (fun τ : ℝ => φ1⁻¹ * (1 + G τ))) = fun τ => φ1⁻¹ * deriv (deriv G) τ := by
    rw [hd1]; funext τ; exact deriv_const_mul_field _
  have hd3 : deriv (deriv (deriv (fun τ : ℝ => φ1⁻¹ * (1 + G τ)))) = fun τ => φ1⁻¹ * deriv (deriv (deriv G)) τ := by
    rw [hd2]; funext τ; exact deriv_const_mul_field _
  refine ⟨contDiff_const.mul (contDiff_const.add hGc), fun τ hτ => ?_⟩
  rw [hd3, hd2, hd1]
  have hτ0 := abs_nonneg τ
  have hK0 : 0 ≤ 2 * (C1 + C2 + C3) := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : φ1⁻¹ * (1 + G τ) - 1 = φ1⁻¹ * (G τ - G 0) := by
      calc φ1⁻¹ * (1 + G τ) - 1 = φ1⁻¹ * (1 + G τ) - φ1⁻¹ * φ1 := by rw [inv_mul_cancel₀ hφ0]
        _ = φ1⁻¹ * (G τ - G 0) := by rw [hφ1e]; ring
    rw [e, norm_mul]
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (f := G) (s := univ) (C := C1 * p)
      (fun x _ => (cd3_diffs hGc).1 x) (fun x _ => b1 x) convex_univ (mem_univ 0) (mem_univ τ)
    rw [sub_zero, Real.norm_eq_abs] at hmv
    have h1' : ‖φ1⁻¹‖ * ‖G τ - G 0‖ ≤ 2 * (C1 * p * |τ|) :=
      mul_le_mul hinv hmv (norm_nonneg _) (by norm_num)
    nlinarith [mul_nonneg hp0 hτ0, mul_nonneg hC1 (mul_nonneg hp0 hτ0), mul_nonneg hK0 (sq_nonneg τ),
      mul_nonneg (mul_nonneg hp0 hτ0) (add_nonneg hC2 hC3)]
  · rw [norm_mul]
    have := mul_le_mul hinv (b1 τ) (norm_nonneg _) (by norm_num)
    nlinarith [mul_nonneg hC1 hp0, mul_nonneg hK0 hτ0, mul_nonneg (add_nonneg hC2 hC3) hp0]
  · rw [norm_mul]
    have := mul_le_mul hinv (b2 τ) (norm_nonneg _) (by norm_num)
    nlinarith [mul_nonneg hC2 hp0, mul_le_mul_of_nonneg_left hp1 hC2, hC1, hC3]
  · rw [norm_mul]
    have := mul_le_mul hinv (b3 τ) (norm_nonneg _) (by norm_num)
    nlinarith [mul_nonneg hC3 hp0, mul_le_mul_of_nonneg_left hp1 hC3, hC1, hC2]

/-- info: 'FormalResearch.SignUncertainty.line_deriv3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms line_deriv3

/-- info: 'FormalResearch.SignUncertainty.smallBd_phiQuot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms smallBd_phiQuot

end FormalResearch.SignUncertainty
