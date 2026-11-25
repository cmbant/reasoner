module

public import FormalResearch.CohnElkies.CubicNormalFormBridge

/-!
# Lemma `O.4(2)`: the quotient bound `O4QuotientBound` from the quarter circle (`u1co:O4`)

Notation: `Φ̂ = o4PhiHat L`, `Φ_mod = o4PhiMod L`, `θ₀ = o4Theta0 L`, `𝓕 = o4Quot L`, and
`N = o4Num L = Φ̂ - Φ_mod`.

* **Extension without the bound** (`o4c_factorization`). `N` vanishes at `0` and has double zeros at `±θ₀`:
  `Φ̂(θ₀) = Φ_mod(θ₀)`, and both derivatives vanish at `±θ₀`, since `Φ_mod' = α̃ - π² θ²/12` and
  `Φ̂' = σ₀ Φ_L'(τ₀)` with `Φ_L'(τ₀) = edgePhiDeriv L τ₀ = L - ceEll(π τ₀ / 2) = 0`. Three Newton-quotient steps
  (`dslope`) give `N(θ) = θ (θ - θ₀)² (θ + θ₀)² G(θ)` with `G` holomorphic on `D(0, 1/2)`. Proved, unconditionally.
* **Maximum principle** (`o4QuotientBound_of_circle`). Off the three points `G = 𝓕`. `G` is holomorphic on a
  neighbourhood of the closed disc of radius `1/4`, so the bound on the circle `|θ| = 1/4` gives `‖𝓕‖ ≤ 0.13`
  on the open disc.
* **Symmetry and the quarter arc** (`o4QuotientBound_of_quarter`). `𝓕` is even and `𝓕(conj θ) = conj 𝓕(θ)`, so
  every point of the circle has the same `‖𝓕‖` as a first-quadrant point, and the first-quadrant points of the
  circle are exactly `(1/4)(1 - t² + 2it)/(1 + t²)` with `t ∈ [0, 1]`.
-/

@[expose] public section

open Metric Set Filter Topology Complex Function
open scoped Real

namespace FormalResearch.CohnElkies

/-! ### Newton quotients of a function vanishing at a point -/

/-- If `g c = 0`, then `g z = (z - c) · dslope g c z` and `dslope g c` is holomorphic on `s`. -/
lemma o4c_factor {g : ℂ → ℂ} {c : ℂ} {s : Set ℂ} (hs : s ∈ 𝓝 c) (hg : DifferentiableOn ℂ g s)
    (h0 : g c = 0) :
    DifferentiableOn ℂ (dslope g c) s ∧ ∀ z, g z = (z - c) * dslope g c z := by
  refine ⟨(differentiableOn_dslope hs).mpr hg, fun z => ?_⟩
  by_cases hz : z = c
  · subst hz; simp [h0]
  · have hzc : z - c ≠ 0 := sub_ne_zero.mpr hz
    rw [dslope_of_ne _ hz, slope_def_field, h0, sub_zero]
    field_simp

/-- If `g c = 0` and `deriv g c = 0`, then `g z = (z - c)² · G z` with `G` holomorphic on `s`. -/
lemma o4c_factor2 {g : ℂ → ℂ} {c : ℂ} {s : Set ℂ} (hs : s ∈ 𝓝 c) (hg : DifferentiableOn ℂ g s)
    (h0 : g c = 0) (h1 : deriv g c = 0) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G s ∧ ∀ z, g z = (z - c) ^ 2 * G z := by
  obtain ⟨hd, hid⟩ := o4c_factor hs hg h0
  obtain ⟨hd2, hid2⟩ := o4c_factor hs hd (by rw [dslope_same, h1])
  exact ⟨dslope (dslope g c) c, hd2, fun z => by rw [hid z, hid2 z]; ring⟩

/-! ### Derivatives and symmetries of the phases -/

section phases

variable {L : ℝ}

lemma o4c_sigma_norm (hL0 : 0 < L) (hL2 : L ≤ 0.002) {θ : ℂ} (hθ : ‖θ‖ ≤ 0.5) :
    ‖(o4Sigma0 L : ℂ) * θ‖ < 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (o4Sigma0_pos hL0)]
  have h := o4Sigma0_le hL0 hL2
  nlinarith [norm_nonneg θ, o4Sigma0_pos hL0]

lemma o4c_PhiHat_neg (hL0 : 0 < L) (hL2 : L ≤ 0.002) {θ : ℂ} (hθ : ‖θ‖ ≤ 0.5) :
    o4PhiHat L (-θ) = -o4PhiHat L θ := by
  unfold o4PhiHat
  rw [mul_neg, edgePhiC_neg L (o4c_sigma_norm hL0 hL2 hθ)]

lemma o4c_PhiHat_hasDerivAt (hL0 : 0 < L) (hL2 : L ≤ 0.002) {z : ℂ} (hz : ‖z‖ ≤ 0.5) :
    HasDerivAt (o4PhiHat L)
      (((L : ℂ) + stripG (Complex.I * ((o4Sigma0 L : ℂ) * z))) * (o4Sigma0 L : ℂ)) z := by
  have h1 := hasDerivAt_edgePhiC L (o4c_sigma_norm hL0 hL2 hz)
  have h2 : HasDerivAt (fun w : ℂ => (o4Sigma0 L : ℂ) * w) (o4Sigma0 L : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul (o4Sigma0 L : ℂ)
  exact h1.comp z h2

lemma o4c_PhiMod_hasDerivAt (z : ℂ) :
    HasDerivAt (o4PhiMod L) ((edgeAlphaTilde L : ℂ) - (π : ℂ) ^ 2 / 12 * z ^ 2) z := by
  have h := ((hasDerivAt_id' z).const_mul (edgeAlphaTilde L : ℂ)).sub
    ((hasDerivAt_pow 3 z).const_mul ((π : ℂ) ^ 2 / 36))
  convert h using 1
  · funext y; simp [o4PhiMod]
  · norm_num; ring

lemma o4c_theta0_norm (hL0 : 0 < L) (hL2 : L ≤ 0.002) : ‖(o4Theta0 L : ℂ)‖ < 0.05 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (o4Theta0_pos hL0)]
  exact o4Theta0_lt hL0 hL2

lemma o4c_theta0_sq (hL0 : 0 < L) : (o4Theta0 L : ℂ) ^ 2 = (o4Theta0Sq L : ℂ) := by
  exact_mod_cast o4Theta0_sq hL0

lemma o4c_tau0_abs (hL0 : 0 < L) (hL2 : L ≤ 0.002) : |tau0 L| < 1 := by
  rw [abs_of_pos (tau0_pos hL0)]
  linarith [(tau0_bounds hL0 hL2).1]

/-- `edgePhiDeriv L τ₀ = 0`: the saddle `τ₀` is the critical point of `Φ_L` on the real axis. -/
lemma o4c_edgePhiDeriv_tau0 (hL0 : 0 < L) : edgePhiDeriv L (tau0 L) = 0 := by
  have h := ceEll_tau0 hL0
  unfold ceEll at h
  unfold edgePhiDeriv
  rw [ite_eq_right (tau0_pos hL0).ne', abs_of_pos (tau0_pos hL0)]
  rw [show Real.tanh (π * tau0 L / 2) / (π * tau0 L / 2)
      = (π * tau0 L / 2 / Real.tanh (π * tau0 L / 2))⁻¹ by rw [inv_div], Real.log_inv]
  linarith

lemma o4c_alpha_eq (hL0 : 0 < L) :
    (edgeAlphaTilde L : ℂ) - (π : ℂ) ^ 2 / 12 * (o4Theta0 L : ℂ) ^ 2 = 0 := by
  rw [o4c_theta0_sq hL0]
  unfold o4Theta0Sq
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring

lemma o4c_alpha_eq_neg (hL0 : 0 < L) :
    (edgeAlphaTilde L : ℂ) - (π : ℂ) ^ 2 / 12 * (-(o4Theta0 L : ℂ)) ^ 2 = 0 := by
  rw [neg_sq]; exact o4c_alpha_eq hL0

/-- `N = Φ̂ - Φ_mod` as a function, so that its derivative can be taken. -/
noncomputable def o4Num (L : ℝ) (θ : ℂ) : ℂ := o4PhiHat L θ - o4PhiMod L θ

lemma o4c_N_hasDerivAt_pos (hL0 : 0 < L) (hL2 : L ≤ 0.002) :
    HasDerivAt (o4Num L) 0 (o4Theta0 L : ℂ) := by
  have hn : ‖(o4Theta0 L : ℂ)‖ ≤ 0.5 := (o4c_theta0_norm hL0 hL2).le.trans (by norm_num)
  have hτ : (o4Sigma0 L : ℂ) * (o4Theta0 L : ℂ) = (tau0 L : ℂ) := by
    exact_mod_cast o4Sigma0_mul hL0
  have hLd : (L : ℂ) + stripG (Complex.I * (tau0 L : ℂ)) = 0 := by
    rw [edgePhiC_deriv_ofReal L (o4c_tau0_abs hL0 hL2), o4c_edgePhiDeriv_tau0 hL0]
    simp
  have h := (o4c_PhiHat_hasDerivAt hL0 hL2 hn).sub (o4c_PhiMod_hasDerivAt (L := L) (o4Theta0 L : ℂ))
  rw [hτ, hLd, o4c_alpha_eq hL0] at h
  exact h.congr_deriv (by ring)

lemma o4c_N_hasDerivAt_neg (hL0 : 0 < L) (hL2 : L ≤ 0.002) :
    HasDerivAt (o4Num L) 0 (-(o4Theta0 L : ℂ)) := by
  have hn : ‖-(o4Theta0 L : ℂ)‖ ≤ 0.5 := by
    rw [norm_neg]; exact (o4c_theta0_norm hL0 hL2).le.trans (by norm_num)
  have hτ : (o4Sigma0 L : ℂ) * (o4Theta0 L : ℂ) = (tau0 L : ℂ) := by
    exact_mod_cast o4Sigma0_mul hL0
  have hLd : (L : ℂ) + stripG (Complex.I * (tau0 L : ℂ)) = 0 := by
    rw [edgePhiC_deriv_ofReal L (o4c_tau0_abs hL0 hL2), o4c_edgePhiDeriv_tau0 hL0]
    simp
  have h := (o4c_PhiHat_hasDerivAt hL0 hL2 hn).sub (o4c_PhiMod_hasDerivAt (L := L) (-(o4Theta0 L : ℂ)))
  rw [mul_neg, hτ, stripG_I_mul_neg, hLd, o4c_alpha_eq_neg hL0] at h
  exact h.congr_deriv (by ring)

lemma o4Num_zero : o4Num L 0 = 0 := by
  unfold o4Num; simp [o4PhiHat_zero, o4PhiMod_zero]

lemma o4Num_theta0 (hL0 : 0 < L) (hL2 : L ≤ 0.002) : o4Num L (o4Theta0 L : ℂ) = 0 :=
  sub_eq_zero.mpr (o4PhiHat_theta0 hL0 hL2)

lemma o4Num_neg_theta0 (hL0 : 0 < L) (hL2 : L ≤ 0.002) : o4Num L (-(o4Theta0 L : ℂ)) = 0 := by
  have h := o4Num_theta0 hL0 hL2
  have hn : ‖(o4Theta0 L : ℂ)‖ ≤ 0.5 := (o4c_theta0_norm hL0 hL2).le.trans (by norm_num)
  unfold o4Num at h ⊢
  rw [o4c_PhiHat_neg hL0 hL2 hn, o4PhiMod_neg]
  linear_combination -h

lemma o4c_quot_neg (hL0 : 0 < L) (hL2 : L ≤ 0.002) {θ : ℂ} (hθ : ‖θ‖ ≤ 0.5) :
    o4Quot L (-θ) = o4Quot L θ := by
  unfold o4Quot
  rw [o4c_PhiHat_neg hL0 hL2 hθ, o4PhiMod_neg, show (-θ) ^ 2 = θ ^ 2 by ring,
    show -θ * (θ ^ 2 - (o4Theta0Sq L : ℂ)) ^ 2 = -(θ * (θ ^ 2 - (o4Theta0Sq L : ℂ)) ^ 2) by ring,
    show -o4PhiHat L θ - -o4PhiMod L θ = -(o4PhiHat L θ - o4PhiMod L θ) by ring, neg_div_neg_eq]

lemma o4c_quot_conj (hL0 : 0 < L) (hL2 : L ≤ 0.002) {θ : ℂ} (hθ : ‖θ‖ ≤ 0.5) :
    o4Quot L ((starRingEnd ℂ) θ) = (starRingEnd ℂ) (o4Quot L θ) := by
  have hσ := o4c_sigma_norm hL0 hL2 hθ
  unfold o4Quot o4PhiHat o4PhiMod
  have hc1 : (o4Sigma0 L : ℂ) * (starRingEnd ℂ) θ = (starRingEnd ℂ) ((o4Sigma0 L : ℂ) * θ) := by
    simp [map_mul, Complex.conj_ofReal]
  rw [hc1, edgePhiC_conj L hσ]
  simp [map_sub, map_mul, map_div₀, map_pow, Complex.conj_ofReal, map_ofNat]

end phases

/-! ### The extension across `0, ±θ₀` without the bound -/

section extension

variable {L : ℝ}

/-- `N = θ (θ - θ₀)² (θ + θ₀)² G` on `D(0, 1/2)` with `G` holomorphic: the three singularities of `𝓕` are
removable, with no bound assumed. -/
lemma o4c_factorization (hL0 : 0 < L) (hL2 : L ≤ 0.002) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball (0 : ℂ) 0.5) ∧
      ∀ θ ∈ ball (0 : ℂ) 0.5, o4PhiHat L θ - o4PhiMod L θ =
        θ * ((θ - (o4Theta0 L : ℂ)) ^ 2 * (θ + (o4Theta0 L : ℂ)) ^ 2) * G θ := by
  have hSt : ∀ c : ℂ, c ∈ ball (0 : ℂ) 0.5 → ball (0 : ℂ) 0.5 ∈ 𝓝 c :=
    fun c hc => isOpen_ball.mem_nhds hc
  have hS0 : ball (0 : ℂ) 0.5 ∈ 𝓝 (0 : ℂ) := hSt 0 (mem_ball_self (by norm_num))
  have hNd : DifferentiableOn ℂ (o4Num L) (ball (0 : ℂ) 0.5) := by
    intro θ hθ
    have hθ' : ‖θ‖ ≤ 0.5 := (mem_ball_zero_iff.mp hθ).le
    exact ((o4c_PhiHat_hasDerivAt hL0 hL2 hθ').sub (o4c_PhiMod_hasDerivAt θ)).differentiableAt
      |>.differentiableWithinAt
  have htS : (o4Theta0 L : ℂ) ∈ ball (0 : ℂ) 0.5 :=
    mem_ball_zero_iff.mpr ((o4c_theta0_norm hL0 hL2).trans (by norm_num))
  have htneg : -(o4Theta0 L : ℂ) ∈ ball (0 : ℂ) 0.5 := by
    rw [mem_ball_zero_iff, norm_neg]
    exact (o4c_theta0_norm hL0 hL2).trans (by norm_num)
  have ht0 : (o4Theta0 L : ℂ) ≠ 0 := by exact_mod_cast (o4Theta0_pos hL0).ne'
  -- step 0: the simple zero at `0`
  obtain ⟨F1d, F1id⟩ := o4c_factor hS0 hNd o4Num_zero
  obtain ⟨F1, hF1⟩ : ∃ F1 : ℂ → ℂ, F1 = dslope (o4Num L) 0 := ⟨_, rfl⟩
  have hF1d : DifferentiableOn ℂ F1 (ball (0 : ℂ) 0.5) := by rw [hF1]; exact F1d
  have hF1id : ∀ z, o4Num L z = z * F1 z := fun z => by
    rw [F1id z, hF1, sub_zero]
  -- step 1: the double zero at `θ₀`
  have hF1t : F1 (o4Theta0 L : ℂ) = 0 := by
    have h := hF1id (o4Theta0 L : ℂ)
    rw [o4Num_theta0 hL0 hL2] at h
    exact (mul_eq_zero.mp h.symm).resolve_left ht0
  have hF1t' : deriv F1 (o4Theta0 L : ℂ) = 0 := by
    have hdiff : DifferentiableAt ℂ F1 (o4Theta0 L : ℂ) := hF1d.differentiableAt (hSt _ htS)
    have hprod : HasDerivAt (fun z => z * F1 z) (1 * F1 (o4Theta0 L : ℂ) + (o4Theta0 L : ℂ) *
        deriv F1 (o4Theta0 L : ℂ)) (o4Theta0 L : ℂ) :=
      (hasDerivAt_id' _).mul hdiff.hasDerivAt
    have hev : o4Num L =ᶠ[𝓝 (o4Theta0 L : ℂ)] fun z => z * F1 z :=
      Filter.eventually_of_mem (hSt _ htS) (fun z _ => hF1id z)
    have hu := (hprod.congr_of_eventuallyEq hev).unique (o4c_N_hasDerivAt_pos hL0 hL2)
    rw [hF1t] at hu
    have h2 : (o4Theta0 L : ℂ) * deriv F1 (o4Theta0 L : ℂ) = 0 := by linear_combination hu
    exact (mul_eq_zero.mp h2).resolve_left ht0
  obtain ⟨Gt, hGtd, hGt⟩ := o4c_factor2 (hSt _ htS) hF1d hF1t hF1t'
  -- step 2: the double zero at `-θ₀`, for the factor `Gt`
  have hGneg : Gt (-(o4Theta0 L : ℂ)) = 0 := by
    have h := o4Num_neg_theta0 hL0 hL2
    rw [hF1id, hGt] at h
    have h2 : (-(o4Theta0 L : ℂ)) * (-(o4Theta0 L : ℂ) - o4Theta0 L) ^ 2 * Gt (-(o4Theta0 L : ℂ)) = 0 := by
      linear_combination h
    have hfac : (-(o4Theta0 L : ℂ)) * (-(o4Theta0 L : ℂ) - o4Theta0 L) ^ 2 ≠ 0 := by
      have e : (-(o4Theta0 L : ℂ)) * (-(o4Theta0 L : ℂ) - o4Theta0 L) ^ 2 =
          -4 * (o4Theta0 L : ℂ) ^ 3 := by ring
      rw [e]
      exact mul_ne_zero (by norm_num) (pow_ne_zero _ ht0)
    exact (mul_eq_zero.mp h2).resolve_left hfac
  have hGneg' : deriv Gt (-(o4Theta0 L : ℂ)) = 0 := by
    have hsq : HasDerivAt (fun z : ℂ => (z - (o4Theta0 L : ℂ)) ^ 2)
        (2 * (-(o4Theta0 L : ℂ) - o4Theta0 L)) (-(o4Theta0 L : ℂ)) := by
      have := ((hasDerivAt_id' (-(o4Theta0 L : ℂ))).sub_const (o4Theta0 L : ℂ)).pow 2
      convert this using 1
      norm_num
    have hGder : HasDerivAt Gt (deriv Gt (-(o4Theta0 L : ℂ))) (-(o4Theta0 L : ℂ)) :=
      (hGtd.differentiableAt (hSt _ htneg)).hasDerivAt
    have hprod : HasDerivAt (fun z => z * ((z - (o4Theta0 L : ℂ)) ^ 2 * Gt z))
        (1 * ((-(o4Theta0 L : ℂ) - o4Theta0 L) ^ 2 * Gt (-(o4Theta0 L : ℂ))) +
          (-(o4Theta0 L : ℂ)) * (2 * (-(o4Theta0 L : ℂ) - o4Theta0 L) * Gt (-(o4Theta0 L : ℂ)) +
            (-(o4Theta0 L : ℂ) - o4Theta0 L) ^ 2 * deriv Gt (-(o4Theta0 L : ℂ))))
        (-(o4Theta0 L : ℂ)) :=
      (hasDerivAt_id' _).mul (hsq.mul hGder)
    have hev : o4Num L =ᶠ[𝓝 (-(o4Theta0 L : ℂ))] fun z => z * ((z - (o4Theta0 L : ℂ)) ^ 2 * Gt z) :=
      Filter.eventually_of_mem (hSt _ htneg) (fun z _ => by rw [hF1id, hGt])
    have hu := (hprod.congr_of_eventuallyEq hev).unique (o4c_N_hasDerivAt_neg hL0 hL2)
    rw [hGneg] at hu
    have h2 : (-(o4Theta0 L : ℂ)) * (-(o4Theta0 L : ℂ) - o4Theta0 L) ^ 2 * deriv Gt (-(o4Theta0 L : ℂ)) = 0 := by
      linear_combination hu
    have hfac : (-(o4Theta0 L : ℂ)) * (-(o4Theta0 L : ℂ) - o4Theta0 L) ^ 2 ≠ 0 := by
      have e : (-(o4Theta0 L : ℂ)) * (-(o4Theta0 L : ℂ) - o4Theta0 L) ^ 2 =
          -4 * (o4Theta0 L : ℂ) ^ 3 := by ring
      rw [e]
      exact mul_ne_zero (by norm_num) (pow_ne_zero _ ht0)
    exact (mul_eq_zero.mp h2).resolve_left hfac
  obtain ⟨Gm, hGmd, hGm⟩ := o4c_factor2 (hSt _ htneg) hGtd hGneg hGneg'
  refine ⟨Gm, hGmd, fun θ _ => ?_⟩
  have e1 := hF1id θ
  have e2 := hGt θ
  have e3 := hGm θ
  show o4Num L θ = _
  rw [e1, e2, e3]
  ring

/-- Off the three points, the factor `G` equals the quotient `𝓕`. -/
lemma o4c_quot_eq (hL0 : 0 < L) {G : ℂ → ℂ}
    (hG : ∀ θ ∈ ball (0 : ℂ) 0.5, o4PhiHat L θ - o4PhiMod L θ =
      θ * ((θ - (o4Theta0 L : ℂ)) ^ 2 * (θ + (o4Theta0 L : ℂ)) ^ 2) * G θ)
    {θ : ℂ} (hθ : θ ∈ ball (0 : ℂ) 0.5) (h0 : θ ≠ 0) (h1 : θ ≠ (o4Theta0 L : ℂ))
    (h2 : θ ≠ -(o4Theta0 L : ℂ)) :
    o4Quot L θ = G θ := by
  have h3 : θ + (o4Theta0 L : ℂ) ≠ 0 := fun h => h2 (eq_neg_of_add_eq_zero_left h)
  have hden : θ * (θ ^ 2 - (o4Theta0Sq L : ℂ)) ^ 2 ≠ 0 := by
    rw [← o4c_theta0_sq hL0]
    have e : θ ^ 2 - (o4Theta0 L : ℂ) ^ 2 = (θ - (o4Theta0 L : ℂ)) * (θ + (o4Theta0 L : ℂ)) := by ring
    rw [e, mul_pow]
    exact mul_ne_zero h0 (mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr h1)) (pow_ne_zero _ h3))
  unfold o4Quot
  rw [div_eq_iff hden, hG θ hθ, ← o4c_theta0_sq hL0]
  ring

end extension

/-! ### The maximum principle: the circle bound gives the disc bound -/

/-- **Reduction to the circle.** The bound `‖𝓕‖ ≤ 0.13` on the circle `|θ| = 1/4` gives
`O4QuotientBound L` (maximum principle for the holomorphic extension of `𝓕`). -/
theorem o4QuotientBound_of_circle {L : ℝ} (hL0 : 0 < L) (hL2 : L ≤ 0.002)
    (hC : ∀ θ : ℂ, ‖θ‖ = 0.25 → ‖o4Quot L θ‖ ≤ 0.13) : O4QuotientBound L := by
  obtain ⟨G, hGd, hG⟩ := o4c_factorization hL0 hL2
  have hsub : closedBall (0 : ℂ) 0.25 ⊆ ball (0 : ℂ) 0.5 := closedBall_subset_ball (by norm_num)
  have hd : DiffContOnCl ℂ G (ball (0 : ℂ) 0.25) := hGd.diffContOnCl_ball hsub
  have hfr : ∀ z ∈ frontier (ball (0 : ℂ) 0.25), ‖G z‖ ≤ 0.13 := by
    intro z hz
    rw [frontier_ball (0 : ℂ) (by norm_num), mem_sphere_zero_iff_norm] at hz
    have hzS : z ∈ ball (0 : ℂ) 0.5 := mem_ball_zero_iff.mpr (by rw [hz]; norm_num)
    have h0 : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hz; norm_num at hz
    have h1 : z ≠ (o4Theta0 L : ℂ) := by
      intro h
      have hn := o4c_theta0_norm hL0 hL2
      rw [← h, hz] at hn; norm_num at hn
    have h2 : z ≠ -(o4Theta0 L : ℂ) := by
      intro h
      have hn := o4c_theta0_norm hL0 hL2
      rw [← norm_neg, ← h, hz] at hn; norm_num at hn
    rw [← o4c_quot_eq hL0 hG hzS h0 h1 h2]
    exact hC z hz
  unfold O4QuotientBound
  intro θ hθ h0 h1 h2
  have hθS : θ ∈ ball (0 : ℂ) 0.5 := mem_ball_zero_iff.mpr (lt_trans hθ (by norm_num))
  have hθU : θ ∈ ball (0 : ℂ) 0.25 := mem_ball_zero_iff.mpr hθ
  rw [o4c_quot_eq hL0 hG hθS h0 h1 h2]
  exact Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd hfr (subset_closure hθU)

/-! ### The first-quadrant arc and the symmetry reduction -/

/-- Every `φ` with `|φ| = 1/4`, `Re φ ≥ 0`, `Im φ ≥ 0` is `(1/4)(1 - t² + 2it)/(1 + t²)` for some `t ∈ [0, 1]`. -/
lemma o4c_quarter_param {φ : ℂ} (hn : ‖φ‖ = 1 / 4) (hre : 0 ≤ φ.re) (him : 0 ≤ φ.im) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      φ = ((1 / 4 : ℝ) : ℂ) * (((1 - t ^ 2 : ℝ) : ℂ) + (2 * t : ℝ) * Complex.I) / ((1 + t ^ 2 : ℝ) : ℂ) := by
  have hsq : φ.re * φ.re + φ.im * φ.im = 1 / 16 := by
    have h := Complex.sq_norm φ
    rw [hn, Complex.normSq_apply] at h
    linarith
  have hs0 : 0 < 1 + 4 * φ.re := by linarith
  have ht1 : 4 * φ.im / (1 + 4 * φ.re) ≤ 1 := by
    rw [div_le_one hs0]
    nlinarith [mul_self_nonneg φ.re]
  set t : ℝ := 4 * φ.im / (1 + 4 * φ.re) with htdef
  have ht : t * (1 + 4 * φ.re) = 4 * φ.im := div_mul_cancel₀ _ hs0.ne'
  have key : t ^ 2 * (1 + 4 * φ.re) = 1 - 4 * φ.re := by
    apply mul_left_cancel₀ hs0.ne'
    linear_combination (t * (1 + 4 * φ.re) + 4 * φ.im) * ht + 16 * hsq
  refine ⟨t, div_nonneg (by linarith) hs0.le, ht1, ?_⟩
  have hC0 : ((1 + t ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (0 : ℝ) < 1 + t ^ 2).ne'
  rw [eq_div_iff hC0]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
    linear_combination (1 / 4 : ℝ) * key
  · simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
    linear_combination (-(1 + t ^ 2) / 4 : ℝ) * ht + (t / 4 : ℝ) * key

/-- The bound on the first-quadrant arc, read at any point of the circle of radius `1/4`. -/
lemma o4c_quot_quarter {L : ℝ} (hL0 : 0 < L) (hL2 : L ≤ 0.002)
    (hQ : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖o4Quot L (((1 / 4 : ℝ) : ℂ) * (((1 - t ^ 2 : ℝ) : ℂ) + (2 * t : ℝ) * Complex.I) / ((1 + t ^ 2 : ℝ) : ℂ))‖ ≤ 0.13)
    {φ : ℂ} (hn : ‖φ‖ = 1 / 4) : ‖o4Quot L φ‖ ≤ 0.13 := by
  have hfirst : ∀ ψ : ℂ, ‖ψ‖ = 1 / 4 → 0 ≤ ψ.re → 0 ≤ ψ.im → ‖o4Quot L ψ‖ ≤ 0.13 := by
    intro ψ hψ hre him
    obtain ⟨t, h0, h1, rfl⟩ := o4c_quarter_param hψ hre him
    exact hQ t h0 h1
  have hnh : ‖φ‖ ≤ 0.5 := by rw [hn]; norm_num
  rcases le_total 0 φ.re with hre | hre <;> rcases le_total 0 φ.im with him | him
  · exact hfirst φ hn hre him
  · -- conjugate lies in the first quadrant
    have e := o4c_quot_conj hL0 hL2 hnh
    have h := hfirst (starRingEnd ℂ φ) (by rw [Complex.norm_conj, hn])
      (by rw [Complex.conj_re]; exact hre) (by rw [Complex.conj_im]; linarith)
    rw [e, Complex.norm_conj] at h
    exact h
  · -- minus the conjugate lies in the first quadrant
    have hnc : ‖starRingEnd ℂ φ‖ ≤ 0.5 := by rw [Complex.norm_conj]; exact hnh
    have e := o4c_quot_conj hL0 hL2 hnh
    have h := hfirst (-(starRingEnd ℂ φ)) (by rw [norm_neg, Complex.norm_conj, hn])
      (by rw [Complex.neg_re, Complex.conj_re]; linarith) (by rw [Complex.neg_im, Complex.conj_im]; linarith)
    rw [o4c_quot_neg hL0 hL2 hnc, e, Complex.norm_conj] at h
    exact h
  · -- minus the point lies in the first quadrant
    have h := hfirst (-φ) (by rw [norm_neg, hn])
      (by rw [Complex.neg_re]; linarith) (by rw [Complex.neg_im]; linarith)
    rw [o4c_quot_neg hL0 hL2 hnh] at h
    exact h

/-- **Reduction to the quarter arc.** `𝓕` is even and commutes with conjugation, so the circle bound
follows from the bound on the first-quadrant arc `θ(t) = (1/4)(1 - t² + 2it)/(1 + t²)`, `t ∈ [0, 1]`. -/
theorem o4QuotientBound_of_quarter {L : ℝ} (hL0 : 0 < L) (hL2 : L ≤ 0.002)
    (hQ : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖o4Quot L (((1 / 4 : ℝ) : ℂ) * (((1 - t ^ 2 : ℝ) : ℂ) + (2 * t : ℝ) * Complex.I) / ((1 + t ^ 2 : ℝ) : ℂ))‖ ≤ 0.13) :
    O4QuotientBound L :=
  o4QuotientBound_of_circle hL0 hL2 (fun θ hθ => o4c_quot_quarter hL0 hL2 hQ (by rw [hθ]; norm_num))

/-- info: 'FormalResearch.CohnElkies.o4c_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalResearch.CohnElkies.o4c_factor

/-- info: 'FormalResearch.CohnElkies.o4c_factor2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalResearch.CohnElkies.o4c_factor2

/-- info: 'FormalResearch.CohnElkies.o4c_sigma_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalResearch.CohnElkies.o4c_sigma_norm

/-- info: 'FormalResearch.CohnElkies.o4c_PhiHat_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalResearch.CohnElkies.o4c_PhiHat_neg

/-- info: 'FormalResearch.CohnElkies.o4c_PhiHat_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalResearch.CohnElkies.o4c_PhiHat_hasDerivAt

/-- info: 'FormalResearch.CohnElkies.o4c_PhiMod_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalResearch.CohnElkies.o4c_PhiMod_hasDerivAt

/-- info: 'FormalResearch.CohnElkies.o4c_theta0_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalResearch.CohnElkies.o4c_theta0_norm

/-- info: 'FormalResearch.CohnElkies.o4c_theta0_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalResearch.CohnElkies.o4c_theta0_sq

/-- info: 'FormalResearch.CohnElkies.o4c_tau0_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalResearch.CohnElkies.o4c_tau0_abs

/-- info: 'FormalResearch.CohnElkies.o4c_edgePhiDeriv_tau0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalResearch.CohnElkies.o4c_edgePhiDeriv_tau0

/-- info: 'FormalResearch.CohnElkies.o4c_alpha_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalResearch.CohnElkies.o4c_alpha_eq

/-- info: 'FormalResearch.CohnElkies.o4c_alpha_eq_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalResearch.CohnElkies.o4c_alpha_eq_neg

/-- info: 'FormalResearch.CohnElkies.o4c_N_hasDerivAt_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalResearch.CohnElkies.o4c_N_hasDerivAt_pos

/-- info: 'FormalResearch.CohnElkies.o4c_N_hasDerivAt_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalResearch.CohnElkies.o4c_N_hasDerivAt_neg

/-- info: 'FormalResearch.CohnElkies.o4Num_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalResearch.CohnElkies.o4Num_zero

/-- info: 'FormalResearch.CohnElkies.o4Num_theta0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalResearch.CohnElkies.o4Num_theta0

/-- info: 'FormalResearch.CohnElkies.o4Num_neg_theta0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalResearch.CohnElkies.o4Num_neg_theta0

/-- info: 'FormalResearch.CohnElkies.o4c_quot_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalResearch.CohnElkies.o4c_quot_neg

/-- info: 'FormalResearch.CohnElkies.o4c_quot_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalResearch.CohnElkies.o4c_quot_conj

/-- info: 'FormalResearch.CohnElkies.o4c_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalResearch.CohnElkies.o4c_factorization

/-- info: 'FormalResearch.CohnElkies.o4c_quot_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalResearch.CohnElkies.o4c_quot_eq

/-- info: 'FormalResearch.CohnElkies.o4QuotientBound_of_circle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalResearch.CohnElkies.o4QuotientBound_of_circle

/-- info: 'FormalResearch.CohnElkies.o4c_quarter_param' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalResearch.CohnElkies.o4c_quarter_param

/-- info: 'FormalResearch.CohnElkies.o4c_quot_quarter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalResearch.CohnElkies.o4c_quot_quarter

/-- info: 'FormalResearch.CohnElkies.o4QuotientBound_of_quarter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalResearch.CohnElkies.o4QuotientBound_of_quarter

end FormalResearch.CohnElkies
