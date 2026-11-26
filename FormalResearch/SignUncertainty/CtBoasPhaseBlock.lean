module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasFarPhase
public import FormalResearch.SignUncertainty.CtBoasPlbField

/-!
# `ct:boas-ineq`: the phase of the concrete band kernel on a block (freezing, derivative-free)

`constant_terms_lower.tex`, proof of `ct:boas` Step 5 ("Estimate of `D_j` on the whole line"): for `X = Ξ - θ_ε ∘ τ₀`,
`Ξ(L) = cΦ(L)`, `Φ(L) = Φ_Ph(τ₀(L); L)`, the frozen phase `X(L₀) + ν(L₀)(L - L₀)`, `ν = cτ₀`, satisfies, for `L, L₀` in a block
where `τ₀ ∈ [r/3, 3r]`,
`|X(L₀) + ν(L₀)(L - L₀) - X(L)| ≤ C_l|L - L₀| + C_q(L - L₀)²`, `C_q = cΛ`, `C_l = Λ C_θ/(1 + r/3)²`, `Λ = 27(1 + r²)/r`.

The TeX uses `Ξ' = cτ₀`, `Ξ'' = c/m'(τ₀)` and Taylor's theorem.  Here the same estimate is derivative-free:

* `edgePhi_tau0_ge` / `phi_legendre`: `Φ(L) = max_τ Φ_Ph(τ; L)` (the envelope: `Φ_Ph(τ; L)` is concave in `τ` with maximum at `τ₀(L)`),
  hence `0 ≤ Φ(L) - Φ(L₀) - τ₀(L₀)(L - L₀) ≤ (τ₀(L) - τ₀(L₀))(L - L₀)`;
* `tau0_lipschitz_block`: `|τ₀(L) - τ₀(L')| ≤ Λ|L - L'|` (mean value theorem for `m` with `m'(t) ≥ t/(1+t²)`);
* `ct:outer`(3) (`|θ_ε'(t)| ≤ C_θ(1+|t|)^{-2}`, `hθ'`) and the mean value theorem for `θ_ε`.

**Proved**, unconditional (`C_θ` is an explicit hypothesis, discharged by `ct_outer_part3`).
-/

@[expose] public section

open Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- `∂_τ Φ_Ph(τ; L) = L - m(τ)` for `τ > 0`. -/
lemma hasDerivAt_edgePhi_pos (L : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (edgePhi L) (L - hankelEdgeM τ) τ := by
  have h := hasDerivAt_edgePhi L τ
  refine h.congr_deriv ?_
  unfold edgePhiDeriv hankelEdgeM
  simp only [hτ.ne', ↓reduceIte, abs_of_pos hτ]
  have hx0 : 0 < π * τ / 2 := by positivity
  have : Real.log (Real.tanh (π * τ / 2) / (π * τ / 2)) = -ceEll (π * τ / 2) := by
    unfold ceEll; rw [← Real.log_inv, inv_div]
  rw [this]; ring

/-- **Maximality of the saddle**: `Φ_Ph(τ; L) ≤ Φ_Ph(τ₀(L); L)` for `L > 0`, `τ ≥ 0`. -/
lemma edgePhi_le_tau0 {L : ℝ} (hL : 0 < L) {τ : ℝ} (hτ : 0 ≤ τ) : edgePhi L τ ≤ edgePhi L (tau0 L) := by
  have hτ0 := tau0_pos hL
  have hm : hankelEdgeM (tau0 L) = L := hankelEdgeM_tau0 hL
  rcases le_total τ (tau0 L) with h | h
  · have hmono : MonotoneOn (edgePhi L) (Icc 0 (tau0 L)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (tau0 L))
        (fun τ _ => (hasDerivAt_edgePhi L τ).continuousAt.continuousWithinAt)
        (fun τ _ => (hasDerivAt_edgePhi L τ).differentiableAt.differentiableWithinAt) fun τ hτ' => ?_
      rw [interior_Icc] at hτ'
      rw [(hasDerivAt_edgePhi_pos L hτ'.1).deriv]
      have := hankelEdgeM_strictMonoOn.monotoneOn (mem_Ici.2 hτ'.1.le) (mem_Ici.2 hτ0.le) hτ'.2.le
      linarith
    exact hmono ⟨hτ, h⟩ ⟨hτ0.le, le_rfl⟩ h
  · have hanti : AntitoneOn (edgePhi L) (Icc (tau0 L) τ) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc (tau0 L) τ)
        (fun τ _ => (hasDerivAt_edgePhi L τ).continuousAt.continuousWithinAt)
        (fun τ _ => (hasDerivAt_edgePhi L τ).differentiableAt.differentiableWithinAt) fun τ' hτ' => ?_
      rw [interior_Icc] at hτ'
      have hp : 0 < τ' := lt_trans hτ0 hτ'.1
      rw [(hasDerivAt_edgePhi_pos L hp).deriv]
      have := hankelEdgeM_strictMonoOn.monotoneOn (mem_Ici.2 hτ0.le) (mem_Ici.2 hp.le) hτ'.1.le
      linarith
    exact hanti ⟨le_rfl, h⟩ ⟨h, le_rfl⟩ h

/-- **Legendre sandwich** for `Φ(L) = Φ_Ph(τ₀(L); L)`:
`0 ≤ Φ(L) - Φ(L₀) - τ₀(L₀)(L - L₀) ≤ (τ₀(L) - τ₀(L₀))(L - L₀)` for `L, L₀ > 0`. -/
lemma phi_legendre {L L0 : ℝ} (hL : 0 < L) (hL0 : 0 < L0) :
    0 ≤ edgePhi L (tau0 L) - edgePhi L0 (tau0 L0) - tau0 L0 * (L - L0) ∧
    edgePhi L (tau0 L) - edgePhi L0 (tau0 L0) - tau0 L0 * (L - L0) ≤ (tau0 L - tau0 L0) * (L - L0) := by
  have hlin : ∀ a b τ : ℝ, edgePhi a τ = edgePhi b τ + (a - b) * τ := fun a b τ => by
    unfold edgePhi; ring
  have h1 : edgePhi L (tau0 L0) ≤ edgePhi L (tau0 L) := edgePhi_le_tau0 hL (tau0_pos hL0).le
  have h2 : edgePhi L0 (tau0 L) ≤ edgePhi L0 (tau0 L0) := edgePhi_le_tau0 hL0 (tau0_pos hL).le
  rw [hlin L L0 (tau0 L0)] at h1
  rw [hlin L0 L (tau0 L)] at h2
  constructor <;> nlinarith

/-- **`|Φ(L) - Φ(L₀) - τ₀(L₀)(L - L₀)| ≤ |τ₀(L) - τ₀(L₀)||L - L₀|`.** -/
lemma abs_phi_taylor_le {L L0 : ℝ} (hL : 0 < L) (hL0 : 0 < L0) :
    |edgePhi L (tau0 L) - edgePhi L0 (tau0 L0) - tau0 L0 * (L - L0)| ≤ |tau0 L - tau0 L0| * |L - L0| := by
  obtain ⟨h1, h2⟩ := phi_legendre hL hL0
  rw [abs_of_nonneg h1, ← abs_mul]
  exact h2.trans (le_abs_self _)

/-- **Lipschitz bound of `τ₀` on a block** (mean value theorem for `m = hankelEdgeM`, `m'(t) ≥ t/(1+t²)`): if
`τ₀(L), τ₀(L') ∈ [r/3, 3r]` then `|τ₀(L) - τ₀(L')| ≤ 27 (1 + r²)/r · |L - L'|`. -/
lemma tau0_lipschitz_block {r L L' : ℝ} (hr : 0 < r) (hL : 0 < L) (hL' : 0 < L')
    (h1 : r / 3 ≤ tau0 L) (h2 : tau0 L ≤ 3 * r) (h3 : r / 3 ≤ tau0 L') (h4 : tau0 L' ≤ 3 * r) :
    |tau0 L - tau0 L'| ≤ 27 * (1 + r ^ 2) / r * |L - L'| := by
  have core : ∀ {a b : ℝ}, a < b → r / 3 ≤ a → b ≤ 3 * r → hankelEdgeM b - hankelEdgeM a ≥
      r / (27 * (1 + r ^ 2)) * (b - a) := by
    intro a b hab ha hb
    have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
    obtain ⟨ξ, hξ, hξd⟩ := exists_hasDerivAt_eq_slope hankelEdgeM hankelEdgeM' hab
      (hankelEdgeM_continuousOn.mono (fun x hx => le_trans ha0.le hx.1))
      (fun x hx => hankelEdgeM_hasDerivAt (lt_trans ha0 hx.1))
    have hξ0 : 0 < ξ := lt_trans ha0 hξ.1
    have hq := hankelEdgeM'_ge_simple hξ0
    have hq2 : r / (27 * (1 + r ^ 2)) ≤ ξ / (1 + ξ ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hξ1 : r / 3 ≤ ξ := ha.trans hξ.1.le
      have hξ2 : ξ ≤ 3 * r := hξ.2.le.trans hb
      nlinarith [mul_nonneg hr.le (sq_nonneg (ξ - r / 3)), mul_nonneg hξ0.le (sq_nonneg r), mul_pos hr hξ0,
        mul_nonneg (sub_nonneg.2 hξ1) (sq_nonneg r), mul_nonneg hr.le (sub_nonneg.2 hξ2),
        mul_nonneg (mul_nonneg hr.le hr.le) (sub_nonneg.2 hξ1), sq_nonneg ξ, mul_nonneg hr.le (sq_nonneg ξ)]
    have hdiff : hankelEdgeM b - hankelEdgeM a = hankelEdgeM' ξ * (b - a) := by
      rw [hξd]; field_simp
    rw [hdiff]
    exact mul_le_mul_of_nonneg_right (hq2.trans hq) (by linarith)
  have hmL : hankelEdgeM (tau0 L) = L := hankelEdgeM_tau0 hL
  have hmL' : hankelEdgeM (tau0 L') = L' := hankelEdgeM_tau0 hL'
  have hc : 0 < 27 * (1 + r ^ 2) / r := by positivity
  have hkey : ∀ {a b : ℝ}, a ≤ b → r / 3 ≤ a → b ≤ 3 * r → hankelEdgeM b - hankelEdgeM a ≥ 0 →
      b - a ≤ 27 * (1 + r ^ 2) / r * (hankelEdgeM b - hankelEdgeM a) := by
    intro a b hab ha hb _
    rcases eq_or_lt_of_le hab with h | h
    · rw [h]; simp
    · have := core h ha hb
      have e : 27 * (1 + r ^ 2) / r * (r / (27 * (1 + r ^ 2))) = 1 := by field_simp
      calc b - a = (27 * (1 + r ^ 2) / r * (r / (27 * (1 + r ^ 2)))) * (b - a) := by rw [e]; ring
        _ = 27 * (1 + r ^ 2) / r * (r / (27 * (1 + r ^ 2)) * (b - a)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this hc.le
  rcases le_total (tau0 L') (tau0 L) with h | h
  · have hm : hankelEdgeM (tau0 L') ≤ hankelEdgeM (tau0 L) :=
      hankelEdgeM_strictMonoOn.monotoneOn (mem_Ici.2 (tau0_pos hL').le) (mem_Ici.2 (tau0_pos hL).le) h
    rw [hmL, hmL'] at hm
    have := hkey h h3 h2 (by rw [hmL, hmL']; linarith)
    rw [hmL, hmL'] at this
    rw [abs_of_nonneg (by linarith : 0 ≤ tau0 L - tau0 L'), abs_of_nonneg (by linarith : 0 ≤ L - L')]
    exact this
  · have hm : hankelEdgeM (tau0 L) ≤ hankelEdgeM (tau0 L') :=
      hankelEdgeM_strictMonoOn.monotoneOn (mem_Ici.2 (tau0_pos hL).le) (mem_Ici.2 (tau0_pos hL').le) h
    rw [hmL, hmL'] at hm
    have := hkey h h1 h4 (by rw [hmL, hmL']; linarith)
    rw [hmL, hmL'] at this
    rw [abs_of_nonpos (by linarith : tau0 L - tau0 L' ≤ 0), abs_of_nonpos (by linarith : L - L' ≤ 0)]
    linarith

/-- **The frozen phase on a block** (`ct:boas` Step 5): if `τ₀(L), τ₀(L₀) ∈ [r/3, 3r]` (`L, L₀ > 0`) and
`|θ_ε'(t)| ≤ C_θ(1+|t|)^{-2}` (`ct:outer`(3), `hθ'`), then with `Λ = 27(1+r²)/r`,
`|X(L₀) + ν(L₀)(L - L₀) - X(L)| ≤ Λ C_θ/(1+r/3)² · |L - L₀| + cΛ (L - L₀)²`, `X = boasX c ε`, `ν = boasNu c`. -/
theorem boas_phase_block {c ε Cθ r L L0 : ℝ} (hc : 0 ≤ c) (hCθ0 : 0 ≤ Cθ) (hr : 0 < r)
    (hθ' : ∀ t : ℝ, |deriv (CtOuter.outerTheta ε) t| ≤ Cθ / (1 + |t|) ^ 2)
    (hL : 0 < L) (hL0 : 0 < L0)
    (h1 : r / 3 ≤ tau0 L) (h2 : tau0 L ≤ 3 * r) (h3 : r / 3 ≤ tau0 L0) (h4 : tau0 L0 ≤ 3 * r) :
    |boasX c ε L0 + boasNu c L0 * (L - L0) - boasX c ε L| ≤
      (27 * (1 + r ^ 2) / r * (Cθ / (1 + r / 3) ^ 2)) * |L - L0| +
        (c * (27 * (1 + r ^ 2) / r)) * (L - L0) ^ 2 := by
  set Λ : ℝ := 27 * (1 + r ^ 2) / r with hΛ
  have hΛ0 : 0 < Λ := by positivity
  have hlip := tau0_lipschitz_block hr hL hL0 h1 h2 h3 h4
  have hΔ : |tau0 L - tau0 L0| ≤ Λ * |L - L0| := hlip
  -- the `θ` increment
  set Cm : ℝ := Cθ / (1 + r / 3) ^ 2 with hCm
  have hθd : Differentiable ℝ (CtOuter.outerTheta ε) :=
    (CtOuter.contDiff_outerTheta ε).differentiable (by simp)
  have hθb : ∀ t ∈ Icc (r / 3) (3 * r), ‖deriv (CtOuter.outerTheta ε) t‖ ≤ Cm := by
    intro t ht
    rw [Real.norm_eq_abs]
    refine (hθ' t).trans ?_
    rw [hCm]
    apply div_le_div_of_nonneg_left hCθ0 (by positivity)
    have : r / 3 ≤ |t| := by rw [abs_of_nonneg (by linarith [ht.1, show 0 < r / 3 by positivity])]; exact ht.1
    nlinarith [show 0 < r / 3 by positivity]
  have hθinc := Convex.norm_image_sub_le_of_norm_deriv_le (fun t _ => hθd t) hθb (convex_Icc (r / 3) (3 * r))
    (show tau0 L0 ∈ Icc (r / 3) (3 * r) from ⟨h3, h4⟩) (show tau0 L ∈ Icc (r / 3) (3 * r) from ⟨h1, h2⟩)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hθinc
  have hCm0 : 0 ≤ Cm := by positivity
  -- the `Φ` increment
  have hφ := abs_phi_taylor_le hL hL0
  have hid : boasX c ε L0 + boasNu c L0 * (L - L0) - boasX c ε L =
      -(c * (edgePhi L (tau0 L) - edgePhi L0 (tau0 L0) - tau0 L0 * (L - L0))) +
        (CtOuter.outerTheta ε (tau0 L) - CtOuter.outerTheta ε (tau0 L0)) := by
    unfold boasX boasNu; ring
  rw [hid]
  have hA : |c * (edgePhi L (tau0 L) - edgePhi L0 (tau0 L0) - tau0 L0 * (L - L0))| ≤
      c * Λ * (L - L0) ^ 2 := by
    rw [abs_mul, abs_of_nonneg hc]
    have : |tau0 L - tau0 L0| * |L - L0| ≤ Λ * |L - L0| * |L - L0| :=
      mul_le_mul_of_nonneg_right hΔ (abs_nonneg _)
    calc c * |edgePhi L (tau0 L) - edgePhi L0 (tau0 L0) - tau0 L0 * (L - L0)|
        ≤ c * (|tau0 L - tau0 L0| * |L - L0|) := mul_le_mul_of_nonneg_left hφ hc
      _ ≤ c * (Λ * |L - L0| * |L - L0|) := mul_le_mul_of_nonneg_left this hc
      _ = c * Λ * (L - L0) ^ 2 := by rw [mul_assoc, ← sq_abs (L - L0)]; ring
  have hB : |CtOuter.outerTheta ε (tau0 L) - CtOuter.outerTheta ε (tau0 L0)| ≤ Λ * Cm * |L - L0| := by
    have : |tau0 L - tau0 L0| ≤ Λ * |L - L0| := hΔ
    calc |CtOuter.outerTheta ε (tau0 L) - CtOuter.outerTheta ε (tau0 L0)| ≤ Cm * |tau0 L - tau0 L0| := hθinc
      _ ≤ Cm * (Λ * |L - L0|) := mul_le_mul_of_nonneg_left this hCm0
      _ = Λ * Cm * |L - L0| := by ring
  calc |-(c * (edgePhi L (tau0 L) - edgePhi L0 (tau0 L0) - tau0 L0 * (L - L0))) +
        (CtOuter.outerTheta ε (tau0 L) - CtOuter.outerTheta ε (tau0 L0))|
      ≤ |-(c * (edgePhi L (tau0 L) - edgePhi L0 (tau0 L0) - tau0 L0 * (L - L0)))| +
        |CtOuter.outerTheta ε (tau0 L) - CtOuter.outerTheta ε (tau0 L0)| := abs_add_le _ _
    _ ≤ _ := by rw [abs_neg]; linarith

/-- info: 'FormalResearch.SignUncertainty.boas_phase_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boas_phase_block

end FormalResearch.SignUncertainty
