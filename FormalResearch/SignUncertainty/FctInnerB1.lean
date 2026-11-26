/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctInnerCoord

/-!
# `fct:inner-symbols` (b1): the size and derivative bounds of the coordinate map

Paper I (`constant_terms_five.tex`), Lemma `fct:inner-symbols` (b1) and its proof, in the abstract setting of `FctInnerCoord` (a perturbed phase
`Φ̃` with `FctPhaseBox`).  Notation: `c ≥ 1`, `κ_c = 2^{-2/3} c^{2/3}`, `τ₁ = c^{-1/4}`, `û = -κ_c ã`, `A = ã/τ₁²`, `T̃(s) = s V(s²/τ₁²)`.

* `FctPhaseBox.tau0_eq_of_chart`, `FctPhaseBox.tau0_div_sqrt_atil`: the identity `∂_{L₁} ã = τ̃₀/√ã = V(A)`: `T̃(√ã)` is a critical point of `Φ̃`, because
  `Φ̃(T̃(s)) ≡ ã s - s³/3` and `T̃' ≠ 0`; by uniqueness `T̃(√ã) = τ̃₀`.
* `fctAtil_size`: `|û - a₁| ≤ c^{-7/6}` (admissible), `c ≥ 100`, gives `3 c^{-2/3} ≤ ã ≤ 4 c^{-2/3}` (`ã ≍ c^{-2/3}`).
* `fct_uL_bound`: from `|V - τ_*| ≤ C c^{-1/2}`, `|û_L + 2^{-2/3} τ_* c^{2/3}| ≤ C c^{1/6}` (the second claim of (b1) for `û_L`).
* `fct_uAlpha_bound`: from `|∂_αΦ̃(τ) | ≤ C_ϑ c^{-1} τ₁^{-9} τ^{11}`, `τ̃₀ ≤ C c^{-1/3}` and `ã ≥ c₁ c^{-2/3}`: `|û_α| ≤ C' c^{-17/12}`.

Class: proved from the stated hypotheses (the hypotheses `|V - τ_*| ≤ C c^{-1/2}` (`fct:comp-cfu`), `|∂_αΦ̃| ≤ C_ϑ ...` (`fct:th-inner`) are the paper's inputs and
are named as such in `FctInnerSymbols`).
-/
@[expose] public section

open Set Filter Topology Metric

namespace FormalResearch.SignUncertainty

namespace FctPhaseBox

variable {Φ : ℝ → ℝ × ℝ → ℝ} {Ω : Set (ℝ × ℝ)} {τ0 : ℝ × ℝ → ℝ}

/-- **`T̃(√ã)` is the critical point `τ̃₀`.**  If `T` is differentiable at `s₀ = √ã(p)` with `T'(s₀) ≠ 0`, `T(s₀) > 0`, and `Φ̃(T(s); p) = ã s - s³/3`
near `s₀` (the cubic normal form of `fct:comp-cfu`), then `T(s₀) = τ̃₀(p)`. -/
theorem tau0_eq_of_chart (h : FctPhaseBox Φ Ω τ0) {p : ℝ × ℝ} (hp : p ∈ Ω) {T : ℝ → ℝ} {T' : ℝ}
    (hT : HasDerivAt T T' (√(fctAtil Φ τ0 p))) (hT' : T' ≠ 0) (hpos : 0 < T (√(fctAtil Φ τ0 p)))
    (hnf : ∀ᶠ s in 𝓝 (√(fctAtil Φ τ0 p)), Φ (T s) p = fctAtil Φ τ0 p * s - s ^ 3 / 3) :
    T (√(fctAtil Φ τ0 p)) = τ0 p := by
  set s₀ := √(fctAtil Φ τ0 p) with hs₀
  have hs₀sq : s₀ ^ 2 = fctAtil Φ τ0 p := Real.sq_sqrt (h.atil_pos hp).le
  have hph : HasFDerivAt (fctPh Φ) (fderiv ℝ (fctPh Φ) (T s₀, p)) (T s₀, p) :=
    ((h.contDiffAt_ph hpos hp).differentiableAt (by simp)).hasFDerivAt
  have hcurve : HasDerivAt (fun s : ℝ => (T s, p)) (T', (0 : ℝ × ℝ)) s₀ := hT.prodMk (hasDerivAt_const s₀ p)
  have h1 := hph.comp_hasDerivAt s₀ hcurve
  have h2 : HasDerivAt (fun s : ℝ => fctAtil Φ τ0 p * s - s ^ 3 / 3) (fctAtil Φ τ0 p - s₀ ^ 2) s₀ := by
    have e1 : HasDerivAt (fun s : ℝ => fctAtil Φ τ0 p * s) (fctAtil Φ τ0 p) s₀ := by
      simpa using (hasDerivAt_id s₀).const_mul (fctAtil Φ τ0 p)
    have e2 : HasDerivAt (fun s : ℝ => s ^ 3 / 3) (s₀ ^ 2) s₀ := by
      have := (hasDerivAt_pow 3 s₀).div_const 3
      convert this using 1
      norm_num
    exact e1.sub e2
  have h3 : HasDerivAt (fun s : ℝ => fctPh Φ (T s, p)) (fctAtil Φ τ0 p - s₀ ^ 2) s₀ :=
    h2.congr_of_eventuallyEq (hnf.mono fun s hs => hs)
  have h4 := h1.unique h3
  have h5 : fderiv ℝ (fctPh Φ) (T s₀, p) (T', (0 : ℝ × ℝ)) = T' * fctPhTau Φ (T s₀) p := by
    have := fderiv_decomp (fderiv ℝ (fctPh Φ) (T s₀, p)) T' (0 : ℝ × ℝ)
    simp only [Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero] at this
    rw [fctPhTau]
    simpa using this
  have h6 : T' * fctPhTau Φ (T s₀) p = 0 := by
    rw [← h5, h4, hs₀sq]; ring
  have h7 : fctPhTau Φ (T s₀) p = 0 := (mul_eq_zero.1 h6).resolve_left hT'
  exact h.unique p hp _ hpos h7

/-- **`∂_{L₁} ã = τ̃₀/√ã = V(A)`** (`fct:inner-symbols` (b1)): with `T̃(s) = s V(s²/τ₁²)` and `A = ã/τ₁²`. -/
theorem tau0_div_sqrt_atil (h : FctPhaseBox Φ Ω τ0) {p : ℝ × ℝ} (hp : p ∈ Ω) {V : ℝ → ℝ} {τ₁ V' : ℝ} (hτ₁ : 0 < τ₁)
    (hVd : HasDerivAt V V' (fctAtil Φ τ0 p / τ₁ ^ 2)) (hVpos : 0 < V (fctAtil Φ τ0 p / τ₁ ^ 2))
    (hVne : V (fctAtil Φ τ0 p / τ₁ ^ 2) + 2 * (fctAtil Φ τ0 p / τ₁ ^ 2) * V' ≠ 0)
    (hnf : ∀ᶠ s in 𝓝 (√(fctAtil Φ τ0 p)),
      Φ (s * V (s ^ 2 / τ₁ ^ 2)) p = fctAtil Φ τ0 p * s - s ^ 3 / 3) :
    τ0 p / √(fctAtil Φ τ0 p) = V (fctAtil Φ τ0 p / τ₁ ^ 2) := by
  set s₀ := √(fctAtil Φ τ0 p) with hs₀
  have hs₀pos : 0 < s₀ := h.sqrt_atil_pos hp
  have hs₀sq : s₀ ^ 2 = fctAtil Φ τ0 p := Real.sq_sqrt (h.atil_pos hp).le
  set A := fctAtil Φ τ0 p / τ₁ ^ 2 with hA
  have hY : HasDerivAt (fun s : ℝ => s ^ 2 / τ₁ ^ 2) (2 * s₀ / τ₁ ^ 2) s₀ := by
    have := ((hasDerivAt_pow 2 s₀).div_const (τ₁ ^ 2))
    simpa using this
  have hYA : s₀ ^ 2 / τ₁ ^ 2 = A := by rw [hA, hs₀sq]
  have hVd' : HasDerivAt V V' (s₀ ^ 2 / τ₁ ^ 2) := by rw [hYA]; exact hVd
  have hTd : HasDerivAt (fun s : ℝ => s * V (s ^ 2 / τ₁ ^ 2)) (1 * V (s₀ ^ 2 / τ₁ ^ 2) + s₀ * (V' * (2 * s₀ / τ₁ ^ 2))) s₀ :=
    (hasDerivAt_id s₀).mul (hVd'.comp s₀ hY)
  have hT'ne : 1 * V (s₀ ^ 2 / τ₁ ^ 2) + s₀ * (V' * (2 * s₀ / τ₁ ^ 2)) ≠ 0 := by
    rw [hYA]
    intro hz
    apply hVne
    have : s₀ * (V' * (2 * s₀ / τ₁ ^ 2)) = 2 * A * V' := by
      rw [← hYA]; field_simp
    linarith
  have hpos : 0 < s₀ * V (s₀ ^ 2 / τ₁ ^ 2) := by rw [hYA]; exact mul_pos hs₀pos hVpos
  have key := h.tau0_eq_of_chart hp (T := fun s => s * V (s ^ 2 / τ₁ ^ 2)) hTd hT'ne hpos hnf
  have hτ : τ0 p = s₀ * V A := by rw [← hYA]; exact key.symm
  rw [hτ]
  field_simp

end FctPhaseBox


/-! ### The size and derivative bounds of (b1) -/

/-- `κ_c = 2^{-2/3} c^{2/3}`, so that `û = -κ_c ã` (`û = -2^{-2/3} c^{2/3} ã`, `fct:inner-symbols` (b)). -/
noncomputable def fctKappa (c : ℝ) : ℝ := (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ)

lemma fctKappa_pos {c : ℝ} (hc : 0 < c) : 0 < fctKappa c :=
  mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos hc _)

lemma two_rpow_23_bounds : (1.58 : ℝ) ≤ (2 : ℝ) ^ (2 / 3 : ℝ) ∧ (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 1.6 := by
  have h3 : ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hp : 0 < (2 : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  constructor
  · by_contra hc
    push Not at hc
    have : ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 < 1.58 ^ 3 := pow_lt_pow_left₀ hc hp.le (by norm_num)
    rw [h3] at this; norm_num at this
  · by_contra hc
    push Not at hc
    have : (1.6 : ℝ) ^ 3 < ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 := pow_lt_pow_left₀ hc (by norm_num) (by norm_num)
    rw [h3] at this; norm_num at this

/-- **`ã ≍ c^{-2/3}` on the admissible box** (`fct:inner-symbols` (b1)): `û = -κ_c ã`, `|û - a₁| ≤ c^{-7/6}`, `a₁ ∈ (-2.35, -2.33)` and `c ≥ 100` give
`3 c^{-2/3} ≤ ã ≤ 4 c^{-2/3}`. -/
theorem fctAtil_size {c û ã a₁ : ℝ} (hc : 100 ≤ c) (hu : û = -fctKappa c * ã) (hadm : |û - a₁| ≤ c ^ (-(7 / 6 : ℝ)))
    (ha₁ : -2.35 < a₁ ∧ a₁ < -2.33) (hã : 0 < ã) :
    3 * c ^ (-(2 / 3 : ℝ)) ≤ ã ∧ ã ≤ 4 * c ^ (-(2 / 3 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  have h1 : c ^ (-(7 / 6 : ℝ)) ≤ c ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have h2 : c ^ (-(1 : ℝ)) ≤ 0.01 := by
    rw [Real.rpow_neg_one]
    have : (1 : ℝ) / 100 ≥ c⁻¹ := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hc
    linarith
  have hab := abs_le.1 (hadm.trans (h1.trans h2))
  obtain ⟨hr1, hr2⟩ := two_rpow_23_bounds
  set q : ℝ := c ^ (2 / 3 : ℝ) with hq
  set r : ℝ := (2 : ℝ) ^ (2 / 3 : ℝ) with hr
  have hqpos : 0 < q := Real.rpow_pos_of_pos hc0 _
  have hcq : c ^ (-(2 / 3 : ℝ)) = q⁻¹ := Real.rpow_neg hc0.le _
  have hκ : fctKappa c = r⁻¹ * q := by
    unfold fctKappa; rw [Real.rpow_neg (by norm_num)]
  rw [hcq]
  have hmu : -û * r = ã * q := by
    rw [hu, hκ]; field_simp
  have hu1 : 2.32 ≤ -û := by linarith [hab.1, hab.2]
  have hu2 : -û ≤ 2.36 := by linarith [hab.1, hab.2]
  have hãq : ã = -û * r * q⁻¹ := by
    rw [← div_eq_mul_inv, eq_div_iff hqpos.ne']; linarith
  rw [hãq]
  exact ⟨mul_le_mul_of_nonneg_right (by nlinarith) (inv_nonneg.2 hqpos.le),
    mul_le_mul_of_nonneg_right (by nlinarith) (inv_nonneg.2 hqpos.le)⟩

/-- **`û_L` (`fct:inner-symbols` (b1))**: `û_L = -κ_c V(A)`; if `|V(A) - τ_*| ≤ C c^{-1/2}` then `|û_L + 2^{-2/3} τ_* c^{2/3}| ≤ C c^{1/6}`. -/
theorem fct_uL_close {c v τs C : ℝ} (hc : 0 < c) (hv : |v - τs| ≤ C * c ^ (-(1 / 2 : ℝ))) :
    |-fctKappa c * v + (2 : ℝ) ^ (-(2 / 3 : ℝ)) * τs * c ^ (2 / 3 : ℝ)| ≤ C * c ^ (1 / 6 : ℝ) := by
  have hC : 0 ≤ C := by
    have h0 : 0 ≤ C * c ^ (-(1 / 2 : ℝ)) := (abs_nonneg _).trans hv
    exact nonneg_of_mul_nonneg_left h0 (Real.rpow_pos_of_pos hc _)
  have e : -fctKappa c * v + (2 : ℝ) ^ (-(2 / 3 : ℝ)) * τs * c ^ (2 / 3 : ℝ) = -(fctKappa c * (v - τs)) := by
    unfold fctKappa; ring
  rw [e, abs_neg, abs_mul, abs_of_pos (fctKappa_pos hc)]
  have h2 : (2 : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq : c ^ (2 / 3 : ℝ) * c ^ (-(1 / 2 : ℝ)) = c ^ (1 / 6 : ℝ) := by
    rw [← Real.rpow_add hc]; norm_num
  calc fctKappa c * |v - τs| ≤ ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ)) * (C * c ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hv (fctKappa_pos hc).le
    _ = (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (C * (c ^ (2 / 3 : ℝ) * c ^ (-(1 / 2 : ℝ)))) := by ring
    _ = (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (C * c ^ (1 / 6 : ℝ)) := by rw [hq]
    _ ≤ 1 * (C * c ^ (1 / 6 : ℝ)) :=
        mul_le_mul_of_nonneg_right h2 (mul_nonneg hC (Real.rpow_pos_of_pos hc _).le)
    _ = C * c ^ (1 / 6 : ℝ) := one_mul _


/-- **`û_α = O(c^{-17/12})`** (`fct:inner-symbols` (b1)): `û_α = -κ_c g/√ã` with `g = ∂_αΦ̃(τ̃₀)`.  If `ã ≥ c₁ c^{-2/3}`, `0 < τ̃₀ ≤ C_τ c^{-1/3}` and
`|g| ≤ C_ϑ c^{-1} τ₁^{-9} τ̃₀^{11}` (`τ₁^{-9} = c^{9/4}`; `∂_αΦ̃ = c^{-1} ϑ^{(1)}` and `|ϑ^{(1)}(t)| ≤ C τ₁^{-9} t^{11}`, `fct:th-inner`), then
`|û_α| ≤ (C_ϑ C_τ^{11}/√c₁) c^{-17/12}`. -/
theorem fct_uAlpha_bound {c ã τ g c₁ Cθ Cτ : ℝ} (hc : 0 < c) (hc₁ : 0 < c₁) (hCθ : 0 ≤ Cθ) (hCτ : 0 ≤ Cτ)
    (hã : c₁ * c ^ (-(2 / 3 : ℝ)) ≤ ã) (hτ0 : 0 < τ) (hτ : τ ≤ Cτ * c ^ (-(1 / 3 : ℝ)))
    (hg : |g| ≤ Cθ * c ^ (-(1 : ℝ)) * c ^ (9 / 4 : ℝ) * τ ^ 11) :
    |-fctKappa c * (g / √ã)| ≤ Cθ * Cτ ^ 11 / √c₁ * c ^ (-(17 / 12 : ℝ)) := by
  have hcpos : ∀ x : ℝ, 0 < c ^ x := fun x => Real.rpow_pos_of_pos hc x
  have hsq : √c₁ * c ^ (-(1 / 3 : ℝ)) ≤ √ã := by
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow, Real.sq_sqrt hc₁.le, ← Real.rpow_natCast, ← Real.rpow_mul hc.le]
    norm_num
    exact hã
  have hsqpos : 0 < √c₁ * c ^ (-(1 / 3 : ℝ)) := mul_pos (Real.sqrt_pos.2 hc₁) (hcpos _)
  have hκ : fctKappa c ≤ c ^ (2 / 3 : ℝ) := by
    unfold fctKappa
    have : (2 : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    nlinarith [hcpos (2 / 3 : ℝ)]
  have hτ11 : τ ^ 11 ≤ Cτ ^ 11 * c ^ (-(11 / 3 : ℝ)) := by
    calc τ ^ 11 ≤ (Cτ * c ^ (-(1 / 3 : ℝ))) ^ 11 := pow_le_pow_left₀ hτ0.le hτ 11
      _ = Cτ ^ 11 * c ^ (-(11 / 3 : ℝ)) := by
        have : (c ^ (-(1 / 3 : ℝ))) ^ 11 = c ^ (-(11 / 3 : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num
        rw [mul_pow, this]
  have hgb : |g| ≤ Cθ * Cτ ^ 11 * c ^ (-(29 / 12 : ℝ)) := by
    calc |g| ≤ Cθ * c ^ (-(1 : ℝ)) * c ^ (9 / 4 : ℝ) * τ ^ 11 := hg
      _ ≤ Cθ * c ^ (-(1 : ℝ)) * c ^ (9 / 4 : ℝ) * (Cτ ^ 11 * c ^ (-(11 / 3 : ℝ))) :=
          mul_le_mul_of_nonneg_left hτ11 (mul_nonneg (mul_nonneg hCθ (hcpos _).le) (hcpos _).le)
      _ = Cθ * Cτ ^ 11 * (c ^ (-(1 : ℝ)) * c ^ (9 / 4 : ℝ) * c ^ (-(11 / 3 : ℝ))) := by ring
      _ = Cθ * Cτ ^ 11 * c ^ (-(29 / 12 : ℝ)) := by
        rw [← Real.rpow_add hc, ← Real.rpow_add hc]; norm_num
  rw [neg_mul, abs_neg, abs_mul, abs_of_pos (fctKappa_pos hc), abs_div, abs_of_pos (lt_of_lt_of_le hsqpos hsq)]
  have hCτ11 : 0 ≤ Cτ ^ 11 := pow_nonneg hCτ 11
  calc fctKappa c * (|g| / √ã) ≤ c ^ (2 / 3 : ℝ) * ((Cθ * Cτ ^ 11 * c ^ (-(29 / 12 : ℝ))) / (√c₁ * c ^ (-(1 / 3 : ℝ)))) := by
        apply mul_le_mul hκ _ (by positivity) (hcpos _).le
        exact div_le_div₀ (by positivity) hgb hsqpos hsq
    _ = Cθ * Cτ ^ 11 / √c₁ * (c ^ (2 / 3 : ℝ) * c ^ (-(29 / 12 : ℝ)) / c ^ (-(1 / 3 : ℝ))) := by
        field_simp
    _ = Cθ * Cτ ^ 11 / √c₁ * c ^ (-(17 / 12 : ℝ)) := by
        congr 1
        rw [← Real.rpow_add hc, ← Real.rpow_sub hc]; norm_num


namespace FctPhaseBox

variable {Φ : ℝ → ℝ × ℝ → ℝ} {Ω : Set (ℝ × ℝ)} {τ0 : ℝ × ℝ → ℝ}

/-- **`fct:inner-symbols` (b1), coordinate part** (abstract phase `Φ̃`).  Let `p = (L₁, α) ∈ Ω`, `c ≥ 100`, `κ_c = 2^{-2/3} c^{2/3}`, `û = -κ_c ã`
admissible (`|û - a₁| ≤ c^{-7/6}`, `a₁ ∈ (-2.35, -2.33)`), `τ₁ = c^{-1/4}`, and let `V` be the CFU function with `Φ̃(s V(s²/τ₁²)) = ã s - s³/3`
near `s = √ã` (`T̃' ≠ 0` there) with `|V(A) - τ_*| ≤ C_V c^{-1/2}`, `A = ã/τ₁²` (`fct:comp-cfu`), and `|∂_αΦ̃(τ̃₀)| ≤ C_ϑ c^{-1} τ₁^{-9} τ̃₀^{11}`
(`fct:th-inner`).  Then
* `3 c^{-2/3} ≤ ã ≤ 4 c^{-2/3}`;
* `∂_{L₁} ã = τ̃₀/√ã = V(A)` (as a derivative in `L` at fixed `α`, and `û_L = -κ_c V(A)`);
* `|û_L + 2^{-2/3} τ_* c^{2/3}| ≤ C_V c^{1/6}`;
* `|û_α| ≤ C_ϑ C_τ^{11}/√3 · c^{-17/12}` with `C_τ = 2(τ_* + C_V)`. -/
theorem fct_inner_b1 (h : FctPhaseBox Φ Ω τ0) {p : ℝ × ℝ} (hp : p ∈ Ω) {c a₁ τs CV Cθ : ℝ} (hc : 100 ≤ c)
    (ha₁ : -2.35 < a₁ ∧ a₁ < -2.33) (hadm : |-fctKappa c * fctAtil Φ τ0 p - a₁| ≤ c ^ (-(7 / 6 : ℝ)))
    {V : ℝ → ℝ} {V' : ℝ}
    (hVd : HasDerivAt V V' (fctAtil Φ τ0 p / (c ^ (-(1 / 4 : ℝ))) ^ 2))
    (hVpos : 0 < V (fctAtil Φ τ0 p / (c ^ (-(1 / 4 : ℝ))) ^ 2))
    (hVne : V (fctAtil Φ τ0 p / (c ^ (-(1 / 4 : ℝ))) ^ 2) + 2 * (fctAtil Φ τ0 p / (c ^ (-(1 / 4 : ℝ))) ^ 2) * V' ≠ 0)
    (hnf : ∀ᶠ s in 𝓝 (√(fctAtil Φ τ0 p)),
      Φ (s * V (s ^ 2 / (c ^ (-(1 / 4 : ℝ))) ^ 2)) p = fctAtil Φ τ0 p * s - s ^ 3 / 3)
    (hτs : 0 ≤ τs) (hCθ : 0 ≤ Cθ)
    (hV : |V (fctAtil Φ τ0 p / (c ^ (-(1 / 4 : ℝ))) ^ 2) - τs| ≤ CV * c ^ (-(1 / 2 : ℝ)))
    (hg : |fctPhAlpha Φ (τ0 p) p| ≤ Cθ * c ^ (-(1 : ℝ)) * c ^ (9 / 4 : ℝ) * (τ0 p) ^ 11) :
    (3 * c ^ (-(2 / 3 : ℝ)) ≤ fctAtil Φ τ0 p ∧ fctAtil Φ τ0 p ≤ 4 * c ^ (-(2 / 3 : ℝ))) ∧
    τ0 p / √(fctAtil Φ τ0 p) = V (fctAtil Φ τ0 p / (c ^ (-(1 / 4 : ℝ))) ^ 2) ∧
    uL (fctKappa c) Φ τ0 p = -fctKappa c * V (fctAtil Φ τ0 p / (c ^ (-(1 / 4 : ℝ))) ^ 2) ∧
    |uL (fctKappa c) Φ τ0 p + (2 : ℝ) ^ (-(2 / 3 : ℝ)) * τs * c ^ (2 / 3 : ℝ)| ≤ CV * c ^ (1 / 6 : ℝ) ∧
    |uAlpha (fctKappa c) Φ τ0 p| ≤ Cθ * (2 * (τs + CV)) ^ 11 / √3 * c ^ (-(17 / 12 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  have hτ₁ : 0 < c ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hã := h.atil_pos hp
  have hsize := fctAtil_size hc (û := -fctKappa c * fctAtil Φ τ0 p) rfl hadm ha₁ hã
  have hid := h.tau0_div_sqrt_atil hp hτ₁ hVd hVpos hVne hnf
  have hCV : 0 ≤ CV := by
    have h0 : 0 ≤ CV * c ^ (-(1 / 2 : ℝ)) := (abs_nonneg _).trans hV
    exact nonneg_of_mul_nonneg_left h0 (Real.rpow_pos_of_pos hc0 _)
  have hUL : uL (fctKappa c) Φ τ0 p = -fctKappa c * V (fctAtil Φ τ0 p / (c ^ (-(1 / 4 : ℝ))) ^ 2) := by
    rw [uL, hid]
  refine ⟨hsize, hid, hUL, ?_, ?_⟩
  · rw [hUL]; exact fct_uL_close hc0 hV
  · -- `û_α`
    have hsq : √(fctAtil Φ τ0 p) ≤ 2 * c ^ (-(1 / 3 : ℝ)) := by
      apply Real.sqrt_le_iff.2
      refine ⟨by positivity, ?_⟩
      have : (2 * c ^ (-(1 / 3 : ℝ))) ^ 2 = 4 * c ^ (-(2 / 3 : ℝ)) := by
        have h2 : (c ^ (-(1 / 3 : ℝ))) ^ 2 = c ^ (-(2 / 3 : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
        rw [mul_pow, h2]; norm_num
      rw [this]; exact hsize.2
    have hVle : V (fctAtil Φ τ0 p / (c ^ (-(1 / 4 : ℝ))) ^ 2) ≤ τs + CV := by
      have h1 := (abs_le.1 hV).2
      have h2 : c ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
      nlinarith [Real.rpow_pos_of_pos hc0 (-(1 / 2 : ℝ))]
    have hτ0le : τ0 p ≤ 2 * (τs + CV) * c ^ (-(1 / 3 : ℝ)) := by
      have : τ0 p = √(fctAtil Φ τ0 p) * V (fctAtil Φ τ0 p / (c ^ (-(1 / 4 : ℝ))) ^ 2) := by
        rw [← hid]; field_simp
      rw [this]
      calc √(fctAtil Φ τ0 p) * V (fctAtil Φ τ0 p / (c ^ (-(1 / 4 : ℝ))) ^ 2)
          ≤ (2 * c ^ (-(1 / 3 : ℝ))) * (τs + CV) :=
            mul_le_mul hsq hVle hVpos.le (by positivity)
        _ = 2 * (τs + CV) * c ^ (-(1 / 3 : ℝ)) := by ring
    exact fct_uAlpha_bound hc0 (by norm_num : (0 : ℝ) < 3) hCθ (by positivity) hsize.1 (h.pos p hp) hτ0le hg

end FctPhaseBox

/-- info: 'FormalResearch.SignUncertainty.FctPhaseBox.fct_inner_b1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FctPhaseBox.fct_inner_b1

end FormalResearch.SignUncertainty
