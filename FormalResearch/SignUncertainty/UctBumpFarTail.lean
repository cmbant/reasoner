module

public import FormalResearch.SignUncertainty.UctBumpFarTailLap
public import FormalResearch.SignUncertainty.UctE0Small
public import FormalResearch.SignUncertainty.UctBumpFarIbp
public import FormalResearch.SignUncertainty.UctBumpE0

/-!
# The smooth tail of the far band (F2a, `uct:bump-weighted`)

For `B_tail = bumpTail B` (a `BumpProfile 1 1 M α β (tailK K)`, `β ≥ 3/2`), `L > 0`, `c ≥ 64`:
`‖∫ E₀(τ) e^{icLτ} B̂_tail(icτ) dτ‖ ≤ C M c⁻² L⁻²` (`bump_tail_bound`), `C` depending only on `K`.

Route (the paper's, with the damped transforms `Φ_m^η(τ) = ∫ e^{-(icτ+η)x} x^m B_tail`, `η > 0`, in place of the conditionally convergent ones): for `η > 0`,
`(E₀ Φ_0^η)'' = E₀''Φ_0 + 2E₀'Φ_0' + E₀Φ_0''` with `Φ_m' = -ic Φ_{m+1}`.  By `tailPhi_pt` (`|Φ_m| ≲ M u^{-(m-1/2)}`, `u = c|τ|`, near `u ≤ 1`, and `≲ M u^{-N}` always) and `E0_small_bounds`
(`|E₀| ≲ (u/c)X^q`, `|E₀'| ≲ X^q`, `|E₀''| ≲ c X^q`, `X = 1+u`), `|(E₀Φ_0^η)''| ≤ K M c u^{-1/2}(1+u)^{-3}`, uniformly in `η`; its `L¹` norm is `O(M)`
(`c dτ = du`).  Two integrations by parts in `τ` (`fourier_twice`) give `O(M c⁻² L⁻²)` and `η ↓ 0` is dominated convergence.

Class: proved, no hypotheses.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open FormalResearch.Asymptotics
open scoped Real

namespace FormalResearch.SignUncertainty

/-- Abstract form of the pointwise estimate: with `N = q + 6`. -/
lemma tail_Q_bound {q N : ℕ} (hN : N = q + 6) {M Z0 D0 D1 D2 A1 A2 u a0 a1 a2 : ℝ} (hM : 0 ≤ M) (hZ0 : 0 ≤ Z0)
    (hD0 : 0 ≤ D0) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hu : 0 < u) (ha0 : 0 ≤ a0)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (h0 : a0 ≤ M * Z0) (h0' : a0 ≤ M * D0 * (u⁻¹) ^ N)
    (h1 : a1 ≤ M * D1 * (u⁻¹) ^ N) (h1' : u ≤ 1 → a1 ≤ M * A1 * (u⁻¹) ^ ((1 : ℝ) - 1 / 2))
    (h2 : a2 ≤ M * D2 * (u⁻¹) ^ N) (h2' : u ≤ 1 → a2 ≤ M * A2 * (u⁻¹) ^ (((2 : ℕ) : ℝ) - 1 / 2)) :
    (1 + u) ^ (q + 1) * (a0 + 2 * a1 + u * a2) ≤
      (8 * 2 ^ (q + 1) * (Z0 + 2 * A1 + A2 + D0 + 2 * D1 + D2)) * M * ((u⁻¹) ^ ((1 : ℝ) / 2) * ((1 + u) ^ 3)⁻¹) := by
  set t : ℝ := u⁻¹ with ht
  have ht0 : 0 < t := inv_pos.mpr hu
  have hut : u * t = 1 := mul_inv_cancel₀ hu.ne'
  set K0 : ℝ := Z0 + 2 * A1 + A2 + D0 + 2 * D1 + D2 with hK0
  have hK00 : 0 ≤ K0 := by positivity
  have hsq : 0 ≤ t ^ ((1 : ℝ) / 2) := Real.rpow_nonneg ht0.le _
  have hinv3 : 0 ≤ ((1 + u) ^ 3)⁻¹ := by positivity
  by_cases hu1 : u ≤ 1
  · have ht1 : 1 ≤ t := (one_le_inv₀ hu).mpr hu1
    have hsq1 : 1 ≤ t ^ ((1 : ℝ) / 2) := Real.one_le_rpow ht1 (by norm_num)
    have e1 : t ^ ((1 : ℝ) - 1 / 2) = t ^ ((1 : ℝ) / 2) := by norm_num
    have e2 : u * t ^ (((2 : ℕ) : ℝ) - 1 / 2) = t ^ ((1 : ℝ) / 2) := by
      have : t ^ (((2 : ℕ) : ℝ) - 1 / 2) = t * t ^ ((1 : ℝ) / 2) := by
        rw [show (((2 : ℕ) : ℝ) - 1 / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add ht0, Real.rpow_one]
      rw [this, ← mul_assoc, hut, one_mul]
    have b1 := h1' hu1
    have b2 := h2' hu1
    rw [e1] at b1
    have hu2 : u * a2 ≤ u * (M * A2 * t ^ (((2 : ℕ) : ℝ) - 1 / 2)) := mul_le_mul_of_nonneg_left b2 hu.le
    have hu2' : u * (M * A2 * t ^ (((2 : ℕ) : ℝ) - 1 / 2)) = M * A2 * t ^ ((1 : ℝ) / 2) := by
      rw [← e2]; ring
    have hsum : a0 + 2 * a1 + u * a2 ≤ M * (Z0 + 2 * A1 + A2) * t ^ ((1 : ℝ) / 2) := by
      have h0t : a0 ≤ M * Z0 * t ^ ((1 : ℝ) / 2) := by
        calc a0 ≤ M * Z0 := h0
          _ = M * Z0 * 1 := (mul_one _).symm
          _ ≤ M * Z0 * t ^ ((1 : ℝ) / 2) := by gcongr
      nlinarith
    have hp : (1 + u) ^ (q + 1) ≤ 2 ^ (q + 1) := by
      gcongr
      linarith
    have h8 : (1 : ℝ) ≤ 8 * ((1 + u) ^ 3)⁻¹ := by
      have : (1 + u) ^ 3 ≤ 8 := by
        have h23 : (1 + u) ^ 3 ≤ 2 ^ 3 := by gcongr; linarith
        norm_num at h23 ⊢; linarith
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      linarith
    have hS0 : 0 ≤ M * (Z0 + 2 * A1 + A2) * t ^ ((1 : ℝ) / 2) := by positivity
    calc (1 + u) ^ (q + 1) * (a0 + 2 * a1 + u * a2) ≤ 2 ^ (q + 1) * (M * (Z0 + 2 * A1 + A2) * t ^ ((1 : ℝ) / 2)) := by
          gcongr
      _ ≤ 2 ^ (q + 1) * (M * (Z0 + 2 * A1 + A2) * t ^ ((1 : ℝ) / 2) * (8 * ((1 + u) ^ 3)⁻¹)) := by
          have := le_mul_of_one_le_right hS0 h8
          exact mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ _ := by
          have hZ : Z0 + 2 * A1 + A2 ≤ K0 := by rw [hK0]; linarith
          have : M * (Z0 + 2 * A1 + A2) ≤ M * K0 := by gcongr
          calc 2 ^ (q + 1) * (M * (Z0 + 2 * A1 + A2) * t ^ ((1 : ℝ) / 2) * (8 * ((1 + u) ^ 3)⁻¹))
              ≤ 2 ^ (q + 1) * (M * K0 * t ^ ((1 : ℝ) / 2) * (8 * ((1 + u) ^ 3)⁻¹)) := by gcongr
            _ = _ := by ring
  · have hu1' : 1 < u := not_le.mp hu1
    have ht1 : t ≤ 1 := inv_le_one_of_one_le₀ hu1'.le
    have hDsum : a0 + 2 * a1 + u * a2 ≤ M * (D0 + 2 * D1 + D2) * u * t ^ N := by
      have e : u * (M * D2 * t ^ N) = M * D2 * u * t ^ N := by ring
      have hu2 : u * a2 ≤ M * D2 * u * t ^ N := by rw [← e]; exact mul_le_mul_of_nonneg_left h2 hu.le
      have hu1'' : M * D0 * t ^ N ≤ M * D0 * u * t ^ N := by
        have : M * D0 * t ^ N * 1 ≤ M * D0 * t ^ N * u := by gcongr
        nlinarith
      have hu3 : M * D1 * t ^ N ≤ M * D1 * u * t ^ N := by
        have : M * D1 * t ^ N * 1 ≤ M * D1 * t ^ N * u := by gcongr
        nlinarith
      nlinarith
    have hp : (1 + u) ^ (q + 1) ≤ 2 ^ (q + 1) * u ^ (q + 1) := by
      rw [← mul_pow]
      gcongr
      linarith
    have hkey : u ^ (q + 1) * (u * t ^ N) = t ^ 4 := by
      rw [hN]
      have : u ^ (q + 1) * (u * t ^ (q + 6)) = (u * t) ^ (q + 2) * t ^ 4 := by ring
      rw [this, hut, one_pow, one_mul]
    have h8 : t ^ 3 ≤ 8 * ((1 + u) ^ 3)⁻¹ := by
      have h1u : 1 + u ≤ 2 * u := by linarith
      have : (1 + u) ^ 3 ≤ 8 * u ^ 3 := by
        calc (1 + u) ^ 3 ≤ (2 * u) ^ 3 := by gcongr
          _ = 8 * u ^ 3 := by ring
      have hi : (8 * u ^ 3)⁻¹ ≤ ((1 + u) ^ 3)⁻¹ := inv_anti₀ (by positivity) this
      calc t ^ 3 = 8 * (8 * u ^ 3)⁻¹ := by rw [ht, inv_pow]; field_simp
        _ ≤ 8 * ((1 + u) ^ 3)⁻¹ := by gcongr
    have h74 : t ^ 4 ≤ t ^ ((1 : ℝ) / 2) * t ^ 3 := by
      have : t ^ ((1 : ℝ) / 2) * t ^ 3 = t ^ ((7 : ℝ) / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add ht0]; norm_num
      rw [this, ← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by norm_num)
    have hK0n : 0 ≤ M * (D0 + 2 * D1 + D2) := by positivity
    calc (1 + u) ^ (q + 1) * (a0 + 2 * a1 + u * a2)
        ≤ (2 ^ (q + 1) * u ^ (q + 1)) * (M * (D0 + 2 * D1 + D2) * u * t ^ N) := by
          gcongr
      _ = 2 ^ (q + 1) * (M * (D0 + 2 * D1 + D2)) * (u ^ (q + 1) * (u * t ^ N)) := by ring
      _ = 2 ^ (q + 1) * (M * (D0 + 2 * D1 + D2)) * t ^ 4 := by rw [hkey]
      _ ≤ 2 ^ (q + 1) * (M * (D0 + 2 * D1 + D2)) * (t ^ ((1 : ℝ) / 2) * (8 * ((1 + u) ^ 3)⁻¹)) := by
          gcongr
          calc t ^ 4 ≤ t ^ ((1 : ℝ) / 2) * t ^ 3 := h74
            _ ≤ t ^ ((1 : ℝ) / 2) * (8 * ((1 + u) ^ 3)⁻¹) := by gcongr
      _ ≤ _ := by
          have hZ : D0 + 2 * D1 + D2 ≤ K0 := by rw [hK0]; linarith
          have : M * (D0 + 2 * D1 + D2) ≤ M * K0 := by gcongr
          calc 2 ^ (q + 1) * (M * (D0 + 2 * D1 + D2)) * (t ^ ((1 : ℝ) / 2) * (8 * ((1 + u) ^ 3)⁻¹))
              ≤ 2 ^ (q + 1) * (M * K0) * (t ^ ((1 : ℝ) / 2) * (8 * ((1 + u) ^ 3)⁻¹)) := by gcongr
            _ = _ := by ring

lemma integrable_comp_abs' {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) : Integrable (fun x : ℝ => f |x|) := by
  have h1 : IntegrableOn (fun x : ℝ => f |x|) (Ioi 0) :=
    hf.congr_fun (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
  have int_Iic : IntegrableOn (fun x : ℝ => f |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi h1
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact int_Iic.union h1

/-- `ψ(u) = u^{-1/2}(1+u)^{-3}` is integrable on `(0, ∞)`. -/
lemma integrableOn_psi : IntegrableOn (fun u : ℝ => (u⁻¹) ^ ((1 : ℝ) / 2) * ((1 + u) ^ 3)⁻¹) (Ioi 0) := by
  have hmeas : Measurable fun u : ℝ => (u⁻¹) ^ ((1 : ℝ) / 2) * ((1 + u) ^ 3)⁻¹ := by fun_prop
  have hs : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    ext x; simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro hx; by_cases h1 : x ≤ 1
      · exact Or.inl ⟨hx, h1⟩
      · exact Or.inr (not_le.mp h1)
    · rintro (⟨h, _⟩ | h) <;> linarith
  rw [hs]
  refine IntegrableOn.union ?_ ?_
  · have hi : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (Ioc 0 1) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := -(1 / 2 : ℝ)) (by norm_num))
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp this
    refine hi.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1
    have e : (x⁻¹) ^ ((1 : ℝ) / 2) = x ^ (-(1 / 2 : ℝ)) := by
      rw [Real.inv_rpow hx0.le, ← Real.rpow_neg hx0.le]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), e]
    have : ((1 + x) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    calc x ^ (-(1 / 2 : ℝ)) * ((1 + x) ^ 3)⁻¹ ≤ x ^ (-(1 / 2 : ℝ)) * 1 := by gcongr
      _ = _ := mul_one _
  · have hi : IntegrableOn (fun x : ℝ => x ^ (-(7 / 2 : ℝ))) (Ioi 1) := integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
    refine hi.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : (1 : ℝ) < x := hx
    have hx0 : 0 < x := by linarith
    have e : (x⁻¹) ^ ((1 : ℝ) / 2) = x ^ (-(1 / 2 : ℝ)) := by
      rw [Real.inv_rpow hx0.le, ← Real.rpow_neg hx0.le]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), e]
    have h3 : ((1 + x) ^ 3)⁻¹ ≤ (x ^ 3)⁻¹ := inv_anti₀ (by positivity) (by gcongr; linarith)
    have e3 : x ^ (-(7 / 2 : ℝ)) = x ^ (-(1 / 2 : ℝ)) * (x ^ 3)⁻¹ := by
      rw [show (-(7 / 2 : ℝ)) = -(1 / 2 : ℝ) + (-(3 : ℝ)) by norm_num, Real.rpow_add hx0]
      rw [Real.rpow_neg hx0.le (3 : ℝ), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e3]
    gcongr

lemma integrable_psi_abs : Integrable (fun y : ℝ => ((|y|)⁻¹) ^ ((1 : ℝ) / 2) * ((1 + |y|) ^ 3)⁻¹) :=
  integrable_comp_abs' (f := fun u : ℝ => (u⁻¹) ^ ((1 : ℝ) / 2) * ((1 + u) ^ 3)⁻¹) integrableOn_psi

/-- The three pointwise estimates for `E₀ Φ`, `(E₀ Φ)'`, `(E₀ Φ)''` in terms of `Q = (1+u)^{q+1}(a₀+2a₁+u a₂)`. -/
lemma tail_num {CE c u Y a0 a1 a2 e0 e1 e2 : ℝ} (hc : 1 ≤ c) (hu : 0 < u) (hY : 0 ≤ Y) (hCE : 0 ≤ CE)
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (h0 : e0 ≤ CE * (u / c) * Y) (h1 : e1 ≤ CE * Y) (h2 : e2 ≤ CE * c * Y) :
    e0 * a0 ≤ CE * c * ((1 + u) * Y * (a0 + 2 * a1 + u * a2)) ∧
    e1 * a0 + c * e0 * a1 ≤ CE * c * ((1 + u) * Y * (a0 + 2 * a1 + u * a2)) ∧
    e2 * a0 + 2 * c * e1 * a1 + c ^ 2 * e0 * a2 ≤ CE * c * ((1 + u) * Y * (a0 + 2 * a1 + u * a2)) := by
  have hc0 : 0 < c := by linarith
  have huc : u / c ≤ u := div_le_self hu.le hc
  have hcu : c * (u / c) = u := by field_simp
  set Q : ℝ := a0 + 2 * a1 + u * a2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hCY : 0 ≤ CE * Y := by positivity
  refine ⟨?_, ?_, ?_⟩
  · calc e0 * a0 ≤ CE * (u / c) * Y * a0 := by gcongr
      _ ≤ CE * Y * (u * a0) := by
          have : CE * (u / c) * Y * a0 = CE * Y * ((u / c) * a0) := by ring
          rw [this]; gcongr
      _ ≤ CE * c * ((1 + u) * Y * Q) := by
          have h1 : u * a0 ≤ (1 + u) * Q := by nlinarith [mul_nonneg hu.le ha1, mul_nonneg hu.le (mul_nonneg hu.le ha2)]
          have h2 : CE * Y * (u * a0) ≤ CE * Y * ((1 + u) * Q) := by gcongr
          have h3 : CE * Y * ((1 + u) * Q) ≤ c * (CE * Y * ((1 + u) * Q)) :=
            le_mul_of_one_le_left (by positivity) hc
          nlinarith
  · calc e1 * a0 + c * e0 * a1 ≤ CE * Y * a0 + c * (CE * (u / c) * Y) * a1 := by gcongr
      _ = CE * Y * (a0 + u * a1) := by
          have : c * (CE * (u / c) * Y) = CE * Y * u := by
            calc c * (CE * (u / c) * Y) = CE * Y * (c * (u / c)) := by ring
              _ = _ := by rw [hcu]
          rw [this]; ring
      _ ≤ CE * c * ((1 + u) * Y * Q) := by
          have h1 : a0 + u * a1 ≤ (1 + u) * Q := by nlinarith [mul_nonneg hu.le ha0, mul_nonneg hu.le ha1, mul_nonneg hu.le (mul_nonneg hu.le ha2)]
          have h2 : CE * Y * (a0 + u * a1) ≤ CE * Y * ((1 + u) * Q) := by gcongr
          have h3 : CE * Y * ((1 + u) * Q) ≤ c * (CE * Y * ((1 + u) * Q)) :=
            le_mul_of_one_le_left (by positivity) hc
          nlinarith
  · calc e2 * a0 + 2 * c * e1 * a1 + c ^ 2 * e0 * a2
        ≤ CE * c * Y * a0 + 2 * c * (CE * Y) * a1 + c ^ 2 * (CE * (u / c) * Y) * a2 := by gcongr
      _ = CE * c * Y * Q := by
          have : c ^ 2 * (CE * (u / c) * Y) = c * (CE * Y * u) := by
            calc c ^ 2 * (CE * (u / c) * Y) = c * CE * Y * (c * (u / c)) := by ring
              _ = _ := by rw [hcu]; ring
          rw [hQ]
          calc CE * c * Y * a0 + 2 * c * (CE * Y) * a1 + c ^ 2 * (CE * (u / c) * Y) * a2
              = CE * c * Y * a0 + 2 * c * (CE * Y) * a1 + (c ^ 2 * (CE * (u / c) * Y)) * a2 := by ring
            _ = _ := by rw [this]; ring
      _ ≤ CE * c * ((1 + u) * Y * Q) := by
          have : CE * c * Y * Q ≤ CE * c * Y * ((1 + u) * Q) := by
            gcongr
            nlinarith
          nlinarith [this]

theorem bump_tail_bound {α β : ℝ} (K : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ → ℝ) (M c L : ℝ), 0 ≤ M → 64 ≤ c → 0 < L → 3 / 2 ≤ β → BumpProfile 1 1 M α β K B →
      Integrable (fun τ : ℝ => bumpE0 c τ * Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) *
          bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I))) ∧
      ‖∫ τ : ℝ, bumpE0 c τ * Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) *
          bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I))‖ ≤ C * M * (c ^ 2)⁻¹ * (L ^ 2)⁻¹ := by
  obtain ⟨CE, q, hCE0, hE⟩ := E0_small_bounds
  set N : ℕ := q + 6 with hNdef
  set Z0 : ℝ := 2 * |K 0| with hZ0
  set D : ℕ → ℝ := fun m => mulPowK K m N with hDdef
  set A : ℕ → ℝ := fun m => tailA K m + D m with hAdef
  have hD0 : ∀ m, 0 ≤ D m := fun m => mulPowK_nonneg K m N
  have hA0 : ∀ m, 0 ≤ A m := fun m => add_nonneg (tailA_nonneg K m) (hD0 m)
  have hZ00 : 0 ≤ Z0 := by positivity
  set KQ : ℝ := 8 * 2 ^ (q + 1) * (Z0 + 2 * A 1 + A 2 + D 0 + 2 * D 1 + D 2) with hKQ
  have hKQ0 : 0 ≤ KQ := by
    have := hD0 0; have := hD0 1; have := hD0 2; have := hA0 1; have := hA0 2
    positivity
  set Ipsi : ℝ := ∫ y : ℝ, ((|y|)⁻¹) ^ ((1 : ℝ) / 2) * ((1 + |y|) ^ 3)⁻¹ with hIpsi
  have hIpsi0 : 0 ≤ Ipsi := integral_nonneg fun y => by positivity
  refine ⟨CE * KQ * Ipsi, by positivity, ?_⟩
  intro B M c L hM hc hL hβ hB
  have hc0 : 0 < c := by linarith
  obtain ⟨h, hh, hh8, hch⟩ : ∃ h : ℝ, 0 < h ∧ h ≤ 1 / 8 ∧ c = (h ^ 2)⁻¹ := by
    have hs0 : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
    have hs4 : 8 ≤ Real.sqrt c := by
      rw [show (8 : ℝ) = Real.sqrt 64 by rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hc
    refine ⟨(Real.sqrt c)⁻¹, inv_pos.mpr hs0, ?_, ?_⟩
    · rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hs4
    · rw [inv_pow, Real.sq_sqrt hc0.le, inv_inv]
  subst hch
  set c : ℝ := (h ^ 2)⁻¹ with hcdef
  have hc1 : 1 ≤ c := by linarith
  have hc2 : 2 ≤ c := by linarith
  obtain ⟨hEC2, hEb⟩ := hE h hh hh8
  set E : ℝ → ℂ := bumpE0 c with hEdef
  have hh1 : h ≤ 1 := by linarith
  -- regularity of `E`
  have hEc : Continuous E := hEC2.continuous
  have hE1c : Continuous (deriv E) := (cd1_of_cd2 hEC2).continuous
  have hE2c : Continuous (deriv (deriv E)) := (cd1_of_cd2 hEC2).continuous_deriv le_rfl
  have hEd : ∀ τ, HasDerivAt E (deriv E τ) τ := fun τ => (hEC2.differentiable (by norm_num) τ).hasDerivAt
  have hEd1 : ∀ τ, HasDerivAt (deriv E) (deriv (deriv E) τ) τ :=
    fun τ => ((cd1_of_cd2 hEC2).differentiable (by norm_num) τ).hasDerivAt
  -- the profile
  have hBc : Continuous B := hB.smooth.continuous
  have hz : ∀ x : ℝ, x < 0 → B x = 0 := fun x hx => hB.zero_le_one (by linarith)
  have hβ1 : 1 < β := by linarith
  set Φ : ℝ → ℕ → ℝ → ℂ := fun η m τ => bumpLapW B m (((c * τ : ℝ) : ℂ) * Complex.I + ((η : ℝ) : ℂ)) with hΦ
  have hΦd : ∀ η : ℝ, 0 < η → ∀ (m : ℕ) (τ : ℝ),
      HasDerivAt (Φ η m) (-((c : ℂ) * Complex.I) * Φ η (m + 1) τ) τ := fun η hη m τ =>
    hasDerivAt_bumpLapW_param hBc hz hη.le c τ (hB.integrable_pow_B_exp (by norm_num) (by norm_num) hβ1 m hη)
      (hB.integrable_pow_B_exp (by norm_num) (by norm_num) hβ1 (m + 1) hη)
  have hΦc : ∀ η : ℝ, 0 < η → ∀ m : ℕ, Continuous (Φ η m) := fun η hη m =>
    continuous_iff_continuousAt.mpr fun τ => (hΦd η hη m τ).continuousAt
  have hcontL : Continuous fun τ : ℝ => bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I)) :=
    (hB.continuousOn_laplace (by norm_num) (by norm_num) hβ1).comp_continuous (by fun_prop) (fun τ => by simp)
  -- majorant
  set ψ : ℝ → ℝ := fun y => ((|y|)⁻¹) ^ ((1 : ℝ) / 2) * ((1 + |y|) ^ 3)⁻¹ with hψ
  set G : ℝ → ℝ := fun τ => CE * c * (KQ * M * ψ (c * τ)) with hG
  have hGi : Integrable G := by
    have := (integrable_psi_abs.comp_mul_left' hc0.ne').const_mul (CE * c * (KQ * M))
    refine this.congr (ae_of_all _ fun τ => ?_)
    simp only [hG, hψ]; ring
  have hG0 : ∀ τ, 0 ≤ G τ := fun τ => by simp only [hG, hψ]; positivity
  have hne : ∀ᵐ τ : ℝ ∂volume, τ ≠ 0 := by
    have := (Set.countable_singleton (0 : ℝ)).ae_notMem (volume : Measure ℝ)
    filter_upwards [this] with τ hτ using hτ
  -- pointwise bounds
  have key : ∀ η : ℝ, 0 < η → ∀ τ : ℝ, τ ≠ 0 →
      ‖E τ * Φ η 0 τ‖ ≤ G τ ∧
      ‖deriv E τ * Φ η 0 τ + E τ * (-((c : ℂ) * Complex.I) * Φ η 1 τ)‖ ≤ G τ ∧
      ‖(deriv (deriv E) τ * Φ η 0 τ + deriv E τ * (-((c : ℂ) * Complex.I) * Φ η 1 τ)) +
        (deriv E τ * (-((c : ℂ) * Complex.I) * Φ η 1 τ) +
          E τ * (-((c : ℂ) * Complex.I) * (-((c : ℂ) * Complex.I) * Φ η 2 τ)))‖ ≤ G τ := by
    intro η hη τ hτ
    set u : ℝ := |c * τ| with hu
    have hu0 : 0 < u := abs_pos.mpr (mul_ne_zero hc0.ne' hτ)
    set s : ℂ := ((c * τ : ℝ) : ℂ) * Complex.I + ((η : ℝ) : ℂ) with hs
    have hsre : 0 < s.re := by simp [hs, hη]
    have hsu : u ≤ ‖s‖ := by
      have := Complex.abs_im_le_norm s
      simpa [hs, hu] using this
    have hpt := fun m (hm : m ≤ 2) => hB.tailPhi_pt hM hβ hsre hu0 hsu m N hm (by omega)
    have hz0 := hB.tailLapW_zero hM hβ hsre.le
    have P0 := hpt 0 (by norm_num)
    have P1 := hpt 1 (by norm_num)
    have P2 := hpt 2 (by norm_num)
    have Qb := tail_Q_bound (q := q) (N := N) rfl (M := M) (Z0 := Z0) (D0 := D 0) (D1 := D 1) (D2 := D 2) (A1 := A 1)
      (A2 := A 2) (u := u) (a0 := ‖Φ η 0 τ‖) (a1 := ‖Φ η 1 τ‖) (a2 := ‖Φ η 2 τ‖) hM hZ00 (hD0 0) (hD0 1) (hD0 2) (hA0 1)
      (hA0 2) hu0 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (by simp only [hΦ, hZ0]; nlinarith [hz0])
      P0.1 P1.1
      (fun hu1 => by have := P1.2 le_rfl hu1; rw [Nat.cast_one] at this; exact this)
      P2.1 (fun hu1 => P2.2 (by norm_num) hu1)
    obtain ⟨b0, b1, b2⟩ := hEb τ
    have hτu : |τ| = u / c := by rw [hu, abs_mul, abs_of_pos hc0]; field_simp
    have hX : 1 + |τ / h| ≤ 1 + u := by
      have hh1' : h⁻¹ ≤ (h ^ 2) ⁻¹ := by
        have : 1 ≤ h⁻¹ := one_le_inv₀ hh |>.mpr hh1
        rw [← inv_pow, pow_two]
        exact le_mul_of_one_le_left (inv_nonneg.mpr hh.le) this
      have : |τ / h| ≤ u := by
        rw [abs_div, abs_of_pos hh, hu, abs_mul, abs_of_pos hc0, div_eq_mul_inv]
        calc |τ| * h⁻¹ ≤ |τ| * (h ^ 2)⁻¹ := by gcongr
          _ = c * |τ| := by rw [hcdef]; ring
      linarith
    have hY0 : 0 ≤ (1 + u) ^ q := by positivity
    have hXY : (1 + |τ / h|) ^ q ≤ (1 + u) ^ q := pow_le_pow_left₀ (by positivity) hX q
    have he0 : ‖E τ‖ ≤ CE * (u / c) * (1 + u) ^ q := by
      refine b0.trans ?_
      rw [hτu]; gcongr
    have he1 : ‖deriv E τ‖ ≤ CE * (1 + u) ^ q := b1.trans (by gcongr)
    have he2 : ‖deriv (deriv E) τ‖ ≤ CE * c * (1 + u) ^ q := b2.trans (by gcongr)
    obtain ⟨T1, T2, T3⟩ := tail_num (CE := CE) (c := c) (u := u) (Y := (1 + u) ^ q) hc1 hu0 hY0 hCE0
      (norm_nonneg (Φ η 0 τ)) (norm_nonneg (Φ η 1 τ)) (norm_nonneg (Φ η 2 τ)) he0 he1 he2
    have hcn : ‖-((c : ℂ) * Complex.I)‖ = c := by
      rw [norm_neg, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_of_nonneg hc0.le]
    have hGe : CE * c * ((1 + u) * (1 + u) ^ q * (‖Φ η 0 τ‖ + 2 * ‖Φ η 1 τ‖ + u * ‖Φ η 2 τ‖)) ≤ G τ := by
      have e : (1 + u) * (1 + u) ^ q = (1 + u) ^ (q + 1) := by ring
      rw [e]
      simp only [hG, hψ]
      have hu' : |c * τ| = u := rfl
      rw [hu']
      have := mul_le_mul_of_nonneg_left Qb (by positivity : 0 ≤ CE * c)
      refine this.trans (le_of_eq ?_)
      ring
    refine ⟨?_, ?_, ?_⟩
    · rw [norm_mul]; exact T1.trans hGe
    · refine le_trans ?_ (T2.trans hGe)
      calc _ ≤ ‖deriv E τ * Φ η 0 τ‖ + ‖E τ * (-((c : ℂ) * Complex.I) * Φ η 1 τ)‖ := norm_add_le _ _
        _ = ‖deriv E τ‖ * ‖Φ η 0 τ‖ + c * ‖E τ‖ * ‖Φ η 1 τ‖ := by simp only [norm_mul, hcn]; ring
    · refine le_trans ?_ (T3.trans hGe)
      calc _ ≤ (‖deriv (deriv E) τ * Φ η 0 τ‖ + ‖deriv E τ * (-((c : ℂ) * Complex.I) * Φ η 1 τ)‖) +
            (‖deriv E τ * (-((c : ℂ) * Complex.I) * Φ η 1 τ)‖ +
              ‖E τ * (-((c : ℂ) * Complex.I) * (-((c : ℂ) * Complex.I) * Φ η 2 τ))‖) :=
            (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
        _ = ‖deriv (deriv E) τ‖ * ‖Φ η 0 τ‖ + 2 * c * ‖deriv E τ‖ * ‖Φ η 1 τ‖ + c ^ 2 * ‖E τ‖ * ‖Φ η 2 τ‖ := by
            simp only [norm_mul, hcn]; ring
  -- two integrations by parts for each `η > 0`
  have hbound : ∀ η : ℝ, 0 < η →
      ‖∫ τ : ℝ, E τ * Φ η 0 τ * Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ))‖ ≤
        CE * KQ * Ipsi * M * (c ^ 2)⁻¹ * (L ^ 2)⁻¹ := by
    intro η hη
    set cI : ℂ := -((c : ℂ) * Complex.I) with hcI
    set f : ℝ → ℂ := fun τ => E τ * Φ η 0 τ with hf
    set g1 : ℝ → ℂ := fun τ => deriv E τ * Φ η 0 τ + E τ * (cI * Φ η 1 τ) with hg1
    set g2 : ℝ → ℂ := fun τ => (deriv (deriv E) τ * Φ η 0 τ + deriv E τ * (cI * Φ η 1 τ)) +
      (deriv E τ * (cI * Φ η 1 τ) + E τ * (cI * (cI * Φ η 2 τ))) with hg2
    have hfd : ∀ τ, HasDerivAt f (g1 τ) τ := fun τ => (hEd τ).mul (hΦd η hη 0 τ)
    have hg1d : ∀ τ, HasDerivAt g1 (g2 τ) τ := fun τ =>
      ((hEd1 τ).mul (hΦd η hη 0 τ)).add ((hEd τ).mul (((hΦd η hη 1 τ).const_mul cI).congr_deriv (by rw [hcI])))
    have hΦ0c := hΦc η hη 0
    have hΦ1c := hΦc η hη 1
    have hΦ2c := hΦc η hη 2
    have hg1c : Continuous g1 := by
      simp only [hg1]
      exact (hE1c.mul hΦ0c).add (hEc.mul (continuous_const.mul hΦ1c))
    have hg2c : Continuous g2 := by
      simp only [hg2]
      exact ((hE2c.mul hΦ0c).add (hE1c.mul (continuous_const.mul hΦ1c))).add
        ((hE1c.mul (continuous_const.mul hΦ1c)).add (hEc.mul (continuous_const.mul (continuous_const.mul hΦ2c))))
    have i0 : Integrable f :=
      hGi.mono' (hEc.mul hΦ0c).aestronglyMeasurable (by filter_upwards [hne] with τ hτ using (key η hη τ hτ).1)
    have i1 : Integrable g1 :=
      hGi.mono' hg1c.aestronglyMeasurable (by filter_upwards [hne] with τ hτ using (key η hη τ hτ).2.1)
    have i2 : Integrable g2 :=
      hGi.mono' hg2c.aestronglyMeasurable (by filter_upwards [hne] with τ hτ using (key η hη τ hτ).2.2)
    have hω : c * L ≠ 0 := (mul_pos hc0 hL).ne'
    have ft := fourier_twice hfd hg1d hg1c hg2c i0 i1 i2 hω
    have hint2 : ∫ τ : ℝ, ‖g2 τ‖ ≤ ∫ τ : ℝ, G τ :=
      integral_mono_of_nonneg (ae_of_all _ fun τ => norm_nonneg _) hGi
        (by filter_upwards [hne] with τ hτ using (key η hη τ hτ).2.2)
    have hGint : ∫ τ : ℝ, G τ = CE * KQ * Ipsi * M := by
      have h1 : ∫ τ : ℝ, G τ = CE * c * (KQ * M) * ∫ τ : ℝ, ψ (c * τ) := by
        simp only [hG]; rw [← integral_const_mul]; congr 1; funext τ; ring
      rw [h1, Measure.integral_comp_mul_left ψ c, smul_eq_mul, abs_of_pos (inv_pos.mpr hc0)]
      field_simp
      rfl
    refine ft.trans ?_
    rw [hGint] at hint2
    calc (∫ τ : ℝ, ‖g2 τ‖) / (c * L) ^ 2 ≤ (CE * KQ * Ipsi * M) / (c * L) ^ 2 := by gcongr
      _ = _ := by rw [mul_pow]; field_simp
  -- the limit `η ↓ 0`
  set Λ : ℝ → ℂ := fun τ => bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I)) with hΛ
  set F0 : ℝ → ℂ := fun τ => bumpE0 c τ * Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) * Λ τ with hF0
  set Fη : ℝ → ℝ → ℂ := fun η τ => E τ * Φ η 0 τ * Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) with hFη
  have hexpc : Continuous fun τ : ℝ => Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) := by fun_prop
  have hlim : ∀ τ : ℝ, Tendsto (fun η : ℝ => Fη η τ) (𝓝[>] (0 : ℝ)) (𝓝 (F0 τ)) := by
    intro τ
    have hcl : ContinuousOn (fun η : ℝ => bumpLaplace B (((c * τ : ℝ) : ℂ) * Complex.I + ((η : ℝ) : ℂ))) (Ici 0) := by
      refine (hB.continuousOn_laplace (by norm_num) (by norm_num) hβ1).comp (by fun_prop : Continuous fun η : ℝ =>
        ((c * τ : ℝ) : ℂ) * Complex.I + ((η : ℝ) : ℂ)).continuousOn (fun η hη => ?_)
      simpa using hη
    have h0 := (hcl 0 (mem_Ici.mpr le_rfl)).tendsto
    have h1 : Tendsto (fun η : ℝ => bumpLaplace B (((c * τ : ℝ) : ℂ) * Complex.I + ((η : ℝ) : ℂ))) (𝓝[>] (0 : ℝ))
        (𝓝 (Λ τ)) := by
      have := h0.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
      simp only [Complex.ofReal_zero, add_zero] at this
      have e : Λ τ = bumpLaplace B (((c * τ : ℝ) : ℂ) * Complex.I) := by
        simp only [hΛ]; congr 1; push_cast; ring
      rw [e]; exact this
    have h2 : Tendsto (fun η : ℝ => Fη η τ) (𝓝[>] (0 : ℝ))
        (𝓝 (E τ * Λ τ * Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)))) := by
      have := (h1.const_mul (E τ)).mul_const (Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)))
      refine this.congr (fun η => ?_)
      simp only [hFη, hΦ, BumpProfile.bumpLapW_zero_B]
    have e2 : E τ * Λ τ * Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) = F0 τ := by
      simp only [hF0, hEdef]; ring
    rw [e2] at h2
    exact h2
  have hF0c : Continuous F0 := by
    simp only [hF0]
    exact (hEc.mul hexpc).mul hcontL
  have hFbd : ∀ η : ℝ, 0 < η → ∀ τ : ℝ, τ ≠ 0 → ‖Fη η τ‖ ≤ G τ := by
    intro η hη τ hτ
    simp only [hFη]
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
    exact (key η hη τ hτ).1
  have hF0bd : ∀ τ : ℝ, τ ≠ 0 → ‖F0 τ‖ ≤ G τ := fun τ hτ =>
    le_of_tendsto (hlim τ).norm (eventually_of_mem self_mem_nhdsWithin fun η hη => hFbd η hη τ hτ)
  have hF0i : Integrable F0 :=
    hGi.mono' hF0c.aestronglyMeasurable (by filter_upwards [hne] with τ hτ using hF0bd τ hτ)
  refine ⟨hF0i, ?_⟩
  have hdom := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ)) G
    (F := Fη) (f := F0)
    (eventually_of_mem self_mem_nhdsWithin fun η hη =>
      ((hEc.mul (hΦc η hη 0)).mul hexpc).aestronglyMeasurable)
    (eventually_of_mem self_mem_nhdsWithin fun η hη => by
      filter_upwards [hne] with τ hτ using hFbd η hη τ hτ)
    hGi (by filter_upwards [hne] with τ hτ using hlim τ)
  have := le_of_tendsto hdom.norm (eventually_of_mem self_mem_nhdsWithin fun η (hη : 0 < η) => hbound η hη)
  refine this.trans (le_of_eq ?_)
  ring

/-- info: 'FormalResearch.SignUncertainty.bump_tail_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_tail_bound

end FormalResearch.SignUncertainty
