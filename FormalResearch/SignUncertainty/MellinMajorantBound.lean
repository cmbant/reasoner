module

public import FormalResearch.SignUncertainty.MellinMajorant

/-!
# The Mellin majorant, edge bounds, growth and Phragmén–Lindelöf (`gt:7.4(2)`)

See `MellinMajorant` for the set-up. This module proves that `W = mellinW c ε f` is bounded by
`M[f] e^{1/(6c)}` on both edges of `0 ≤ Re ζ ≤ 1`, has growth `exp(B exp(3 |Im ζ|))` inside, and applies
`PhragmenLindelof.vertical_strip`; the main result is `norm_mellinStrip_le_majorant`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

lemma norm_sqrt_cpow {ζ : ℂ} (hζ : 0 ≤ ζ.re) : ‖(1 + ζ) ^ (1 / 2 : ℂ)‖ = ‖1 + ζ‖ ^ (1 / 2 : ℝ) := by
  rw [Complex.norm_cpow_of_ne_zero (one_add_ne_zero hζ)]
  simp

lemma rpow_quarter_le {x N : ℝ} (hx : 0 ≤ x) (hN0 : 0 ≤ N) (hN : x ≤ N ^ 2) :
    x ^ (1 / 4 : ℝ) ≤ N ^ (1 / 2 : ℝ) := by
  have h1 : x ^ (1 / 4 : ℝ) = (Real.sqrt x) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]; norm_num
  rw [h1]
  exact Real.rpow_le_rpow (Real.sqrt_nonneg _) (Real.sqrt_le_iff.mpr ⟨hN0, hN⟩) (by norm_num)

/-- The edge bound in terms of `hInt`: `|M̃_f(c(1 - iτ))| ≤ M (1+τ²)^{1/4} exp(c Re ℋ̂(iτ) + 1/(6c))`. -/
theorem norm_mellinStrip_edge_core {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (τ : ℝ) :
    ‖mellinStrip f ((c : ℂ) * (1 - (τ : ℂ) * Complex.I))‖ ≤
      hankelMass c f * ((1 + τ ^ 2) ^ (1 / 4 : ℝ) *
        Real.exp (c * (hInt ((τ : ℂ) * Complex.I)).re + 1 / (6 * c))) := by
  have h1 := norm_mellinStrip_edge_le hc hf (-(c * τ))
  have e1 : (c : ℂ) + ((-(c * τ) : ℝ) : ℂ) * Complex.I = (c : ℂ) * (1 - (τ : ℂ) * Complex.I) := by
    push_cast; ring
  rw [e1] at h1
  have h2 := gamma_ratio_edge_le hc τ
  rw [re_hInt_imag]
  have hM := hankelMass_nonneg hc f
  calc _ ≤ Real.Gamma c * hankelMass c f / ‖Complex.Gamma ((c : ℂ) * (1 - (τ : ℂ) * Complex.I))‖ := h1
    _ = hankelMass c f * (Real.Gamma c / ‖Complex.Gamma ((c : ℂ) * (1 - (τ : ℂ) * Complex.I))‖) := by
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 hM

/-- From an edge bound for `Fm` to the bound `M e^{1/(6c)}` for `W`. -/
theorem norm_mellinW_le_of_edge {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} {ζ : ℂ} (hζ0 : 0 ≤ ζ.re)
    (τ : ℝ)
    (hF : ‖mellinFm c ε f ζ‖ ≤ hankelMass c f * ((1 + τ ^ 2) ^ (1 / 4 : ℝ) *
      Real.exp (c * (hInt ζ).re + 1 / (6 * c))))
    (hN : 1 + τ ^ 2 ≤ ‖1 + ζ‖ ^ 2) (hM : 0 ≤ hankelMass c f) :
    ‖mellinW c ε f ζ‖ ≤ hankelMass c f * Real.exp (1 / (6 * c)) := by
  have hA0 : 0 < (1 + τ ^ 2) ^ (1 / 4 : ℝ) := by positivity
  have hAN : (1 + τ ^ 2) ^ (1 / 4 : ℝ) ≤ ‖1 + ζ‖ ^ (1 / 2 : ℝ) :=
    rpow_quarter_le (by positivity) (norm_nonneg _) hN
  have hNpos : 0 < ‖1 + ζ‖ ^ (1 / 2 : ℝ) := lt_of_lt_of_le hA0 hAN
  unfold mellinW
  rw [norm_mul, norm_mul, norm_inv, norm_sqrt_cpow hζ0, Complex.norm_exp]
  have hre : (-((c : ℂ) * hInt ζ)).re = -(c * (hInt ζ).re) := by simp
  rw [hre]
  set A := (1 + τ ^ 2) ^ (1 / 4 : ℝ) with hA
  set N := ‖1 + ζ‖ ^ (1 / 2 : ℝ) with hNdef
  set h := (hInt ζ).re with hh
  have e1 : Real.exp (c * h + 1 / (6 * c)) * Real.exp (-(c * h)) = Real.exp (1 / (6 * c)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc ‖mellinFm c ε f ζ‖ * Real.exp (-(c * h)) * N⁻¹
      ≤ (hankelMass c f * (A * Real.exp (c * h + 1 / (6 * c)))) * Real.exp (-(c * h)) * N⁻¹ := by
        gcongr
    _ = hankelMass c f * Real.exp (1 / (6 * c)) * (A / N) := by
        rw [← e1]; field_simp
    _ ≤ hankelMass c f * Real.exp (1 / (6 * c)) * 1 := by
        gcongr
        rw [div_le_one hNpos]; exact hAN
    _ = _ := mul_one _

theorem norm_mellinW_left_edge {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    {ζ : ℂ} (hζ : ζ.re = 0) :
    ‖mellinW c ε f ζ‖ ≤ hankelMass c f * Real.exp (1 / (6 * c)) := by
  have hc0 : 0 < c := by linarith
  set τ : ℝ := ζ.im with hτ
  have hζeq : ζ = (τ : ℂ) * Complex.I := Complex.ext (by simp [hζ]) (by simp [hτ])
  have hFm : mellinFm c ε f ζ = mellinStrip f ((c : ℂ) * (1 - (τ : ℂ) * Complex.I)) := by
    rw [mellinFm_eq hc hf (by rw [hζ]) (by rw [hζ]; norm_num), hζeq]
  refine norm_mellinW_le_of_edge hc0 (by rw [hζ]) τ ?_ ?_ (hankelMass_nonneg hc0 f)
  · rw [hFm, hζeq]; exact norm_mellinStrip_edge_core hc0 hf τ
  · have : ‖1 + ζ‖ ^ 2 = 1 + τ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp [hζ]; ring
    rw [this]

theorem norm_mellinW_right_edge {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) {ζ : ℂ} (hζ : ζ.re = 1) :
    ‖mellinW c ε f ζ‖ ≤ hankelMass c f * Real.exp (1 / (6 * c)) := by
  have hc0 : 0 < c := by linarith
  set τ : ℝ := -ζ.im with hτ
  have hζeq : ζ = 1 - (τ : ℂ) * Complex.I := Complex.ext (by simp [hζ]) (by simp [hτ])
  have hFm : mellinFm c ε f ζ = (ε : ℂ) * mellinStrip f ((c : ℂ) * (1 - (τ : ℂ) * Complex.I)) := by
    unfold mellinFm
    rw [if_neg (by rw [hζ]; norm_num), ← hζeq]
  have hε1 : ‖(ε : ℂ)‖ = 1 := by rcases hε with h | h <;> simp [h]
  have hmem : ((τ : ℂ) * Complex.I) ∈ hStrip := ⟨by simp, by simp⟩
  have hH : hInt ζ = hInt ((τ : ℂ) * Complex.I) := by
    rw [hζeq, hInt_one_sub hmem]
  refine norm_mellinW_le_of_edge hc0 (by rw [hζ]; norm_num) τ ?_ ?_ (hankelMass_nonneg hc0 f)
  · rw [hFm, norm_mul, hε1, one_mul, hH]; exact norm_mellinStrip_edge_core hc0 hf τ
  · have : ‖1 + ζ‖ ^ 2 = 4 + τ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp [hζ, hτ]; ring
    rw [this]; linarith

/-- Double-exponential growth of `W` inside the strip. -/
theorem mellinW_growth {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) :
    ∃ B : ℝ, ∀ ζ : ℂ, 0 < ζ.re → ζ.re < 1 →
      ‖mellinW c ε f ζ‖ ≤ Real.exp (B * Real.exp (3 * |ζ.im|)) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨K, hK0, hK⟩ := exists_norm_mellinStrip_le hc hf hε
  refine ⟨K + K * c + 4400 * c, fun ζ hζ0 hζ1 => ?_⟩
  set Y : ℝ := |ζ.im| with hY
  have hY0 : 0 ≤ Y := abs_nonneg _
  have hre : ((c : ℂ) * (1 - ζ)).re = c * (1 - ζ.re) := by simp
  have him : |((c : ℂ) * (1 - ζ)).im| = c * Y := by
    have : ((c : ℂ) * (1 - ζ)).im = -(c * ζ.im) := by simp
    rw [this, abs_neg, abs_mul, abs_of_pos hc0]
  -- the three factors
  have hF : ‖mellinFm c ε f ζ‖ ≤ K * Real.exp (K * (c * Y)) := by
    rw [mellinFm_eq hc hf hζ0.le hζ1]
    have := hK ((c : ℂ) * (1 - ζ)) (by rw [hre]; nlinarith) (by rw [hre]; nlinarith)
    rwa [him] at this
  have hnζ : ‖ζ‖ ≤ 1 + Y := by
    refine (Complex.norm_le_abs_re_add_abs_im ζ).trans ?_
    have : |ζ.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    linarith
  have hHb : ‖hInt ζ‖ ≤ 4400 * (1 + Y) ^ 3 := by
    refine (norm_hInt_le hζ0.le hζ1.le).trans ?_
    have h1 : ‖ζ‖ * (1 + ‖ζ‖) ^ 2 ≤ (1 + Y) * (2 + Y) ^ 2 := by
      have h2 : (1 + ‖ζ‖) ^ 2 ≤ (2 + Y) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
      exact mul_le_mul (by linarith) h2 (by positivity) (by linarith)
    have h3 : (1 + Y) * (2 + Y) ^ 2 ≤ 4 * (1 + Y) ^ 3 := by
      have : (2 + Y) ^ 2 ≤ 4 * (1 + Y) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ 1 + Y)]
    nlinarith
  have hExp : ‖Complex.exp (-((c : ℂ) * hInt ζ))‖ ≤ Real.exp (4400 * c * (1 + Y) ^ 3) := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have hre : (-((c : ℂ) * hInt ζ)).re = -(c * (hInt ζ).re) := by simp
    rw [hre]
    have h1 : -(hInt ζ).re ≤ ‖hInt ζ‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm _)
    nlinarith [mul_le_mul_of_nonneg_left h1 hc0.le, mul_le_mul_of_nonneg_left hHb hc0.le]
  have hP : ‖((1 + ζ) ^ (1 / 2 : ℂ))⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_sqrt_cpow hζ0.le]
    refine inv_le_one_of_one_le₀ (Real.one_le_rpow ?_ (by norm_num))
    have := Complex.re_le_norm (1 + ζ)
    simp at this
    linarith
  have hY3 : Y ≤ (1 + Y) ^ 3 := by nlinarith [sq_nonneg Y, mul_nonneg hY0 hY0]
  have h13 : 1 ≤ (1 + Y) ^ 3 := one_le_pow₀ (by linarith)
  have hexp3 : (1 + Y) ^ 3 ≤ Real.exp (3 * |ζ.im|) := by
    have h1 : 1 + Y ≤ Real.exp Y := by linarith [Real.add_one_le_exp Y]
    have h2 : Real.exp (3 * Y) = Real.exp Y ^ 3 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [← hY, h2]
    exact pow_le_pow_left₀ (by linarith) h1 3
  have hKe : K ≤ Real.exp K := by linarith [Real.add_one_le_exp K]
  unfold mellinW
  rw [norm_mul, norm_mul]
  calc ‖mellinFm c ε f ζ‖ * ‖Complex.exp (-((c : ℂ) * hInt ζ))‖ * ‖((1 + ζ) ^ (1 / 2 : ℂ))⁻¹‖
      ≤ (K * Real.exp (K * (c * Y))) * Real.exp (4400 * c * (1 + Y) ^ 3) * 1 := by gcongr
    _ ≤ Real.exp K * Real.exp (K * (c * Y)) * Real.exp (4400 * c * (1 + Y) ^ 3) * 1 := by gcongr
    _ = Real.exp (K + K * (c * Y) + 4400 * c * (1 + Y) ^ 3) := by
        rw [mul_one, ← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp ((K + K * c + 4400 * c) * Real.exp (3 * |ζ.im|)) := by
        refine Real.exp_le_exp.mpr ?_
        have a1 : K ≤ K * (1 + Y) ^ 3 := le_mul_of_one_le_right hK0 h13
        have a2 : K * (c * Y) ≤ K * c * (1 + Y) ^ 3 := by
          have := mul_le_mul_of_nonneg_left hY3 (mul_nonneg hK0 hc0.le)
          linarith
        have a3 : (K + K * c + 4400 * c) * (1 + Y) ^ 3 ≤
            (K + K * c + 4400 * c) * Real.exp (3 * |ζ.im|) :=
          mul_le_mul_of_nonneg_left hexp3 (by positivity)
        nlinarith

/-- Phragmén–Lindelöf: `‖W‖ ≤ M[f] e^{1/(6c)}` on the closed strip. -/
theorem norm_mellinW_le {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) {ζ : ℂ} (hζ0 : 0 ≤ ζ.re) (hζ1 : ζ.re ≤ 1) :
    ‖mellinW c ε f ζ‖ ≤ hankelMass c f * Real.exp (1 / (6 * c)) := by
  obtain ⟨B, hB⟩ := mellinW_growth hc hf hε
  refine PhragmenLindelof.vertical_strip (a := 0) (b := 1) (f := mellinW c ε f)
    (diffContOnCl_mellinW hc hf) ⟨3, by linarith [Real.pi_gt_three], B, ?_⟩
    (fun ζ hζ => norm_mellinW_left_edge hc hf hζ)
    (fun ζ hζ => norm_mellinW_right_edge hc hf hε hζ) hζ0 hζ1
  refine Asymptotics.IsBigO.of_bound 1 ?_
  rw [Filter.eventually_inf_principal]
  refine Filter.Eventually.of_forall fun ζ hζ => ?_
  have hζ' : 0 < ζ.re ∧ ζ.re < 1 := hζ
  rw [one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hB ζ hζ'.1 hζ'.2

/-- **`gt:7.4(2)`, the Mellin majorant.** For `c > 3/2`, `f ∈ 𝒜_c^ε`, `ε = ±1` and `0 ≤ Re ζ < 1`:
`|M̃_f(c(1-ζ))| ≤ M[f] |1+ζ|^{1/2} exp(c Re ℋ(ζ) + 1/(6c))`, with `ℋ = hInt`. -/
theorem norm_mellinStrip_le_majorant {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ}
    (hf : IsHankelEigenfn c ε f) (hε : ε = 1 ∨ ε = -1) {ζ : ℂ} (hζ0 : 0 ≤ ζ.re) (hζ1 : ζ.re < 1) :
    ‖mellinStrip f ((c : ℂ) * (1 - ζ))‖ ≤
      hankelMass c f * ‖1 + ζ‖ ^ (1 / 2 : ℝ) *
        Real.exp (c * (hInt ζ).re + 1 / (6 * c)) := by
  have hW := norm_mellinW_le hc hf hε hζ0 hζ1.le
  rw [← mellinFm_eq hc hf hζ0 hζ1]
  have hP : 0 < ‖1 + ζ‖ ^ (1 / 2 : ℝ) := by
    have : 0 < ‖1 + ζ‖ := norm_pos_iff.mpr (one_add_ne_zero hζ0)
    positivity
  have hFm : mellinFm c ε f ζ = mellinW c ε f ζ * Complex.exp ((c : ℂ) * hInt ζ) *
      (1 + ζ) ^ (1 / 2 : ℂ) := by
    unfold mellinW
    have h1 := sqrt_cpow_ne_zero hζ0
    have hE : Complex.exp (-((c : ℂ) * hInt ζ)) * Complex.exp ((c : ℂ) * hInt ζ) = 1 := by
      rw [← Complex.exp_add]; simp
    calc mellinFm c ε f ζ = mellinFm c ε f ζ * (Complex.exp (-((c : ℂ) * hInt ζ)) *
          Complex.exp ((c : ℂ) * hInt ζ)) * ((1 + ζ) ^ (1 / 2 : ℂ))⁻¹ * (1 + ζ) ^ (1 / 2 : ℂ) := by
          rw [hE, mul_one, inv_mul_cancel_right₀ h1]
      _ = _ := by ring
  rw [hFm, norm_mul, norm_mul, Complex.norm_exp, norm_sqrt_cpow hζ0]
  have hre : ((c : ℂ) * hInt ζ).re = c * (hInt ζ).re := by simp
  rw [hre]
  have e : Real.exp (c * (hInt ζ).re + 1 / (6 * c)) =
      Real.exp (c * (hInt ζ).re) * Real.exp (1 / (6 * c)) := Real.exp_add _ _
  rw [e]
  have hM := hankelMass_nonneg (by linarith : 0 < c) f
  calc ‖mellinW c ε f ζ‖ * Real.exp (c * (hInt ζ).re) * ‖1 + ζ‖ ^ (1 / 2 : ℝ)
      ≤ (hankelMass c f * Real.exp (1 / (6 * c))) * Real.exp (c * (hInt ζ).re) *
        ‖1 + ζ‖ ^ (1 / 2 : ℝ) := by gcongr
    _ = _ := by ring

/-- The same bound with the principal-branch `ℋ = stripH` of `gt:7.4(2)`. -/
theorem norm_mellinStrip_le_majorant_stripH {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ}
    (hf : IsHankelEigenfn c ε f) (hε : ε = 1 ∨ ε = -1) {ζ : ℂ} (hζ0 : 0 ≤ ζ.re) (hζ1 : ζ.re < 1) :
    ‖mellinStrip f ((c : ℂ) * (1 - ζ))‖ ≤
      hankelMass c f * ‖1 + ζ‖ ^ (1 / 2 : ℝ) *
        Real.exp (c * (stripH ζ).re + 1 / (6 * c)) := by
  rw [← hInt_eq_stripH hζ0 hζ1]
  exact norm_mellinStrip_le_majorant hc hf hε hζ0 hζ1

/-- info: 'FormalResearch.SignUncertainty.norm_mellinStrip_edge_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_mellinStrip_edge_core

/-- info: 'FormalResearch.SignUncertainty.norm_mellinW_left_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_mellinW_left_edge

/-- info: 'FormalResearch.SignUncertainty.norm_mellinW_right_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_mellinW_right_edge

/-- info: 'FormalResearch.SignUncertainty.mellinW_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mellinW_growth

/-- info: 'FormalResearch.SignUncertainty.norm_mellinW_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_mellinW_le

/-- info: 'FormalResearch.SignUncertainty.norm_mellinStrip_le_majorant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_mellinStrip_le_majorant

/-- info: 'FormalResearch.SignUncertainty.norm_mellinStrip_le_majorant_stripH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_mellinStrip_le_majorant_stripH

end FormalResearch.SignUncertainty
