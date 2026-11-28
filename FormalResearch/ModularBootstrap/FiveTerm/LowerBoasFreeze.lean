module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasFreezeOsc
public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasFreezeTaper
public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasFreezeGauss

/-!
# Centre-Averaged Freezing of `P`, `W_1`, `θ` in `cts:boas` (`ctl:freeze`)

Formalizes `ctl:freeze` (`CFT/modular_bootstrap/paper/constant_term_lower_log.tex`) and the
Fubini/window-freezing reduction of Step 3 of Lemma C8 (`cts:boas`) in `constant_term_slit_strip.tex`:

* `boasZetaStar c' := zetaMin c' + 8 * Real.log c' + 1`.
* `boasPhi0 c' z := if 0 < z then unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' z) / (2 * π) - 1 / 4 else 0`.
* `boasA c' R ζ z := lowerPζ c' R z * (1 - 2 * lowerWeps (c' ^ (-2 : ℝ)) (lowerY (xOfZeta c' z)) *
    Real.sin (2 * π * ζ - unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' z)))`.
* `boasA_eq_cos`: exact phase shift rewriting `1 - 2 W_0 sin(2πζ - θ_0)` as
  `(1 - W_0) + W_0 (1 + 2 cos(2π(ζ - φ_0)))`.
* `boas_freezing_estimate`: compares `∫_{ζ ≥ ζ_min} boasA c' R ζ ζ * h ζ` against the
  `z ≥ ζ_*` centre-averaged frozen window integral `∫_{z ≥ ζ_*} boasFrozenInt c' R h z`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special
open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

noncomputable section

/-! ### 1. Definitions and cosine rewriting -/

/-- Lower centre cutoff `ζ_* = ζ_min + 8 log c' + 1`. -/
def boasZetaStar (c' : ℝ) : ℝ := zetaMin c' + 8 * Real.log c' + 1

/-- Measurable centre phase `φ₀(z) = θ(z) / (2π) - 1/4` for `z > 0` (`0` otherwise). -/
def boasPhi0 (c' z : ℝ) : ℝ :=
  if 0 < z then unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' z) / (2 * π) - 1 / 4 else 0

/-- Frozen integrand factor `A_ζ(z) = P(z) [1 - 2 W₁(z) sin(2πζ - θ(z))]`. -/
def boasA (c' R ζ z : ℝ) : ℝ :=
  lowerPζ c' R z *
    (1 - 2 * lowerWeps (c' ^ (-2 : ℝ)) (lowerY (xOfZeta c' z)) *
      Real.sin (2 * π * ζ - unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' z)))

/-- Frozen local Gaussian-windowed integral over `[z - L_0(z), z + L_0(z)]`. -/
def boasFrozenInt (c' R : ℝ) (h : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ ζ in (z - goodL0 c' (boasPhi0 c') z)..(z + goodL0 c' (boasPhi0 c') z),
    gaussW c' (z - ζ) * boasA c' R ζ z * h ζ

lemma boasA_eq_cos (c' R ζ z : ℝ) (hz : 0 < z) :
    boasA c' R ζ z =
      lowerPζ c' R z *
        ((1 - lowerWeps (c' ^ (-2 : ℝ)) (lowerY (xOfZeta c' z))) +
          lowerWeps (c' ^ (-2 : ℝ)) (lowerY (xOfZeta c' z)) *
            (1 + 2 * Real.cos (2 * π * (ζ - boasPhi0 c' z)))) := by
  unfold boasA boasPhi0
  simp only [hz, ↓reduceIte]
  set θ₀ := unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' z)
  have hpi := Real.pi_pos.ne'
  have harg : 2 * π * (ζ - (θ₀ / (2 * π) - 1 / 4)) = (2 * π * ζ - θ₀) + π / 2 := by
    field_simp [hpi]; ring
  rw [harg, Real.cos_add_pi_div_two]
  ring

lemma abs_boasA_le {c' R ζ z : ℝ} (hc0 : 0 < c') (hz : 0 < z) (hP : 0 ≤ lowerPζ c' R z) :
    |boasA c' R ζ z| ≤ 3 * lowerPζ c' R z := by
  have hW := lowerWeps_mem_Icc (Real.rpow_nonneg hc0.le (-2)) (xOfZeta_spec hc0 hz).1
  have hsin := Real.abs_sin_le_one (2 * π * ζ - unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' z))
  have hfac : |1 - 2 * lowerWeps (c' ^ (-2 : ℝ)) (lowerY (xOfZeta c' z)) *
      Real.sin (2 * π * ζ - unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' z))| ≤ 3 := by
    refine (abs_sub _ _).trans ?_
    rw [abs_one, abs_mul, abs_mul, abs_of_pos zero_lt_two, abs_of_nonneg hW.1]
    have hmul : lowerWeps (c' ^ (-2 : ℝ)) (lowerY (xOfZeta c' z)) *
        |Real.sin (2 * π * ζ - unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' z))| ≤ 1 := by
      calc _ ≤ 1 * 1 := mul_le_mul hW.2 hsin (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    linarith only [hmul]
  unfold boasA
  rw [abs_mul, abs_of_nonneg hP, mul_comm (lowerPζ c' R z)]
  exact mul_le_mul_of_nonneg_right hfac hP

lemma measurable_boasPhi0 {c' : ℝ} (hc' : 10000 ≤ c') : Measurable (boasPhi0 c') := by
  obtain ⟨_, _, hWθ⟩ := lowerWeps_unwrappedTheta_deriv_bounds
  obtain ⟨_, _, θ', _, hspec⟩ := hWθ hc'
  have hθ : ContinuousOn (fun z => unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' z)) (Ioi 0) :=
    fun z hz => (hspec hz).2.2.1.continuousAt.continuousWithinAt
  have hcont : ContinuousOn (fun z => unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' z) / (2 * π) - 1 / 4)
      (Ioi 0) := (hθ.div_const _).sub continuousOn_const
  have heq : boasPhi0 c' =
      (Ioi (0 : ℝ)).piecewise (fun z => unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' z) / (2 * π) - 1 / 4) 0 := by
    ext z; unfold boasPhi0 Set.piecewise; simp [mem_Ioi]
  rw [heq]
  exact hcont.measurable_piecewise continuousOn_const measurableSet_Ioi

/-! ### 2. Global `C^1` + piecewise `C^2` quadratic Taylor bound on compact intervals -/

private lemma deriv_lip_one_split {f1 f2 : ℝ → ℝ} {a b c₀ M2 u v : ℝ}
    (hcont : ContinuousOn f1 (Icc a b))
    (hd : ∀ {t : ℝ}, a ≤ t → t ≤ b → t ≠ c₀ → HasDerivAt f1 (f2 t) t)
    (hbd : ∀ {t : ℝ}, a ≤ t → t ≤ b → |f2 t| ≤ M2)
    (_hM2_nn : 0 ≤ M2)
    (ha : a ≤ u) (huv : u ≤ v) (hb : v ≤ b) :
    |f1 v - f1 u| ≤ M2 * (v - u) := by
  rcases huv.eq_or_lt with rfl | hlt
  · simp
  have hsub : ∀ {p q : ℝ}, a ≤ p → p < q → q ≤ b → (∀ t ∈ Ioo p q, t ≠ c₀) →
      |f1 q - f1 p| ≤ M2 * (q - p) := by
    intro p q hp hpq hqb hno
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f1 f2 hpq
      (hcont.mono fun t ht => ⟨hp.trans ht.1, ht.2.trans hqb⟩)
      (fun t ht => hd (hp.trans ht.1.le) (ht.2.le.trans hqb) (hno t ht))
    have hdiff : f1 q - f1 p = f2 ξ * (q - p) := by
      rw [hslope, div_mul_cancel₀ _ (sub_pos.mpr hpq).ne']
    rw [hdiff, abs_mul, abs_of_pos (sub_pos.mpr hpq)]
    exact mul_le_mul_of_nonneg_right (hbd (hp.trans hξ.1.le) (hξ.2.le.trans hqb))
      (sub_pos.mpr hpq).le
  by_cases hc₀ : c₀ ∈ Ioo u v
  · have h1 := hsub ha hc₀.1 (hc₀.2.le.trans hb) (fun t ht => ht.2.ne)
    have h2 := hsub (ha.trans hc₀.1.le) hc₀.2 hb (fun t ht => ht.1.ne')
    calc |f1 v - f1 u|
        = |(f1 v - f1 c₀) + (f1 c₀ - f1 u)| := by ring_nf
      _ ≤ |f1 v - f1 c₀| + |f1 c₀ - f1 u| := abs_add_le _ _
      _ ≤ M2 * (v - c₀) + M2 * (c₀ - u) := add_le_add h2 h1
      _ = M2 * (v - u) := by ring
  · exact hsub ha hlt hb (fun t ht heq => hc₀ (heq ▸ ht))

private lemma taylor2_of_c1_piecewise_c2 {f f1 f2 : ℝ → ℝ} {a b c₀ M2 ζ z : ℝ}
    (hcont : ContinuousOn f1 (Icc a b))
    (hd1 : ∀ {t : ℝ}, a ≤ t → t ≤ b → HasDerivAt f (f1 t) t)
    (hd2 : ∀ {t : ℝ}, a ≤ t → t ≤ b → t ≠ c₀ → HasDerivAt f1 (f2 t) t)
    (hbd : ∀ {t : ℝ}, a ≤ t → t ≤ b → |f2 t| ≤ M2)
    (hM2_nn : 0 ≤ M2)
    (hζ : ζ ∈ Icc a b) (hz : z ∈ Icc a b) :
    |f z - f ζ - f1 ζ * (z - ζ)| ≤ M2 * (z - ζ) ^ 2 := by
  rcases lt_trichotomy ζ z with hlt | rfl | hlt
  · have hcf : ContinuousOn f (Icc ζ z) := fun t ht =>
      (hd1 (hζ.1.trans ht.1) (ht.2.trans hz.2)).continuousAt.continuousWithinAt
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f f1 hlt hcf
      (fun t ht => hd1 (hζ.1.trans ht.1.le) (ht.2.le.trans hz.2))
    have heq : f z - f ζ - f1 ζ * (z - ζ) = (f1 ξ - f1 ζ) * (z - ζ) := by
      rw [show f z - f ζ = f1 ξ * (z - ζ) by rw [hslope, div_mul_cancel₀ _ (sub_pos.mpr hlt).ne']]
      ring
    rw [heq, abs_mul, abs_of_pos (sub_pos.mpr hlt)]
    have hlip := deriv_lip_one_split hcont hd2 hbd hM2_nn hζ.1 hξ.1.le (hξ.2.le.trans hz.2)
    calc |f1 ξ - f1 ζ| * (z - ζ) ≤ (M2 * (ξ - ζ)) * (z - ζ) :=
          mul_le_mul_of_nonneg_right hlip (sub_pos.mpr hlt).le
      _ ≤ (M2 * (z - ζ)) * (z - ζ) := by have := hξ.2.le; gcongr
      _ = M2 * (z - ζ) ^ 2 := by ring
  · simp
  · have hcf : ContinuousOn f (Icc z ζ) := fun t ht =>
      (hd1 (hz.1.trans ht.1) (ht.2.trans hζ.2)).continuousAt.continuousWithinAt
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f f1 hlt hcf
      (fun t ht => hd1 (hz.1.trans ht.1.le) (ht.2.le.trans hζ.2))
    have heq : f z - f ζ - f1 ζ * (z - ζ) = (f1 ξ - f1 ζ) * (z - ζ) := by
      have hf : f ζ - f z = f1 ξ * (ζ - z) := by
        rw [hslope, div_mul_cancel₀ _ (sub_pos.mpr hlt).ne']
      linarith only [hf]
    rw [heq, abs_mul, abs_sub_comm z ζ, abs_of_pos (sub_pos.mpr hlt)]
    have hlip := deriv_lip_one_split hcont hd2 hbd hM2_nn (hz.1.trans hξ.1.le) hξ.2.le hζ.2
    calc |f1 ξ - f1 ζ| * (ζ - z)
        = |f1 ζ - f1 ξ| * (ζ - z) := by rw [abs_sub_comm]
      _ ≤ (M2 * (ζ - ξ)) * (ζ - z) := mul_le_mul_of_nonneg_right hlip (sub_pos.mpr hlt).le
      _ ≤ (M2 * (ζ - z)) * (ζ - z) := by have := hξ.1.le; gcongr
      _ = M2 * (z - ζ) ^ 2 := by ring

/-! ### 3. Coefficient `C^1` + piecewise `C^2` bounds for `P`, `P W₁ cos θ`, `P W₁ sin θ` -/

private lemma c1_piecewise_c2_mul {f f1 f2 g g1 g2 : ℝ → ℝ} {a c₀ : ℝ}
    (hf1 : ContinuousOn f1 (Ici a))
    (hdf : ∀ {t : ℝ}, a ≤ t → HasDerivAt f (f1 t) t)
    (hdf2 : ∀ {t : ℝ}, a ≤ t → t ≠ c₀ → HasDerivAt f1 (f2 t) t)
    (hdg : ∀ {t : ℝ}, a ≤ t → HasDerivAt g (g1 t) t)
    (hdg2 : ∀ {t : ℝ}, a ≤ t → HasDerivAt g1 (g2 t) t) :
    let h := fun t => f t * g t
    let h1 := fun t => f1 t * g t + f t * g1 t
    let h2 := fun t => f2 t * g t + 2 * f1 t * g1 t + f t * g2 t
    ContinuousOn h1 (Ici a) ∧
    (∀ {t : ℝ}, a ≤ t → HasDerivAt h (h1 t) t) ∧
    (∀ {t : ℝ}, a ≤ t → t ≠ c₀ → HasDerivAt h1 (h2 t) t) := by
  intro h h1 h2
  have hcf : ContinuousOn f (Ici a) := fun t ht => (hdf ht).continuousAt.continuousWithinAt
  have hcg : ContinuousOn g (Ici a) := fun t ht => (hdg ht).continuousAt.continuousWithinAt
  have hg1 : ContinuousOn g1 (Ici a) := fun t ht => (hdg2 ht).continuousAt.continuousWithinAt
  refine ⟨(hf1.mul hcg).add (hcf.mul hg1), fun {t} ht => (hdf ht).mul (hdg ht), fun {t} ht hne => ?_⟩
  exact ((hdf2 ht hne).mul (hdg ht)).add ((hdf ht).mul (hdg2 ht)) |>.congr_deriv (by dsimp [h2]; ring)

lemma boas_trig_c2_bounds :
    ∃ C_trig : ℝ, 0 < C_trig ∧ ∀ {c' : ℝ}, 10000 ≤ c' →
      let W1 := fun z => lowerWeps (c' ^ (-2 : ℝ)) (lowerY (xOfZeta c' z))
      let θ := fun z => unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' z)
      ∃ U1 U2 V1 V2 : ℝ → ℝ, ∀ {z : ℝ}, 0 < z →
        HasDerivAt (fun t => W1 t * Real.cos (θ t)) (U1 z) z ∧
        HasDerivAt U1 (U2 z) z ∧
        HasDerivAt (fun t => W1 t * Real.sin (θ t)) (V1 z) z ∧
        HasDerivAt V1 (V2 z) z ∧
        |U1 z| ≤ C_trig * (z⁻¹ + c'⁻¹) ∧
        |U2 z| ≤ C_trig * (z ^ (-2 : ℝ) + c' ^ (-2 : ℝ)) ∧
        |V1 z| ≤ C_trig * (z⁻¹ + c'⁻¹) ∧
        |V2 z| ≤ C_trig * (z ^ (-2 : ℝ) + c' ^ (-2 : ℝ)) := by
  obtain ⟨C_osc, hCosc, hWθ⟩ := lowerWeps_unwrappedTheta_deriv_bounds
  let C_trig : ℝ := 2 * C_osc + 6 * C_osc ^ 2 + 1
  refine ⟨C_trig, by positivity, fun {c'} hc' => ?_⟩
  have hc0 : 0 < c' := by linarith
  have hε0 : 0 ≤ c' ^ (-2 : ℝ) := Real.rpow_nonneg hc0.le _
  obtain ⟨W1', W1'', θ', θ'', hspec⟩ := hWθ hc'
  let W1 := fun z => lowerWeps (c' ^ (-2 : ℝ)) (lowerY (xOfZeta c' z))
  let θ := fun z => unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' z)
  let c1 := fun z => -(Real.sin (θ z)) * θ' z
  let c2 := fun z => -(Real.cos (θ z)) * θ' z ^ 2 - Real.sin (θ z) * θ'' z
  let s1 := fun z => Real.cos (θ z) * θ' z
  let s2 := fun z => -(Real.sin (θ z)) * θ' z ^ 2 + Real.cos (θ z) * θ'' z
  let U1 := fun z => W1' z * Real.cos (θ z) + W1 z * c1 z
  let U2 := fun z => W1'' z * Real.cos (θ z) + 2 * W1' z * c1 z + W1 z * c2 z
  let V1 := fun z => W1' z * Real.sin (θ z) + W1 z * s1 z
  let V2 := fun z => W1'' z * Real.sin (θ z) + 2 * W1' z * s1 z + W1 z * s2 z
  have hc_hd : ∀ {z : ℝ}, 0 < z → HasDerivAt (fun t => Real.cos (θ t)) (c1 z) z ∧
      HasDerivAt c1 (c2 z) z ∧
      HasDerivAt (fun t => Real.sin (θ t)) (s1 z) z ∧
      HasDerivAt s1 (s2 z) z := fun {z} hz => by
    obtain ⟨_, _, hθ1, hθ2, _⟩ := hspec hz
    have hcos : HasDerivAt (fun t => Real.cos (θ t)) (c1 z) z := by
      simpa [c1, mul_comm, Function.comp_def] using (Real.hasDerivAt_cos (θ z)).comp z hθ1
    have hsin : HasDerivAt (fun t => Real.sin (θ t)) (s1 z) z := by
      simpa [s1, mul_comm, Function.comp_def] using (Real.hasDerivAt_sin (θ z)).comp z hθ1
    exact ⟨hcos, (hsin.neg.mul hθ2).congr_deriv (by dsimp [c2]; ring),
      hsin, (hcos.mul hθ2).congr_deriv (by dsimp [s2]; ring)⟩
  refine ⟨U1, U2, V1, V2, fun {z} hz => ?_⟩
  obtain ⟨hW1, hW2, _, _, hW1b, hW2b, hθ1b, hθ2b⟩ := hspec hz
  obtain ⟨hc1, hc2, hs1, hs2⟩ := hc_hd hz
  have hW_mem := lowerWeps_mem_Icc hε0 (xOfZeta_spec hc0 hz).1
  have hW_abs : |W1 z| ≤ 1 := abs_le.mpr ⟨by linarith [hW_mem.1], hW_mem.2⟩
  have hsq_bd : (z⁻¹ + c'⁻¹) ^ 2 ≤ 2 * (z ^ (-2 : ℝ) + c' ^ (-2 : ℝ)) := by
    have ha : (z⁻¹) ^ 2 = z ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hz.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]
    have hb : (c'⁻¹) ^ 2 = c' ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hc0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]
    nlinarith [sq_nonneg (z⁻¹ - c'⁻¹), ha, hb]
  have hcs1 : |c1 z| ≤ C_osc * (z⁻¹ + c'⁻¹) ∧ |s1 z| ≤ C_osc * (z⁻¹ + c'⁻¹) := by
    refine ⟨?_, ?_⟩
    · calc |c1 z| = |Real.sin (θ z)| * |θ' z| := by dsimp [c1]; rw [abs_mul, abs_neg]
        _ ≤ 1 * |θ' z| := by gcongr; exact Real.abs_sin_le_one _
        _ ≤ C_osc * (z⁻¹ + c'⁻¹) := by linarith only [hθ1b]
    · calc |s1 z| = |Real.cos (θ z)| * |θ' z| := by dsimp [s1]; rw [abs_mul]
        _ ≤ 1 * |θ' z| := by gcongr; exact Real.abs_cos_le_one _
        _ ≤ C_osc * (z⁻¹ + c'⁻¹) := by linarith only [hθ1b]
  have hcs2 : |c2 z| ≤ (2 * C_osc ^ 2 + C_osc) * (z ^ (-2 : ℝ) + c' ^ (-2 : ℝ)) ∧
      |s2 z| ≤ (2 * C_osc ^ 2 + C_osc) * (z ^ (-2 : ℝ) + c' ^ (-2 : ℝ)) := by
    have hθsq : |θ' z| ^ 2 ≤ 2 * C_osc ^ 2 * (z ^ (-2 : ℝ) + c' ^ (-2 : ℝ)) := by
      calc |θ' z| ^ 2 ≤ (C_osc * (z⁻¹ + c'⁻¹)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hθ1b 2
        _ = C_osc ^ 2 * (z⁻¹ + c'⁻¹) ^ 2 := by ring
        _ ≤ 2 * C_osc ^ 2 * (z ^ (-2 : ℝ) + c' ^ (-2 : ℝ)) := by
            have := mul_le_mul_of_nonneg_left hsq_bd (sq_nonneg C_osc); linarith
    have htri : ∀ x1 x2 : ℝ, |x1| ≤ 1 → |x2| ≤ 1 →
        |x1 * θ' z ^ 2 + x2 * θ'' z| ≤ (2 * C_osc ^ 2 + C_osc) * (z ^ (-2 : ℝ) + c' ^ (-2 : ℝ)) := by
      intro x1 x2 hx1 hx2
      calc |x1 * θ' z ^ 2 + x2 * θ'' z|
          ≤ |x1| * |θ' z| ^ 2 + |x2| * |θ'' z| := by
            have := abs_add_le (x1 * θ' z ^ 2) (x2 * θ'' z)
            rwa [abs_mul, abs_mul, abs_pow] at this
        _ ≤ 1 * (2 * C_osc ^ 2 * (z ^ (-2 : ℝ) + c' ^ (-2 : ℝ))) +
              1 * (C_osc * (z ^ (-2 : ℝ) + c' ^ (-2 : ℝ))) := by gcongr
        _ = (2 * C_osc ^ 2 + C_osc) * (z ^ (-2 : ℝ) + c' ^ (-2 : ℝ)) := by ring
    have h1 := htri (-Real.cos (θ z)) (-Real.sin (θ z)) (by simpa using Real.abs_cos_le_one _)
      (by simpa using Real.abs_sin_le_one _)
    have h2 := htri (-Real.sin (θ z)) (Real.cos (θ z)) (by simpa using Real.abs_sin_le_one _)
      (Real.abs_cos_le_one _)
    have hc2_eq : (-Real.cos (θ z)) * θ' z ^ 2 + (-Real.sin (θ z)) * θ'' z = c2 z := by
      dsimp [c2]; ring
    have hs2_eq : (-Real.sin (θ z)) * θ' z ^ 2 + Real.cos (θ z) * θ'' z = s2 z := rfl
    exact ⟨hc2_eq ▸ h1, hs2_eq ▸ h2⟩
  have h2_prod : ∀ r : ℝ, |r| ≤ C_osc * (z⁻¹ + c'⁻¹) →
      2 * |W1' z| * |r| ≤ 4 * C_osc ^ 2 * (z ^ (-2 : ℝ) + c' ^ (-2 : ℝ)) := fun r hr => by
    have h1 := mul_le_mul_of_nonneg_left hr (abs_nonneg (W1' z))
    have h2 : |W1' z| * (C_osc * (z⁻¹ + c'⁻¹)) ≤ 2 * C_osc ^ 2 * (z ^ (-2 : ℝ) + c' ^ (-2 : ℝ)) := by
      calc |W1' z| * (C_osc * (z⁻¹ + c'⁻¹))
          ≤ (C_osc * (z⁻¹ + c'⁻¹)) * (C_osc * (z⁻¹ + c'⁻¹)) := by gcongr
        _ = C_osc ^ 2 * (z⁻¹ + c'⁻¹) ^ 2 := by ring
        _ ≤ 2 * C_osc ^ 2 * (z ^ (-2 : ℝ) + c' ^ (-2 : ℝ)) := by
            have := mul_le_mul_of_nonneg_left hsq_bd (sq_nonneg C_osc); linarith
    linarith only [h1, h2]
  have htri2 : ∀ (w2 w1f : ℝ) (cs : ℝ), |cs| ≤ 1 → |w2| ≤ C_osc * (z ^ (-2 : ℝ) + c' ^ (-2 : ℝ)) →
      2 * |W1' z| * |w1f| ≤ 4 * C_osc ^ 2 * (z ^ (-2 : ℝ) + c' ^ (-2 : ℝ)) →
      ∀ c2s : ℝ, |c2s| ≤ (2 * C_osc ^ 2 + C_osc) * (z ^ (-2 : ℝ) + c' ^ (-2 : ℝ)) →
      |w2 * cs + 2 * W1' z * w1f + W1 z * c2s| ≤ C_trig * (z ^ (-2 : ℝ) + c' ^ (-2 : ℝ)) := by
    intro w2 w1f cs hcs hw2 hmw c2s hc2s
    have htri : |w2 * cs + 2 * W1' z * w1f + W1 z * c2s| ≤
        |w2| * |cs| + 2 * |W1' z| * |w1f| + |W1 z| * |c2s| := by
      have ha := abs_add_le (w2 * cs + 2 * W1' z * w1f) (W1 z * c2s)
      have hb := abs_add_le (w2 * cs) (2 * W1' z * w1f)
      rw [abs_mul] at ha
      rw [abs_mul, abs_mul, abs_mul, abs_two] at hb
      linarith only [ha, hb]
    have hpow_nn : 0 ≤ z ^ (-2 : ℝ) + c' ^ (-2 : ℝ) := by positivity
    have h1 := mul_le_mul hw2 hcs (abs_nonneg _) (by positivity)
    have h3 := mul_le_mul hW_abs hc2s (abs_nonneg _) zero_le_one
    have hCtrig : 2 * C_osc + 6 * C_osc ^ 2 ≤ C_trig := by dsimp [C_trig]; linarith
    have hsum : (2 * C_osc + 6 * C_osc ^ 2) * (z ^ (-2 : ℝ) + c' ^ (-2 : ℝ)) ≤
        C_trig * (z ^ (-2 : ℝ) + c' ^ (-2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hCtrig hpow_nn
    linarith only [htri, h1, hmw, h3, hsum]
  refine ⟨hW1.mul hc1, ((hW2.mul hc1).add (hW1.mul hc2)).congr_deriv (by dsimp [U2]; ring),
    hW1.mul hs1, ((hW2.mul hs1).add (hW1.mul hs2)).congr_deriv (by dsimp [V2]; ring), ?_, ?_, ?_, ?_⟩
  · calc |U1 z| ≤ |W1' z| * |Real.cos (θ z)| + |W1 z| * |c1 z| := by
          dsimp [U1]; exact (abs_add_le _ _).trans (by rw [abs_mul, abs_mul])
      _ ≤ (C_osc * (z⁻¹ + c'⁻¹)) * 1 + 1 * (C_osc * (z⁻¹ + c'⁻¹)) := by
          have := Real.abs_cos_le_one (θ z); have := hcs1.1; gcongr
      _ = 2 * C_osc * (z⁻¹ + c'⁻¹) := by ring
      _ ≤ C_trig * (z⁻¹ + c'⁻¹) := by
          have hCtrig : 2 * C_osc ≤ C_trig := by dsimp [C_trig]; linarith only [sq_nonneg C_osc]
          have hpos : 0 ≤ z⁻¹ + c'⁻¹ := by positivity
          exact mul_le_mul_of_nonneg_right hCtrig hpos
  · exact htri2 _ _ _ (Real.abs_cos_le_one _) hW2b (h2_prod _ hcs1.1) _ hcs2.1
  · calc |V1 z| ≤ |W1' z| * |Real.sin (θ z)| + |W1 z| * |s1 z| := by
          dsimp [V1]; exact (abs_add_le _ _).trans (by rw [abs_mul, abs_mul])
      _ ≤ (C_osc * (z⁻¹ + c'⁻¹)) * 1 + 1 * (C_osc * (z⁻¹ + c'⁻¹)) := by
          have := Real.abs_sin_le_one (θ z); have := hcs1.2; gcongr
      _ = 2 * C_osc * (z⁻¹ + c'⁻¹) := by ring
      _ ≤ C_trig * (z⁻¹ + c'⁻¹) := by
          have hCtrig : 2 * C_osc ≤ C_trig := by dsimp [C_trig]; linarith only [sq_nonneg C_osc]
          have hpos : 0 ≤ z⁻¹ + c'⁻¹ := by positivity
          exact mul_le_mul_of_nonneg_right hCtrig hpos
  · exact htri2 _ _ _ (Real.abs_sin_le_one _) hW2b (h2_prod _ hcs1.2) _ hcs2.2

/-! ### 4. Local frozen-window error and global Fubini estimate (`ctl:freeze`) -/

private lemma lowerPζ_z_inv_bounds {c' z : ℝ} (hc1 : 1 ≤ c') (hz : zetaMin c' / 2 ≤ z) :
    z⁻¹ ≤ (3 * π) * c' ^ (-(6 / 7 : ℝ)) ∧
    z⁻¹ + c'⁻¹ ≤ (3 * π + 1) * c' ^ (-(6 / 7 : ℝ)) ∧
    z ^ (-2 : ℝ) ≤ 9 * π ^ 2 * c' ^ (-(12 / 7 : ℝ)) ∧
    z ^ (-2 : ℝ) + c' ^ (-2 : ℝ) ≤ (9 * π ^ 2 + 1) * c' ^ (-(12 / 7 : ℝ)) := by
  have hc0 : 0 < c' := by linarith
  have hpi := Real.pi_pos
  have ha_pos : 0 < zetaMin c' / 2 := by have := zetaMin_pos hc0; positivity
  have ha_eq : zetaMin c' / 2 = (1 / (3 * π)) * c' ^ (6 / 7 : ℝ) := by
    unfold zetaMin; ring
  have hz_inv : z⁻¹ ≤ (3 * π) * c' ^ (-(6 / 7 : ℝ)) := by
    calc z⁻¹ ≤ (zetaMin c' / 2)⁻¹ := inv_anti₀ ha_pos hz
      _ = (3 * π) * c' ^ (-(6 / 7 : ℝ)) := by
          rw [ha_eq, mul_inv, one_div, inv_inv, Real.rpow_neg hc0.le]
  have hc_inv : c'⁻¹ ≤ c' ^ (-(6 / 7 : ℝ)) := by
    rw [← Real.rpow_neg_one c']
    exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hz_m2 : z ^ (-2 : ℝ) ≤ 9 * π ^ 2 * c' ^ (-(12 / 7 : ℝ)) := by
    have hz_pos : 0 < z := ha_pos.trans_le hz
    rw [Real.rpow_neg hz_pos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← inv_pow]
    calc (z⁻¹) ^ 2 ≤ ((3 * π) * c' ^ (-(6 / 7 : ℝ))) ^ 2 := pow_le_pow_left₀ (inv_nonneg.mpr hz_pos.le) hz_inv 2
      _ = 9 * π ^ 2 * (c' ^ (-(6 / 7 : ℝ))) ^ 2 := by ring
      _ = 9 * π ^ 2 * c' ^ (-(12 / 7 : ℝ)) := by
          rw [← Real.rpow_natCast (c' ^ (-(6 / 7 : ℝ))) 2, ← Real.rpow_mul hc0.le]; norm_num
  have hc_m2 : c' ^ (-2 : ℝ) ≤ c' ^ (-(12 / 7 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  exact ⟨hz_inv, by linarith only [hz_inv, hc_inv], hz_m2, by linarith only [hz_m2, hc_m2]⟩

lemma boasA_local_error {c' R C_P C_trig : ℝ} (hc10000 : 10000 ≤ c')
    (hCP : 0 < C_P) (hCtrig : 0 < C_trig)
    (hsmall : (8 * Real.log c' + 1) ≤ zetaMin c' / 2)
    (hpows : 8 * Real.sqrt 2 * Real.log c' * c' ^ (-(12 / 7 : ℝ)) ≤ c' ^ (-1 : ℝ) ∧
      2 * c' ^ (-8 : ℝ) ≤ c' ^ (-1 : ℝ))
    (hP_spec : ∃ P1 P2 : ℝ → ℝ, ContinuousOn P1 (Ici (zetaMin c' / 2)) ∧
      (∀ {ζ : ℝ}, zetaMin c' / 2 ≤ ζ → 0 < lowerPζ c' R ζ ∧ HasDerivAt (lowerPζ c' R) (P1 ζ) ζ ∧
        |P1 ζ| ≤ C_P * lowerPζ c' R ζ / ζ ∧ (ζ ≠ zetaR c' R → HasDerivAt P1 (P2 ζ) ζ) ∧
        |P2 ζ| ≤ C_P * lowerPζ c' R ζ / ζ ^ 2) ∧
      (∀ {ζ₁ ζ₂ : ℝ}, zetaMin c' / 2 ≤ ζ₁ → zetaMin c' / 2 ≤ ζ₂ → |ζ₁ - ζ₂| ≤ 8 * Real.log c' + 1 →
        lowerPζ c' R ζ₁ ≤ 2 * lowerPζ c' R ζ₂))
    (hT_spec : let W1 := fun z => lowerWeps (c' ^ (-2 : ℝ)) (lowerY (xOfZeta c' z))
      let θ := fun z => unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' z)
      ∃ U1 U2 V1 V2 : ℝ → ℝ, ∀ {z : ℝ}, 0 < z →
        HasDerivAt (fun t => W1 t * Real.cos (θ t)) (U1 z) z ∧ HasDerivAt U1 (U2 z) z ∧
        HasDerivAt (fun t => W1 t * Real.sin (θ t)) (V1 z) z ∧ HasDerivAt V1 (V2 z) z ∧
        |U1 z| ≤ C_trig * (z⁻¹ + c'⁻¹) ∧ |U2 z| ≤ C_trig * (z ^ (-2 : ℝ) + c' ^ (-2 : ℝ)) ∧
        |V1 z| ≤ C_trig * (z⁻¹ + c'⁻¹) ∧ |V2 z| ≤ C_trig * (z ^ (-2 : ℝ) + c' ^ (-2 : ℝ))) :
    let K_loc : ℝ := 10 * (9 * π ^ 2 * C_P + 2 * (3 * π) * C_P * C_trig * (3 * π + 1) +
        C_trig * (9 * π ^ 2 + 1) + 1) + 9
    ∀ {ζ : ℝ}, boasZetaStar c' + 8 * Real.log c' + 1 / 2 ≤ ζ →
      |(∫ z in {z : ℝ | boasZetaStar c' ≤ z ∧ z - goodL0 c' (boasPhi0 c') z < ζ ∧
            ζ ≤ z + goodL0 c' (boasPhi0 c') z},
          gaussW c' (z - ζ) * boasA c' R ζ z) - boasA c' R ζ ζ| ≤
        K_loc * lowerPζ c' R ζ * c' ^ (-1 : ℝ) := by
  intro K_loc ζ hζ
  have hc0 : 0 < c' := by linarith
  have hc1 : 1 < c' := by linarith
  have hl_pos : 0 < Real.log c' := Real.log_pos hc1
  set L : ℝ := 8 * Real.log c'
  have hL_pos : 0 < L := by positivity
  set φ₀ := boasPhi0 c'
  set L₀ := goodL0 c' φ₀
  set Iζ : Set ℝ := {z : ℝ | boasZetaStar c' ≤ z ∧ z - L₀ z < ζ ∧ ζ ≤ z + L₀ z}
  obtain ⟨P1, P2, hcont_P1, hP_pt, hP_cmp⟩ := hP_spec
  obtain ⟨U1, U2, V1, V2, hT_pt⟩ := hT_spec
  let a : ℝ := ζ - (L + 1 / 2)
  let b : ℝ := ζ + (L + 1 / 2)
  have ha_ge : zetaMin c' / 2 ≤ a := by
    unfold boasZetaStar at hζ
    have : L + 1 / 2 ≤ L + 1 := by linarith
    dsimp [a, L]; linarith [zetaMin_pos hc0]
  have hζ_ab : ζ ∈ Icc a b := ⟨by dsimp [a]; linarith, by dsimp [b]; linarith⟩
  have hζ_min : zetaMin c' / 2 ≤ ζ := ha_ge.trans hζ_ab.1
  have hPζ_pos : 0 < lowerPζ c' R ζ := (hP_pt hζ_min).1
  let W1 := fun z => lowerWeps (c' ^ (-2 : ℝ)) (lowerY (xOfZeta c' z))
  let θ := fun z => unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' z)
  let FU := fun z => lowerPζ c' R z * (W1 z * Real.cos (θ z))
  let FU1 := fun z => P1 z * (W1 z * Real.cos (θ z)) + lowerPζ c' R z * U1 z
  let FU2 := fun z => P2 z * (W1 z * Real.cos (θ z)) + 2 * P1 z * U1 z + lowerPζ c' R z * U2 z
  let FV := fun z => lowerPζ c' R z * (W1 z * Real.sin (θ z))
  let FV1 := fun z => P1 z * (W1 z * Real.sin (θ z)) + lowerPζ c' R z * V1 z
  let FV2 := fun z => P2 z * (W1 z * Real.sin (θ z)) + 2 * P1 z * V1 z + lowerPζ c' R z * V2 z
  have hU_c2 := c1_piecewise_c2_mul (a := zetaMin c' / 2) (c₀ := zetaR c' R) hcont_P1
    (fun {t} ht => (hP_pt ht).2.1) (fun {t} ht hne => (hP_pt ht).2.2.2.1 hne)
    (fun {t} ht => (hT_pt (lt_of_lt_of_le (div_pos (zetaMin_pos hc0) zero_lt_two) ht)).1)
    (fun {t} ht => (hT_pt (lt_of_lt_of_le (div_pos (zetaMin_pos hc0) zero_lt_two) ht)).2.1)
  have hV_c2 := c1_piecewise_c2_mul (a := zetaMin c' / 2) (c₀ := zetaR c' R) hcont_P1
    (fun {t} ht => (hP_pt ht).2.1) (fun {t} ht hne => (hP_pt ht).2.2.2.1 hne)
    (fun {t} ht => (hT_pt (lt_of_lt_of_le (div_pos (zetaMin_pos hc0) zero_lt_two) ht)).2.2.1)
    (fun {t} ht => (hT_pt (lt_of_lt_of_le (div_pos (zetaMin_pos hc0) zero_lt_two) ht)).2.2.2.1)
  let C2 : ℝ := 9 * π ^ 2 * C_P + 2 * (3 * π) * C_P * C_trig * (3 * π + 1) + C_trig * (9 * π ^ 2 + 1)
  have hC2_nn : 0 ≤ C2 := by have := Real.pi_pos; positivity
  let M2 : ℝ := 2 * C2 * lowerPζ c' R ζ * c' ^ (-(12 / 7 : ℝ))
  have hM2_nn : 0 ≤ M2 := by positivity
  have hbd_tab : ∀ {t : ℝ}, t ∈ Icc a b →
      |P2 t| ≤ C2 * lowerPζ c' R t * c' ^ (-(12 / 7 : ℝ)) ∧
      |FU2 t| ≤ C2 * lowerPζ c' R t * c' ^ (-(12 / 7 : ℝ)) ∧
      |FV2 t| ≤ C2 * lowerPζ c' R t * c' ^ (-(12 / 7 : ℝ)) ∧
      lowerPζ c' R t ≤ 2 * lowerPζ c' R ζ := by
    intro t ht
    have ht_ge : zetaMin c' / 2 ≤ t := ha_ge.trans ht.1
    have ht_pos : 0 < t := lt_of_lt_of_le (by have := zetaMin_pos hc0; positivity) ht_ge
    obtain ⟨_, hP_hd, hP1_bd, _, hP2_bd⟩ := hP_pt ht_ge
    obtain ⟨_, _, _, _, hU1_bd, hU2_bd, hV1_bd, hV2_bd⟩ := hT_pt ht_pos
    obtain ⟨hz1, hz1c, hzm2, hzm2c⟩ := lowerPζ_z_inv_bounds hc1.le ht_ge
    have ht_sq : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
      rw [Real.rpow_neg ht_pos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hP_pos := (hP_pt ht_ge).1
    have hP2_le : |P2 t| ≤ 9 * π ^ 2 * C_P * lowerPζ c' R t * c' ^ (-(12 / 7 : ℝ)) := by
      calc |P2 t| ≤ C_P * lowerPζ c' R t / t ^ 2 := hP2_bd
        _ = C_P * lowerPζ c' R t * t ^ (-2 : ℝ) := by rw [ht_sq, div_eq_mul_inv]
        _ ≤ C_P * lowerPζ c' R t * (9 * π ^ 2 * c' ^ (-(12 / 7 : ℝ))) := by gcongr
        _ = _ := by ring
    have hprod_le : ∀ (X1 X2 : ℝ) (c_cs : ℝ), |c_cs| ≤ 1 → |X1| ≤ C_trig * (t⁻¹ + c'⁻¹) →
        |X2| ≤ C_trig * (t ^ (-2 : ℝ) + c' ^ (-2 : ℝ)) →
        |P2 t * c_cs + 2 * P1 t * X1 + lowerPζ c' R t * X2| ≤
          C2 * lowerPζ c' R t * c' ^ (-(12 / 7 : ℝ)) := by
      intro X1 X2 c_cs hcs hX1 hX2
      have htri : |P2 t * c_cs + 2 * P1 t * X1 + lowerPζ c' R t * X2| ≤
          |P2 t| * |c_cs| + 2 * |P1 t| * |X1| + lowerPζ c' R t * |X2| := by
        have ha := abs_add_le (P2 t * c_cs + 2 * P1 t * X1) (lowerPζ c' R t * X2)
        have hb := abs_add_le (P2 t * c_cs) (2 * P1 t * X1)
        rw [abs_mul, abs_of_pos hP_pos] at ha
        rw [abs_mul, abs_mul, abs_mul, abs_two] at hb
        linarith only [ha, hb]
      have hmid : 2 * |P1 t| * |X1| ≤
          2 * (3 * π) * C_P * C_trig * (3 * π + 1) * lowerPζ c' R t * c' ^ (-(12 / 7 : ℝ)) := by
        have hP1' : |P1 t| ≤ 3 * π * C_P * lowerPζ c' R t * c' ^ (-(6 / 7 : ℝ)) := by
          calc |P1 t| ≤ C_P * lowerPζ c' R t / t := hP1_bd
            _ = C_P * lowerPζ c' R t * t⁻¹ := div_eq_mul_inv _ _
            _ ≤ C_P * lowerPζ c' R t * ((3 * π) * c' ^ (-(6 / 7 : ℝ))) := by gcongr
            _ = _ := by ring
        have hX1' : |X1| ≤ C_trig * (3 * π + 1) * c' ^ (-(6 / 7 : ℝ)) :=
          hX1.trans (by calc C_trig * (t⁻¹ + c'⁻¹) ≤ C_trig * ((3 * π + 1) * c' ^ (-(6 / 7 : ℝ))) := by gcongr
            _ = _ := by ring)
        have hpow : c' ^ (-(6 / 7 : ℝ)) * c' ^ (-(6 / 7 : ℝ)) = c' ^ (-(12 / 7 : ℝ)) := by
          rw [← Real.rpow_add hc0]; congr 1; norm_num
        calc 2 * |P1 t| * |X1|
            ≤ 2 * (3 * π * C_P * lowerPζ c' R t * c' ^ (-(6 / 7 : ℝ))) *
                (C_trig * (3 * π + 1) * c' ^ (-(6 / 7 : ℝ))) := by gcongr
          _ = 2 * (3 * π) * C_P * C_trig * (3 * π + 1) * lowerPζ c' R t *
                (c' ^ (-(6 / 7 : ℝ)) * c' ^ (-(6 / 7 : ℝ))) := by ring
          _ = _ := by rw [hpow]
      have hlast : lowerPζ c' R t * |X2| ≤
          C_trig * (9 * π ^ 2 + 1) * lowerPζ c' R t * c' ^ (-(12 / 7 : ℝ)) := by
        have hX2' : |X2| ≤ C_trig * (9 * π ^ 2 + 1) * c' ^ (-(12 / 7 : ℝ)) :=
          hX2.trans (by calc C_trig * (t ^ (-2 : ℝ) + c' ^ (-2 : ℝ))
              ≤ C_trig * ((9 * π ^ 2 + 1) * c' ^ (-(12 / 7 : ℝ))) := by gcongr
            _ = _ := by ring)
        calc lowerPζ c' R t * |X2| ≤ lowerPζ c' R t * (C_trig * (9 * π ^ 2 + 1) * c' ^ (-(12 / 7 : ℝ))) := by gcongr
          _ = _ := by ring
      have h1 : |P2 t| * |c_cs| ≤ 9 * π ^ 2 * C_P * lowerPζ c' R t * c' ^ (-(12 / 7 : ℝ)) := by
        calc |P2 t| * |c_cs| ≤ |P2 t| * 1 := by gcongr
          _ = |P2 t| := mul_one _
          _ ≤ _ := hP2_le
      dsimp [C2]
      linarith only [htri, h1, hmid, hlast]
    have hdist : |t - ζ| ≤ 8 * Real.log c' + 1 := by
      have ht' := ht
      dsimp [a, b, L] at ht'
      rw [abs_le]; constructor <;> linarith only [ht'.1, ht'.2]
    have hW_mem := lowerWeps_mem_Icc (Real.rpow_nonneg hc0.le (-2)) (xOfZeta_spec hc0 ht_pos).1
    have hW_abs : |W1 t| ≤ 1 := abs_le.mpr ⟨by linarith only [hW_mem.1], hW_mem.2⟩
    have hWcos : |W1 t * Real.cos (θ t)| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul hW_abs (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
    have hWsin : |W1 t * Real.sin (θ t)| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul hW_abs (Real.abs_sin_le_one _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
    have hC2_1 : 9 * π ^ 2 * C_P ≤ C2 := by
      dsimp [C2]
      have hrest : 0 ≤ 2 * (3 * π) * C_P * C_trig * (3 * π + 1) + C_trig * (9 * π ^ 2 + 1) := by
        have := Real.pi_pos; positivity
      linarith only [hrest]
    refine ⟨hP2_le.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC2_1 hP_pos.le) (Real.rpow_nonneg hc0.le _)),
      hprod_le (U1 t) (U2 t) (W1 t * Real.cos (θ t)) hWcos hU1_bd hU2_bd,
      hprod_le (V1 t) (V2 t) (W1 t * Real.sin (θ t)) hWsin hV1_bd hV2_bd,
      hP_cmp ht_ge hζ_min hdist⟩
  have hP_tay : ∀ {z : ℝ}, z ∈ Icc a b → |lowerPζ c' R z - lowerPζ c' R ζ - P1 ζ * (z - ζ)| ≤ M2 * (z - ζ) ^ 2 :=
    fun {z} hz => taylor2_of_c1_piecewise_c2 (hcont_P1.mono fun t ht => ha_ge.trans ht.1)
      (fun {t} ht1 ht2 => (hP_pt (ha_ge.trans ht1)).2.1)
      (fun {t} ht1 ht2 hne => (hP_pt (ha_ge.trans ht1)).2.2.2.1 hne)
      (fun {t} ht1 ht2 => by
        obtain ⟨h0, _, _, hcmp⟩ := hbd_tab ⟨ht1, ht2⟩
        calc |P2 t| ≤ C2 * lowerPζ c' R t * c' ^ (-(12 / 7 : ℝ)) := h0
          _ ≤ C2 * (2 * lowerPζ c' R ζ) * c' ^ (-(12 / 7 : ℝ)) := by gcongr
          _ = M2 := by dsimp [M2]; ring)
      hM2_nn hζ_ab hz
  have hFU_tay : ∀ {z : ℝ}, z ∈ Icc a b → |FU z - FU ζ - FU1 ζ * (z - ζ)| ≤ M2 * (z - ζ) ^ 2 :=
    fun {z} hz => taylor2_of_c1_piecewise_c2 (hU_c2.1.mono fun t ht => ha_ge.trans ht.1)
      (fun {t} ht1 ht2 => hU_c2.2.1 (ha_ge.trans ht1))
      (fun {t} ht1 ht2 hne => hU_c2.2.2 (ha_ge.trans ht1) hne)
      (fun {t} ht1 ht2 => by
        obtain ⟨_, h1, _, hcmp⟩ := hbd_tab ⟨ht1, ht2⟩
        calc |FU2 t| ≤ C2 * lowerPζ c' R t * c' ^ (-(12 / 7 : ℝ)) := h1
          _ ≤ C2 * (2 * lowerPζ c' R ζ) * c' ^ (-(12 / 7 : ℝ)) := by gcongr
          _ = M2 := by dsimp [M2]; ring)
      hM2_nn hζ_ab hz
  have hFV_tay : ∀ {z : ℝ}, z ∈ Icc a b → |FV z - FV ζ - FV1 ζ * (z - ζ)| ≤ M2 * (z - ζ) ^ 2 :=
    fun {z} hz => taylor2_of_c1_piecewise_c2 (hV_c2.1.mono fun t ht => ha_ge.trans ht.1)
      (fun {t} ht1 ht2 => hV_c2.2.1 (ha_ge.trans ht1))
      (fun {t} ht1 ht2 hne => hV_c2.2.2 (ha_ge.trans ht1) hne)
      (fun {t} ht1 ht2 => by
        obtain ⟨_, _, h2, hcmp⟩ := hbd_tab ⟨ht1, ht2⟩
        calc |FV2 t| ≤ C2 * lowerPζ c' R t * c' ^ (-(12 / 7 : ℝ)) := h2
          _ ≤ C2 * (2 * lowerPζ c' R ζ) * c' ^ (-(12 / 7 : ℝ)) := by gcongr
          _ = M2 := by dsimp [M2]; ring)
      hM2_nn hζ_ab hz
  set A1 : ℝ := P1 ζ - 2 * FU1 ζ * Real.sin (2 * π * ζ) + 2 * FV1 ζ * Real.cos (2 * π * ζ)
  have hA_tay : ∀ {z : ℝ}, z ∈ Icc a b → |boasA c' R ζ z - (boasA c' R ζ ζ + A1 * (z - ζ))| ≤
      5 * M2 * (z - ζ) ^ 2 := fun {z} hz => by
    have hsplit : ∀ t : ℝ, boasA c' R ζ t =
        lowerPζ c' R t - 2 * FU t * Real.sin (2 * π * ζ) + 2 * FV t * Real.cos (2 * π * ζ) := fun t => by
      unfold boasA; dsimp [FU, FV, W1, θ]
      rw [Real.sin_sub]
      ring
    have heq : boasA c' R ζ z - (boasA c' R ζ ζ + A1 * (z - ζ)) =
        (lowerPζ c' R z - lowerPζ c' R ζ - P1 ζ * (z - ζ)) -
          2 * Real.sin (2 * π * ζ) * (FU z - FU ζ - FU1 ζ * (z - ζ)) +
          2 * Real.cos (2 * π * ζ) * (FV z - FV ζ - FV1 ζ * (z - ζ)) := by
      rw [hsplit z, hsplit ζ]; dsimp [A1]; ring
    rw [heq]
    have htri : |(lowerPζ c' R z - lowerPζ c' R ζ - P1 ζ * (z - ζ)) -
          2 * Real.sin (2 * π * ζ) * (FU z - FU ζ - FU1 ζ * (z - ζ)) +
          2 * Real.cos (2 * π * ζ) * (FV z - FV ζ - FV1 ζ * (z - ζ))| ≤
        |lowerPζ c' R z - lowerPζ c' R ζ - P1 ζ * (z - ζ)| +
          2 * |Real.sin (2 * π * ζ)| * |FU z - FU ζ - FU1 ζ * (z - ζ)| +
          2 * |Real.cos (2 * π * ζ)| * |FV z - FV ζ - FV1 ζ * (z - ζ)| := by
      have ha := abs_add_le
        ((lowerPζ c' R z - lowerPζ c' R ζ - P1 ζ * (z - ζ)) -
          2 * Real.sin (2 * π * ζ) * (FU z - FU ζ - FU1 ζ * (z - ζ)))
        (2 * Real.cos (2 * π * ζ) * (FV z - FV ζ - FV1 ζ * (z - ζ)))
      have hb := abs_sub (lowerPζ c' R z - lowerPζ c' R ζ - P1 ζ * (z - ζ))
        (2 * Real.sin (2 * π * ζ) * (FU z - FU ζ - FU1 ζ * (z - ζ)))
      rw [abs_mul, abs_mul, abs_two] at ha
      rw [abs_mul, abs_mul, abs_two] at hb
      linarith only [ha, hb]
    have h1 := hP_tay hz
    have h2 := hFU_tay hz
    have h3 := hFV_tay hz
    have hs := Real.abs_sin_le_one (2 * π * ζ)
    have hc := Real.abs_cos_le_one (2 * π * ζ)
    have h2' : |Real.sin (2 * π * ζ)| * |FU z - FU ζ - FU1 ζ * (z - ζ)| ≤ M2 * (z - ζ) ^ 2 := by
      calc |Real.sin (2 * π * ζ)| * |FU z - FU ζ - FU1 ζ * (z - ζ)|
          ≤ 1 * (M2 * (z - ζ) ^ 2) := mul_le_mul hs h2 (abs_nonneg _) zero_le_one
        _ = M2 * (z - ζ) ^ 2 := one_mul _
    have h3' : |Real.cos (2 * π * ζ)| * |FV z - FV ζ - FV1 ζ * (z - ζ)| ≤ M2 * (z - ζ) ^ 2 := by
      calc |Real.cos (2 * π * ζ)| * |FV z - FV ζ - FV1 ζ * (z - ζ)|
          ≤ 1 * (M2 * (z - ζ) ^ 2) := mul_le_mul hc h3 (abs_nonneg _) zero_le_one
        _ = M2 * (z - ζ) ^ 2 := one_mul _
    linarith only [htri, h1, h2', h3']
  -- Split `Iζ` into `Ioo (ζ - L) (ζ + L)` and `Iζ \ Ioo (ζ - L) (ζ + L)`
  have hsub_core : Ioo (ζ - L) (ζ + L) ⊆ Iζ := by
    intro z hz
    have hL0 := goodL0_bounds_and_poles c' φ₀ z
    refine ⟨?_, ?_, ?_⟩
    · have : ζ - L ≥ boasZetaStar c' + 1 / 2 := by linarith only [hζ]
      linarith only [hz.1, this]
    · dsimp [L₀]; linarith only [hz.2, hL0.1]
    · dsimp [L₀]; linarith only [hz.1, hL0.1]
  have hIζ_meas : MeasurableSet Iζ := by
    have hL0m : Measurable L₀ := measurable_goodL0 c' (measurable_boasPhi0 hc10000)
    have h1 : MeasurableSet {z : ℝ | boasZetaStar c' ≤ z} := measurableSet_Ici
    have h2 : MeasurableSet {z : ℝ | z - L₀ z < ζ} :=
      measurableSet_lt (measurable_id.sub hL0m) measurable_const
    have h3 : MeasurableSet {z : ℝ | ζ ≤ z + L₀ z} :=
      measurableSet_le measurable_const (measurable_id.add hL0m)
    exact h1.inter (h2.inter h3)
  have hIζ_bd : ∀ z ∈ Iζ, |boasA c' R ζ z| ≤ 6 * lowerPζ c' R ζ := by
    intro z hz
    have hz_ge : zetaMin c' / 2 ≤ z := by
      have hz1 : boasZetaStar c' ≤ z := hz.1
      unfold boasZetaStar at hz1
      exact (half_le_self (zetaMin_pos hc0).le).trans (by linarith only [hz1, hl_pos])
    have hz_pos : 0 < z := lt_of_lt_of_le (by have := zetaMin_pos hc0; positivity) hz_ge
    have hL0 := goodL0_bounds_and_poles c' φ₀ z
    have hdist : |z - ζ| ≤ L + 1 := by
      rw [abs_le]
      have hz21 : z - L₀ z < ζ := hz.2.1
      have hz22 : ζ ≤ z + L₀ z := hz.2.2
      constructor <;> linarith only [hz21, hz22, hL0.2.1]
    have hP_pos := (hP_pt hz_ge).1
    have hA := abs_boasA_le (ζ := ζ) hc0 hz_pos hP_pos.le
    have hcmp := hP_cmp hz_ge hζ_min hdist
    linarith only [hA, hcmp]
  have hg_shift_int : Integrable (fun z => gaussW c' (z - ζ)) :=
    (integrable_gaussW hc1).comp_sub_right ζ
  have hboasA_cont : ContinuousOn (fun z => boasA c' R ζ z) (Ici (zetaMin c' / 2)) := by
    have hP_cont : ContinuousOn (lowerPζ c' R) (Ici (zetaMin c' / 2)) :=
      fun z hz => (hP_pt hz).2.1.continuousAt.continuousWithinAt
    have hU_cont : ContinuousOn (fun z => W1 z * Real.cos (θ z)) (Ici (zetaMin c' / 2)) := fun z hz =>
      (hT_pt (lt_of_lt_of_le (by have := zetaMin_pos hc0; positivity) hz)).1.continuousAt.continuousWithinAt
    have hV_cont : ContinuousOn (fun z => W1 z * Real.sin (θ z)) (Ici (zetaMin c' / 2)) := fun z hz =>
      (hT_pt (lt_of_lt_of_le (by have := zetaMin_pos hc0; positivity) hz)).2.2.1.continuousAt.continuousWithinAt
    have heq : (fun z => boasA c' R ζ z) = fun z =>
        lowerPζ c' R z - 2 * (lowerPζ c' R z * (W1 z * Real.cos (θ z))) * Real.sin (2 * π * ζ) +
          2 * (lowerPζ c' R z * (W1 z * Real.sin (θ z))) * Real.cos (2 * π * ζ) := by
      ext z; unfold boasA; dsimp [W1, θ]; rw [Real.sin_sub]; ring
    rw [heq]
    exact (hP_cont.sub (((hP_cont.mul hU_cont).const_mul 2).mul continuousOn_const)).add
      (((hP_cont.mul hV_cont).const_mul 2).mul continuousOn_const)
  have hg_cont : Continuous (fun z => gaussW c' (z - ζ)) := by unfold gaussW; fun_prop
  have hIζ_sub_min : Iζ ⊆ Ici (zetaMin c' / 2) := fun z hz => by
    have hz1 : boasZetaStar c' ≤ z := hz.1
    unfold boasZetaStar at hz1
    exact (half_le_self (zetaMin_pos hc0).le).trans (by linarith only [hz1, hl_pos])
  have hG_cont : ContinuousOn (fun z => gaussW c' (z - ζ) * boasA c' R ζ z) (Ici (zetaMin c' / 2)) :=
    hg_cont.continuousOn.mul hboasA_cont
  have hIζ_int : IntegrableOn (fun z => gaussW c' (z - ζ) * boasA c' R ζ z) Iζ := by
    refine ((hg_shift_int.const_mul (6 * lowerPζ c' R ζ)).integrableOn).mono'
      (hG_cont.mono hIζ_sub_min |>.aestronglyMeasurable hIζ_meas) ?_
    filter_upwards [ae_restrict_mem hIζ_meas] with z hz
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussW_nonneg _ _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hIζ_bd z hz) (gaussW_nonneg _ _)
  have hIoo_sub : Ioo (ζ - L) (ζ + L) ⊆ Ici (zetaMin c' / 2) := hsub_core.trans hIζ_sub_min
  have hIoo_int : IntegrableOn (fun z => gaussW c' (z - ζ) * boasA c' R ζ z) (Ioo (ζ - L) (ζ + L)) :=
    hIζ_int.mono_set hsub_core
  have hdiff_int : IntegrableOn (fun z => gaussW c' (z - ζ) * boasA c' R ζ z)
      (Iζ \ Ioo (ζ - L) (ζ + L)) :=
    hIζ_int.mono_set sdiff_subset
  have hunion_eq : Iζ = Ioo (ζ - L) (ζ + L) ∪ (Iζ \ Ioo (ζ - L) (ζ + L)) :=
    (union_sdiff_cancel hsub_core).symm
  have hsplit_int :
      ∫ z in Iζ, gaussW c' (z - ζ) * boasA c' R ζ z =
        (∫ z in Ioo (ζ - L) (ζ + L), gaussW c' (z - ζ) * boasA c' R ζ z) +
          ∫ z in Iζ \ Ioo (ζ - L) (ζ + L), gaussW c' (z - ζ) * boasA c' R ζ z := by
    nth_rewrite 1 [hunion_eq]
    exact setIntegral_union disjoint_sdiff_self_right (hIζ_meas.diff measurableSet_Ioo) hIoo_int hdiff_int
  -- Core integral over `(-L)..L`
  have hcore_eq :
      ∫ z in Ioo (ζ - L) (ζ + L), gaussW c' (z - ζ) * boasA c' R ζ z =
        ∫ q in (-L)..L, gaussW c' q * boasA c' R ζ (q + ζ) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith only [hL_pos])]
    have hsh := intervalIntegral.integral_comp_add_right
      (f := fun z => gaussW c' (z - ζ) * boasA c' R ζ z) ζ (a := -L) (b := L)
    rw [show -L + ζ = ζ - L by ring, show L + ζ = ζ + L by ring] at hsh
    rw [← hsh]
    refine intervalIntegral.integral_congr fun q _ => ?_
    simp [add_sub_cancel_right]
  have hq2_int : Integrable (fun q => q ^ 2 * gaussW c' q) := by
    let W2 := 2 * Real.log c'
    have hW2 : 0 < W2 := by positivity
    let dom := fun q : ℝ => (4 * W2) * (Real.exp (-(4 * W2)⁻¹ * q ^ 2) /
      (Real.sqrt (2 * π) * Real.sqrt W2))
    have hdom_int : Integrable dom :=
      (((integrable_exp_neg_mul_sq (by positivity : 0 < (4 * W2)⁻¹)).div_const _).const_mul (4 * W2)).congr
        (Eventually.of_forall fun _ => rfl)
    refine hdom_int.mono (by unfold gaussW; fun_prop : Continuous fun q => q ^ 2 * gaussW c' q).aestronglyMeasurable
      (Eventually.of_forall fun q => ?_)
    have h1 := Real.add_one_le_exp (q ^ 2 / (4 * W2))
    have hex1 : q ^ 2 / (4 * W2) * Real.exp (-(q ^ 2 / (4 * W2))) ≤ 1 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]; linarith
    have hex2 : Real.exp (-q ^ 2 / (2 * W2)) =
        Real.exp (-(q ^ 2 / (4 * W2))) * Real.exp (-(4 * W2)⁻¹ * q ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have hq2_le : q ^ 2 * Real.exp (-q ^ 2 / (2 * W2)) ≤
        4 * W2 * Real.exp (-(4 * W2)⁻¹ * q ^ 2) := by
      rw [hex2, ← mul_assoc]
      calc q ^ 2 * Real.exp (-(q ^ 2 / (4 * W2))) * Real.exp (-(4 * W2)⁻¹ * q ^ 2)
          = (4 * W2) * (q ^ 2 / (4 * W2) * Real.exp (-(q ^ 2 / (4 * W2)))) *
              Real.exp (-(4 * W2)⁻¹ * q ^ 2) := by field_simp [hW2.ne']
        _ ≤ (4 * W2) * 1 * Real.exp (-(4 * W2)⁻¹ * q ^ 2) := by gcongr
        _ = 4 * W2 * Real.exp (-(4 * W2)⁻¹ * q ^ 2) := by ring
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (gaussW_nonneg _ _)),
      Real.norm_of_nonneg (by dsimp [dom]; positivity)]
    unfold gaussW; dsimp [dom, W2]
    rw [mul_div_assoc', mul_div_assoc']
    exact div_le_div_of_nonneg_right hq2_le (by positivity)
  have hcore_err :
      |(∫ q in (-L)..L, gaussW c' q * boasA c' R ζ (q + ζ)) - boasA c' R ζ ζ| ≤
        5 * M2 * (8 * Real.sqrt 2 * Real.log c') + 6 * lowerPζ c' R ζ * c' ^ (-8 : ℝ) := by
    have hA_cont : ContinuousOn (fun q => gaussW c' q * boasA c' R ζ (q + ζ)) (Icc (-L) L) := by
      have hg0 : Continuous (gaussW c') := by unfold gaussW; fun_prop
      have hcomp : ContinuousOn (fun q => boasA c' R ζ (q + ζ)) (Icc (-L) L) :=
        hboasA_cont.comp (continuous_id.add continuous_const).continuousOn fun q hq => by
          have : a ≤ q + ζ := by dsimp [a]; linarith only [hq.1]
          exact ha_ge.trans this
      exact hg0.continuousOn.mul hcomp
    have hA_int : IntervalIntegrable (fun q => gaussW c' q * boasA c' R ζ (q + ζ)) volume (-L) L :=
      ContinuousOn.intervalIntegrable (by rwa [uIcc_of_le (by linarith only [hL_pos])])
    have hlin_cont : Continuous (fun q => gaussW c' q * (boasA c' R ζ ζ + A1 * q)) := by
      have hg0 : Continuous (gaussW c') := by unfold gaussW; fun_prop
      fun_prop
    have hlin_int : IntervalIntegrable (fun q => gaussW c' q * (boasA c' R ζ ζ + A1 * q)) volume (-L) L :=
      hlin_cont.intervalIntegrable (-L) L
    have hlin_val : ∫ q in (-L)..L, gaussW c' q * (boasA c' R ζ ζ + A1 * q) =
        boasA c' R ζ ζ * ∫ q in (-L)..L, gaussW c' q := by
      have hsp : (fun q => gaussW c' q * (boasA c' R ζ ζ + A1 * q)) =
          fun q => boasA c' R ζ ζ * gaussW c' q + A1 * (q * gaussW c' q) := by
        ext q; ring
      rw [hsp, intervalIntegral.integral_add
          ((by unfold gaussW; fun_prop : Continuous fun q => boasA c' R ζ ζ * gaussW c' q).intervalIntegrable (-L) L)
          ((by unfold gaussW; fun_prop : Continuous fun q => A1 * (q * gaussW c' q)).intervalIntegrable (-L) L),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        gaussW_odd_integral, mul_zero, add_zero]
    have h1_sub : |(∫ q in (-L)..L, gaussW c' q) - 1| ≤ 2 * c' ^ (-8 : ℝ) := by
      have hcompl : (Icc (-L) L)ᶜ = {q : ℝ | L < |q|} := by
        ext q; simp only [mem_compl_iff, mem_Icc, mem_ofPred_eq, lt_abs, not_and_or, not_le]
        constructor
        · rintro (h | h)
          · right; linarith only [h]
          · left; exact h
        · rintro (h | h)
          · right; exact h
          · left; linarith only [h]
      have hsum : (∫ q in Icc (-L) L, gaussW c' q) + ∫ q in {q : ℝ | L < |q|}, gaussW c' q = 1 := by
        rw [← hcompl, integral_add_compl measurableSet_Icc (integrable_gaussW hc1), integral_gaussW hc1]
      have heq_I : ∫ q in (-L)..L, gaussW c' q = ∫ q in Icc (-L) L, gaussW c' q := by
        rw [intervalIntegral.integral_of_le (by linarith only [hL_pos]), integral_Icc_eq_integral_Ioc]
      have htail := gaussW_tail_le hc1
      have htl_nn : 0 ≤ ∫ q in {q : ℝ | L < |q|}, gaussW c' q :=
        setIntegral_nonneg (measurableSet_lt measurable_const continuous_abs.measurable)
          fun q _ => gaussW_nonneg _ _
      have hdiff : (∫ q in (-L)..L, gaussW c' q) - 1 = -(∫ q in {q : ℝ | L < |q|}, gaussW c' q) := by
        linarith only [heq_I, hsum]
      rw [hdiff, abs_neg, abs_of_nonneg htl_nn]
      exact htail
    have hrem : |∫ q in (-L)..L, (gaussW c' q * boasA c' R ζ (q + ζ) -
          gaussW c' q * (boasA c' R ζ ζ + A1 * q))| ≤ 5 * M2 * (8 * Real.sqrt 2 * Real.log c') := by
      have habs : |∫ q in (-L)..L, (gaussW c' q * boasA c' R ζ (q + ζ) -
            gaussW c' q * (boasA c' R ζ ζ + A1 * q))| ≤
          ∫ q in (-L)..L, |gaussW c' q * boasA c' R ζ (q + ζ) -
            gaussW c' q * (boasA c' R ζ ζ + A1 * q)| :=
        intervalIntegral.abs_integral_le_integral_abs (by linarith only [hL_pos])
      have hmono : ∫ q in (-L)..L, |gaussW c' q * boasA c' R ζ (q + ζ) -
            gaussW c' q * (boasA c' R ζ ζ + A1 * q)| ≤
          ∫ q in (-L)..L, 5 * M2 * (q ^ 2 * gaussW c' q) := by
        refine intervalIntegral.integral_mono_on (by linarith only [hL_pos])
          ((hA_int.sub hlin_int).abs) (hq2_int.intervalIntegrable.const_mul (5 * M2)) ?_
        intro q hq
        have hqz : q + ζ ∈ Icc a b := ⟨by dsimp [a]; linarith only [hq.1], by dsimp [b]; linarith only [hq.2]⟩
        have hqsub : q + ζ - ζ = q := add_sub_cancel_right q ζ
        have hpt := hA_tay hqz
        rw [hqsub] at hpt
        have heq : gaussW c' q * boasA c' R ζ (q + ζ) - gaussW c' q * (boasA c' R ζ ζ + A1 * q) =
            gaussW c' q * (boasA c' R ζ (q + ζ) - (boasA c' R ζ ζ + A1 * q)) := by ring
        rw [heq, abs_mul, abs_of_nonneg (gaussW_nonneg _ _)]
        calc gaussW c' q * |boasA c' R ζ (q + ζ) - (boasA c' R ζ ζ + A1 * q)|
            ≤ gaussW c' q * (5 * M2 * q ^ 2) := mul_le_mul_of_nonneg_left hpt (gaussW_nonneg _ _)
          _ = 5 * M2 * (q ^ 2 * gaussW c' q) := by ring
      have hfull : ∫ q in (-L)..L, 5 * M2 * (q ^ 2 * gaussW c' q) ≤
          5 * M2 * ∫ q : ℝ, q ^ 2 * gaussW c' q := by
        rw [intervalIntegral.integral_of_le (by linarith only [hL_pos]), integral_const_mul]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact setIntegral_le_integral hq2_int (Eventually.of_forall fun q =>
          mul_nonneg (sq_nonneg q) (gaussW_nonneg _ _))
      calc |∫ q in (-L)..L, (gaussW c' q * boasA c' R ζ (q + ζ) -
              gaussW c' q * (boasA c' R ζ ζ + A1 * q))|
          ≤ ∫ q in (-L)..L, 5 * M2 * (q ^ 2 * gaussW c' q) := habs.trans hmono
        _ ≤ 5 * M2 * ∫ q : ℝ, q ^ 2 * gaussW c' q := hfull
        _ ≤ 5 * M2 * (8 * Real.sqrt 2 * Real.log c') :=
            mul_le_mul_of_nonneg_left (gaussW_sq_integral_le hc1) (by positivity)
    have hAζ_bd : |boasA c' R ζ ζ| ≤ 3 * lowerPζ c' R ζ :=
      abs_boasA_le hc0 ((div_pos (zetaMin_pos hc0) zero_lt_two).trans_le hζ_min) hPζ_pos.le
    have hconst_err : |boasA c' R ζ ζ * (∫ q in (-L)..L, gaussW c' q) - boasA c' R ζ ζ| ≤
        6 * lowerPζ c' R ζ * c' ^ (-8 : ℝ) := by
      have heq : boasA c' R ζ ζ * (∫ q in (-L)..L, gaussW c' q) - boasA c' R ζ ζ =
          boasA c' R ζ ζ * ((∫ q in (-L)..L, gaussW c' q) - 1) := by ring
      rw [heq, abs_mul]
      calc |boasA c' R ζ ζ| * |(∫ q in (-L)..L, gaussW c' q) - 1|
          ≤ (3 * lowerPζ c' R ζ) * (2 * c' ^ (-8 : ℝ)) := mul_le_mul hAζ_bd h1_sub (abs_nonneg _) (by positivity)
        _ = 6 * lowerPζ c' R ζ * c' ^ (-8 : ℝ) := by ring
    have hsplit : (∫ q in (-L)..L, gaussW c' q * boasA c' R ζ (q + ζ)) - boasA c' R ζ ζ =
        (∫ q in (-L)..L, (gaussW c' q * boasA c' R ζ (q + ζ) -
          gaussW c' q * (boasA c' R ζ ζ + A1 * q))) +
          (boasA c' R ζ ζ * (∫ q in (-L)..L, gaussW c' q) - boasA c' R ζ ζ) := by
      have hsub := intervalIntegral.integral_sub hA_int hlin_int
      rw [hlin_val] at hsub
      linarith only [hsub]
    rw [hsplit]
    exact (abs_add_le _ _).trans (add_le_add hrem hconst_err)
  have htail_err :
      |∫ z in Iζ \ Ioo (ζ - L) (ζ + L), gaussW c' (z - ζ) * boasA c' R ζ z| ≤
        12 * lowerPζ c' R ζ * c' ^ (-8 : ℝ) := by
    have habs := norm_integral_le_integral_norm
      (f := fun z => gaussW c' (z - ζ) * boasA c' R ζ z) (μ := volume.restrict (Iζ \ Ioo (ζ - L) (ζ + L)))
    have hle1 : ∫ z in Iζ \ Ioo (ζ - L) (ζ + L), ‖gaussW c' (z - ζ) * boasA c' R ζ z‖ ≤
        ∫ z in Iζ \ Ioo (ζ - L) (ζ + L), 6 * lowerPζ c' R ζ * gaussW c' (z - ζ) := by
      refine setIntegral_mono_on hdiff_int.norm ((hg_shift_int.const_mul (6 * lowerPζ c' R ζ)).integrableOn)
        (hIζ_meas.diff measurableSet_Ioo) fun z hz => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussW_nonneg _ _), mul_comm (gaussW c' (z - ζ))]
      exact mul_le_mul_of_nonneg_right (hIζ_bd z hz.1) (gaussW_nonneg _ _)
    have hsub_le : Iζ \ Ioo (ζ - L) (ζ + L) ⊆ {z : ℝ | L ≤ |z - ζ|} := fun z hz => by
      have hz2 : ¬ (ζ - L < z ∧ z < ζ + L) := hz.2
      rw [not_and_or, not_lt, not_lt] at hz2
      rw [Set.mem_ofPred_eq, le_abs]
      rcases hz2 with h | h
      · right; linarith only [h]
      · left; linarith only [h]
    have hle2 : ∫ z in Iζ \ Ioo (ζ - L) (ζ + L), 6 * lowerPζ c' R ζ * gaussW c' (z - ζ) ≤
        ∫ z in {z : ℝ | L ≤ |z - ζ|}, 6 * lowerPζ c' R ζ * gaussW c' (z - ζ) :=
      setIntegral_mono_set ((hg_shift_int.const_mul (6 * lowerPζ c' R ζ)).integrableOn)
        (Eventually.of_forall fun z => mul_nonneg (by positivity) (gaussW_nonneg _ _))
        (Eventually.of_forall hsub_le)
    have hle_eq : ∫ z in {z : ℝ | L ≤ |z - ζ|}, gaussW c' (z - ζ) =
        ∫ q in {q : ℝ | L < |q|}, gaussW c' q := by
      have hae : ({z : ℝ | L < |z - ζ|} : Set ℝ) =ᵐ[volume] {z : ℝ | L ≤ |z - ζ|} := by
        have hnull : volume ({ζ - L, ζ + L} : Set ℝ) = 0 :=
          Set.Finite.measure_zero ((Set.finite_singleton _).insert _) volume
        filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
        exact ⟨fun h => h.le, fun h => lt_of_le_of_ne h (fun heq => by
          rcases (abs_eq hL_pos.le).mp heq.symm with h1 | h2
          · exact hz.2 (by linarith only [h1])
          · exact hz.1 (by linarith only [h2]))⟩
      rw [setIntegral_congr_set hae.symm]
      let φ : ℝ → ℝ := fun q => if L < |q| then gaussW c' q else 0
      have hm1 : MeasurableSet {z : ℝ | L < |z - ζ|} :=
        measurableSet_lt measurable_const (continuous_abs.comp (continuous_id.sub continuous_const)).measurable
      have hm2 : MeasurableSet {q : ℝ | L < |q|} :=
        measurableSet_lt measurable_const continuous_abs.measurable
      have hL1 : ∫ z in {z : ℝ | L < |z - ζ|}, gaussW c' (z - ζ) = ∫ z, φ (z - ζ) := by
        rw [← integral_indicator (μ := volume) (f := fun z => gaussW c' (z - ζ)) hm1]
        congr 1
      have hL2 : ∫ q in {q : ℝ | L < |q|}, gaussW c' q = ∫ q, φ q := by
        rw [← integral_indicator (μ := volume) (f := gaussW c') hm2]
        congr 1
      rw [hL1, hL2, integral_sub_right_eq_self φ ζ]
    calc |∫ z in Iζ \ Ioo (ζ - L) (ζ + L), gaussW c' (z - ζ) * boasA c' R ζ z|
        ≤ ∫ z in {z : ℝ | L ≤ |z - ζ|}, 6 * lowerPζ c' R ζ * gaussW c' (z - ζ) :=
          (habs.trans hle1).trans hle2
      _ = 6 * lowerPζ c' R ζ * ∫ z in {z : ℝ | L ≤ |z - ζ|}, gaussW c' (z - ζ) :=
          integral_const_mul _ _
      _ = 6 * lowerPζ c' R ζ * ∫ q in {q : ℝ | L < |q|}, gaussW c' q := by rw [hle_eq]
      _ ≤ 6 * lowerPζ c' R ζ * (2 * c' ^ (-8 : ℝ)) := by gcongr; exact gaussW_tail_le hc1
      _ = 12 * lowerPζ c' R ζ * c' ^ (-8 : ℝ) := by ring
  have hM2_mul : 5 * M2 * (8 * Real.sqrt 2 * Real.log c') ≤ 10 * C2 * lowerPζ c' R ζ * c' ^ (-1 : ℝ) := by
    calc 5 * M2 * (8 * Real.sqrt 2 * Real.log c')
        = 10 * C2 * lowerPζ c' R ζ * (8 * Real.sqrt 2 * Real.log c' * c' ^ (-(12 / 7 : ℝ))) := by
          dsimp [M2]; ring
      _ ≤ 10 * C2 * lowerPζ c' R ζ * c' ^ (-1 : ℝ) := by gcongr; exact hpows.1
  have h18_mul : 18 * lowerPζ c' R ζ * c' ^ (-8 : ℝ) ≤ 9 * lowerPζ c' R ζ * c' ^ (-1 : ℝ) := by
    calc 18 * lowerPζ c' R ζ * c' ^ (-8 : ℝ)
        = 9 * lowerPζ c' R ζ * (2 * c' ^ (-8 : ℝ)) := by ring
      _ ≤ 9 * lowerPζ c' R ζ * c' ^ (-1 : ℝ) := by gcongr; exact hpows.2
  have htot : |(∫ z in Iζ, gaussW c' (z - ζ) * boasA c' R ζ z) - boasA c' R ζ ζ| ≤
      (10 * C2 + 9) * lowerPζ c' R ζ * c' ^ (-1 : ℝ) := by
    rw [hsplit_int, hcore_eq]
    have hsum_eq : (∫ q in (-L)..L, gaussW c' q * boasA c' R ζ (q + ζ)) +
          (∫ z in Iζ \ Ioo (ζ - L) (ζ + L), gaussW c' (z - ζ) * boasA c' R ζ z) -
          boasA c' R ζ ζ =
        ((∫ q in (-L)..L, gaussW c' q * boasA c' R ζ (q + ζ)) - boasA c' R ζ ζ) +
          ∫ z in Iζ \ Ioo (ζ - L) (ζ + L), gaussW c' (z - ζ) * boasA c' R ζ z := by ring
    rw [hsum_eq]
    have htri := (abs_add_le _ _).trans (add_le_add hcore_err htail_err)
    linarith only [htri, hM2_mul, h18_mul]
  exact htot.trans (by
    dsimp [K_loc, C2]
    have hnn : 0 ≤ lowerPζ c' R ζ * c' ^ (-1 : ℝ) := by positivity
    nlinarith only [hnn])

end

end FormalResearch.ModularBootstrap.FiveTerm




