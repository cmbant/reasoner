module

public import FormalResearch.SignUncertainty.UctBumpFarIbp
public import FormalResearch.SignUncertainty.UctBumpFarSplit
public import FormalResearch.SignUncertainty.UctBumpEdge
public import FormalResearch.SignUncertainty.UctBumpInvPoly
public import FormalResearch.SignUncertainty.UctBumpE0

/-!
# The compactly supported part of the far band (F2a, `uct:bump-weighted`)

For `B_near = bumpNear B` (support in `[bδ, 2]`) and `L ≥ 2`, with `c = h⁻²`, `h ≤ 1/4`, `δ ≥ a₀ h`, `α ≤ 4`:
`‖∫ E₀(τ) e^{icLτ} B̂_near(icτ) dτ‖ ≤ C M c⁻² L⁻²` (`bump_near_bound`), `C` depending only on `b, α, K, a₀`.

Route: `E₀ = ε + (E₀'(0)τ + G_h(τ/h))` (`E0_poly_remainder`).  The polynomial in `τ` contributes `∑ κ_k ∫ τ^k e^{icLτ} B̂ = ∑ κ_k (2π/c)(i c)^{-k} B_near^{(k)}(L) = 0`
(`tau_pow_inversion`; `B_near^{(k)}(L) = 0` for `L ≥ 2`), and `ε` is handled by two integrations by parts (`eps_ibp_bound`) against `Φ_j(τ) = ∫ x^j B_near e^{-icτx}`,
whose decay `|Φ_j| ≤ C M Λ_{α-j}(δ)(1+cδ|τ|)^{-r}` is `bump_laplace_decay` for the profile `x^j B_near` (`BumpProfile.mulPow`, `near_profile`), and `Λ_{α-j}(δ) ≤ 2 δ^{-(3-j)}` for `α ≤ 4`.

Class: proved, no hypotheses.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open FormalResearch.Asymptotics
open scoped Real

namespace FormalResearch.SignUncertainty

lemma bumpLambda_le_inv_pow {γ δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {m : ℕ} (hm : 1 ≤ m) (hγ : γ ≤ m + 1) :
    bumpLambda γ δ ≤ 2 * (δ⁻¹) ^ m := by
  have hi : 1 ≤ δ⁻¹ := one_le_inv_iff₀.mpr ⟨hδ0, hδ1⟩
  have h1 : 1 ≤ (δ⁻¹) ^ m := one_le_pow₀ hi
  unfold bumpLambda
  split_ifs with hα
  · have h2 : Real.log (1 / δ) ≤ 1 / δ - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h3 : δ⁻¹ ≤ (δ⁻¹) ^ m := by
      calc δ⁻¹ = (δ⁻¹) ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ hi hm
    rw [one_div] at h2 ⊢
    linarith
  · have h2 : δ ^ (1 - γ) = (δ⁻¹) ^ (γ - 1) := by
      rw [Real.inv_rpow hδ0.le, ← Real.rpow_neg hδ0.le]; ring_nf
    have h3 : (δ⁻¹) ^ (γ - 1) ≤ (δ⁻¹) ^ ((m : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hi (by linarith)
    rw [h2]
    rw [Real.rpow_natCast] at h3
    linarith

/-- `Φ_m(τ) = ∫ e^{-icτx} x^m f(x) dx`. -/
noncomputable def nearPhi (f : ℝ → ℝ) (c : ℝ) (m : ℕ) (τ : ℝ) : ℂ :=
  bumpLapW f m (((c * τ : ℝ) : ℂ) * Complex.I + ((0 : ℝ) : ℂ))

lemma nearPhi_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (hz : ∀ x : ℝ, x < 0 → f x = 0)
    (hI : ∀ m : ℕ, Integrable (fun x : ℝ => x ^ m * f x)) (c : ℝ) (m : ℕ) (τ : ℝ) :
    HasDerivAt (nearPhi f c m) (-((c : ℂ) * Complex.I) * nearPhi f c (m + 1) τ) τ := by
  have := hasDerivAt_bumpLapW_param hf hz (le_refl (0 : ℝ)) c τ (by simpa using hI m) (by simpa using hI (m + 1))
  exact this

lemma nearPhi_zero_eq (f : ℝ → ℝ) (c τ : ℝ) :
    nearPhi f c 0 τ = bumpLaplace f ((c : ℂ) * ((τ : ℂ) * Complex.I)) := by
  unfold nearPhi
  rw [BumpProfile.bumpLapW_zero_B]
  congr 1
  push_cast
  ring

lemma integrable_pow_compact {f : ℝ → ℝ} (hf : Continuous f) (hz : ∀ x : ℝ, x < 0 → f x = 0)
    (hr : ∀ x : ℝ, 2 ≤ x → f x = 0) (m : ℕ) : Integrable (fun x : ℝ => x ^ m * f x) := by
  have hc : Continuous fun x : ℝ => x ^ m * f x := (continuous_pow m).mul hf
  refine hc.integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 2)) fun x hx => ?_)
  by_cases hx0 : x < 0
  · rw [hz x hx0, mul_zero]
  · have : 2 < x := by
      by_contra hcon
      exact hx ⟨not_lt.mp hx0, not_lt.mp hcon⟩
    rw [hr x this.le, mul_zero]

lemma nearPhi_decay {b α : ℝ} (hb : 0 < b) (K : ℕ → ℝ) (j : ℕ) (hj : j ≤ 2) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ → ℝ) (δ M c β τ : ℝ), 0 < δ → δ ≤ 1 → b * δ ≤ 1 → 0 ≤ M → 0 < c → 3 / 2 ≤ β →
      BumpProfile b δ M α β K B →
        ‖nearPhi (bumpNear B) c j τ‖ ≤ C * M * bumpLambda (α - j) δ / (1 + c * δ * |τ|) ^ r := by
  have hj2 : (j : ℝ) ≤ 2 := by exact_mod_cast hj
  obtain ⟨C, hC, hdec⟩ := bump_laplace_decay (b := b) (α := α - j) (β := 7 / 2 - j) hb (by linarith)
    (mulPowK (BumpProfile.nearK K) j) r
  refine ⟨C, hC, fun B δ M c β τ hδ0 hδ1 hbδ hM hc hβ h => ?_⟩
  have hn := (h.near_profile hb hδ0 hM hβ).mulPow hb hδ0 hM j
  have := hdec _ δ M c 0 τ hδ0 hδ1 hbδ hM hc le_rfl hn
  have hs : (((c * τ : ℝ) : ℂ) * Complex.I + ((0 : ℝ) : ℂ)) = (c : ℂ) * (((0 : ℝ) : ℂ) + (τ : ℂ) * Complex.I) := by
    push_cast; ring
  have e : nearPhi (bumpNear B) c j τ = bumpLaplace (fun y : ℝ => y ^ j * bumpNear B y)
      ((c : ℂ) * (((0 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)) := by
    unfold nearPhi bumpLapW bumpLaplace
    rw [hs]
  rw [e]
  simpa using this

lemma integrable_pow_of_decay {Φ : ℝ → ℂ} (hc : Continuous Φ) {a D : ℝ} (ha : 0 < a) (k : ℕ)
    (hb : ∀ τ, ‖Φ τ‖ ≤ D / (1 + a * |τ|) ^ (k + 2)) : Integrable (fun τ : ℝ => (τ : ℂ) ^ k * Φ τ) := by
  have hD : 0 ≤ D := by
    have := hb 0
    simp only [abs_zero, mul_zero, add_zero, one_pow, div_one] at this
    exact (norm_nonneg _).trans this
  obtain ⟨hint, -⟩ := integral_inv_sq_scaled ha
  refine (hint.const_mul (D / a ^ k)).mono' ((Complex.continuous_ofReal.pow k).mul hc).aestronglyMeasurable
    (ae_of_all _ fun τ => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hY : 0 < 1 + a * |τ| := by positivity
  have h1 : |τ| ^ k ≤ (1 + a * |τ|) ^ k / a ^ k := by
    rw [le_div_iff₀ (by positivity), ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [abs_nonneg τ]) k
  calc |τ| ^ k * ‖Φ τ‖ ≤ ((1 + a * |τ|) ^ k / a ^ k) * (D / (1 + a * |τ|) ^ (k + 2)) :=
        mul_le_mul h1 (hb τ) (norm_nonneg _) (by positivity)
    _ = D / a ^ k * ((1 + a * |τ|) ^ 2)⁻¹ := by
        field_simp
        ring

/-- The polynomial `a₁ τ + G_h(τ/h)` integrates to zero against `W` as soon as every `τ^k W`, `k ≥ 1`, does. -/
lemma poly_part_zero (P : P2) {h : ℝ} (hh : 0 < h) (a1 : ℂ) {W : ℝ → ℂ}
    (hint : ∀ k : ℕ, 1 ≤ k → Integrable (fun τ : ℝ => (τ : ℂ) ^ k * W τ))
    (hz : ∀ k : ℕ, 1 ≤ k → ∫ τ : ℝ, (τ : ℂ) ^ k * W τ = 0) :
    Integrable (fun τ : ℝ => (a1 * (τ : ℂ) + gP0 P h (τ / h)) * W τ) ∧
      ∫ τ : ℝ, (a1 * (τ : ℂ) + gP0 P h (τ / h)) * W τ = 0 := by
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  set κ : (Fin 2 →₀ ℕ) → ℂ := fun d =>
    P.coeff d * (h : ℂ) ^ (d 0) / (((d 1 + 1 : ℕ)) : ℂ) / (h : ℂ) ^ (d 1 + 2) / (((d 1 + 2 : ℕ)) : ℂ) with hκ
  have hpt : ∀ τ : ℝ, (a1 * (τ : ℂ) + gP0 P h (τ / h)) * W τ =
      a1 * ((τ : ℂ) ^ 1 * W τ) + ∑ d ∈ P.support, κ d * ((τ : ℂ) ^ (d 1 + 2) * W τ) := by
    intro τ
    have hg : gP0 P h (τ / h) = ∑ d ∈ P.support, κ d * (τ : ℂ) ^ (d 1 + 2) := by
      unfold gP0
      refine Finset.sum_congr rfl fun d _ => ?_
      simp only [hκ]
      push_cast
      rw [div_pow]
      field_simp
    rw [hg, add_mul, Finset.sum_mul, pow_one]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun d _ => by ring
  simp_rw [hpt]
  have i1 := hint 1 le_rfl
  have iS : ∀ d ∈ P.support, Integrable (fun τ : ℝ => κ d * ((τ : ℂ) ^ (d 1 + 2) * W τ)) volume :=
    fun d _ => (hint (d 1 + 2) (by omega)).const_mul (κ d)
  refine ⟨(i1.const_mul a1).add (integrable_finsetSum _ iS), ?_⟩
  have e1 : ∫ τ : ℝ, (τ : ℂ) ^ 1 * W τ = 0 := hz 1 le_rfl
  have e2 : ∀ d ∈ P.support, ∫ τ : ℝ, κ d * ((τ : ℂ) ^ (d 1 + 2) * W τ) = 0 := fun d _ => by
    rw [integral_const_mul, hz _ (by omega), mul_zero]
  rw [integral_add (i1.const_mul a1) (integrable_finsetSum _ iS), integral_const_mul, e1, mul_zero,
    integral_finsetSum _ iS, Finset.sum_eq_zero e2, add_zero]

lemma near_arith {h δ L M Cε C0 C1 C2 I₂ q U Λ0 Λ1 Λ2 : ℝ} {p : ℕ} (hh : 0 < h) (hδ : 0 < δ) (hL : 0 < L)
    (hM : 0 ≤ M) (hCε : 0 ≤ Cε) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hI : 0 ≤ I₂) (hq : 0 < q)
    (hw : h / δ ≤ q) (hU1 : 1 ≤ U) (hUq : q ≤ U) (hΛ0 : Λ0 ≤ 2 * (δ⁻¹) ^ 3) (hΛ1 : Λ1 ≤ 2 * (δ⁻¹) ^ 2)
    (hΛ2 : Λ2 ≤ 2 * (δ⁻¹) ^ 1) (hΛ0n : 0 ≤ Λ0) (hΛ1n : 0 ≤ Λ1) (hΛ2n : 0 ≤ Λ2) :
    Cε * (max 1 (1 / (δ / h))) ^ p * (I₂ / ((δ / h) / h)) * (h ^ 4 / L ^ 2) *
        (h ^ 2 * (C0 * M * Λ0) + 2 * h * (C1 * M * Λ1) + C2 * M * Λ2) ≤
      Cε * U ^ p * I₂ * (2 * C0 * q ^ 4 + 4 * C1 * q ^ 3 + 2 * C2 * q ^ 2) * M * (((h ^ 2)⁻¹) ^ 2)⁻¹ * (L ^ 2)⁻¹ := by
  set w : ℝ := h / δ with hwdef
  have hw0 : 0 < w := div_pos hh hδ
  have hδw : δ = h / w := by rw [hwdef]; field_simp
  have hδinv : δ⁻¹ = w / h := by rw [hδw]; field_simp
  have hmax : max 1 (1 / (δ / h)) ≤ U := max_le hU1 (by rw [one_div_div]; exact hw.trans hUq)
  have e1 : I₂ / ((δ / h) / h) = I₂ * h ^ 2 / δ := by field_simp
  have hsum : h ^ 2 * (C0 * M * Λ0) + 2 * h * (C1 * M * Λ1) + C2 * M * Λ2 ≤
      M * (2 * C0 * h ^ 2 * (w / h) ^ 3 + 4 * C1 * h * (w / h) ^ 2 + 2 * C2 * (w / h)) := by
    rw [hδinv] at hΛ0 hΛ1 hΛ2
    calc h ^ 2 * (C0 * M * Λ0) + 2 * h * (C1 * M * Λ1) + C2 * M * Λ2
        ≤ h ^ 2 * (C0 * M * (2 * (w / h) ^ 3)) + 2 * h * (C1 * M * (2 * (w / h) ^ 2)) + C2 * M * (2 * (w / h) ^ 1) := by
          gcongr
      _ = _ := by ring
  have hS : 0 ≤ M * (2 * C0 * h ^ 2 * (w / h) ^ 3 + 4 * C1 * h * (w / h) ^ 2 + 2 * C2 * (w / h)) := by positivity
  calc Cε * (max 1 (1 / (δ / h))) ^ p * (I₂ / ((δ / h) / h)) * (h ^ 4 / L ^ 2) *
        (h ^ 2 * (C0 * M * Λ0) + 2 * h * (C1 * M * Λ1) + C2 * M * Λ2)
      ≤ Cε * U ^ p * (I₂ * h ^ 2 / δ) * (h ^ 4 / L ^ 2) *
        (M * (2 * C0 * h ^ 2 * (w / h) ^ 3 + 4 * C1 * h * (w / h) ^ 2 + 2 * C2 * (w / h))) := by
        rw [e1]
        have hmp : (max 1 (1 / (δ / h))) ^ p ≤ U ^ p := pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) hmax p
        gcongr
    _ = Cε * U ^ p * I₂ * M * (h ^ 4 / L ^ 2) * (2 * C0 * w ^ 4 + 4 * C1 * w ^ 3 + 2 * C2 * w ^ 2) := by
        rw [hδw]; field_simp
    _ ≤ Cε * U ^ p * I₂ * M * (h ^ 4 / L ^ 2) * (2 * C0 * q ^ 4 + 4 * C1 * q ^ 3 + 2 * C2 * q ^ 2) := by
        have hwq : w ≤ q := hw
        gcongr
    _ = _ := by field_simp

/-- **The compactly supported part of the far band.**  `C` depends only on `b, α, K, a₀`. -/
theorem bump_near_bound {b α : ℝ} (hb : 0 < b) (hα : α ≤ 4) (K : ℕ → ℝ) {a0 : ℝ} (ha0 : 0 < a0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ → ℝ) (δ M c L β : ℝ), 0 < δ → δ ≤ 1 → b * δ ≤ 1 → 0 ≤ M → 16 ≤ c → 2 ≤ L →
      3 / 2 ≤ β → a0 ≤ Real.sqrt c * δ → BumpProfile b δ M α β K B →
      Integrable (fun τ : ℝ => bumpE0 c τ * Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) *
          bumpLaplace (bumpNear B) ((c : ℂ) * ((τ : ℂ) * Complex.I))) ∧
      ‖∫ τ : ℝ, bumpE0 c τ * Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) *
          bumpLaplace (bumpNear B) ((c : ℂ) * ((τ : ℂ) * Complex.I))‖ ≤ C * M * (c ^ 2)⁻¹ * (L ^ 2)⁻¹ := by
  obtain ⟨P, Cε, p, hP, hP0, hCε, hrem⟩ := E0_poly_remainder
  obtain ⟨C0, hC0, hd0⟩ := nearPhi_decay (b := b) (α := α) hb K 0 (by norm_num) (p + 2)
  obtain ⟨C1, hC1, hd1⟩ := nearPhi_decay (b := b) (α := α) hb K 1 (by norm_num) (p + 2)
  obtain ⟨C2, hC2, hd2⟩ := nearPhi_decay (b := b) (α := α) hb K 2 (by norm_num) (p + 2)
  set I₂ : ℝ := ∫ x : ℝ, ((1 + |x|) ^ 2)⁻¹ with hI₂
  have hI₂0 : 0 ≤ I₂ := integral_nonneg fun x => by positivity
  set q : ℝ := 1 / a0 with hq
  have hq0 : 0 < q := by positivity
  set U : ℝ := max 1 q with hU
  have hU1 : 1 ≤ U := le_max_left _ _
  refine ⟨Cε * U ^ p * I₂ * (2 * C0 * q ^ 4 + 4 * C1 * q ^ 3 + 2 * C2 * q ^ 2), by positivity, ?_⟩
  intro B δ M c L β hδ0 hδ1 hbδ hM hc hL hβ ha hB
  have hc0 : 0 < c := by linarith
  obtain ⟨h, hh, hh4, hch, hah⟩ : ∃ h : ℝ, 0 < h ∧ h ≤ 1 / 4 ∧ c = (h ^ 2) ⁻¹ ∧ a0 * h ≤ δ := by
    have hs0 : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
    have hs4 : 4 ≤ Real.sqrt c := by
      rw [show (4 : ℝ) = Real.sqrt 16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hc
    refine ⟨(Real.sqrt c)⁻¹, inv_pos.mpr hs0, ?_, ?_, ?_⟩
    · rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hs4
    · rw [inv_pow, Real.sq_sqrt hc0.le, inv_inv]
    · have := mul_le_mul_of_nonneg_right ha (inv_nonneg.mpr hs0.le)
      calc a0 * (Real.sqrt c)⁻¹ ≤ Real.sqrt c * δ * (Real.sqrt c)⁻¹ := this
        _ = δ := by field_simp
  subst hch
  have hc0' : 0 < (h ^ 2)⁻¹ := hc0
  have hfn := hB.near_profile hb hδ0 hM hβ
  have hf : Continuous (bumpNear B) := (contDiff_bumpNear hB.smooth).continuous
  have hz : ∀ x : ℝ, x < 0 → bumpNear B x = 0 := fun x hx => hfn.support x (by nlinarith [mul_pos hb hδ0])
  have hr : ∀ x : ℝ, 2 ≤ x → bumpNear B x = 0 := fun x hx => bumpNear_of_ge hx
  have hI : ∀ m : ℕ, Integrable (fun x : ℝ => x ^ m * bumpNear B x) := integrable_pow_compact hf hz hr
  set c : ℝ := (h ^ 2)⁻¹ with hcdef
  set Φ : ℕ → ℝ → ℂ := fun m => nearPhi (bumpNear B) c m with hΦ
  have hΦd : ∀ m τ, HasDerivAt (Φ m) (-((c : ℂ) * Complex.I) * Φ (m + 1) τ) τ :=
    fun m τ => nearPhi_hasDerivAt hf hz hI c m τ
  have hΦc : ∀ m, Continuous (Φ m) := fun m =>
    continuous_iff_continuousAt.mpr fun τ => (hΦd m τ).continuousAt
  have hY : ∀ τ : ℝ, c * δ * |τ| = δ / h * |τ / h| := fun τ => by
    rw [hcdef, abs_div, abs_of_pos hh]; field_simp
  have hbj : ∀ (j : ℕ) (C : ℝ), (∀ τ : ℝ, ‖Φ j τ‖ ≤ C * M * bumpLambda (α - j) δ / (1 + c * δ * |τ|) ^ (p + 2)) →
      ∀ τ : ℝ, ‖Φ j τ‖ ≤ (C * M * bumpLambda (α - j) δ) / (1 + δ / h * |τ / h|) ^ (p + 2) := by
    intro j C hbd τ
    have := hbd τ
    rwa [hY τ] at this
  have hb0 := hbj 0 C0 fun τ => hd0 B δ M c β τ hδ0 hδ1 hbδ hM hc0' hβ hB
  have hb1 := hbj 1 C1 fun τ => hd1 B δ M c β τ hδ0 hδ1 hbδ hM hc0' hβ hB
  have hb2 := hbj 2 C2 fun τ => hd2 B δ M c β τ hδ0 hδ1 hbδ hM hc0' hβ hB
  have ha1 : 0 < δ / h := div_pos hδ0 hh
  have hΛnn : ∀ γ : ℝ, 0 ≤ bumpLambda γ δ := fun γ => by linarith [one_le_bumpLambda (α := γ) hδ0 hδ1]
  obtain ⟨hεC2, hε⟩ := hrem h hh hh4
  obtain ⟨hint1, hbound⟩ := eps_ibp_bound (ε := E0r P h) (Φ0 := Φ 0) (Φ1 := Φ 1) (Φ2 := Φ 2) (h := h) (c := c)
    (L := L) (Cε := Cε) (a := δ / h) (p := p) hh rfl ha1 (by linarith) hCε
    (by have := hΛnn (α - ((0 : ℕ) : ℝ)); positivity) (by have := hΛnn (α - ((1 : ℕ) : ℝ)); positivity)
    (by have := hΛnn (α - ((2 : ℕ) : ℝ)); positivity) hεC2
    (fun τ => (hε τ).1) (fun τ => (hε τ).2.1) (fun τ => (hε τ).2.2)
    (fun τ => hΦd 0 τ) (fun τ => hΦd 1 τ) (hΦc 2) hb0 hb1 hb2
  -- the polynomial part
  set W : ℝ → ℂ := fun τ => Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) *
    bumpLaplace (bumpNear B) ((c : ℂ) * ((τ : ℂ) * Complex.I)) with hW
  have hΦ0 : ∀ τ, Φ 0 τ = bumpLaplace (bumpNear B) ((c : ℂ) * ((τ : ℂ) * Complex.I)) :=
    fun τ => nearPhi_zero_eq _ _ _
  have hintk : ∀ k : ℕ, Integrable (fun τ : ℝ => (τ : ℂ) ^ k * bumpLaplace (bumpNear B) ((c : ℂ) * ((τ : ℂ) * Complex.I))) := by
    intro k
    obtain ⟨Ck, hCk, hdk⟩ := nearPhi_decay (b := b) (α := α) hb K 0 (by norm_num) (k + 2)
    have := integrable_pow_of_decay (hΦc 0) (a := c * δ) (D := Ck * M * bumpLambda (α - ((0 : ℕ) : ℝ)) δ) (by positivity) k
      (fun τ => hdk B δ M c β τ hδ0 hδ1 hbδ hM hc0' hβ hB)
    simpa only [hΦ0] using this
  have hcontL : Continuous fun τ : ℝ => bumpLaplace (bumpNear B) ((c : ℂ) * ((τ : ℂ) * Complex.I)) := by
    have := hΦc 0
    simpa only [funext hΦ0] using this
  have hexpc : Continuous fun τ : ℝ => Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) := by fun_prop
  have hintW : ∀ k : ℕ, 1 ≤ k → Integrable (fun τ : ℝ => (τ : ℂ) ^ k * W τ) := by
    intro k _
    refine (hintk k).norm.mono' ((Complex.continuous_ofReal.pow k).mul (hexpc.mul hcontL)).aestronglyMeasurable
      (ae_of_all _ fun τ => ?_)
    simp only [hW, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, le_refl]
  have hzW : ∀ k : ℕ, 1 ≤ k → ∫ τ : ℝ, (τ : ℂ) ^ k * W τ = 0 := by
    intro k _
    have := tau_pow_inversion hfn hb hδ0 hbδ (by norm_num) hc0' k (hintk k) L
    simp only [hW]
    rw [this, iteratedDeriv_bumpNear_right hB.smooth k hL]
    simp
  have hpoly := poly_part_zero P hh (deriv (bumpE0 c) 0) hintW hzW
  have key : ∀ τ : ℝ, bumpE0 c τ * Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) *
      bumpLaplace (bumpNear B) ((c : ℂ) * ((τ : ℂ) * Complex.I)) =
      E0r P h τ * Φ 0 τ * Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) +
        (deriv (bumpE0 c) 0 * (τ : ℂ) + gP0 P h (τ / h)) * W τ := by
    intro τ
    have e : bumpE0 c τ = E0r P h τ + (deriv (bumpE0 c) 0 * (τ : ℂ) + gP0 P h (τ / h)) := by
      unfold E0r; ring
    rw [e, hΦ0 τ]
    simp only [hW]
    ring
  simp_rw [key]
  refine ⟨hint1.add hpoly.1, ?_⟩
  rw [integral_add hint1 hpoly.1, hpoly.2, add_zero]
  refine hbound.trans ?_
  have := near_arith (p := p) (L := L) (M := M) (Cε := Cε) (C0 := C0) (C1 := C1) (C2 := C2) (I₂ := I₂) (q := q) (U := U)
    (Λ0 := bumpLambda (α - ((0 : ℕ) : ℝ)) δ) (Λ1 := bumpLambda (α - ((1 : ℕ) : ℝ)) δ)
    (Λ2 := bumpLambda (α - ((2 : ℕ) : ℝ)) δ) hh hδ0 (by linarith) hM hCε hC0 hC1 hC2 hI₂0 hq0
    (by rw [div_le_iff₀ hδ0, hq, one_div, inv_mul_eq_div, le_div_iff₀ ha0]; linarith) hU1 (le_max_right _ _)
    (bumpLambda_le_inv_pow hδ0 hδ1 (m := 3) (by norm_num) (by norm_num; linarith))
    (bumpLambda_le_inv_pow hδ0 hδ1 (m := 2) (by norm_num) (by norm_num; linarith))
    (bumpLambda_le_inv_pow hδ0 hδ1 (m := 1) (by norm_num) (by norm_num; linarith))
    (hΛnn _) (hΛnn _) (hΛnn _)
  exact this

/-- info: 'FormalResearch.SignUncertainty.bump_near_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_near_bound

end FormalResearch.SignUncertainty
