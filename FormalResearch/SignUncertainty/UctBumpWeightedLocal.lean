module

public import FormalResearch.SignUncertainty.UctBumpWeightedExp
public import FormalResearch.SignUncertainty.UctBumpInvPoly

/-!
# `uct:bump-weighted`, local estimate (F2a)

`bump_weighted_local`: with `E₀`-identity `(uct:E0-def)`, the weight-four expansion `E0_poly_expansion` and the monomial inversion `tau_pow_inversion`,
for `L = log(π²ξ) ≥ bδ/2`, `δ ≥ a₀ c^{-1/2}`, `c ≥ 2` and `|B^{(k)}(L)| ≤ C_k M_loc L^{-k}` (`1 ≤ k ≤ 9`):
`|Δh_main(L) - c⁻¹B(L)| ≤ C M_loc (c⁻²L⁻¹ + c⁻³L⁻³) + C M Λ_α(δ) c⁻² δ`.

Class: proved, no hypotheses beyond those displayed.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

lemma pow_le_poly_u {u U : ℝ} (hu : 0 < u) (hU : 1 ≤ U) (huU : u ≤ U) {k : ℕ} (hk1 : 1 ≤ k) (hk9 : k ≤ 9) :
    u ^ k ≤ U ^ 9 * (u + u ^ 3) := by
  have hU9 : 1 ≤ U ^ 9 := one_le_pow₀ hU
  have hu3 : 0 ≤ u ^ 3 := by positivity
  rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with h | h | h
  · subst h; simp only [pow_one]; nlinarith
  · subst h; nlinarith [sq_nonneg (1 - u), mul_nonneg hu.le (sq_nonneg (1 - u))]
  · have h1 : u ^ k = u ^ 3 * u ^ (k - 3) := by rw [← pow_add]; congr 1; omega
    have h2 : u ^ (k - 3) ≤ U ^ (k - 3) := pow_le_pow_left₀ hu.le huU _
    have h3 : U ^ (k - 3) ≤ U ^ 9 := pow_le_pow_right₀ hU (by omega)
    rw [h1]
    nlinarith [mul_le_mul_of_nonneg_left (h2.trans h3) hu3]

lemma poly_term_bound {s L U : ℝ} (hs : 1 ≤ s) (hL : 0 < L) (hU : 1 ≤ U) (hu : (s * L)⁻¹ ≤ U) {d0 d1 : ℕ}
    (hd0 : 1 ≤ d0) (hd1 : 1 ≤ d1) (hd9 : d1 ≤ 9) :
    (s⁻¹) ^ d0 * s ^ d1 * ((s ^ 2) ^ (d1 + 1))⁻¹ * (L ^ d1)⁻¹ ≤
      U ^ 9 * (((s ^ 2) ^ 2)⁻¹ * L⁻¹ + ((s ^ 2) ^ 3)⁻¹ * (L ^ 3)⁻¹) := by
  have hs0 : 0 < s := by linarith
  set u : ℝ := (s * L)⁻¹ with hu_def
  have hu0 : 0 < u := by positivity
  have e1 : (s⁻¹) ^ d0 * s ^ d1 * ((s ^ 2) ^ (d1 + 1))⁻¹ * (L ^ d1)⁻¹ = (s ^ (d0 + 2))⁻¹ * u ^ d1 := by
    have hs' : s ≠ 0 := hs0.ne'
    have hL' : L ≠ 0 := hL.ne'
    simp only [hu_def, mul_inv, mul_pow, inv_pow, ← pow_mul, pow_add, pow_succ]
    field_simp
    ring
  have e2 : ((s ^ 2) ^ 2)⁻¹ * L⁻¹ + ((s ^ 2) ^ 3)⁻¹ * (L ^ 3)⁻¹ = (s ^ 3)⁻¹ * (u + u ^ 3) := by
    rw [hu_def]
    field_simp
  rw [e1, e2]
  have h3 : (s ^ (d0 + 2))⁻¹ ≤ (s ^ 3)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hs (by omega))
  have h4 := pow_le_poly_u hu0 hU hu hd1 hd9
  calc (s ^ (d0 + 2))⁻¹ * u ^ d1 ≤ (s ^ 3)⁻¹ * (U ^ 9 * (u + u ^ 3)) :=
        mul_le_mul h3 h4 (by positivity) (by positivity)
    _ = _ := by ring

lemma integrable_tau_pow_phi {Φ : ℝ → ℂ} (hc : Continuous Φ) {a Q : ℝ} (ha : 0 < a)
    (hQ : ∀ τ : ℝ, ‖Φ τ‖ ≤ Q / (1 + a * |τ|) ^ 23) {k : ℕ} (hk : k ≤ 21) :
    Integrable fun τ : ℝ => (τ : ℂ) ^ k * Φ τ := by
  obtain ⟨hint, -⟩ := integral_inv_sq_scaled ha
  have hQ0 : 0 ≤ Q := by
    have := (norm_nonneg (Φ 0)).trans (hQ 0)
    simpa using this
  refine (hint.const_mul (Q * (a ^ k)⁻¹)).mono' ((Complex.continuous_ofReal.pow k).mul hc).aestronglyMeasurable
    (ae_of_all _ fun τ => ?_)
  have hx : 0 < 1 + a * |τ| := by positivity
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have h1 : |τ| ^ k * ‖Φ τ‖ ≤ |τ| ^ k * (Q / (1 + a * |τ|) ^ 23) :=
    mul_le_mul_of_nonneg_left (hQ τ) (by positivity)
  refine h1.trans ?_
  have h2 : |τ| ^ k = (a ^ k)⁻¹ * (a * |τ|) ^ k := by
    rw [mul_pow]; field_simp
  have h3 : (a * |τ|) ^ k ≤ (1 + a * |τ|) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) _
  have h4 : (1 + a * |τ|) ^ (k + 2) ≤ (1 + a * |τ|) ^ 23 :=
    pow_le_pow_right₀ (by nlinarith [mul_nonneg ha.le (abs_nonneg τ)]) (by omega)
  rw [h2]
  have : (a ^ k)⁻¹ * (a * |τ|) ^ k * (Q / (1 + a * |τ|) ^ 23) ≤ (a ^ k)⁻¹ * (1 + a * |τ|) ^ k * (Q / (1 + a * |τ|) ^ 23) := by
    gcongr
  refine this.trans ?_
  have h5 : (1 + a * |τ|) ^ (k + 2) / (1 + a * |τ|) ^ 23 ≤ 1 := (div_le_one (by positivity)).mpr h4
  have h6 : (a ^ k)⁻¹ * (1 + a * |τ|) ^ k * (Q / (1 + a * |τ|) ^ 23) =
      (Q * (a ^ k)⁻¹) * (((1 + a * |τ|) ^ (k + 2) / (1 + a * |τ|) ^ 23) * ((1 + a * |τ|) ^ 2)⁻¹) := by
    field_simp
    ring
  rw [h6]
  have h7 : 0 ≤ Q * (a ^ k)⁻¹ := by positivity
  calc (Q * (a ^ k)⁻¹) * (((1 + a * |τ|) ^ (k + 2) / (1 + a * |τ|) ^ 23) * ((1 + a * |τ|) ^ 2)⁻¹)
      ≤ (Q * (a ^ k)⁻¹) * (1 * ((1 + a * |τ|) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h5 (by positivity)) h7
    _ = _ := by ring

/-- The polynomial part of `E₀` as a function of `τ` (`h = c^{-1/2}`, `v = c^{1/2} τ`). -/
noncomputable def polyPart (S : Finset (Fin 2 →₀ ℕ)) (a : (Fin 2 →₀ ℕ) → ℂ) (c τ : ℝ) : ℂ :=
  ∑ d ∈ S, a d * ((((Real.sqrt c)⁻¹ : ℝ) : ℂ) ^ (d 0) * (((Real.sqrt c * τ : ℝ)) : ℂ) ^ (d 1))

/-- The polynomial part inverts monomial by monomial (`tau_pow_inversion`): norm bound. -/
lemma poly_part_integral_bound {b α β : ℝ} {K : ℕ → ℝ} (S : Finset (Fin 2 →₀ ℕ)) (a : (Fin 2 →₀ ℕ) → ℂ)
    (hS : ∀ d ∈ S, 1 ≤ d 0 ∧ d 0 < 4 ∧ d 1 ≤ 3 * d 0 ∧ 1 ≤ d 1)
    {B : ℝ → ℝ} {δ M : ℝ} (h : BumpProfile b δ M α β K B) (hb : 0 < b) (hδ : 0 < δ) (hbδ : b * δ ≤ 1) (hβ : 1 < β)
    {c : ℝ} (hc : 1 ≤ c) (L : ℝ) (hL : 0 < L) {U Kb Mloc : ℝ} (hU : 1 ≤ U) (hu : (Real.sqrt c * L)⁻¹ ≤ U)
    (_hMl : 0 ≤ Mloc)
    (hder : ∀ k : ℕ, 1 ≤ k → k ≤ 9 → |iteratedDeriv k B L| ≤ Kb * Mloc / L ^ k)
    (hint : ∀ k : ℕ, k ≤ 9 → Integrable fun τ : ℝ => (τ : ℂ) ^ k * bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I))) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ τ : ℝ, polyPart S a c τ * (Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) *
        bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I)))‖ ≤
      (∑ d ∈ S, ‖a d‖) * Kb * U ^ 9 * Mloc * (((c ^ 2)⁻¹) * L⁻¹ + ((c ^ 3)⁻¹) * (L ^ 3)⁻¹) := by
  set s : ℝ := Real.sqrt c with hs
  have hc0 : 0 < c := by linarith
  have hs0 : 0 < s := Real.sqrt_pos.mpr hc0
  have hs1 : 1 ≤ s := by rw [hs, ← Real.sqrt_one]; exact Real.sqrt_le_sqrt hc
  have hs2 : s ^ 2 = c := Real.sq_sqrt hc0.le
  set Φ : ℝ → ℂ := fun τ => bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I)) with hΦ
  set E : ℝ → ℂ := fun τ => Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) with hE
  have hEc : Continuous E := by simp only [hE]; fun_prop
  have hEn : ∀ τ, ‖E τ‖ = 1 := fun τ => Complex.norm_exp_I_mul_ofReal _
  have hKb : 0 ≤ Kb * Mloc := by
    have := (abs_nonneg (iteratedDeriv 1 B L)).trans (hder 1 le_rfl (by norm_num))
    have h2 : 0 ≤ Kb * Mloc / L ^ 1 := this
    rw [pow_one] at h2
    exact (div_nonneg_iff.mp h2).elim (fun h => h.1) (fun h => by linarith [h.2, hL])
  set coef : (Fin 2 →₀ ℕ) → ℂ := fun d => a d * (((s⁻¹ : ℝ) : ℂ)) ^ (d 0) * (s : ℂ) ^ (d 1) with hcoef
  have hF : ∀ τ : ℝ, polyPart S a c τ * (E τ * Φ τ) = ∑ d ∈ S, coef d * ((τ : ℂ) ^ (d 1) * (E τ * Φ τ)) := by
    intro τ
    unfold polyPart
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [hcoef, ← hs]
    push_cast
    ring
  have hintd : ∀ d ∈ S, Integrable fun τ : ℝ => coef d * ((τ : ℂ) ^ (d 1) * (E τ * Φ τ)) := by
    intro d hd
    have hk : d 1 ≤ 9 := by have := hS d hd; omega
    have := MeasureTheory.Integrable.bdd_mul (hint (d 1) hk) hEc.aestronglyMeasurable (c := 1) (ae_of_all _ fun τ => (hEn τ).le)
    refine (this.const_mul (coef d)).congr (ae_of_all _ fun τ => ?_)
    simp only []
    ring
  have hint_eq : ∫ τ : ℝ, polyPart S a c τ * (E τ * Φ τ) =
      ∑ d ∈ S, coef d * (((2 * Real.pi / c : ℝ) : ℂ) * (Complex.I ^ (d 1) * (c : ℂ) ^ (d 1))⁻¹ *
        ((iteratedDeriv (d 1) B L : ℝ) : ℂ)) := by
    simp_rw [hF]
    rw [MeasureTheory.integral_finsetSum _ hintd]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [integral_const_mul]
    congr 1
    have hk : d 1 ≤ 9 := by have := hS d hd; omega
    exact tau_pow_inversion h hb hδ hbδ hβ hc0 (d 1) (hint (d 1) hk) L
  rw [hint_eq, norm_mul]
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hnorm1 : ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hnorm1]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
  have hterm : ∀ d ∈ S, 1 / (2 * Real.pi) * ‖coef d * (((2 * Real.pi / c : ℝ) : ℂ) *
      (Complex.I ^ (d 1) * (c : ℂ) ^ (d 1))⁻¹ * ((iteratedDeriv (d 1) B L : ℝ) : ℂ))‖ ≤
      ‖a d‖ * (Kb * Mloc) * (U ^ 9 * (((c ^ 2)⁻¹) * L⁻¹ + ((c ^ 3)⁻¹) * (L ^ 3)⁻¹)) := by
    intro d hd
    obtain ⟨h1, h2, h3, h4⟩ := hS d hd
    have hk9 : d 1 ≤ 9 := by omega
    have hB := hder (d 1) h4 hk9
    have hpt := poly_term_bound hs1 hL hU hu h1 h4 hk9
    have hn : ‖coef d * (((2 * Real.pi / c : ℝ) : ℂ) * (Complex.I ^ (d 1) * (c : ℂ) ^ (d 1))⁻¹ *
        ((iteratedDeriv (d 1) B L : ℝ) : ℂ))‖ =
        ‖a d‖ * (s⁻¹) ^ (d 0) * s ^ (d 1) * (2 * Real.pi / c * (c ^ (d 1))⁻¹ * |iteratedDeriv (d 1) B L|) := by
      simp only [hcoef, norm_mul, norm_inv, norm_pow, Complex.norm_real, Complex.norm_I, one_pow, one_mul,
        Real.norm_eq_abs, abs_of_pos hc0, abs_of_pos hs0,
        abs_of_pos (by positivity : 0 < 2 * Real.pi / c)]
    rw [hn]
    have e : 1 / (2 * Real.pi) * (‖a d‖ * (s⁻¹) ^ (d 0) * s ^ (d 1) * (2 * Real.pi / c * (c ^ (d 1))⁻¹ *
        |iteratedDeriv (d 1) B L|)) = ‖a d‖ * ((s⁻¹) ^ (d 0) * s ^ (d 1) * ((s ^ 2) ^ (d 1 + 1))⁻¹ * (L ^ (d 1))⁻¹) *
        (|iteratedDeriv (d 1) B L| * L ^ (d 1)) := by
      rw [← hs2]
      field_simp
      ring
    rw [e]
    have hBL : |iteratedDeriv (d 1) B L| * L ^ (d 1) ≤ Kb * Mloc := by
      have hLk : 0 < L ^ (d 1) := by positivity
      calc |iteratedDeriv (d 1) B L| * L ^ (d 1) ≤ (Kb * Mloc / L ^ (d 1)) * L ^ (d 1) :=
            mul_le_mul_of_nonneg_right hB hLk.le
        _ = Kb * Mloc := by field_simp
    have hW : 0 ≤ U ^ 9 * (((c ^ 2)⁻¹) * L⁻¹ + ((c ^ 3)⁻¹) * (L ^ 3)⁻¹) := by positivity
    have hY : 0 ≤ (s⁻¹) ^ (d 0) * s ^ (d 1) * ((s ^ 2) ^ (d 1 + 1))⁻¹ * (L ^ (d 1))⁻¹ := by positivity
    have hpt' : (s⁻¹) ^ (d 0) * s ^ (d 1) * ((s ^ 2) ^ (d 1 + 1))⁻¹ * (L ^ (d 1))⁻¹ ≤
        U ^ 9 * (((c ^ 2)⁻¹) * L⁻¹ + ((c ^ 3)⁻¹) * (L ^ 3)⁻¹) := by
      rw [← hs2]; exact hpt
    calc ‖a d‖ * ((s⁻¹) ^ (d 0) * s ^ (d 1) * ((s ^ 2) ^ (d 1 + 1))⁻¹ * (L ^ (d 1))⁻¹) * (|iteratedDeriv (d 1) B L| * L ^ (d 1))
        ≤ ‖a d‖ * (U ^ 9 * (((c ^ 2)⁻¹) * L⁻¹ + ((c ^ 3)⁻¹) * (L ^ 3)⁻¹)) * (Kb * Mloc) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hpt' (norm_nonneg _)) hBL (by positivity) (by positivity)
      _ = _ := by ring
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

lemma continuous_polyPart (S : Finset (Fin 2 →₀ ℕ)) (a : (Fin 2 →₀ ℕ) → ℂ) (c : ℝ) :
    Continuous fun τ : ℝ => polyPart S a c τ := by
  unfold polyPart
  refine continuous_finsetSum _ fun d _ => ?_
  fun_prop

/-- The remainder part: absolute bound with the pointwise `E₀` remainder and the decay of `B̂`. -/
lemma rem_part_integral_bound {c δ a0 CR Q L : ℝ} {S : Finset (Fin 2 →₀ ℕ)} {a : (Fin 2 →₀ ℕ) → ℂ}
    {Φ : ℝ → ℂ} (hΦc : Continuous Φ) (hc : 1 ≤ c) (hδ : 0 < δ) (ha0 : 0 < a0) (hsc : a0 ≤ Real.sqrt c * δ)
    (hCR : 0 ≤ CR) (hQ : ∀ τ : ℝ, ‖Φ τ‖ ≤ Q / (1 + c * δ * |τ|) ^ 23)
    (hrem : ∀ τ : ℝ, ‖bumpE0 c τ - polyPart S a c τ‖ ≤ CR * ((Real.sqrt c)⁻¹) ^ 4 * (1 + |Real.sqrt c * τ|) ^ 21)
    (hRc : Continuous fun τ : ℝ => bumpE0 c τ - polyPart S a c τ) :
    Integrable (fun τ : ℝ => (bumpE0 c τ - polyPart S a c τ) *
        (Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) * Φ τ)) ∧
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ τ : ℝ, (bumpE0 c τ - polyPart S a c τ) *
        (Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) * Φ τ)‖ ≤
      (1 / (2 * Real.pi)) * CR * Q * ((min 1 a0) ^ 21)⁻¹ * (∫ x : ℝ, ((1 + |x|) ^ 2)⁻¹) * (a0 ^ 2)⁻¹ * ((c ^ 2)⁻¹ * δ) := by
  have hc0 : 0 < c := by linarith
  set s : ℝ := Real.sqrt c with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hc0
  have hs2 : s ^ 2 = c := Real.sq_sqrt hc0.le
  set m : ℝ := min 1 a0 with hm
  have hm0 : 0 < m := lt_min one_pos ha0
  have hm1 : m ≤ 1 := min_le_left _ _
  have hma : m ≤ a0 := min_le_right _ _
  set aa : ℝ := c * δ with haa
  have haa0 : 0 < aa := mul_pos hc0 hδ
  obtain ⟨hint, hval⟩ := integral_inv_sq_scaled haa0
  have hQ0 : 0 ≤ Q := by simpa using (norm_nonneg (Φ 0)).trans (hQ 0)
  set I2 : ℝ := ∫ x : ℝ, ((1 + |x|) ^ 2)⁻¹ with hI2
  have hI20 : 0 ≤ I2 := integral_nonneg fun x => by positivity
  have hpt : ∀ τ : ℝ, ‖(bumpE0 c τ - polyPart S a c τ) * (Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) * Φ τ)‖ ≤
      (CR * (s⁻¹) ^ 4 * Q * (m ^ 21)⁻¹) * ((1 + aa * |τ|) ^ 2)⁻¹ := by
    intro τ
    rw [norm_mul, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
    have hx : 0 < 1 + aa * |τ| := by positivity
    have h1 : 1 + |s * τ| ≤ m⁻¹ * (1 + aa * |τ|) := by
      rw [abs_mul, abs_of_pos hs0]
      have hsd : a0 ≤ s * δ := hsc
      have : aa * |τ| = (s * δ) * (s * |τ|) := by rw [haa, ← hs2]; ring
      rw [this, le_inv_mul_iff₀ hm0]
      have hx0 : 0 ≤ s * |τ| := by positivity
      nlinarith [mul_le_mul_of_nonneg_right (hma.trans hsd) hx0]
    have h2 : (1 + |s * τ|) ^ 21 ≤ (m ^ 21)⁻¹ * (1 + aa * |τ|) ^ 21 := by
      calc (1 + |s * τ|) ^ 21 ≤ (m⁻¹ * (1 + aa * |τ|)) ^ 21 := pow_le_pow_left₀ (by positivity) h1 _
        _ = _ := by rw [mul_pow, inv_pow]
    have h3 : ‖bumpE0 c τ - polyPart S a c τ‖ * ‖Φ τ‖ ≤
        (CR * (s⁻¹) ^ 4 * (1 + |s * τ|) ^ 21) * (Q / (1 + aa * |τ|) ^ 23) :=
      mul_le_mul (hrem τ) (hQ τ) (norm_nonneg _) (by positivity)
    refine h3.trans ?_
    have h4 : (1 + aa * |τ|) ^ 21 / (1 + aa * |τ|) ^ 23 = ((1 + aa * |τ|) ^ 2)⁻¹ := by
      field_simp
    calc (CR * (s⁻¹) ^ 4 * (1 + |s * τ|) ^ 21) * (Q / (1 + aa * |τ|) ^ 23)
        ≤ (CR * (s⁻¹) ^ 4 * ((m ^ 21)⁻¹ * (1 + aa * |τ|) ^ 21)) * (Q / (1 + aa * |τ|) ^ 23) := by
          gcongr
      _ = (CR * (s⁻¹) ^ 4 * Q * (m ^ 21)⁻¹) * ((1 + aa * |τ|) ^ 21 / (1 + aa * |τ|) ^ 23) := by ring
      _ = _ := by rw [h4]
  have hK1 : 0 ≤ CR * (s⁻¹) ^ 4 * Q * (m ^ 21)⁻¹ := by positivity
  have hEc : Continuous fun τ : ℝ => Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) := by fun_prop
  have hI : Integrable (fun τ : ℝ => (bumpE0 c τ - polyPart S a c τ) *
        (Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) * Φ τ)) :=
    (hint.const_mul (CR * (s⁻¹) ^ 4 * Q * (m ^ 21)⁻¹)).mono' (hRc.mul (hEc.mul hΦc)).aestronglyMeasurable
      (ae_of_all _ hpt)
  refine ⟨hI, ?_⟩
  have hnorm : ‖∫ τ : ℝ, (bumpE0 c τ - polyPart S a c τ) * (Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) * Φ τ)‖ ≤
      (CR * (s⁻¹) ^ 4 * Q * (m ^ 21)⁻¹) * (I2 / aa) := by
    refine (norm_integral_le_of_norm_le (hint.const_mul _) (ae_of_all _ hpt)).trans ?_
    rw [integral_const_mul, hval]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  refine (mul_le_mul_of_nonneg_left hnorm (by positivity)).trans ?_
  have hsd : a0 ≤ s * δ := hsc
  have hinv : (I2 / aa) ≤ I2 * (a0 ^ 2)⁻¹ * δ := by
    have h5 : a0 ^ 2 ≤ aa * δ := by
      rw [haa, ← hs2]; nlinarith [mul_self_le_mul_self ha0.le hsd]
    rw [div_le_iff₀ haa0]
    have : I2 * (a0 ^ 2)⁻¹ * δ * aa = I2 * ((aa * δ) / a0 ^ 2) := by field_simp
    rw [this]
    have h6 : 1 ≤ (aa * δ) / a0 ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
    nlinarith [mul_le_mul_of_nonneg_left h6 hI20]
  have hs4 : (s⁻¹) ^ 4 = (c ^ 2)⁻¹ := by rw [inv_pow, ← hs2]; ring_nf
  calc 1 / (2 * Real.pi) * ((CR * (s⁻¹) ^ 4 * Q * (m ^ 21)⁻¹) * (I2 / aa))
      ≤ 1 / (2 * Real.pi) * ((CR * (s⁻¹) ^ 4 * Q * (m ^ 21)⁻¹) * (I2 * (a0 ^ 2)⁻¹ * δ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinv hK1) (by positivity)
    _ = _ := by rw [hs4]; ring

theorem bump_weighted_local {b α β : ℝ} (hb : 0 < b) (hβ : 3 / 2 ≤ β) (K Kl : ℕ → ℝ) {a0 : ℝ} (ha0 : 0 < a0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ → ℝ) (δ M Mloc c ξ : ℝ), 0 < δ → δ ≤ 1 → b * δ ≤ 1 → 0 ≤ M → 0 ≤ Mloc → 2 ≤ c →
      a0 ≤ Real.sqrt c * δ → 0 < ξ → b * δ / 2 ≤ Real.log (Real.pi ^ 2 * ξ) →
      (∀ k : ℕ, 1 ≤ k → k ≤ 9 → |iteratedDeriv k B (Real.log (Real.pi ^ 2 * ξ))| ≤
        Kl k * Mloc / (Real.log (Real.pi ^ 2 * ξ)) ^ k) →
      BumpProfile b δ M α β K B →
        ‖bumpHmain c B ξ - ((c⁻¹ * B (Real.log (Real.pi ^ 2 * ξ)) : ℝ) : ℂ)‖ ≤
          C * Mloc * (((c ^ 2)⁻¹) * (Real.log (Real.pi ^ 2 * ξ))⁻¹ +
            ((c ^ 3)⁻¹) * ((Real.log (Real.pi ^ 2 * ξ)) ^ 3)⁻¹) +
          C * M * bumpLambda α δ * ((c ^ 2)⁻¹ * δ) := by
  obtain ⟨S, a, CR, hS, hCR, hrem⟩ := E0_poly_expansion
  obtain ⟨Cd, hCd, hdec⟩ := bump_laplace_decay (α := α) hb hβ K 23
  obtain ⟨Ca, hCa, haenv⟩ := kernel_amp_env2
  set A : ℝ := ∑ d ∈ S, ‖a d‖ with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set Kb : ℝ := ∑ k ∈ Finset.range 10, |Kl k| with hKb
  have hKb0 : 0 ≤ Kb := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set U : ℝ := max 1 (2 / (b * a0)) with hU
  have hU1 : 1 ≤ U := le_max_left _ _
  set I2 : ℝ := ∫ x : ℝ, ((1 + |x|) ^ 2)⁻¹ with hI2
  have hI20 : 0 ≤ I2 := integral_nonneg fun x => by positivity
  set Cr : ℝ := (1 / (2 * Real.pi)) * CR * Cd * ((min 1 a0) ^ 21)⁻¹ * I2 * (a0 ^ 2)⁻¹ with hCr
  have hm0 : 0 < min 1 a0 := lt_min one_pos ha0
  have hCr0 : 0 ≤ Cr := by positivity
  have hCp0 : 0 ≤ A * Kb * U ^ 9 := by positivity
  refine ⟨A * Kb * U ^ 9 + Cr, by positivity, ?_⟩
  intro B δ M Mloc c ξ hδ0 hδ1 hbδ hM hMl hc2 hsc hξ hL hder h
  set L : ℝ := Real.log (Real.pi ^ 2 * ξ) with hLdef
  have hc0 : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  set s : ℝ := Real.sqrt c with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hc0
  have hs1 : 1 ≤ s := by rw [hs, ← Real.sqrt_one]; exact Real.sqrt_le_sqrt hc1
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hΛ : 1 ≤ bumpLambda α δ := one_le_bumpLambda (α := α) hδ0 hδ1
  have hder' : ∀ k : ℕ, 1 ≤ k → k ≤ 9 → |iteratedDeriv k B L| ≤ Kb * Mloc / L ^ k := by
    intro k hk1 hk9
    refine (hder k hk1 hk9).trans ?_
    have : Kl k ≤ Kb := by
      calc Kl k ≤ |Kl k| := le_abs_self _
        _ ≤ Kb := Finset.single_le_sum (f := fun k => |Kl k|) (fun _ _ => abs_nonneg _)
            (Finset.mem_range.mpr (by omega))
    gcongr
  -- the line transform
  set Φ : ℝ → ℂ := fun τ => bumpLaplace B ((c : ℂ) * ((τ : ℂ) * Complex.I)) with hΦ
  have hΦi : Integrable Φ := bump_laplace_integrable (α := α) hb hβ K B δ M c hδ0 hδ1 hbδ hM hc0 h
  have hΦc : Continuous Φ :=
    (h.continuousOn_laplace (by positivity) hbδ (by linarith)).comp_continuous (by fun_prop) (fun τ => by simp)
  have hΦd : ∀ τ : ℝ, ‖Φ τ‖ ≤ (Cd * M * bumpLambda α δ) / (1 + c * δ * |τ|) ^ 23 := by
    intro τ
    have := hdec B δ M c 0 τ hδ0 hδ1 hbδ hM hc0 le_rfl h
    simp only [Complex.ofReal_zero, zero_add, mul_zero, zero_mul, neg_zero, Real.exp_zero, mul_one] at this
    exact this
  have haa0 : 0 < c * δ := mul_pos hc0 hδ0
  have hint_k : ∀ k : ℕ, k ≤ 9 → Integrable fun τ : ℝ => (τ : ℂ) ^ k * Φ τ := fun k hk =>
    integrable_tau_pow_phi hΦc haa0 hΦd (by omega)
  -- the size of `s L`
  have hu : (s * L)⁻¹ ≤ U := by
    have hδs : a0 ≤ s * δ := hsc
    have h1 : b * a0 / 2 ≤ s * L := by
      have : b * δ / 2 * s ≤ L * s := mul_le_mul_of_nonneg_right hL hs0.le
      nlinarith [mul_le_mul_of_nonneg_left hδs hb.le]
    have h2 : 0 < b * a0 / 2 := by positivity
    calc (s * L)⁻¹ ≤ (b * a0 / 2)⁻¹ := inv_anti₀ h2 h1
      _ = 2 / (b * a0) := by field_simp
      _ ≤ U := le_max_right _ _
  -- the exact identity
  have hid := bump_E0_identity (α := α) hb hβ K B δ M c ξ hδ0 hδ1 hbδ hM hc2 hξ h
  set E : ℝ → ℂ := fun τ => Complex.exp (Complex.I * ((c * L * τ : ℝ) : ℂ)) with hE
  have hEc : Continuous E := by simp only [hE]; fun_prop
  have hkc : Continuous (kernelAmp c) := (haenv c hc2).1.continuous
  have hE0c : Continuous fun τ : ℝ => bumpE0 c τ := by unfold bumpE0; exact hkc.sub continuous_const
  have hE0n : ∀ τ : ℝ, ‖bumpE0 c τ‖ ≤ 2 := by
    intro τ
    unfold bumpE0
    have := norm_kernelAmp_le_one hc0 τ
    calc _ ≤ ‖kernelAmp c τ‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 := by simp; linarith
  have hiE : Integrable fun τ : ℝ => bumpE0 c τ * (E τ * Φ τ) := by
    refine (hΦi.norm.const_mul 2).mono' (hE0c.mul (hEc.mul hΦc)).aestronglyMeasurable (ae_of_all _ fun τ => ?_)
    rw [norm_mul, norm_mul]
    have : ‖E τ‖ = 1 := Complex.norm_exp_I_mul_ofReal _
    rw [this, one_mul]
    exact mul_le_mul_of_nonneg_right (hE0n τ) (norm_nonneg _)
  obtain ⟨hiR, hremb⟩ := rem_part_integral_bound (S := S) (a := a) (L := L) (Q := Cd * M * bumpLambda α δ) hΦc hc1 hδ0 ha0 hsc
    hCR hΦd (hrem c hc1) (hE0c.sub (continuous_polyPart S a c))
  have hiP : Integrable fun τ : ℝ => polyPart S a c τ * (E τ * Φ τ) := by
    refine (hiE.sub hiR).congr (ae_of_all _ fun τ => ?_)
    simp only [Pi.sub_apply]; ring
  have hsplit : ∫ τ : ℝ, bumpE0 c τ * E τ * Φ τ =
      (∫ τ : ℝ, polyPart S a c τ * (E τ * Φ τ)) +
        ∫ τ : ℝ, (bumpE0 c τ - polyPart S a c τ) * (E τ * Φ τ) := by
    rw [← integral_add hiP hiR]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only []; ring
  have hpoly := poly_part_integral_bound S a hS h hb hδ0 hbδ (by linarith) hc1 L hLpos hU1 hu hMl hder' hint_k
  rw [hid, hsplit, mul_add]
  refine (norm_add_le _ _).trans ?_
  have hW : 0 ≤ ((c ^ 2)⁻¹) * L⁻¹ + ((c ^ 3)⁻¹) * (L ^ 3)⁻¹ := by positivity
  have hb1 : ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ τ : ℝ, polyPart S a c τ * (E τ * Φ τ)‖ ≤
      (A * Kb * U ^ 9 + Cr) * Mloc * (((c ^ 2)⁻¹) * L⁻¹ + ((c ^ 3)⁻¹) * (L ^ 3)⁻¹) := by
    refine hpoly.trans ?_
    have : A * Kb * U ^ 9 * Mloc * (((c ^ 2)⁻¹) * L⁻¹ + ((c ^ 3)⁻¹) * (L ^ 3)⁻¹) ≤
        (A * Kb * U ^ 9 + Cr) * Mloc * (((c ^ 2)⁻¹) * L⁻¹ + ((c ^ 3)⁻¹) * (L ^ 3)⁻¹) := by
      have : 0 ≤ Cr * Mloc * (((c ^ 2)⁻¹) * L⁻¹ + ((c ^ 3)⁻¹) * (L ^ 3)⁻¹) := by positivity
      nlinarith
    exact this
  have hb2 : ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ τ : ℝ, (bumpE0 c τ - polyPart S a c τ) * (E τ * Φ τ)‖ ≤
      (A * Kb * U ^ 9 + Cr) * M * bumpLambda α δ * ((c ^ 2)⁻¹ * δ) := by
    refine hremb.trans ?_
    have e : (1 / (2 * Real.pi)) * CR * (Cd * M * bumpLambda α δ) * ((min 1 a0) ^ 21)⁻¹ * I2 * (a0 ^ 2)⁻¹ * ((c ^ 2)⁻¹ * δ) =
        Cr * M * bumpLambda α δ * ((c ^ 2)⁻¹ * δ) := by rw [hCr]; ring
    rw [e]
    have : 0 ≤ A * Kb * U ^ 9 * M * bumpLambda α δ * ((c ^ 2)⁻¹ * δ) := by positivity
    nlinarith
  linarith

/-- info: 'FormalResearch.SignUncertainty.bump_weighted_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_weighted_local

/-- info: 'FormalResearch.SignUncertainty.poly_part_integral_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms poly_part_integral_bound

/-- info: 'FormalResearch.SignUncertainty.rem_part_integral_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rem_part_integral_bound

end FormalResearch.SignUncertainty
