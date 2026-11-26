module

public import FormalResearch.SignUncertainty.UctBumpRefl
public import FormalResearch.SignUncertainty.UctBumpMain
public import FormalResearch.SignUncertainty.UctBumpWeightedLocal
public import FormalResearch.SignUncertainty.UctBumpWeightedFar

/-!
# `fct:bump-5` (Lemma FCT.7) items (1), (2) and (3) (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma `fct:bump-5`: the bump `B` with `supp B ⊂ [3δ_L/2, ∞)` and the symbol bounds `(fct:B-sym)`
is a `BumpProfile (3/2) δ_L M α β K B`, and `δ_L ≍ c^{-1/2}` (`a₀ ≤ c^{1/2} δ_L`).

* `fct_bump5_main_small` (1), main density for `L ≤ 3δ_L/4`: `|Δh_main(L)| ≤ C M e^{-c₁ c^{1/4}}`.
* `fct_bump5_refl` (1), reflected density: `|Δh_refl(L)| ≤ C M e^{-c₁ c^{1/2}} min(1, L_+^{-2})`.
* (1), the common bounds of `uct:bump-symbol` (`bump_laplace_decay`, `bump_stripAdmissFull`) and (2), the precision inversion on `L ≥ 3δ_L/4`
  (`bump_weighted_local` with `b = 3/2`), are instances of the theorems named.

* `fct_bump5_far` (3), the far band `L ≥ ¼ log c` (`c ≥ e⁸`): `|Δh_main(L) - c⁻¹B(L)| ≤ C M c⁻² L⁻²` for `α ≤ 4` (`bump_weighted_far`).

Class: proved, no hypotheses beyond those displayed.
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

lemma pow_exp_absorb (n : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x → x ^ n * Real.exp (-(κ * x)) ≤ C * Real.exp (-(κ / 2 * x)) := by
  refine ⟨(n.factorial : ℝ) * (2 / κ) ^ n, by positivity, fun x hx => ?_⟩
  have h1 := Real.pow_div_factorial_le_exp (κ / 2 * x) (by positivity) n
  have e : Real.exp (-(κ * x)) = Real.exp (-(κ / 2 * x)) * Real.exp (-(κ / 2 * x)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hE : 0 < Real.exp (κ / 2 * x) := Real.exp_pos _
  have h2 : x ^ n * Real.exp (-(κ / 2 * x)) ≤ (n.factorial : ℝ) * (2 / κ) ^ n := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hE]
    have hf : (0 : ℝ) < n.factorial := by positivity
    have h3 : (κ / 2 * x) ^ n ≤ n.factorial * Real.exp (κ / 2 * x) := by
      rw [div_le_iff₀ hf] at h1; linarith
    have h4 : (κ / 2) ^ n * x ^ n ≤ n.factorial * Real.exp (κ / 2 * x) := by rw [← mul_pow]; exact h3
    have h5 : (2 / κ) ^ n * (κ / 2) ^ n = 1 := by rw [← mul_pow]; field_simp; simp
    calc x ^ n = ((2 / κ) ^ n * (κ / 2) ^ n) * x ^ n := by rw [h5, one_mul]
      _ = (2 / κ) ^ n * ((κ / 2) ^ n * x ^ n) := by ring
      _ ≤ (2 / κ) ^ n * (n.factorial * Real.exp (κ / 2 * x)) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = _ := by ring
  rw [e]
  calc x ^ n * (Real.exp (-(κ / 2 * x)) * Real.exp (-(κ / 2 * x)))
      = (x ^ n * Real.exp (-(κ / 2 * x))) * Real.exp (-(κ / 2 * x)) := by ring
    _ ≤ ((n.factorial : ℝ) * (2 / κ) ^ n) * Real.exp (-(κ / 2 * x)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le

lemma bumpLambda_le_pow (α : ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    bumpLambda α δ ≤ 2 * (δ⁻¹) ^ (⌈|α - 1|⌉₊ + 1) := by
  have hi : 1 ≤ δ⁻¹ := one_le_inv_iff₀.mpr ⟨hδ0, hδ1⟩
  have h1 : 1 ≤ (δ⁻¹) ^ (⌈|α - 1|⌉₊ + 1) := one_le_pow₀ hi
  unfold bumpLambda
  split_ifs with hα
  · have h2 : Real.log (1 / δ) ≤ 1 / δ - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h3 : δ⁻¹ ≤ (δ⁻¹) ^ (⌈|α - 1|⌉₊ + 1) := by
      calc δ⁻¹ = (δ⁻¹) ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ hi (by omega)
    rw [one_div] at h2 ⊢
    linarith
  · have h2 : δ ^ (1 - α) = (δ⁻¹) ^ (α - 1) := by
      rw [Real.inv_rpow hδ0.le, ← Real.rpow_neg hδ0.le]; ring_nf
    have h3 : (δ⁻¹) ^ (α - 1) ≤ (δ⁻¹) ^ ((⌈|α - 1|⌉₊ + 1 : ℕ) : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le hi ?_
      have := Nat.le_ceil |α - 1|
      push_cast
      linarith [le_abs_self (α - 1)]
    rw [h2]
    rw [Real.rpow_natCast] at h3
    linarith

lemma rpow_three_halves {t : ℝ} (ht : 0 < t) : (t ^ 2) ^ ((3 : ℝ) / 2) = t ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  norm_num

theorem fct_bump5_main_small {α β : ℝ} (hβ : 3 / 2 ≤ β) (K : ℕ → ℝ) {a0 : ℝ} (ha0 : 0 < a0) :
    ∃ C c1 : ℝ, 0 ≤ C ∧ 0 < c1 ∧ ∀ (B : ℝ → ℝ) (δ M c ξ : ℝ), 0 < δ → δ ≤ 1 → 3 / 2 * δ ≤ 1 → 0 ≤ M → 1 ≤ c →
      a0 ≤ Real.sqrt c * δ → 0 < ξ → Real.log (Real.pi ^ 2 * ξ) ≤ 3 / 2 * δ / 2 →
      BumpProfile (3 / 2) δ M α β K B →
        ‖bumpHmain c B ξ‖ ≤ C * M * Real.exp (-(c1 * Real.sqrt (Real.sqrt c))) := by
  obtain ⟨κ, C0, hκ, hC0, hmain⟩ := bump_main_density (α := α) (b := 3 / 2) (by norm_num) hβ K
  set n : ℕ := ⌈|α - 1|⌉₊ + 1 with hn
  set κ' : ℝ := κ * a0 ^ (3 / 2 : ℝ) with hκ'
  have hκ'0 : 0 < κ' := by positivity
  obtain ⟨Ca, hCa, habs⟩ := pow_exp_absorb (2 * n) hκ'0
  refine ⟨C0 * a0⁻¹ * 2 * (a0⁻¹) ^ n * Ca, κ' / 2, by positivity, by positivity, ?_⟩
  intro B δ M c ξ hδ0 hδ1 hbδ hM hc hsc hξ hL h
  have hc0 : 0 < c := by linarith
  set t : ℝ := Real.sqrt (Real.sqrt c) with ht
  have hs0 : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
  have ht0 : 0 < t := Real.sqrt_pos.mpr hs0
  have ht2 : t ^ 2 = Real.sqrt c := Real.sq_sqrt hs0.le
  have ht4 : t ^ 4 = c := by
    have : t ^ 4 = (t ^ 2) ^ 2 := by ring
    rw [this, ht2, Real.sq_sqrt hc0.le]
  have hs1 : 1 ≤ Real.sqrt c := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hc
  have ht1 : 1 ≤ t := by
    by_contra hcon
    have : t ^ 2 < 1 := by nlinarith
    linarith
  have hsδ : a0 ≤ t ^ 2 * δ := by rw [ht2]; exact hsc
  have h1 := hmain B δ M c ξ hδ0 hδ1 hbδ hM hc hξ hL h
  -- pieces
  have hcδ : a0 ≤ c * δ := by
    have : c * δ = t ^ 2 * (t ^ 2 * δ) := by rw [← ht4]; ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_right (by nlinarith : (1 : ℝ) ≤ t ^ 2) (by positivity : (0 : ℝ) ≤ t ^ 2 * δ)]
  have hinv : (c * δ)⁻¹ ≤ a0⁻¹ := inv_anti₀ ha0 hcδ
  have hδinv : δ⁻¹ ≤ t ^ 2 / a0 := by
    rw [inv_le_comm₀ hδ0 (by positivity), inv_div, div_le_iff₀ (by positivity)]
    linarith
  have hΛ : bumpLambda α δ ≤ 2 * (t ^ 2 / a0) ^ n :=
    (bumpLambda_le_pow α hδ0 hδ1).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hδinv _) (by norm_num))
  have hδ32 : a0 ^ (3 / 2 : ℝ) / t ^ 3 ≤ δ ^ (3 / 2 : ℝ) := by
    have hδge : a0 / t ^ 2 ≤ δ := by rw [div_le_iff₀ (by positivity)]; linarith
    have := Real.rpow_le_rpow (by positivity) hδge (by norm_num : (0 : ℝ) ≤ 3 / 2)
    rwa [Real.div_rpow ha0.le (by positivity), rpow_three_halves ht0] at this
  have hexp : κ' * t ≤ κ * c * δ ^ (3 / 2 : ℝ) := by
    have : κ * c * δ ^ (3 / 2 : ℝ) ≥ κ * c * (a0 ^ (3 / 2 : ℝ) / t ^ 3) :=
      mul_le_mul_of_nonneg_left hδ32 (by positivity)
    refine le_trans (le_of_eq ?_) this
    rw [← ht4, hκ']; field_simp
  have hE : Real.exp (-(κ * c * δ ^ (3 / 2 : ℝ))) ≤ Real.exp (-(κ' * t)) := Real.exp_le_exp.mpr (by linarith)
  refine h1.trans ?_
  have hΛ0 : 0 ≤ bumpLambda α δ := by linarith [one_le_bumpLambda (α := α) hδ0 hδ1]
  have habs' := habs t ht0.le
  have e : (t ^ 2 / a0) ^ n = (a0⁻¹) ^ n * t ^ (2 * n) := by
    rw [div_eq_inv_mul, mul_pow, ← pow_mul]
  calc C0 * M * (c * δ)⁻¹ * bumpLambda α δ * Real.exp (-(κ * c * δ ^ (3 / 2 : ℝ)))
      ≤ C0 * M * a0⁻¹ * (2 * (t ^ 2 / a0) ^ n) * Real.exp (-(κ' * t)) := by
        gcongr
    _ = (C0 * a0⁻¹ * 2 * (a0⁻¹) ^ n) * M * (t ^ (2 * n) * Real.exp (-(κ' * t))) := by rw [e]; ring
    _ ≤ (C0 * a0⁻¹ * 2 * (a0⁻¹) ^ n) * M * (Ca * Real.exp (-(κ' / 2 * t))) := by
        gcongr
    _ = _ := by ring

theorem fct_bump5_refl {α β : ℝ} (hβ : 3 / 2 ≤ β) (K : ℕ → ℝ) {a0 : ℝ} (ha0 : 0 < a0) :
    ∃ C c1 : ℝ, 0 ≤ C ∧ 0 < c1 ∧ ∀ (B : ℝ → ℝ) (δ M c ξ : ℝ), 0 < δ → δ ≤ 1 → 3 / 2 * δ ≤ 1 → 0 ≤ M → 2 ≤ c →
      1 ≤ a0 * Real.sqrt c → a0 ≤ Real.sqrt c * δ → 0 < ξ → BumpProfile (3 / 2) δ M α β K B →
        ‖bumpHrefl c B ξ‖ ≤ C * M * Real.exp (-(c1 * Real.sqrt c)) ∧
        (1 ≤ Real.log (Real.pi ^ 2 * ξ) → ‖bumpHrefl c B ξ‖ ≤
          C * M * Real.exp (-(c1 * Real.sqrt c)) / Real.log (Real.pi ^ 2 * ξ) ^ 2) := by
  obtain ⟨C0, hC0, hrefl⟩ := bump_refl_density (α := α) (b := 3 / 2) (by norm_num) hβ K
  set n : ℕ := ⌈|α - 1|⌉₊ + 1 with hn
  set κ' : ℝ := 3 / 4 * a0 with hκ'
  have hκ'0 : 0 < κ' := by positivity
  obtain ⟨Ca, hCa, habs⟩ := pow_exp_absorb n hκ'0
  refine ⟨C0 * 2 * (a0⁻¹) ^ n * Ca, κ' / 2, by positivity, by positivity, ?_⟩
  intro B δ M c ξ hδ0 hδ1 hbδ hM hc2 hca hsc hξ h
  have hc0 : 0 < c := by linarith
  set s : ℝ := Real.sqrt c with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hc0
  have hs2 : s ^ 2 = c := Real.sq_sqrt hc0.le
  have hcδ : a0 * s ≤ c * δ := by
    have : c * δ = s * (s * δ) := by rw [← hs2]; ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hsc hs0.le]
  have hcδ1 : 1 ≤ c * δ := by nlinarith
  obtain ⟨h1, h2⟩ := hrefl B δ M c ξ hδ0 hδ1 hbδ hM hc2 hcδ1 hξ h
  have hinv : (c * δ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hcδ1
  have hδinv : δ⁻¹ ≤ s / a0 := by
    rw [inv_le_comm₀ hδ0 (by positivity), inv_div, div_le_iff₀ (by positivity)]
    linarith
  have hΛ : bumpLambda α δ ≤ 2 * (s / a0) ^ n :=
    (bumpLambda_le_pow α hδ0 hδ1).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hδinv _) (by norm_num))
  have hΛ0 : 0 ≤ bumpLambda α δ := by linarith [one_le_bumpLambda (α := α) hδ0 hδ1]
  have hE : Real.exp (-(3 / 2 * c * δ / 2)) ≤ Real.exp (-(κ' * s)) := by
    refine Real.exp_le_exp.mpr ?_
    rw [hκ']; nlinarith
  have e : (s / a0) ^ n = (a0⁻¹) ^ n * s ^ n := by rw [div_eq_inv_mul, mul_pow]
  have habs' := habs s hs0.le
  have hbound : C0 * M * (c * δ)⁻¹ * bumpLambda α δ * Real.exp (-(3 / 2 * c * δ / 2)) ≤
      (C0 * 2 * (a0⁻¹) ^ n * Ca) * M * Real.exp (-(κ' / 2 * s)) := by
    calc C0 * M * (c * δ)⁻¹ * bumpLambda α δ * Real.exp (-(3 / 2 * c * δ / 2))
        ≤ C0 * M * 1 * (2 * (s / a0) ^ n) * Real.exp (-(κ' * s)) := by gcongr
      _ = (C0 * 2 * (a0⁻¹) ^ n) * M * (s ^ n * Real.exp (-(κ' * s))) := by rw [e]; ring
      _ ≤ (C0 * 2 * (a0⁻¹) ^ n) * M * (Ca * Real.exp (-(κ' / 2 * s))) := by gcongr
      _ = _ := by ring
  refine ⟨h1.trans hbound, fun hL => (h2 hL).trans ?_⟩
  have hLp : 0 < Real.log (Real.pi ^ 2 * ξ) ^ 2 := by positivity
  have : C0 * M * (c * δ)⁻¹ * bumpLambda α δ * Real.exp (-(3 / 2 * c * δ / 2)) / Real.log (Real.pi ^ 2 * ξ) ^ 2 ≤
      (C0 * 2 * (a0⁻¹) ^ n * Ca) * M * Real.exp (-(κ' / 2 * s)) / Real.log (Real.pi ^ 2 * ξ) ^ 2 :=
    div_le_div_of_nonneg_right hbound hLp.le
  exact this

lemma iteratedDeriv_zero_of_support {B : ℝ → ℝ} {c : ℝ} (hs : ∀ x : ℝ, x < c → B x = 0) (j : ℕ) {x : ℝ}
    (hx : x < c) : iteratedDeriv j B x = 0 := by
  have hev : B =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hx] with y hy using hs y hy
  rw [hev.iteratedDeriv_eq]
  cases j with
  | zero => simp
  | succ n => simp

/-- The symbol bounds `(fct:B-sym)` for `B` supported in `[3δ_L/2, ∞)`. -/
structure BSym (δ M α β : ℝ) (Kc : ℕ → ℝ) (B : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) B
  support : ∀ x : ℝ, x < 3 / 2 * δ → B x = 0
  K_nonneg : ∀ r : ℕ, 0 ≤ Kc r
  bound : ∀ (r : ℕ) (x : ℝ), 3 / 2 * δ ≤ x →
    |iteratedDeriv r B x| ≤ Kc r * M * min (x ^ (-α - (r : ℝ))) (x ^ (-β - (r : ℝ)))

lemma BSym.profile {δ M α β : ℝ} {Kc : ℕ → ℝ} {B : ℝ → ℝ} (h : BSym δ M α β Kc B) (hM : 0 ≤ M) :
    BumpProfile (3 / 2) δ M α β Kc B where
  smooth := h.smooth
  support := h.support
  near := fun k x hx _ => (h.bound k x hx).trans
    (mul_le_mul_of_nonneg_left (min_le_left _ _) (mul_nonneg (h.K_nonneg k) hM))
  far := fun k x hx1 => by
    have hδ : 3 / 2 * δ ≤ x ∨ x < 3 / 2 * δ := le_or_gt _ _
    rcases hδ with hδ | hδ
    · exact (h.bound k x hδ).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (mul_nonneg (h.K_nonneg k) hM))
    · rw [iteratedDeriv_zero_of_support h.support k hδ]
      simp only [abs_zero]
      exact mul_nonneg (mul_nonneg (h.K_nonneg k) hM) (Real.rpow_nonneg (by linarith) _)

/-- `fct:bump-5` (2) with `M_loc(L) = M L^{-α}` (the global symbol bound `(fct:B-sym)`). -/
theorem fct_bump5_mid {α β : ℝ} (hβ : 3 / 2 ≤ β) (Kc : ℕ → ℝ) {a0 : ℝ} (ha0 : 0 < a0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ → ℝ) (δ M c ξ : ℝ), 0 < δ → δ ≤ 1 → 3 / 2 * δ ≤ 1 → 0 ≤ M → 2 ≤ c →
      a0 ≤ Real.sqrt c * δ → 0 < ξ → 3 / 2 * δ / 2 ≤ Real.log (Real.pi ^ 2 * ξ) → BSym δ M α β Kc B →
        ‖bumpHmain c B ξ - ((c⁻¹ * B (Real.log (Real.pi ^ 2 * ξ)) : ℝ) : ℂ)‖ ≤
          C * (M * Real.log (Real.pi ^ 2 * ξ) ^ (-α)) * (((c ^ 2)⁻¹) * (Real.log (Real.pi ^ 2 * ξ))⁻¹ +
            ((c ^ 3)⁻¹) * ((Real.log (Real.pi ^ 2 * ξ)) ^ 3)⁻¹) +
          C * M * bumpLambda α δ * ((c ^ 2)⁻¹ * δ) := by
  obtain ⟨C, hC, hmain⟩ := bump_weighted_local (α := α) (b := 3 / 2) (by norm_num) hβ Kc Kc ha0
  refine ⟨C, hC, fun B δ M c ξ hδ0 hδ1 hbδ hM hc2 hsc hξ hL hsym => ?_⟩
  set L : ℝ := Real.log (Real.pi ^ 2 * ξ) with hLdef
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hMl : 0 ≤ M * L ^ (-α) := mul_nonneg hM (Real.rpow_nonneg hLpos.le _)
  refine hmain B δ M (M * L ^ (-α)) c ξ hδ0 hδ1 hbδ hM hMl hc2 hsc hξ hL ?_ (hsym.profile hM)
  intro k hk1 hk9
  rcases lt_or_ge L (3 / 2 * δ) with hlt | hge
  · rw [iteratedDeriv_zero_of_support hsym.support k hlt]
    simp only [abs_zero]
    exact div_nonneg (mul_nonneg (hsym.K_nonneg k) hMl) (by positivity)
  · refine (hsym.bound k L hge).trans ?_
    refine (mul_le_mul_of_nonneg_left (min_le_left _ _) (mul_nonneg (hsym.K_nonneg k) hM)).trans (le_of_eq ?_)
    rw [sub_eq_add_neg (-α), Real.rpow_add hLpos]
    simp only [Real.rpow_neg hLpos.le, Real.rpow_natCast]
    rw [← hLdef]
    field_simp

/-- `fct:bump-5` (3), the far band `L ≥ ¼ log c` (`c ≥ e⁸`, so `L ≥ 2`): for `α ≤ 4` (the paper's `α ≤ 7/2` included) the correction `c⁻²δ_L^{3-α}` of `(fct:bump-far-5)`
is absorbed and `|Δh_main(L) - c⁻¹B(L)| ≤ C M c⁻² L⁻²`; this implies the displayed `C M (1 + c⁻²δ_L^{3-α}) c⁻² L⁻²`. -/
theorem fct_bump5_far {α β : ℝ} (hα : α ≤ 4) (hβ : 3 / 2 ≤ β) (Kc : ℕ → ℝ) {a0 : ℝ} (ha0 : 0 < a0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ → ℝ) (δ M c ξ : ℝ), 0 < δ → δ ≤ 1 → 3 / 2 * δ ≤ 1 → 0 ≤ M → Real.exp 8 ≤ c →
      a0 ≤ Real.sqrt c * δ → 0 < ξ → Real.log c / 4 ≤ Real.log (Real.pi ^ 2 * ξ) → BSym δ M α β Kc B →
        ‖bumpHmain c B ξ - ((c⁻¹ * B (Real.log (Real.pi ^ 2 * ξ)) : ℝ) : ℂ)‖ ≤
          C * M * (c ^ 2)⁻¹ * ((Real.log (Real.pi ^ 2 * ξ)) ^ 2)⁻¹ := by
  obtain ⟨C, hC, hfar⟩ := bump_weighted_far (b := 3 / 2) (α := α) (β := β) (by norm_num) hα Kc ha0
  refine ⟨C, hC, fun B δ M c ξ hδ0 hδ1 hbδ hM hc hsc hξ hL hsym => ?_⟩
  have hc0 : 0 < c := lt_of_lt_of_le (Real.exp_pos _) hc
  have hlogc : 8 ≤ Real.log c := (Real.le_log_iff_exp_le hc0).mpr hc
  have h64 : (64 : ℝ) ≤ c := by
    refine le_trans ?_ hc
    have h2 : (3 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith
    have : Real.exp 8 = Real.exp 2 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) h2 4]
  exact hfar B δ M c ξ hδ0 hδ1 hbδ hM h64 hξ (by linarith) hβ hsc (hsym.profile hM)

/-- info: 'FormalResearch.SignUncertainty.fct_bump5_main_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fct_bump5_main_small

/-- info: 'FormalResearch.SignUncertainty.fct_bump5_refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fct_bump5_refl

/-- info: 'FormalResearch.SignUncertainty.fct_bump5_mid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fct_bump5_mid

/-- info: 'FormalResearch.SignUncertainty.fct_bump5_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fct_bump5_far

/-- info: 'FormalResearch.SignUncertainty.BSym.profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BSym.profile

end FormalResearch.SignUncertainty
