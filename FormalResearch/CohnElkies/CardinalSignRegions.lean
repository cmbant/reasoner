module

public import FormalResearch.CohnElkies.AiryGaussianTransform
public import FormalResearch.CohnElkies.PreEdgeAndSplineFloor
public import FormalResearch.CohnElkies.CardinalAsymptotics

/-!
# Cardinal Source Sign Regions (`O.11p`) and Far-Half-Line Positivity (`O.11j`)

Formalizes `CFT/sign_uncertainty/paper/ce_o1_route.tex` (origin/main `9b51a651f`, lines 124–313):
1. **Part 1 — Exact Stieltjes Resolvent `H_{s,h}` & `J(w)` (`(ceo:O11j.8)`, `(ceo:O11j.coefficients)`).**
2. **Part 2 — Lemma `O.11p` (`ceo:O11p`, `(ceo:O11p.1)`–`(ceo:O11p.4)` & `(ceo:O11p.uniform)`).**
3. **Part 3 — Theorem `O.11j` (`ceo:O11j`, `(ceo:O11j.2)`, `(ceo:O11j.5)`–`(ceo:O11j.10)`).**
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.CohnElkies

open FormalResearch.Special

/-! ### Shared Helpers -/

private lemma compact_abs_bound {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b)) (hab : a ≤ b) :
    ∃ M > 0, ∀ u ∈ Icc a b, |f u| ≤ M := by
  obtain ⟨u, _, hu⟩ := isCompact_Icc.exists_isMaxOn ⟨a, left_mem_Icc.mpr hab⟩ hf.abs
  exact ⟨|f u| + 1, by positivity, fun x hx => (hu hx).trans (by linarith)⟩

private lemma airyZero_succ_ne {n m : ℕ} (h : n ≠ m) : airyZero (n + 1) ≠ airyZero (m + 1) := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact (airyZero_lt_of_lt (n := n + 1) (m := m + 1) (by omega) (by omega)).ne'
  · exact (airyZero_lt_of_lt (n := m + 1) (m := n + 1) (by omega) (by omega)).ne

private lemma pi_rpow_neg_half : π ^ (-(1 / 2 : ℝ)) = 1 / √π := by
  rw [Real.rpow_neg Real.pi_pos.le, ← one_div, Real.sqrt_eq_rpow]
private lemma pi_rpow_neg_half_sq : (π ^ (-(1 / 2 : ℝ))) ^ 2 = π⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]; norm_num; exact Real.rpow_neg_one _
private lemma rpow_sq_eq {x a : ℝ} (hx : 0 ≤ x) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; congr 1; ring
private lemma rpow_add_eq {x a b c : ℝ} (hx : 0 < x) (h : a + b = c) : x ^ a * x ^ b = x ^ c := by
  rw [← Real.rpow_add hx, h]
private lemma pi_x32_inv {x : ℝ} (hx : 0 < x) : π * x ^ (3 / 2 : ℝ) * (π⁻¹ * x ^ (-(3 / 2 : ℝ))) = 1 := by
  rw [show π * x ^ (3 / 2 : ℝ) * (π⁻¹ * x ^ (-(3 / 2 : ℝ))) = (π * π⁻¹) * (x ^ (3 / 2 : ℝ) * x ^ (-(3 / 2 : ℝ))) by ring,
    mul_inv_cancel₀ Real.pi_pos.ne', rpow_add_eq hx (by norm_num : (3 / 2 : ℝ) + -(3 / 2) = 0), Real.rpow_zero, mul_one]
private lemma rpow_mul_x_inv {x a : ℝ} (hx : 0 < x) : (x ^ a * x)⁻¹ = x ^ (-a - 1) := by
  have h : x ^ a * x = x ^ (a + 1) := by rw [Real.rpow_add hx, Real.rpow_one]
  rw [h, ← Real.rpow_neg hx.le]; congr 1; ring
private lemma sqrt_div_one_add_le {x : ℝ} (hx : 0 ≤ x) : √x / (1 + x) ≤ 1 / 2 := by
  rw [div_le_iff₀ (by linarith)]; nlinarith [sq_nonneg (√x - 1), Real.sq_sqrt hx]
private lemma one_sub_ceVarphiP_nonneg {p x : ℝ} (hx : 0 ≤ x) : 0 ≤ 1 - ceVarphiP p x := by
  unfold ceVarphiP; linarith [inv_le_one_of_one_le₀ (by linarith [Real.rpow_nonneg hx p] : 1 ≤ 1 + x ^ p)]
private lemma one_sub_ceVarphiP_le_min {p x : ℝ} (hx : 0 ≤ x) : 1 - ceVarphiP p x ≤ min 1 (x ^ p) := by
  unfold ceVarphiP; have hxp : 0 ≤ x ^ p := Real.rpow_nonneg hx p
  rw [show 1 - (1 + x ^ p)⁻¹ = x ^ p / (1 + x ^ p) by field_simp [show 1 + x ^ p ≠ 0 by linarith]; ring]
  exact le_min (div_le_one_of_le₀ (by linarith) (by linarith)) (div_le_self hxp (by linarith))

private lemma nat_rpow_le_unit_integral {a e : ℝ} (ha : 0 < a) (he : e ≤ 0) :
    (a + 1) ^ e ≤ ∫ x in a..(a + 1), x ^ e := by
  have hc : ContinuousOn (fun x : ℝ => x ^ e) (uIcc a (a + 1)) :=
    ContinuousOn.rpow_const continuousOn_id fun x hx => by
      rw [uIcc_of_le (by linarith)] at hx; exact Or.inl (by linarith [hx.1])
  rw [show (a + 1) ^ e = ∫ _ in a..(a + 1), (a + 1) ^ e by rw [intervalIntegral.integral_const, smul_eq_mul]; ring]
  exact intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const hc.intervalIntegrable
    fun x hx => Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hx.2 he

private lemma inv_rpow_bd {A h q : ℝ} (hA : 0 < A) (hh : 0 < h) (hq : 0 < q) (hle : h ≤ (4 * A) ^ (-q⁻¹)) :
    A * h ^ q ≤ 1 / 4 := by
  have h1 : h ^ q ≤ ((4 * A) ^ (-q⁻¹)) ^ q := Real.rpow_le_rpow hh.le hle hq.le
  rw [← Real.rpow_mul (by positivity), neg_mul, inv_mul_cancel₀ hq.ne', Real.rpow_neg_one] at h1
  exact (mul_le_mul_of_nonneg_left h1 hA.le).trans_eq (by field_simp [hA.ne'])

/-! ### Part 1: Exact Stieltjes Resolvent `H_{s,h}` & `J(w)` -/

/-- Exact Stieltjes resolvent `H_{s,h}(u) = ∑' n, (c_n / (1 + s h E_n)) L_n(u)` (`(ceo:O11j.8)`). -/
noncomputable def cardinalResolventH (s h u : ℝ) : ℝ :=
  ∑' n : ℕ, (cohnC airyDerivFirstZero n / (1 + s * h * cohnE n)) * cohnL n u

/-- Smooth Airy logarithmic-derivative ratio `J(w) = -r(a₁ + w⁻¹) / (a₁ + w⁻¹ - a₁')` (`(ceo:O11j.coefficients)`). -/
noncomputable def cardinalJ (w : ℝ) : ℝ :=
  -dslope airyLogDeriv airyDerivFirstZero (airyZero 1 + w⁻¹)

private lemma airyLogDeriv_a_zero : airyLogDeriv airyDerivFirstZero = 0 := by
  simp [airyLogDeriv, cohnM, airyDerivFirstZero_spec.2.2]
private lemma cohnE_nonneg' (n : ℕ) : 0 ≤ cohnE n := by
  unfold cohnE; linarith [airyZero_anti le_rfl (Nat.le_add_left 1 n)]
lemma cardinalJ_eq_of_ne {w : ℝ} (hza : airyZero 1 + w⁻¹ ≠ airyDerivFirstZero) :
    cardinalJ w = -airyLogDeriv (airyZero 1 + w⁻¹) / (airyZero 1 + w⁻¹ - airyDerivFirstZero) := by
  unfold cardinalJ; rw [dslope_of_ne _ hza, slope_def_field, airyLogDeriv_a_zero, sub_zero, neg_div]
lemma cardinalJ_self : cardinalJ (airyDerivFirstZero - airyZero 1)⁻¹ = -airyDerivFirstZero := by
  unfold cardinalJ
  rw [show airyZero 1 + ((airyDerivFirstZero - airyZero 1)⁻¹)⁻¹ = airyDerivFirstZero by rw [inv_inv]; ring,
    dslope_same, (hasDerivAt_airyLogDeriv airyDerivFirstZero_spec.1).deriv, airyLogDeriv_a_zero, zero_pow two_ne_zero, sub_zero]
lemma continuousOn_cardinalJ : ContinuousOn cardinalJ (Ioi (0 : ℝ)) := by
  have hd_cont : ContinuousOn (dslope airyLogDeriv airyDerivFirstZero) (Ioi (airyZero 1)) := by
    rw [continuousOn_dslope (Ioi_mem_nhds airyDerivFirstZero_spec.1)]
    exact ⟨fun _ hz => (hasDerivAt_airyLogDeriv (mem_Ioi.mp hz)).continuousAt.continuousWithinAt,
      (hasDerivAt_airyLogDeriv airyDerivFirstZero_spec.1).differentiableAt⟩
  exact (hd_cont.comp (continuousOn_const.add (continuousOn_inv₀.mono fun _ hw => (mem_Ioi.mp hw).ne'))
    fun _ hw => by change airyZero 1 < airyZero 1 + _⁻¹; linarith [inv_pos.mpr (mem_Ioi.mp hw)]).neg
lemma tendsto_cardinalJ_removable :
    Tendsto (fun w : ℝ => -airyLogDeriv (airyZero 1 + w⁻¹) / (airyZero 1 + w⁻¹ - airyDerivFirstZero))
      (𝓝[≠] (airyDerivFirstZero - airyZero 1)⁻¹) (𝓝 (cardinalJ (airyDerivFirstZero - airyZero 1)⁻¹)) := by
  have hw0 : 0 < (airyDerivFirstZero - airyZero 1)⁻¹ := inv_pos.mpr (sub_pos.mpr airyDerivFirstZero_spec.1)
  refine (((continuousOn_cardinalJ.continuousAt (Ioi_mem_nhds hw0)).tendsto).mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w (hw : w ≠ (airyDerivFirstZero - airyZero 1)⁻¹)
  exact cardinalJ_eq_of_ne fun h => hw (by rw [← inv_inv w, show w⁻¹ = airyDerivFirstZero - airyZero 1 by linarith])
private lemma summable_cohnL_sq (u : ℝ) : Summable (fun n : ℕ => cohnL n u ^ 2) := by
  by_cases hu : airyAi u = 0
  · obtain ⟨k, hk, rfl⟩ := exists_airyZero_eq hu (by by_contra h; exact absurd hu (airyAi_pos (not_le.mp h).le).ne')
    obtain ⟨n0, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    refine summable_of_ne_finset_zero (s := {n0}) fun n hn => ?_
    rw [cohnL_of_ne (airyZero_succ_ne (Ne.symm (Finset.mem_singleton.not.mp hn))), hu, zero_div, zero_pow two_ne_zero]
  · refine (((hasSum_inv_sq u hu).mul_left (airyAi u ^ 2)).congr_fun fun n => ?_).summable
    rw [cohnL_of_ne (fun h => hu (by rw [h]; exact airyAi_airyZero _)), div_pow]; ring

private lemma summable_abs_cohnC_mul_cohnL (u : ℝ) :
    Summable (fun n : ℕ => |cohnC airyDerivFirstZero n * cohnL n u|) := by
  have hc_sq : Summable (fun n : ℕ => cohnC airyDerivFirstZero n ^ 2) := by
    have h := hasSum_inv_sq airyDerivFirstZero (airyAi_ne_zero_of_deriv_zero airyDerivFirstZero_spec.2.2)
    rw [show cohnM airyDerivFirstZero = 0 by simp [cohnM, airyDerivFirstZero_spec.2.2], zero_pow two_ne_zero, zero_sub] at h
    exact (h.congr_fun fun n => by rw [cohnC, inv_pow]; ring).summable
  refine ((hc_sq.add (summable_cohnL_sq u)).div_const 2).of_nonneg_of_le (fun _ => abs_nonneg _) fun n => ?_
  nlinarith [sq_nonneg (|cohnC airyDerivFirstZero n| - |cohnL n u|), sq_abs (cohnC airyDerivFirstZero n),
    sq_abs (cohnL n u), abs_mul (cohnC airyDerivFirstZero n) (cohnL n u)]

private lemma resolvent_term_abs_le {s h : ℝ} (hs : 0 ≤ s) (hh : 0 ≤ h) (n : ℕ) (u : ℝ) :
    ‖(cohnC airyDerivFirstZero n / (1 + s * h * cohnE n)) * cohnL n u‖ ≤ |cohnC airyDerivFirstZero n * cohnL n u| := by
  have hden : 1 ≤ 1 + s * h * cohnE n := by linarith [mul_nonneg (mul_nonneg hs hh) (cohnE_nonneg' n)]
  rw [Real.norm_eq_abs, show (cohnC airyDerivFirstZero n / (1 + s * h * cohnE n)) * cohnL n u =
    (cohnC airyDerivFirstZero n * cohnL n u) / (1 + s * h * cohnE n) by ring, abs_div, abs_of_pos (by linarith : 0 < 1 + s * h * cohnE n)]
  exact div_le_self (abs_nonneg _) hden
private lemma cardinalResolventH_summable {s h : ℝ} (hs : 0 ≤ s) (hh : 0 ≤ h) (u : ℝ) :
    Summable (fun n : ℕ => (cohnC airyDerivFirstZero n / (1 + s * h * cohnE n)) * cohnL n u) :=
  (summable_abs_cohnC_mul_cohnL u).of_norm_bounded fun n => resolvent_term_abs_le hs hh n u
private lemma continuousOn_cardinalResolventH (h u : ℝ) (hh : 0 ≤ h) :
    ContinuousOn (fun s : ℝ => cardinalResolventH s h u) (Ici (0 : ℝ)) :=
  continuousOn_tsum (u := fun n => |cohnC airyDerivFirstZero n * cohnL n u|)
    (fun n => (continuousOn_const.div (continuousOn_const.add ((continuousOn_id.mul continuousOn_const).mul
      continuousOn_const)) fun s hs => ne_of_gt (by dsimp; linarith [mul_nonneg (mul_nonneg (mem_Ici.mp hs) hh) (cohnE_nonneg' n)])).mul
      continuousOn_const) (summable_abs_cohnC_mul_cohnL u) fun n _ hs => resolvent_term_abs_le (mem_Ici.mp hs) hh n u

private lemma cardinalResolventH_eq_closed_J {s h u : ℝ} (hs : 0 < s) (hh : 0 < h)
    (hza : airyZero 1 + (s * h)⁻¹ ≠ airyDerivFirstZero) (huz : u ≠ airyZero 1 + (s * h)⁻¹) :
    cardinalResolventH s h u =
      (((airyZero 1 + (s * h)⁻¹) - airyZero 1) / (u - (airyZero 1 + (s * h)⁻¹))) *
        (-cardinalHstar airyDerivFirstZero u - cardinalJ (s * h) * airyAi u) := by
  set a := airyDerivFirstZero; set z := airyZero 1 + (s * h)⁻¹
  have hAz : airyAi z ≠ 0 := airyAi_ne_zero_of_gt (by dsimp [z]; linarith [inv_pos.mpr (mul_pos hs hh)])
  have hsh_ne : s * h ≠ 0 := (mul_pos hs hh).ne'; have hza_ne : z - a ≠ 0 := sub_ne_zero.mpr hza
  have huz_ne : u - z ≠ 0 := sub_ne_zero.mpr huz; have hzu_ne : z - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huz)
  have hden_eq : ∀ n : ℕ, 1 + s * h * cohnE n = s * h * (z - airyZero (n + 1)) := fun n => by dsimp [z, cohnE]; field_simp [hsh_ne]; ring
  have hAa : airyAi a ≠ 0 := airyAi_ne_zero_of_deriv_zero airyDerivFirstZero_spec.2.2
  have hz1 : z - airyZero 1 = (s * h)⁻¹ := add_sub_cancel_left _ _
  have hinv_eq : (s * h * (z - a))⁻¹ = (z - airyZero 1) / (z - a) := by
    rw [show s * h * (z - a) = (z - a) / (z - airyZero 1) by rw [hz1]; field_simp [hsh_ne], inv_div]
  by_cases hAu : airyAi u = 0
  · obtain ⟨k, hk, rfl⟩ := exists_airyZero_eq hAu (by by_contra h; exact absurd hAu (airyAi_pos (not_le.mp h).le).ne')
    obtain ⟨n0, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hsingle := hasSum_single (f := fun n : ℕ => (cohnC a n / (1 + s * h * cohnE n)) * cohnL n (airyZero (n0 + 1))) n0
      fun n hn => by rw [cohnL_of_ne (airyZero_succ_ne (Ne.symm hn)), hAu, zero_div, mul_zero]
    have hua : airyZero (n0 + 1) ≠ a := fun h => hAa (by rw [← h]; exact hAu)
    have h1' : airyZero (n0 + 1) - a ≠ 0 := sub_ne_zero.mpr hua
    rw [cardinalResolventH, hsingle.tsum_eq, cohnL_self, hden_eq, cohnC, cardinalHstar_of_ne airyDerivFirstZero_spec.2.2 hua, hAu, mul_zero, sub_zero, hz1]
    change (airyZero (n0 + 1) - a)⁻¹ / (s * h * (z - airyZero (n0 + 1))) * airyAi' (airyZero (n0 + 1)) =
      (s * h)⁻¹ / (airyZero (n0 + 1) - z) * -(airyAi' (airyZero (n0 + 1)) / (airyZero (n0 + 1) - a))
    field_simp [h1', hzu_ne, huz_ne, hsh_ne]; ring
  · have hcomb := ((cardinal_Hstar_hasSum airyDerivFirstZero_spec.2.2 u).add ((cohnR2_hasSum hAz hAu (Ne.symm huz)).mul_left (airyAi u))).mul_left (s * h * (z - a))⁻¹
    have hterm : (fun n : ℕ => (s * h * (z - a))⁻¹ * (cohnC a n * cohnL n u + airyAi u * (1 / ((z - airyZero (n + 1)) * (u - airyZero (n + 1)))))) =
        fun n : ℕ => (cohnC a n / (1 + s * h * cohnE n)) * cohnL n u := funext fun n => by
      have hne : u ≠ airyZero (n + 1) := fun h => hAu (by rw [h]; exact airyAi_airyZero _)
      have h1 : airyZero (n + 1) - a ≠ 0 := sub_ne_zero.mpr (fun h => hAa (by rw [← h]; exact airyAi_airyZero _))
      have h2 : z - airyZero (n + 1) ≠ 0 := sub_ne_zero.mpr (fun h => hAz (by rw [h]; exact airyAi_airyZero _))
      rw [cohnL_of_ne hne, hden_eq, cohnC]; field_simp [h1, h2, sub_ne_zero.mpr hne, hsh_ne, hza_ne]; ring
    rw [hterm] at hcomb
    rw [cardinalResolventH, hcomb.tsum_eq, cardinalJ_eq_of_ne hza, show airyZero 1 + (s * h)⁻¹ = z from rfl, hinv_eq,
      show airyAi u * cohnR2 z u = (airyAi' u - airyLogDeriv z * airyAi u) / (z - u) by unfold cohnR2 airyLogDeriv cohnM; field_simp [hAu, hAz, hzu_ne]]
    generalize airyLogDeriv z = rz
    by_cases hua : u = a
    · subst hua; rw [cardinalHstar_self, airyDerivFirstZero_spec.2.2, zero_sub]; dsimp only [a] at *; field_simp [hza_ne, hzu_ne, huz_ne]; ring
    · have hua_ne : u - a ≠ 0 := sub_ne_zero.mpr hua
      rw [cardinalHstar_of_ne airyDerivFirstZero_spec.2.2 hua]; dsimp only [a] at *; field_simp [hza_ne, hzu_ne, huz_ne, hua_ne]; ring

/-- **Theorem O.11j (`(ceo:O11j.8)`), exact closed form of `H_{s,h}(u)`. -/
theorem cardinalResolventH_eq_closed {s h u : ℝ} (hs : 0 < s) (hh : 0 < h)
    (hza : airyZero 1 + (s * h)⁻¹ ≠ airyDerivFirstZero) (hua : u ≠ airyDerivFirstZero) (huz : u ≠ airyZero 1 + (s * h)⁻¹) :
    let a := airyDerivFirstZero; let z := airyZero 1 + (s * h)⁻¹
    cardinalResolventH s h u = (cardinalHstar a u - (airyAi' u - airyLogDeriv z * airyAi u) / (u - z)) / (s * h * (z - a)) ∧
    cardinalResolventH s h u = ((z - airyZero 1) / (u - z)) * (-(airyAi' u / (u - a)) + (airyLogDeriv z / (z - a)) * airyAi u) := by
  intro a z; have hsh_ne : s * h ≠ 0 := (mul_pos hs hh).ne'
  have hza_ne : z - a ≠ 0 := sub_ne_zero.mpr hza; have huz_ne : u - z ≠ 0 := sub_ne_zero.mpr huz; have hua_ne : u - a ≠ 0 := sub_ne_zero.mpr hua
  have hmain := cardinalResolventH_eq_closed_J hs hh hza huz; have hz1 : z - airyZero 1 = (s * h)⁻¹ := add_sub_cancel_left _ _
  rw [hmain, cardinalJ_eq_of_ne hza, show airyZero 1 + (s * h)⁻¹ = z from rfl, cardinalHstar_of_ne airyDerivFirstZero_spec.2.2 hua]
  generalize airyLogDeriv z = rz; dsimp only [a] at *
  refine ⟨?_, by ring⟩; rw [hz1]; field_simp [hsh_ne, hza_ne, huz_ne, hua_ne]; ring

/-- **Theorem O.11j (`(ceo:O11j.coefficients)`), `(X, Y)` decomposition of `H_{s,h}(u)`. -/
theorem cardinalResolventH_eq_XY {s h u : ℝ} (hs : 0 < s) (hh : 0 < h) (hu : u < airyZero 1) :
    let v := airyZero 1 - u
    cardinalResolventH s h u = (cardinalHstar airyDerivFirstZero u + √v * cardinalJ (s * h) * (airyAi u / √v)) / (1 + s * h * v) := by
  intro v; have hv_pos : 0 < v := sub_pos.mpr hu; have hsqrt_ne : √v ≠ 0 := (Real.sqrt_pos.mpr hv_pos).ne'
  have h_ne : ∀ s' > 0, airyZero 1 + (s' * h)⁻¹ ≠ airyDerivFirstZero →
      cardinalResolventH s' h u = (cardinalHstar airyDerivFirstZero u + √v * cardinalJ (s' * h) * (airyAi u / √v)) / (1 + s' * h * v) := by
    intro s' hs' hza; let z' := airyZero 1 + (s' * h)⁻¹
    have hcl := cardinalResolventH_eq_closed_J hs' hh hza (ne_of_lt (by linarith [inv_pos.mpr (mul_pos hs' hh)] : u < airyZero 1 + (s' * h)⁻¹))
    have hz1 : z' - airyZero 1 = (s' * h)⁻¹ := add_sub_cancel_left _ _
    have huz_eq : u - z' = -(1 + s' * h * v) / (s' * h) := by dsimp [z', v]; field_simp [(mul_pos hs' hh).ne']; ring
    rw [hcl]; change ((z' - airyZero 1) / (u - z')) * _ = _; rw [hz1, huz_eq]
    field_simp [(mul_pos hs' hh).ne', hsqrt_ne, (by positivity : 1 + s' * h * v ≠ 0)]; ring
  by_cases hza : airyZero 1 + (s * h)⁻¹ = airyDerivFirstZero
  · have hcont_rhs : ContinuousOn (fun s' : ℝ => (cardinalHstar airyDerivFirstZero u + √v * cardinalJ (s' * h) * (airyAi u / √v)) / (1 + s' * h * v)) (Ioi (0 : ℝ)) :=
      (continuousOn_const.add ((continuousOn_const.mul (continuousOn_cardinalJ.comp (continuousOn_id.mul continuousOn_const)
        fun _ hs' => mul_pos (mem_Ioi.mp hs') hh)).mul continuousOn_const)).div
        (continuousOn_const.add ((continuousOn_id.mul continuousOn_const).mul continuousOn_const))
        fun _ hs' => ne_of_gt (by have := mem_Ioi.mp hs'; positivity)
    have hev : ∀ᶠ s' in 𝓝[≠] s, cardinalResolventH s' h u =
        (cardinalHstar airyDerivFirstZero u + √v * cardinalJ (s' * h) * (airyAi u / √v)) / (1 + s' * h * v) := by
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hs), self_mem_nhdsWithin] with s' hs' hne
      exact h_ne s' hs' fun h0 => hne (mul_right_cancel₀ hh.ne' (inv_injective (by linarith)))
    exact tendsto_nhds_unique (((((continuousOn_cardinalResolventH h u hh.le).continuousAt (Ici_mem_nhds hs)).tendsto).mono_left nhdsWithin_le_nhds).congr' hev)
      (((hcont_rhs.continuousAt (Ioi_mem_nhds hs)).tendsto).mono_left nhdsWithin_le_nhds)
  · exact h_ne s hs hza

/-- Uniform asymptotic bound `|J(w) - √w| ≤ C w` for all `w > 0` (`ce_o1_route.tex` line 219). -/
theorem cardinalJ_asymptotic :
    ∃ C > 0, ∀ w > 0, |cardinalJ w - √w| ≤ C * w := by
  let a := airyDerivFirstZero; let a₁ := airyZero 1
  have ha1 : a₁ < a := airyDerivFirstZero_spec.1; have ha1_neg : a₁ < 0 := airyZero_neg 1
  let d : ℝ := a - a₁; have hd_pos : 0 < d := sub_pos.mpr ha1
  let W₁ : ℝ := max 2 (max (1 - a₁) (max (2 * d) (2 * (-a₁))))
  let w₁ : ℝ := W₁⁻¹; have hw₁_pos : 0 < w₁ := inv_pos.mpr (by positivity)
  have hw₁_le1 : w₁ ≤ 1 := inv_le_one_of_one_le₀ (le_max_left _ _ |>.trans' (by norm_num))
  have hsmall : ∀ w : ℝ, 0 < w → w ≤ w₁ → |cardinalJ w - √w| ≤ (1 + 2 * (-a₁) + 2 * d) * w := fun w hw hwle => by
    have hw_inv : W₁ ≤ w⁻¹ := (le_inv_comm₀ (by positivity) hw).mpr hwle; have hw1 : w ≤ 1 := hwle.trans hw₁_le1
    let z : ℝ := a₁ + w⁻¹
    have hz_pos : 0 < z := by dsimp [z]; linarith [le_max_left (1 - a₁) (max (2 * d) (2 * (-a₁))), le_max_right 2 (max (1 - a₁) (max (2 * d) (2 * (-a₁))))]
    have hza_half : w⁻¹ / 2 ≤ z - a := by dsimp [z]; linarith [le_max_left (2 * d) (2 * (-a₁)), le_max_right (1 - a₁) (max (2 * d) (2 * (-a₁))), le_max_right 2 (max (1 - a₁) (max (2 * d) (2 * (-a₁))))]
    have hza_pos : 0 < z - a := lt_of_lt_of_le (by positivity) hza_half
    have hlog_err : |-airyLogDeriv z - √z| ≤ 1 / (4 * z) := by
      have hpos : 0 < √(z + 1 / (2 * √z)) + √z := by positivity
      have hdiff : √(z + 1 / (2 * √z)) - √z = (1 / (2 * √z)) / (√(z + 1 / (2 * √z)) + √z) := by
        rw [eq_div_iff hpos.ne', mul_comm (√(z + 1 / (2 * √z)) - √z), ← sq_sub_sq, Real.sq_sqrt (by positivity), Real.sq_sqrt hz_pos.le]; ring
      rw [abs_of_pos (sub_pos.mpr (neg_airyLogDeriv_gt_sqrt hz_pos.le))]
      calc -airyLogDeriv z - √z ≤ √(z + 1 / (2 * √z)) - √z := by linarith [neg_airyLogDeriv_le hz_pos]
        _ ≤ (1 / (2 * √z)) / (2 * √z) := hdiff ▸ div_le_div_of_nonneg_left (by positivity) (by positivity)
            (by linarith [Real.sqrt_le_sqrt (le_add_of_nonneg_right (by positivity) : z ≤ z + 1 / (2 * √z))])
        _ = 1 / (4 * z) := by field_simp [Real.sq_sqrt hz_pos.le]; rw [Real.sq_sqrt hz_pos.le]; ring
    have hsqrt_diff : |√z - √(w⁻¹)| ≤ (-a₁) * √w := by
      have hpos : 0 < √z + √(w⁻¹) := by positivity
      have heq : √z - √(w⁻¹) = a₁ / (√z + √(w⁻¹)) := by
        rw [eq_div_iff hpos.ne', mul_comm (√z - √(w⁻¹)), ← sq_sub_sq, Real.sq_sqrt hz_pos.le, Real.sq_sqrt (inv_pos.mpr hw).le]; dsimp [z]; ring
      rw [heq, abs_div, abs_of_neg ha1_neg, abs_of_pos hpos, Real.sqrt_inv]
      exact (div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith [Real.sqrt_nonneg z])).trans_eq (div_inv_eq_mul _ _)
    have hinv_diff : |(z - a)⁻¹ - w| ≤ 2 * d * w ^ 2 := by
      have heq : (z - a)⁻¹ - w = d * w / (z - a) := by
        rw [eq_div_iff hza_pos.ne', sub_mul, inv_mul_cancel₀ hza_pos.ne']; dsimp [z, d]; rw [mul_sub, mul_add, mul_inv_cancel₀ hw.ne']; ring
      rw [heq, abs_div, abs_mul, abs_of_pos hd_pos, abs_of_pos hw, abs_of_pos hza_pos]
      exact (div_le_div_of_nonneg_left (by positivity) (by positivity) hza_half).trans_eq (by field_simp [hw.ne'])
    have hsplit : cardinalJ w - √w = (-airyLogDeriv z - √z) / (z - a) + (√z - √(w⁻¹)) / (z - a) + √(w⁻¹) * ((z - a)⁻¹ - w) := by
      rw [cardinalJ_eq_of_ne (by dsimp [z, a₁, a] at hza_pos ⊢; linarith),
        show √w = √(w⁻¹) * w by rw [Real.sqrt_inv, inv_mul_eq_div, eq_div_iff (Real.sqrt_pos.mpr hw).ne', Real.mul_self_sqrt hw.le]]
      simp only [div_eq_mul_inv]; ring
    have ht1 : |(-airyLogDeriv z - √z) / (z - a)| ≤ 1 * w := by
      have hz_half : w⁻¹ / 2 ≤ z := by dsimp [z]; linarith [le_max_right (2 * d) (2 * (-a₁)), le_max_right (1 - a₁) (max (2 * d) (2 * (-a₁))), le_max_right 2 (max (1 - a₁) (max (2 * d) (2 * (-a₁))))]
      rw [abs_div, abs_of_pos hza_pos]
      calc |(-airyLogDeriv z - √z)| / (z - a) ≤ (1 / (4 * z)) / (w⁻¹ / 2) := div_le_div₀ (by positivity) hlog_err (by positivity) hza_half
        _ ≤ (1 / (4 * (w⁻¹ / 2))) / (w⁻¹ / 2) := by gcongr
        _ = w ^ 2 := by field_simp [hw.ne']; ring
        _ ≤ 1 * w := by nlinarith
    have ht2 : |(√z - √(w⁻¹)) / (z - a)| ≤ 2 * (-a₁) * w := by
      rw [abs_div, abs_of_pos hza_pos]
      exact ((div_le_div₀ (mul_nonneg (by linarith) (Real.sqrt_nonneg w)) hsqrt_diff (by positivity) hza_half).trans_eq
        (by field_simp [hw.ne'])).trans (mul_le_of_le_one_right (mul_nonneg (by linarith) hw.le) (Real.sqrt_le_one.mpr hw1))
    have ht3 : |√(w⁻¹) * ((z - a)⁻¹ - w)| ≤ 2 * d * w := by
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_inv]
      have hw_sq : w * (√w)⁻¹ = √w := by rw [mul_inv_eq_iff_eq_mul₀ (Real.sqrt_pos.mpr hw).ne', Real.mul_self_sqrt hw.le]
      exact ((mul_le_mul_of_nonneg_left hinv_diff (by positivity)).trans_eq (by rw [show (√w)⁻¹ * (2 * d * w ^ 2) = 2 * d * w * (w * (√w)⁻¹) by ring, hw_sq])).trans
        (mul_le_of_le_one_right (by positivity) (Real.sqrt_le_one.mpr hw1))
    rw [hsplit]; exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans (by linarith)
  let q₁ : ℝ → ℝ := dslope airyAi a₁
  have hq₁_cont : Continuous q₁ := by
    rw [← continuousOn_univ, continuousOn_dslope univ_mem]; exact ⟨differentiable_airyAi.continuous.continuousOn, differentiable_airyAi a₁⟩
  have hq₁_a₁ : 0 < q₁ a₁ := by dsimp [q₁]; rw [dslope_same, deriv_airyAi]; exact airyAi'_first_pos
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp (hq₁_cont.continuousAt (x := a₁)) (q₁ a₁ / 2) (half_pos hq₁_a₁)
  let δ₀ : ℝ := min (min (δ / 2) 1) (d / 2); have hδ₀_pos : 0 < δ₀ := lt_min (lt_min (half_pos hδ_pos) one_pos) (half_pos hd_pos)
  let w₂ : ℝ := δ₀⁻¹; have hw₂_ge1 : 1 ≤ w₂ := one_le_inv₀ hδ₀_pos |>.mpr ((min_le_left _ _).trans (min_le_right _ _))
  obtain ⟨M_Ai', hM_Ai', hAi'_bd⟩ := compact_abs_bound continuous_airyAi'.continuousOn (by linarith : a₁ ≤ a₁ + 1)
  let C_lg : ℝ := 4 * M_Ai' / (d * airyAi' a₁) + 1
  have hlarge : ∀ w : ℝ, w₂ ≤ w → |cardinalJ w - √w| ≤ C_lg * w := fun w hw => by
    have hw_pos : 0 < w := lt_of_lt_of_le (by positivity) hw; have ht_pos : 0 < w⁻¹ := inv_pos.mpr hw_pos
    have ht_le : w⁻¹ ≤ δ₀ := inv_le_of_inv_le₀ hδ₀_pos hw; let z : ℝ := a₁ + w⁻¹
    have hz_dist : dist z a₁ < δ := by
      rw [Real.dist_eq, show z - a₁ = w⁻¹ by dsimp [z]; ring, abs_of_pos ht_pos]
      exact ht_le.trans_lt (by linarith [min_le_left (δ / 2) 1, min_le_left (min (δ / 2) 1) (d / 2)])
    have hq_ge : airyAi' a₁ / 2 ≤ q₁ z := by
      have h1 := abs_lt.mp (by simpa [Real.dist_eq] using hδ hz_dist)
      have hqa : q₁ a₁ = airyAi' a₁ := by dsimp [q₁]; rw [dslope_same, deriv_airyAi]
      linarith [h1.1]
    have hAi_ge : w⁻¹ * (airyAi' a₁ / 2) ≤ |airyAi z| := by
      have hAi_eq : airyAi z = w⁻¹ * q₁ z := by
        dsimp [q₁]; rw [dslope_of_ne _ (by dsimp [z]; linarith), slope_def_field, airyAi_airyZero, sub_zero, show z - a₁ = w⁻¹ by dsimp [z]; ring, mul_div_cancel₀ _ ht_pos.ne']
      rw [hAi_eq, abs_mul, abs_of_pos ht_pos, abs_of_pos (lt_of_lt_of_le (half_pos airyAi'_first_pos) hq_ge)]; exact mul_le_mul_of_nonneg_left hq_ge ht_pos.le
    have hJ_le : |cardinalJ w| ≤ 4 * M_Ai' / (d * airyAi' a₁) * w := by
      have hz_mem : z ∈ Icc a₁ (a₁ + 1) := ⟨by dsimp [z]; linarith, by dsimp [z]; linarith [min_le_right (δ / 2) 1, min_le_left (min (δ / 2) 1) (d / 2)]⟩
      have hza_abs : d / 2 ≤ |z - a| := by rw [abs_of_neg (by dsimp [z, d]; linarith [min_le_right (min (δ / 2) 1) (d / 2)])]; dsimp [z, d]; linarith [min_le_right (min (δ / 2) 1) (d / 2)]
      rw [cardinalJ_eq_of_ne (by dsimp [z, d]; linarith [min_le_right (min (δ / 2) 1) (d / 2)]), abs_div, abs_neg]
      unfold airyLogDeriv cohnM; rw [abs_div]; have hden1 : 0 < w⁻¹ * (airyAi' a₁ / 2) := mul_pos ht_pos (half_pos airyAi'_first_pos)
      exact (div_le_div₀ (div_nonneg hM_Ai'.le hden1.le) (div_le_div₀ hM_Ai'.le (hAi'_bd z hz_mem) hden1 hAi_ge) (half_pos hd_pos) hza_abs).trans_eq
        (by field_simp [hw_pos.ne', airyAi'_first_pos.ne', hd_pos.ne']; ring)
    have hsqrt_le : √w ≤ w := Real.sqrt_le_iff.mpr ⟨hw_pos.le, by nlinarith [hw₂_ge1.trans hw]⟩
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg (Real.sqrt_nonneg w)]; dsimp [C_lg]; linarith)
  obtain ⟨C_mid, hC_mid, hmid_bd⟩ := compact_abs_bound (f := fun w : ℝ => (cardinalJ w - √w) / w)
    (((continuousOn_cardinalJ.mono fun _ (hw : _ ∈ Icc w₁ (max w₁ w₂)) => lt_of_lt_of_le hw₁_pos hw.1).sub Real.continuous_sqrt.continuousOn).div
      continuousOn_id fun _ hw => (lt_of_lt_of_le hw₁_pos hw.1).ne') (le_max_left w₁ w₂)
  refine ⟨max (1 + 2 * (-a₁) + 2 * d) (max C_lg C_mid), lt_of_lt_of_le hC_mid ((le_max_right _ _).trans (le_max_right _ _)), fun w hw => ?_⟩
  rcases le_or_gt w w₁ with h1 | h1
  · exact (hsmall w hw h1).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hw.le)
  · rcases le_or_gt w₂ w with h2 | h2
    · exact (hlarge w h2).trans (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hw.le)
    · have hdiv := hmid_bd w ⟨h1.le, h2.le.trans (le_max_right _ _)⟩
      change |(cardinalJ w - √w) / w| ≤ C_mid at hdiv; rw [abs_div, abs_of_pos hw] at hdiv
      exact ((div_le_iff₀ hw).mp hdiv).trans (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hw.le)

/-- **Fubini representation:** `H_h^{(0)}(u) = ∫_0^∞ H_{s,h}(u) dμ_p(s)` for `p ∈ (1/2, 1)`, `h > 0`. -/
theorem cardinalH_untuned_eq_integral {p h : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hh : 0 < h) (u : ℝ) :
    cardinalH_untuned p h u = ∫ s in Ioi (0 : ℝ), cardinalResolventH s h u * fracMuDensity p s := by
  have hp01 : p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], hp.2⟩
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let F : ℕ → ℝ → ℝ := fun n s => ((cohnC airyDerivFirstZero n / (1 + s * h * cohnE n)) * cohnL n u) * fracMuDensity p s
  have hF_int : ∀ n : ℕ, Integrable (F n) ν := fun n => by
    have hst : IntegrableOn (fun s : ℝ => (1 + s * (h * cohnE n))⁻¹ * fracMuDensity p s) (Ioi (0 : ℝ)) := by
      refine (fracMuDensity_integrable hp01).mono'
        (((Measurable.aestronglyMeasurable (by fun_prop : Measurable fun s : ℝ => (1 + s * (h * cohnE n))⁻¹)).restrict).mul
          (fracMuDensity_integrable hp01).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
      rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (by linarith [mul_nonneg hs.le (mul_nonneg hh.le (cohnE_nonneg' n))])) (fracMuDensity_pos hp01 hs).le)]
      exact mul_le_of_le_one_left (fracMuDensity_pos hp01 hs).le (inv_le_one_of_one_le₀ (by linarith [mul_nonneg hs.le (mul_nonneg hh.le (cohnE_nonneg' n))]))
    exact (hst.const_mul (cohnC airyDerivFirstZero n * cohnL n u)).congr (ae_of_all _ fun s => by dsimp [F]; ring)
  have hF_norm_le : ∀ n : ℕ, ∫ s, ‖F n s‖ ∂ν ≤ |cohnC airyDerivFirstZero n * cohnL n u| := fun n => by
    refine (integral_mono_ae (hF_int n).norm ((fracMuDensity_integrable hp01).const_mul _) ?_).trans_eq
      (by rw [integral_const_mul, fracMuDensity_integral_one hp01, mul_one])
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
    rw [Real.norm_eq_abs, show F n s = (cohnC airyDerivFirstZero n / (1 + s * h * cohnE n)) * cohnL n u * fracMuDensity p s from rfl,
      abs_mul, abs_of_pos (fracMuDensity_pos hp01 hs)]
    exact mul_le_mul_of_nonneg_right ((Real.norm_eq_abs _).symm.trans_le (resolvent_term_abs_le hs.le hh.le n u)) (fracMuDensity_pos hp01 hs).le
  have h_enorm : ∑' n : ℕ, ∫⁻ s, ‖F n s‖ₑ ∂ν ≠ ⊤ := by
    have hsum_bd : Summable (fun n : ℕ => ∫ s, ‖F n s‖ ∂ν) :=
      (summable_abs_cohnC_mul_cohnL u).of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hF_norm_le
    rw [show (fun n : ℕ => ∫⁻ s, ‖F n s‖ₑ ∂ν) = fun n => ENNReal.ofReal (∫ s, ‖F n s‖ ∂ν) from
      funext fun n => (MeasureTheory.ofReal_integral_norm_eq_lintegral_eNorm (hF_int n)).symm,
      ← ENNReal.ofReal_tsum_of_nonneg (fun _ => integral_nonneg fun _ => norm_nonneg _) hsum_bd]
    exact ENNReal.ofReal_ne_top
  have h_lhs : (∫ s, ∑' n : ℕ, F n s ∂ν) = ∫ s in Ioi (0 : ℝ), cardinalResolventH s h u * fracMuDensity p s :=
    setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => by dsimp [F]; rw [cardinalResolventH, ← (cardinalResolventH_summable hs.le hh.le u).tsum_mul_right]
  have h_rhs : (∑' n : ℕ, ∫ s, F n s ∂ν) = cardinalH_untuned p h u := by
    unfold cardinalH_untuned; refine tsum_congr fun n => ?_
    rw [show (fun s => F n s) = fun s => (cohnC airyDerivFirstZero n * cohnL n u) * ((1 + s * (h * cohnE n))⁻¹ * fracMuDensity p s) by funext s; dsimp [F]; ring,
      integral_const_mul, fracMu_stieltjes_eq hp01 (mul_nonneg hh.le (cohnE_nonneg' n))]; ring
  rw [← h_lhs, integral_tsum (fun n => (hF_int n).aestronglyMeasurable) h_enorm, h_rhs]

/-! ### Part 2: Lemma `O.11p` (`ceo:O11p`) — All Three Regions Covering `u < a₁` -/

/-- Exact Pythagorean identity `g₁'(u) - f₁(u) = X(u)² + Y(u)² > 0` for `u < a₁` (`(ceo:O11p)`). -/
theorem o11p_B_eq_X_sq_add_Y_sq {u : ℝ} (hu : u < airyZero 1) :
    ceG1Deriv airyDerivFirstZero u - ceF1 u = cardinalHstar airyDerivFirstZero u ^ 2 + (airyAi u / √(airyZero 1 - u)) ^ 2 ∧
    0 < ceG1Deriv airyDerivFirstZero u - ceF1 u := by
  let a := airyDerivFirstZero; have hv_pos : 0 < airyZero 1 - u := sub_pos.mpr hu
  have hF : -ceF1 u = (airyAi u / √(airyZero 1 - u)) ^ 2 := by
    unfold ceF1; rw [dslope_of_ne _ hu.ne, slope_def_field, airyAi_airyZero, sub_zero, div_pow, Real.sq_sqrt hv_pos.le]
    field_simp [sub_ne_zero.mpr hu.ne, hv_pos.ne']; ring
  have hEq : ceG1Deriv a u - ceF1 u = cardinalHstar a u ^ 2 + (airyAi u / √(airyZero 1 - u)) ^ 2 := by
    have hG : ceG1Deriv a u = cardinalHstar a u ^ 2 := rfl; linarith
  refine ⟨hEq, ?_⟩; rw [hEq]; by_contra hle; push Not at hle
  have hX0 : cardinalHstar a u = 0 := by nlinarith [sq_nonneg (cardinalHstar a u), sq_nonneg (airyAi u / √(airyZero 1 - u))]
  have hY0 : airyAi u / √(airyZero 1 - u) = 0 := by nlinarith [sq_nonneg (cardinalHstar a u), sq_nonneg (airyAi u / √(airyZero 1 - u))]
  have hua : u ≠ a := (hu.trans airyDerivFirstZero_spec.1).ne
  rw [cardinalHstar_of_ne airyDerivFirstZero_spec.2.2 hua, div_eq_zero_iff] at hX0
  exact airyAi_ne_zero_of_deriv_zero (hX0.resolve_right (sub_ne_zero.mpr hua)) ((div_eq_zero_iff.mp hY0).resolve_right (Real.sqrt_pos.mpr hv_pos).ne')

private lemma sum_tail_cutoff_rpow_le {p : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) :
    ∃ C > 0, ∀ {h : ℝ}, 0 < h → h ≤ 1 →
      ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) * min 1 ((h * (2.85 * ((n + 2 : ℕ) : ℝ) ^ (2 / 3 : ℝ))) ^ p) ≤ C * √h := by
  have hp_pos : 0 < p := by linarith [hp.1]
  have hp_sub : 0 < 2 * p - 1 := by linarith [hp.1]
  refine ⟨2.85 ^ p * (3 / (2 * p - 1)) + 3 * (2 : ℝ) ^ (1 / 3 : ℝ), by positivity, fun {h} hh hh1 => ?_⟩
  let f : ℕ → ℝ := fun n => ((n + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) * min 1 ((h * (2.85 * ((n + 2 : ℕ) : ℝ) ^ (2 / 3 : ℝ))) ^ p)
  have hf_sum : Summable f := ((summable_nat_add_iff 2).mpr (Real.summable_nat_rpow_inv.mpr (by norm_num : 1 < (4 / 3 : ℝ)))).of_nonneg_of_le
    (fun _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (le_min zero_le_one (Real.rpow_nonneg (by positivity) _)))
    fun n => by dsimp [f]; rw [Real.rpow_neg (Nat.cast_nonneg _)]; exact mul_le_of_le_one_right (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (min_le_left _ _)
  let H : ℝ := h ^ (-(3 / 2 : ℝ)); have hH_ge1 : (1 : ℝ) ≤ H := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hh hh1 (by norm_num)
  let M : ℕ := Nat.floor H; have hM_ge1 : 1 ≤ M := Nat.le_floor (by norm_num; exact hH_ge1)
  have hpart1 : ∑ n ∈ Finset.range (M - 1), f n ≤ 2.85 ^ p * (3 / (2 * p - 1)) * √h := by
    have hstep : ∀ n ∈ Finset.range (M - 1), f n ≤ (2.85 * h) ^ p * ∫ x in (n + 1 : ℝ)..(n + 2 : ℝ), x ^ (2 * p / 3 - 4 / 3) := fun n _ => by
      have hmin_le : min 1 ((h * (2.85 * ((n + 2 : ℕ) : ℝ) ^ (2 / 3 : ℝ))) ^ p) ≤ (2.85 * h) ^ p * ((n + 2 : ℕ) : ℝ) ^ (2 * p / 3) :=
        (min_le_right _ _).trans_eq (by rw [show h * (2.85 * ((n + 2 : ℕ) : ℝ) ^ (2 / 3 : ℝ)) = (2.85 * h) * ((n + 2 : ℕ) : ℝ) ^ (2 / 3 : ℝ) by ring,
          Real.mul_rpow (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _), ← Real.rpow_mul (Nat.cast_nonneg _)]; congr 2; ring)
      have hint_mono : ((n + 2 : ℕ) : ℝ) ^ (2 * p / 3 - 4 / 3) ≤ ∫ x in (n + 1 : ℝ)..(n + 2 : ℝ), x ^ (2 * p / 3 - 4 / 3) := by
        rw [show ((n + 2 : ℕ) : ℝ) = (n + 1 : ℝ) + 1 by push_cast; ring, show (n + 2 : ℝ) = (n + 1 : ℝ) + 1 by ring]
        exact nat_rpow_le_unit_integral (by positivity) (by linarith [hp.2])
      exact ((mul_le_mul_of_nonneg_left hmin_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans_eq
        (by rw [mul_left_comm, rpow_add_eq (by positivity) (by ring : -(4 / 3 : ℝ) + 2 * p / 3 = 2 * p / 3 - 4 / 3)])).trans
        (mul_le_mul_of_nonneg_left hint_mono (Real.rpow_nonneg (by positivity) _))
    have hsum_int : ∑ n ∈ Finset.range (M - 1), ∫ x in (n + 1 : ℝ)..(n + 2 : ℝ), x ^ (2 * p / 3 - 4 / 3) = ∫ x in (1 : ℝ)..(M : ℝ), x ^ (2 * p / 3 - 4 / 3) := by
      have hadj := intervalIntegral.sum_integral_adjacent_intervals (f := fun x : ℝ => x ^ (2 * p / 3 - 4 / 3))
        (μ := volume) (a := fun k : ℕ => (k + 1 : ℝ)) (n := M - 1) fun k _ => intervalIntegral.intervalIntegrable_rpow' (by linarith [hp.1])
      simp only [Nat.cast_zero, zero_add] at hadj
      rw [show (((M - 1 : ℕ) : ℝ) + 1) = (M : ℝ) by rw [← Nat.cast_add_one, Nat.sub_add_cancel hM_ge1]] at hadj
      rw [← hadj]; exact Finset.sum_congr rfl fun k _ => by push_cast; rw [show (k : ℝ) + 1 + 1 = (k : ℝ) + 2 by ring]
    have hint_eval : ∫ x in (1 : ℝ)..(M : ℝ), x ^ (2 * p / 3 - 4 / 3) ≤ (3 / (2 * p - 1)) * H ^ ((2 * p - 1) / 3) := by
      have hpow_le : (M : ℝ) ^ ((2 * p - 1) / 3) ≤ H ^ ((2 * p - 1) / 3) := Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by positivity)) (by linarith [hp.1])
      rw [_root_.integral_rpow (Or.inl (by linarith [hp.1])), Real.one_rpow, show 2 * p / 3 - 4 / 3 + 1 = (2 * p - 1) / 3 by ring]
      exact (div_le_div_of_nonneg_right (by linarith) (by linarith [hp.1])).trans_eq (by rw [div_eq_mul_inv, inv_div, mul_comm])
    have hcomb : (2.85 * h) ^ p * ((3 / (2 * p - 1)) * H ^ ((2 * p - 1) / 3)) = 2.85 ^ p * (3 / (2 * p - 1)) * √h := by
      rw [Real.mul_rpow (by norm_num) hh.le, show H ^ ((2 * p - 1) / 3) = h ^ (1 / 2 - p) by dsimp [H]; rw [← Real.rpow_mul hh.le]; congr 1; ring]
      rw [show 2.85 ^ p * h ^ p * (3 / (2 * p - 1) * h ^ (1 / 2 - p)) = 2.85 ^ p * (3 / (2 * p - 1)) * (h ^ p * h ^ (1 / 2 - p)) by ring,
        rpow_add_eq hh (by ring : p + (1 / 2 - p) = 1 / 2), Real.sqrt_eq_rpow]
    exact ((Finset.sum_le_sum hstep).trans_eq (Finset.mul_sum _ _ _).symm).trans
      (by rw [hsum_int]; exact (mul_le_mul_of_nonneg_left hint_eval (Real.rpow_nonneg (by positivity) _)).trans_eq hcomb)
  have hpart2 : ∑' m : ℕ, f (m + (M - 1)) ≤ 3 * (2 : ℝ) ^ (1 / 3 : ℝ) * √h := by
    have hM_pos : (0 : ℝ) < M := by exact_mod_cast hM_ge1
    have hM_ge_H : H / 2 ≤ M := by linarith [Nat.lt_floor_add_one H, (by exact_mod_cast hM_ge1 : (1 : ℝ) ≤ M)]
    have hint_Ioi : IntegrableOn (fun x : ℝ => x ^ (-(4 / 3 : ℝ))) (Ioi (M : ℝ)) := integrableOn_Ioi_rpow_of_lt (by norm_num) hM_pos
    have hle_int : ∀ K : ℕ, ∑ m ∈ Finset.range K, f (m + (M - 1)) ≤ ∫ x in Ioi (M : ℝ), x ^ (-(4 / 3 : ℝ)) := fun K => by
      have hstep : ∀ m ∈ Finset.range K, f (m + (M - 1)) ≤ ∫ x in ((M : ℝ) + m)..((M : ℝ) + m + 1), x ^ (-(4 / 3 : ℝ)) := fun m _ =>
        ((mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg _) _) (min_le_left _ _)).trans_eq
          (by rw [show ((m + (M - 1) + 2 : ℕ) : ℝ) = (M : ℝ) + m + 1 by rw [show m + (M - 1) + 2 = M + m + 1 by omega]; push_cast; ring])).trans
          (nat_rpow_le_unit_integral (by positivity) (by norm_num))
      have hadj := intervalIntegral.sum_integral_adjacent_intervals (f := fun x : ℝ => x ^ (-(4 / 3 : ℝ)))
        (μ := volume) (a := fun k : ℕ => (M : ℝ) + k) (n := K) fun k _ => (ContinuousOn.rpow_const continuousOn_id fun x hx => by
          push_cast at hx; rw [uIcc_of_le (by linarith [(Nat.cast_le.mpr (Nat.le_succ k) : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ))])] at hx
          exact Or.inl (by dsimp only [id]; linarith [hx.1, hM_pos, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)])).intervalIntegrable
      simp only [Nat.cast_zero, add_zero] at hadj
      have hset : ∫ x in (M : ℝ)..((M : ℝ) + K), x ^ (-(4 / 3 : ℝ)) ≤ ∫ x in Ioi (M : ℝ), x ^ (-(4 / 3 : ℝ)) := by
        rw [intervalIntegral.integral_of_le (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)])]
        exact setIntegral_mono_set hint_Ioi ((ae_restrict_mem measurableSet_Ioi).mono fun x (hx : M < x) => Real.rpow_nonneg (by linarith) _) Ioc_subset_Ioi_self.eventuallySubset
      exact ((Finset.sum_le_sum hstep).trans_eq (by rw [← hadj]; exact Finset.sum_congr rfl fun m _ => by rw [Nat.cast_add, Nat.cast_one, add_assoc])).trans hset
    have htsum_le := le_of_tendsto (hf_sum.comp_injective (add_left_injective (M - 1))).hasSum.tendsto_sum_nat (Eventually.of_forall hle_int)
    have hint_val : ∫ x in Ioi (M : ℝ), x ^ (-(4 / 3 : ℝ)) = 3 * (M : ℝ) ^ (-(1 / 3 : ℝ)) := by
      rw [integral_Ioi_rpow_of_lt (by norm_num) hM_pos, show (-(4 / 3 : ℝ) + 1) = -(1 / 3) by norm_num]; ring
    have hH_pow : (H / 2) ^ (-(1 / 3 : ℝ)) = (2 : ℝ) ^ (1 / 3 : ℝ) * √h := by
      have hH' : H ^ (-(1 / 3 : ℝ)) = √h := by dsimp [H]; rw [← Real.rpow_mul hh.le, Real.sqrt_eq_rpow]; congr 1; norm_num
      rw [Real.div_rpow (by positivity) zero_le_two, hH', Real.rpow_neg zero_le_two, div_inv_eq_mul, mul_comm]
    exact (htsum_le.trans_eq hint_val).trans ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity) hM_ge_H (by norm_num)) (by norm_num)).trans_eq
      (by rw [hH_pow]; ring))
  rw [← hf_sum.sum_add_tsum_nat_add (M - 1)]; exact (add_le_add hpart1 hpart2).trans_eq (by ring)

private lemma linear_sep_exists {v₀ : ℝ} (hv₀ : v₀ ∈ Ioo (0 : ℝ) (airyZero 1 - airyZero 2)) :
    ∃ c_sep > 0, ∀ m : ℕ, c_sep * (-airyZero (m + 2)) ≤ (airyZero 1 - v₀) - airyZero (m + 2) := by
  let a₂ := airyZero 2; have ha2_neg : a₂ < 0 := airyZero_neg 2; have hcb : 0 < (airyZero 1 - v₀) - a₂ := by linarith [hv₀.2]
  refine ⟨min (1 / 2) (((airyZero 1 - v₀) - a₂) / (2 * (-a₂))), lt_min (by norm_num) (div_pos hcb (by linarith)), fun m => ?_⟩
  have ha_m : airyZero (m + 2) ≤ a₂ := airyZero_anti (by norm_num) (by omega)
  by_cases hb : -airyZero (m + 2) ≤ 2 * (-a₂)
  · calc _ ≤ ((airyZero 1 - v₀ - a₂) / (2 * (-a₂))) * (2 * (-a₂)) :=
        mul_le_mul (min_le_right _ _) hb (neg_nonneg.mpr (airyZero_neg _).le) (div_nonneg hcb.le (by linarith))
      _ = (airyZero 1 - v₀) - a₂ := by field_simp [ha2_neg.ne]
      _ ≤ (airyZero 1 - v₀) - airyZero (m + 2) := by linarith
  · push Not at hb
    calc _ ≤ (1 / 2) * (-airyZero (m + 2)) := mul_le_mul_of_nonneg_right (min_le_left _ _) (neg_nonneg.mpr (airyZero_neg _).le)
      _ ≤ (airyZero 1 - v₀) - airyZero (m + 2) := by linarith

private lemma near_node_untuned_sub_Hstar_le {p v₀ : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1)
    (hv₀ : v₀ ∈ Ioo (0 : ℝ) (airyZero 1 - airyZero 2)) :
    ∃ C > 0, ∀ {h : ℝ}, h ∈ Ioc (0 : ℝ) 1 → ∀ u ∈ Icc (airyZero 1 - v₀) (airyZero 1),
      |cardinalH_untuned p h u - cardinalHstar airyDerivFirstZero u| ≤ C * √h := by
  let a := airyDerivFirstZero; have hp_pos : 0 < p := by linarith [hp.1]
  obtain ⟨c_sep, hc_sep, hlin_sep⟩ := linear_sep_exists hv₀
  obtain ⟨M_Ai, hM_Ai, hAi_bd⟩ := compact_abs_bound continuous_airyAi.continuousOn (by linarith [hv₀.1] : airyZero 1 - v₀ ≤ airyZero 1)
  obtain ⟨C_tail, hC_tail, htail_bd⟩ := sum_tail_cutoff_rpow_le hp
  let C_pre : ℝ := M_Ai / (c_sep ^ 2 * 2.5 ^ 2); have hC_pre : 0 < C_pre := by positivity
  refine ⟨C_pre * C_tail, mul_pos hC_pre hC_tail, fun {h} hh u hu => ?_⟩
  have hh0 : 0 < h := hh.1
  have hdiff_sum : HasSum (fun n : ℕ => cohnC a n * (1 - ceVarphiP p (h * cohnE n)) * cohnL n u)
      (cardinalHstar a u - cardinalH_untuned p h u) :=
    ((cardinal_Hstar_hasSum_firstDerivZero u).sub ((cardinalH_untuned_converges hh0.le (p := p)).2.1 u)).congr_fun fun _ => by ring
  have hterm0 : cohnC a 0 * (1 - ceVarphiP p (h * cohnE 0)) * cohnL 0 u = 0 := by
    have hE0 : cohnE 0 = 0 := by simp [cohnE]
    rw [hE0, mul_zero]; unfold ceVarphiP; rw [Real.zero_rpow hp_pos.ne']; norm_num
  let g : ℕ → ℝ := fun m => cohnC a (m + 1) * (1 - ceVarphiP p (h * cohnE (m + 1))) * cohnL (m + 1) u
  let maj : ℕ → ℝ := fun m => C_pre * (((m + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) * min 1 ((h * (2.85 * ((m + 2 : ℕ) : ℝ) ^ (2 / 3 : ℝ))) ^ p))
  have hterm_bd : ∀ m : ℕ, |g m| ≤ maj m := fun m => by
    have hneg_m_pos : 0 < -airyZero (m + 2) := neg_pos.mpr (airyZero_neg (m + 2))
    have hsep_u : c_sep * (-airyZero (m + 2)) ≤ u - airyZero (m + 2) := (hlin_sep m).trans (by linarith [hu.1])
    have hsep_u_pos : 0 < u - airyZero (m + 2) := lt_of_lt_of_le (mul_pos hc_sep hneg_m_pos) hsep_u
    have hsep_a : c_sep * (-airyZero (m + 2)) ≤ a - airyZero (m + 2) := hsep_u.trans (by linarith [hu.2, airyDerivFirstZero_spec.1])
    have hL_le : |cohnL (m + 1) u| ≤ M_Ai / (c_sep * (-airyZero (m + 2))) := by
      rw [cohnL_of_ne (ne_of_gt (sub_pos.mp hsep_u_pos)), abs_div, abs_of_pos hsep_u_pos]
      exact div_le_div₀ hM_Ai.le (hAi_bd u hu) (mul_pos hc_sep hneg_m_pos) hsep_u
    have hC_le : |cohnC a (m + 1)| ≤ 1 / (c_sep * (-airyZero (m + 2))) := by
      rw [cohnC, abs_inv, show airyZero (m + 1 + 1) - a = -(a - airyZero (m + 2)) by ring,
        abs_neg, abs_of_pos (lt_of_lt_of_le (mul_pos hc_sep hneg_m_pos) hsep_a), inv_eq_one_div]
      exact div_le_div_of_nonneg_left zero_le_one (mul_pos hc_sep hneg_m_pos) hsep_a
    have hzm := airyZero_abs_bounds (by omega : 2 ≤ m + 2)
    have hCL_bd : |cohnC a (m + 1)| * |cohnL (m + 1) u| ≤ C_pre * ((m + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) := by
      have hk_pos : (0 : ℝ) < (m + 2 : ℕ) := by positivity
      have hden_le : (c_sep * (2.5 * ((m + 2 : ℕ) : ℝ) ^ (2 / 3 : ℝ))) ^ 2 ≤ (c_sep * (-airyZero (m + 2))) ^ 2 := by gcongr; exact hzm.1
      calc _ ≤ M_Ai / (c_sep * (-airyZero (m + 2))) ^ 2 := (mul_le_mul hC_le hL_le (abs_nonneg _) (by positivity)).trans_eq (by ring)
        _ ≤ M_Ai / (c_sep * (2.5 * ((m + 2 : ℕ) : ℝ) ^ (2 / 3 : ℝ))) ^ 2 := div_le_div_of_nonneg_left hM_Ai.le (by positivity) hden_le
        _ = C_pre * ((m + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) := by
            rw [mul_pow, mul_pow, rpow_sq_eq hk_pos.le, Real.rpow_neg hk_pos.le, div_eq_mul_inv]; dsimp [C_pre]; norm_num; ring
    have hE_le : h * cohnE (m + 1) ≤ h * (2.85 * ((m + 2 : ℕ) : ℝ) ^ (2 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left ((by unfold cohnE; linarith [airyZero_neg 1] : cohnE (m + 1) ≤ -airyZero (m + 2)).trans hzm.2) hh0.le
    have hphi_bd : |1 - ceVarphiP p (h * cohnE (m + 1))| ≤ min 1 ((h * (2.85 * ((m + 2 : ℕ) : ℝ) ^ (2 / 3 : ℝ))) ^ p) := by
      rw [abs_of_nonneg (one_sub_ceVarphiP_nonneg (mul_nonneg hh0.le (cohnE_nonneg' (m + 1))))]
      exact (one_sub_ceVarphiP_le_min (mul_nonneg hh0.le (cohnE_nonneg' (m + 1)))).trans
        (le_min (min_le_left _ _) ((min_le_right _ _).trans (Real.rpow_le_rpow (mul_nonneg hh0.le (cohnE_nonneg' (m + 1))) hE_le hp_pos.le)))
    dsimp [g, maj]; rw [abs_mul, abs_mul, mul_right_comm, ← mul_assoc]; exact mul_le_mul hCL_bd hphi_bd (abs_nonneg _) (by positivity)
  have hsum_maj : Summable maj :=
    (((summable_nat_add_iff 2).mpr (Real.summable_nat_rpow_inv.mpr (by norm_num : 1 < (4 / 3 : ℝ)))).of_nonneg_of_le
      (fun _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (le_min zero_le_one (Real.rpow_nonneg (by positivity) _)))
      fun m => by rw [Real.rpow_neg (Nat.cast_nonneg _)]; exact mul_le_of_le_one_right (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (min_le_left _ _)).mul_left C_pre
  have hg_norm : Summable (fun m : ℕ => ‖g m‖) := hsum_maj.of_nonneg_of_le (fun _ => norm_nonneg _) fun m => (Real.norm_eq_abs _).trans_le (hterm_bd m)
  rw [show |cardinalH_untuned p h u - cardinalHstar a u| = |∑' m : ℕ, g m| by
      rw [abs_sub_comm, ← hdiff_sum.tsum_eq, hdiff_sum.summable.tsum_eq_zero_add, hterm0, zero_add], ← Real.norm_eq_abs]
  calc ‖∑' m : ℕ, g m‖ ≤ ∑' m : ℕ, ‖g m‖ := norm_tsum_le_tsum_norm hg_norm
    _ ≤ ∑' m : ℕ, maj m := hg_norm.tsum_le_tsum (fun m => (Real.norm_eq_abs _).trans_le (hterm_bd m)) hsum_maj
    _ = C_pre * ∑' m : ℕ, ((m + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) * min 1 ((h * (2.85 * ((m + 2 : ℕ) : ℝ) ^ (2 / 3 : ℝ))) ^ p) := tsum_mul_left
    _ ≤ (C_pre * C_tail) * √h := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (htail_bd hh0 hh.2) hC_pre.le

/-- **Lemma O.11p (`(ceo:O11p.1)`), Near-node region `u ∈ [a₁ - v₀, a₁]`. -/
theorem cardinalQ_near_node {p R₀ v₀ : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hR₀ : 0 ≤ R₀)
    (hv₀ : v₀ ∈ Ioo (0 : ℝ) (airyZero 1 - airyZero 2)) :
    let m := sInf ((fun u => dslope airyAi (airyZero 1) u ^ 2) '' Icc (airyZero 1 - v₀) (airyZero 1))
    0 < m ∧
    ∃ h₀ > 0, ∃ K₀ > 0, ∀ {h σ : ℝ}, h ∈ Ioo 0 h₀ → 0 ≤ σ → σ ≤ 1 → 1 - σ ^ 2 ≤ R₀ * √h →
      ∀ u ∈ Icc (airyZero 1 - v₀) (airyZero 1),
        |cardinalH p h σ u ^ 2 - ceG1Deriv airyDerivFirstZero u| ≤ K₀ * √h ∧
        m * (airyZero 1 - u) - K₀ * √h ≤ cardinalQ p h σ u := by
  let a := airyDerivFirstZero; let a₁ := airyZero 1; let q₁ : ℝ → ℝ := dslope airyAi a₁
  have hq₁_cont : Continuous q₁ := by
    rw [← continuousOn_univ, continuousOn_dslope univ_mem]; exact ⟨differentiable_airyAi.continuous.continuousOn, differentiable_airyAi a₁⟩
  let S_m := (fun u => q₁ u ^ 2) '' Icc (a₁ - v₀) a₁
  have hne_Icc : (Icc (a₁ - v₀) a₁).Nonempty := ⟨a₁, right_mem_Icc.mpr (by linarith [hv₀.1])⟩
  obtain ⟨u_m, hu_m_mem, hu_m_min⟩ := isCompact_Icc.exists_isMinOn (f := fun u => q₁ u ^ 2) hne_Icc (hq₁_cont.pow 2).continuousOn
  have hm_pos : 0 < sInf S_m := by
    have hu_m_pos : 0 < q₁ u_m ^ 2 := sq_pos_iff.mpr (by
      by_cases h1 : u_m = a₁
      · subst h1; dsimp [q₁]; rw [dslope_same, deriv_airyAi]; exact airyAi'_first_pos.ne'
      · have hne := airyAi_ne_zero_of_mem_gap (n := 2) (by norm_num) ⟨by linarith [hu_m_mem.1, hv₀.2], lt_of_le_of_ne hu_m_mem.2 h1⟩
        dsimp [q₁]; rw [dslope_of_ne _ h1, slope_def_field, airyAi_airyZero, sub_zero]; exact div_ne_zero hne (sub_ne_zero.mpr h1))
    exact hu_m_pos.trans_le (le_csInf (hne_Icc.image _) fun _ ⟨u, hu, hy⟩ => hy ▸ hu_m_min hu)
  have hX_cont : Continuous (cardinalHstar a) := by
    rw [← continuousOn_univ, show cardinalHstar a = dslope airyAi' a from rfl, continuousOn_dslope univ_mem]
    exact ⟨continuous_airyAi'.continuousOn, (hasDerivAt_airyAi' a).differentiableAt⟩
  obtain ⟨M_X, hM_X, hX_bd⟩ := compact_abs_bound hX_cont.continuousOn (by linarith [hv₀.1] : a₁ - v₀ ≤ a₁)
  obtain ⟨M_L, hM_L, hL_bd⟩ := compact_abs_bound hq₁_cont.continuousOn (by linarith [hv₀.1] : a₁ - v₀ ≤ a₁)
  obtain ⟨C_u, hC_u, h_unt⟩ := near_node_untuned_sub_Hstar_le hp hv₀
  obtain ⟨C_eta, hC_eta, h_eta⟩ := cardinalEtaHat_sqrt_bound hp hR₀
  let K₁ : ℝ := C_u + R₀ * M_X + C_eta * M_L + 1; let K₀ : ℝ := K₁ * (K₁ + 2 * M_X) + 1
  refine ⟨hm_pos, 1, one_pos, K₀, by positivity, fun {h σ} hh hσ0 hσ1 hsig u hu => ?_⟩
  have hh_Ioc : h ∈ Ioc (0 : ℝ) 1 := ⟨hh.1, hh.2.le⟩; have hp_pos : 0 < p := by linarith [hp.1]
  have hL0_eq : cohnL 0 u = q₁ u := by
    by_cases h1 : u = a₁
    · subst h1; dsimp [q₁]; rw [cohnL_self, dslope_same, deriv_airyAi]
    · dsimp [q₁]; rw [cohnL_of_ne h1, dslope_of_ne _ h1, slope_def_field, airyAi_airyZero, sub_zero]
  have h1s : 1 - σ ≤ R₀ * √h := by
    have hle : 1 - σ ≤ (1 - σ) * (1 + σ) := le_mul_of_one_le_right (by linarith) (by linarith)
    linarith [show (1 - σ) * (1 + σ) = 1 - σ ^ 2 by ring]
  have heta_nn : 0 ≤ cardinalEtaHat p h σ := (cardinalEtaHat_bounds hp_pos hh.1.le hσ0 hσ1).2.1
  have ht1 : |cardinalH p h σ u - cardinalHstar a u| ≤ K₁ * √h := by
    have ht1a : |σ * (cardinalH_untuned p h u - cardinalHstar a u)| ≤ C_u * √h := by
      rw [abs_mul, abs_of_nonneg hσ0]; exact (mul_le_of_le_one_left (abs_nonneg _) hσ1).trans (h_unt hh_Ioc u hu)
    have ht2a : |(1 - σ) * cardinalHstar a u| ≤ R₀ * M_X * √h := by
      rw [abs_mul, abs_of_nonneg (by linarith)]; exact (mul_le_mul h1s (hX_bd u hu) (abs_nonneg _) (by positivity)).trans_eq (by ring)
    have ht3a : |cardinalEtaHat p h σ * q₁ u| ≤ C_eta * M_L * √h := by
      rw [abs_mul, abs_of_nonneg heta_nn]; exact (mul_le_mul (h_eta hh_Ioc hσ0 hσ1 hsig) (hL_bd u hu) (abs_nonneg _) (by positivity)).trans_eq (by ring)
    rw [show cardinalH p h σ u - cardinalHstar a u = σ * (cardinalH_untuned p h u - cardinalHstar a u) - (1 - σ) * cardinalHstar a u - cardinalEtaHat p h σ * q₁ u by
      rw [(cardinalH_eq_untuned_sub hp_pos hh.1.le hσ0 hσ1).1 u, hL0_eq]; ring]
    exact ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans (by dsimp [K₁]; linarith [Real.sqrt_nonneg h])
  have hH_sum_le : |cardinalH p h σ u + cardinalHstar a u| ≤ K₁ + 2 * M_X := by
    have hdiff_le : |cardinalH p h σ u - cardinalHstar a u| ≤ K₁ := ht1.trans (mul_le_of_le_one_right (by positivity) (Real.sqrt_le_one.mpr hh.2.le))
    have htr := abs_add_le (cardinalH p h σ u - cardinalHstar a u) (2 * cardinalHstar a u)
    rw [show cardinalH p h σ u - cardinalHstar a u + 2 * cardinalHstar a u = cardinalH p h σ u + cardinalHstar a u by ring, abs_mul, abs_two] at htr
    linarith [hX_bd u hu]
  have hsq_err : |cardinalH p h σ u ^ 2 - ceG1Deriv a u| ≤ K₀ * √h := by
    rw [show ceG1Deriv a u = cardinalHstar a u ^ 2 from rfl, sq_sub_sq, abs_mul, mul_comm]
    exact (mul_le_mul ht1 hH_sum_le (abs_nonneg _) (by positivity)).trans (by dsimp [K₀]; linarith [Real.sqrt_nonneg h])
  refine ⟨hsq_err, ?_⟩
  have hf_eq : -ceF1 u = (a₁ - u) * q₁ u ^ 2 := by
    by_cases h1 : u = a₁
    · subst h1; simp [ceF1]; left; exact airyAi_airyZero 1
    · unfold ceF1; dsimp [q₁]; rw [dslope_of_ne _ h1, slope_def_field, airyAi_airyZero, sub_zero]; field_simp [sub_ne_zero.mpr h1]; ring
  have hf_ge : sInf S_m * (a₁ - u) ≤ -ceF1 u := by
    rw [hf_eq, mul_comm (sInf S_m)]
    exact mul_le_mul_of_nonneg_left (csInf_le ⟨0, fun _ ⟨_, _, hy⟩ => by rw [← hy]; exact sq_nonneg _⟩ ⟨u, hu, rfl⟩) (sub_nonneg.mpr hu.2)
  have hg_ge : ceG1Deriv a u - cardinalH p h σ u ^ 2 ≥ -(K₀ * √h) := by linarith [(abs_le.mp hsq_err).2]
  unfold cardinalQ cardinalP; linarith

private lemma fracMu_denom_lb {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    0 < 1 - |Real.cos (π * p)| ∧
    ∀ {s : ℝ}, 0 < s → (1 - |Real.cos (π * p)|) * (s ^ (2 * p) + 1) ≤ s ^ (2 * p) + 2 * s ^ p * Real.cos (π * p) + 1 := by
  have hsin : 0 < Real.sin (π * p) := Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hp.1) (by nlinarith [Real.pi_pos, hp.2])
  have hcos : |Real.cos (π * p)| < 1 := by rw [← sq_lt_one_iff_abs_lt_one]; nlinarith [Real.sin_sq_add_cos_sq (π * p), sq_pos_iff.mpr hsin.ne']
  refine ⟨sub_pos.mpr hcos, fun {s} hs => ?_⟩
  have h2sp : 2 * s ^ p ≤ s ^ (2 * p) + 1 := by nlinarith [sq_nonneg (s ^ p - 1), rpow_sq_eq (a := p) hs.le]
  have hab : -(2 * s ^ p * Real.cos (π * p)) ≤ |Real.cos (π * p)| * (s ^ (2 * p) + 1) := by
    calc -(2 * s ^ p * Real.cos (π * p)) ≤ |2 * s ^ p * Real.cos (π * p)| := neg_le_abs _
      _ = (2 * s ^ p) * |Real.cos (π * p)| := by rw [abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ (s ^ (2 * p) + 1) * |Real.cos (π * p)| := mul_le_mul_of_nonneg_right h2sp (abs_nonneg _)
      _ = |Real.cos (π * p)| * (s ^ (2 * p) + 1) := mul_comm _ _
  linarith
private lemma continuousOn_fracMuDensity {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) : ContinuousOn (fracMuDensity p) (Ioi (0 : ℝ)) := by
  obtain ⟨hc_pos, hden_lb⟩ := fracMu_denom_lb hp; unfold fracMuDensity
  refine continuousOn_const.mul ((ContinuousOn.rpow_const continuousOn_id fun _ hx => Or.inl (mem_Ioi.mp hx).ne').div
    (((ContinuousOn.rpow_const continuousOn_id fun _ hx => Or.inl (mem_Ioi.mp hx).ne').add
      ((continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id fun _ hx => Or.inl (mem_Ioi.mp hx).ne')).mul continuousOn_const)).add continuousOn_const)
    fun s hs => ne_of_gt (lt_of_lt_of_le (mul_pos hc_pos (add_pos_of_nonneg_of_pos (Real.rpow_nonneg (mem_Ioi.mp hs).le _) one_pos)) (hden_lb (mem_Ioi.mp hs))))
private lemma fracZp_im_eq {p t : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (ht : 0 ≤ t) :
    (fracZp p t).im = ∫ s in Ioi (0 : ℝ), (√(s * t) / (1 + s * t)) * fracMuDensity p s := by
  rw [fracZp, ← RCLike.im_eq_complex_im, ← integral_im (fracZp_integrable hp ht)]
  refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => ?_
  have hns : Complex.normSq (1 - Complex.I * ((√(s * t) : ℝ) : ℂ)) = 1 + s * t := by rw [Complex.normSq_apply]; simp; linarith [Real.sq_sqrt (mul_nonneg hs.le ht)]
  rw [RCLike.im_eq_complex_im]; simp [Complex.inv_im, hns]
private lemma integrableOn_sqrt_mul_div_one_add {p t : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (ht : 0 ≤ t) :
    IntegrableOn (fun s : ℝ => (√(s * t) / (1 + s * t)) * fracMuDensity p s) (Ioi (0 : ℝ)) := by
  refine ((fracMuDensity_integrable hp).const_mul (1 / 2 : ℝ)).mono'
    ((((Real.continuous_sqrt.comp (continuous_id.mul continuous_const)).continuousOn.div
      (continuousOn_const.add (continuousOn_id.mul continuousOn_const))
      fun s hs => ne_of_gt (by dsimp; linarith [mul_nonneg (mem_Ioi.mp hs).le ht])).mul (continuousOn_fracMuDensity hp)).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
  rw [Real.norm_of_nonneg (mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (by positivity)) (fracMuDensity_pos hp hs).le)]
  exact mul_le_mul_of_nonneg_right (sqrt_div_one_add_le (mul_nonneg hs.le ht)) (fracMuDensity_pos hp hs).le
private lemma integrableOn_inv_fracMu {p t : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (ht : 0 ≤ t) :
    IntegrableOn (fun s : ℝ => (1 + s * t)⁻¹ * fracMuDensity p s) (Ioi (0 : ℝ)) := by
  refine (fracMuDensity_integrable hp).mono'
    ((((continuousOn_const.add (continuousOn_id.mul continuousOn_const)).inv₀ fun s hs =>
      ne_of_gt (by dsimp; linarith [mul_nonneg (mem_Ioi.mp hs).le ht])).mul (continuousOn_fracMuDensity hp)).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
  rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (by linarith [mul_nonneg hs.le ht])) (fracMuDensity_pos hp hs).le)]
  exact mul_le_of_le_one_left (fracMuDensity_pos hp hs).le (inv_le_one_of_one_le₀ (by linarith [mul_nonneg hs.le ht]))
private lemma fracZp_im_bounds {p : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) :
    ∃ C_Z > 0, ∀ {t : ℝ}, 0 ≤ t → 0 ≤ (fracZp p t).im ∧ (fracZp p t).im ≤ 1 / 2 ∧ (fracZp p t).im ≤ C_Z * √t := by
  have hp01 : p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], hp.2⟩
  obtain ⟨hc_pos, hden_lb⟩ := fracMu_denom_lb hp01
  have hsin := Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hp01.1) (by nlinarith [Real.pi_pos, hp01.2])
  let C₀ : ℝ := (Real.sin (π * p) / π) / (1 - |Real.cos (π * p)|)
  have hC₀ : 0 ≤ C₀ := div_nonneg (div_nonneg hsin.le Real.pi_pos.le) hc_pos.le
  have hbd : ∀ s > 0, 0 ≤ √s * fracMuDensity p s ∧ √s * fracMuDensity p s ≤ C₀ * (s ^ (p - 1 / 2 : ℝ) / (s ^ (2 * p) + 1)) := fun s hs => by
    have hpow : √s * s ^ (p - 1) = s ^ (p - 1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow, rpow_add_eq hs (by ring : 1 / 2 + (p - 1) = p - 1 / 2)]
    refine ⟨mul_nonneg (Real.sqrt_nonneg s) (fracMuDensity_pos hp01 hs).le, ?_⟩; unfold fracMuDensity
    exact (div_le_div_of_nonneg_left (mul_nonneg (div_nonneg hsin.le Real.pi_pos.le) (Real.rpow_nonneg hs.le _))
      (mul_pos hc_pos (add_pos_of_nonneg_of_pos (Real.rpow_nonneg hs.le _) one_pos)) (hden_lb hs) |>.trans_eq'
      (by rw [← hpow]; ring)).trans_eq (by dsimp [C₀]; field_simp [hc_pos.ne'])
  have hmeas : AEStronglyMeasurable (fun s : ℝ => √s * fracMuDensity p s) (volume.restrict (Ioi (0 : ℝ))) :=
    (Real.continuous_sqrt.continuousOn.mul (continuousOn_fracMuDensity hp01)).aestronglyMeasurable measurableSet_Ioi
  have h1 : IntegrableOn (fun s : ℝ => √s * fracMuDensity p s) (Ioc 0 1) := by
    refine ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      ((intervalIntegral.intervalIntegrable_rpow' (by linarith [hp.1] : (-1 : ℝ) < p - 1 / 2)).const_mul C₀)).mono' (hmeas.mono_set Ioc_subset_Ioi_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Real.norm_of_nonneg (hbd s hs.1).1]
    exact (hbd s hs.1).2.trans (mul_le_mul_of_nonneg_left (div_le_self (Real.rpow_nonneg hs.1.le _) (by linarith [Real.rpow_nonneg hs.1.le (2 * p)])) hC₀)
  have h2 : IntegrableOn (fun s : ℝ => √s * fracMuDensity p s) (Ioi 1) := by
    refine ((integrableOn_Ioi_rpow_of_lt (by linarith [hp.1] : -p - 1 / 2 < -1) zero_lt_one).const_mul C₀).mono' (hmeas.mono_set (Ioi_subset_Ioi zero_le_one)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 1 < s)
    have hs0 : 0 < s := by linarith
    rw [Real.norm_of_nonneg (hbd s hs0).1]
    exact (hbd s hs0).2.trans ((mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (Real.rpow_nonneg hs0.le _)
      (Real.rpow_pos_of_pos hs0 _) (by linarith)) hC₀).trans_eq (by rw [← Real.rpow_sub hs0]; ring_nf))
  have hint_sq : IntegrableOn (fun s : ℝ => √s * fracMuDensity p s) (Ioi (0 : ℝ)) := by simpa [Ioc_union_Ioi_eq_Ioi zero_le_one] using h1.union h2
  let C_Z : ℝ := (∫ s in Ioi (0 : ℝ), √s * fracMuDensity p s) + 1
  have hC_pos : 0 < C_Z := by
    have hnn : 0 ≤ ∫ s in Ioi (0 : ℝ), √s * fracMuDensity p s :=
      setIntegral_nonneg measurableSet_Ioi fun s hs => mul_nonneg (Real.sqrt_nonneg s) (fracMuDensity_pos hp01 hs).le
    linarith
  refine ⟨C_Z, hC_pos, fun {t} ht => ?_⟩
  rw [fracZp_im_eq hp01 ht]; have hint_im := integrableOn_sqrt_mul_div_one_add hp01 ht
  refine ⟨setIntegral_nonneg measurableSet_Ioi fun s hs =>
      mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (by linarith [mul_nonneg hs.le ht])) (fracMuDensity_pos hp01 hs).le,
    (setIntegral_mono_on hint_im ((fracMuDensity_integrable hp01).const_mul (1 / 2)) measurableSet_Ioi
      fun s (hs : 0 < s) => mul_le_mul_of_nonneg_right (sqrt_div_one_add_le (mul_nonneg hs.le ht)) (fracMuDensity_pos hp01 hs).le).trans_eq
      (by rw [integral_const_mul, fracMuDensity_integral_one hp01, mul_one]),
    ((setIntegral_mono_on hint_im (hint_sq.const_mul √t) measurableSet_Ioi fun s (hs : 0 < s) => by
      rw [Real.sqrt_mul hs.le, mul_comm √s √t]
      exact (mul_le_mul_of_nonneg_right (div_le_self (by positivity) (by linarith [mul_nonneg hs.le ht])) (fracMuDensity_pos hp01 hs).le).trans_eq (by ring)).trans_eq
      (integral_const_mul _ _)).trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right (by dsimp [C_Z]; linarith) (Real.sqrt_nonneg t))⟩

/-- Explicit `Y`-coefficient `β(h, σ, u)` in the `(X, Y)` decomposition (`(ceo:O11p.coefficient)`). -/
noncomputable def cardinalBeta (p h σ u : ℝ) : ℝ :=
  σ * (∫ s in Ioi (0 : ℝ), (√(airyZero 1 - u) * cardinalJ (s * h) / (1 + s * (h * (airyZero 1 - u)))) *
    fracMuDensity p s) + cardinalEtaHat p h σ / √(airyZero 1 - u)

private lemma cardinalBeta_integrable {p h u : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hh : 0 < h) (hu : u < airyZero 1) :
    IntegrableOn (fun s : ℝ => (√(airyZero 1 - u) * cardinalJ (s * h) / (1 + s * (h * (airyZero 1 - u)))) *
      fracMuDensity p s) (Ioi (0 : ℝ)) := by
  let v := airyZero 1 - u; have hp01 : p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], hp.2⟩; have hv_pos : 0 < v := sub_pos.mpr hu
  obtain ⟨C_J, hC_J, hJ_bd⟩ := cardinalJ_asymptotic
  have hcont : ContinuousOn (fun s : ℝ => (√v * cardinalJ (s * h) / (1 + s * (h * v))) * fracMuDensity p s) (Ioi (0 : ℝ)) :=
    ((continuousOn_const.mul (continuousOn_cardinalJ.comp (continuousOn_id.mul continuousOn_const)
      fun _ hs => mul_pos (mem_Ioi.mp hs) hh)).div (continuousOn_const.add (continuousOn_id.mul continuousOn_const))
      fun s hs => ne_of_gt (by dsimp; linarith [mul_pos (mem_Ioi.mp hs) (mul_pos hh hv_pos)])).mul (continuousOn_fracMuDensity hp01)
  refine ((fracMuDensity_integrable hp01).const_mul (1 / 2 + C_J / √v)).mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
  have hden_pos : 0 < 1 + s * (h * v) := by positivity
  have hJ_abs : |cardinalJ (s * h)| ≤ √(s * h) + C_J * (s * h) := by have hJb := abs_le.mp (hJ_bd (s * h) (mul_pos hs hh)); exact abs_le.mpr ⟨by linarith [Real.sqrt_nonneg (s * h)], by linarith⟩
  have hst1 : √v * √(s * h) / (1 + s * (h * v)) ≤ 1 / 2 := by
    rw [← Real.sqrt_mul hv_pos.le, show v * (s * h) = s * (h * v) by ring]; exact sqrt_div_one_add_le (mul_pos hs (mul_pos hh hv_pos)).le
  have hst2 : √v * (C_J * (s * h)) / (1 + s * (h * v)) ≤ C_J / √v :=
    ((show √v * (C_J * (s * h)) / (1 + s * (h * v)) = (C_J / √v) * (s * (h * v) / (1 + s * (h * v))) by field_simp [(Real.sqrt_pos.mpr hv_pos).ne']; rw [Real.sq_sqrt hv_pos.le])).symm ▸
      mul_le_of_le_one_right (div_nonneg hC_J.le (Real.sqrt_nonneg _)) (div_le_one_of_le₀ (by linarith) hden_pos.le)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (fracMuDensity_pos hp01 hs), abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos hden_pos]
  exact (mul_le_mul_of_nonneg_right (by rw [← add_div, div_le_div_iff_of_pos_right hden_pos]; nlinarith [Real.sqrt_nonneg v]) (fracMuDensity_pos hp01 hs).le).trans
    (mul_le_mul_of_nonneg_right (add_le_add hst1 hst2) (fracMuDensity_pos hp01 hs).le)

/-- **Lemma O.11p (`(ceo:O11p.2)`, `(ceo:O11p.coefficient)`), `(X, Y)` decomposition on `v ≥ v₀`. -/
theorem cardinalH_decomp_XY {p R₀ v₀ : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hR₀ : 0 ≤ R₀) (hv₀ : 0 < v₀) :
    ∃ C > 0, ∃ K₀ > 0, ∀ {h σ : ℝ}, h ∈ Ioc (0 : ℝ) 1 → 0 ≤ σ → σ ≤ 1 → 1 - σ ^ 2 ≤ R₀ * √h →
      ∀ {u : ℝ}, u ≤ airyZero 1 - v₀ →
        let v := airyZero 1 - u
        let t := h * v
        cardinalH p h σ u =
          (σ * ceVarphiP p t) * cardinalHstar airyDerivFirstZero u + cardinalBeta p h σ u * (airyAi u / √v) ∧
        |cardinalBeta p h σ u - σ * (fracZp p t).im| ≤ C * ((1 - ceVarphiP p t) + √h) / √v ∧
        (t ≤ 1 → |cardinalBeta p h σ u| ≤ K₀ * √t) := by
  have hp01 : p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], hp.2⟩
  obtain ⟨C_J, hC_J, hJ_bd⟩ := cardinalJ_asymptotic
  obtain ⟨C_eta, hC_eta, h_eta⟩ := cardinalEtaHat_sqrt_bound hp hR₀
  obtain ⟨C_Z, hC_Z, h_Z⟩ := fracZp_im_bounds hp
  let C_β : ℝ := max C_J C_eta; let K₀ : ℝ := C_Z + C_β * (v₀ ^ (p - 1) + v₀⁻¹) + 1
  refine ⟨C_β, lt_of_lt_of_le hC_J (le_max_left _ _), K₀, by positivity, fun {h σ} hh hσ0 hσ1 hsig {u} hu => ?_⟩
  have hh0 : 0 < h := hh.1; have hv_ge : v₀ ≤ airyZero 1 - u := by linarith
  have hv_pos : 0 < airyZero 1 - u := lt_of_lt_of_le hv₀ hv_ge; have hu_lt : u < airyZero 1 := sub_pos.mp hv_pos
  let v := airyZero 1 - u; let t := h * v; have ht_pos : 0 < t := mul_pos hh0 hv_pos
  have hint1 := integrableOn_inv_fracMu hp01 ht_pos.le; have hint2 := cardinalBeta_integrable hp hh0 hu_lt
  have hunt_eq : cardinalH_untuned p h u = ceVarphiP p t * cardinalHstar airyDerivFirstZero u +
      (∫ s in Ioi (0 : ℝ), (√v * cardinalJ (s * h) / (1 + s * t)) * fracMuDensity p s) * (airyAi u / √v) := by
    rw [cardinalH_untuned_eq_integral hp hh0 u]
    have hcongr : ∫ s in Ioi (0 : ℝ), cardinalResolventH s h u * fracMuDensity p s =
        ∫ s in Ioi (0 : ℝ), (cardinalHstar airyDerivFirstZero u * ((1 + s * t)⁻¹ * fracMuDensity p s) +
          (airyAi u / √v) * ((√v * cardinalJ (s * h) / (1 + s * t)) * fracMuDensity p s)) :=
      setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => by rw [cardinalResolventH_eq_XY hs hh0 hu_lt]; dsimp [v, t]; ring
    rw [hcongr, integral_add (hint1.const_mul _) (hint2.const_mul _),
      integral_const_mul, integral_const_mul, fracMu_stieltjes_eq hp01 ht_pos.le]; ring
  have hH_eq : cardinalH p h σ u = (σ * ceVarphiP p t) * cardinalHstar airyDerivFirstZero u + cardinalBeta p h σ u * (airyAi u / √v) := by
    have h1 := (cardinalH_eq_untuned_sub hp01.1 hh0.le hσ0 hσ1).1 u
    have hL0 : cohnL 0 u = -(airyAi u / √v) / √v := by
      rw [cohnL_of_ne hu_lt.ne, zero_add, show u - airyZero 1 = -v by dsimp [v]; ring]
      field_simp [(Real.sqrt_pos.mpr hv_pos).ne', hv_pos.ne']; rw [Real.sq_sqrt hv_pos.le]
    rw [h1, hunt_eq, hL0]; unfold cardinalBeta; dsimp [v, t]; ring
  have hint_im := integrableOn_sqrt_mul_div_one_add hp01 ht_pos.le
  have hdiff_int_bd : |(∫ s in Ioi (0 : ℝ), (√v * cardinalJ (s * h) / (1 + s * t)) * fracMuDensity p s) -
      (fracZp p t).im| ≤ C_J * (1 - ceVarphiP p t) / √v := by
    rw [fracZp_im_eq hp01 ht_pos.le, ← integral_sub hint2 hint_im]
    have heq : (fun s => (√(airyZero 1 - u) * cardinalJ (s * h) / (1 + s * (h * (airyZero 1 - u)))) * fracMuDensity p s -
        (√(s * t) / (1 + s * t)) * fracMuDensity p s) =
        fun s => (√v * (cardinalJ (s * h) - √(s * h)) / (1 + s * t)) * fracMuDensity p s := funext fun s => by
      have hsq : √v * √(s * h) = √(s * t) := by
        by_cases hs0 : 0 ≤ s
        · rw [← Real.sqrt_mul hv_pos.le]; congr 1; dsimp [t]; ring
        · rw [Real.sqrt_eq_zero_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (not_le.mp hs0).le hh0.le),
            Real.sqrt_eq_zero_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (not_le.mp hs0).le ht_pos.le), mul_zero]
      dsimp only [v, t] at hsq ⊢; rw [← hsq]; ring
    have hdom_int : IntegrableOn (fun s : ℝ => (C_J / √v) * ((1 - (1 + s * t)⁻¹) * fracMuDensity p s)) (Ioi (0 : ℝ)) :=
      (((fracMuDensity_integrable hp01).sub hint1).congr (ae_of_all _ fun _ => by simp only [Pi.sub_apply]; ring)).const_mul _
    rw [heq, ← Real.norm_eq_abs]
    refine ((norm_integral_le_integral_norm _).trans (setIntegral_mono_on ((hint2.sub hint_im).congr
      (ae_of_all _ fun s => congrFun heq s)).norm hdom_int measurableSet_Ioi fun s (hs : 0 < s) => ?_)).trans_eq ?_
    · have hden_pos : 0 < 1 + s * t := by positivity
      have hsv : (√v)⁻¹ * √v = 1 := inv_mul_cancel₀ (Real.sqrt_pos.mpr hv_pos).ne'
      have h_id : (√v * (C_J * (s * h)) / (1 + s * t)) * fracMuDensity p s = (C_J / √v) * ((1 - (1 + s * t)⁻¹) * fracMuDensity p s) := by
        rw [show 1 - (1 + s * t)⁻¹ = s * t / (1 + s * t) by field_simp [hden_pos.ne']; ring,
          show √v * (C_J * (s * h)) = C_J / √v * (s * h * (√v * √v)) by rw [div_eq_mul_inv,
            show C_J * (√v)⁻¹ * (s * h * (√v * √v)) = ((√v)⁻¹ * √v) * (√v * (C_J * (s * h))) by ring, hsv, one_mul],
          Real.mul_self_sqrt hv_pos.le]; dsimp [t]; ring
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos hden_pos, abs_of_pos (fracMuDensity_pos hp01 hs)]
      exact (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (hJ_bd (s * h) (mul_pos hs hh0)) (Real.sqrt_nonneg _)) hden_pos.le) (fracMuDensity_pos hp01 hs).le).trans_eq h_id
    · rw [integral_const_mul, show (fun s : ℝ => (1 - (1 + s * t)⁻¹) * fracMuDensity p s) =
        fun s => fracMuDensity p s - (1 + s * t)⁻¹ * fracMuDensity p s from funext fun _ => by ring,
        integral_sub (fracMuDensity_integrable hp01) hint1, fracMuDensity_integral_one hp01, fracMu_stieltjes_eq hp01 ht_pos.le]; ring
  have heta_nn : 0 ≤ cardinalEtaHat p h σ := (cardinalEtaHat_bounds hp01.1 hh0.le hσ0 hσ1).2.1
  have hbeta_err : |cardinalBeta p h σ u - σ * (fracZp p t).im| ≤ C_β * ((1 - ceVarphiP p t) + √h) / √v := by
    rw [show cardinalBeta p h σ u - σ * (fracZp p t).im =
      σ * ((∫ s in Ioi (0 : ℝ), (√v * cardinalJ (s * h) / (1 + s * t)) * fracMuDensity p s) - (fracZp p t).im) +
        cardinalEtaHat p h σ / √v by unfold cardinalBeta; dsimp [v, t]; ring]
    have h1 : |σ * ((∫ s in Ioi (0 : ℝ), (√v * cardinalJ (s * h) / (1 + s * t)) * fracMuDensity p s) - (fracZp p t).im)| ≤ C_J * (1 - ceVarphiP p t) / √v := by
      rw [abs_mul, abs_of_nonneg hσ0]; exact (mul_le_of_le_one_left (abs_nonneg _) hσ1).trans hdiff_int_bd
    have h2 : |cardinalEtaHat p h σ / √v| ≤ C_eta * √h / √v := by rw [abs_of_nonneg (div_nonneg heta_nn (Real.sqrt_nonneg _))]; exact div_le_div_of_nonneg_right (h_eta hh hσ0 hσ1 hsig) (Real.sqrt_nonneg _)
    refine (abs_add_le _ _).trans ((add_le_add h1 h2).trans ?_)
    have hle1 : C_J * (1 - ceVarphiP p t) / √v ≤ C_β * (1 - ceVarphiP p t) / √v := by gcongr; exact one_sub_ceVarphiP_nonneg ht_pos.le; exact le_max_left _ _
    have hle2 : C_eta * √h / √v ≤ C_β * √h / √v := by gcongr; exact le_max_right _ _
    linarith [show C_β * ((1 - ceVarphiP p t) + √h) / √v = C_β * (1 - ceVarphiP p t) / √v + C_β * √h / √v by ring]
  refine ⟨hH_eq, hbeta_err, fun _ => ?_⟩
  have hZ_bd : |σ * (fracZp p t).im| ≤ C_Z * √t := by
    rw [abs_mul, abs_of_nonneg hσ0, abs_of_nonneg (h_Z ht_pos.le).1]; exact (mul_le_of_le_one_left (h_Z ht_pos.le).1 hσ1).trans (h_Z ht_pos.le).2.2
  have hphi_v : (1 - ceVarphiP p t) / √v ≤ v₀ ^ (p - 1) * √t := by
    have hpow_eq : t ^ p / √v = (h ^ (p - 1 / 2) * v ^ (p - 1)) * √t := by
      dsimp [t, v]; rw [Real.mul_rpow hh0.le hv_pos.le, Real.sqrt_mul hh0.le, Real.sqrt_eq_rpow h,
        Real.sqrt_eq_rpow (airyZero 1 - u), div_eq_mul_inv, ← Real.rpow_neg hv_pos.le,
        show h ^ p = h ^ (1 / 2 : ℝ) * h ^ (p - 1 / 2) by rw [← Real.rpow_add hh0]; ring_nf, mul_assoc (h ^ (1 / 2 : ℝ) * h ^ (p - 1 / 2)),
        show (airyZero 1 - u) ^ p * (airyZero 1 - u) ^ (-(1 / 2 : ℝ)) = (airyZero 1 - u) ^ (1 / 2 : ℝ) * (airyZero 1 - u) ^ (p - 1) by
          rw [← Real.rpow_add hv_pos, ← Real.rpow_add hv_pos]; congr 1; ring]; ring
    calc (1 - ceVarphiP p t) / √v ≤ t ^ p / √v := div_le_div_of_nonneg_right ((one_sub_ceVarphiP_le_min ht_pos.le).trans (min_le_right _ _)) (Real.sqrt_nonneg _)
      _ = (h ^ (p - 1 / 2) * v ^ (p - 1)) * √t := hpow_eq
      _ ≤ (1 * v₀ ^ (p - 1)) * √t := mul_le_mul_of_nonneg_right (mul_le_mul (Real.rpow_le_one hh0.le hh.2 (by linarith [hp.1]))
          (Real.rpow_le_rpow_of_nonpos hv₀ hv_ge (by linarith [hp.2])) (Real.rpow_nonneg hv_pos.le _) zero_le_one) (Real.sqrt_nonneg _)
      _ = v₀ ^ (p - 1) * √t := by rw [one_mul]
  have hsqrt_v : √h / √v ≤ v₀⁻¹ * √t := by
    rw [show √h / √v = v⁻¹ * √t by dsimp [t, v]; rw [Real.sqrt_mul hh0.le]; field_simp [(Real.sqrt_pos.mpr hv_pos).ne']; rw [Real.sq_sqrt hv_pos.le]]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hv₀ hv_ge) (Real.sqrt_nonneg _)
  calc |cardinalBeta p h σ u| ≤ |cardinalBeta p h σ u - σ * (fracZp p t).im| + |σ * (fracZp p t).im| := by
        simpa [sub_add_cancel] using abs_add_le (cardinalBeta p h σ u - σ * (fracZp p t).im) (σ * (fracZp p t).im)
    _ ≤ C_β * ((1 - ceVarphiP p t) / √v + √h / √v) + C_Z * √t := by
        linarith [show C_β * ((1 - ceVarphiP p t) + √h) / √v = C_β * ((1 - ceVarphiP p t) / √v + √h / √v) by ring]
    _ ≤ C_β * (v₀ ^ (p - 1) * √t + v₀⁻¹ * √t) + C_Z * √t := by gcongr
    _ ≤ K₀ * √t := by dsimp [K₀]; linarith [Real.sqrt_nonneg t]

/-- **Lemma O.11p (`(ceo:O11p.uniform)`), Uniform quadratic-margin lower bound on `u ≤ a₁ - v₀`. -/
theorem cardinalQ_uniform_lower {p R₀ v₀ : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hR₀ : 0 ≤ R₀) (hv₀ : 0 < v₀) :
    ∃ h₀ > 0, ∀ {h σ : ℝ}, h ∈ Ioo 0 h₀ → 0 ≤ σ → σ ≤ 1 → 1 - σ ^ 2 ≤ R₀ * √h →
      ∀ {u : ℝ}, u ≤ airyZero 1 - v₀ →
        let t := h * (airyZero 1 - u)
        ((1 / 2 : ℝ) * (1 - ceVarphiP p t) + (1 - σ ^ 2) * ceVarphiP p t) *
          (ceG1Deriv airyDerivFirstZero u - ceF1 u) ≤ cardinalQ p h σ u := by
  have hp01 : p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], hp.2⟩
  obtain ⟨C_β, hC_β, K₀, hK₀, hdecomp⟩ := cardinalH_decomp_XY hp hR₀ hv₀
  obtain ⟨C_Z, hC_Z, h_Z⟩ := fracZp_im_bounds hp
  let A_sq : ℝ := max (C_β * (K₀ + C_Z)) (4 * C_β * (1 + 2 * C_β)) + 1
  let A_p : ℝ := 2 * C_β * (K₀ + C_Z) / v₀ ^ p + 1; have h1mp : 0 < 1 - p := sub_pos.mpr hp.2
  refine ⟨min 1 (min ((4 * A_sq) ^ (-2 : ℝ)) ((4 * A_p) ^ (-(1 - p)⁻¹))),
    lt_min one_pos (lt_min (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos (by positivity) _)),
    fun {h σ} hh hσ0 hσ1 hsig {u} hu => ?_⟩
  have hh0 : 0 < h := hh.1; have hh1 : h < 1 := lt_of_lt_of_le hh.2 (min_le_left _ _)
  have hv_ge : v₀ ≤ airyZero 1 - u := by linarith;
  have hv_pos : 0 < airyZero 1 - u := lt_of_lt_of_le hv₀ hv_ge
  obtain ⟨hH_eq, hβ_err, hβ_t⟩ := hdecomp ⟨hh0, hh1.le⟩ hσ0 hσ1 hsig hu
  let v := airyZero 1 - u; let t := h * v; have ht_pos : 0 < t := mul_pos hh0 hv_pos
  let X := cardinalHstar airyDerivFirstZero u; let Y := airyAi u / √v
  let α := σ * ceVarphiP p t; let β := cardinalBeta p h σ u; let φ := ceVarphiP p t; let d := 1 - φ; let imZ := (fracZp p t).im
  have hd_nn : 0 ≤ d := one_sub_ceVarphiP_nonneg ht_pos.le
  have hA_sq_bd : A_sq * √h ≤ 1 / 4 := by
    rw [Real.sqrt_eq_rpow]
    exact inv_rpow_bd (by positivity) hh0 (by norm_num : (0 : ℝ) < 1 / 2)
      ((show -(1 / 2 : ℝ)⁻¹ = (-2 : ℝ) by norm_num) ▸ hh.2.le.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hA_p_bd : A_p * h ^ (1 - p) ≤ 1 / 4 := inv_rpow_bd (by positivity) hh0 h1mp (hh.2.le.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hβ_sq_err : |β ^ 2 - σ ^ 2 * imZ ^ 2| ≤ d / 2 := by
    rw [show β ^ 2 - σ ^ 2 * imZ ^ 2 = (β - σ * imZ) * (β + σ * imZ) by ring, abs_mul]
    rcases le_or_gt t 1 with ht1 | ht1
    · have hsum_bd : |β + σ * imZ| ≤ (K₀ + C_Z) * √t := by
        have hσZ : |σ * imZ| ≤ C_Z * √t := by rw [abs_mul, abs_of_nonneg hσ0, abs_of_nonneg (h_Z ht_pos.le).1]; exact (mul_le_of_le_one_left (h_Z ht_pos.le).1 hσ1).trans (h_Z ht_pos.le).2.2
        exact ((abs_add_le _ _).trans (add_le_add (hβ_t ht1) hσZ)).trans_eq (by ring)
      have hd_lb : h ^ p * v₀ ^ p / 2 ≤ d := by
        have htp_le1 : t ^ p ≤ 1 := Real.rpow_le_one ht_pos.le ht1 hp01.1.le
        have htv : h ^ p * v₀ ^ p ≤ t ^ p := by dsimp [t]; rw [Real.mul_rpow hh0.le hv_pos.le]; exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hv₀.le hv_ge hp01.1.le) (Real.rpow_nonneg hh0.le _)
        rw [show d = t ^ p / (1 + t ^ p) by dsimp [d, φ]; unfold ceVarphiP; field_simp [show 1 + t ^ p ≠ 0 by positivity]; ring]
        exact (div_le_div_of_nonneg_right htv zero_le_two).trans (div_le_div_of_nonneg_left (Real.rpow_nonneg ht_pos.le _) (by positivity) (by linarith))
      have heq1 : (d + √h) / √v * √t = √h * d + h := by
        have hsqrt_tv : √t / √v = √h := by dsimp [t]; rw [Real.sqrt_mul hh0.le, mul_div_cancel_right₀ _ (Real.sqrt_pos.mpr hv_pos).ne']
        rw [add_div, add_mul, show d / √v * √t = d * (√t / √v) by ring, show √h / √v * √t = √h * (√t / √v) by ring, hsqrt_tv, Real.mul_self_sqrt hh0.le]; ring
      have h_t2 : C_β * (K₀ + C_Z) * h ≤ (A_p * h ^ (1 - p)) * d := by
        rw [show C_β * (K₀ + C_Z) * h = (2 * C_β * (K₀ + C_Z) / v₀ ^ p) * h ^ (1 - p) * (h ^ p * v₀ ^ p / 2) by
          conv_lhs => rw [show h = h ^ (1 - p) * h ^ p by rw [← Real.rpow_add hh0]; simp]
          field_simp [(Real.rpow_pos_of_pos hv₀ p).ne']]
        exact mul_le_mul (mul_le_mul_of_nonneg_right (by dsimp [A_p]; linarith) (Real.rpow_nonneg hh0.le _)) hd_lb (by positivity) (mul_nonneg (by positivity) (Real.rpow_nonneg hh0.le _))
      have h_t1 : C_β * (K₀ + C_Z) * √h * d ≤ (A_sq * √h) * d := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (by dsimp [A_sq]; linarith)) (Real.sqrt_nonneg h)) hd_nn
      exact ((mul_le_mul hβ_err hsum_bd (abs_nonneg _) (by positivity)).trans_eq
        (by rw [show (C_β * (d + √h) / √v) * ((K₀ + C_Z) * √t) = C_β * (K₀ + C_Z) * ((d + √h) / √v * √t) by ring, heq1]; ring)).trans
        ((add_le_add h_t1 h_t2).trans ((add_le_add (mul_le_mul_of_nonneg_right hA_sq_bd hd_nn) (mul_le_mul_of_nonneg_right hA_p_bd hd_nn)).trans_eq (by ring)))
    · have htp_ge1 : 1 ≤ t ^ p := Real.one_le_rpow ht1.le hp01.1.le
      have hd_lb : 1 / 2 ≤ d := by rw [show d = t ^ p / (1 + t ^ p) by dsimp [d, φ]; unfold ceVarphiP; field_simp [show 1 + t ^ p ≠ 0 by positivity]; ring, le_div_iff₀ (by positivity)]; linarith
      have hv_inv : 1 / √v ≤ √h :=
        (by dsimp [t]; rw [Real.sqrt_mul hh0.le]; field_simp [(Real.sqrt_pos.mpr hv_pos).ne', (Real.sqrt_pos.mpr hh0).ne'] : 1 / √v = √h / √t) ▸
          div_le_self (Real.sqrt_nonneg h) (Real.one_le_sqrt.mpr ht1.le)
      have hβ_diff : |β - σ * imZ| ≤ 2 * C_β * √h :=
        ((by dsimp [d, φ, v, t]; rw [← div_eq_mul_one_div]; exact hβ_err : |β - σ * imZ| ≤ _).trans
          (mul_le_mul (mul_le_mul_of_nonneg_left (by linarith [(one_sub_ceVarphiP_le_min (p := p) ht_pos.le).trans (min_le_left 1 (t ^ p)), Real.sqrt_le_one.mpr hh1.le] : d + √h ≤ 2) hC_β.le) hv_inv (by positivity) (by positivity))).trans_eq (by ring)
      have hσZ : |σ * imZ| ≤ 1 / 2 := by rw [abs_mul, abs_of_nonneg hσ0, abs_of_nonneg (h_Z ht_pos.le).1]; exact (mul_le_of_le_one_left (h_Z ht_pos.le).1 hσ1).trans (h_Z ht_pos.le).2.1
      have hβ_bd : |β| ≤ 1 / 2 + 2 * C_β := by have htri := abs_add_le (β - σ * imZ) (σ * imZ); rw [sub_add_cancel] at htri; linarith [mul_le_of_le_one_right (by positivity : 0 ≤ 2 * C_β) (Real.sqrt_le_one.mpr hh1.le)]
      calc _ ≤ (2 * C_β * √h) * (1 + 2 * C_β) := mul_le_mul hβ_diff ((abs_add_le _ _).trans (by linarith)) (abs_nonneg _) (by positivity)
        _ = (4 * C_β * (1 + 2 * C_β) * √h) * (1 / 2) := by ring
        _ ≤ (A_sq * √h) * d := mul_le_mul (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (by dsimp [A_sq]; linarith)) (Real.sqrt_nonneg h)) hd_lb (by norm_num) (by positivity)
        _ ≤ d / 2 := (mul_le_mul_of_nonneg_right hA_sq_bd hd_nn).trans (by linarith)
  have hB := o11p_B_eq_X_sq_add_Y_sq (sub_pos.mp hv_pos)
  have hZ_norm : φ ^ 2 + imZ ^ 2 ≤ φ := by have h1 := fracZp_norm_sq_le hp01 ht_pos.le; rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, fracZp_re_eq hp01 ht_pos.le] at h1; simpa [sq] using h1
  have hcoef : (1 / 2 : ℝ) * d + (1 - σ ^ 2) * φ ≤ 1 - (α ^ 2 + β ^ 2) := by
    have hασ : α ^ 2 + σ ^ 2 * imZ ^ 2 ≤ σ ^ 2 * φ := by rw [show α ^ 2 + σ ^ 2 * imZ ^ 2 = σ ^ 2 * (φ ^ 2 + imZ ^ 2) by dsimp [α]; ring]; exact mul_le_mul_of_nonneg_left hZ_norm (sq_nonneg σ)
    linarith [(abs_le.mp hβ_sq_err).2]
  rw [show cardinalQ p h σ u = (X ^ 2 + Y ^ 2) - (α * X + β * Y) ^ 2 by unfold cardinalQ cardinalP; dsimp [X, Y, α, β]; rw [hH_eq, ← hB.1]; ring, hB.1]
  exact (mul_le_mul_of_nonneg_right hcoef (by positivity)).trans (by linarith [sq_nonneg (α * Y - β * X)])

/-- **Lemma O.11p (`(ceo:O11p.3)`), Intermediate region `h v ≤ t₀ ≤ 1`. -/
theorem cardinalQ_intermediate_region {p R₀ v₀ t₀ : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1)
    (hR₀ : 0 ≤ R₀) (hv₀ : 0 < v₀) (ht₀ : t₀ ∈ Ioc (0 : ℝ) 1) :
    ∃ h₀ > 0, ∀ {h σ : ℝ}, h ∈ Ioo 0 h₀ → 0 ≤ σ → σ ≤ 1 → 1 - σ ^ 2 ≤ R₀ * √h →
      ∀ {u : ℝ}, u ≤ airyZero 1 - v₀ → h * (airyZero 1 - u) ≤ t₀ →
        let t := h * (airyZero 1 - u)
        ((1 / 2 : ℝ) * (1 - σ ^ 2) + (1 / 4 : ℝ) * t ^ p) * (ceG1Deriv airyDerivFirstZero u - ceF1 u) ≤ cardinalQ p h σ u := by
  obtain ⟨h₀, hh₀, hunif⟩ := cardinalQ_uniform_lower hp hR₀ hv₀
  refine ⟨h₀, hh₀, fun {h σ} hh hσ0 hσ1 hsig {u} hu htv => ?_⟩
  have hv_pos : 0 < airyZero 1 - u := by linarith
  have ht_pos : 0 < h * (airyZero 1 - u) := mul_pos hh.1 hv_pos
  have htp1 : (h * (airyZero 1 - u)) ^ p ≤ 1 := Real.rpow_le_one ht_pos.le (htv.trans ht₀.2) (by linarith [hp.1])
  have hφ_ge : 1 / 2 ≤ ceVarphiP p (h * (airyZero 1 - u)) := by unfold ceVarphiP; rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]; exact inv_anti₀ (by positivity) (by linarith)
  have h1φ_ge : (h * (airyZero 1 - u)) ^ p / 2 ≤ 1 - ceVarphiP p (h * (airyZero 1 - u)) := by
    unfold ceVarphiP; have hden : 0 < 1 + (h * (airyZero 1 - u)) ^ p := by positivity
    rw [show 1 - (1 + (h * (airyZero 1 - u)) ^ p)⁻¹ = (h * (airyZero 1 - u)) ^ p / (1 + (h * (airyZero 1 - u)) ^ p) by field_simp [hden.ne']; ring]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg ht_pos.le _) hden (by linarith)
  exact (mul_le_mul_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left hφ_ge (by nlinarith : 0 ≤ 1 - σ ^ 2)])
    (o11p_B_eq_X_sq_add_Y_sq (sub_pos.mp hv_pos)).2.le).trans (hunif hh hσ0 hσ1 hsig hu)

/-- **Lemma O.11p (`(ceo:O11p.4)`), Far bulk region `h v ≥ t₀ > 0`. -/
theorem cardinalQ_far_region {p R₀ v₀ t₀ : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1)
    (hR₀ : 0 ≤ R₀) (hv₀ : 0 < v₀) (ht₀ : 0 < t₀) :
    ∃ c₀ > 0, ∃ h₀ > 0, ∀ {h σ : ℝ}, h ∈ Ioo 0 h₀ → 0 ≤ σ → σ ≤ 1 → 1 - σ ^ 2 ≤ R₀ * √h →
      ∀ {u : ℝ}, u ≤ airyZero 1 - v₀ → t₀ ≤ h * (airyZero 1 - u) →
        c₀ * (ceG1Deriv airyDerivFirstZero u - ceF1 u) ≤ cardinalQ p h σ u := by
  obtain ⟨h₀, hh₀, hunif⟩ := cardinalQ_uniform_lower hp hR₀ hv₀
  let c₀ : ℝ := (1 / 2 : ℝ) * (1 - ceVarphiP p t₀)
  have hc₀ : 0 < c₀ := by
    have hlt : ceVarphiP p t₀ < 1 := by unfold ceVarphiP; exact inv_lt_one_of_one_lt₀ (by linarith [Real.rpow_pos_of_pos ht₀ p])
    dsimp [c₀]; linarith
  refine ⟨c₀, hc₀, h₀, hh₀, fun {h σ} hh hσ0 hσ1 hsig {u} hu htv => ?_⟩
  have hv_pos : 0 < airyZero 1 - u := by linarith
  have hanti : ceVarphiP p (h * (airyZero 1 - u)) ≤ ceVarphiP p t₀ := by unfold ceVarphiP; exact inv_anti₀ (add_pos_of_pos_of_nonneg zero_lt_one (Real.rpow_nonneg ht₀.le p)) (by gcongr; linarith [hp.1])
  have hφ_nn : 0 ≤ ceVarphiP p (h * (airyZero 1 - u)) := by unfold ceVarphiP; exact inv_nonneg.mpr (add_nonneg zero_le_one (Real.rpow_nonneg (mul_pos hh.1 hv_pos).le p))
  exact (mul_le_mul_of_nonneg_right (by dsimp [c₀]; nlinarith [mul_nonneg (by nlinarith : 0 ≤ 1 - σ ^ 2) hφ_nn])
    (o11p_B_eq_X_sq_add_Y_sq (sub_pos.mp hv_pos)).2.le).trans (hunif hh hσ0 hσ1 hsig hu)

/-- **Lemma O.11p (`ceo:O11p`), combined three-region summary covering all `u ≤ a₁`. -/
theorem lemma_O11p {p R₀ v₀ t₀ : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hR₀ : 0 ≤ R₀)
    (hv₀ : v₀ ∈ Ioo (0 : ℝ) (airyZero 1 - airyZero 2)) (ht₀ : t₀ ∈ Ioc (0 : ℝ) 1) :
    let m := sInf ((fun u => dslope airyAi (airyZero 1) u ^ 2) '' Icc (airyZero 1 - v₀) (airyZero 1))
    0 < m ∧ ∃ h₀ > 0, ∃ K₀ > 0, ∃ c₀ > 0, ∀ {h σ : ℝ}, h ∈ Ioo 0 h₀ → 0 ≤ σ → σ ≤ 1 → 1 - σ ^ 2 ≤ R₀ * √h →
      (∀ u ∈ Icc (airyZero 1 - v₀) (airyZero 1),
        |cardinalH p h σ u ^ 2 - ceG1Deriv airyDerivFirstZero u| ≤ K₀ * √h ∧ m * (airyZero 1 - u) - K₀ * √h ≤ cardinalQ p h σ u) ∧
      (∀ {u : ℝ}, u ≤ airyZero 1 - v₀ →
        let t := h * (airyZero 1 - u)
        ((1 / 2 : ℝ) * (1 - ceVarphiP p t) + (1 - σ ^ 2) * ceVarphiP p t) * (ceG1Deriv airyDerivFirstZero u - ceF1 u) ≤ cardinalQ p h σ u) ∧
      (∀ {u : ℝ}, u ≤ airyZero 1 - v₀ → h * (airyZero 1 - u) ≤ t₀ →
        ((1 / 2 : ℝ) * (1 - σ ^ 2) + (1 / 4 : ℝ) * (h * (airyZero 1 - u)) ^ p) * (ceG1Deriv airyDerivFirstZero u - ceF1 u) ≤ cardinalQ p h σ u) ∧
      (∀ {u : ℝ}, u ≤ airyZero 1 - v₀ → t₀ ≤ h * (airyZero 1 - u) → c₀ * (ceG1Deriv airyDerivFirstZero u - ceF1 u) ≤ cardinalQ p h σ u) := by
  obtain ⟨hm, h1, hh1, K₀, hK₀, hnear⟩ := cardinalQ_near_node hp hR₀ hv₀
  obtain ⟨h2, hh2, hunif⟩ := cardinalQ_uniform_lower hp hR₀ hv₀.1
  obtain ⟨h3, hh3, hinter⟩ := cardinalQ_intermediate_region hp hR₀ hv₀.1 ht₀
  obtain ⟨c₀, hc₀, h4, hh4, hfar⟩ := cardinalQ_far_region hp hR₀ hv₀.1 ht₀.1
  refine ⟨hm, min (min h1 h2) (min h3 h4), lt_min (lt_min hh1 hh2) (lt_min hh3 hh4), K₀, hK₀, c₀, hc₀,
    fun {h σ} hh hσ0 hσ1 hsig => ⟨hnear ⟨hh.1, hh.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))⟩ hσ0 hσ1 hsig,
      fun hu => hunif ⟨hh.1, hh.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))⟩ hσ0 hσ1 hsig hu,
      fun hu htv => hinter ⟨hh.1, hh.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩ hσ0 hσ1 hsig hu htv,
      fun hu htv => hfar ⟨hh.1, hh.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩ hσ0 hσ1 hsig hu htv⟩⟩

/-! ### Part 3: Theorem `O.11j` (`ceo:O11j`) — Far-Half-Line WKB Asymptotics & Positivity -/

private lemma abs_sq_sub_sq_far_le {x C u Lu : ℝ} (hx : 1 ≤ x)
    (hdiff : |u - Lu| ≤ C * x ^ (-(7 / 4 : ℝ))) (hLu : |Lu| ≤ (1 / √π) * x ^ (-(3 / 4 : ℝ))) :
    |u ^ 2 - Lu ^ 2| ≤ (2 / √π * C + C ^ 2) * x ^ (-(5 / 2 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  have hsum : |u + Lu| ≤ (2 / √π) * x ^ (-(3 / 4 : ℝ)) + C * x ^ (-(7 / 4 : ℝ)) := by
    have ht := abs_add_le (u - Lu) (2 * Lu); rw [show u - Lu + 2 * Lu = u + Lu by ring, abs_mul, abs_two] at ht
    linarith [hdiff, hLu, show 2 * ((1 / √π) * x ^ (-(3 / 4 : ℝ))) = (2 / √π) * x ^ (-(3 / 4 : ℝ)) by ring]
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans hdiff) (Real.rpow_pos_of_pos hx0 _)
  have h77 : x ^ (-(7 / 4 : ℝ)) * x ^ (-(7 / 4 : ℝ)) ≤ x ^ (-(5 / 2 : ℝ)) := by rw [← Real.rpow_add hx0]; exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  rw [sq_sub_sq, abs_mul, mul_comm]
  exact ((mul_le_mul hdiff hsum (abs_nonneg _) (by positivity)).trans_eq
    (by rw [show (C * x ^ (-(7 / 4 : ℝ))) * ((2 / √π) * x ^ (-(3 / 4 : ℝ)) + C * x ^ (-(7 / 4 : ℝ))) =
      (2 / √π * C) * (x ^ (-(7 / 4 : ℝ)) * x ^ (-(3 / 4 : ℝ))) + C ^ 2 * (x ^ (-(7 / 4 : ℝ)) * x ^ (-(7 / 4 : ℝ))) by ring,
      rpow_add_eq hx0 (show -(7 / 4 : ℝ) + -(3 / 4 : ℝ) = -(5 / 2 : ℝ) by norm_num)])).trans (by linarith [mul_le_mul_of_nonneg_left h77 (sq_nonneg C)])

private lemma cardinalXY_far_asymptotic :
    ∃ C > 0, ∀ {x : ℝ}, 10 ≤ x →
      |cardinalHstar airyDerivFirstZero (-x) - π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) * Real.cos (cohnTheta x)| ≤ C * x ^ (-(7 / 4 : ℝ)) ∧
      |airyAi (-x) / √(airyZero 1 - (-x)) - π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) * Real.sin (cohnTheta x)| ≤ C * x ^ (-(7 / 4 : ℝ)) ∧
      |airyAi (-x)| ≤ C * x ^ (-(1 / 4 : ℝ)) := by
  let a := airyDerivFirstZero
  let C : ℝ := max (4 / 5 + 4.7 / √π) (max (√2 / 8 + 2.35 * √2 / √π) (1 / √π + 1 / 8)) + 1
  refine ⟨C, by positivity, fun {x} hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have ha1 := airyZero_one; have ha := airyDerivFirstZero_spec
  have hv_half : x / 2 ≤ x + airyZero 1 := by linarith
  have hv_pos : 0 < x + airyZero 1 := by linarith
  have hw_pos : 0 < x + a := by linarith [ha.1]
  have hX : |cardinalHstar a (-x) - π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) * Real.cos (cohnTheta x)| ≤ (4 / 5 + 4.7 / √π) * x ^ (-(7 / 4 : ℝ)) := by
    rw [cardinalHstar_of_ne ha.2.2 (by linarith [ha.1] : -x ≠ a)]
    have hsplit : airyAi' (-x) / (-x - a) - π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) * Real.cos (cohnTheta x) =
        -(airyAi' (-x) + x ^ (1 / 4 : ℝ) * Real.cos (cohnTheta x) / √π) / (x + a) +
          (x ^ (1 / 4 : ℝ) * Real.cos (cohnTheta x) / √π) * ((x + a)⁻¹ - x⁻¹) := by
      rw [pi_rpow_neg_half, show x ^ (-(3 / 4 : ℝ)) = x ^ (1 / 4 : ℝ) * x⁻¹ by rw [← Real.rpow_neg_one x, rpow_add_eq hx0 (by norm_num : (1 / 4 : ℝ) + -1 = -(3 / 4))],
        show -x - a = -(x + a) by ring]
      field_simp [hw_pos.ne', hx0.ne', (Real.sqrt_pos.mpr Real.pi_pos).ne']; ring
    have ht1 : |-(airyAi' (-x) + x ^ (1 / 4 : ℝ) * Real.cos (cohnTheta x) / √π) / (x + a)| ≤ (4 / 5 : ℝ) * x ^ (-(7 / 4 : ℝ)) := by
      rw [abs_div, abs_neg, abs_of_pos hw_pos]
      have hpow : (x ^ (5 / 4 : ℝ) * x)⁻¹ = x ^ (-(9 / 4 : ℝ)) := (rpow_mul_x_inv hx0).trans (by norm_num)
      exact ((div_le_div₀ (by positivity) (airyAi'_neg_asymptotic_theta hx0) (by positivity) (by linarith : x / 2 ≤ x + a)).trans_eq
        (by rw [show (2 / (5 * x ^ (5 / 4 : ℝ))) / (x / 2) = (4 / 5 : ℝ) * (x ^ (5 / 4 : ℝ) * x)⁻¹ by ring, hpow])).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)) (by norm_num))
    have ht2 : |(x ^ (1 / 4 : ℝ) * Real.cos (cohnTheta x) / √π) * ((x + a)⁻¹ - x⁻¹)| ≤ (4.7 / √π) * x ^ (-(7 / 4 : ℝ)) := by
      have hid : (x + a)⁻¹ - x⁻¹ = (-a) / (x * (x + a)) := by field_simp [hw_pos.ne', hx0.ne']; ring
      have hpow : x ^ (1 / 4 : ℝ) * (x * x)⁻¹ = x ^ (-(7 / 4 : ℝ)) := by
        rw [show x * x = x ^ (2 : ℝ) by norm_cast; ring, ← Real.rpow_neg hx0.le, rpow_add_eq hx0 (by norm_num : (1 / 4 : ℝ) + -2 = -(7 / 4))]
      rw [abs_mul, abs_div, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _), abs_of_pos (Real.sqrt_pos.mpr Real.pi_pos),
        hid, abs_div, abs_of_pos (neg_pos.mpr ha.2.1), abs_of_pos (mul_pos hx0 hw_pos)]
      exact (mul_le_mul (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.rpow_nonneg hx0.le _)) (Real.sqrt_nonneg _))
        (div_le_div₀ (by positivity) (by dsimp [a]; linarith [ha.1, ha1.1] : -a ≤ 2.35) (by positivity) (mul_le_mul_of_nonneg_left (by linarith : x / 2 ≤ x + a) hx0.le))
        (div_nonneg (neg_nonneg.mpr ha.2.1.le) (mul_pos hx0 hw_pos).le) (by positivity)).trans_eq
        (by rw [show x ^ (1 / 4 : ℝ) * 1 / √π * (2.35 / (x * (x / 2))) = (4.7 / √π) * (x ^ (1 / 4 : ℝ) * (x * x)⁻¹) by ring, hpow])
    rw [hsplit]; exact ((abs_add_le _ _).trans (add_le_add ht1 ht2)).trans_eq (by ring)
  have hY : |airyAi (-x) / √(airyZero 1 - (-x)) - π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) * Real.sin (cohnTheta x)| ≤
      (√2 / 8 + 2.35 * √2 / √π) * x ^ (-(7 / 4 : ℝ)) := by
    have hsplit : airyAi (-x) / √(x + airyZero 1) - π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) * Real.sin (cohnTheta x) =
        (airyAi (-x) - Real.sin (cohnTheta x) / (√π * x ^ (1 / 4 : ℝ))) / √(x + airyZero 1) +
          (Real.sin (cohnTheta x) / (√π * x ^ (1 / 4 : ℝ))) * ((√(x + airyZero 1))⁻¹ - (√x)⁻¹) := by
      rw [pi_rpow_neg_half, show x ^ (-(3 / 4 : ℝ)) = (x ^ (1 / 4 : ℝ))⁻¹ * (√x)⁻¹ by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hx0.le, ← Real.rpow_neg hx0.le, rpow_add_eq hx0 (by norm_num : -(1 / 4 : ℝ) + -(1 / 2) = -(3 / 4))]]; ring
    have ht1 : |(airyAi (-x) - Real.sin (cohnTheta x) / (√π * x ^ (1 / 4 : ℝ))) / √(x + airyZero 1)| ≤ (√2 / 8) * x ^ (-(7 / 4 : ℝ)) := by
      rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr hv_pos)]
      have hpow : (x ^ (7 / 4 : ℝ) * √x)⁻¹ = x ^ (-(9 / 4 : ℝ)) := by rw [Real.sqrt_eq_rpow, rpow_add_eq hx0 (by norm_num : (7 / 4 : ℝ) + 1 / 2 = 9 / 4), ← Real.rpow_neg hx0.le]
      exact ((div_le_div₀ (by positivity) (airyAi_neg_asymptotic_theta hx0) (by positivity) (Real.sqrt_le_sqrt hv_half)).trans_eq
        (by rw [Real.sqrt_div hx0.le, show (1 / (8 * x ^ (7 / 4 : ℝ))) / (√x / √2) = (√2 / 8) * (x ^ (7 / 4 : ℝ) * √x)⁻¹ by
          field_simp [Real.sqrt_ne_zero'.mpr hx0, Real.sqrt_ne_zero'.mpr zero_lt_two], hpow])).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)) (by positivity))
    have ht2 : |(Real.sin (cohnTheta x) / (√π * x ^ (1 / 4 : ℝ))) * ((√(x + airyZero 1))⁻¹ - (√x)⁻¹)| ≤ (2.35 * √2 / √π) * x ^ (-(7 / 4 : ℝ)) := by
      have hid : (√(x + airyZero 1))⁻¹ - (√x)⁻¹ = (-airyZero 1) / (√(x + airyZero 1) * √x * (√x + √(x + airyZero 1))) := by
        field_simp [(Real.sqrt_pos.mpr hv_pos).ne', (Real.sqrt_pos.mpr hx0).ne', (by positivity : √x + √(x + airyZero 1) ≠ 0)]
        nlinarith only [Real.sq_sqrt hx0.le, Real.sq_sqrt hv_pos.le]
      have hden_ge : √(x / 2) * x ≤ √(x + airyZero 1) * √x * (√x + √(x + airyZero 1)) :=
        (by rw [mul_assoc, Real.mul_self_sqrt hx0.le] : √(x / 2) * x = (√(x / 2) * √x) * √x).trans_le
          (mul_le_mul (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hv_half) (Real.sqrt_nonneg _)) (by linarith [Real.sqrt_nonneg (x + airyZero 1)]) (Real.sqrt_nonneg _) (by positivity))
      have hpow : (x ^ (1 / 4 : ℝ) * √x * x)⁻¹ = x ^ (-(7 / 4 : ℝ)) := by
        rw [Real.sqrt_eq_rpow x, rpow_add_eq hx0 (by norm_num : (1 / 4 : ℝ) + 1 / 2 = 3 / 4)]; exact (rpow_mul_x_inv hx0).trans (by norm_num)
      rw [abs_mul, abs_div, abs_mul, abs_of_pos (Real.sqrt_pos.mpr Real.pi_pos), abs_of_nonneg (Real.rpow_nonneg hx0.le _),
        hid, abs_div, abs_of_pos (neg_pos.mpr (airyZero_neg 1)), abs_of_pos (by positivity : 0 < √(x + airyZero 1) * √x * (√x + √(x + airyZero 1)))]
      exact (mul_le_mul (div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity))
        (div_le_div₀ (by positivity) (by linarith [ha1.1] : -airyZero 1 ≤ 2.35) (by positivity) hden_ge) (div_nonneg (neg_nonneg.mpr (airyZero_neg 1).le) (by positivity))
        (by positivity)).trans_eq (by rw [Real.sqrt_div hx0.le, show 1 / (√π * x ^ (1 / 4 : ℝ)) * (2.35 / (√x / √2 * x)) = (2.35 * √2 / √π) * (x ^ (1 / 4 : ℝ) * √x * x)⁻¹ by
          field_simp [Real.sqrt_ne_zero'.mpr hx0, Real.sqrt_ne_zero'.mpr zero_lt_two], hpow])
    rw [show airyZero 1 - (-x) = x + airyZero 1 by ring, hsplit]; exact ((abs_add_le _ _).trans (add_le_add ht1 ht2)).trans_eq (by ring)
  have hAi_bd : |airyAi (-x)| ≤ (1 / √π + 1 / 8) * x ^ (-(1 / 4 : ℝ)) := by
    have h1 : |Real.sin (cohnTheta x) / (√π * x ^ (1 / 4 : ℝ))| ≤ (1 / √π) * x ^ (-(1 / 4 : ℝ)) := by
      rw [abs_div, abs_of_pos (by positivity : 0 < √π * x ^ (1 / 4 : ℝ)), show (1 / √π) * x ^ (-(1 / 4 : ℝ)) = 1 / (√π * x ^ (1 / 4 : ℝ)) by rw [Real.rpow_neg hx0.le]; ring]
      exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)
    have h2 : 1 / (8 * x ^ (7 / 4 : ℝ)) ≤ (1 / 8) * x ^ (-(1 / 4 : ℝ)) := by
      rw [show 1 / (8 * x ^ (7 / 4 : ℝ)) = (1 / 8) * x ^ (-(7 / 4 : ℝ)) by rw [Real.rpow_neg hx0.le]; ring]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)) (by norm_num)
    have htri := abs_sub_abs_le_abs_sub (airyAi (-x)) (Real.sin (cohnTheta x) / (√π * x ^ (1 / 4 : ℝ))); linarith [airyAi_neg_asymptotic_theta hx0]
  refine ⟨hX.trans (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (by dsimp [C]; exact le_add_of_nonneg_right zero_le_one)) (by positivity)),
    hY.trans (mul_le_mul_of_nonneg_right (((le_max_left _ _).trans (le_max_right _ _)).trans (by dsimp [C]; exact le_add_of_nonneg_right zero_le_one)) (by positivity)),
    hAi_bd.trans (mul_le_mul_of_nonneg_right (((le_max_right _ _).trans (le_max_right _ _)).trans (by dsimp [C]; exact le_add_of_nonneg_right zero_le_one)) (by positivity))⟩

/-- **Theorem O.11j (`(ceo:O11j.10)` & `(ceo:O11j.9)`), uniform WKB asymptotic and decay of `H_{s,h}(-x)` for `x ≥ 10`. -/
theorem cardinalResolventH_far_asymptotic :
    ∃ C > 0, ∀ {s h x : ℝ}, 0 < s → 0 < h → 10 ≤ x →
      |cardinalResolventH s h (-x) - π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) *
        ((1 + s * h * x)⁻¹ * Real.cos (cohnTheta x) + (√(s * h * x) / (1 + s * h * x)) * Real.sin (cohnTheta x))| ≤ C * x ^ (-(5 / 4 : ℝ)) ∧
      |cardinalResolventH s h (-x)| ≤ C * x ^ (-(3 / 4 : ℝ)) := by
  obtain ⟨C_XY, hC_XY, hXY⟩ := cardinalXY_far_asymptotic; obtain ⟨C_J, hC_J, hJ⟩ := cardinalJ_asymptotic
  let C_rem : ℝ := C_XY + 4.7 / √π + 2 * C_J * C_XY + 1 / √2 + 2.35 * √2 / (2 * √π)
  let C_all : ℝ := max C_rem (C_rem + 2 / √π)
  refine ⟨C_all, by positivity, fun {s h x} hs hh hx => ?_⟩
  have hx0 : 0 < x := by linarith;
  have hx1 : 1 ≤ x := by linarith
  have hv_half : x / 2 ≤ x + airyZero 1 := by linarith [airyZero_one];
  have hv_pos : 0 < airyZero 1 - (-x) := by linarith
  obtain ⟨hX_bd, _, hAi_bd⟩ := hXY hx
  let v := airyZero 1 - (-x)
  have hden_v : 0 < 1 + s * h * v := by positivity
  have hden_x : 0 < 1 + s * h * x := by positivity
  have hres_eq : cardinalResolventH s h (-x) = (1 + s * h * v)⁻¹ * cardinalHstar airyDerivFirstZero (-x) + cardinalJ (s * h) * airyAi (-x) / (1 + s * h * v) := by
    rw [cardinalResolventH_eq_XY hs hh (sub_pos.mp hv_pos)]; dsimp [v]; field_simp [(Real.sqrt_pos.mpr hv_pos).ne']
  have hsplit : cardinalResolventH s h (-x) - π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) *
        ((1 + s * h * x)⁻¹ * Real.cos (cohnTheta x) + (√(s * h * x) / (1 + s * h * x)) * Real.sin (cohnTheta x)) =
      (1 + s * h * v)⁻¹ * (cardinalHstar airyDerivFirstZero (-x) - π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) * Real.cos (cohnTheta x)) +
      (π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) * Real.cos (cohnTheta x)) * ((1 + s * h * v)⁻¹ - (1 + s * h * x)⁻¹) +
      ((cardinalJ (s * h) - √(s * h)) / (1 + s * h * v)) * airyAi (-x) +
      (√(s * h) / (1 + s * h * v)) * (airyAi (-x) - Real.sin (cohnTheta x) / (√π * x ^ (1 / 4 : ℝ))) +
      (Real.sin (cohnTheta x) / (√π * x ^ (1 / 4 : ℝ))) * (√(s * h) / (1 + s * h * v) - √(s * h) / (1 + s * h * x)) := by
    have hpow : x ^ (-(3 / 4 : ℝ)) * √(s * h * x) = √(s * h) * (x ^ (1 / 4 : ℝ))⁻¹ := by
      rw [Real.sqrt_mul (mul_pos hs hh).le, Real.sqrt_eq_rpow x, mul_left_comm, rpow_add_eq hx0 (by norm_num : -(3 / 4 : ℝ) + 1 / 2 = -(1 / 4)), Real.rpow_neg hx0.le]
    rw [hres_eq, pi_rpow_neg_half, show (1 / √π) * x ^ (-(3 / 4 : ℝ)) * ((1 + s * h * x)⁻¹ * Real.cos (cohnTheta x) +
        (√(s * h * x) / (1 + s * h * x)) * Real.sin (cohnTheta x)) =
        (1 / √π) * x ^ (-(3 / 4 : ℝ)) * (1 + s * h * x)⁻¹ * Real.cos (cohnTheta x) +
          (1 / √π) * (x ^ (-(3 / 4 : ℝ)) * √(s * h * x)) / (1 + s * h * x) * Real.sin (cohnTheta x) by ring, hpow]; ring
  have hx75 : x ^ (-(7 / 4 : ℝ)) ≤ x ^ (-(5 / 4 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have ht1 : |(1 + s * h * v)⁻¹ * (cardinalHstar airyDerivFirstZero (-x) - π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) * Real.cos (cohnTheta x))| ≤ C_XY * x ^ (-(5 / 4 : ℝ)) := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hden_v)]
    exact (mul_le_of_le_one_left (abs_nonneg _) (inv_le_one_of_one_le₀ (by linarith [mul_pos (mul_pos hs hh) hv_pos]))).trans (hX_bd.trans (mul_le_mul_of_nonneg_left hx75 hC_XY.le))
  have ht2 : |(π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) * Real.cos (cohnTheta x)) * ((1 + s * h * v)⁻¹ - (1 + s * h * x)⁻¹)| ≤ (4.7 / √π) * x ^ (-(5 / 4 : ℝ)) := by
    have hid : (1 + s * h * v)⁻¹ - (1 + s * h * x)⁻¹ = (-airyZero 1 / v) * (s * h * v / (1 + s * h * v)) * (1 + s * h * x)⁻¹ := by
      dsimp [v]; field_simp [hden_v.ne', hden_x.ne', hv_pos.ne']; ring
    have hdiff_bd : |(1 + s * h * v)⁻¹ - (1 + s * h * x)⁻¹| ≤ 4.7 * x⁻¹ := by
      rw [hid, abs_mul, abs_mul, abs_of_pos (div_pos (neg_pos.mpr (airyZero_neg 1)) hv_pos), abs_of_pos (div_pos (by positivity) hden_v), abs_of_pos (inv_pos.mpr hden_x)]
      exact (mul_le_mul (mul_le_mul (div_le_div₀ (by positivity) (by linarith [airyZero_one] : -airyZero 1 ≤ 2.35) (by positivity) (by dsimp [v]; linarith [airyZero_one] : x / 2 ≤ v))
        (div_le_one_of_le₀ (by linarith) hden_v.le) (by positivity) (by positivity))
        (inv_le_one_of_one_le₀ (by linarith [mul_pos (mul_pos hs hh) hx0])) (by positivity) (by positivity)).trans_eq (by ring)
    rw [abs_mul, pi_rpow_neg_half, abs_mul, abs_mul, abs_of_pos (div_pos one_pos (Real.sqrt_pos.mpr Real.pi_pos)), abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    exact ((mul_le_mul (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)) hdiff_bd (abs_nonneg _) (by positivity)).trans_eq
      (by rw [← Real.rpow_neg_one x, show (1 / √π * x ^ (-(3 / 4 : ℝ)) * 1) * (4.7 * x ^ (-1 : ℝ)) = (4.7 / √π) * (x ^ (-(3 / 4 : ℝ)) * x ^ (-1 : ℝ)) by ring,
        rpow_add_eq hx0 (by norm_num : -(3 / 4 : ℝ) + -1 = -(7 / 4))])).trans (by gcongr)
  have ht3 : |((cardinalJ (s * h) - √(s * h)) / (1 + s * h * v)) * airyAi (-x)| ≤ (2 * C_J * C_XY) * x ^ (-(5 / 4 : ℝ)) := by
    rw [abs_mul, abs_div, abs_of_pos hden_v]
    have h1 : |cardinalJ (s * h) - √(s * h)| / (1 + s * h * v) ≤ 2 * C_J * x⁻¹ := by
      have hid : (C_J * (s * h)) / (1 + s * h * v) = (C_J / v) * (s * h * v / (1 + s * h * v)) := by
        rw [div_eq_mul_inv C_J v, show C_J * v⁻¹ * (s * h * v / (1 + s * h * v)) = (v⁻¹ * v) * (C_J * (s * h) / (1 + s * h * v)) by ring, inv_mul_cancel₀ hv_pos.ne', one_mul]
      exact (div_le_div_of_nonneg_right (hJ (s * h) (mul_pos hs hh)) hden_v.le).trans
        (hid ▸ (mul_le_mul (div_le_div_of_nonneg_left hC_J.le (by positivity) (by dsimp [v]; linarith [airyZero_one] : x / 2 ≤ v)) (div_le_one_of_le₀ (by linarith) hden_v.le) (by positivity) (by positivity)).trans_eq (by ring))
    exact (mul_le_mul h1 hAi_bd (abs_nonneg _) (by positivity)).trans_eq
      (by rw [show (2 * C_J * x⁻¹) * (C_XY * x ^ (-(1 / 4 : ℝ))) = (2 * C_J * C_XY) * (x ^ (-1 : ℝ) * x ^ (-(1 / 4 : ℝ))) by
        rw [Real.rpow_neg_one]; ring, rpow_add_eq hx0 (by norm_num : (-1 : ℝ) + -(1 / 4) = -(5 / 4))])
  have ht4 : |(√(s * h) / (1 + s * h * v)) * (airyAi (-x) - Real.sin (cohnTheta x) / (√π * x ^ (1 / 4 : ℝ)))| ≤ (1 / √2) * x ^ (-(5 / 4 : ℝ)) := by
    rw [abs_mul, abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hden_v.le)]
    have hsq2 : (2 : ℝ)⁻¹ * √2 = (√2)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [mul_assoc, Real.mul_self_sqrt zero_le_two, inv_mul_cancel₀ two_ne_zero])
    have h1 : √(s * h) / (1 + s * h * v) ≤ (1 / √2) * x ^ (-(1 / 2 : ℝ)) := by
      rw [show √(s * h) / (1 + s * h * v) = (√(s * h * v) / (1 + s * h * v)) / √v by
        rw [Real.sqrt_mul (mul_pos hs hh).le, div_eq_mul_inv _ (√v),
          show (√(s * h) * √v / (1 + s * h * v)) * (√v)⁻¹ = (√v * (√v)⁻¹) * (√(s * h) / (1 + s * h * v)) by ring,
          mul_inv_cancel₀ (Real.sqrt_pos.mpr hv_pos).ne', one_mul]]
      exact (div_le_div₀ (by norm_num) (sqrt_div_one_add_le (mul_pos (mul_pos hs hh) hv_pos).le) (by positivity)
        (Real.sqrt_le_sqrt (by dsimp [v]; linarith [airyZero_one] : x / 2 ≤ v))).trans_eq
        (by rw [Real.sqrt_div hx0.le, one_div (√2), div_eq_mul_inv (1 / 2), div_eq_mul_inv (√x), mul_inv, inv_inv,
          Real.sqrt_eq_rpow x, Real.rpow_neg hx0.le, show (1 / 2 : ℝ) = 2⁻¹ by norm_num, ← hsq2]; ring)
    calc √(s * h) / (1 + s * h * v) * |airyAi (-x) - Real.sin (cohnTheta x) / (√π * x ^ (1 / 4 : ℝ))|
        ≤ ((1 / √2) * x ^ (-(1 / 2 : ℝ))) * (1 / (8 * x ^ (7 / 4 : ℝ))) := mul_le_mul h1 (airyAi_neg_asymptotic_theta hx0) (abs_nonneg _) (by positivity)
      _ ≤ (1 / √2) * x ^ (-(9 / 4 : ℝ)) := by
          rw [show 1 / (8 * x ^ (7 / 4 : ℝ)) = (1 / 8) * x ^ (-(7 / 4 : ℝ)) by rw [Real.rpow_neg hx0.le]; ring,
            show (1 / √2) * x ^ (-(1 / 2 : ℝ)) * ((1 / 8) * x ^ (-(7 / 4 : ℝ))) = (1 / 8) * ((1 / √2) * (x ^ (-(1 / 2 : ℝ)) * x ^ (-(7 / 4 : ℝ)))) by ring,
            rpow_add_eq hx0 (by norm_num : -(1 / 2 : ℝ) + -(7 / 4 : ℝ) = -(9 / 4 : ℝ))]
          linarith only [mul_nonneg (by positivity : 0 ≤ 1 / √2) (Real.rpow_nonneg hx0.le (-(9 / 4 : ℝ)))]
      _ ≤ (1 / √2) * x ^ (-(5 / 4 : ℝ)) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)) (by positivity)
  have ht5 : |(Real.sin (cohnTheta x) / (√π * x ^ (1 / 4 : ℝ))) * (√(s * h) / (1 + s * h * v) - √(s * h) / (1 + s * h * x))| ≤ (2.35 * √2 / (2 * √π)) * x ^ (-(5 / 4 : ℝ)) := by
    have hid : √(s * h) / (1 + s * h * v) - √(s * h) / (1 + s * h * x) = ((-airyZero 1) / (√v * x)) * (√(s * h * v) / (1 + s * h * v)) * (s * h * x / (1 + s * h * x)) := by
      have hvx : -airyZero 1 = x - v := by dsimp [v]; ring
      rw [Real.sqrt_mul (mul_pos hs hh).le, hvx, div_sub_div _ _ hden_v.ne' hden_x.ne', div_mul_div_comm, div_mul_div_comm]
      have hcancel : (x - v) * (√(s * h) * √v) * (s * h * x) = (√v * x) * (√(s * h) * (1 + s * h * x) - √(s * h) * (1 + s * h * v)) := by ring
      rw [hcancel, show √v * x * (1 + s * h * v) * (1 + s * h * x) = (√v * x) * ((1 + s * h * v) * (1 + s * h * x)) by ring,
        mul_div_mul_left _ _ (mul_pos (Real.sqrt_pos.mpr hv_pos) hx0).ne']; ring
    have hdiff_bd : |√(s * h) / (1 + s * h * v) - √(s * h) / (1 + s * h * x)| ≤ (2.35 * √2 / 2) * x ^ (-(3 / 2 : ℝ)) := by
      rw [hid, abs_mul, abs_mul, abs_of_pos (div_pos (neg_pos.mpr (airyZero_neg 1)) (mul_pos (Real.sqrt_pos.mpr hv_pos) hx0)),
        abs_of_pos (div_pos (Real.sqrt_pos.mpr (mul_pos (mul_pos hs hh) hv_pos)) hden_v), abs_of_pos (div_pos (mul_pos (mul_pos hs hh) hx0) hden_x)]
      have hpow : (√x * x)⁻¹ = x ^ (-(3 / 2 : ℝ)) := by rw [Real.sqrt_eq_rpow x]; exact (rpow_mul_x_inv hx0).trans (by norm_num)
      exact (mul_le_mul (mul_le_mul (div_le_div₀ (by positivity) (by linarith [airyZero_one] : -airyZero 1 ≤ 2.35) (by positivity)
        (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by dsimp [v]; linarith [airyZero_one] : x / 2 ≤ v)) hx0.le))
        (sqrt_div_one_add_le (mul_pos (mul_pos hs hh) hv_pos).le) (by positivity) (by positivity))
        (div_le_one_of_le₀ (by linarith) hden_x.le) (by positivity) (by positivity)).trans_eq
        (by rw [Real.sqrt_div hx0.le, div_eq_mul_inv (2.35), div_eq_mul_inv (√x), mul_inv, mul_inv, inv_inv, ← hpow, mul_inv]; ring)
    rw [abs_mul, abs_div, abs_of_pos (by positivity : 0 < √π * x ^ (1 / 4 : ℝ))]
    calc _ ≤ (1 / (√π * x ^ (1 / 4 : ℝ))) * ((2.35 * √2 / 2) * x ^ (-(3 / 2 : ℝ))) := mul_le_mul (div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)) hdiff_bd (abs_nonneg _) (by positivity)
      _ = (2.35 * √2 / (2 * √π)) * (x ^ (-(1 / 4 : ℝ)) * x ^ (-(3 / 2 : ℝ))) := by rw [Real.rpow_neg hx0.le (1 / 4), Real.rpow_neg hx0.le (3 / 2)]; ring
      _ = (2.35 * √2 / (2 * √π)) * x ^ (-(7 / 4 : ℝ)) := by rw [rpow_add_eq hx0 (by norm_num : -(1 / 4 : ℝ) + -(3 / 2) = -(7 / 4))]
      _ ≤ (2.35 * √2 / (2 * √π)) * x ^ (-(5 / 4 : ℝ)) := by gcongr
  have hmain_err : |cardinalResolventH s h (-x) - π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) *
      ((1 + s * h * x)⁻¹ * Real.cos (cohnTheta x) + (√(s * h * x) / (1 + s * h * x)) * Real.sin (cohnTheta x))| ≤ C_rem * x ^ (-(5 / 4 : ℝ)) := by
    rw [hsplit]
    exact ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)).trans
      (by dsimp [C_rem]; linarith)
  have hlead_bd : |π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) *
      ((1 + s * h * x)⁻¹ * Real.cos (cohnTheta x) + (√(s * h * x) / (1 + s * h * x)) * Real.sin (cohnTheta x))| ≤ (2 / √π) * x ^ (-(3 / 4 : ℝ)) := by
    have h1 : |(1 + s * h * x)⁻¹ * Real.cos (cohnTheta x)| ≤ 1 := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hden_x)]
      exact (mul_le_of_le_one_right (inv_nonneg.mpr hden_x.le) (Real.abs_cos_le_one _)).trans (inv_le_one_of_one_le₀ (by linarith [mul_pos (mul_pos hs hh) hx0]))
    have h2 : |(√(s * h * x) / (1 + s * h * x)) * Real.sin (cohnTheta x)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hden_x.le)]
      exact (mul_le_of_le_one_right (div_nonneg (Real.sqrt_nonneg _) hden_x.le) (Real.abs_sin_le_one _)).trans ((sqrt_div_one_add_le (mul_pos (mul_pos hs hh) hx0).le).trans (by norm_num))
    rw [abs_mul, abs_mul, pi_rpow_neg_half, abs_of_pos (div_pos one_pos (Real.sqrt_pos.mpr Real.pi_pos)), abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    exact (mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add h1 h2)) (by positivity)).trans_eq (by ring)
  have htri := abs_sub_abs_le_abs_sub (cardinalResolventH s h (-x))
    (π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) * ((1 + s * h * x)⁻¹ * Real.cos (cohnTheta x) + (√(s * h * x) / (1 + s * h * x)) * Real.sin (cohnTheta x)))
  have hscale_rem := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : -(5 / 4 : ℝ) ≤ -(3 / 4 : ℝ))) (by positivity : 0 ≤ C_rem)
  exact ⟨hmain_err.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)),
    (by linarith : |cardinalResolventH s h (-x)| ≤ (C_rem + 2 / √π) * x ^ (-(3 / 4 : ℝ))).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))⟩

/-- **Theorem O.11j (`(ceo:O11j.5)` & `(ceo:O11j.7)`), uniform far-half-line asymptotics for `H_h(-x)` and `g₁'(-x) - f₁(-x)`. -/
theorem cardinalH_far_asymptotic {p : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) :
    ∃ C > 0, ∀ {h x : ℝ}, h ∈ Ioc (0 : ℝ) 1 → 10 ≤ x →
      |cardinalH p h 1 (-x) - π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) *
        ((fracZp p (h * x)).re * Real.cos (cohnTheta x) + (fracZp p (h * x)).im * Real.sin (cohnTheta x))| ≤
          C * x ^ (-(3 / 4 : ℝ)) * (x ^ (-(1 / 2 : ℝ)) + √h * x ^ (-(1 / 2 : ℝ))) ∧
      |cardinalH_untuned p h (-x) - π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) *
        ((fracZp p (h * x)).re * Real.cos (cohnTheta x) + (fracZp p (h * x)).im * Real.sin (cohnTheta x))| ≤ C * x ^ (-(5 / 4 : ℝ)) ∧
      |(ceG1Deriv airyDerivFirstZero (-x) - ceF1 (-x)) - π⁻¹ * x ^ (-(3 / 2 : ℝ))| ≤ C * x ^ (-(5 / 2 : ℝ)) := by
  have hp01 : p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], hp.2⟩
  obtain ⟨C_R, hC_R, hRes⟩ := cardinalResolventH_far_asymptotic; obtain ⟨C_XY, hC_XY, hXY⟩ := cardinalXY_far_asymptotic
  obtain ⟨C_eta, hC_eta, h_eta⟩ := cardinalEtaHat_sqrt_bound hp le_rfl
  let C_B : ℝ := 4 / √π * C_XY + 2 * C_XY ^ 2; let C_all : ℝ := max (C_R + 2 * C_eta * C_XY) (max C_R C_B) + 1
  refine ⟨C_all, by positivity, fun {h x} hh hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hv_half : x / 2 ≤ x + airyZero 1 := by linarith [airyZero_one]
  have hv_pos : 0 < airyZero 1 - (-x) := by linarith
  have hRes_int : IntegrableOn (fun s : ℝ => cardinalResolventH s h (-x) * fracMuDensity p s) (Ioi (0 : ℝ)) := by
    have hcont : ContinuousOn (fun s : ℝ => cardinalResolventH s h (-x) * fracMuDensity p s) (Ioi (0 : ℝ)) :=
      ((continuousOn_cardinalResolventH h (-x) hh.1.le).mono Ioi_subset_Ici_self).mul (continuousOn_fracMuDensity hp01)
    refine ((fracMuDensity_integrable hp01).const_mul (C_R * x ^ (-(3 / 4 : ℝ)))).mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (fracMuDensity_pos hp01 hs)]; exact mul_le_mul_of_nonneg_right (hRes hs hh.1 hx).2 (fracMuDensity_pos hp01 hs).le
  let lead := fun s : ℝ => π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) *
    ((1 + s * (h * x))⁻¹ * Real.cos (cohnTheta x) + (√(s * (h * x)) / (1 + s * (h * x))) * Real.sin (cohnTheta x))
  have hint1 := integrableOn_inv_fracMu hp01 (mul_nonneg hh.1.le hx0.le); have hint2 := integrableOn_sqrt_mul_div_one_add hp01 (mul_nonneg hh.1.le hx0.le)
  have hlead_int : IntegrableOn (fun s : ℝ => lead s * fracMuDensity p s) (Ioi (0 : ℝ)) :=
    (((hint1.const_mul (Real.cos (cohnTheta x))).add (hint2.const_mul (Real.sin (cohnTheta x)))).const_mul
      (π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)))).congr (ae_of_all _ fun _ => by dsimp [lead]; ring)
  have hlead_val : ∫ s in Ioi (0 : ℝ), lead s * fracMuDensity p s = π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) *
      ((fracZp p (h * x)).re * Real.cos (cohnTheta x) + (fracZp p (h * x)).im * Real.sin (cohnTheta x)) := by
    rw [show (fun s : ℝ => lead s * fracMuDensity p s) = fun s => (π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ))) *
        (Real.cos (cohnTheta x) * ((1 + s * (h * x))⁻¹ * fracMuDensity p s) +
          Real.sin (cohnTheta x) * ((√(s * (h * x)) / (1 + s * (h * x))) * fracMuDensity p s)) from funext fun _ => by dsimp [lead]; ring,
      integral_const_mul, integral_add (hint1.const_mul _) (hint2.const_mul _), integral_const_mul, integral_const_mul,
      fracMu_stieltjes_eq hp01 (mul_nonneg hh.1.le hx0.le), ← fracZp_re_eq hp01 (mul_nonneg hh.1.le hx0.le),
      ← fracZp_im_eq hp01 (mul_nonneg hh.1.le hx0.le)]; ring
  let M_lead : ℝ := π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) *
    ((fracZp p (h * x)).re * Real.cos (cohnTheta x) + (fracZp p (h * x)).im * Real.sin (cohnTheta x))
  have hunt_err : |cardinalH_untuned p h (-x) - M_lead| ≤ C_R * x ^ (-(5 / 4 : ℝ)) := by
    rw [cardinalH_untuned_eq_integral hp hh.1 (-x), show M_lead = ∫ s in Ioi (0 : ℝ), lead s * fracMuDensity p s from hlead_val.symm,
      ← integral_sub hRes_int hlead_int, ← Real.norm_eq_abs]
    calc _ ≤ ∫ s in Ioi (0 : ℝ), ‖cardinalResolventH s h (-x) * fracMuDensity p s - lead s * fracMuDensity p s‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ s in Ioi (0 : ℝ), (C_R * x ^ (-(5 / 4 : ℝ))) * fracMuDensity p s := by
          refine setIntegral_mono_on (hRes_int.sub hlead_int).norm ((fracMuDensity_integrable hp01).const_mul _) measurableSet_Ioi fun s (hs : 0 < s) => ?_
          rw [Real.norm_eq_abs, ← sub_mul, abs_mul, abs_of_pos (fracMuDensity_pos hp01 hs)]
          exact mul_le_mul_of_nonneg_right (by simpa [lead, mul_assoc] using (hRes hs hh.1 hx).1) (fracMuDensity_pos hp01 hs).le
      _ = C_R * x ^ (-(5 / 4 : ℝ)) := by rw [integral_const_mul, fracMuDensity_integral_one hp01, mul_one]
  have hL0_bd : |cardinalEtaHat p h 1 * cohnL 0 (-x)| ≤ (2 * C_eta * C_XY) * √h * x ^ (-(5 / 4 : ℝ)) := by
    have heta_nn : 0 ≤ cardinalEtaHat p h 1 := (cardinalEtaHat_bounds hp01.1 hh.1.le zero_le_one le_rfl).2.1
    rw [cohnL_of_ne (sub_pos.mp hv_pos).ne, abs_mul, abs_div, abs_of_nonneg heta_nn, show -x - airyZero 1 = -(airyZero 1 - (-x)) by ring, abs_neg, abs_of_pos hv_pos]
    calc _ ≤ (C_eta * √h) * (C_XY * x ^ (-(1 / 4 : ℝ)) / (x / 2)) := mul_le_mul (h_eta hh zero_le_one le_rfl (by simp))
          (div_le_div₀ (by positivity) (hXY hx).2.2 (by positivity) (by linarith : x / 2 ≤ airyZero 1 - (-x))) (by positivity) (by positivity)
      _ = (2 * C_eta * C_XY) * √h * (x ^ (-(1 / 4 : ℝ)) * x ^ (-1 : ℝ)) := by rw [Real.rpow_neg_one]; ring
      _ = (2 * C_eta * C_XY) * √h * x ^ (-(5 / 4 : ℝ)) := by rw [rpow_add_eq hx0 (by norm_num : -(1 / 4 : ℝ) + -1 = -(5 / 4))]
  have hH_err : |cardinalH p h 1 (-x) - M_lead| ≤ C_all * x ^ (-(3 / 4 : ℝ)) * (x ^ (-(1 / 2 : ℝ)) + √h * x ^ (-(1 / 2 : ℝ))) := by
    have hpow : x ^ (-(3 / 4 : ℝ)) * x ^ (-(1 / 2 : ℝ)) = x ^ (-(5 / 4 : ℝ)) := rpow_add_eq hx0 (by norm_num)
    have h1 : C_R ≤ C_all := by dsimp [C_all]; linarith [le_max_left (C_R + 2 * C_eta * C_XY) (max C_R C_B), (by positivity : 0 ≤ 2 * C_eta * C_XY)]
    have h2 : 2 * C_eta * C_XY ≤ C_all := by dsimp [C_all]; linarith [le_max_left (C_R + 2 * C_eta * C_XY) (max C_R C_B)]
    calc |cardinalH p h 1 (-x) - M_lead|
        = |(cardinalH_untuned p h (-x) - M_lead) - cardinalEtaHat p h 1 * cohnL 0 (-x)| := by rw [(cardinalH_eq_untuned_sub hp01.1 hh.1.le zero_le_one le_rfl).1 (-x), one_mul]; ring_nf
      _ ≤ |cardinalH_untuned p h (-x) - M_lead| + |cardinalEtaHat p h 1 * cohnL 0 (-x)| := abs_sub _ _
      _ ≤ C_R * x ^ (-(5 / 4 : ℝ)) + (2 * C_eta * C_XY) * √h * x ^ (-(5 / 4 : ℝ)) := add_le_add hunt_err hL0_bd
      _ ≤ C_all * x ^ (-(5 / 4 : ℝ)) + C_all * √h * x ^ (-(5 / 4 : ℝ)) := add_le_add (mul_le_mul_of_nonneg_right h1 (by positivity))
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg h)) (by positivity))
      _ = C_all * x ^ (-(3 / 4 : ℝ)) * (x ^ (-(1 / 2 : ℝ)) + √h * x ^ (-(1 / 2 : ℝ))) := by rw [← hpow]; ring
  have hB_err : |(ceG1Deriv airyDerivFirstZero (-x) - ceF1 (-x)) - π⁻¹ * x ^ (-(3 / 2 : ℝ))| ≤ C_B * x ^ (-(5 / 2 : ℝ)) := by
    obtain ⟨hX_err, hY_err, _⟩ := hXY hx
    let LX := π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) * Real.cos (cohnTheta x); let LY := π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) * Real.sin (cohnTheta x)
    have hLsq : LX ^ 2 + LY ^ 2 = π⁻¹ * x ^ (-(3 / 2 : ℝ)) := by
      have hx32 : (x ^ (-(3 / 4 : ℝ))) ^ 2 = x ^ (-(3 / 2 : ℝ)) := by rw [rpow_sq_eq hx0.le]; norm_num
      dsimp [LX, LY]; rw [show (π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) * Real.cos (cohnTheta x)) ^ 2 +
        (π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) * Real.sin (cohnTheta x)) ^ 2 = (π ^ (-(1 / 2 : ℝ))) ^ 2 * (x ^ (-(3 / 4 : ℝ))) ^ 2 *
        (Real.cos (cohnTheta x) ^ 2 + Real.sin (cohnTheta x) ^ 2) by ring, Real.cos_sq_add_sin_sq, mul_one, pi_rpow_neg_half_sq, hx32]
    have htrig_bd : ∀ y : ℝ, |y| ≤ 1 → |π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) * y| ≤ (1 / √π) * x ^ (-(3 / 4 : ℝ)) := fun y hy => by
      rw [abs_mul, abs_mul, pi_rpow_neg_half, abs_of_pos (div_pos one_pos (Real.sqrt_pos.mpr Real.pi_pos)), abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
      exact mul_le_of_le_one_right (by positivity) hy
    rw [show (ceG1Deriv airyDerivFirstZero (-x) - ceF1 (-x)) - π⁻¹ * x ^ (-(3 / 2 : ℝ)) =
        (cardinalHstar airyDerivFirstZero (-x) ^ 2 - LX ^ 2) + ((airyAi (-x) / √(airyZero 1 - (-x))) ^ 2 - LY ^ 2) by
      rw [(o11p_B_eq_X_sq_add_Y_sq (sub_pos.mp hv_pos)).1, ← hLsq]; ring]
    exact (abs_add_le _ _).trans ((add_le_add (abs_sq_sub_sq_far_le hx1 hX_err (htrig_bd _ (Real.abs_cos_le_one _)))
      (abs_sq_sub_sq_far_le hx1 hY_err (htrig_bd _ (Real.abs_sin_le_one _)))).trans_eq (by dsimp [C_B]; ring))
  exact ⟨hH_err, hunt_err.trans (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans ((le_max_right _ _).trans (by dsimp [C_all]; linarith))) (by positivity)),
    hB_err.trans (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans ((le_max_right _ _).trans (by dsimp [C_all]; linarith))) (by positivity))⟩

private lemma continuousOn_fracZp {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) : ContinuousOn (fracZp p) (Ici (0 : ℝ)) := by
  refine continuousOn_of_dominated (s := Ici (0 : ℝ)) (bound := fracMuDensity p)
    (fun _ ht => (fracZp_integrable hp (mem_Ici.mp ht)).aestronglyMeasurable) (fun t ht => ?_) (fracMuDensity_integrable hp) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
    have hnorm : 1 ≤ ‖1 - Complex.I * ((√(s * t) : ℝ) : ℂ)‖ := by rw [← sq_le_sq₀ zero_le_one (norm_nonneg _), one_pow, Complex.sq_norm, Complex.normSq_apply]; simp; exact mul_self_nonneg _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (fracMuDensity_pos hp hs).le, norm_inv]
    exact mul_le_of_le_one_left (fracMuDensity_pos hp hs).le (inv_le_one_of_one_le₀ hnorm)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
    exact ((continuousOn_const.sub (continuousOn_const.mul ((Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (continuous_const.mul continuous_id))).continuousOn))).inv₀
      fun t ht h0 => by have hsq := congrArg Complex.normSq h0; rw [Complex.normSq_apply, Complex.normSq_zero] at hsq; simp at hsq; linarith [mul_self_nonneg (√(s * t))]).mul continuousOn_const

/-- **Theorem O.11j (`(ceo:O11j.6)` & `(ceo:O11j.2)`), sharp far-half-line margin & unconditional strict positivity. -/
theorem cardinalQ_far_margin_pos {p t₀ : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (ht₀ : 0 < t₀) :
    let S := sSup ((fun t => ‖fracZp p t‖ ^ 2) '' Ici t₀)
    S < 1 ∧
    (∀ ε' > 0, ∃ h₀ > 0, ∀ {h t : ℝ}, h ∈ Ioo 0 h₀ → t₀ ≤ t →
      (1 - S) - ε' ≤ π * (t / h) ^ (3 / 2 : ℝ) * cardinalQ p h 1 (-(t / h))) ∧
    (∃ h₀ > 0, ∀ {h x : ℝ}, h ∈ Ioo 0 h₀ → t₀ / h ≤ x → 0 < cardinalQ p h 1 (-x)) := by
  have hp01 : p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], hp.2⟩
  let S := sSup ((fun t => ‖fracZp p t‖ ^ 2) '' Ici t₀)
  have h_tend : Tendsto (fun t => ‖fracZp p t‖ ^ 2) atTop (𝓝 0) := by simpa [zero_pow two_ne_zero] using ((fracZp_tendsto_zero hp01).norm).pow 2
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp (h_tend (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  obtain ⟨t_m, ht_m_mem, ht_m_max⟩ := isCompact_Icc.exists_isMaxOn (f := fun t => ‖fracZp p t‖ ^ 2)
    ⟨t₀, ⟨le_rfl, le_max_right T₀ t₀⟩⟩ (((continuousOn_fracZp hp01).norm.pow 2).mono fun _ (ht : _ ∈ Icc t₀ (max T₀ t₀)) => le_trans ht₀.le ht.1)
  have hM₀_lt : ‖fracZp p t_m‖ ^ 2 < 1 := by have := fracZp_norm_lt_one hp01 (lt_of_lt_of_le ht₀ ht_m_mem.1); nlinarith [norm_nonneg (fracZp p t_m)]
  have hS_lt : S < 1 := (csSup_le (Set.Nonempty.image _ ⟨t₀, self_mem_Ici⟩) <| by
    rintro _ ⟨t, ht, rfl⟩
    exact (le_or_gt t (max T₀ t₀)).elim (fun h1 => (ht_m_max ⟨ht, h1⟩).trans (le_max_left _ _))
      fun h1 => (le_of_lt (hT₀ t (le_trans (le_max_left _ _) h1.le))).trans (le_max_right _ _)).trans_lt (max_lt hM₀_lt (by norm_num))
  have hS_ge : ∀ t ≥ t₀, ‖fracZp p t‖ ^ 2 ≤ S := fun t ht =>
    le_csSup ⟨1, by rintro _ ⟨s, hs, rfl⟩; have := fracZp_norm_lt_one hp01 (lt_of_lt_of_le ht₀ hs); nlinarith [norm_nonneg (fracZp p s)]⟩ ⟨t, ht, rfl⟩
  obtain ⟨C, hC, hfar⟩ := cardinalH_far_asymptotic hp
  have hmargin : ∀ ε' > 0, ∃ h₀ > 0, ∀ {h t : ℝ}, h ∈ Ioo 0 h₀ → t₀ ≤ t →
      (1 - S) - ε' ≤ π * (t / h) ^ (3 / 2 : ℝ) * cardinalQ p h 1 (-(t / h)) := fun ε' hε' => by
    let D : ℝ := π * C / t₀ + 4 * √π * C / √t₀ + 4 * π * C ^ 2 / t₀ + 1
    refine ⟨min (t₀ / 10) (min 1 ((ε' / D) ^ 2)), lt_min (by positivity) (lt_min one_pos (by positivity)), fun {h t} hh ht => ?_⟩
    have hh1 : h ∈ Ioc (0 : ℝ) 1 := ⟨hh.1, hh.2.le.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
    have hx10 : 10 ≤ t / h := (le_div_iff₀ hh.1).mpr (by nlinarith [hh.2.le.trans (min_le_left _ _)])
    let x := t / h; have hx0 : 0 < x := by linarith
    obtain ⟨hH_err, _, hB_err⟩ := hfar hh1 hx10; rw [mul_div_cancel₀ t hh.1.ne'] at hH_err
    have hE_bd : |cardinalH p h 1 (-x) - π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) *
        ((fracZp p t).re * Real.cos (cohnTheta x) + (fracZp p t).im * Real.sin (cohnTheta x))| ≤ 2 * C * x ^ (-(5 / 4 : ℝ)) :=
      (hH_err.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_right (Real.sqrt_le_one.mpr hh1.2) (by positivity))) (by positivity))).trans_eq
        (by rw [← rpow_add_eq hx0 (by norm_num : -(3 / 4 : ℝ) + -(1 / 2) = -(5 / 4))]; ring)
    have hlead_norm : |(fracZp p t).re * Real.cos (cohnTheta x) + (fracZp p t).im * Real.sin (cohnTheta x)| ≤ ‖fracZp p t‖ := by
      have hsq : ((fracZp p t).re * Real.cos (cohnTheta x) + (fracZp p t).im * Real.sin (cohnTheta x)) ^ 2 ≤
          ((fracZp p t).re ^ 2 + (fracZp p t).im ^ 2) * (Real.cos (cohnTheta x) ^ 2 + Real.sin (cohnTheta x) ^ 2) := by
        nlinarith only [sq_nonneg ((fracZp p t).re * Real.sin (cohnTheta x) - (fracZp p t).im * Real.cos (cohnTheta x))]
      rw [Real.cos_sq_add_sin_sq, mul_one, show (fracZp p t).re ^ 2 + (fracZp p t).im ^ 2 = ‖fracZp p t‖ ^ 2 by rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sq, sq]] at hsq
      exact abs_le.mpr (abs_le_of_sq_le_sq' hsq (norm_nonneg _))
    have hP_bd : π * x ^ (3 / 2 : ℝ) * cardinalP p h 1 (-x) ≤ S + 4 * √π * C * x ^ (-(1 / 2 : ℝ)) + 4 * π * C ^ 2 * x⁻¹ := by
      have hZ_lt : ‖fracZp p t‖ ≤ 1 := (fracZp_norm_lt_one hp01 (lt_of_lt_of_le ht₀ ht)).le
      have hH_abs : |cardinalH p h 1 (-x)| ≤ π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) * ‖fracZp p t‖ + 2 * C * x ^ (-(5 / 4 : ℝ)) := by
        have htri := abs_sub_abs_le_abs_sub (cardinalH p h 1 (-x)) (π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) * ((fracZp p t).re * Real.cos (cohnTheta x) + (fracZp p t).im * Real.sin (cohnTheta x)))
        have habs : |π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) * ((fracZp p t).re * Real.cos (cohnTheta x) + (fracZp p t).im * Real.sin (cohnTheta x))| ≤ π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) * ‖fracZp p t‖ := by
          rw [abs_mul, abs_of_pos (mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.rpow_pos_of_pos hx0 _))]; exact mul_le_mul_of_nonneg_left hlead_norm (by positivity)
        linarith
      have hH_sq : cardinalH p h 1 (-x) ^ 2 ≤ π⁻¹ * x ^ (-(3 / 2 : ℝ)) * ‖fracZp p t‖ ^ 2 + 4 * π ^ (-(1 / 2 : ℝ)) * C * x ^ (-2 : ℝ) + 4 * C ^ 2 * x ^ (-(5 / 2 : ℝ)) := by
        have hmulZ := mul_le_mul_of_nonneg_left hZ_lt (by positivity : 0 ≤ 4 * π ^ (-(1 / 2 : ℝ)) * C * x ^ (-2 : ℝ))
        exact ((sq_abs _).symm.trans_le (pow_le_pow_left₀ (abs_nonneg _) hH_abs 2)).trans (by
          rw [show (π ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) * ‖fracZp p t‖ + 2 * C * x ^ (-(5 / 4 : ℝ))) ^ 2 =
            (π ^ (-(1 / 2 : ℝ))) ^ 2 * (x ^ (-(3 / 4 : ℝ))) ^ 2 * ‖fracZp p t‖ ^ 2 +
              4 * π ^ (-(1 / 2 : ℝ)) * C * (x ^ (-(3 / 4 : ℝ)) * x ^ (-(5 / 4 : ℝ))) * ‖fracZp p t‖ + 4 * C ^ 2 * (x ^ (-(5 / 4 : ℝ))) ^ 2 by ring,
            pi_rpow_neg_half_sq, (by rw [rpow_sq_eq hx0.le]; norm_num : (x ^ (-(3 / 4 : ℝ))) ^ 2 = x ^ (-(3 / 2 : ℝ))),
            rpow_add_eq hx0 (by norm_num : -(3 / 4 : ℝ) + -(5 / 4) = -2), (by rw [rpow_sq_eq hx0.le]; norm_num : (x ^ (-(5 / 4 : ℝ))) ^ 2 = x ^ (-(5 / 2 : ℝ)))]; linarith)
      have hscale1 : π * x ^ (3 / 2 : ℝ) * (π ^ (-(1 / 2 : ℝ)) * x ^ (-2 : ℝ)) = √π * x ^ (-(1 / 2 : ℝ)) := by
        rw [show π * x ^ (3 / 2 : ℝ) * (π ^ (-(1 / 2 : ℝ)) * x ^ (-2 : ℝ)) = (π ^ (1 : ℝ) * π ^ (-(1 / 2 : ℝ))) * (x ^ (3 / 2 : ℝ) * x ^ (-2 : ℝ)) by rw [Real.rpow_one]; ring,
          rpow_add_eq Real.pi_pos (by norm_num : (1 : ℝ) + -(1 / 2 : ℝ) = 1 / 2), ← Real.sqrt_eq_rpow π, rpow_add_eq hx0 (by norm_num : (3 / 2 : ℝ) + -2 = -(1 / 2))]
      have hscale2 : π * x ^ (3 / 2 : ℝ) * x ^ (-(5 / 2 : ℝ)) = π * x⁻¹ := by
        rw [mul_assoc, rpow_add_eq hx0 (by norm_num : (3 / 2 : ℝ) + -(5 / 2 : ℝ) = -1), Real.rpow_neg_one]
      have hP_le : π * x ^ (3 / 2 : ℝ) * cardinalP p h 1 (-x) ≤ ‖fracZp p t‖ ^ 2 + 4 * √π * C * x ^ (-(1 / 2 : ℝ)) + 4 * π * C ^ 2 * x⁻¹ :=
        (mul_le_mul_of_nonneg_left (show cardinalP p h 1 (-x) ≤ _ from hH_sq) (by positivity)).trans_eq
          (by rw [show π * x ^ (3 / 2 : ℝ) * (π⁻¹ * x ^ (-(3 / 2 : ℝ)) * ‖fracZp p t‖ ^ 2 + 4 * π ^ (-(1 / 2 : ℝ)) * C * x ^ (-2 : ℝ) + 4 * C ^ 2 * x ^ (-(5 / 2 : ℝ))) =
            (π * x ^ (3 / 2 : ℝ) * (π⁻¹ * x ^ (-(3 / 2 : ℝ)))) * ‖fracZp p t‖ ^ 2 + 4 * C * (π * x ^ (3 / 2 : ℝ) * (π ^ (-(1 / 2 : ℝ)) * x ^ (-2 : ℝ))) +
            4 * C ^ 2 * (π * x ^ (3 / 2 : ℝ) * x ^ (-(5 / 2 : ℝ))) by ring, pi_x32_inv hx0, hscale1, hscale2]; ring)
      linarith [hS_ge t ht]
    have hB_lb : 1 - π * C * x⁻¹ ≤ π * x ^ (3 / 2 : ℝ) * (ceG1Deriv airyDerivFirstZero (-x) - ceF1 (-x)) :=
      (mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp hB_err).1] : π⁻¹ * x ^ (-(3 / 2 : ℝ)) - C * x ^ (-(5 / 2 : ℝ)) ≤ _) (by positivity)).trans_eq'
        (by rw [mul_sub, pi_x32_inv hx0, show π * x ^ (3 / 2 : ℝ) * (C * x ^ (-(5 / 2 : ℝ))) = π * C * (x ^ (3 / 2 : ℝ) * x ^ (-(5 / 2 : ℝ))) by ring,
          rpow_add_eq hx0 (by norm_num : (3 / 2 : ℝ) + -(5 / 2 : ℝ) = -1), Real.rpow_neg_one])
    have hxinv_le : x⁻¹ ≤ √h * (1 / t₀) :=
      (by dsimp [x]; rw [inv_div]; exact div_le_div_of_nonneg_left hh.1.le ht₀ ht : x⁻¹ ≤ h / t₀).trans
        (by rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_right ((Real.mul_self_sqrt hh.1.le).symm.trans_le
          ((mul_le_mul_of_nonneg_right (Real.sqrt_le_one.mpr hh1.2) (Real.sqrt_nonneg h)).trans_eq (one_mul _))) (by positivity))
    have hxhalf_le : x ^ (-(1 / 2 : ℝ)) ≤ √h * (1 / √t₀) := by
      rw [Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow]
      exact (inv_anti₀ (Real.sqrt_pos.mpr (div_pos ht₀ hh.1)) (Real.sqrt_le_sqrt ((div_le_iff₀ hh.1).mpr (by dsimp [x]; rw [div_mul_cancel₀ _ hh.1.ne']; exact ht)))).trans_eq
        (by rw [Real.sqrt_div ht₀.le]; field_simp [(Real.sqrt_pos.mpr hh.1).ne', (Real.sqrt_pos.mpr ht₀).ne'])
    have hsqh_bd : D * √h ≤ ε' := (le_div_iff₀' (by positivity : 0 < D)).mp
      ((Real.sqrt_le_sqrt (hh.2.le.trans ((min_le_right _ _).trans (min_le_right _ _)))).trans_eq (Real.sqrt_sq (by positivity)))
    dsimp [D] at hsqh_bd
    have hloss : π * C * x⁻¹ + 4 * √π * C * x ^ (-(1 / 2 : ℝ)) + 4 * π * C ^ 2 * x⁻¹ ≤ ε' :=
      ((add_le_add (add_le_add (mul_le_mul_of_nonneg_left hxinv_le (by positivity)) (mul_le_mul_of_nonneg_left hxhalf_le (by positivity)))
        (mul_le_mul_of_nonneg_left hxinv_le (by positivity))).trans_eq (by ring)).trans
        ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (Real.sqrt_nonneg h)).trans hsqh_bd)
    rw [show cardinalQ p h 1 (-x) = (ceG1Deriv airyDerivFirstZero (-x) - ceF1 (-x)) - cardinalP p h 1 (-x) by unfold cardinalQ; ring, mul_sub]; linarith
  obtain ⟨h₀, hh₀, hmar⟩ := hmargin ((1 - S) / 2) (by linarith)
  refine ⟨hS_lt, hmargin, h₀, hh₀, fun {h x} hh hx => ?_⟩
  have hQ_pos := hmar hh ((div_le_iff₀' hh.1).mp hx); rw [mul_div_cancel_left₀ x hh.1.ne'] at hQ_pos
  have hx0 : 0 < x := lt_of_lt_of_le (div_pos ht₀ hh.1) hx
  exact (mul_pos_iff_of_pos_left (by positivity : 0 < π * x ^ (3 / 2 : ℝ))).mp (by linarith : 0 < π * x ^ (3 / 2 : ℝ) * cardinalQ p h 1 (-x))

/-- info: 'FormalResearch.CohnElkies.cardinalResolventH_eq_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardinalResolventH_eq_closed
/-- info: 'FormalResearch.CohnElkies.cardinalResolventH_eq_XY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardinalResolventH_eq_XY
/-- info: 'FormalResearch.CohnElkies.cardinalJ_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardinalJ_asymptotic
/-- info: 'FormalResearch.CohnElkies.cardinalH_untuned_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardinalH_untuned_eq_integral
/-- info: 'FormalResearch.CohnElkies.o11p_B_eq_X_sq_add_Y_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms o11p_B_eq_X_sq_add_Y_sq
/-- info: 'FormalResearch.CohnElkies.cardinalQ_near_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardinalQ_near_node
/-- info: 'FormalResearch.CohnElkies.cardinalH_decomp_XY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardinalH_decomp_XY
/-- info: 'FormalResearch.CohnElkies.cardinalQ_uniform_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardinalQ_uniform_lower
/-- info: 'FormalResearch.CohnElkies.cardinalQ_intermediate_region' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardinalQ_intermediate_region
/-- info: 'FormalResearch.CohnElkies.cardinalQ_far_region' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardinalQ_far_region
/-- info: 'FormalResearch.CohnElkies.lemma_O11p' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_O11p
/-- info: 'FormalResearch.CohnElkies.cardinalResolventH_far_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardinalResolventH_far_asymptotic
/-- info: 'FormalResearch.CohnElkies.cardinalH_far_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardinalH_far_asymptotic
/-- info: 'FormalResearch.CohnElkies.cardinalQ_far_margin_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardinalQ_far_margin_pos

end FormalResearch.CohnElkies
