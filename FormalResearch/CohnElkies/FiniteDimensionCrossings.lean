module

public import FormalResearch.CohnElkies.FiniteGaussianBase

/-!
# Finite-Dimensional Gaussian Crossings (`ce_finite_bounds.tex` Theorems E.2, E.2')

Source: `CFT/sign_uncertainty/paper/ce_finite_bounds.tex` (PR 240, commit `c3d8c90fe`).

Stirling–Robbins factorial bounds, dyadic log enclosure, quadratic Gaussian dimension crossings
(`d ≥ 104, 469, 9544`), and cubic Laguerre Gaussian bounds (`d ≥ 24, 48, 95, 106`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform Polynomial RealInnerProductSpace SchwartzMap Matrix

namespace FormalResearch.CohnElkies

/-! ### Section 3: Stirling–Robbins Bounds & Dyadic Logarithm Enclosure -/

lemma log_stirlingSeq_sub_half_log_pi_bounds {n : ℕ} (hn : 1 ≤ n) :
    (1 : ℝ) / (12 * n) - 1 / (144 * (n : ℝ) ^ 3) ≤
      Real.log (Stirling.stirlingSeq n) - Real.log √π ∧
    Real.log (Stirling.stirlingSeq n) - Real.log √π ≤ 1 / (12 * n) := by
  have htend_sub : Tendsto (fun N : ℕ =>
      Real.log (Stirling.stirlingSeq n) - Real.log (Stirling.stirlingSeq (n + N)))
      atTop (𝓝 (Real.log (Stirling.stirlingSeq n) - Real.log √π)) :=
    tendsto_const_nhds.sub ((Real.continuousAt_log (Real.sqrt_ne_zero'.mpr Real.pi_pos)).tendsto.comp
      (by simpa [Function.comp_def, Nat.add_comm] using
        Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat n)))
  have hup_N : ∀ N : ℕ, Real.log (Stirling.stirlingSeq n) -
      Real.log (Stirling.stirlingSeq (n + N)) ≤ 1 / (12 * n) := fun N => by
    let f : ℕ → ℝ := fun k => Real.log (Stirling.stirlingSeq (n + k))
    let g : ℕ → ℝ := fun k => 1 / (12 * ((n + k : ℕ) : ℝ))
    have hsum := Finset.sum_le_sum (s := Finset.range N) (f := fun k => f k - f (k + 1))
      (g := fun k => g k - g (k + 1)) fun k _ => by
        have hnk : (1 : ℝ) ≤ (n + k : ℕ) := by exact_mod_cast (by omega : 1 ≤ n + k)
        have hg_eq : g k - g (k + 1) = 1 / (12 * ((n + k : ℕ) : ℝ) * (((n + k : ℕ) : ℝ) + 1)) := by
          dsimp [g]; push_cast; field_simp; ring
        rw [hg_eq]; simpa [f, add_assoc] using Stirling.log_stirlingSeq_sdiff_le (n + k)
    rw [Finset.sum_range_sub' f N, Finset.sum_range_sub' g N] at hsum
    dsimp only [f, g] at hsum; push_cast at hsum; simp only [add_zero] at hsum
    linarith [show (0 : ℝ) ≤ 1 / (12 * ((n : ℝ) + N)) by positivity]
  have hlo_N : ∀ N : ℕ, (1 : ℝ) / (12 * n) - 1 / (12 * ((n : ℝ) + N)) -
      (1 / (144 * (n : ℝ) ^ 3) - 1 / (144 * ((n : ℝ) + N) ^ 3)) ≤
      Real.log (Stirling.stirlingSeq n) - Real.log (Stirling.stirlingSeq (n + N)) := fun N => by
    let f : ℕ → ℝ := fun k => Real.log (Stirling.stirlingSeq (n + k))
    let g : ℕ → ℝ := fun k => 1 / (12 * ((n + k : ℕ) : ℝ)) - 1 / (144 * ((n + k : ℕ) : ℝ) ^ 3)
    have hsum := Finset.sum_le_sum (s := Finset.range N) (f := fun k => g k - g (k + 1))
      (g := fun k => f k - f (k + 1)) fun k _ => by
        have hm : n + k = (n + k - 1) + 1 := by omega
        let tfun : ℕ → ℝ := fun j => (1 : ℝ) / (2 * (j + 1 : ℕ) + 1) *
          ((1 / (2 * ((n + k - 1) + 1 : ℕ) + 1)) ^ 2) ^ (j + 1)
        have h0 : tfun 0 ≤ Real.log (Stirling.stirlingSeq ((n + k - 1) + 1)) -
            Real.log (Stirling.stirlingSeq ((n + k - 1) + 2)) :=
          hasSum_le (fun j => by
              by_cases hj : j = 0
              · dsimp only [tfun]; subst hj; exact le_rfl
              · simp only [hj, ↓reduceIte]; positivity)
            (hasSum_ite_eq 0 (tfun 0)) (Stirling.log_stirlingSeq_sdiff_hasSum (n + k - 1))
        rw [← hm, show (n + k - 1) + 2 = n + (k + 1) by omega] at h0
        have hu : (1 : ℝ) ≤ (n + k : ℕ) := by exact_mod_cast (by omega : 1 ≤ n + k)
        set u : ℝ := ((n + k : ℕ) : ℝ)
        have h0' : 1 / (3 * (2 * u + 1) ^ 2) ≤ f k - f (k + 1) := by
          convert h0 using 2
          dsimp only [tfun, u]; rw [← hm]; norm_num; ring
        have hrat : g k - g (k + 1) ≤ 1 / (3 * (2 * u + 1) ^ 2) := by
          have hu1 : (n + (k + 1) : ℕ) = (n + k : ℕ) + 1 := by omega
          have huc : (n : ℝ) + k = u := by dsimp [u]; push_cast; ring
          dsimp [g]; rw [hu1]; push_cast; rw [huc]
          rw [show 1 / (12 * u) - 1 / (144 * u ^ 3) - (1 / (12 * (u + 1)) - 1 / (144 * (u + 1) ^ 3)) =
              (1 / (12 * u) - 1 / (12 * (u + 1))) - (1 / (144 * u ^ 3) - 1 / (144 * (u + 1) ^ 3)) by ring,
            show 1 / (12 * u) - 1 / (12 * (u + 1)) = 1 / (12 * u * (u + 1)) by field_simp; ring,
            sub_le_iff_le_add, ← sub_le_iff_le_add',
            show 1 / (12 * u * (u + 1)) - 1 / (3 * (2 * u + 1) ^ 2) =
              1 / (12 * u * (u + 1) * (2 * u + 1) ^ 2) by field_simp; ring,
            show 1 / (144 * u ^ 3) - 1 / (144 * (u + 1) ^ 3) =
              (3 * u ^ 2 + 3 * u + 1) / (144 * u ^ 3 * (u + 1) ^ 3) by field_simp; ring,
            div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [sq_nonneg u]
        exact hrat.trans h0'
    rw [Finset.sum_range_sub' g N, Finset.sum_range_sub' f N] at hsum
    dsimp only [f, g] at hsum; push_cast at hsum; simp only [add_zero] at hsum
    linarith
  have htend_lo : Tendsto (fun N : ℕ =>
      (1 : ℝ) / (12 * n) - 1 / (12 * ((n : ℝ) + N)) -
        (1 / (144 * (n : ℝ) ^ 3) - 1 / (144 * ((n : ℝ) + N) ^ 3)))
      atTop (𝓝 ((1 : ℝ) / (12 * n) - 1 / (144 * (n : ℝ) ^ 3))) := by
    have hadd : Tendsto (fun N : ℕ => (n : ℝ) + (N : ℝ)) atTop atTop := by
      simpa only [Function.comp_def, Nat.add_comm, Nat.cast_add] using
        tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat n)
    have h1 := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop
      (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 12) hadd)
    have h2 := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop
      (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 144)
        ((tendsto_pow_atTop (by norm_num : 3 ≠ 0)).comp hadd))
    simpa using ((tendsto_const_nhds.sub h1).sub (tendsto_const_nhds.sub h2))
  exact ⟨le_of_tendsto_of_tendsto htend_lo htend_sub (Eventually.of_forall hlo_N),
    le_of_tendsto htend_sub (Eventually.of_forall hup_N)⟩

lemma gamma_nat_add_half {m : ℕ} :
    Real.Gamma ((m : ℝ) + 1 / 2) =
      ((2 * m).factorial : ℝ) * √π / ((4 : ℝ) ^ m * (m.factorial : ℝ)) := by
  induction m with
  | zero => norm_num [Real.Gamma_one_half_eq]
  | succ m ih =>
    rw [show ((m + 1 : ℕ) : ℝ) + 1 / 2 = ((m : ℝ) + 1 / 2) + 1 by push_cast; ring,
      Real.Gamma_add_one (by positivity), ih, show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
      Nat.factorial_succ (2 * m + 1), Nat.factorial_succ (2 * m), Nat.factorial_succ m, pow_succ]
    push_cast; field_simp; ring

lemma log_factorial_stirling_bounds {n : ℕ} (hn : 1 ≤ n) :
    (1 / 2 : ℝ) * Real.log (2 * π) + ((n : ℝ) + 1 / 2) * Real.log n - n + 1 / (12 * n) -
        1 / (144 * (n : ℝ) ^ 3) ≤ Real.log (n.factorial : ℝ) ∧
      Real.log (n.factorial : ℝ) ≤
        (1 / 2 : ℝ) * Real.log (2 * π) + ((n : ℝ) + 1 / 2) * Real.log n - n + 1 / (12 * n) := by
  have hb := log_stirlingSeq_sub_half_log_pi_bounds hn
  have hlog : Real.log (Stirling.stirlingSeq n) - Real.log √π =
      Real.log (n.factorial : ℝ) -
        ((1 / 2 : ℝ) * Real.log (2 * π) + ((n : ℝ) + 1 / 2) * Real.log n - n) := by
    rw [Stirling.log_stirlingSeq_formula n, Real.log_sqrt Real.pi_pos.le,
      Real.log_mul two_ne_zero (by positivity),
      Real.log_mul two_ne_zero Real.pi_ne_zero,
      Real.log_div (by positivity) (Real.exp_pos _).ne', Real.log_exp]
    ring
  rw [hlog] at hb; constructor <;> linarith

lemma log_gamma_half_odd_bounds {m : ℕ} (hm : 1 ≤ m) :
    (1 / 2 : ℝ) * Real.log (2 * π) + m * Real.log m - m - 1 / (24 * m) - 1 / (144 * (m : ℝ) ^ 3) ≤
        Real.log (Real.Gamma ((m : ℝ) + 1 / 2)) ∧
      Real.log (Real.Gamma ((m : ℝ) + 1 / 2)) ≤
        (1 / 2 : ℝ) * Real.log (2 * π) + m * Real.log m - m - 1 / (24 * m) +
          1 / (144 * (m : ℝ) ^ 3) := by
  have hlogG : Real.log (Real.Gamma ((m : ℝ) + 1 / 2)) =
      Real.log ((2 * m).factorial : ℝ) + Real.log π / 2 - (2 * m * Real.log 2 + Real.log (m.factorial : ℝ)) := by
    rw [gamma_nat_add_half, Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (Real.sqrt_pos.mpr Real.pi_pos).ne',
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_sqrt Real.pi_pos.le,
      Real.log_four_eq]
    ring
  rw [hlogG, Real.log_mul two_ne_zero Real.pi_ne_zero]
  have h2m := log_factorial_stirling_bounds (n := 2 * m) (by omega)
  have hm' := log_factorial_stirling_bounds (n := m) hm
  have hlog2m : Real.log ((2 * m : ℕ) : ℝ) = Real.log 2 + Real.log m := by
    push_cast; exact Real.log_mul two_ne_zero (by positivity)
  rw [hlog2m] at h2m
  rw [Real.log_mul two_ne_zero Real.pi_ne_zero] at h2m hm'
  rw [show ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) by push_cast; ring,
    show (1 : ℝ) / (12 * (2 * (m : ℝ))) = 1 / (24 * m) by ring] at h2m
  have hinv3 : (0 : ℝ) ≤ (m : ℝ)⁻¹ ^ 3 := by positivity
  set F2 : ℝ := Real.log ((2 * m).factorial : ℝ)
  set F1 : ℝ := Real.log (m.factorial : ℝ)
  ring_nf at h2m hm' ⊢
  constructor <;> linarith [h2m.1, h2m.2, hm'.1, hm'.2, hinv3]

lemma log_dyadic_approx {r : ℝ} (k : ℤ) (x : ℝ) (hx : |x| < 1)
    (hr : r = (2 : ℝ) ^ k * (1 - x)⁻¹) (N : ℕ) :
    |Real.log r - ((k : ℝ) * (287209 / 414355 : ℝ) +
      ∑ i ∈ Finset.range N, x ^ (i + 1) / (i + 1))| ≤
      |(k : ℝ)| * (1 / 10 ^ 10 : ℝ) + |x| ^ (N + 1) / (1 - |x|) := by
  have h1x : 0 < 1 - x := sub_pos.mpr (abs_lt.mp hx).2
  have hlog : Real.log r = k * Real.log 2 - Real.log (1 - x) := by
    rw [hr, Real.log_mul (by positivity) (inv_ne_zero h1x.ne'), Real.log_zpow, Real.log_inv]; ring
  rw [hlog, show (k : ℝ) * Real.log 2 - Real.log (1 - x) -
      ((k : ℝ) * (287209 / 414355) + ∑ i ∈ Finset.range N, x ^ (i + 1) / (i + 1)) =
      (k : ℝ) * (Real.log 2 - 287209 / 414355) -
        (∑ i ∈ Finset.range N, x ^ (i + 1) / (i + 1) + Real.log (1 - x)) by ring]
  have hk2 : |(k : ℝ) * (Real.log 2 - 287209 / 414355)| ≤ |(k : ℝ)| * (1 / 10 ^ 10 : ℝ) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left Real.log_two_near_10 (abs_nonneg _)
  linarith [abs_sub ((k : ℝ) * (Real.log 2 - 287209 / 414355))
    (∑ i ∈ Finset.range N, x ^ (i + 1) / (i + 1) + Real.log (1 - x)),
    Real.abs_log_sub_add_sum_range_le hx N]

lemma log_pi_bounds : (1.144729 : ℝ) < Real.log π ∧ Real.log π < 1.144731 := by
  have hlo := log_dyadic_approx (r := 3141592 / 1000000) 2 (-107301 / 392699)
    (by norm_num) (by norm_num) 14
  have hhi := log_dyadic_approx (r := 3141593 / 1000000) 2 (-858407 / 3141593)
    (by norm_num) (by norm_num) 14
  norm_num [Finset.sum_range_succ] at hlo hhi
  constructor <;> linarith [(abs_le.mp hlo).1, (abs_le.mp hhi).2,
    Real.log_lt_log (by norm_num) Real.pi_gt_d6, Real.log_lt_log Real.pi_pos Real.pi_lt_d6]

/-! ### Section 4: Theorem E.2 — Quadratic Gaussian Dimension Bounds (`thm:ce-quadratic-dimensions`) -/

theorem quadD_parity_step {d : ℕ} (hd : 2 ≤ d) :
    quadD (d + 2) / quadD d = (1 / 4 : ℝ) * (1 + 2 / ((d : ℝ) + 2)) ^ ((d : ℝ) / 2 + 2) := by
  unfold quadD
  have hc : (d : ℝ) / 2 + 1 ≠ 0 := by positivity
  have hG : Real.Gamma ((d : ℝ) / 2 + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  rw [show ((d + 2 : ℕ) : ℝ) / 2 + 1 = ((d : ℝ) / 2 + 1) + 1 by push_cast; ring,
    Real.Gamma_add_one hc]
  have hpow : ((((d + 2 : ℕ) : ℝ) + 2) / 8) ^ (((d + 2 : ℕ) : ℝ) / 2) =
      ((d : ℝ) + 4) / 8 * ((((d : ℝ) + 4) / ((d : ℝ) + 2)) ^ ((d : ℝ) / 2) *
        (((d : ℝ) + 2) / 8) ^ ((d : ℝ) / 2)) := by
    push_cast
    rw [show ((d : ℝ) + 2 + 2) / 8 = ((d : ℝ) + 4) / 8 by ring,
      show ((d : ℝ) + 2) / 2 = (d : ℝ) / 2 + 1 by ring, Real.rpow_add (by positivity),
      Real.rpow_one, ← Real.mul_rpow (by positivity) (by positivity)]
    rw [show ((d : ℝ) + 4) / ((d : ℝ) + 2) * (((d : ℝ) + 2) / 8) = ((d : ℝ) + 4) / 8 by
      field_simp]
    ring
  have hadd : (1 : ℝ) + 2 / ((d : ℝ) + 2) = ((d : ℝ) + 4) / ((d : ℝ) + 2) := by field_simp; ring
  rw [hpow, hadd, Real.rpow_add (by positivity), show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
  push_cast; field_simp [hG]; ring

noncomputable def quadB (d : ℕ) (κ : ℝ) : ℝ := Real.log ((2 : ℝ) ^ (κ * d) * quadD d)

lemma quadB_le_zero_iff {d : ℕ} (hd : 2 ≤ d) (κ : ℝ) :
    quadB d κ ≤ 0 ↔ quadD d ≤ (2 : ℝ) ^ (-κ * d) := by
  unfold quadB
  rw [Real.log_nonpos_iff (mul_pos (Real.rpow_pos_of_pos two_pos _) (quadD_pos hd)).le,
    mul_comm, ← le_div_iff₀ (Real.rpow_pos_of_pos two_pos _), one_div,
    ← Real.rpow_neg two_pos.le, neg_mul]

lemma quadB_pos_iff {d : ℕ} (hd : 2 ≤ d) (κ : ℝ) :
    0 < quadB d κ ↔ (2 : ℝ) ^ (-κ * d) < quadD d := by
  rw [← not_le, ← not_le, quadB_le_zero_iff hd]

theorem quadB_step_le {d : ℕ} (hd : 2 ≤ d) (κ : ℝ) :
    quadB (d + 2) κ - quadB d κ ≤ 1 + 2 / ((d : ℝ) + 2) - 2 * (1 - κ) * Real.log 2 := by
  unfold quadB
  rw [← Real.log_div (mul_pos (Real.rpow_pos_of_pos two_pos _) (quadD_pos (by omega))).ne'
    (mul_pos (Real.rpow_pos_of_pos two_pos _) (quadD_pos hd)).ne']
  have hratio : ((2 : ℝ) ^ (κ * ((d + 2 : ℕ) : ℝ)) * quadD (d + 2)) /
      ((2 : ℝ) ^ (κ * d) * quadD d) =
      (2 : ℝ) ^ (2 * κ - 2) * (1 + 2 / ((d : ℝ) + 2)) ^ ((d : ℝ) / 2 + 2) := by
    have hpow : (2 : ℝ) ^ (κ * ((d + 2 : ℕ) : ℝ)) / (2 : ℝ) ^ (κ * d) = (2 : ℝ) ^ (2 * κ) := by
      push_cast; rw [← Real.rpow_sub two_pos]; congr 1; ring
    rw [mul_div_mul_comm, hpow, quadD_parity_step hd, mul_left_comm, ← mul_assoc,
      show (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) by norm_num, ← Real.rpow_add two_pos]
    congr 1; ring_nf
  rw [hratio, Real.log_mul (Real.rpow_pos_of_pos two_pos _).ne'
    (Real.rpow_pos_of_pos (by positivity) _).ne', Real.log_rpow two_pos, Real.log_rpow (by positivity)]
  have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 2 / ((d : ℝ) + 2) by positivity)
  have hmul : ((d : ℝ) / 2 + 2) * Real.log (1 + 2 / ((d : ℝ) + 2)) ≤
      ((d : ℝ) / 2 + 2) * (2 / ((d : ℝ) + 2)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rw [show ((d : ℝ) / 2 + 2) * (2 / ((d : ℝ) + 2)) = 1 + 2 / ((d : ℝ) + 2) by field_simp; ring] at hmul
  linarith

lemma quadB_step_strictAnti (κ : ℝ) :
    StrictAnti (fun d : ℕ => quadB (d + 4) κ - quadB (d + 2) κ) := by
  let g : ℝ → ℝ := fun u => ((1 + u) * Real.log (1 + u)) / u
  have hg_mono : StrictMonoOn g (Ioi 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
    · exact ((continuousOn_const.add continuousOn_id).mul
        (ContinuousOn.comp Real.continuousOn_log (continuousOn_const.add continuousOn_id)
          fun u hu => ne_of_gt (by dsimp; linarith [Set.mem_Ioi.mp hu]))).div continuousOn_id
        fun u hu => (Set.mem_Ioi.mp hu).ne'
    · intro u hu
      rw [interior_Ioi] at hu
      have hu0 : 0 < u := hu; have h1u : 0 < 1 + u := by linarith
      have hl : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 + u)⁻¹ u :=
        ((Real.hasDerivAt_log h1u.ne').comp u ((hasDerivAt_id u).const_add 1)).congr_deriv (mul_one _)
      have hd1 : HasDerivAt (fun x : ℝ => (1 + x) * Real.log (1 + x)) (Real.log (1 + u) + 1) u := by
        refine (((hasDerivAt_id u).const_add 1).mul hl).congr_deriv ?_
        simp only [id_eq]; field_simp [h1u.ne']
      have hg' : HasDerivAt g ((u - Real.log (1 + u)) / u ^ 2) u :=
        (hd1.div (hasDerivAt_id u) hu0.ne').congr_deriv (by
          simp only [id_eq]; field_simp [hu0.ne']; ring)
      rw [hg'.deriv]
      exact div_pos (by linarith [Real.log_lt_sub_one_of_pos h1u (by linarith)]) (sq_pos_of_pos hu0)
  intro d₁ d₂ hd12
  have hstep : ∀ d : ℕ, quadB (d + 4) κ - quadB (d + 2) κ =
      (2 * κ - 2) * Real.log 2 + g (2 / ((d : ℝ) + 4)) := by
    intro d
    have hp4 := mul_pos (Real.rpow_pos_of_pos two_pos (κ * ((d + 4 : ℕ) : ℝ)))
      (quadD_pos (d := d + 4) (by omega))
    have hp2 := mul_pos (Real.rpow_pos_of_pos two_pos (κ * ((d + 2 : ℕ) : ℝ)))
      (quadD_pos (d := d + 2) (by omega))
    unfold quadB
    rw [← Real.log_div hp4.ne' hp2.ne']
    have hpow : (2 : ℝ) ^ (κ * ((d + 4 : ℕ) : ℝ)) / (2 : ℝ) ^ (κ * ((d + 2 : ℕ) : ℝ)) =
        (2 : ℝ) ^ (2 * κ) := by push_cast; rw [← Real.rpow_sub two_pos]; congr 1; ring
    rw [mul_div_mul_comm, hpow, quadD_parity_step (by omega), mul_left_comm, ← mul_assoc,
      show (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) by norm_num, ← Real.rpow_add two_pos,
      Real.log_mul (Real.rpow_pos_of_pos two_pos _).ne' (Real.rpow_pos_of_pos (by positivity) _).ne',
      Real.log_rpow two_pos, Real.log_rpow (by positivity)]
    push_cast
    rw [show g (2 / ((d : ℝ) + 4)) = (((d : ℝ) + 2) / 2 + 2) * Real.log (1 + 2 / ((d : ℝ) + 2 + 2)) by
      dsimp [g]; field_simp; ring_nf]
    ring
  dsimp only; rw [hstep d₁, hstep d₂]
  linarith [hg_mono (by positivity : (0 : ℝ) < 2 / ((d₂ : ℝ) + 4))
    (by positivity : (0 : ℝ) < 2 / ((d₁ : ℝ) + 4)) (by gcongr)]

lemma discrete_concave_pos {a : ℕ → ℝ} (hanti : Antitone (fun k => a (k + 1) - a k))
    {N : ℕ} (h0 : 0 < a 0) (hN : 0 < a N) : ∀ k ≤ N, 0 < a k := by
  intro k hkN; by_contra hle; rw [not_lt] at hle
  have hneg : ∃ i < k, a (i + 1) - a i < 0 := by
    by_contra hnone; push Not at hnone
    have hsum : 0 ≤ ∑ i ∈ Finset.range k, (a (i + 1) - a i) :=
      Finset.sum_nonneg fun i hi => hnone i (Finset.mem_range.mp hi)
    rw [Finset.sum_range_sub a k] at hsum; linarith
  rcases hneg with ⟨i, hik, hi_neg⟩
  have hsum2 : ∑ j ∈ Finset.Ico k N, (a (j + 1) - a j) < 0 :=
    Finset.sum_neg (fun j hj => (hanti (by have := (Finset.mem_Ico.mp hj).1; omega)).trans_lt hi_neg)
      ⟨k, Finset.left_mem_Ico.mpr (lt_of_le_of_ne hkN (by rintro rfl; linarith))⟩
  rw [Finset.sum_Ico_eq_sub _ hkN, Finset.sum_range_sub, Finset.sum_range_sub] at hsum2
  linarith

private lemma abs_six_terms_le (a b c d e f : ℝ) :
    |a - b + c + d - e - f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
  have h1 := abs_sub (a - b + c + d - e) f
  have h2 := abs_sub (a - b + c + d) e
  have h3 := abs_add_le (a - b + c) d
  have h4 := abs_add_le (a - b) c
  have h5 := abs_sub a b
  linarith

private lemma quadB_even_eval_bounds {n : ℕ} (hn : 1 ≤ n) (κ : ℝ)
    (k_n k_d : ℤ) (x_n x_d : ℝ) (hxn : |x_n| < 1) (hxd : |x_d| < 1)
    (hrn : (n : ℝ) = (2 : ℝ) ^ k_n * (1 - x_n)⁻¹)
    (hrd : (1 + (n : ℝ)⁻¹ : ℝ) = (2 : ℝ) ^ k_d * (1 - x_d)⁻¹) (N : ℕ) :
    |quadB (2 * n) κ - (-(1 / 2 : ℝ) * (287209 / 414355 + 1.144730) +
        (1 / 2 : ℝ) * ((k_n : ℝ) * (287209 / 414355) + ∑ i ∈ Finset.range N, x_n ^ (i + 1) / (i + 1)) +
        ((n : ℝ) + 1) * ((k_d : ℝ) * (287209 / 414355) + ∑ i ∈ Finset.range 4, x_d ^ (i + 1) / (i + 1)) +
        n * (1 - 2 * (1 - κ) * (287209 / 414355)) - 1 / (12 * n))| ≤
      1 / (2 * 10 ^ 10) + 1 / 10 ^ 6 +
        (1 / 2) * (|(k_n : ℝ)| * (1 / 10 ^ 10) + |x_n| ^ (N + 1) / (1 - |x_n|)) +
        ((n : ℝ) + 1) * (|(k_d : ℝ)| * (1 / 10 ^ 10) + |x_d| ^ 5 / (1 - |x_d|)) +
        (2 * n * |1 - κ|) * (1 / 10 ^ 10) + 1 / (144 * (n : ℝ) ^ 3) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hG : Real.Gamma (((2 * n : ℕ) : ℝ) / 2 + 1) = (n.factorial : ℝ) := by
    push_cast; rw [show 2 * (n : ℝ) / 2 + 1 = (n : ℝ) + 1 by ring, Real.Gamma_nat_eq_factorial]
  let stErr := Real.log (n.factorial : ℝ) -
    ((1 / 2 : ℝ) * Real.log (2 * π) + ((n : ℝ) + 1 / 2) * Real.log n - n + 1 / (12 * n))
  have hb_eq : quadB (2 * n) κ =
      -(1 / 2 : ℝ) * (Real.log 2 + Real.log π) + (1 / 2 : ℝ) * Real.log n +
        ((n : ℝ) + 1) * Real.log (1 + (n : ℝ)⁻¹) + n * (1 - 2 * (1 - κ) * Real.log 2) -
        1 / (12 * n) - stErr := by
    unfold quadB quadD
    rw [hG, Real.log_mul (by positivity) (by positivity), Real.log_rpow two_pos,
      Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
      Real.log_mul two_pos.ne' (by positivity), Real.log_rpow (by positivity)]
    push_cast
    rw [show (2 * (n : ℝ) + 2) = 2 * ((n : ℝ) + 1) by ring,
      show (2 * ((n : ℝ) + 1)) / 8 = ((n : ℝ) + 1) / 4 by ring,
      show 2 * (n : ℝ) / 2 = n by ring,
      Real.log_mul two_ne_zero (by positivity),
      Real.log_div (by positivity) (by norm_num), Real.log_four_eq]
    have hlogn1 : Real.log ((n : ℝ) + 1) = Real.log n + Real.log (1 + (n : ℝ)⁻¹) := by
      rw [show (n : ℝ) + 1 = (n : ℝ) * (1 + (n : ℝ)⁻¹) by field_simp,
        Real.log_mul hn0.ne' (by positivity)]
    rw [hlogn1]
    dsimp only [stErr]; rw [Real.log_mul two_ne_zero Real.pi_ne_zero]; ring
  rw [hb_eq, show (-(1 / 2 : ℝ) * (Real.log 2 + Real.log π) + (1 / 2 : ℝ) * Real.log n +
      ((n : ℝ) + 1) * Real.log (1 + (n : ℝ)⁻¹) + n * (1 - 2 * (1 - κ) * Real.log 2) -
      1 / (12 * n) - stErr) - _ =
      -(1 / 2 : ℝ) * (Real.log 2 - 287209 / 414355) - (1 / 2 : ℝ) * (Real.log π - 1.144730) +
        (1 / 2 : ℝ) * (Real.log n - ((k_n : ℝ) * (287209 / 414355) +
          ∑ i ∈ Finset.range N, x_n ^ (i + 1) / (i + 1))) +
        ((n : ℝ) + 1) * (Real.log (1 + (n : ℝ)⁻¹) - ((k_d : ℝ) * (287209 / 414355) +
          ∑ i ∈ Finset.range 4, x_d ^ (i + 1) / (i + 1))) -
        (2 * n * (1 - κ)) * (Real.log 2 - 287209 / 414355) - stErr by ring]
  refine (abs_six_terms_le _ _ _ _ _ _).trans ?_
  have hpi := log_pi_bounds; have hl2 := Real.log_two_near_10
  have hln := log_dyadic_approx k_n x_n hxn hrn N; have hld := log_dyadic_approx k_d x_d hxd hrd 4
  have hst := log_factorial_stirling_bounds hn
  have hpi_err : |Real.log π - 1.144730| ≤ 1 / 10 ^ 6 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hst_err : |stErr| ≤ 1 / (144 * (n : ℝ) ^ 3) :=
    abs_le.mpr (by dsimp only [stErr]; constructor <;> linarith)
  have ha1 : |-(1 / 2 : ℝ) * (Real.log 2 - 287209 / 414355)| ≤ 1 / 2 * (1 / 10 ^ 10) := by
    rw [abs_mul, abs_neg, abs_of_pos (by norm_num)]; exact mul_le_mul_of_nonneg_left hl2 (by norm_num)
  have ha2 : |(1 / 2 : ℝ) * (Real.log π - 1.144730)| ≤ 1 / 2 * (1 / 10 ^ 6) := by
    rw [abs_mul, abs_of_pos (by norm_num)]; exact mul_le_mul_of_nonneg_left hpi_err (by norm_num)
  have ha3 : |(1 / 2 : ℝ) * (Real.log n - ((k_n : ℝ) * (287209 / 414355) +
      ∑ i ∈ Finset.range N, x_n ^ (i + 1) / (i + 1)))| ≤
      1 / 2 * (|(k_n : ℝ)| * (1 / 10 ^ 10) + |x_n| ^ (N + 1) / (1 - |x_n|)) := by
    rw [abs_mul, abs_of_pos (by norm_num)]; exact mul_le_mul_of_nonneg_left hln (by norm_num)
  have ha4 : |((n : ℝ) + 1) * (Real.log (1 + (n : ℝ)⁻¹) - ((k_d : ℝ) * (287209 / 414355) +
      ∑ i ∈ Finset.range 4, x_d ^ (i + 1) / (i + 1)))| ≤
      ((n : ℝ) + 1) * (|(k_d : ℝ)| * (1 / 10 ^ 10) + |x_d| ^ 5 / (1 - |x_d|)) := by
    rw [abs_mul, abs_of_pos (by positivity)]; exact mul_le_mul_of_nonneg_left hld (by positivity)
  have ha5 : |(2 * (n : ℝ) * (1 - κ)) * (Real.log 2 - 287209 / 414355)| ≤
      (2 * n * |1 - κ|) * (1 / 10 ^ 10) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hl2 (by positivity)
  linarith

private lemma quadB_odd_eval_bounds {m : ℕ} (hm : 1 ≤ m) (κ : ℝ)
    (k_m k_d : ℤ) (x_m x_d : ℝ) (hxm : |x_m| < 1) (hxd : |x_d| < 1)
    (hrm : (m : ℝ) = (2 : ℝ) ^ k_m * (1 - x_m)⁻¹)
    (hrd : (1 + (2 * (m : ℝ))⁻¹ : ℝ) = (2 : ℝ) ^ k_d * (1 - x_d)⁻¹) (N : ℕ) :
    |quadB (2 * m - 1) κ - (-(1 / 2 : ℝ) * (287209 / 414355 + 1.144730) +
        (1 / 2 : ℝ) * ((k_m : ℝ) * (287209 / 414355) + ∑ i ∈ Finset.range N, x_m ^ (i + 1) / (i + 1)) +
        ((m : ℝ) + 1 / 2) * ((k_d : ℝ) * (287209 / 414355) + ∑ i ∈ Finset.range 4, x_d ^ (i + 1) / (i + 1)) +
        m - (2 * m - 1) * (1 - κ) * (287209 / 414355) + 1 / (24 * m))| ≤
      1 / (2 * 10 ^ 10) + 1 / 10 ^ 6 +
        (1 / 2) * (|(k_m : ℝ)| * (1 / 10 ^ 10) + |x_m| ^ (N + 1) / (1 - |x_m|)) +
        ((m : ℝ) + 1 / 2) * (|(k_d : ℝ)| * (1 / 10 ^ 10) + |x_d| ^ 5 / (1 - |x_d|)) +
        ((2 * m - 1 : ℝ) * |1 - κ|) * (1 / 10 ^ 10) + 1 / (144 * (m : ℝ) ^ 3) := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hG : Real.Gamma (((2 * m - 1 : ℕ) : ℝ) / 2 + 1) = Real.Gamma ((m : ℝ) + 1 / 2) := by
    congr 1; rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hd_cast : ((2 * m - 1 : ℕ) : ℝ) = 2 * (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  let gErr := Real.log (Real.Gamma ((m : ℝ) + 1 / 2)) -
    ((1 / 2 : ℝ) * Real.log (2 * π) + m * Real.log m - m - 1 / (24 * m))
  have hb_eq : quadB (2 * m - 1) κ =
      -(1 / 2 : ℝ) * (Real.log 2 + Real.log π) + (1 / 2 : ℝ) * Real.log m +
        ((m : ℝ) + 1 / 2) * Real.log (1 + (2 * (m : ℝ))⁻¹) + m -
        (2 * m - 1) * (1 - κ) * Real.log 2 + 1 / (24 * m) - gErr := by
    unfold quadB quadD
    rw [hG, hd_cast, show 2 * (m : ℝ) - 1 + 2 = 2 * m + 1 by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_rpow two_pos,
      Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
      Real.log_mul two_pos.ne' (Real.Gamma_pos_of_pos (by positivity)).ne', Real.log_rpow (by positivity),
      Real.log_div (by positivity) (by norm_num),
      show Real.log 8 = 3 * Real.log 2 by rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; ring,
      show 2 * (m : ℝ) + 1 = 2 * m * (1 + (2 * (m : ℝ))⁻¹) by field_simp,
      Real.log_mul (by positivity) (by positivity), Real.log_mul two_ne_zero hm0.ne']
    dsimp only [gErr]; rw [Real.log_mul two_ne_zero Real.pi_ne_zero]; ring
  rw [hb_eq, show (-(1 / 2 : ℝ) * (Real.log 2 + Real.log π) + (1 / 2 : ℝ) * Real.log m +
      ((m : ℝ) + 1 / 2) * Real.log (1 + (2 * (m : ℝ))⁻¹) + m -
      (2 * m - 1) * (1 - κ) * Real.log 2 + 1 / (24 * m) - gErr) - _ =
      -(1 / 2 : ℝ) * (Real.log 2 - 287209 / 414355) - (1 / 2 : ℝ) * (Real.log π - 1.144730) +
        (1 / 2 : ℝ) * (Real.log m - ((k_m : ℝ) * (287209 / 414355) +
          ∑ i ∈ Finset.range N, x_m ^ (i + 1) / (i + 1))) +
        ((m : ℝ) + 1 / 2) * (Real.log (1 + (2 * (m : ℝ))⁻¹) - ((k_d : ℝ) * (287209 / 414355) +
          ∑ i ∈ Finset.range 4, x_d ^ (i + 1) / (i + 1))) -
        ((2 * m - 1 : ℝ) * (1 - κ)) * (Real.log 2 - 287209 / 414355) - gErr by ring]
  refine (abs_six_terms_le _ _ _ _ _ _).trans ?_
  have hpi := log_pi_bounds; have hl2 := Real.log_two_near_10
  have hln := log_dyadic_approx k_m x_m hxm hrm N; have hld := log_dyadic_approx k_d x_d hxd hrd 4
  have hG_bd := log_gamma_half_odd_bounds hm
  have hpi_err : |Real.log π - 1.144730| ≤ 1 / 10 ^ 6 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hG_err : |gErr| ≤ 1 / (144 * (m : ℝ) ^ 3) :=
    abs_le.mpr (by dsimp only [gErr]; constructor <;> linarith)
  have ha1 : |-(1 / 2 : ℝ) * (Real.log 2 - 287209 / 414355)| ≤ 1 / 2 * (1 / 10 ^ 10) := by
    rw [abs_mul, abs_neg, abs_of_pos (by norm_num)]; exact mul_le_mul_of_nonneg_left hl2 (by norm_num)
  have ha2 : |(1 / 2 : ℝ) * (Real.log π - 1.144730)| ≤ 1 / 2 * (1 / 10 ^ 6) := by
    rw [abs_mul, abs_of_pos (by norm_num)]; exact mul_le_mul_of_nonneg_left hpi_err (by norm_num)
  have ha3 : |(1 / 2 : ℝ) * (Real.log m - ((k_m : ℝ) * (287209 / 414355) +
      ∑ i ∈ Finset.range N, x_m ^ (i + 1) / (i + 1)))| ≤
      1 / 2 * (|(k_m : ℝ)| * (1 / 10 ^ 10) + |x_m| ^ (N + 1) / (1 - |x_m|)) := by
    rw [abs_mul, abs_of_pos (by norm_num)]; exact mul_le_mul_of_nonneg_left hln (by norm_num)
  have ha4 : |((m : ℝ) + 1 / 2) * (Real.log (1 + (2 * (m : ℝ))⁻¹) - ((k_d : ℝ) * (287209 / 414355) +
      ∑ i ∈ Finset.range 4, x_d ^ (i + 1) / (i + 1)))| ≤
      ((m : ℝ) + 1 / 2) * (|(k_d : ℝ)| * (1 / 10 ^ 10) + |x_d| ^ 5 / (1 - |x_d|)) := by
    rw [abs_mul, abs_of_pos (by positivity)]; exact mul_le_mul_of_nonneg_left hld (by positivity)
  have ha5 : |((2 * (m : ℝ) - 1) * (1 - κ)) * (Real.log 2 - 287209 / 414355)| ≤
      ((2 * m - 1 : ℝ) * |1 - κ|) * (1 / 10 ^ 10) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith)]
    exact mul_le_mul_of_nonneg_left hl2 (mul_nonneg (by linarith) (abs_nonneg _))
  linarith

private lemma quadB_2_3_pos : 0 < quadB 2 (1 / 4) ∧ 0 < quadB 3 (1 / 4) := by
  constructor
  · rw [quadB_pos_iff (by norm_num) (1 / 4)]
    have hD2 : quadD 2 = 1 := by
      unfold quadD; push_cast
      rw [show (2 : ℝ) / 2 + 1 = ((1 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
      norm_num
    rw [hD2]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
      (by norm_num : -(1 / 4 : ℝ) * ((2 : ℕ) : ℝ) < 0)
  · rw [quadB_pos_iff (by norm_num) (1 / 4)]
    have hπ := Real.sqrt_pos.mpr Real.pi_pos
    have hG : Real.Gamma ((3 : ℝ) / 2 + 1) = (3 / 4 : ℝ) * √π := by
      rw [Real.Gamma_add_one (by norm_num),
        show (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 by norm_num, Real.Gamma_add_one (by norm_num),
        Real.Gamma_one_half_eq]; ring
    have hD3 : quadD 3 = 10 / (3 * √π) * (5 / 8 : ℝ) ^ (3 / 2 : ℝ) := by
      unfold quadD; push_cast; rw [hG]; ring_nf
    rw [hD3, ← Real.rpow_lt_rpow_iff (by positivity) (by positivity) (by norm_num : (0 : ℝ) < 4),
      ← Real.rpow_mul two_pos.le,
      show -(1 / 4 : ℝ) * ((3 : ℕ) : ℝ) * 4 = (-3 : ℝ) by norm_num,
      show (2 : ℝ) ^ (-3 : ℝ) = (1 / 8 : ℝ) by norm_num,
      show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h2 : (10 / (3 * √π) * (5 / 8 : ℝ) ^ (3 / 2 : ℝ)) ^ 4 =
        10 ^ 4 * (5 / 8 : ℝ) ^ 6 / (81 * π ^ 2) := by
      rw [mul_pow, div_pow, ← Real.rpow_natCast ((5 / 8 : ℝ) ^ (3 / 2 : ℝ)) 4,
        ← Real.rpow_mul (by norm_num), mul_pow,
        show (√π) ^ 4 = π ^ 2 by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt Real.pi_pos.le]]
      norm_num; ring
    rw [h2, lt_div_iff₀ (by positivity)]
    nlinarith [Real.pi_lt_four, Real.pi_pos]

private lemma quadB_global_from_crossings (d₀ : ℕ) (κ : ℝ) (hd0 : 4 ≤ d₀) (hκ : 1 / 4 ≤ κ)
    (hstep0 : 1 + 2 / ((d₀ : ℝ) + 2) - 2 * (1 - κ) * Real.log 2 < 0)
    (hpos2 : 0 < quadB (d₀ - 2) κ) (hpos1 : 0 < quadB (d₀ - 1) κ)
    (hneg0 : quadB d₀ κ ≤ 0) (hneg1 : quadB (d₀ + 1) κ ≤ 0) :
    (∀ d : ℕ, d₀ ≤ d → quadD d ≤ (2 : ℝ) ^ (-κ * d)) ∧
      (∀ d : ℕ, 2 ≤ d → d < d₀ → (2 : ℝ) ^ (-κ * d) < quadD d) := by
  have hdec : ∀ d, d₀ ≤ d → quadB (d + 2) κ < quadB d κ := fun d hd => by
    have h1 := quadB_step_le (by omega : 2 ≤ d) κ
    have h2 : 1 + 2 / ((d : ℝ) + 2) ≤ 1 + 2 / ((d₀ : ℝ) + 2) := by gcongr
    linarith
  have hge : ∀ d, d₀ ≤ d → quadB d κ ≤ 0 := fun d hd => by
    obtain ⟨k, rfl | rfl⟩ : ∃ k, d = d₀ + 2 * k ∨ d = d₀ + 1 + 2 * k := ⟨(d - d₀) / 2, by omega⟩
    · induction k with
      | zero => simpa using hneg0
      | succ k ih => rw [show d₀ + 2 * (k + 1) = d₀ + 2 * k + 2 by ring]; linarith [hdec (d₀ + 2 * k) (by omega), ih (by omega)]
    · induction k with
      | zero => simpa using hneg1
      | succ k ih => rw [show d₀ + 1 + 2 * (k + 1) = d₀ + 1 + 2 * k + 2 by ring]; linarith [hdec (d₀ + 1 + 2 * k) (by omega), ih (by omega)]
  have hmono_k : ∀ d : ℕ, quadB d (1 / 4) ≤ quadB d κ := fun d => by
    unfold quadB
    have hGpos : 0 < Real.Gamma ((d : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
    have hDpos : 0 < quadD d := by unfold quadD; positivity
    refine Real.log_le_log (mul_pos (Real.rpow_pos_of_pos two_pos _) hDpos) ?_
    gcongr; norm_num
  have hb2 := lt_of_lt_of_le quadB_2_3_pos.1 (hmono_k 2)
  have hb3 := lt_of_lt_of_le quadB_2_3_pos.2 (hmono_k 3)
  have heven_anti : Antitone (fun k => quadB (2 * (k + 1) + 2) κ - quadB (2 * k + 2) κ) := by
    intro k₁ k₂ hk
    have h1 := (quadB_step_strictAnti κ).antitone (by omega : 2 * k₁ ≤ 2 * k₂)
    simpa [show ∀ k, 2 * (k + 1) + 2 = 2 * k + 4 by intro; omega] using h1
  have hodd_anti : Antitone (fun k => quadB (2 * (k + 1) + 3) κ - quadB (2 * k + 3) κ) := by
    intro k₁ k₂ hk
    have h1 := (quadB_step_strictAnti κ).antitone (by omega : 2 * k₁ + 1 ≤ 2 * k₂ + 1)
    simpa [show ∀ k, 2 * (k + 1) + 3 = (2 * k + 1) + 4 by intro; omega,
      show ∀ k, 2 * k + 3 = (2 * k + 1) + 2 by intro; omega] using h1
  refine ⟨fun d hd => (quadB_le_zero_iff (by omega) κ).mp (hge d hd), fun d hd2 hdlt => ?_⟩
  rw [← quadB_pos_iff hd2 κ]
  rcases Nat.even_or_odd d with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have : ∃ k, m + m = 2 * k + 2 := ⟨m - 1, by omega⟩
    rcases this with ⟨k, hk_eq⟩; rw [hk_eq]
    rcases Nat.even_or_odd d₀ with ⟨m₀, hd₀⟩ | ⟨m₀, hd₀⟩
    · refine discrete_concave_pos (a := fun j => quadB (2 * j + 2) κ) heven_anti
        (N := m₀ - 2) hb2 (by convert hpos2 using 2; omega) k (by omega)
    · refine discrete_concave_pos (a := fun j => quadB (2 * j + 2) κ) heven_anti
        (N := m₀ - 1) hb2 (by convert hpos1 using 2; omega) k (by omega)
  · have : ∃ k, 2 * m + 1 = 2 * k + 3 := ⟨m - 1, by omega⟩
    rcases this with ⟨k, hk_eq⟩; rw [hk_eq]
    rcases Nat.even_or_odd d₀ with ⟨m₀, hd₀⟩ | ⟨m₀, hd₀⟩
    · refine discrete_concave_pos (a := fun j => quadB (2 * j + 3) κ) hodd_anti
        (N := m₀ - 2) hb3 (by convert hpos1 using 2; omega) k (by omega)
    · refine discrete_concave_pos (a := fun j => quadB (2 * j + 3) κ) hodd_anti
        (N := m₀ - 2) hb3 (by convert hpos2 using 2; omega) k (by omega)

theorem quadD_bounds_104 :
    (∀ d : ℕ, 104 ≤ d → quadD d ≤ (2 : ℝ) ^ (-(1 / 4 : ℝ) * d)) ∧
      (∀ d : ℕ, 2 ≤ d → d < 104 → (2 : ℝ) ^ (-(1 / 4 : ℝ) * d) < quadD d) := by
  have h102 := quadB_even_eval_bounds (n := 51) (by norm_num) (1 / 4) 6 0 (-13 / 51) (1 / 52)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  have h103 := quadB_odd_eval_bounds (m := 52) (by norm_num) (1 / 4) 6 0 (-3 / 13) (1 / 105)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  have h104 := quadB_even_eval_bounds (n := 52) (by norm_num) (1 / 4) 6 0 (-3 / 13) (1 / 53)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  have h105 := quadB_odd_eval_bounds (m := 53) (by norm_num) (1 / 4) 6 0 (-11 / 53) (1 / 107)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  norm_num [Finset.sum_range_succ] at h102 h103 h104 h105
  exact quadB_global_from_crossings 104 (1 / 4) (by norm_num) le_rfl
    (by linarith [Real.log_two_gt_d9]) (by linarith [(abs_le.mp h102).1])
    (by linarith [(abs_le.mp h103).1]) (by linarith [(abs_le.mp h104).2])
    (by linarith [(abs_le.mp h105).2])

theorem quadD_bounds_469 :
    (∀ d : ℕ, 469 ≤ d → quadD d ≤ (2 : ℝ) ^ (-(0.27 : ℝ) * d)) ∧
      (∀ d : ℕ, 2 ≤ d → d < 469 → (2 : ℝ) ^ (-(0.27 : ℝ) * d) < quadD d) := by
  have h467 := quadB_odd_eval_bounds (m := 234) (by norm_num) 0.27 8 0 (-11 / 117) (1 / 469)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  have h468 := quadB_even_eval_bounds (n := 234) (by norm_num) 0.27 8 0 (-11 / 117) (1 / 235)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  have h469 := quadB_odd_eval_bounds (m := 235) (by norm_num) 0.27 8 0 (-21 / 235) (1 / 471)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  have h470 := quadB_even_eval_bounds (n := 235) (by norm_num) 0.27 8 0 (-21 / 235) (1 / 236)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  norm_num [Finset.sum_range_succ] at h467 h468 h469 h470
  exact quadB_global_from_crossings 469 0.27 (by norm_num) (by norm_num)
    (by linarith [Real.log_two_gt_d9]) (by linarith [(abs_le.mp h467).1])
    (by linarith [(abs_le.mp h468).1]) (by linarith [(abs_le.mp h469).2])
    (by linarith [(abs_le.mp h470).2])

theorem quadD_bounds_9544 :
    (∀ d : ℕ, 9544 ≤ d → quadD d ≤ (2 : ℝ) ^ (-(0.278 : ℝ) * d)) ∧
      (∀ d : ℕ, 2 ≤ d → d < 9544 → (2 : ℝ) ^ (-(0.278 : ℝ) * d) < quadD d) := by
  have h9542 := quadB_even_eval_bounds (n := 4771) (by norm_num) 0.278 12 0 (675 / 4771) (1 / 4772)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 12
  have h9543 := quadB_odd_eval_bounds (m := 4772) (by norm_num) 0.278 12 0 (169 / 1193) (1 / 9545)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 12
  have h9544 := quadB_even_eval_bounds (n := 4772) (by norm_num) 0.278 12 0 (169 / 1193) (1 / 4773)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 12
  have h9545 := quadB_odd_eval_bounds (m := 4773) (by norm_num) 0.278 12 0 (677 / 4773) (1 / 9547)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 12
  norm_num [Finset.sum_range_succ] at h9542 h9543 h9544 h9545
  exact quadB_global_from_crossings 9544 0.278 (by norm_num) (by norm_num)
    (by linarith [Real.log_two_gt_d9]) (by linarith [(abs_le.mp h9542).1])
    (by linarith [(abs_le.mp h9543).1]) (by linarith [(abs_le.mp h9544).2])
    (by linarith [(abs_le.mp h9545).2])

/-- **Theorem E.2 (`thm:ce-quadratic-dimensions`, `(eq:finite:E.2)`).** -/
theorem ce_quadratic_dimensions :
    (∀ d : ℕ, 104 ≤ d → optimalCohnElkiesBound d ≤ (2 : ℝ) ^ (-(1 / 4 : ℝ) * d)) ∧
    (∀ d : ℕ, 469 ≤ d → optimalCohnElkiesBound d ≤ (2 : ℝ) ^ (-(0.27 : ℝ) * d)) ∧
    (∀ d : ℕ, 9544 ≤ d → optimalCohnElkiesBound d ≤ (2 : ℝ) ^ (-(0.278 : ℝ) * d)) :=
  ⟨fun d hd => (optimalCohnElkiesBound_le_quadD (by omega)).trans (quadD_bounds_104.1 d hd),
   fun d hd => (optimalCohnElkiesBound_le_quadD (by omega)).trans (quadD_bounds_469.1 d hd),
   fun d hd => (optimalCohnElkiesBound_le_quadD (by omega)).trans (quadD_bounds_9544.1 d hd)⟩

/-! ### Section 5: Theorem E.2' — Cubic Laguerre Gaussian (`thm:ce-cubic`, `(eq:finite:E.5a)`–`(eq:finite:E.5b)`) -/

/-- Laguerre polynomials `L_n^{(α)}` for `n ≤ 3`. -/
noncomputable def laguerreSmall (α : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => Polynomial.C (α + 1) - Polynomial.X
  | 2 => Polynomial.C ((α + 1) * (α + 2) / 2) - Polynomial.C (α + 2) * Polynomial.X +
      Polynomial.C (1 / 2 : ℝ) * Polynomial.X ^ 2
  | 3 => Polynomial.C ((α + 1) * (α + 2) * (α + 3) / 6) -
      Polynomial.C ((α + 2) * (α + 3) / 2) * Polynomial.X +
      Polynomial.C ((α + 3) / 2) * Polynomial.X ^ 2 -
      Polynomial.C (1 / 6 : ℝ) * Polynomial.X ^ 3
  | _ + 4 => 0

lemma laguerreSmall_natDegree_le (α : ℝ) {n : ℕ} (hn : n ≤ 3) :
    (laguerreSmall α n).natDegree ≤ 3 := by
  interval_cases n <;> simp [laguerreSmall] <;> compute_degree!

lemma laguerreSmall_fourier_eigen (c : ℝ) {n : ℕ} (hn : n ≤ 3) (x : ℝ) :
    (fourierPolyTransform c (laguerreSmall (c - 1) n)).eval x =
      (-1 : ℝ) ^ n * (laguerreSmall (c - 1) n).eval x := by
  rw [fourierPolyTransform_eval c (laguerreSmall_natDegree_le _ hn)]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  have hR0 : (fourierBasisPoly c 0).eval x = 1 := by simp [fourierBasisPoly]
  have hR1 : (fourierBasisPoly c 1).eval x = 2 * c - x := by simp [fourierBasisPoly]
  have hR2 : (fourierBasisPoly c 2).eval x = 4 * c * (c + 1) - 4 * (c + 1) * x + x ^ 2 := by
    simp [fourierBasisPoly, Polynomial.derivative_C, Polynomial.derivative_X]; ring
  have hR3 : (fourierBasisPoly c 3).eval x =
      8 * c * (c + 1) * (c + 2) - 12 * (c + 1) * (c + 2) * x + 6 * (c + 2) * x ^ 2 - x ^ 3 := by
    simp [fourierBasisPoly, Polynomial.derivative_C, Polynomial.derivative_X,
      Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_add]; ring
  rw [hR0, hR1, hR2, hR3]
  interval_cases n <;>
    simp [laguerreSmall, Polynomial.coeff_one, Polynomial.coeff_C, Polynomial.coeff_X,
      Polynomial.coeff_X_pow] <;> ring

noncomputable def cubicTheta (d : ℕ) : ℝ := 2 * ((d : ℝ) + 4) / ((d : ℝ) + 6)
noncomputable def cubicA2 (d : ℕ) : ℝ := 2 * cubicTheta d - ((d : ℝ) + 4)
noncomputable def cubicA0 (d : ℕ) : ℝ :=
  cubicTheta d * ((d : ℝ) + 4) ^ 2 - (d : ℝ) * ((d : ℝ) + 2) / 8 * cubicA2 d

noncomputable def cubicPPoly (d : ℕ) : ℝ[X] :=
  Polynomial.C (cubicA0 d) * laguerreSmall ((d : ℝ) / 2 - 1) 0 +
    Polynomial.C (cubicA2 d) * laguerreSmall ((d : ℝ) / 2 - 1) 2

noncomputable def cubicQPoly (d : ℕ) : ℝ[X] :=
  Polynomial.C (((d : ℝ) / 2 + 1) * ((d : ℝ) / 2 + 2)) * laguerreSmall ((d : ℝ) / 2 - 1) 1 -
    Polynomial.C 6 * laguerreSmall ((d : ℝ) / 2 - 1) 3

noncomputable def cubicHPoly (d : ℕ) : ℝ[X] := cubicPPoly d - cubicQPoly d

noncomputable def cubicH (d : ℕ) (x : Euc d) : ℝ :=
  (cubicHPoly d).eval (2 * π * ‖x‖ ^ 2) * Real.exp (-π * ‖x‖ ^ 2)

noncomputable def cubicU (d : ℕ) : ℝ := (((d : ℝ) + 6) ^ 2 - 2) / ((d : ℝ) + 6)
noncomputable def cubicUSharp (d : ℕ) : ℝ := (d : ℝ) + 6 - 7 / (2 * ((d : ℝ) + 6))
noncomputable def cubicR (d : ℕ) : ℝ := Real.sqrt (cubicU d / (2 * π))
noncomputable def cubicRSharp (d : ℕ) : ℝ := Real.sqrt (cubicUSharp d / (2 * π))

noncomputable def genD (d : ℕ) (r : ℝ) : ℝ :=
  (r / 8) ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1)

noncomputable def cubicD (d : ℕ) : ℝ := genD d (cubicU d)
noncomputable def cubicDSharp (d : ℕ) : ℝ := genD d (cubicUSharp d)
noncomputable def kappaGauss : ℝ := 1 - 1 / (2 * Real.log 2)

lemma cubicQPoly_eval (d : ℕ) (X : ℝ) :
    (cubicQPoly d).eval X =
      X * (X ^ 2 - 3 / 2 * ((d : ℝ) + 4) * X + 1 / 2 * ((d : ℝ) + 2) * ((d : ℝ) + 4)) := by
  unfold cubicQPoly laguerreSmall; simp; ring

lemma cubicP_add_Q_eval (d : ℕ) (X : ℝ) :
    (cubicPPoly d + cubicQPoly d).eval X = (X + cubicTheta d) * (X - ((d : ℝ) + 4)) ^ 2 := by
  unfold cubicPPoly cubicQPoly cubicA0 cubicA2 cubicTheta laguerreSmall
  simp; field_simp [(by positivity : (d : ℝ) + 6 ≠ 0)]; ring

lemma cubicH_fourier_eq (d : ℕ) (y : Euc d) :
    𝓕 (fun x : Euc d => (cubicH d x : ℂ)) y =
      (((2 * π * ‖y‖ ^ 2 + cubicTheta d) * (2 * π * ‖y‖ ^ 2 - ((d : ℝ) + 4)) ^ 2 *
        Real.exp (-π * ‖y‖ ^ 2) : ℝ) : ℂ) := by
  have h1 : (fun x : Euc d => (cubicH d x : ℂ)) =
      fun x => ((cubicHPoly d).eval (2 * π * ‖x‖ ^ 2) * Real.exp (-π * ‖x‖ ^ 2) : ℂ) := by
    ext x; simp [cubicH]
  rw [h1, fourier_poly_gaussian d (cubicHPoly d)]
  congr 1
  have hlin : (fourierPolyTransform ((d : ℝ) / 2) (cubicHPoly d)).eval (2 * π * ‖y‖ ^ 2) =
      (cubicPPoly d + cubicQPoly d).eval (2 * π * ‖y‖ ^ 2) := by
    have hdegP : (cubicPPoly d).natDegree ≤ 3 := by
      unfold cubicPPoly
      exact (Polynomial.natDegree_add_le _ _).trans (max_le
        ((Polynomial.natDegree_C_mul_le _ _).trans (laguerreSmall_natDegree_le _ (by norm_num)))
        ((Polynomial.natDegree_C_mul_le _ _).trans (laguerreSmall_natDegree_le _ (by norm_num))))
    have hdegQ : (cubicQPoly d).natDegree ≤ 3 := by
      unfold cubicQPoly
      exact (Polynomial.natDegree_sub_le _ _).trans (max_le
        ((Polynomial.natDegree_C_mul_le _ _).trans (laguerreSmall_natDegree_le _ (by norm_num)))
        ((Polynomial.natDegree_C_mul_le _ _).trans (laguerreSmall_natDegree_le _ (by norm_num))))
    have hdegH : (cubicHPoly d).natDegree ≤ 3 := by
      unfold cubicHPoly; exact (Polynomial.natDegree_sub_le _ _).trans (max_le hdegP hdegQ)
    rw [fourierPolyTransform_eval _ hdegH]
    let x := 2 * π * ‖y‖ ^ 2
    have hL0 := laguerreSmall_fourier_eigen ((d : ℝ) / 2) (n := 0) (by norm_num) x
    have hL1 := laguerreSmall_fourier_eigen ((d : ℝ) / 2) (n := 1) (by norm_num) x
    have hL2 := laguerreSmall_fourier_eigen ((d : ℝ) / 2) (n := 2) (by norm_num) x
    have hL3 := laguerreSmall_fourier_eigen ((d : ℝ) / 2) (n := 3) (by norm_num) x
    rw [fourierPolyTransform_eval _ (laguerreSmall_natDegree_le _ (by norm_num))] at hL0 hL1 hL2 hL3
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add] at *
    have hH_coeff : ∀ k, (cubicHPoly d).coeff k =
        cubicA0 d * (laguerreSmall ((d : ℝ) / 2 - 1) 0).coeff k +
        cubicA2 d * (laguerreSmall ((d : ℝ) / 2 - 1) 2).coeff k -
        ((d : ℝ) / 2 + 1) * ((d : ℝ) / 2 + 2) * (laguerreSmall ((d : ℝ) / 2 - 1) 1).coeff k +
        6 * (laguerreSmall ((d : ℝ) / 2 - 1) 3).coeff k := fun k => by
      simp only [cubicHPoly, cubicPPoly, cubicQPoly, Polynomial.coeff_sub,
        Polynomial.coeff_add, Polynomial.coeff_C_mul]
      ring
    simp_rw [hH_coeff]
    have hP_eval : (cubicPPoly d).eval x =
        cubicA0 d * (laguerreSmall ((d : ℝ) / 2 - 1) 0).eval x +
        cubicA2 d * (laguerreSmall ((d : ℝ) / 2 - 1) 2).eval x := by
      simp [cubicPPoly]
    have hQ_eval : (cubicQPoly d).eval x =
        ((d : ℝ) / 2 + 1) * ((d : ℝ) / 2 + 2) * (laguerreSmall ((d : ℝ) / 2 - 1) 1).eval x -
        6 * (laguerreSmall ((d : ℝ) / 2 - 1) 3).eval x := by
      simp [cubicQPoly]
    rw [Polynomial.eval_add, hP_eval, hQ_eval]
    change _ = _ at hL0 hL1 hL2 hL3
    calc _ = cubicA0 d * ((-1 : ℝ) ^ 0 * (laguerreSmall ((d : ℝ) / 2 - 1) 0).eval x) +
          cubicA2 d * ((-1 : ℝ) ^ 2 * (laguerreSmall ((d : ℝ) / 2 - 1) 2).eval x) -
          ((d : ℝ) / 2 + 1) * ((d : ℝ) / 2 + 2) *
            ((-1 : ℝ) ^ 1 * (laguerreSmall ((d : ℝ) / 2 - 1) 1).eval x) +
          6 * ((-1 : ℝ) ^ 3 * (laguerreSmall ((d : ℝ) / 2 - 1) 3).eval x) := by
            rw [← hL0, ← hL1, ← hL2, ← hL3]; ring
      _ = _ := by ring
  rw [hlin, cubicP_add_Q_eval]

lemma cubicH_origin (d : ℕ) :
    cubicH d 0 = cubicTheta d * ((d : ℝ) + 4) ^ 2 ∧
      𝓕 (fun x : Euc d => (cubicH d x : ℂ)) 0 =
        ((cubicTheta d * ((d : ℝ) + 4) ^ 2 : ℝ) : ℂ) := by
  have h0 : (cubicHPoly d).eval 0 = (cubicPPoly d + cubicQPoly d).eval 0 := by
    have hq0 : (cubicQPoly d).eval 0 = 0 := by rw [cubicQPoly_eval]; ring
    unfold cubicHPoly; simp [hq0]
  refine ⟨?_, ?_⟩
  · simp only [cubicH, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, Real.exp_zero, mul_one]
    rw [h0, cubicP_add_Q_eval]; ring
  · rw [cubicH_fourier_eq, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add,
      Real.exp_zero, mul_one, zero_sub]
    congr 1; ring

lemma cubicH_radial (d : ℕ) : IsRadialSchwartz d (cubicH d) := by
  let P : ℝ[X] := (cubicHPoly d).comp ((2 * π) • Polynomial.X)
  have h0 : cubicH d = fun x => P.eval (‖x‖ ^ 2) * Real.exp (-π * 1 * ‖x‖ ^ 2) := by
    ext x; simp [cubicH, P, mul_assoc]
  rw [h0]
  exact isRadialSchwartz_poly_gaussian d one_pos P

lemma cubicQ_shift (d : ℕ) (v : ℝ) :
    -(cubicHPoly d).eval ((d : ℝ) + 4 + v) =
      v ^ 3 + (2 * (d : ℝ) + 8 - cubicTheta d) * v ^ 2 +
        ((d : ℝ) + 4) * ((d : ℝ) + 2) * v - 2 * ((d : ℝ) + 4) ^ 2 := by
  have h1 : -cubicHPoly d = 2 * cubicQPoly d - (cubicPPoly d + cubicQPoly d) := by
    unfold cubicHPoly; ring
  rw [show -(cubicHPoly d).eval ((d : ℝ) + 4 + v) =
      (2 * cubicQPoly d - (cubicPPoly d + cubicQPoly d)).eval ((d : ℝ) + 4 + v) by
    rw [← Polynomial.eval_neg, h1], Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_ofNat, cubicP_add_Q_eval, cubicQPoly_eval]
  ring

lemma cubicQ_mono {d : ℕ} {v₁ v₂ : ℝ} (hv1 : 0 ≤ v₁) (hv12 : v₁ ≤ v₂) :
    -(cubicHPoly d).eval ((d : ℝ) + 4 + v₁) ≤ -(cubicHPoly d).eval ((d : ℝ) + 4 + v₂) := by
  rw [cubicQ_shift, cubicQ_shift]
  have hth : 2 * (d : ℝ) + 8 - cubicTheta d > 0 := by
    unfold cubicTheta; rw [gt_iff_lt, sub_pos, div_lt_iff₀ (by positivity)]; nlinarith
  have hv2 : 0 ≤ v₂ := hv1.trans hv12
  have h3 : v₁ ^ 3 ≤ v₂ ^ 3 := pow_le_pow_left₀ hv1 hv12 3
  have h2 : v₁ ^ 2 ≤ v₂ ^ 2 := pow_le_pow_left₀ hv1 hv12 2
  nlinarith [mul_le_mul_of_nonneg_left h2 hth.le,
    mul_le_mul_of_nonneg_left hv12 (by positivity : 0 ≤ ((d : ℝ) + 4) * ((d : ℝ) + 2))]

lemma cubicH_neg_ge_u (d : ℕ) (x : Euc d) (hx : cubicR d ≤ ‖x‖) : cubicH d x < 0 := by
  have hu_pos : 0 < cubicU d := by
    unfold cubicU
    have : 2 < ((d : ℝ) + 6) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
    exact div_pos (by linarith) (by positivity)
  have hX : cubicU d ≤ 2 * π * ‖x‖ ^ 2 := by
    have hsq : cubicU d / (2 * π) ≤ ‖x‖ ^ 2 := by
      rw [← Real.sq_sqrt (div_nonneg hu_pos.le (by positivity))]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hx 2
    nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2 * π),
      show 2 * π * (cubicU d / (2 * π)) = cubicU d by field_simp [Real.pi_ne_zero]]
  let v₀ : ℝ := 2 * ((d : ℝ) + 5) / ((d : ℝ) + 6)
  have hv₀_nonneg : 0 ≤ v₀ := by dsimp [v₀]; positivity
  have hu_shift : (d : ℝ) + 4 + v₀ = cubicU d := by
    unfold cubicU; dsimp [v₀]; field_simp [(by positivity : (d : ℝ) + 6 ≠ 0)]; ring
  have hQ_u : 0 < -(cubicHPoly d).eval (cubicU d) := by
    rw [← hu_shift, cubicQ_shift]
    have halg : v₀ ^ 3 + (2 * (d : ℝ) + 8 - cubicTheta d) * v₀ ^ 2 +
        ((d : ℝ) + 4) * ((d : ℝ) + 2) * v₀ - 2 * ((d : ℝ) + 4) ^ 2 =
        2 * ((d : ℝ) + 4) ^ 3 / ((d : ℝ) + 6) ^ 2 +
          8 * ((d : ℝ) + 5) ^ 2 / ((d : ℝ) + 6) ^ 3 := by
      dsimp [v₀]; unfold cubicTheta; field_simp [(by positivity : (d : ℝ) + 6 ≠ 0)]; ring
    rw [halg]; positivity
  have hQ_mono : -(cubicHPoly d).eval (cubicU d) ≤ -(cubicHPoly d).eval (2 * π * ‖x‖ ^ 2) := by
    rw [← hu_shift, show 2 * π * ‖x‖ ^ 2 = (d : ℝ) + 4 + (2 * π * ‖x‖ ^ 2 - ((d : ℝ) + 4)) by ring]
    exact cubicQ_mono hv₀_nonneg (by linarith [hu_shift])
  have hneg : (cubicHPoly d).eval (2 * π * ‖x‖ ^ 2) < 0 := by linarith
  exact mul_neg_of_neg_of_pos hneg (Real.exp_pos _)

lemma cubicH_neg_ge_uSharp {d : ℕ} (hd : 20 ≤ d) (x : Euc d) (hx : cubicRSharp d ≤ ‖x‖) :
    cubicH d x < 0 := by
  have hd20 : (20 : ℝ) ≤ d := by exact_mod_cast hd
  have hu_pos : 0 < cubicUSharp d := by
    unfold cubicUSharp; rw [sub_pos, div_lt_iff₀ (by positivity)]; nlinarith
  have hX : cubicUSharp d ≤ 2 * π * ‖x‖ ^ 2 := by
    have hsq : cubicUSharp d / (2 * π) ≤ ‖x‖ ^ 2 := by
      rw [← Real.sq_sqrt (div_nonneg hu_pos.le (by positivity))]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hx 2
    nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2 * π),
      show 2 * π * (cubicUSharp d / (2 * π)) = cubicUSharp d by field_simp [Real.pi_ne_zero]]
  let v₀ : ℝ := 2 - 7 / (2 * ((d : ℝ) + 6))
  have hv₀_nonneg : 0 ≤ v₀ := by
    dsimp [v₀]; rw [sub_nonneg, div_le_iff₀ (by positivity)]; linarith
  have hu_shift : (d : ℝ) + 4 + v₀ = cubicUSharp d := by
    unfold cubicUSharp; dsimp [v₀]; ring
  have hQ_u : 0 < -(cubicHPoly d).eval (cubicUSharp d) := by
    rw [← hu_shift, cubicQ_shift]
    set e : ℝ := ((d - 20 : ℕ) : ℝ)
    have he0 : 0 ≤ e := Nat.cast_nonneg _
    have hde : (d : ℝ) = e + 20 := by
      dsimp [e]; rw [Nat.cast_sub hd]; push_cast; ring
    have he26 : (e + 26 : ℝ) ≠ 0 := by linarith
    have halg : v₀ ^ 3 + (2 * (d : ℝ) + 8 - cubicTheta d) * v₀ ^ 2 +
        ((d : ℝ) + 4) * ((d : ℝ) + 2) * v₀ - 2 * ((d : ℝ) + 4) ^ 2 =
        (4 * e ^ 4 + 296 * e ^ 3 + 7300 * e ^ 2 + 60080 * e + 1921) /
          (8 * ((d : ℝ) + 6) ^ 3) := by
      dsimp [v₀]; unfold cubicTheta; rw [hde]
      rw [show (e + 20 + 6 : ℝ) = e + 26 by ring]
      field_simp [he26]; ring
    rw [halg]; positivity
  have hQ_mono : -(cubicHPoly d).eval (cubicUSharp d) ≤
      -(cubicHPoly d).eval (2 * π * ‖x‖ ^ 2) := by
    rw [← hu_shift, show 2 * π * ‖x‖ ^ 2 = (d : ℝ) + 4 + (2 * π * ‖x‖ ^ 2 - ((d : ℝ) + 4)) by ring]
    exact cubicQ_mono hv₀_nonneg (by linarith [hu_shift])
  exact mul_neg_of_neg_of_pos (by linarith) (Real.exp_pos _)

private lemma cubicH_admissible_of_radius {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r)
    (hnonpos : ∀ x : Euc d, r ≤ ‖x‖ → cubicH d x ≤ 0) :
    IsCohnElkiesAdmissible d r (cubicH d) := by
  obtain ⟨⟨S, hS⟩, _⟩ := cubicH_radial d
  have hS_eq : (fun x : Euc d => (cubicH d x : ℂ)) = S := funext fun x => (hS x).symm
  refine ⟨hr, by unfold cubicH; fun_prop,
    Complex.reCLM.integrable_comp (hS_eq ▸ S.integrable) |>.congr (Eventually.of_forall fun _ => by simp),
    by rw [hS_eq]; exact (𝓕 S).integrable,
    by rw [(cubicH_origin d).1]; unfold cubicTheta; positivity,
    by rw [(cubicH_origin d).2, Complex.ofReal_re]; unfold cubicTheta; positivity,
    hnonpos, fun y => ?_⟩
  rw [cubicH_fourier_eq]
  refine ⟨rfl, ?_⟩
  simp only [Complex.ofReal_re]
  unfold cubicTheta
  exact mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (Real.exp_pos _).le

lemma cubicH_bound_eq {d : ℕ} (hd : 1 ≤ d) {u : ℝ} (hu : 0 < u) :
    cohnElkiesBound d (Real.sqrt (u / (2 * π))) (cubicH d) = genD d u := by
  unfold cohnElkiesBound genD
  rw [(cubicH_origin d).1, (cubicH_origin d).2, Complex.ofReal_re,
    div_self (by unfold cubicTheta; positivity), one_mul,
    volume_half_ball_eq hd (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
  congr 1; field_simp [Real.pi_ne_zero]; ring_nf

theorem optimalCohnElkiesBound_le_cubicD {d : ℕ} (hd : 1 ≤ d) :
    optimalCohnElkiesBound d ≤ cubicD d := by
  have hu : 0 < cubicU d := by
    unfold cubicU; have : 2 < ((d : ℝ) + 6) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
    exact div_pos (by linarith) (by positivity)
  exact (optimalCohnElkiesBound_le (cubicH_admissible_of_radius hd
    (Real.sqrt_pos.mpr (by positivity)) fun x hx => (cubicH_neg_ge_u d x hx).le)).trans_eq
    (cubicH_bound_eq hd hu)

theorem optimalCohnElkiesBound_le_cubicDSharp_lt {d : ℕ} (hd : 20 ≤ d) :
    optimalCohnElkiesBound d ≤ cubicDSharp d ∧ cubicDSharp d < cubicD d := by
  have hd20 : (20 : ℝ) ≤ d := by exact_mod_cast hd
  have hu : 0 < cubicU d := by
    unfold cubicU; have : 2 < ((d : ℝ) + 6) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
    exact div_pos (by linarith) (by positivity)
  have hus : 0 < cubicUSharp d := by
    unfold cubicUSharp; rw [sub_pos, div_lt_iff₀ (by positivity)]; nlinarith
  have hlt_u : cubicUSharp d < cubicU d := by
    have hdiff : cubicU d - cubicUSharp d = 3 / (2 * ((d : ℝ) + 6)) := by
      unfold cubicU cubicUSharp; field_simp [(by positivity : (d : ℝ) + 6 ≠ 0)]; ring
    linarith [show (0 : ℝ) < 3 / (2 * ((d : ℝ) + 6)) by positivity]
  refine ⟨(optimalCohnElkiesBound_le (cubicH_admissible_of_radius (by omega)
      (Real.sqrt_pos.mpr (by positivity)) fun x hx =>
        (cubicH_neg_ge_uSharp hd x hx).le)).trans_eq (cubicH_bound_eq (by omega) hus), ?_⟩
  unfold cubicDSharp cubicD genD
  refine div_lt_div_of_pos_right
    (Real.rpow_lt_rpow (by positivity) (by gcongr) (by positivity))
    (Real.Gamma_pos_of_pos (by positivity))

lemma log_le_half_sub_inv {t : ℝ} (ht : 1 ≤ t) : Real.log t ≤ (t - t⁻¹) / 2 := by
  let f : ℝ → ℝ := fun x => (x - x⁻¹) / 2 - Real.log x
  have hmono : MonotoneOn f (Ici 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 1) ?_ ?_ ?_
    · exact ((continuousOn_id.sub (continuousOn_id.inv₀ fun x hx =>
          ne_of_gt (lt_of_lt_of_le zero_lt_one hx))).div_const 2).sub
        (Real.continuousOn_log.mono fun x hx => ne_of_gt (lt_of_lt_of_le zero_lt_one hx))
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : 0 < x := lt_trans zero_lt_one hx
      exact (((((hasDerivAt_id x).sub (hasDerivAt_inv hx0.ne')).div_const 2).sub
        (Real.hasDerivAt_log hx0.ne'))).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : 0 < x := lt_trans zero_lt_one hx
      have hd : HasDerivAt f ((x - 1) ^ 2 / (2 * x ^ 2)) x := by
        refine ((((hasDerivAt_id x).sub (hasDerivAt_inv hx0.ne')).div_const 2).sub
          (Real.hasDerivAt_log hx0.ne')).congr_deriv ?_
        field_simp [hx0.ne']; ring
      rw [hd.deriv]; positivity
  have := hmono (by simp : (1 : ℝ) ∈ Ici 1) ht ht
  dsimp [f] at this; norm_num at this; linarith

noncomputable def cubicB (d : ℕ) (κ : ℝ) : ℝ := Real.log ((2 : ℝ) ^ (κ * d) * cubicD d)

lemma cubicD_pos {d : ℕ} (hd : 1 ≤ d) : 0 < cubicD d := by
  unfold cubicD genD cubicU
  have : 2 < ((d : ℝ) + 6) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (d : ℝ) / 2 + 1)
  positivity

lemma cubicDSharp_pos {d : ℕ} (hd : 20 ≤ d) : 0 < cubicDSharp d := by
  have hd20 : (20 : ℝ) ≤ d := by exact_mod_cast hd
  unfold cubicDSharp genD cubicUSharp
  have h1 : 0 < (d : ℝ) + 6 - 7 / (2 * ((d : ℝ) + 6)) := by
    rw [sub_pos, div_lt_iff₀ (by positivity)]; nlinarith
  have := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (d : ℝ) / 2 + 1)
  positivity

theorem cubicB_step_neg {d : ℕ} (hd : 12 ≤ d) {κ : ℝ} (hκ : κ ≤ kappaGauss) :
    cubicB (d + 2) κ < cubicB d κ := by
  let t₁ : ℝ := cubicU (d + 2) / ((d : ℝ) + 2)
  let t₂ : ℝ := cubicU (d + 2) / cubicU d
  have hu_pos : ∀ k : ℕ, 0 < cubicU k := fun k => by
    unfold cubicU; have : 2 < ((k : ℝ) + 6) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
    exact div_pos (by linarith) (by positivity)
  have ht1_ge : 1 ≤ t₁ := by
    dsimp [t₁]; unfold cubicU; rw [one_le_div (by positivity), le_div_iff₀ (by positivity)]
    push_cast; nlinarith
  have ht2_ge : 1 ≤ t₂ := by
    dsimp [t₂]; rw [one_le_div (hu_pos d)]; unfold cubicU
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; push_cast; nlinarith
  have hratio : ((2 : ℝ) ^ (κ * ((d + 2 : ℕ) : ℝ)) * cubicD (d + 2)) /
      ((2 : ℝ) ^ (κ * d) * cubicD d) =
      (2 : ℝ) ^ (2 * (κ - 1)) * (t₁ * t₂ ^ ((d : ℝ) / 2)) := by
    have hpow : (2 : ℝ) ^ (κ * ((d + 2 : ℕ) : ℝ)) / (2 : ℝ) ^ (κ * d) = (2 : ℝ) ^ (2 * κ) := by
      push_cast; rw [← Real.rpow_sub two_pos]; congr 1; ring
    have hc : (d : ℝ) / 2 + 1 ≠ 0 := by positivity
    have hG : Real.Gamma ((d : ℝ) / 2 + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
    have hD_rat : cubicD (d + 2) / cubicD d = (1 / 4 : ℝ) * (t₁ * t₂ ^ ((d : ℝ) / 2)) := by
      unfold cubicD genD
      have hdiv_pow : (cubicU (d + 2) / 8) ^ ((d : ℝ) / 2) / (cubicU d / 8) ^ ((d : ℝ) / 2) =
          t₂ ^ ((d : ℝ) / 2) := by
        rw [← Real.div_rpow (div_pos (hu_pos _) (by positivity)).le
          (div_pos (hu_pos _) (by positivity)).le]
        dsimp [t₂]; congr 1; field_simp
      have hu2 : cubicU (d + 2) = ((d : ℝ) + 2) * t₁ := by
        dsimp [t₁]; field_simp [(by positivity : (d : ℝ) + 2 ≠ 0)]
      rw [show ((d + 2 : ℕ) : ℝ) / 2 + 1 = ((d : ℝ) / 2 + 1) + 1 by push_cast; ring,
        Real.Gamma_add_one hc,
        show ((d + 2 : ℕ) : ℝ) / 2 = (d : ℝ) / 2 + 1 by push_cast; ring,
        Real.rpow_add (div_pos (hu_pos _) (by positivity)), Real.rpow_one]
      calc (cubicU (d + 2) / 8) ^ ((d : ℝ) / 2) * (cubicU (d + 2) / 8) /
            (((d : ℝ) / 2 + 1) * Real.Gamma ((d : ℝ) / 2 + 1)) /
            ((cubicU d / 8) ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1))
          = ((cubicU (d + 2) / 8) ^ ((d : ℝ) / 2) / (cubicU d / 8) ^ ((d : ℝ) / 2)) *
              ((cubicU (d + 2) / 8) / ((d : ℝ) / 2 + 1)) := by field_simp [hG, hc]
        _ = t₂ ^ ((d : ℝ) / 2) * ((((d : ℝ) + 2) * t₁ / 8) / ((d : ℝ) / 2 + 1)) := by
              rw [hdiv_pow, hu2]
        _ = (1 / 4 : ℝ) * (t₁ * t₂ ^ ((d : ℝ) / 2)) := by field_simp [hc]; ring
    rw [mul_div_mul_comm, hpow, hD_rat, show (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) by norm_num,
      ← mul_assoc (2 ^ (2 * κ)), ← Real.rpow_add two_pos]
    congr 2; ring
  have hlog_step : cubicB (d + 2) κ - cubicB d κ ≤ (t₁ - t₁⁻¹) / 2 + (d : ℝ) * (t₂ - t₂⁻¹) / 4 - 1 := by
    unfold cubicB
    rw [← Real.log_div (mul_pos (Real.rpow_pos_of_pos two_pos _) (cubicD_pos (by omega))).ne'
      (mul_pos (Real.rpow_pos_of_pos two_pos _) (cubicD_pos (by omega))).ne', hratio,
      Real.log_mul (Real.rpow_pos_of_pos two_pos _).ne'
        (mul_pos (by linarith : 0 < t₁) (Real.rpow_pos_of_pos (by linarith) _)).ne',
      Real.log_mul (by linarith : t₁ ≠ 0) (Real.rpow_pos_of_pos (by linarith) _).ne',
      Real.log_rpow two_pos, Real.log_rpow (by linarith)]
    have hk_le : 2 * (κ - 1) * Real.log 2 ≤ -1 := by
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      calc 2 * (κ - 1) * Real.log 2
          ≤ 2 * (kappaGauss - 1) * Real.log 2 := by gcongr
        _ = -1 := by unfold kappaGauss; field_simp [hl2.ne']; ring
    have hl1 := log_le_half_sub_inv ht1_ge
    have hl2 := mul_le_mul_of_nonneg_left (log_le_half_sub_inv ht2_ge) (by positivity : 0 ≤ (d : ℝ) / 2)
    linarith
  set y : ℝ := ((d - 12 : ℕ) : ℝ)
  have hy0 : 0 ≤ y := Nat.cast_nonneg _
  have hdy : (d : ℝ) = y + 12 := by dsimp [y]; rw [Nat.cast_sub hd]; push_cast; ring
  let denom : ℝ := ((d : ℝ) + 2) * ((d : ℝ) + 6) * ((d : ℝ) + 8) *
    (((d : ℝ) + 6) ^ 2 - 2) * (((d : ℝ) + 8) ^ 2 - 2)
  have hdenom : 0 < denom := by
    dsimp [denom]
    have hd1 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    have h4 : 0 < ((d : ℝ) + 6) ^ 2 - 2 := by nlinarith
    have h5 : 0 < ((d : ℝ) + 8) ^ 2 - 2 := by nlinarith
    positivity
  have halg : (t₁ - t₁⁻¹) / 2 + (d : ℝ) * (t₂ - t₂⁻¹) / 4 - 1 =
      -(y ^ 6 + 94 * y ^ 5 + 3536 * y ^ 4 + 66598 * y ^ 3 + 629672 * y ^ 2 + 2421460 * y + 384216) /
        denom := by
    dsimp [t₁, t₂, denom]; unfold cubicU; push_cast
    rw [show ((d : ℝ) + 2 + 6) = (d : ℝ) + 8 by ring]
    have hd1 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    have h1 : (d : ℝ) + 2 ≠ 0 := by positivity
    have h2 : (d : ℝ) + 6 ≠ 0 := by positivity
    have h3 : (d : ℝ) + 8 ≠ 0 := by positivity
    have h4 : ((d : ℝ) + 6) ^ 2 - 2 ≠ 0 := by nlinarith
    have h5 : ((d : ℝ) + 8) ^ 2 - 2 ≠ 0 := by nlinarith
    field_simp [h1, h2, h3, h4, h5]
    rw [hdy]; ring
  have hneg_rhs : (t₁ - t₁⁻¹) / 2 + (d : ℝ) * (t₂ - t₂⁻¹) / 4 - 1 < 0 := by
    rw [halg, div_neg_iff]
    right; exact ⟨by linarith [show 0 < y ^ 6 + 94 * y ^ 5 + 3536 * y ^ 4 + 66598 * y ^ 3 +
      629672 * y ^ 2 + 2421460 * y + 384216 by positivity], hdenom⟩
  linarith

private lemma genB_even_eval_bounds {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) (κ Lκ Eκ : ℝ)
    (hLκ : |n * (1 - 2 * (1 - κ) * Real.log 2) - Lκ| ≤ Eκ)
    (k_n : ℤ) (x_n x_q : ℝ) (hxn : |x_n| < 1) (hxq : |x_q| < 1)
    (hrn : (n : ℝ) = (2 : ℝ) ^ k_n * (1 - x_n)⁻¹)
    (hrq : (r / 2 / n : ℝ) = (1 - x_q)⁻¹) (Nn Nq : ℕ) :
    |Real.log ((2 : ℝ) ^ (κ * (2 * n)) * genD (2 * n) r) -
      (-(1 / 2 : ℝ) * (287209 / 414355 + 1.144730) -
        (1 / 2 : ℝ) * ((k_n : ℝ) * (287209 / 414355) + ∑ i ∈ Finset.range Nn, x_n ^ (i + 1) / (i + 1)) +
        n * (∑ i ∈ Finset.range Nq, x_q ^ (i + 1) / (i + 1)) + Lκ - 1 / (12 * n))| ≤
      1 / (2 * 10 ^ 10) + 1 / 10 ^ 6 +
        (1 / 2) * (|(k_n : ℝ)| * (1 / 10 ^ 10) + |x_n| ^ (Nn + 1) / (1 - |x_n|)) +
        n * (|x_q| ^ (Nq + 1) / (1 - |x_q|)) + Eκ + 1 / (144 * (n : ℝ) ^ 3) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hG : Real.Gamma (((2 * n : ℕ) : ℝ) / 2 + 1) = (n.factorial : ℝ) := by
    push_cast; rw [show 2 * (n : ℝ) / 2 + 1 = (n : ℝ) + 1 by ring, Real.Gamma_nat_eq_factorial]
  let stErr := Real.log (n.factorial : ℝ) -
    ((1 / 2 : ℝ) * Real.log (2 * π) + ((n : ℝ) + 1 / 2) * Real.log n - n + 1 / (12 * n))
  have hb_eq : Real.log ((2 : ℝ) ^ (κ * (2 * n)) * genD (2 * n) r) =
      -(1 / 2 : ℝ) * (Real.log 2 + Real.log π) - (1 / 2 : ℝ) * Real.log n +
        n * Real.log (r / 2 / n) + n * (1 - 2 * (1 - κ) * Real.log 2) - 1 / (12 * n) - stErr := by
    unfold genD
    rw [hG, Real.log_mul (by positivity) (by positivity), Real.log_rpow two_pos,
      Real.log_div (by positivity) (by positivity), Real.log_rpow (by positivity)]
    push_cast
    rw [show 2 * (n : ℝ) / 2 = n by ring,
      show r / 8 = (r / 2 / n) * n / 4 by field_simp; norm_num,
      Real.log_div (by positivity) (by norm_num), Real.log_mul (by positivity) hn0.ne',
      Real.log_four_eq]
    dsimp only [stErr]; rw [Real.log_mul two_ne_zero Real.pi_ne_zero]; ring
  rw [hb_eq, show (-(1 / 2 : ℝ) * (Real.log 2 + Real.log π) - (1 / 2 : ℝ) * Real.log n +
        n * Real.log (r / 2 / n) + n * (1 - 2 * (1 - κ) * Real.log 2) - 1 / (12 * n) - stErr) -
      (-(1 / 2 : ℝ) * (287209 / 414355 + 1.144730) -
        (1 / 2 : ℝ) * ((k_n : ℝ) * (287209 / 414355) + ∑ i ∈ Finset.range Nn, x_n ^ (i + 1) / (i + 1)) +
        n * (∑ i ∈ Finset.range Nq, x_q ^ (i + 1) / (i + 1)) + Lκ - 1 / (12 * n)) =
      -(1 / 2 : ℝ) * (Real.log 2 - 287209 / 414355) - (1 / 2 : ℝ) * (Real.log π - 1.144730) -
        (1 / 2 : ℝ) * (Real.log n - ((k_n : ℝ) * (287209 / 414355) +
          ∑ i ∈ Finset.range Nn, x_n ^ (i + 1) / (i + 1))) +
        n * (Real.log (r / 2 / n) - ∑ i ∈ Finset.range Nq, x_q ^ (i + 1) / (i + 1)) +
        (n * (1 - 2 * (1 - κ) * Real.log 2) - Lκ) - stErr by ring]
  have h1 := abs_sub (-(1 / 2 : ℝ) * (Real.log 2 - 287209 / 414355) - (1 / 2 : ℝ) * (Real.log π - 1.144730) -
    (1 / 2 : ℝ) * (Real.log n - ((k_n : ℝ) * (287209 / 414355) + ∑ i ∈ Finset.range Nn, x_n ^ (i + 1) / (i + 1))) +
    n * (Real.log (r / 2 / n) - ∑ i ∈ Finset.range Nq, x_q ^ (i + 1) / (i + 1)) +
    (n * (1 - 2 * (1 - κ) * Real.log 2) - Lκ)) stErr
  have h2 := abs_add_le (-(1 / 2 : ℝ) * (Real.log 2 - 287209 / 414355) - (1 / 2 : ℝ) * (Real.log π - 1.144730) -
    (1 / 2 : ℝ) * (Real.log n - ((k_n : ℝ) * (287209 / 414355) + ∑ i ∈ Finset.range Nn, x_n ^ (i + 1) / (i + 1))) +
    n * (Real.log (r / 2 / n) - ∑ i ∈ Finset.range Nq, x_q ^ (i + 1) / (i + 1)))
    (n * (1 - 2 * (1 - κ) * Real.log 2) - Lκ)
  have h3 := abs_add_le (-(1 / 2 : ℝ) * (Real.log 2 - 287209 / 414355) - (1 / 2 : ℝ) * (Real.log π - 1.144730) -
    (1 / 2 : ℝ) * (Real.log n - ((k_n : ℝ) * (287209 / 414355) + ∑ i ∈ Finset.range Nn, x_n ^ (i + 1) / (i + 1))))
    (n * (Real.log (r / 2 / n) - ∑ i ∈ Finset.range Nq, x_q ^ (i + 1) / (i + 1)))
  have h4 := abs_sub (-(1 / 2 : ℝ) * (Real.log 2 - 287209 / 414355) - (1 / 2 : ℝ) * (Real.log π - 1.144730))
    ((1 / 2 : ℝ) * (Real.log n - ((k_n : ℝ) * (287209 / 414355) + ∑ i ∈ Finset.range Nn, x_n ^ (i + 1) / (i + 1))))
  have h5 := abs_sub (-(1 / 2 : ℝ) * (Real.log 2 - 287209 / 414355)) ((1 / 2 : ℝ) * (Real.log π - 1.144730))
  have hpi := log_pi_bounds; have hl2 := Real.log_two_near_10
  have hln := log_dyadic_approx k_n x_n hxn hrn Nn
  have hlq := log_dyadic_approx 0 x_q hxq (by simpa using hrq) Nq
  simp only [Int.cast_zero, zero_mul, zero_add, abs_zero] at hlq
  have hst := log_factorial_stirling_bounds hn
  have ha1 : |-(1 / 2 : ℝ) * (Real.log 2 - 287209 / 414355)| ≤ 1 / 2 * (1 / 10 ^ 10) := by
    rw [abs_mul, abs_neg, abs_of_pos (by norm_num)]; exact mul_le_mul_of_nonneg_left hl2 (by norm_num)
  have ha2 : |(1 / 2 : ℝ) * (Real.log π - 1.144730)| ≤ 1 / 2 * (1 / 10 ^ 6) := by
    rw [abs_mul, abs_of_pos (by norm_num)]
    exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) (by norm_num)
  have ha3 : |(1 / 2 : ℝ) * (Real.log n - ((k_n : ℝ) * (287209 / 414355) +
      ∑ i ∈ Finset.range Nn, x_n ^ (i + 1) / (i + 1)))| ≤
      1 / 2 * (|(k_n : ℝ)| * (1 / 10 ^ 10) + |x_n| ^ (Nn + 1) / (1 - |x_n|)) := by
    rw [abs_mul, abs_of_pos (by norm_num)]; exact mul_le_mul_of_nonneg_left hln (by norm_num)
  have ha4 : |(n : ℝ) * (Real.log (r / 2 / n) - ∑ i ∈ Finset.range Nq, x_q ^ (i + 1) / (i + 1))| ≤
      n * (|x_q| ^ (Nq + 1) / (1 - |x_q|)) := by
    rw [abs_mul, abs_of_pos hn0]; exact mul_le_mul_of_nonneg_left hlq hn0.le
  have hst_err : |stErr| ≤ 1 / (144 * (n : ℝ) ^ 3) :=
    abs_le.mpr (by dsimp only [stErr]; constructor <;> linarith)
  linarith

private lemma genB_odd_eval_bounds {m : ℕ} (hm : 1 ≤ m) {r : ℝ} (hr : 0 < r) (κ Lκ Eκ : ℝ)
    (hLκ : |(m : ℝ) - (2 * m - 1) * (1 - κ) * Real.log 2 - Lκ| ≤ Eκ)
    (k_m : ℤ) (x_m x_q : ℝ) (hxm : |x_m| < 1) (hxq : |x_q| < 1)
    (hrm : (m : ℝ) = (2 : ℝ) ^ k_m * (1 - x_m)⁻¹)
    (hrq : (r / 2 / m : ℝ) = (1 - x_q)⁻¹) (Nm Nq : ℕ) :
    |Real.log ((2 : ℝ) ^ (κ * (2 * m - 1 : ℕ)) * genD (2 * m - 1) r) -
      (-(1 / 2 : ℝ) * (287209 / 414355 + 1.144730) -
        (1 / 2 : ℝ) * ((k_m : ℝ) * (287209 / 414355) + ∑ i ∈ Finset.range Nm, x_m ^ (i + 1) / (i + 1)) +
        ((m : ℝ) - 1 / 2) * (∑ i ∈ Finset.range Nq, x_q ^ (i + 1) / (i + 1)) + Lκ + 1 / (24 * m))| ≤
      1 / (2 * 10 ^ 10) + 1 / 10 ^ 6 +
        (1 / 2) * (|(k_m : ℝ)| * (1 / 10 ^ 10) + |x_m| ^ (Nm + 1) / (1 - |x_m|)) +
        ((m : ℝ) - 1 / 2) * (|x_q| ^ (Nq + 1) / (1 - |x_q|)) + Eκ + 1 / (144 * (m : ℝ) ^ 3) := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hG : Real.Gamma (((2 * m - 1 : ℕ) : ℝ) / 2 + 1) = Real.Gamma ((m : ℝ) + 1 / 2) := by
    congr 1; rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hd_cast : ((2 * m - 1 : ℕ) : ℝ) = 2 * (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  let gErr := Real.log (Real.Gamma ((m : ℝ) + 1 / 2)) -
    ((1 / 2 : ℝ) * Real.log (2 * π) + m * Real.log m - m - 1 / (24 * m))
  have hb_eq : Real.log ((2 : ℝ) ^ (κ * (2 * m - 1 : ℕ)) * genD (2 * m - 1) r) =
      -(1 / 2 : ℝ) * (Real.log 2 + Real.log π) - (1 / 2 : ℝ) * Real.log m +
        ((m : ℝ) - 1 / 2) * Real.log (r / 2 / m) +
        ((m : ℝ) - (2 * m - 1) * (1 - κ) * Real.log 2) + 1 / (24 * m) - gErr := by
    unfold genD
    rw [hG, hd_cast, show (2 * (m : ℝ) - 1) / 2 = m - 1 / 2 by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_rpow two_pos,
      Real.log_div (by positivity) (Real.Gamma_pos_of_pos (by positivity)).ne',
      Real.log_rpow (by positivity),
      show r / 8 = (r / 2 / m) * m / 4 by field_simp; norm_num,
      Real.log_div (by positivity) (by norm_num), Real.log_mul (by positivity) hm0.ne',
      Real.log_four_eq]
    dsimp only [gErr]; rw [Real.log_mul two_ne_zero Real.pi_ne_zero]; ring
  rw [hb_eq, show (-(1 / 2 : ℝ) * (Real.log 2 + Real.log π) - (1 / 2 : ℝ) * Real.log m +
        ((m : ℝ) - 1 / 2) * Real.log (r / 2 / m) +
        ((m : ℝ) - (2 * m - 1) * (1 - κ) * Real.log 2) + 1 / (24 * m) - gErr) -
      (-(1 / 2 : ℝ) * (287209 / 414355 + 1.144730) -
        (1 / 2 : ℝ) * ((k_m : ℝ) * (287209 / 414355) + ∑ i ∈ Finset.range Nm, x_m ^ (i + 1) / (i + 1)) +
        ((m : ℝ) - 1 / 2) * (∑ i ∈ Finset.range Nq, x_q ^ (i + 1) / (i + 1)) + Lκ + 1 / (24 * m)) =
      -(1 / 2 : ℝ) * (Real.log 2 - 287209 / 414355) - (1 / 2 : ℝ) * (Real.log π - 1.144730) -
        (1 / 2 : ℝ) * (Real.log m - ((k_m : ℝ) * (287209 / 414355) +
          ∑ i ∈ Finset.range Nm, x_m ^ (i + 1) / (i + 1))) +
        ((m : ℝ) - 1 / 2) * (Real.log (r / 2 / m) - ∑ i ∈ Finset.range Nq, x_q ^ (i + 1) / (i + 1)) +
        ((m : ℝ) - (2 * m - 1) * (1 - κ) * Real.log 2 - Lκ) - gErr by ring]
  have h1 := abs_sub (-(1 / 2 : ℝ) * (Real.log 2 - 287209 / 414355) - (1 / 2 : ℝ) * (Real.log π - 1.144730) -
    (1 / 2 : ℝ) * (Real.log m - ((k_m : ℝ) * (287209 / 414355) + ∑ i ∈ Finset.range Nm, x_m ^ (i + 1) / (i + 1))) +
    ((m : ℝ) - 1 / 2) * (Real.log (r / 2 / m) - ∑ i ∈ Finset.range Nq, x_q ^ (i + 1) / (i + 1)) +
    ((m : ℝ) - (2 * m - 1) * (1 - κ) * Real.log 2 - Lκ)) gErr
  have h2 := abs_add_le (-(1 / 2 : ℝ) * (Real.log 2 - 287209 / 414355) - (1 / 2 : ℝ) * (Real.log π - 1.144730) -
    (1 / 2 : ℝ) * (Real.log m - ((k_m : ℝ) * (287209 / 414355) + ∑ i ∈ Finset.range Nm, x_m ^ (i + 1) / (i + 1))) +
    ((m : ℝ) - 1 / 2) * (Real.log (r / 2 / m) - ∑ i ∈ Finset.range Nq, x_q ^ (i + 1) / (i + 1)))
    ((m : ℝ) - (2 * m - 1) * (1 - κ) * Real.log 2 - Lκ)
  have h3 := abs_add_le (-(1 / 2 : ℝ) * (Real.log 2 - 287209 / 414355) - (1 / 2 : ℝ) * (Real.log π - 1.144730) -
    (1 / 2 : ℝ) * (Real.log m - ((k_m : ℝ) * (287209 / 414355) + ∑ i ∈ Finset.range Nm, x_m ^ (i + 1) / (i + 1))))
    (((m : ℝ) - 1 / 2) * (Real.log (r / 2 / m) - ∑ i ∈ Finset.range Nq, x_q ^ (i + 1) / (i + 1)))
  have h4 := abs_sub (-(1 / 2 : ℝ) * (Real.log 2 - 287209 / 414355) - (1 / 2 : ℝ) * (Real.log π - 1.144730))
    ((1 / 2 : ℝ) * (Real.log m - ((k_m : ℝ) * (287209 / 414355) + ∑ i ∈ Finset.range Nm, x_m ^ (i + 1) / (i + 1))))
  have h5 := abs_sub (-(1 / 2 : ℝ) * (Real.log 2 - 287209 / 414355)) ((1 / 2 : ℝ) * (Real.log π - 1.144730))
  have hpi := log_pi_bounds; have hl2 := Real.log_two_near_10
  have hln := log_dyadic_approx k_m x_m hxm hrm Nm
  have hlq := log_dyadic_approx 0 x_q hxq (by simpa using hrq) Nq
  simp only [Int.cast_zero, zero_mul, zero_add, abs_zero] at hlq
  have hG_bd := log_gamma_half_odd_bounds hm
  have ha1 : |-(1 / 2 : ℝ) * (Real.log 2 - 287209 / 414355)| ≤ 1 / 2 * (1 / 10 ^ 10) := by
    rw [abs_mul, abs_neg, abs_of_pos (by norm_num)]; exact mul_le_mul_of_nonneg_left hl2 (by norm_num)
  have ha2 : |(1 / 2 : ℝ) * (Real.log π - 1.144730)| ≤ 1 / 2 * (1 / 10 ^ 6) := by
    rw [abs_mul, abs_of_pos (by norm_num)]
    exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) (by norm_num)
  have ha3 : |(1 / 2 : ℝ) * (Real.log m - ((k_m : ℝ) * (287209 / 414355) +
      ∑ i ∈ Finset.range Nm, x_m ^ (i + 1) / (i + 1)))| ≤
      1 / 2 * (|(k_m : ℝ)| * (1 / 10 ^ 10) + |x_m| ^ (Nm + 1) / (1 - |x_m|)) := by
    rw [abs_mul, abs_of_pos (by norm_num)]; exact mul_le_mul_of_nonneg_left hln (by norm_num)
  have ha4 : |((m : ℝ) - 1 / 2) * (Real.log (r / 2 / m) - ∑ i ∈ Finset.range Nq, x_q ^ (i + 1) / (i + 1))| ≤
      ((m : ℝ) - 1 / 2) * (|x_q| ^ (Nq + 1) / (1 - |x_q|)) := by
    rw [abs_mul, abs_of_pos (by linarith)]; exact mul_le_mul_of_nonneg_left hlq (by linarith)
  have hG_err : |gErr| ≤ 1 / (144 * (m : ℝ) ^ 3) :=
    abs_le.mpr (by dsimp only [gErr]; constructor <;> linarith)
  linarith

private lemma rat_Lκ_even (n : ℕ) (κ : ℝ) :
    |(n : ℝ) * (1 - 2 * (1 - κ) * Real.log 2) - n * (1 - 2 * (1 - κ) * (287209 / 414355))| ≤
      (2 * n * |1 - κ|) * (1 / 10 ^ 10) := by
  rw [show (n : ℝ) * (1 - 2 * (1 - κ) * Real.log 2) - n * (1 - 2 * (1 - κ) * (287209 / 414355)) =
      (-(2 * n * (1 - κ))) * (Real.log 2 - 287209 / 414355) by ring,
    abs_mul, abs_neg, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2),
    abs_of_nonneg (Nat.cast_nonneg n)]
  exact mul_le_mul_of_nonneg_left Real.log_two_near_10 (by positivity)

private lemma rat_Lκ_odd {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) :
    |(m : ℝ) - (2 * m - 1) * (1 - κ) * Real.log 2 -
        ((m : ℝ) - (2 * m - 1) * (1 - κ) * (287209 / 414355))| ≤
      ((2 * m - 1 : ℝ) * |1 - κ|) * (1 / 10 ^ 10) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [show (m : ℝ) - (2 * m - 1) * (1 - κ) * Real.log 2 -
        ((m : ℝ) - (2 * m - 1) * (1 - κ) * (287209 / 414355)) =
      (-(2 * (m : ℝ) - 1) * (1 - κ)) * (Real.log 2 - 287209 / 414355) by ring,
    abs_mul, abs_mul, abs_neg, abs_of_nonneg (by linarith)]
  exact mul_le_mul_of_nonneg_left Real.log_two_near_10 (mul_nonneg (by linarith) (abs_nonneg _))

private lemma genD_le_of_log_nonpos {d : ℕ} {r κ : ℝ} (hr : 0 < r)
    (hlog : Real.log ((2 : ℝ) ^ (κ * d) * genD d r) ≤ 0) :
    genD d r ≤ (2 : ℝ) ^ (-κ * d) := by
  have hD : 0 < genD d r := by
    unfold genD; have := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (d : ℝ) / 2 + 1); positivity
  rw [Real.log_nonpos_iff (mul_pos (Real.rpow_pos_of_pos two_pos _) hD).le,
    mul_comm, ← le_div_iff₀ (Real.rpow_pos_of_pos two_pos _), one_div,
    ← Real.rpow_neg two_pos.le, ← neg_mul] at hlog
  exact hlog

private lemma cubicD_global_from_crossings (d₀ : ℕ) (hd0 : 12 ≤ d₀) (κ : ℝ) (hκ : κ ≤ kappaGauss)
    (h0 : cubicB d₀ κ ≤ 0) (h1 : cubicB (d₀ + 1) κ ≤ 0) :
    ∀ d : ℕ, d₀ ≤ d → optimalCohnElkiesBound d ≤ (2 : ℝ) ^ (-κ * d) := by
  have hge : ∀ d : ℕ, d₀ ≤ d → cubicB d κ ≤ 0 := fun d hd => by
    obtain ⟨k, rfl | rfl⟩ : ∃ k, d = d₀ + 2 * k ∨ d = d₀ + 1 + 2 * k := ⟨(d - d₀) / 2, by omega⟩
    · induction k with
      | zero => simpa using h0
      | succ k ih =>
        rw [show d₀ + 2 * (k + 1) = d₀ + 2 * k + 2 by ring]
        linarith [cubicB_step_neg (by omega : 12 ≤ d₀ + 2 * k) hκ, ih (by omega)]
    · induction k with
      | zero => simpa using h1
      | succ k ih =>
        rw [show d₀ + 1 + 2 * (k + 1) = d₀ + 1 + 2 * k + 2 by ring]
        linarith [cubicB_step_neg (by omega : 12 ≤ d₀ + 1 + 2 * k) hκ, ih (by omega)]
  intro d hd
  refine (optimalCohnElkiesBound_le_cubicD (by omega)).trans ?_
  have hu : 0 < cubicU d := by
    unfold cubicU; have : 2 < ((d : ℝ) + 6) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
    exact div_pos (by linarith) (by positivity)
  exact genD_le_of_log_nonpos hu (hge d hd)

/-- **Theorem E.2' (`thm:ce-cubic`, `(eq:finite:E.5b)`).** -/
theorem ce_cubic_dimensions :
    (∀ d : ℕ, 24 ≤ d → optimalCohnElkiesBound d ≤ (2 : ℝ) ^ (-(1 / 4 : ℝ) * d)) ∧
    (∀ d : ℕ, 48 ≤ d → optimalCohnElkiesBound d ≤ (2 : ℝ) ^ (-(0.27 : ℝ) * d)) ∧
    (∀ d : ℕ, 95 ≤ d → optimalCohnElkiesBound d ≤ (2 : ℝ) ^ (-(0.278 : ℝ) * d)) ∧
    (∀ d : ℕ, 106 ≤ d → optimalCohnElkiesBound d ≤ (2 : ℝ) ^ (-kappaGauss * d)) := by
  have hk25 : (1 / 4 : ℝ) ≤ kappaGauss := by
    unfold kappaGauss
    have hlog2 : (0.69 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hdiv : 1 / (2 * Real.log 2) ≤ 3 / 4 := by rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hk27 : (0.27 : ℝ) ≤ kappaGauss := by
    unfold kappaGauss
    have hlog2 : (0.693147 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hdiv : 1 / (2 * Real.log 2) ≤ 0.73 := by rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hk278 : (0.278 : ℝ) ≤ kappaGauss := by
    unfold kappaGauss
    have hlog2 : (0.69314718 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hdiv : 1 / (2 * Real.log 2) ≤ 0.722 := by rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hkG_ev : ∀ n : ℕ, |(n : ℝ) * (1 - 2 * (1 - kappaGauss) * Real.log 2) - 0| ≤ 0 := fun n => by
    unfold kappaGauss; have hl2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    rw [show 1 - 2 * (1 - (1 - 1 / (2 * Real.log 2))) * Real.log 2 = 0 by field_simp [hl2]; ring]
    simp
  have hkG_od : ∀ m : ℕ, |(m : ℝ) - (2 * m - 1) * (1 - kappaGauss) * Real.log 2 - 1 / 2| ≤ 0 := fun m => by
    unfold kappaGauss; have hl2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    rw [show (m : ℝ) - (2 * m - 1) * (1 - (1 - 1 / (2 * Real.log 2))) * Real.log 2 - 1 / 2 = 0 by
      field_simp [hl2]; ring]
    simp
  have hu25 := genB_odd_eval_bounds (m := 13) (by norm_num) (r := cubicU 25) (by unfold cubicU; norm_num)
    (1 / 4) _ _ (rat_Lκ_odd (by norm_num) _) 4 (-3 / 13) (153 / 959) (by norm_num) (by norm_num)
    (by norm_num) (by unfold cubicU; norm_num) 10 8
  have hu26 := genB_even_eval_bounds (n := 13) (by norm_num) (r := cubicU 26) (by unfold cubicU; norm_num)
    (1 / 4) _ _ (rat_Lκ_even 13 _) 4 (-3 / 13) (95 / 511) (by norm_num) (by norm_num)
    (by norm_num) (by unfold cubicU; norm_num) 10 8
  have hs24 := genB_even_eval_bounds (n := 12) (by norm_num) (r := cubicUSharp 24) (by unfold cubicUSharp; norm_num)
    (1 / 4) _ _ (rat_Lκ_even 12 _) 3 (1 / 3) (353 / 1793) (by norm_num) (by norm_num)
    (by norm_num) (by unfold cubicUSharp; norm_num) 10 8
  have hu49 := genB_odd_eval_bounds (m := 25) (by norm_num) (r := cubicU 49) (by unfold cubicU; norm_num)
    0.27 _ _ (rat_Lκ_odd (by norm_num) _) 5 (-7 / 25) (273 / 3023) (by norm_num) (by norm_num)
    (by norm_num) (by unfold cubicU; norm_num) 10 8
  have hu50 := genB_even_eval_bounds (n := 25) (by norm_num) (r := cubicU 50) (by unfold cubicU; norm_num)
    0.27 _ _ (rat_Lκ_even 25 _) 5 (-7 / 25) (167 / 1567) (by norm_num) (by norm_num)
    (by norm_num) (by unfold cubicU; norm_num) 10 8
  have hs48 := genB_even_eval_bounds (n := 24) (by norm_num) (r := cubicUSharp 48) (by unfold cubicUSharp; norm_num)
    0.27 _ _ (rat_Lκ_even 24 _) 4 (1 / 3) (641 / 5825) (by norm_num) (by norm_num)
    (by norm_num) (by unfold cubicUSharp; norm_num) 10 8
  have hu97 := genB_odd_eval_bounds (m := 49) (by norm_num) (r := cubicU 97) (by unfold cubicU; norm_num)
    0.278 _ _ (rat_Lκ_odd (by norm_num) _) 6 (-15 / 49) (513 / 10607) (by norm_num) (by norm_num)
    (by norm_num) (by unfold cubicU; norm_num) 10 8
  have hu98 := genB_even_eval_bounds (n := 49) (by norm_num) (r := cubicU 98) (by unfold cubicU; norm_num)
    0.278 _ _ (rat_Lκ_even 49 _) 6 (-15 / 49) (311 / 5407) (by norm_num) (by norm_num)
    (by norm_num) (by unfold cubicU; norm_num) 10 8
  have hs95 := genB_odd_eval_bounds (m := 48) (by norm_num) (r := cubicUSharp 95) (by unfold cubicUSharp; norm_num)
    0.278 _ _ (rat_Lκ_odd (by norm_num) _) 5 (1 / 3) (1003 / 20395) (by norm_num) (by norm_num)
    (by norm_num) (by unfold cubicUSharp; norm_num) 10 8
  have hs96 := genB_even_eval_bounds (n := 48) (by norm_num) (r := cubicUSharp 96) (by unfold cubicUSharp; norm_num)
    0.278 _ _ (rat_Lκ_even 48 _) 5 (1 / 3) (1217 / 20801) (by norm_num) (by norm_num)
    (by norm_num) (by unfold cubicUSharp; norm_num) 10 8
  have hu108 := genB_even_eval_bounds (n := 54) (by norm_num) (r := cubicU 108) (by unfold cubicU; norm_num)
    kappaGauss 0 0 (hkG_ev 54) 6 (-5 / 27) (341 / 6497) (by norm_num) (by norm_num)
    (by norm_num) (by unfold cubicU; norm_num) 10 8
  have hu109 := genB_odd_eval_bounds (m := 55) (by norm_num) (r := cubicU 109) (by unfold cubicU; norm_num)
    kappaGauss (1 / 2) 0 (hkG_od 55) 6 (-9 / 55) (573 / 13223) (by norm_num) (by norm_num)
    (by norm_num) (by unfold cubicU; norm_num) 10 8
  have hs106 := genB_even_eval_bounds (n := 53) (by norm_num) (r := cubicUSharp 106) (by unfold cubicUSharp; norm_num)
    kappaGauss 0 0 (hkG_ev 53) 6 (-11 / 53) (191 / 3583) (by norm_num) (by norm_num)
    (by norm_num) (by unfold cubicUSharp; norm_num) 10 8
  have hs107 := genB_odd_eval_bounds (m := 54) (by norm_num) (r := cubicUSharp 107) (by unfold cubicUSharp; norm_num)
    kappaGauss (1 / 2) 0 (hkG_od 54) 6 (-5 / 27) (1123 / 25531) (by norm_num) (by norm_num)
    (by norm_num) (by unfold cubicUSharp; norm_num) 10 8
  norm_num [Finset.sum_range_succ] at hu25 hu26 hs24 hu49 hu50 hs48 hu97 hu98 hs95 hs96 hu108 hu109 hs106 hs107
  refine ⟨fun d hd => ?_, fun d hd => ?_, fun d hd => ?_, fun d hd => ?_⟩
  · rcases eq_or_lt_of_le hd with rfl | hgt
    · exact (optimalCohnElkiesBound_le_cubicDSharp_lt (by norm_num)).1.trans
        (genD_le_of_log_nonpos (by unfold cubicUSharp; norm_num) (by linarith [(abs_le.mp hs24).2]))
    · exact cubicD_global_from_crossings 25 (by norm_num) (1 / 4) hk25
        (by unfold cubicB cubicD; linarith [(abs_le.mp hu25).2])
        (by unfold cubicB cubicD; linarith [(abs_le.mp hu26).2]) d hgt
  · rcases eq_or_lt_of_le hd with rfl | hgt
    · exact (optimalCohnElkiesBound_le_cubicDSharp_lt (by norm_num)).1.trans
        (genD_le_of_log_nonpos (by unfold cubicUSharp; norm_num) (by linarith [(abs_le.mp hs48).2]))
    · exact cubicD_global_from_crossings 49 (by norm_num) 0.27 hk27
        (by unfold cubicB cubicD; linarith [(abs_le.mp hu49).2])
        (by unfold cubicB cubicD; linarith [(abs_le.mp hu50).2]) d hgt
  · rcases lt_or_ge d 97 with hlt | hge
    · have : d = 95 ∨ d = 96 := by omega
      rcases this with rfl | rfl
      · exact (optimalCohnElkiesBound_le_cubicDSharp_lt (by norm_num)).1.trans
          (genD_le_of_log_nonpos (by unfold cubicUSharp; norm_num) (by linarith [(abs_le.mp hs95).2]))
      · exact (optimalCohnElkiesBound_le_cubicDSharp_lt (by norm_num)).1.trans
          (genD_le_of_log_nonpos (by unfold cubicUSharp; norm_num) (by linarith [(abs_le.mp hs96).2]))
    · exact cubicD_global_from_crossings 97 (by norm_num) 0.278 hk278
        (by unfold cubicB cubicD; linarith [(abs_le.mp hu97).2])
        (by unfold cubicB cubicD; linarith [(abs_le.mp hu98).2]) d hge
  · rcases lt_or_ge d 108 with hlt | hge
    · have : d = 106 ∨ d = 107 := by omega
      rcases this with rfl | rfl
      · exact (optimalCohnElkiesBound_le_cubicDSharp_lt (by norm_num)).1.trans
          (genD_le_of_log_nonpos (by unfold cubicUSharp; norm_num)
            (by push_cast; linarith [(abs_le.mp hs106).2]))
      · exact (optimalCohnElkiesBound_le_cubicDSharp_lt (by norm_num)).1.trans
          (genD_le_of_log_nonpos (by unfold cubicUSharp; norm_num)
            (by push_cast; linarith [(abs_le.mp hs107).2]))
    · exact cubicD_global_from_crossings 108 (by norm_num) kappaGauss le_rfl
        (by unfold cubicB cubicD; push_cast; linarith [(abs_le.mp hu108).2])
        (by unfold cubicB cubicD; rw [show (108 + 1 : ℕ) = 109 by norm_num]; push_cast
            linarith [(abs_le.mp hu109).2]) d hge


/-! ### Axiom Verification -/

/-- info: 'FormalResearch.CohnElkies.quadD_parity_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms quadD_parity_step

/-- info: 'FormalResearch.CohnElkies.quadB_step_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms quadB_step_le

/-- info: 'FormalResearch.CohnElkies.ce_quadratic_dimensions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_quadratic_dimensions

/-- info: 'FormalResearch.CohnElkies.optimalCohnElkiesBound_le_cubicD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms optimalCohnElkiesBound_le_cubicD

/-- info: 'FormalResearch.CohnElkies.optimalCohnElkiesBound_le_cubicDSharp_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms optimalCohnElkiesBound_le_cubicDSharp_lt

/-- info: 'FormalResearch.CohnElkies.cubicB_step_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubicB_step_neg

/-- info: 'FormalResearch.CohnElkies.ce_cubic_dimensions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_cubic_dimensions

end FormalResearch.CohnElkies
