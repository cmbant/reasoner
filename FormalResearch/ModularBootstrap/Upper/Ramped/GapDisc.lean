module

public import FormalResearch.ModularBootstrap.Upper.Window.Product

/-!
# Gap discs of the Airy zeros: uniform helper lemmas for the ramped Airy profile

Public copies (with explicit constants) of the private helper lemmas of
`Upper/Window/Product.lean` that the profile-uniform Airy product bound (`rem:profile`, Lemma
`P_unif`, `n2_ramped_comb.tex`) needs, together with the two statements that make the proof of the
fixed-design Lemma G (`ut:G`) uniform:

* `airyEnv_on_gap_disc_bounds`: `1 ≤ e(u) ≤ C_e` on the closed discs `B(a_n, gap_n / 4)`;
* `gap_disc_disjoint`: the discs `B(a_k, gap_k / 4)` are pairwise disjoint;
* `norm_airyProdFactor_sub_one_le`: the bound on `‖z_k‖` for a factor of the Airy product;
* `ratio_prefix_bound_unif`: the prefix ratio `‖(u - u_f) / ∏_{k ≤ f} (u - a_k)²‖` is bounded
  uniformly in a bounded first site `u_f`;
* `norm_le_of_gap_disc_extension`: a growth bound for an entire function that holds outside the gap
  discs extends to all of `ℂ` with the constant multiplied by `3^ν C_e` (maximum principle on each
  disc).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Window

lemma airyProdFactor_sub_one_eq (uSite epsU : ℕ → ℝ) (k : ℕ) {u : ℂ}
    (hu : u ≠ (airyZero k : ℂ)) :
    airyProdFactor uSite epsU k u - 1 =
      2 * ((airyZero k - uSite k : ℝ) : ℂ) / (u - (airyZero k : ℂ)) +
      (((airyZero k - uSite k : ℝ) : ℂ) ^ 2 + (epsU k : ℂ) ^ 2) / (u - (airyZero k : ℂ)) ^ 2 := by
  unfold airyProdFactor
  have hne : u - (airyZero k : ℂ) ≠ 0 := sub_ne_zero.mpr hu
  have heq : u - (uSite k : ℂ) = (u - (airyZero k : ℂ)) + ((airyZero k - uSite k : ℝ) : ℂ) := by
    push_cast; ring
  rw [heq]
  field_simp [hne]
  push_cast
  ring

lemma norm_airyProdFactor_sub_one_le (uSite epsU : ℕ → ℝ) (k : ℕ) {u : ℂ}
    (hu : u ≠ (airyZero k : ℂ)) :
    ‖airyProdFactor uSite epsU k u - 1‖ ≤
      2 * |airyZero k - uSite k| / ‖u - (airyZero k : ℂ)‖ +
      (|airyZero k - uSite k| ^ 2 + |epsU k| ^ 2) / ‖u - (airyZero k : ℂ)‖ ^ 2 := by
  rw [airyProdFactor_sub_one_eq uSite epsU k hu]
  refine (norm_add_le _ _).trans ?_
  gcongr
  · rw [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
  · rw [norm_div, norm_pow]
    gcongr
    exact (norm_add_le _ _).trans (by
      rw [norm_pow, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs])

/-- On each closed disc $\overline{D_n} = \overline{B}(a_n, \mathrm{gap}_n / 4)$ ($n \ge 1$),
$e(u) = \exp(-(4/3) \operatorname{Re} u^{3/2})$ satisfies $1 \le e(u) \le C_e$ with $C_e$ absolute. -/
lemma airyEnv_on_gap_disc_bounds :
    ∃ C_e > 0, ∀ n : ℕ, 1 ≤ n → ∀ u : ℂ, ‖u - (airyZero n : ℂ)‖ ≤ airyGap n / 4 →
      1 ≤ airyEnv u ∧ airyEnv u ≤ C_e := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hgap⟩ := airyGap_bounds_exists
  set B := (3 / 2 : ℝ) * c₂ + 2 * (c₂ / 8) ^ 3
  refine ⟨Real.exp (4 / 3 * B), Real.exp_pos _, fun n hn u hu => ?_⟩
  have h_gap_bd : airyGap n ≤ c₂ * (n : ℝ) ^ (-(1 / 3 : ℝ)) := (hgap n hn).2
  have hx_lb : 1 ≤ -u.re := by
    have ha1 : (233 / 100 : ℝ) < -airyZero 1 := by linarith [airyZero_one.2]
    have han : (233 / 100 : ℝ) < -airyZero n := by
      rcases hn.eq_or_lt with rfl | h1n
      · exact ha1
      · linarith [airyZero_lt_of_lt le_rfl h1n]
    have hre : u.re - airyZero n ≤ airyGap n / 4 := (abs_le.mp ((Complex.abs_re_le_norm _).trans hu)).2
    have hgap_ub : airyGap n / 4 ≤ 1 := by
      rcases hn.eq_or_lt with rfl | hn2
      · unfold airyGap
        have h1 := airyZero_one.2
        have h2 := airyZero_two.1
        linarith
      · have hg := (airyZero_gap_bounds hn2).2
        have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
        have hpow : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
        have hgap1 : airyGap n ≤ 2.05 := by unfold airyGap; nlinarith
        linarith
    linarith
  have hx_ub : -u.re ≤ 4 * (n : ℝ) ^ (2 / 3 : ℝ) := by
    have hre : -(airyGap n / 4) ≤ u.re - airyZero n := (abs_le.mp ((Complex.abs_re_le_norm _).trans hu)).1
    rcases hn.eq_or_lt with rfl | hn2
    · simp only [Nat.cast_one, Real.one_rpow, mul_one]
      have h1 := airyZero_one.1
      have h2 := airyZero_two.1
      unfold airyGap at hre
      linarith
    · have han_ub := (airyZero_abs_bounds hn2).2
      have hgap2 : airyGap n ≤ 2.05 * (n : ℝ) ^ (-(1 / 3 : ℝ)) := (airyZero_gap_bounds hn2).2
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hpow_le : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ (n : ℝ) ^ (2 / 3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      have hgap3 : airyGap n ≤ 2.05 * (n : ℝ) ^ (2 / 3 : ℝ) :=
        hgap2.trans (mul_le_mul_of_nonneg_left hpow_le (by norm_num))
      unfold airyGap at hgap3 hre
      linarith
  set x := -u.re
  set y := u.im
  set α := airySqrtRe u
  set β := (u ^ (1 / 2 : ℂ)).im
  have h1 := airySqrtRe_sq_sub u
  have h2 := airySqrtRe_mul_im u
  dsimp [airySqrtRe] at h1 h2
  have hα_nn : 0 ≤ α := cpow_half_re_nonneg u
  have hα2 : α ^ 2 - β ^ 2 = -x := by
    change (u ^ (1 / 2 : ℂ)).re ^ 2 - (u ^ (1 / 2 : ℂ)).im ^ 2 = -(-u.re)
    rw [neg_neg]; exact h1
  have hβ2 : x ≤ β ^ 2 := by linarith [sq_nonneg α]
  have h_re_cube : (u ^ (3 / 2 : ℂ)).re = α * (α ^ 2 - 3 * β ^ 2) := by
    rw [← cpow_half_cube, re_cube]
    change (u ^ (1 / 2 : ℂ)).re ^ 3 - 3 * (u ^ (1 / 2 : ℂ)).re * (u ^ (1 / 2 : ℂ)).im ^ 2 =
      (u ^ (1 / 2 : ℂ)).re * ((u ^ (1 / 2 : ℂ)).re ^ 2 - 3 * (u ^ (1 / 2 : ℂ)).im ^ 2)
    ring
  have h_re_nonpos : (u ^ (3 / 2 : ℂ)).re ≤ 0 := by
    rw [h_re_cube]
    have : α ^ 2 - 3 * β ^ 2 ≤ 0 := by nlinarith [sq_nonneg α, sq_nonneg β]
    exact mul_nonpos_of_nonneg_of_nonpos hα_nn this
  have h_env_ge : 1 ≤ airyEnv u := by
    unfold airyEnv; exact Real.one_le_exp (by linarith)
  have h_im_le : |y| ≤ airyGap n / 4 := by
    have := (Complex.abs_im_le_norm (u - (airyZero n : ℂ))).trans hu
    simpa [y] using this
  have h_sqrt_x : √x ≤ |β| := by
    rw [← Real.sqrt_sq (abs_nonneg β), sq_abs]
    exact Real.sqrt_le_sqrt hβ2
  have h_sqrt_x_pos : 0 < √x := Real.sqrt_pos.mpr (by linarith)
  have h_α_le : α ≤ |y| / (2 * √x) := by
    have h2ab : 2 * α * |β| = |y| := by
      have : |2 * α * β| = |y| := congrArg abs h2
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num), abs_of_nonneg hα_nn] at this
      exact this
    rw [le_div_iff₀ (by positivity)]
    calc α * (2 * √x) ≤ α * (2 * |β|) := by gcongr
      _ = 2 * α * |β| := by ring
      _ = |y| := h2ab
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have h_α_rpow : α ≤ c₂ * (n : ℝ) ^ (-(1 / 3 : ℝ)) / (8 * √x) := by
    calc α ≤ |y| / (2 * √x) := h_α_le
      _ ≤ (airyGap n / 4) / (2 * √x) := by gcongr
      _ ≤ (c₂ * (n : ℝ) ^ (-(1 / 3 : ℝ)) / 4) / (2 * √x) := by gcongr
      _ = c₂ * (n : ℝ) ^ (-(1 / 3 : ℝ)) / (8 * √x) := by ring
  have h_α_sqrt : α * √x ≤ c₂ / 8 * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
    calc α * √x ≤ (c₂ * (n : ℝ) ^ (-(1 / 3 : ℝ)) / (8 * √x)) * √x := by gcongr
      _ = c₂ / 8 * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by field_simp [h_sqrt_x_pos.ne']
  have h_sx_ub : √x ≤ 2 * (n : ℝ) ^ (1 / 3 : ℝ) := by
    have h1' := Real.sqrt_le_sqrt hx_ub
    have h4 : √(4 * (n : ℝ) ^ (2 / 3 : ℝ)) = 2 * (n : ℝ) ^ (1 / 3 : ℝ) := by
      rw [Real.sqrt_mul (by norm_num), show √(4 : ℝ) = 2 by norm_num, Real.sqrt_eq_rpow,
        ← Real.rpow_mul hn_pos.le]
      norm_num
    linarith
  have h_α_ub : α ≤ c₂ / 8 := by
    have h1' : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by norm_num)
    have h2' : 1 ≤ √x := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hx_lb
    calc α ≤ c₂ * (n : ℝ) ^ (-(1 / 3 : ℝ)) / (8 * √x) := h_α_rpow
      _ ≤ c₂ * 1 / (8 * 1) := by gcongr
      _ = c₂ / 8 := by ring
  have h_cube_eq : -(u ^ (3 / 2 : ℂ)).re = 3 * α * x + 2 * α ^ 3 := by
    rw [h_re_cube, show β ^ 2 = x + α ^ 2 by linarith]
    ring
  have h_3ax : 3 * α * x ≤ (3 / 2 : ℝ) * c₂ := by
    have hx_sq : x = √x * √x := (Real.mul_self_sqrt (by linarith)).symm
    have hmul : (n : ℝ) ^ (-(1 / 3 : ℝ)) * (n : ℝ) ^ (1 / 3 : ℝ) = 1 := by
      rw [← Real.rpow_add hn_pos, neg_add_cancel, Real.rpow_zero]
    calc 3 * α * x = 3 * (α * √x) * √x := by (conv_lhs => rw [hx_sq]); ring
      _ ≤ 3 * (c₂ / 8 * (n : ℝ) ^ (-(1 / 3 : ℝ))) * (2 * (n : ℝ) ^ (1 / 3 : ℝ)) := by
          gcongr
      _ = (3 / 4 : ℝ) * c₂ * ((n : ℝ) ^ (-(1 / 3 : ℝ)) * (n : ℝ) ^ (1 / 3 : ℝ)) := by ring
      _ = (3 / 4 : ℝ) * c₂ := by rw [hmul, mul_one]
      _ ≤ (3 / 2 : ℝ) * c₂ := by linarith
  have h_2a3 : 2 * α ^ 3 ≤ 2 * (c₂ / 8) ^ 3 := by
    gcongr
  have h_env_le : airyEnv u ≤ Real.exp (4 / 3 * B) := by
    unfold airyEnv
    refine Real.exp_le_exp.mpr ?_
    have : -(4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re = 4 / 3 * (3 * α * x + 2 * α ^ 3) := by
      rw [← h_cube_eq]; ring
    rw [this]
    dsimp [B]
    linarith
  exact ⟨h_env_ge, h_env_le⟩

lemma gap_disc_disjoint {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) (hkn : k ≠ n) :
    airyGap k / 4 + airyGap n / 4 < |airyZero k - airyZero n| := by
  have h_ordered : ∀ a b : ℕ, 1 ≤ a → a < b →
      airyGap a / 4 + airyGap b / 4 < airyZero a - airyZero b := by
    intro a b ha hab
    have hba : airyZero b ≤ airyZero (a + 1) := by
      rcases eq_or_lt_of_le (by omega : a + 1 ≤ b) with rfl | hlt
      · exact le_rfl
      · exact (airyZero_lt_of_lt (by omega) hlt).le
    have hgap_a : airyGap a ≤ airyZero a - airyZero b := by unfold airyGap; linarith
    rcases ha.eq_or_lt with rfl | ha2
    · have hg1 : airyGap 1 ≤ 251 / 100 := by
        unfold airyGap; linarith [airyZero_one.2, airyZero_two.1]
      have h12 : 165 / 100 ≤ airyGap 1 := by
        unfold airyGap; linarith [airyZero_one.1, airyZero_two.2]
      have hb2 : 2 ≤ b := by omega
      have hgb : airyGap b ≤ (41 / 20 : ℝ) * (2 : ℝ) ^ (-(1 / 3 : ℝ)) := by
        have h1 : airyGap b ≤ (41 / 20 : ℝ) * (b : ℝ) ^ (-(1 / 3 : ℝ)) := by
          unfold airyGap; linarith [(airyZero_gap_bounds hb2).2]
        have hpow : (b : ℝ) ^ (-(1 / 3 : ℝ)) ≤ (2 : ℝ) ^ (-(1 / 3 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hb2) (by norm_num)
        linarith
      have h2pow : (2 : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 4 / 5 := by
        refine le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) (by norm_num) ?_
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
          show -(1 / 3 : ℝ) * ((3 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
        norm_num
      linarith
    · have hga : (9 / 5 : ℝ) * ((a : ℝ) + 1) ^ (-(1 / 3 : ℝ)) ≤ airyGap a := by
        unfold airyGap; linarith [(airyZero_gap_bounds ha2).1]
      have hgb : airyGap b ≤ (41 / 20 : ℝ) * (b : ℝ) ^ (-(1 / 3 : ℝ)) := by
        unfold airyGap; linarith [(airyZero_gap_bounds (by omega : 2 ≤ b)).2]
      have hpow : (b : ℝ) ^ (-(1 / 3 : ℝ)) ≤ ((a : ℝ) + 1) ^ (-(1 / 3 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast (by omega : a + 1 ≤ b)) (by norm_num)
      have hgb' : airyGap b ≤ (41 / 20 : ℝ) * ((a : ℝ) + 1) ^ (-(1 / 3 : ℝ)) := by linarith
      have hgab : airyGap b ≤ (41 / 36 : ℝ) * airyGap a := by linarith
      have hga_pos := airyGap_pos ha
      linarith
  rcases lt_or_gt_of_ne hkn with hlt | hgt
  · rw [abs_of_nonneg (sub_nonneg.mpr (airyZero_lt_of_lt hk hlt).le)]
    exact h_ordered k n hk hlt
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (airyZero_lt_of_lt hn hgt).le), add_comm]
    exact h_ordered n k hn hgt

lemma ratio_prefix_bound_unif (f : ℕ) {U : ℝ} (hU : 0 ≤ U) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∃ C_rat > 0, ∀ uF : ℝ, |uF| ≤ U → ∀ u : ℂ, (∀ k : ℕ, 1 ≤ k → c₀ * airyGap k ≤ ‖u - (airyZero k : ℂ)‖) →
      ‖(u - (uF : ℂ)) / (∏ k ∈ Finset.Icc 1 f, (u - (airyZero k : ℂ)) ^ 2)‖ ≤
        C_rat * (1 + ‖u‖) ^ (1 - 2 * (f : ℝ)) := by
  set M_k : ℕ → ℝ := fun k => 1 + (1 + |airyZero k|) / (c₀ * airyGap k)
  have hM_pos : ∀ k : ℕ, 1 ≤ k → 0 < M_k k := fun k hk => by
    dsimp [M_k]; have := airyGap_pos hk; positivity
  set C_prod : ℝ := ∏ k ∈ Finset.Icc 1 f, M_k k ^ 2
  have hC_prod_pos : 0 < C_prod := Finset.prod_pos fun k hk =>
    pow_pos (hM_pos k (Finset.mem_Icc.mp hk).1) 2
  set C_rat : ℝ := (1 + U) * C_prod
  refine ⟨C_rat, by positivity, fun uF huF u hu => ?_⟩
  have hnum : ‖u - (uF : ℂ)‖ ≤ (1 + U) * (1 + ‖u‖) := by
    have h1 : ‖u - (uF : ℂ)‖ ≤ ‖u‖ + |uF| := by
      have := norm_sub_le u (uF : ℂ)
      rwa [Complex.norm_real, Real.norm_eq_abs] at this
    nlinarith [norm_nonneg u, abs_nonneg uF, huF]
  have hden_term : ∀ k ∈ Finset.Icc 1 f,
      1 + ‖u‖ ≤ M_k k * ‖u - (airyZero k : ℂ)‖ := fun k hk => by
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hgap := hu k hk1
    have hgap_pos : 0 < c₀ * airyGap k := mul_pos hc₀ (airyGap_pos hk1)
    have h1 : 1 + ‖u‖ ≤ ‖u - (airyZero k : ℂ)‖ + (1 + |airyZero k|) := by
      have htri := norm_add_le (u - (airyZero k : ℂ)) (airyZero k : ℂ)
      rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs] at htri
      linarith
    have h2 : 1 + |airyZero k| ≤ ((1 + |airyZero k|) / (c₀ * airyGap k)) * ‖u - (airyZero k : ℂ)‖ := by
      calc 1 + |airyZero k|
          = ((1 + |airyZero k|) / (c₀ * airyGap k)) * (c₀ * airyGap k) :=
            (div_mul_cancel₀ (1 + |airyZero k|) hgap_pos.ne').symm
        _ ≤ ((1 + |airyZero k|) / (c₀ * airyGap k)) * ‖u - (airyZero k : ℂ)‖ := by gcongr
    calc 1 + ‖u‖ ≤ ‖u - (airyZero k : ℂ)‖ + (1 + |airyZero k|) := h1
      _ ≤ ‖u - (airyZero k : ℂ)‖ + ((1 + |airyZero k|) / (c₀ * airyGap k)) * ‖u - (airyZero k : ℂ)‖ := by
          gcongr
      _ = M_k k * ‖u - (airyZero k : ℂ)‖ := by dsimp [M_k]; ring
  have hden_sq : ∀ k ∈ Finset.Icc 1 f,
      (1 + ‖u‖) ^ 2 ≤ M_k k ^ 2 * ‖u - (airyZero k : ℂ)‖ ^ 2 := fun k hk => by
    have h1 := pow_le_pow_left₀ (by positivity) (hden_term k hk) 2
    rwa [mul_pow] at h1
  have hden_prod : (1 + ‖u‖) ^ (2 * f) ≤
      C_prod * ∏ k ∈ Finset.Icc 1 f, ‖u - (airyZero k : ℂ)‖ ^ 2 := by
    have h1 := Finset.prod_le_prod₀ (fun _ _ => by positivity) hden_sq
    have hcard : (Finset.Icc 1 f).card = f := by simp
    rw [Finset.prod_const, hcard, ← pow_mul, Finset.prod_mul_distrib] at h1
    exact h1
  have hden_pos : 0 < ∏ k ∈ Finset.Icc 1 f, ‖u - (airyZero k : ℂ)‖ ^ 2 := by
    refine Finset.prod_pos fun k hk => sq_pos_of_pos ?_
    have hk1 := (Finset.mem_Icc.mp hk).1
    exact lt_of_lt_of_le (mul_pos hc₀ (airyGap_pos hk1)) (hu k hk1)
  have h1u : 0 < 1 + ‖u‖ := by positivity
  rw [norm_div, norm_prod]
  simp_rw [norm_pow]
  calc ‖u - (uF : ℂ)‖ / ∏ k ∈ Finset.Icc 1 f, ‖u - (airyZero k : ℂ)‖ ^ 2
      ≤ ((1 + U) * (1 + ‖u‖)) / ((1 + ‖u‖) ^ (2 * f) / C_prod) := by
        gcongr
        rw [div_le_iff₀ hC_prod_pos]
        linarith
    _ = C_rat * ((1 + ‖u‖) / (1 + ‖u‖) ^ (2 * f)) := by
        dsimp [C_rat]; field_simp [hC_prod_pos.ne']
    _ = C_rat * (1 + ‖u‖) ^ (1 - 2 * (f : ℝ)) := by
        congr 1
        have h2f : (1 + ‖u‖) ^ (2 * f) = (1 + ‖u‖) ^ ((2 * f : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
        rw [h2f]
        conv_lhs => arg 1; rw [← Real.rpow_one (1 + ‖u‖)]
        rw [← Real.rpow_sub h1u]
        push_cast; rfl

/-- **Maximum-principle extension from outside the gap discs.** If an entire `W` satisfies
`‖W u‖ ≤ C_out (1 + ‖u‖)^(-ν) e(u)` for every `u` outside all the discs `B(a_k, gap_k / 4)`, then
it satisfies the same bound everywhere with constant `3^ν C_e C_out`, `C_e` absolute. -/
theorem norm_le_of_gap_disc_extension :
    ∃ C_env : ℝ, 1 ≤ C_env ∧ ∀ {ν : ℝ}, 0 ≤ ν → ∀ {W : ℂ → ℂ}, Differentiable ℂ W →
      ∀ {C_out : ℝ}, 0 ≤ C_out →
      (∀ u : ℂ, (∀ k : ℕ, 1 ≤ k → airyGap k / 4 ≤ ‖u - (airyZero k : ℂ)‖) →
        ‖W u‖ ≤ C_out * (1 + ‖u‖) ^ (-ν) * airyEnv u) →
      ∀ u : ℂ, ‖W u‖ ≤ ((3 : ℝ) ^ ν * C_env * C_out) * (1 + ‖u‖) ^ (-ν) * airyEnv u := by
  obtain ⟨C_env, hC_env, henv_disc⟩ := airyEnv_on_gap_disc_bounds
  have h1e : 1 ≤ C_env := by
    have := henv_disc 1 le_rfl (airyZero 1 : ℂ)
      (by rw [sub_self, norm_zero]; exact div_nonneg (airyGap_pos le_rfl).le (by norm_num))
    linarith [this.1, this.2]
  refine ⟨C_env, h1e, fun {ν} hν {W} hW {C_out} hC_out h_out => ?_⟩
  intro u
  set C := (3 : ℝ) ^ ν * C_env * C_out
  by_cases hu : ∀ k : ℕ, 1 ≤ k → airyGap k / 4 ≤ ‖u - (airyZero k : ℂ)‖
  · refine (h_out u hu).trans ?_
    have h13 : (1 : ℝ) ≤ (3 : ℝ) ^ ν := by
      exact Real.one_le_rpow (by norm_num) hν
    have h1e : 1 ≤ C_env := by
      have := henv_disc 1 le_rfl (airyZero 1 : ℂ)
        (by rw [sub_self, norm_zero]; exact div_nonneg (airyGap_pos le_rfl).le (by norm_num))
      linarith [this.1, this.2]
    have hle : C_out ≤ C := by
      dsimp [C]
      calc C_out = 1 * 1 * C_out := by ring
        _ ≤ (3 : ℝ) ^ ν * C_env * C_out := by gcongr
    gcongr
    exact (airyEnv_pos u).le
  · push Not at hu
    obtain ⟨n, hn, hu_in⟩ := hu
    set r := airyGap n / 4
    have hr_pos : 0 < r := by dsimp [r]; linarith [airyGap_pos hn]
    have hdc : DiffContOnCl ℂ (W) (ball (airyZero n : ℂ) r) :=
      hW.differentiableOn.diffContOnCl
    have hfr_out : ∀ w ∈ frontier (ball (airyZero n : ℂ) r),
        ∀ k : ℕ, 1 ≤ k → airyGap k / 4 ≤ ‖w - (airyZero k : ℂ)‖ := by
      intro w hw k hk
      rw [frontier_ball (airyZero n : ℂ) hr_pos.ne'] at hw
      have hwn : ‖w - (airyZero n : ℂ)‖ = r := mem_sphere_iff_norm.mp hw
      by_cases hkn : k = n
      · subst hkn; exact hwn.ge
      · have hdisj := gap_disc_disjoint hk hn hkn
        have h_ak : ‖(airyZero k : ℂ) - (airyZero n : ℂ)‖ ≤ ‖w - (airyZero k : ℂ)‖ + ‖w - (airyZero n : ℂ)‖ := by
          have := norm_add_le ((airyZero k : ℂ) - w) (w - (airyZero n : ℂ))
          rw [sub_add_sub_cancel, norm_sub_rev (airyZero k : ℂ) w] at this
          exact this
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hwn] at h_ak
        dsimp [r] at h_ak
        linarith
    have hgap_le_4 : airyGap n ≤ 4 := by
      rcases hn.eq_or_lt with rfl | hn2
      · unfold airyGap; linarith [airyZero_one.2, airyZero_two.1]
      · have hg : airyGap n ≤ (41 / 20 : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
          unfold airyGap; linarith [(airyZero_gap_bounds hn2).2]
        have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
        have hpow : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
        linarith
    have hbd_fr : ∀ w ∈ frontier (ball (airyZero n : ℂ) r),
        ‖W w‖ ≤ C * (1 + ‖u‖) ^ (-(ν)) * airyEnv u := by
      intro w hw
      have h_w_out := h_out w (hfr_out w hw)
      rw [frontier_ball (airyZero n : ℂ) hr_pos.ne'] at hw
      have hwn : ‖w - (airyZero n : ℂ)‖ = r := mem_sphere_iff_norm.mp hw
      have henv_w := (henv_disc n hn w hwn.le).2
      have henv_u := (henv_disc n hn u hu_in.le).1
      have hnorm_uw : 1 + ‖u‖ ≤ 3 * (1 + ‖w‖) := by
        have h1 : ‖u - w‖ ≤ ‖u - (airyZero n : ℂ)‖ + ‖w - (airyZero n : ℂ)‖ := by
          have := norm_sub_le (u - (airyZero n : ℂ)) (w - (airyZero n : ℂ))
          simpa [sub_sub_sub_cancel_right] using this
        have h2 : ‖u‖ ≤ ‖w‖ + ‖u - w‖ := by
          have := norm_add_le w (u - w)
          simpa [add_sub_cancel] using this
        have h_r2 : 2 * r ≤ 2 := by dsimp [r]; linarith
        linarith [norm_nonneg w]
      have hrpow_le : (1 + ‖w‖) ^ (-(ν)) ≤
          (3 : ℝ) ^ ν * (1 + ‖u‖) ^ (-(ν)) := by
        have h1w : 0 < 1 + ‖w‖ := by positivity
        have h1u : 0 < 1 + ‖u‖ := by positivity
        have hpow := Real.rpow_le_rpow_of_nonpos h1u hnorm_uw (neg_nonpos.mpr hν)
        rw [Real.mul_rpow (by norm_num) h1w.le, Real.rpow_neg (by norm_num)] at hpow
        have h3pos : 0 < (3 : ℝ) ^ ν := by positivity
        calc (1 + ‖w‖) ^ (-(ν))
            = (3 : ℝ) ^ ν *
                (((3 : ℝ) ^ ν)⁻¹ * (1 + ‖w‖) ^ (-(ν))) := by
              field_simp [h3pos.ne']
          _ ≤ (3 : ℝ) ^ ν * (1 + ‖u‖) ^ (-(ν)) := by
              gcongr
      calc ‖W w‖
          ≤ C_out * (1 + ‖w‖) ^ (-(ν)) * airyEnv w := h_w_out
        _ ≤ C_out * ((3 : ℝ) ^ ν * (1 + ‖u‖) ^ (-(ν))) *
              (C_env * airyEnv u) := by
            have henv_w_nn : 0 ≤ airyEnv w := (airyEnv_pos w).le
            have henv_le_mul : airyEnv w ≤ C_env * airyEnv u := by
              calc airyEnv w ≤ C_env := henv_w
                _ = C_env * 1 := (mul_one C_env).symm
                _ ≤ C_env * airyEnv u := mul_le_mul_of_nonneg_left henv_u hC_env.le
            gcongr
        _ = C * (1 + ‖u‖) ^ (-(ν)) * airyEnv u := by dsimp [C]; ring
    exact Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc hbd_fr
      (subset_closure (mem_ball_iff_norm.mpr hu_in))

end FormalResearch.ModularBootstrap.Upper.Ramped
