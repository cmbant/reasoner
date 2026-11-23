module

public import FormalResearch.ModularBootstrap.Upper.Comb.ZeroLaw
public import FormalResearch.ModularBootstrap.Upper.Window.Product

/-!
# Finite perturbations of the reference comb: Lemma `P`

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, §0 (designs) and §1, Lemma `P`
(`ut:P`, (b)).

A *finite modification* of the index-`f` reference comb `refComb c' f η₀` (`Upper.Comb.ZeroLaw`)
is described by the data `σ ε : ℕ → ℝ`: a simple zero at `χ'_f = ξ_* + λ σ_f`, conjugate pairs
`χ'_k ± i ε'_k` at `χ'_k = ξ_* + λ σ_k` for `f < k ≤ N`, and the reference pairs
`χ_k ± i η₀ ℓ_k` for `k > N` (`designComb`).

* `designComb`, `combTail`, `pairT`: the modified comb and its unmodified tail.
* `refComb_eq_split`: the reference comb is the same product with the reference data in the
  first `N - f` places.
* `lemma_P_b` (`ut:P`(b)): for a compact family (`|σ_k| ≤ M`, `0 ≤ ε'_k ≤ M λ`), uniformly in the
  family and in `η₀ ∈ [0, 1/4]`, for large `c'` and every real `x ≥ ξ_* + 4 max(Φ_{N+2}, M) λ`,
  `|log(|B_D(x)| / |B_ref(x)|)| ≤ C λ / (x - ξ_*)`, with `C` depending only on `(N, M)`.

* `lemma_P_a_fixedN` (`ut:P`(a), fixed `N`): the `f = 1` design `D(N, η_*, d)` (`designSigma1`,
  `designWidth1`) is a member of such a family, with `M` any bound for the finitely many offsets
  `(|a_1| + d)/κ`, `s_2, …, s_N`, and gives `|log(|B_D|/|B_ref|)| ≤ C(N, η_*, d) λ/(x - ξ_*)` on
  `x ≥ ξ_* + 4 max(Φ_{N+2}, M) λ`.

The statement `ut:P`(a) with the explicit `N`-dependence `(1 + λ N^{7/3})` for growing `N` needs the
Airy-zero asymptotics (Lemma `Z`) and is not formalised here.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Design

open FormalResearch.ModularBootstrap.Upper.Comb

/-! ### 1. The modified comb -/

/-- The conjugate-pair factor `T_{χ+iε}(b) T_{χ-iε}(b)`. -/
noncomputable def pairT (χ ε : ℝ) (b : ℂ) : ℂ :=
  blaschkeT ((χ : ℂ) + (ε : ℂ) * Complex.I) b * blaschkeT ((χ : ℂ) - (ε : ℂ) * Complex.I) b

/-- The unmodified tail `∏_{k > N} T_{χ_k + iη₀ℓ_k} T_{χ_k - iη₀ℓ_k}` of the reference comb. -/
noncomputable def combTail (c' : ℝ) (N : ℕ) (η₀ : ℝ) (b : ℂ) : ℂ :=
  ∏' m : ℕ, pairT (chiQuantile c' (N + 1 + m : ℕ)) (η₀ * siteGap c' (N + 1 + m)) b

/-- The modified site `χ'_k = ξ_* + λ σ_k`. -/
noncomputable def designSite (c' : ℝ) (σ : ℕ → ℝ) (k : ℕ) : ℝ := xiStar + lambdaComb c' * σ k

/-- The finite modification `B_D^{(f)}` of the index-`f` reference comb: a simple zero at
`χ'_f`, pairs `χ'_k ± iε'_k` for `f < k ≤ N`, reference pairs for `k > N`. -/
noncomputable def designComb (c' : ℝ) (f N : ℕ) (η₀ : ℝ) (σ ε : ℕ → ℝ) (b : ℂ) : ℂ :=
  blaschkeT (designSite c' σ f : ℂ) b *
    (∏ i ∈ Finset.range (N - f), pairT (designSite c' σ (f + 1 + i)) (ε (f + 1 + i)) b) *
    combTail c' N η₀ b

/-- The reference comb as the same finite product times the same tail, with the threshold in `c'`
independent of the cut `N`. -/
theorem refComb_eq_split_unif (f : ℕ) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ N : ℕ, f ≤ N → ∀ {b : ℂ}, |b.im| < 7 / 8 →
      refComb c' f η₀ b =
        blaschkeT (chiQuantile c' f : ℂ) b *
          (∏ i ∈ Finset.range (N - f),
            pairT (chiQuantile c' (f + 1 + i : ℕ)) (η₀ * siteGap c' (f + 1 + i)) b) *
          combTail c' N η₀ b := by
  obtain ⟨_, _, h_ev⟩ := siteGap_eventually_le
  filter_upwards [eventually_gt_atTop 0, h_ev] with c' hc' ⟨hgap_k, _, _, hgap_1⟩ N hfN b hb
  have ha : ∀ k : ℕ, 1 ≤ k → (1 / 4 : ℝ) ≤ (k : ℝ) := fun k hk => by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hgap_nn : ∀ k : ℕ, 1 ≤ k → 0 ≤ siteGap c' k := fun k hk => by
    unfold siteGap
    exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn (ha k hk)
      ((ha k hk).trans (by linarith)) (by linarith))
  have hε_bd : ∀ m : ℕ, |η₀ * siteGap c' (N + 1 + m)| ≤ 1 / 8 := fun m => by
    rw [abs_of_nonneg (mul_nonneg hη₀0 (hgap_nn _ (by omega)))]
    have hgk := (hgap_k (N + 1 + m) (by omega)).trans hgap_1
    calc η₀ * siteGap c' (N + 1 + m) ≤ (1 / 4) * (1 / 2) :=
          mul_le_mul hη₀1 hgk (hgap_nn _ (by omega)) (by norm_num)
      _ = 1 / 8 := by norm_num
  have hχ_nn : ∀ m : ℕ, 0 ≤ chiQuantile c' (N + 1 + m : ℕ) := fun m =>
    xiStar_pos.le.trans (chiQuantile_spec hc' (ha _ (by omega))).1
  have hε_bd0 : ∀ m : ℕ, |η₀ * siteGap c' (f + 1 + m)| ≤ 1 / 8 := fun m => by
    rw [abs_of_nonneg (mul_nonneg hη₀0 (hgap_nn _ (by omega)))]
    have hgk := (hgap_k (f + 1 + m) (by omega)).trans hgap_1
    calc η₀ * siteGap c' (f + 1 + m) ≤ (1 / 4) * (1 / 2) :=
          mul_le_mul hη₀1 hgk (hgap_nn _ (by omega)) (by norm_num)
      _ = 1 / 8 := by norm_num
  have hχ_nn0 : ∀ m : ℕ, 0 ≤ chiQuantile c' (f + 1 + m : ℕ) := fun m =>
    xiStar_pos.le.trans (chiQuantile_spec hc' (ha _ (by omega))).1
  have hfull := (comb_pairProd_hasProdLocallyUniformlyOn
    (fun m : ℕ => chiQuantile c' (f + 1 + m : ℕ)) (fun m : ℕ => η₀ * siteGap c' (f + 1 + m))
    hχ_nn0 hε_bd0 (summable_exp_neg_pi_chiQuantile hc' f)).hasProd hb
  have htail := (comb_pairProd_hasProdLocallyUniformlyOn
    (fun m : ℕ => chiQuantile c' (N + 1 + m : ℕ)) (fun m : ℕ => η₀ * siteGap c' (N + 1 + m))
    hχ_nn hε_bd (summable_exp_neg_pi_chiQuantile hc' N)).hasProd hb
  set g : ℕ → ℂ := fun m => pairT (chiQuantile c' (f + 1 + m : ℕ)) (η₀ * siteGap c' (f + 1 + m)) b
    with hg
  have hshift : (fun n : ℕ => g (n + (N - f))) =
      fun n : ℕ => pairT (chiQuantile c' (N + 1 + n : ℕ)) (η₀ * siteGap c' (N + 1 + n)) b := by
    funext n
    simp only [hg]
    have : f + 1 + (n + (N - f)) = N + 1 + n := by omega
    rw [this]
  have hmul : Multipliable (fun n : ℕ => g (n + (N - f))) := by
    rw [hshift]; exact htail.multipliable
  have hsplit := hmul.prod_mul_tprod_nat_mul'
  have hfull_eq : ∏' m, g m = ∏' m : ℕ, (blaschkeT ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) +
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b *
      blaschkeT ((chiQuantile c' (f + 1 + m : ℕ) : ℂ) -
        ((η₀ * siteGap c' (f + 1 + m) : ℝ) : ℂ) * Complex.I) b) := rfl
  unfold refComb combTail
  rw [← hfull_eq, ← hsplit, hshift, mul_assoc]

/-- The reference comb as the same finite product times the same tail. -/
theorem refComb_eq_split (f N : ℕ) (hfN : f ≤ N) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ {b : ℂ}, |b.im| < 7 / 8 →
      refComb c' f η₀ b =
        blaschkeT (chiQuantile c' f : ℂ) b *
          (∏ i ∈ Finset.range (N - f),
            pairT (chiQuantile c' (f + 1 + i : ℕ)) (η₀ * siteGap c' (f + 1 + i)) b) *
          combTail c' N η₀ b :=
  (refComb_eq_split_unif f hη₀0 hη₀1).mono fun _ h => h N hfN


/-! ### 2. Real-axis logarithms -/

lemma norm_pairT_ofReal (χ ε x : ℝ) : ‖pairT χ ε (x : ℂ)‖ = blaschkePairQ χ ε x := rfl

lemma norm_blaschkeT_ofReal (y x : ℝ) :
    ‖blaschkeT (y : ℂ) (x : ℂ)‖ =
      |Real.tanh (π * (x - y) / 2) * Real.tanh (π * (x + y) / 2)| := by
  unfold blaschkeT
  have h1 : Complex.tanh ((π : ℂ) * ((x : ℂ) - (y : ℂ)) / 2) =
      ((Real.tanh (π * (x - y) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tanh]; congr 1; push_cast; ring
  have h2 : Complex.tanh ((π : ℂ) * ((x : ℂ) + (y : ℂ)) / 2) =
      ((Real.tanh (π * (x + y) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tanh]; congr 1; push_cast; ring
  rw [h1, h2, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs]

lemma tanh_prod_ne_zero {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≠ y) :
    Real.tanh (π * (x - y) / 2) * Real.tanh (π * (x + y) / 2) ≠ 0 := by
  have hpi := Real.pi_pos
  have hne : ∀ z : ℝ, z ≠ 0 → Real.tanh (π * z / 2) ≠ 0 := fun z hz => by
    rw [Real.tanh_eq_sinh_div_cosh, div_ne_zero_iff]
    exact ⟨Real.sinh_ne_zero.mpr (by positivity), (Real.cosh_pos _).ne'⟩
  have hsum : x + y ≠ 0 := by
    rcases eq_or_lt_of_le hx with h | h
    · rw [← h] at hxy ⊢; simpa using (Ne.symm hxy)
    · linarith
  exact mul_ne_zero (hne _ (sub_ne_zero.mpr hxy)) (hne _ hsum)

lemma norm_blaschkeT_ofReal_pos {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≠ y) :
    0 < ‖blaschkeT (y : ℂ) (x : ℂ)‖ := by
  rw [norm_blaschkeT_ofReal]
  exact abs_pos.mpr (tanh_prod_ne_zero hx hy hxy)

lemma blaschkePairQ_pos {χ ε x : ℝ} (hχ : 0 ≤ χ) (hx : 0 ≤ x) (hxχ : x ≠ χ) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 2) : 0 < blaschkePairQ χ ε x := by
  have h := blaschkePairQ_ge_sq χ ε x hε0 hε
  exact lt_of_lt_of_le (by have := tanh_prod_ne_zero hx hχ hxχ; positivity) h

/-- `log q = 2 f_x(χ) + δ` for the pair modulus. -/
lemma log_blaschkePairQ {χ ε x : ℝ} (hχ : 0 ≤ χ) (hx : 0 ≤ x) (hxχ : x ≠ χ) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 2) :
    Real.log (blaschkePairQ χ ε x) = 2 * realLogT x χ + deltaDetune χ ε x := by
  have hq := blaschkePairQ_pos hχ hx hxχ hε0 hε
  have ht := tanh_prod_ne_zero hx hχ hxχ
  unfold deltaDetune realLogT
  rw [norm_blaschkeT_ofReal, Real.log_div hq.ne' (pow_ne_zero 2 ht), Real.log_pow, Real.log_abs]
  push_cast
  ring

/-- Mean-value bound for `y ↦ f_x(y) = log |T_y(x)|` away from `y = x`. -/
lemma abs_realLogT_sub_le {x y y' m : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hy' : 0 ≤ y')
    (hym : y ≤ m) (hy'm : y' ≤ m) (hmx : m < x) :
    |realLogT x y' - realLogT x y| ≤ |y' - y| / (x - m) := by
  have hxm : 0 < x - m := sub_pos.mpr hmx
  have hs : Convex ℝ (Set.uIcc y y') := convex_uIcc y y'
  have hmem : ∀ t ∈ Set.uIcc y y', 0 ≤ t ∧ t ≤ m := fun t ht => by
    rw [Set.mem_uIcc] at ht
    rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hy.trans h1, h2.trans hy'm⟩
    · exact ⟨hy'.trans h1, h2.trans hym⟩
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => realLogT x t) (f' := fun t => realLogTDeriv x t) (C := 1 / (x - m))
    (s := Set.uIcc y y') (x := y) (y := y')
    (fun t ht => (realLogT_hasDerivAt hx (hmem t ht).1
      (ne_of_lt (lt_of_le_of_lt (hmem t ht).2 hmx))).1.hasDerivWithinAt)
    (fun t ht => by
      have hlt : t < x := lt_of_le_of_lt (hmem t ht).2 hmx
      have hb := (realLogT_deriv_bounds hx (hmem t ht).1 (ne_of_lt hlt)).2.1 hlt
      rw [Real.norm_eq_abs]
      exact hb.2.2.le.trans (one_div_le_one_div_of_le hxm (by linarith [(hmem t ht).2])))
    hs Set.left_mem_uIcc Set.right_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at key
  calc |realLogT x y' - realLogT x y| ≤ 1 / (x - m) * |y' - y| := key
    _ = |y' - y| / (x - m) := by ring

/-- Splitting `log (D / R)` for products with a common factor `t`. -/
lemma abs_log_ratio_le (n : ℕ) (a' a0 t : ℝ) (q' q0 : ℕ → ℝ) (ha' : 0 < a') (ha0 : 0 < a0)
    (hq' : ∀ i ∈ Finset.range n, 0 < q' i) (hq0 : ∀ i ∈ Finset.range n, 0 < q0 i) (B : ℝ) (hB : 0 ≤ B)
    (h : |Real.log a' - Real.log a0| +
      ∑ i ∈ Finset.range n, |Real.log (q' i) - Real.log (q0 i)| ≤ B) :
    |Real.log (((a' * ∏ i ∈ Finset.range n, q' i) * t) /
      ((a0 * ∏ i ∈ Finset.range n, q0 i) * t))| ≤ B := by
  by_cases ht : t = 0
  · simp [ht, hB]
  · have hP' : 0 < ∏ i ∈ Finset.range n, q' i := Finset.prod_pos hq'
    have hP0 : 0 < ∏ i ∈ Finset.range n, q0 i := Finset.prod_pos hq0
    rw [mul_div_mul_right _ _ ht, Real.log_div (mul_pos ha' hP').ne' (mul_pos ha0 hP0).ne',
      Real.log_mul ha'.ne' hP'.ne', Real.log_mul ha0.ne' hP0.ne',
      Real.log_prod (fun i hi => (hq' i hi).ne'), Real.log_prod (fun i hi => (hq0 i hi).ne')]
    have hsum : |∑ i ∈ Finset.range n, Real.log (q' i) - ∑ i ∈ Finset.range n, Real.log (q0 i)| ≤
        ∑ i ∈ Finset.range n, |Real.log (q' i) - Real.log (q0 i)| := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.abs_sum_le_sum_abs _ _
    calc _ = |(Real.log a' - Real.log a0) +
          (∑ i ∈ Finset.range n, Real.log (q' i) - ∑ i ∈ Finset.range n, Real.log (q0 i))| := by
            congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (by linarith)

/-- Detuning bound in the form used below. -/
lemma deltaDetune_le_aux {χ ε x X m e : ℝ} (hχ : 0 ≤ χ) (hx : 0 ≤ x) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 8) (hεe : ε ≤ e) (hχm : χ ≤ m) (hmx : x - m = 3 * X / 4) (hX : 0 < X) :
    deltaDetune χ ε x ≤ (80 / 9) * e ^ 2 / X ^ 2 := by
  have hxχ : x ≠ χ := by intro h; rw [h] at hmx; linarith
  have hb := (deltaDetune_bounds_universal hχ hx hxχ hε0 hε1).2
  have hd : 3 * X / 4 ≤ x - χ := by linarith
  have hd0 : 0 < 3 * X / 4 := by positivity
  calc deltaDetune χ ε x ≤ 5 * ε ^ 2 / (x - χ) ^ 2 := hb
    _ ≤ 5 * e ^ 2 / (3 * X / 4) ^ 2 := by
        apply div_le_div₀ (by positivity) (by gcongr) (by positivity) (by gcongr)
    _ = (80 / 9) * e ^ 2 / X ^ 2 := by field_simp; ring

/-- Displacement of a simple zero: `|f_x(χ) - f_x(χ₀)| ≤ D / (x - m)`. -/
lemma abs_realLogT_sub_le_of_dist {χ χ₀ x m D : ℝ} (hχ : 0 ≤ χ) (hχ₀ : 0 ≤ χ₀) (hx : 0 ≤ x)
    (hχm : χ ≤ m) (hχ₀m : χ₀ ≤ m) (hmx : m < x) (hD : |χ - χ₀| ≤ D) :
    |realLogT x χ - realLogT x χ₀| ≤ D / (x - m) :=
  (abs_realLogT_sub_le hx hχ₀ hχ hχ₀m hχm hmx).trans
    (div_le_div_of_nonneg_right hD (sub_pos.mpr hmx).le)

/-- Displacement and widening of a conjugate pair: the change of `log q` is bounded by the
displacement `D` over the distance and the two detuning terms. -/
lemma abs_log_pairQ_sub_le {χ χ₀ ε ε₀ x X m e e₀ D : ℝ} (hχ : 0 ≤ χ) (hχ₀ : 0 ≤ χ₀) (hx : 0 ≤ x)
    (hχm : χ ≤ m) (hχ₀m : χ₀ ≤ m) (hmx : x - m = 3 * X / 4) (hX : 0 < X)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 8) (hεe : ε ≤ e) (hε₀0 : 0 ≤ ε₀) (hε₀1 : ε₀ ≤ 1 / 8)
    (hε₀e : ε₀ ≤ e₀) (hD : |χ - χ₀| ≤ D) :
    |Real.log (blaschkePairQ χ ε x) - Real.log (blaschkePairQ χ₀ ε₀ x)| ≤
      2 * (D / (3 * X / 4)) + ((80 / 9) * e ^ 2 / X ^ 2 + (80 / 9) * e₀ ^ 2 / X ^ 2) := by
  have hxχ : x ≠ χ := by intro h; rw [h] at hmx; linarith
  have hxχ₀ : x ≠ χ₀ := by intro h; rw [h] at hmx; linarith
  have hl1 := log_blaschkePairQ hχ hx hxχ hε0 (by linarith)
  have hl0 := log_blaschkePairQ hχ₀ hx hxχ₀ hε₀0 (by linarith)
  have hd1 := deltaDetune_le_aux hχ hx hε0 hε1 hεe hχm hmx hX
  have hd0 := deltaDetune_le_aux hχ₀ hx hε₀0 hε₀1 hε₀e hχ₀m hmx hX
  have hn1 := (deltaDetune_bounds_universal hχ hx hxχ hε0 hε1).1
  have hn0 := (deltaDetune_bounds_universal hχ₀ hx hxχ₀ hε₀0 hε₀1).1
  have hFF := abs_realLogT_sub_le_of_dist hχ hχ₀ hx hχm hχ₀m (by linarith) hD
  rw [hmx] at hFF
  rw [hl1, hl0]
  rw [abs_le] at hFF ⊢
  constructor <;> nlinarith [hFF.1, hFF.2]

/-- Reference sites `χ_k` with `1 ≤ k ≤ N` lie in `[ξ_*, ξ_* + λ Φ_{N+2}]`. -/
lemma refSite_bounds {c' : ℝ} (hc' : 0 < c') {k N : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    xiStar ≤ chiQuantile c' (k : ℝ) ∧
      chiQuantile c' (k : ℝ) ≤ xiStar + lambdaComb c' * phiQuantile ((N : ℝ) + 2) := by
  have hk14 : (1 / 4 : ℝ) ≤ (k : ℝ) := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  refine ⟨(chiQuantile_spec hc' hk14).1, ?_⟩
  have hb := (siteRadius_bounds hc' hk14).2
  unfold siteRadius at hb
  have hΦ : phiQuantile (k : ℝ) ≤ phiQuantile ((N : ℝ) + 2) := by
    unfold phiQuantile
    apply Real.rpow_le_rpow (by linarith) _ (by norm_num)
    have : (k : ℝ) ≤ N := by exact_mod_cast hkN
    linarith
  have hlam : 0 ≤ lambdaComb c' := (Real.rpow_pos_of_pos (mul_pos kTip_pos hc') _).le
  have : lambdaComb c' * phiQuantile (k : ℝ) ≤ lambdaComb c' * phiQuantile ((N : ℝ) + 2) := by
    gcongr
  linarith

/-- Modified sites with `|σ_k| ≤ M ≤ s` lie in `[0, ξ_* + λ s]` when `λ M ≤ ξ_*`. -/
lemma designSite_bounds {c' : ℝ} {σ : ℕ → ℝ} {k : ℕ} {M s : ℝ} (hlam : 0 ≤ lambdaComb c')
    (hσ : |σ k| ≤ M) (hMs : M ≤ s) (hMl : lambdaComb c' * M ≤ xiStar) :
    0 ≤ designSite c' σ k ∧ designSite c' σ k ≤ xiStar + lambdaComb c' * s := by
  have hσk := abs_le.mp hσ
  unfold designSite
  constructor
  · nlinarith [hσk.1, hσk.2, mul_nonneg hlam (sub_nonneg.mpr hMs)]
  · have : lambdaComb c' * σ k ≤ lambdaComb c' * s := by gcongr; linarith [hσk.2]
    linarith

/-- Distance between a modified and a reference site. -/
lemma designSite_dist_le {c' : ℝ} (hc' : 0 < c') {σ : ℕ → ℝ} {k N : ℕ} {M s : ℝ} (hk : 1 ≤ k)
    (hkN : k ≤ N) (hσ : |σ k| ≤ M) (hMs : M ≤ s) (hΦs : phiQuantile ((N : ℝ) + 2) ≤ s) :
    |designSite c' σ k - chiQuantile c' (k : ℝ)| ≤ 2 * s * lambdaComb c' := by
  have hlam : 0 ≤ lambdaComb c' := (Real.rpow_pos_of_pos (mul_pos kTip_pos hc') _).le
  have h0 := refSite_bounds hc' hk hkN
  have hσk := abs_le.mp hσ
  unfold designSite
  rw [abs_le]
  have h1 : lambdaComb c' * σ k ≤ lambdaComb c' * s := by gcongr; linarith [hσk.2]
  have h2 : lambdaComb c' * (-s) ≤ lambdaComb c' * σ k := by gcongr; linarith [hσk.1]
  have h3 : lambdaComb c' * phiQuantile ((N : ℝ) + 2) ≤ lambdaComb c' * s := by gcongr
  constructor <;> nlinarith [h0.1, h0.2]

/-- Arithmetic of the displacement of a simple zero. -/
lemma first_arith {s lam X : ℝ} (hX : 0 < X) :
    (2 * s * lam) / (3 * X / 4) = (8 * s / 3) * (lam / X) := by
  field_simp; ring

/-- Arithmetic of the displacement and widening of a pair, with `u = λ / X ≤ 1 / (4 s)`. -/
lemma pair_arith {s lam X E Cg : ℝ} (hs : 0 < s) (hlam : 0 < lam) (hXs : 4 * s * lam ≤ X) :
    2 * ((2 * s * lam) / (3 * X / 4)) +
        ((80 / 9) * (E * lam) ^ 2 / X ^ 2 + (80 / 9) * (Cg / 4 * lam) ^ 2 / X ^ 2) ≤
      (16 * s / 3 + (20 / 9) * (E ^ 2 + (Cg / 4) ^ 2) / s) * (lam / X) := by
  have hX : 0 < X := lt_of_lt_of_le (by positivity) hXs
  have hu0 : 0 < lam / X := by positivity
  have hu_le : lam / X ≤ 1 / (4 * s) := by
    rw [div_le_div_iff₀ hX (by positivity)]
    nlinarith
  have e1 : (80 / 9 : ℝ) * (E * lam) ^ 2 / X ^ 2 + (80 / 9) * (Cg / 4 * lam) ^ 2 / X ^ 2 =
      (80 / 9) * (E ^ 2 + (Cg / 4) ^ 2) * (lam / X) ^ 2 := by
    field_simp
  have e2 : 2 * ((2 * s * lam) / (3 * X / 4)) = (16 * s / 3) * (lam / X) := by
    field_simp; ring
  have hu3 : (80 / 9 : ℝ) * (E ^ 2 + (Cg / 4) ^ 2) * (lam / X) ^ 2 ≤
      (20 / 9) * (E ^ 2 + (Cg / 4) ^ 2) / s * (lam / X) := by
    have hu2 : (lam / X) ^ 2 ≤ (lam / X) / (4 * s) := by
      rw [sq, le_div_iff₀ (by positivity)]
      have h4 : lam / X * (4 * s) ≤ 1 := by
        rw [le_div_iff₀ (by positivity)] at hu_le
        linarith
      calc lam / X * (lam / X) * (4 * s) = lam / X * (lam / X * (4 * s)) := by ring
        _ ≤ lam / X * 1 := mul_le_mul_of_nonneg_left h4 hu0.le
        _ = lam / X := mul_one _
    calc (80 / 9 : ℝ) * (E ^ 2 + (Cg / 4) ^ 2) * (lam / X) ^ 2
        ≤ (80 / 9 : ℝ) * (E ^ 2 + (Cg / 4) ^ 2) * ((lam / X) / (4 * s)) := by gcongr
      _ = (20 / 9) * (E ^ 2 + (Cg / 4) ^ 2) / s * (lam / X) := by field_simp; ring
  rw [e1, e2]
  nlinarith [hu3]

/-- **Lemma `P`(b)** (`ut:P`, compact-family version). Fix `f ≥ 1`, `N ≥ f` and `M E ≥ 0`.  There is
`C = C(N, M, E) ≥ 0` such that for every `η₀ ∈ [0, 1/4]`, for `c'` large, for every finite
modification `B_D^{(f)}` with `|σ_k| ≤ M` (`f ≤ k ≤ N`) and `0 ≤ ε'_k ≤ E λ` (`f < k ≤ N`),
uniformly in the family, and for every real `x ≥ ξ_* + R λ` with `R = 4 max(Φ_{N+2}, M)`,
`|log(|B_D^{(f)}(x)| / |B_ref^{(f)}(x)|)| ≤ C λ / (x - ξ_*)`.  The paper's single bound `M` for the
offsets and the widths is the case `E = M`; the radius `R` involves the offsets only. -/
theorem lemma_P_b (f N : ℕ) (hf : 1 ≤ f) (hfN : f ≤ N) (M E : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {η₀ : ℝ}, 0 ≤ η₀ → η₀ ≤ 1 / 4 →
      ∀ᶠ c' in atTop, ∀ σ ε : ℕ → ℝ, (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) →
        (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
        ∀ x : ℝ, xiStar + 4 * max (phiQuantile ((N : ℝ) + 2)) M * lambdaComb c' ≤ x →
          |Real.log (‖designComb c' f N η₀ σ ε (x : ℂ)‖ / ‖refComb c' f η₀ (x : ℂ)‖)| ≤
            C * (lambdaComb c' / (x - xiStar)) := by
  obtain ⟨Cg, hCg, h_ev⟩ := siteGap_eventually_le
  set s : ℝ := max (phiQuantile ((N : ℝ) + 2)) M with hs_def
  have hΦpos : 0 < phiQuantile ((N : ℝ) + 2) := by
    unfold phiQuantile
    apply Real.rpow_pos_of_pos
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hs : 0 < s := lt_of_lt_of_le hΦpos (le_max_left _ _)
  have hMs : M ≤ s := le_max_right _ _
  have hΦs : phiQuantile ((N : ℝ) + 2) ≤ s := le_max_left _ _
  set P : ℝ := 16 * s / 3 + (20 / 9) * (E ^ 2 + (Cg / 4) ^ 2) / s with hP_def
  have hP0 : 0 ≤ P := by positivity
  refine ⟨8 * s / 3 + ((N - f : ℕ) : ℝ) * P, by positivity, ?_⟩
  intro η₀ hη₀0 hη₀1
  have hsplit := refComb_eq_split f N hfN hη₀0 hη₀1
  have hlam_ev : ∀ᶠ c' in atTop, M * lambdaComb c' ≤ xiStar ∧ E * lambdaComb c' ≤ 1 / 8 ∧
      Cg * lambdaComb c' ≤ 1 / 2 := by
    have h1 := tendsto_lambdaComb_atTop.const_mul M
    have h2 := tendsto_lambdaComb_atTop.const_mul Cg
    have h3 := tendsto_lambdaComb_atTop.const_mul E
    simp only [mul_zero] at h1 h2 h3
    exact (h1.eventually_le_const xiStar_pos).and
      ((h3.eventually_le_const (by norm_num)).and (h2.eventually_le_const (by norm_num)))
  filter_upwards [hsplit, h_ev, eventually_gt_atTop 0, hlam_ev] with c' hsp
    ⟨hgap_k, hgap_1_bd, hcd1_bd, hgap_1⟩ hc' ⟨hMlam, hElam, hCglam⟩ σ ε hσ hε x hx
  have hlam : 0 < lambdaComb c' := Real.rpow_pos_of_pos (mul_pos kTip_pos hc') _
  have hX : 0 < x - xiStar := lt_of_lt_of_le (by positivity) (by linarith : 4 * s * lambdaComb c' ≤ x - xiStar)
  have hXs : 4 * s * lambdaComb c' ≤ x - xiStar := by linarith
  have hxpos : 0 ≤ x := by have := xiStar_pos; linarith
  have hMl1 : lambdaComb c' * M ≤ xiStar := by linarith [mul_comm M (lambdaComb c')]
  set m : ℝ := xiStar + (x - xiStar) / 4 with hm_def
  have hxm : x - m = 3 * (x - xiStar) / 4 := by rw [hm_def]; ring
  have hsl : s * lambdaComb c' ≤ (x - xiStar) / 4 := by linarith
  have hx_ne : ∀ y : ℝ, y ≤ m → x ≠ y := fun y hy h => by rw [h] at hxm; linarith
  have hY0 : ∀ k : ℕ, 1 ≤ k → k ≤ N → xiStar ≤ chiQuantile c' (k : ℝ) ∧
      chiQuantile c' (k : ℝ) ≤ m := fun k hk hkN => by
    have h := refSite_bounds hc' hk hkN
    have : lambdaComb c' * phiQuantile ((N : ℝ) + 2) ≤ lambdaComb c' * s := by gcongr
    exact ⟨h.1, by rw [hm_def]; nlinarith [h.2]⟩
  have hY' : ∀ k : ℕ, f ≤ k → k ≤ N → 0 ≤ designSite c' σ k ∧ designSite c' σ k ≤ m :=
    fun k hk hkN => by
    have h := designSite_bounds hlam.le (hσ k hk hkN) hMs hMl1
    exact ⟨h.1, by rw [hm_def]; nlinarith [h.2]⟩
  have hεgap : ∀ i : ℕ, 0 ≤ η₀ * siteGap c' (f + 1 + i) ∧
      η₀ * siteGap c' (f + 1 + i) ≤ Cg / 4 * lambdaComb c' := fun i => by
    have hga : 0 ≤ siteGap c' (f + 1 + i) := by
      unfold siteGap
      have ha : (1 / 4 : ℝ) ≤ ((f + 1 + i : ℕ) : ℝ) := by
        have : (1 : ℝ) ≤ ((f + 1 + i : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ f + 1 + i)
        linarith
      exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn ha
        (ha.trans (by linarith)) (by linarith))
    refine ⟨mul_nonneg hη₀0 hga, ?_⟩
    have hgk := (hgap_k (f + 1 + i) (by omega)).trans (hgap_1_bd.trans hcd1_bd)
    calc η₀ * siteGap c' (f + 1 + i) ≤ (1 / 4) * (Cg * lambdaComb c') :=
          mul_le_mul hη₀1 hgk hga (by norm_num)
      _ = Cg / 4 * lambdaComb c' := by ring
  have hpair : ∀ i ∈ Finset.range (N - f),
      0 < blaschkePairQ (designSite c' σ (f + 1 + i)) (ε (f + 1 + i)) x ∧
      0 < blaschkePairQ (chiQuantile c' ((f + 1 + i : ℕ) : ℝ)) (η₀ * siteGap c' (f + 1 + i)) x ∧
      |Real.log (blaschkePairQ (designSite c' σ (f + 1 + i)) (ε (f + 1 + i)) x) -
        Real.log (blaschkePairQ (chiQuantile c' ((f + 1 + i : ℕ) : ℝ))
          (η₀ * siteGap c' (f + 1 + i)) x)| ≤ P * (lambdaComb c' / (x - xiStar)) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hy := hY' (f + 1 + i) (by omega) (by omega)
    have hy0 := hY0 (f + 1 + i) (by omega) (by omega)
    have hy00 : 0 ≤ chiQuantile c' ((f + 1 + i : ℕ) : ℝ) := xiStar_pos.le.trans hy0.1
    have hε' := hε (f + 1 + i) (by omega) (by omega)
    have hε'1 : ε (f + 1 + i) ≤ 1 / 8 := by linarith [hε'.2]
    have hε01 : η₀ * siteGap c' (f + 1 + i) ≤ 1 / 8 := by
      have := (hεgap i).2; linarith
    refine ⟨blaschkePairQ_pos hy.1 hxpos (hx_ne _ hy.2) hε'.1 (by linarith),
      blaschkePairQ_pos hy00 hxpos (hx_ne _ hy0.2) (hεgap i).1 (by linarith), ?_⟩
    have hk := abs_log_pairQ_sub_le hy.1 hy00 hxpos hy.2 hy0.2 hxm hX hε'.1 hε'1 hε'.2
      (hεgap i).1 hε01 (hεgap i).2
      (designSite_dist_le hc' (by omega : 1 ≤ f + 1 + i) (by omega) (hσ _ (by omega) (by omega))
        hMs hΦs)
    exact hk.trans (pair_arith hs hlam hXs)
  have hnorm_ref : ‖refComb c' f η₀ (x : ℂ)‖ =
      ((‖blaschkeT (chiQuantile c' (f : ℝ) : ℂ) (x : ℂ)‖) *
        ∏ i ∈ Finset.range (N - f), blaschkePairQ (chiQuantile c' ((f + 1 + i : ℕ) : ℝ))
          (η₀ * siteGap c' (f + 1 + i)) x) * ‖combTail c' N η₀ (x : ℂ)‖ := by
    rw [hsp (by simp), norm_mul, norm_mul, norm_prod]
    rfl
  have hnorm_D : ‖designComb c' f N η₀ σ ε (x : ℂ)‖ =
      ((‖blaschkeT (designSite c' σ f : ℂ) (x : ℂ)‖) *
        ∏ i ∈ Finset.range (N - f), blaschkePairQ (designSite c' σ (f + 1 + i))
          (ε (f + 1 + i)) x) * ‖combTail c' N η₀ (x : ℂ)‖ := by
    unfold designComb
    rw [norm_mul, norm_mul, norm_prod]
    rfl
  rw [hnorm_ref, hnorm_D]
  have hy := hY' f le_rfl hfN
  have hy0 := hY0 f hf hfN
  have hF1 : |realLogT x (designSite c' σ f) - realLogT x (chiQuantile c' (f : ℝ))| ≤
      (8 * s / 3) * (lambdaComb c' / (x - xiStar)) := by
    have h1 := abs_realLogT_sub_le_of_dist hy.1 (xiStar_pos.le.trans hy0.1) hxpos hy.2 hy0.2
      (by linarith) (designSite_dist_le hc' hf hfN (hσ f le_rfl hfN) hMs hΦs)
    rw [hxm, first_arith hX] at h1
    exact h1
  have hB0 : 0 ≤ (8 * s / 3 + ((N - f : ℕ) : ℝ) * P) * (lambdaComb c' / (x - xiStar)) := by
    positivity
  refine abs_log_ratio_le (N - f) (‖blaschkeT (designSite c' σ f : ℂ) (x : ℂ)‖)
    (‖blaschkeT (chiQuantile c' (f : ℝ) : ℂ) (x : ℂ)‖) (‖combTail c' N η₀ (x : ℂ)‖)
    (fun i => blaschkePairQ (designSite c' σ (f + 1 + i)) (ε (f + 1 + i)) x)
    (fun i => blaschkePairQ (chiQuantile c' ((f + 1 + i : ℕ) : ℝ)) (η₀ * siteGap c' (f + 1 + i)) x)
    (norm_blaschkeT_ofReal_pos hxpos hy.1 (hx_ne _ hy.2))
    (norm_blaschkeT_ofReal_pos hxpos (xiStar_pos.le.trans hy0.1) (hx_ne _ hy0.2))
    (fun i hi => (hpair i hi).1) (fun i hi => (hpair i hi).2.1) _ hB0 ?_
  · have hsum : ∑ i ∈ Finset.range (N - f),
        |Real.log (blaschkePairQ (designSite c' σ (f + 1 + i)) (ε (f + 1 + i)) x) -
          Real.log (blaschkePairQ (chiQuantile c' ((f + 1 + i : ℕ) : ℝ))
            (η₀ * siteGap c' (f + 1 + i)) x)| ≤
        ((N - f : ℕ) : ℝ) * (P * (lambdaComb c' / (x - xiStar))) := by
      calc _ ≤ ∑ _i ∈ Finset.range (N - f), P * (lambdaComb c' / (x - xiStar)) :=
            Finset.sum_le_sum fun i hi => (hpair i hi).2.2
        _ = ((N - f : ℕ) : ℝ) * (P * (lambdaComb c' / (x - xiStar))) := by simp
    show |realLogT x (designSite c' σ f) - realLogT x (chiQuantile c' (f : ℝ))| + _ ≤ _
    nlinarith [hF1, hsum]

/-! ### 3. The `f = 1` design `D(N, η_*, d)` at fixed `N` -/

/-- Offsets `σ_k` of the design `D(N, η_*, d)`: `σ_1 = (|a_1| + d)/κ`, `σ_k = s_k = |a_k|/κ`. -/
noncomputable def designSigma1 (d : ℝ) (k : ℕ) : ℝ :=
  if k = 1 then (|FormalResearch.Special.airyZero 1| + d) / Window.kappaAiry
  else Window.sNodeAiry k

/-- Widths `ε'_k = η_* (χ_{k+1} - χ_k)` of the design `D(N, η_*, d)`. -/
noncomputable def designWidth1 (c' etaStar : ℝ) (k : ℕ) : ℝ := etaStar * siteGap c' k

lemma siteGap_nonneg {c' : ℝ} (hc' : 0 < c') {k : ℕ} (hk : 1 ≤ k) : 0 ≤ siteGap c' k := by
  unfold siteGap
  have ha : (1 / 4 : ℝ) ≤ (k : ℝ) := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn ha
    (ha.trans (by linarith)) (by linarith))

/-- **Lemma `P`(a) at fixed `N`** (`ut:P`(a)): for the design `D(N, η_*, d)` (`f = 1`, `η₀ = 1/4`),
`c` large and every real `x ≥ ξ_* + R_N λ`, `R_N = 4 max(Φ_{N+2}, M)` with `M` a bound for the offsets
`σ_1, …, σ_N`, `|log(|B_D(x)| / |B_ref(x)|)| ≤ C(N, η_*, d) λ / (x - ξ_*)`. -/
theorem lemma_P_a_fixedN (N : ℕ) (hN : 1 ≤ N) {etaStar : ℝ} (hη0 : 0 ≤ etaStar)
    (hη1 : etaStar ≤ 1 / 4) (d M : ℝ) (hM : ∀ k, 1 ≤ k → k ≤ N → |designSigma1 d k| ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ c' in atTop,
      ∀ x : ℝ, xiStar + 4 * max (phiQuantile ((N : ℝ) + 2)) M * lambdaComb c' ≤ x →
        |Real.log (‖designComb c' 1 N (1 / 4) (designSigma1 d) (designWidth1 c' etaStar) (x : ℂ)‖ /
          ‖refComb c' 1 (1 / 4) (x : ℂ)‖)| ≤ C * (lambdaComb c' / (x - xiStar)) := by
  obtain ⟨Cg, hCg, h_ev⟩ := siteGap_eventually_le
  obtain ⟨C, hC, h⟩ := lemma_P_b 1 N le_rfl hN M Cg
  refine ⟨C, hC, ?_⟩
  filter_upwards [h (by norm_num : (0 : ℝ) ≤ 1 / 4) le_rfl, h_ev, eventually_gt_atTop 0] with c' hc'
    ⟨hgap_k, hgap_1_bd, hcd1_bd, _⟩ hpos
  refine fun x hx => hc' (designSigma1 d) (designWidth1 c' etaStar) (fun k hk hkN => hM k hk hkN)
    (fun k hk hkN => ⟨mul_nonneg hη0 (siteGap_nonneg hpos (by omega)), ?_⟩) x hx
  have hgk := (hgap_k k (by omega)).trans (hgap_1_bd.trans hcd1_bd)
  unfold designWidth1
  calc etaStar * siteGap c' k ≤ 1 * (Cg * lambdaComb c') :=
        mul_le_mul (hη1.trans (by norm_num)) hgk (siteGap_nonneg hpos (by omega)) (by norm_num)
    _ = Cg * lambdaComb c' := one_mul _

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.refComb_eq_split_unif' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms refComb_eq_split_unif

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.lemma_P_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_P_b

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.lemma_P_a_fixedN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_P_a_fixedN

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.refComb_eq_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms refComb_eq_split

end FormalResearch.ModularBootstrap.Upper.Design
