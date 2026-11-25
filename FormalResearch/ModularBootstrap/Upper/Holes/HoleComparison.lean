module

public import FormalResearch.ModularBootstrap.Upper.Holes.Holes
public import FormalResearch.ModularBootstrap.Upper.Design.PerturbP

/-!
# Hole comparison for modified combs (`cmb:K4`, Λ-form; `rem:thmU` Steps (3)-(4))

Sources: `CFT/modular_bootstrap/paper/comb_estimates.tex`, Lemma K4 (`cmb:K4`), and
`CFT/notes/n2_ramped_comb.tex`, Lemma U* (`rem:thmU`), Steps (3) and (4), "Comparison".

The proof of the lower bound of Lemma K4 bounds every pair outside the hole only through
`q_k ≥ T_{χ_k}(x)²`, i.e. the functional
`Λ_{n,j}^{(f)}(x) = φ(f) + Σ_{k ∉ H} 2 φ(k) + Σ_{k ∈ H} log q_k`
(`lambdaTerm`, `lambdaForm_partial_lower` of `Upper.Holes.Holes`; `hole_lower_K4` there is the
consequence for the reference comb).  This file runs the same lower bound for an arbitrary finite
modification `B_D = designComb c' f N η₀ σ ε` of the `η₀`-reference comb (sites `χ'_k = ξ_* + λσ_k`,
widths `ε_k`, reference pairs beyond `N`):

* `designComb_lower_hole`: for `x ∈ [χ_n, χ_{n+1})` with hole `H = [n-j+1, n+j]`,
  `exp(𝓗_{n,j} + J_end - 2𝓔_left + Σ_mod) ≤ ‖B_D(x)‖ · exp(c' L(x) - c' P^{(f)}(x))`,
  where the modification term `Σ_mod = modLogRatio` consists of the change of the first site, the
  hole pairs `log(q'_k/q⁰_k) = log ρ_k`, and `2(f_x(χ'_k) - f_x(χ_k))` for the pairs outside the hole.
* `modLogRatio_ge`: `Σ_mod ≥ -S + Σ_{k ∈ H} log ρ_k`, `S = holeShiftCost` the site-shift cost of the
  paper (`|f_x(χ'_f) - f_x(χ_f)| + Σ_{k ∉ H} 2|f_x(χ'_k) - f_x(χ_k)|`).
* `abs_realLogT_sub_le`, `holeShiftCost_le`: `|∂_y f_x(y)| ≤ 1/|x-y| + π` (K1(c)) turned into the
  mean-value bound `|f_x(a) - f_x(b)| ≤ (1/d + π)|a - b|` on a segment at distance `≥ d` from `x`, and the
  resulting bound of `S` by `Σ 2(1/d_k + π)|Δ_k|`.

All results are proved unconditionally (no hypothesis beyond the stated ones).
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Holes

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Design

/-! ### 1. Real-axis facts on one Blaschke factor and one pair -/

lemma blaschkePairQ_zero_eps_eq_norm_sq (χ x : ℝ) :
    blaschkePairQ χ 0 x = ‖blaschkeT (χ : ℂ) (x : ℂ)‖ ^ 2 := by
  unfold blaschkePairQ
  simp [sq]

lemma norm_blaschkeT_real_pos {χ x : ℝ} (hχ : 0 ≤ χ) (hx : 0 < x) (hne : χ ≠ x) :
    0 < ‖blaschkeT (χ : ℂ) (x : ℂ)‖ := by
  have hpi := Real.pi_pos
  have ht1 : Real.tanh (π * (x - χ) / 2) ≠ 0 := by
    rw [Real.tanh_eq_sinh_div_cosh, div_ne_zero_iff]
    exact ⟨Real.sinh_ne_zero.mpr (div_ne_zero (mul_ne_zero hpi.ne' (sub_ne_zero.mpr hne.symm))
      two_ne_zero), (Real.cosh_pos _).ne'⟩
  have ht2 : Real.tanh (π * (x + χ) / 2) ≠ 0 := by
    rw [Real.tanh_eq_sinh_div_cosh, div_ne_zero_iff]
    exact ⟨(Real.sinh_pos_iff.mpr (by positivity)).ne', (Real.cosh_pos _).ne'⟩
  have hsq : 0 < blaschkePairQ χ 0 x := by
    rw [blaschkePairQ_zero_eps]
    exact sq_pos_of_ne_zero (mul_ne_zero ht1 ht2)
  rw [blaschkePairQ_zero_eps_eq_norm_sq] at hsq
  exact lt_of_le_of_ne (norm_nonneg _) (fun h => by rw [← h] at hsq; simp at hsq)

/-- A real pair at `x ≠ χ` satisfies `q ≥ T_χ(x)² > 0`, i.e. `2 f_x(χ) ≤ log q`. -/
lemma two_realLogT_le_log_blaschkePairQ {χ ε x : ℝ} (hχ : 0 ≤ χ) (hx : 0 < x) (hne : χ ≠ x)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) :
    0 < blaschkePairQ χ ε x ∧ 2 * realLogT x χ ≤ Real.log (blaschkePairQ χ ε x) := by
  have hT := norm_blaschkeT_real_pos hχ hx hne
  have h0 : blaschkePairQ χ 0 x = ‖blaschkeT (χ : ℂ) (x : ℂ)‖ ^ 2 :=
    blaschkePairQ_zero_eps_eq_norm_sq χ x
  have hle : blaschkePairQ χ 0 x ≤ blaschkePairQ χ ε x :=
    blaschkePairQ_mono_eps χ x le_rfl hε0 hε
  have hpos : 0 < blaschkePairQ χ ε x := lt_of_lt_of_le (by rw [h0]; positivity) hle
  refine ⟨hpos, ?_⟩
  have h1 : 2 * realLogT x χ = Real.log (blaschkePairQ χ 0 x) := by
    rw [h0, Real.log_pow]; unfold realLogT; norm_num
  rw [h1]
  exact Real.log_le_log (by rw [h0]; positivity) hle

/-! ### 2. The first site and the sites outside the hole: mean value bound -/

/-- `|∂_y f_x(y)| ≤ 1/|x - y| + π` for `x ≥ ξ_*`, `y ≥ 0`, `y ≠ x` (K1(c)). -/
lemma abs_realLogTDeriv_le {x y : ℝ} (hx : xiStar ≤ x) (hy : 0 ≤ y) (hxy : y ≠ x) :
    |realLogTDeriv x y| ≤ 1 / |x - y| + π := by
  have hx0 : 0 ≤ x := xiStar_pos.le.trans hx
  obtain ⟨_, h1, h2⟩ := realLogT_deriv_bounds hx0 hy hxy
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · have := (h1 hlt).2.2
    rw [abs_of_pos (sub_pos.mpr hlt)]
    linarith [Real.pi_pos]
  · obtain ⟨hp, hle⟩ := h2 hgt
    rw [abs_of_pos hp, abs_of_neg (sub_neg.mpr hgt), neg_sub]
    exact hle (hx.trans hgt.le)

/-- Mean value bound for `y ↦ f_x(y) = log |T_y(x)|` on a segment staying at distance `≥ d` from `x`. -/
theorem abs_realLogT_sub_le {x a b d : ℝ} (hx : xiStar ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 < d)
    (hseg : ∀ y ∈ Set.uIcc a b, d ≤ |x - y|) :
    |realLogT x a - realLogT x b| ≤ (1 / d + π) * |a - b| := by
  have hx0 : 0 ≤ x := xiStar_pos.le.trans hx
  have hy0 : ∀ y ∈ Set.uIcc a b, 0 ≤ y := fun y hy => by
    rcases Set.mem_uIcc.mp hy with h | h
    · exact ha.trans h.1
    · exact hb.trans h.1
  have hyne : ∀ y ∈ Set.uIcc a b, y ≠ x := fun y hy hyx => by
    have := hseg y hy
    rw [hyx, sub_self, abs_zero] at this
    linarith
  have hderiv : ∀ y ∈ Set.uIcc a b,
      HasDerivWithinAt (fun t => realLogT x t) (realLogTDeriv x y) (Set.uIcc a b) y :=
    fun y hy => (realLogT_hasDerivAt hx0 (hy0 y hy) (hyne y hy)).1.hasDerivWithinAt
  have hbound : ∀ y ∈ Set.uIcc a b, ‖realLogTDeriv x y‖ ≤ 1 / d + π := fun y hy => by
    rw [Real.norm_eq_abs]
    refine (abs_realLogTDeriv_le hx (hy0 y hy) (hyne y hy)).trans ?_
    have := hseg y hy
    have : 1 / |x - y| ≤ 1 / d := one_div_le_one_div_of_le hd this
    linarith
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_uIcc a b) (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  simpa [Real.norm_eq_abs, abs_sub_comm] using this

/-! ### 3. The modification term -/

/-- The hole `H = {n - j + 1, …, n + j}`. -/
abbrev holeSet (n j : ℕ) : Finset ℕ := Finset.Icc (n - j + 1) (n + j)

/-- The summand of `modLogRatio` at the modified pair `k`: `log ρ_k = log q'_k - log q⁰_k` on the hole,
`2(f_x(χ'_k) - f_x(χ_k))` outside. -/
noncomputable def modSummand (c' η₀ x : ℝ) (σ ε : ℕ → ℝ) (n j k : ℕ) : ℝ :=
  if k ∈ holeSet n j then
    Real.log (blaschkePairQ (designSite c' σ k) (ε k) x) - Real.log (pairModQ c' η₀ x k)
  else 2 * (realLogT x (designSite c' σ k) - realLogT x (chiQuantile c' k))

/-- The modification term `Σ_mod` of the Λ-form comparison: change of the first site plus the sum of
`modSummand` over the modified pairs `f < k ≤ N`. -/
noncomputable def modLogRatio (c' η₀ x : ℝ) (σ ε : ℕ → ℝ) (f N n j : ℕ) : ℝ :=
  (realLogT x (designSite c' σ f) - realLogT x (chiQuantile c' f)) +
    ∑ k ∈ Finset.Icc (f + 1) N, modSummand c' η₀ x σ ε n j k

/-- The site-shift cost `S` of `rem:thmU` Step (3): `|f_x(χ'_f) - f_x(χ_f)| + Σ_{k ∉ H} 2|f_x(χ'_k) - f_x(χ_k)|`. -/
noncomputable def holeShiftCost (c' x : ℝ) (σ : ℕ → ℝ) (f N n j : ℕ) : ℝ :=
  |realLogT x (designSite c' σ f) - realLogT x (chiQuantile c' f)| +
    ∑ k ∈ (Finset.Icc (f + 1) N).filter (fun k => k ∉ holeSet n j),
      2 * |realLogT x (designSite c' σ k) - realLogT x (chiQuantile c' k)|

/-- `Σ_{k ∈ H} log ρ_k` over the modified hole pairs. -/
noncomputable def holeLogRho (c' η₀ x : ℝ) (σ ε : ℕ → ℝ) (f N n j : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Icc (f + 1) N).filter (fun k => k ∈ holeSet n j),
    (Real.log (blaschkePairQ (designSite c' σ k) (ε k) x) - Real.log (pairModQ c' η₀ x k))

lemma holeShiftCost_nonneg (c' x : ℝ) (σ : ℕ → ℝ) (f N n j : ℕ) :
    0 ≤ holeShiftCost c' x σ f N n j := by
  unfold holeShiftCost
  exact add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun k _ => by positivity)

/-- The modification term is at least `-S + Σ_H log ρ_k`. -/
theorem modLogRatio_ge (c' η₀ x : ℝ) (σ ε : ℕ → ℝ) (f N n j : ℕ) :
    -holeShiftCost c' x σ f N n j + holeLogRho c' η₀ x σ ε f N n j ≤
      modLogRatio c' η₀ x σ ε f N n j := by
  unfold modLogRatio holeShiftCost holeLogRho
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc (f + 1) N)
    (fun k => k ∈ holeSet n j) (fun k => modSummand c' η₀ x σ ε n j k)
  have h1 : ∑ k ∈ (Finset.Icc (f + 1) N).filter (fun k => k ∈ holeSet n j),
      modSummand c' η₀ x σ ε n j k =
      ∑ k ∈ (Finset.Icc (f + 1) N).filter (fun k => k ∈ holeSet n j),
        (Real.log (blaschkePairQ (designSite c' σ k) (ε k) x) - Real.log (pairModQ c' η₀ x k)) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    simp [modSummand, (Finset.mem_filter.mp hk).2]
  have h2 : -∑ k ∈ (Finset.Icc (f + 1) N).filter (fun k => k ∉ holeSet n j),
        2 * |realLogT x (designSite c' σ k) - realLogT x (chiQuantile c' k)| ≤
      ∑ k ∈ (Finset.Icc (f + 1) N).filter (fun k => k ∉ holeSet n j),
        modSummand c' η₀ x σ ε n j k := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk2 := (Finset.mem_filter.mp hk).2
    have := neg_abs_le (realLogT x (designSite c' σ k) - realLogT x (chiQuantile c' k))
    simp only [modSummand, hk2, ite_false]
    linarith
  have h3 := neg_abs_le (realLogT x (designSite c' σ f) - realLogT x (chiQuantile c' f))
  have h4 := le_abs_self (realLogT x (designSite c' σ f) - realLogT x (chiQuantile c' f))
  linarith

/-- The site-shift cost is bounded through the mean value bound of K1(c): if for the first site and
every modified pair outside the hole the segment `[χ_k, χ'_k]` stays at distance `≥ d_k > 0` from `x`
(and all these sites are `≥ 0`), then `S ≤ (1/d_f + π)|Δ_f| + Σ_{k ∉ H} 2(1/d_k + π)|Δ_k|`. -/
theorem holeShiftCost_le {c' x : ℝ} (hx : xiStar ≤ x) (σ : ℕ → ℝ) {f N : ℕ} (hfN : f ≤ N) (n j : ℕ)
    (d : ℕ → ℝ)
    (hd : ∀ k, f ≤ k → k ≤ N → 0 < d k)
    (hnn : ∀ k, f ≤ k → k ≤ N → 0 ≤ designSite c' σ k ∧ 0 ≤ chiQuantile c' k)
    (hseg : ∀ k, f ≤ k → k ≤ N → (k = f ∨ k ∉ holeSet n j) →
      ∀ y ∈ Set.uIcc (designSite c' σ k) (chiQuantile c' k), d k ≤ |x - y|) :
    holeShiftCost c' x σ f N n j ≤
      (1 / d f + π) * |designSite c' σ f - chiQuantile c' f| +
        ∑ k ∈ (Finset.Icc (f + 1) N).filter (fun k => k ∉ holeSet n j),
          2 * ((1 / d k + π) * |designSite c' σ k - chiQuantile c' k|) := by
  unfold holeShiftCost
  refine add_le_add ?_ (Finset.sum_le_sum fun k hk => ?_)
  · exact abs_realLogT_sub_le hx (hnn f le_rfl hfN).1 (hnn f le_rfl hfN).2 (hd f le_rfl hfN)
      (hseg f le_rfl hfN (Or.inl rfl))
  · have hk' := Finset.mem_filter.mp hk
    have hkI := Finset.mem_Icc.mp hk'.1
    have := abs_realLogT_sub_le hx (hnn k (by omega) hkI.2).1 (hnn k (by omega) hkI.2).2
      (hd k (by omega) hkI.2) (hseg k (by omega) hkI.2 (Or.inr hk'.2))
    linarith

/-! ### 4. The finite product and the reference tail -/

lemma prod_Ioc_eq_prod_range {g : ℕ → ℝ} {a K : ℕ} (hK : a ≤ K) :
    ∏ k ∈ Finset.Ioc a K, g k = ∏ m ∈ Finset.range (K - a), g (a + 1 + m) := by
  have h_eq : Finset.Ioc a K = (Finset.range (K - a)).image (fun m => a + 1 + m) := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro ⟨h1, h2⟩; exact ⟨k - (a + 1), by omega, by omega⟩
    · rintro ⟨m, hm, rfl⟩; omega
  rw [h_eq, Finset.prod_image (fun u _ v _ h => by omega)]

lemma eta_siteGap_bounds {c' η₀ : ℝ} (hc' : 0 < c') (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4)
    (hgap : siteGap c' 1 ≤ 1 / 2) {k : ℕ} (hk : 1 ≤ k) :
    0 ≤ η₀ * siteGap c' k ∧ η₀ * siteGap c' k ≤ 1 / 8 := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hgk_nn : 0 ≤ siteGap c' k := by
    unfold siteGap
    exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn
      (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith)) (by linarith))
  have hgk_le : siteGap c' k ≤ siteGap c' 1 := by
    have hanti := (siteGap_strictAnti hc').antitone (show 0 ≤ k - 1 by omega)
    have heq : (k - 1) + 1 = k := by omega
    simpa [heq] using hanti
  refine ⟨mul_nonneg hη₀0 hgk_nn, ?_⟩
  nlinarith

/-- The partial products of the reference pairs beyond `N` converge to `‖combTail‖`. -/
lemma tendsto_prod_pairModQ_tail {c' η₀ x : ℝ} (hc' : 0 < c') (hη₀0 : 0 ≤ η₀)
    (hη₀1 : η₀ ≤ 1 / 4) (hgap : siteGap c' 1 ≤ 1 / 2) (N : ℕ) :
    Tendsto (fun K : ℕ => ∏ k ∈ Finset.Ioc N K, pairModQ c' η₀ x k) atTop
      (𝓝 ‖combTail c' N η₀ (x : ℂ)‖) := by
  have hχ_nn : ∀ m : ℕ, 0 ≤ chiQuantile c' (N + 1 + m : ℕ) := fun m => by
    have hm1 : (1 : ℝ) ≤ ((N + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N + 1 + m)
    exact xiStar_pos.le.trans (chiQuantile_spec hc' (by linarith)).1
  have hε_bd : ∀ m : ℕ, |η₀ * siteGap c' (N + 1 + m)| ≤ 1 / 8 := fun m => by
    obtain ⟨h0, h1⟩ := eta_siteGap_bounds hc' hη₀0 hη₀1 hgap (k := N + 1 + m) (by omega)
    rw [abs_of_nonneg h0]; exact h1
  have hhas := (comb_pairProd_hasProdLocallyUniformlyOn
    (fun m : ℕ => chiQuantile c' (N + 1 + m : ℕ)) (fun m : ℕ => η₀ * siteGap c' (N + 1 + m))
    hχ_nn hε_bd (summable_exp_neg_pi_chiQuantile hc' N)).hasProd
    (by simp : (x : ℂ) ∈ {b : ℂ | |b.im| < 7 / 8})
  have ht := hhas.tendsto_prod_nat
  have hnorm := (continuous_norm.tendsto _).comp ht
  have hshift : Tendsto (fun K : ℕ => K - N) atTop atTop :=
    tendsto_atTop_atTop.mpr fun M => ⟨M + N, fun K hK => Nat.le_sub_of_add_le hK⟩
  have hcomp := hnorm.comp hshift
  refine hcomp.congr' ?_
  filter_upwards [eventually_ge_atTop N] with K hK
  simp only [Function.comp_def]
  rw [prod_Ioc_eq_prod_range hK, norm_prod]
  refine Finset.prod_congr rfl fun m _ => ?_
  unfold pairModQ blaschkePairQ
  rfl

/-- The norm of the finite modification splits into the first factor, the modified pairs and the tail. -/
lemma norm_designComb_eq (c' η₀ x : ℝ) (σ ε : ℕ → ℝ) {f N : ℕ} (hfN : f ≤ N) :
    ‖designComb c' f N η₀ σ ε (x : ℂ)‖ =
      ‖blaschkeT (designSite c' σ f : ℂ) (x : ℂ)‖ *
        (∏ k ∈ Finset.Ioc f N, blaschkePairQ (designSite c' σ k) (ε k) x) *
        ‖combTail c' N η₀ (x : ℂ)‖ := by
  unfold designComb
  rw [norm_mul, norm_mul, norm_prod,
    prod_Ioc_eq_prod_range (g := fun k => blaschkePairQ (designSite c' σ k) (ε k) x) hfN]
  rfl

/-! ### 5. The comparison theorem -/

lemma Icc_succ_eq_Ioc (a K : ℕ) : Finset.Icc (a + 1) K = Finset.Ioc a K := Finset.Icc_add_one_left_eq_Ioc a K

/-- **Λ-form of Lemma K4 for a finite modification of the reference comb** (`rem:thmU`, Step (3),
"Comparison").  For `x ∈ [χ_n, χ_{n+1})`, the hole `H = [n-j+1, n+j]` and the modification
`B_D = designComb c' f N η₀ σ ε` (`f ≤ N`, reference pairs beyond `N`),
`exp(𝓗_{n,j} + J_end - 2𝓔_left + Σ_mod) ≤ ‖B_D(x)‖ exp(c' L(x) - c' P^{(f)}(x))`,
where `Σ_mod = modLogRatio ≥ -S + Σ_{k∈H} log ρ_k` (`modLogRatio_ge`).  Only the hole pairs enter exactly;
all other modified pairs enter through `q'_k ≥ T_{χ'_k}(x)²`.

Hypotheses: positive reference width `η₀`; widths `0 ≤ ε_k ≤ 1/2` and sites `χ'_k ≥ 0` of the modified
pairs; `x` is not a zero of the first factor nor of a modified pair outside the hole; the modified hole
pairs do not vanish at `x`. -/
theorem designComb_lower_hole {c' η₀ x : ℝ} (hc' : 0 < c') (hη₀0 : 0 < η₀) (hη₀1 : η₀ ≤ 1 / 4)
    (hgap : siteGap c' 1 ≤ 1 / 2) {f N n j : ℕ} (hf : 1 ≤ f) (hfN : f ≤ N) (hj : 1 ≤ j)
    (hfnj : f + j ≤ n) (hx : inCell c' n x) (σ ε : ℕ → ℝ)
    (hε : ∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ 1 / 2)
    (hsite : ∀ k, f ≤ k → k ≤ N → 0 ≤ designSite c' σ k)
    (hf_ne : designSite c' σ f ≠ x)
    (hout : ∀ k, f < k → k ≤ N → k ∉ holeSet n j → designSite c' σ k ≠ x)
    (hhole : ∀ k, f < k → k ≤ N → k ∈ holeSet n j →
      0 < blaschkePairQ (designSite c' σ k) (ε k) x) :
    Real.exp (holeH c' η₀ n j x + jEndComb c' x f - 2 * eLeftComb c' f n j x +
        modLogRatio c' η₀ x σ ε f N n j) ≤
      ‖designComb c' f N η₀ σ ε (x : ℂ)‖ * Real.exp (c' * slitL x - c' * combPf c' f x) := by
  have hn1 : 1 ≤ n := by omega
  have hx_xi : xiStar ≤ x := by
    have hn1r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    exact (chiQuantile_spec hc' (by linarith)).1.trans hx.1
  have hx_pos : 0 < x := xiStar_pos.trans_le hx_xi
  have hnH : n ∈ holeSet n j := by simp only [holeSet, Finset.mem_Icc]; omega
  -- data of the modified comb
  set qD : ℕ → ℝ := fun k =>
    if k ≤ N then blaschkePairQ (designSite c' σ k) (ε k) x else pairModQ c' η₀ x k with hqD
  set sD : ℕ → ℝ := fun k => if k ≤ N then designSite c' σ k else chiQuantile c' k with hsD
  set PD : ℕ → ℝ := fun K =>
    ‖blaschkeT (designSite c' σ f : ℂ) (x : ℂ)‖ * ∏ k ∈ Finset.Ioc f K, qD k with hPD
  have hTf := norm_blaschkeT_real_pos (hsite f le_rfl hfN) hx_pos hf_ne
  -- positivity of every pair
  have hqpos : ∀ k, f < k → 0 < qD k := by
    intro k hk
    by_cases hkN : k ≤ N
    · simp only [hqD, ite_eq_left hkN]
      by_cases hkH : k ∈ holeSet n j
      · exact hhole k hk hkN hkH
      · exact (two_realLogT_le_log_blaschkePairQ (hsite k hk.le hkN) hx_pos (hout k hk hkN hkH)
          (hε k hk hkN).1 (hε k hk hkN).2).1
    · simp only [hqD, ite_eq_right hkN]
      exact pairModQ_pos hc' hη₀0.le hη₀1 hgap (by omega) hx (Or.inl hη₀0)
  -- the Λ-form summand of the modified comb
  have hlam_le : ∀ k, f < k →
      (if k ∈ holeSet n j then Real.log (qD k) else 2 * realLogT x (sD k)) ≤ Real.log (qD k) := by
    intro k hk
    by_cases hkH : k ∈ holeSet n j
    · rw [ite_eq_left hkH]
    · rw [ite_eq_right hkH]
      by_cases hkN : k ≤ N
      · simp only [hqD, hsD, ite_eq_left hkN]
        exact (two_realLogT_le_log_blaschkePairQ (hsite k hk.le hkN) hx_pos (hout k hk hkN hkH)
          (hε k hk hkN).1 (hε k hk hkN).2).2
      · simp only [hqD, hsD, ite_eq_right hkN]
        have hkn : k ≠ n := fun h => hkH (h ▸ hnH)
        exact two_phiVar_le_log_pairModQ hc' hη₀0.le hη₀1 hgap hn1 (by omega) hx hkn
  -- the lower bound for the partial products
  have hpartial : ∀ K, max N (n + j) ≤ K →
      Real.exp (holeH c' η₀ n j x + jEndComb c' x f - 2 * eLeftComb c' f n j x +
          modLogRatio c' η₀ x σ ε f N n j +
          2 * ∫ a in (f : ℝ)..((K : ℝ) + 1 / 2), phiVar c' x a) ≤ PD K := by
    intro K hK
    have hNK : N ≤ K := (le_max_left _ _).trans hK
    have hnjK : n + j ≤ K := (le_max_right _ _).trans hK
    have hPDpos : 0 < PD K :=
      mul_pos hTf (Finset.prod_pos fun k hk => hqpos k (Finset.mem_Ioc.mp hk).1)
    have hlog : Real.log (PD K) =
        realLogT x (designSite c' σ f) + ∑ k ∈ Finset.Ioc f K, Real.log (qD k) := by
      have hprod_ne : ∏ k ∈ Finset.Ioc f K, qD k ≠ 0 :=
        (Finset.prod_pos fun k hk => hqpos k (Finset.mem_Ioc.mp hk).1).ne'
      simp only [hPD]
      rw [Real.log_mul hTf.ne' hprod_ne, Real.log_prod fun k hk => (hqpos k (Finset.mem_Ioc.mp hk).1).ne']
      rfl
    -- Λ-form of the modified comb versus that of the reference comb
    have hsum_lam : ∑ k ∈ Finset.Ioc f K,
        (if k ∈ holeSet n j then Real.log (qD k) else 2 * realLogT x (sD k)) =
        ∑ k ∈ Finset.Ioc f K, lambdaTerm c' η₀ x n j k +
          ∑ k ∈ Finset.Ioc f N, modSummand c' η₀ x σ ε n j k := by
      have hs1 := Finset.sum_Ioc_consecutive
        (fun k => if k ∈ holeSet n j then Real.log (qD k) else 2 * realLogT x (sD k))
        (show f ≤ N from hfN) hNK
      have hs2 := Finset.sum_Ioc_consecutive (fun k => lambdaTerm c' η₀ x n j k)
        (show f ≤ N from hfN) hNK
      rw [← hs1, ← hs2]
      have hhead : ∑ k ∈ Finset.Ioc f N,
          (if k ∈ holeSet n j then Real.log (qD k) else 2 * realLogT x (sD k)) =
          ∑ k ∈ Finset.Ioc f N, lambdaTerm c' η₀ x n j k +
            ∑ k ∈ Finset.Ioc f N, modSummand c' η₀ x σ ε n j k := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hkN := (Finset.mem_Ioc.mp hk).2
        by_cases hkH : k ∈ holeSet n j
        · simp only [hqD, lambdaTerm, modSummand, ite_eq_left hkH, ite_eq_left hkN]; ring
        · simp only [hsD, lambdaTerm, modSummand, phiVar, ite_eq_right hkH, ite_eq_left hkN]; ring
      have htail : ∑ k ∈ Finset.Ioc N K,
          (if k ∈ holeSet n j then Real.log (qD k) else 2 * realLogT x (sD k)) =
          ∑ k ∈ Finset.Ioc N K, lambdaTerm c' η₀ x n j k := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hkN : ¬ k ≤ N := by have := (Finset.mem_Ioc.mp hk).1; omega
        by_cases hkH : k ∈ holeSet n j
        · simp only [hqD, lambdaTerm, ite_eq_left hkH, ite_eq_right hkN]
        · simp only [hsD, lambdaTerm, phiVar, ite_eq_right hkH, ite_eq_right hkN]
      rw [hhead, htail]; ring
    have hbase := lambdaForm_partial_lower (η₀ := η₀) hc' hf hj hfnj hnjK hx
    rw [Icc_succ_eq_Ioc] at hbase
    have hge : realLogT x (designSite c' σ f) +
        ∑ k ∈ Finset.Ioc f K,
          (if k ∈ holeSet n j then Real.log (qD k) else 2 * realLogT x (sD k)) ≤
        Real.log (PD K) := by
      rw [hlog]
      have := Finset.sum_le_sum (s := Finset.Ioc f K) fun k hk => hlam_le k (Finset.mem_Ioc.mp hk).1
      linarith
    have hmod : modLogRatio c' η₀ x σ ε f N n j =
        (realLogT x (designSite c' σ f) - phiVar c' x f) +
          ∑ k ∈ Finset.Ioc f N, modSummand c' η₀ x σ ε n j k := by
      unfold modLogRatio
      rw [Icc_succ_eq_Ioc]
      rfl
    have hfin : holeH c' η₀ n j x + jEndComb c' x f - 2 * eLeftComb c' f n j x +
          modLogRatio c' η₀ x σ ε f N n j +
          2 * ∫ a in (f : ℝ)..((K : ℝ) + 1 / 2), phiVar c' x a ≤ Real.log (PD K) := by
      rw [hmod]
      linarith
    calc Real.exp (_) ≤ Real.exp (Real.log (PD K)) := Real.exp_le_exp.mpr hfin
      _ = PD K := Real.exp_log hPDpos
  -- the limit
  have hlim_PD : Tendsto PD atTop
      (𝓝 ‖designComb c' f N η₀ σ ε (x : ℂ)‖) := by
    rw [norm_designComb_eq c' η₀ x σ ε hfN]
    have htail := tendsto_prod_pairModQ_tail (x := x) hc' hη₀0.le hη₀1 hgap N
    have hconst : Tendsto (fun K : ℕ =>
        ‖blaschkeT (designSite c' σ f : ℂ) (x : ℂ)‖ *
          (∏ k ∈ Finset.Ioc f N, blaschkePairQ (designSite c' σ k) (ε k) x) *
          ∏ k ∈ Finset.Ioc N K, pairModQ c' η₀ x k) atTop
        (𝓝 (‖blaschkeT (designSite c' σ f : ℂ) (x : ℂ)‖ *
          (∏ k ∈ Finset.Ioc f N, blaschkePairQ (designSite c' σ k) (ε k) x) *
          ‖combTail c' N η₀ (x : ℂ)‖)) := tendsto_const_nhds.mul htail
    refine hconst.congr' ?_
    filter_upwards [eventually_ge_atTop N] with K hK
    simp only [hPD]
    have hsplit := Finset.prod_Ioc_consecutive qD hfN hK
    have h1 : ∏ k ∈ Finset.Ioc f N, qD k =
        ∏ k ∈ Finset.Ioc f N, blaschkePairQ (designSite c' σ k) (ε k) x := by
      refine Finset.prod_congr rfl fun k hk => ?_
      simp only [hqD, ite_eq_left (Finset.mem_Ioc.mp hk).2]
    have h2 : ∏ k ∈ Finset.Ioc N K, qD k = ∏ k ∈ Finset.Ioc N K, pairModQ c' η₀ x k := by
      refine Finset.prod_congr rfl fun k hk => ?_
      have : ¬ k ≤ N := by have := (Finset.mem_Ioc.mp hk).1; omega
      simp only [hqD, ite_eq_right this]
    rw [← hsplit, h1, h2, mul_assoc]
  have hlim_exp : Tendsto (fun K : ℕ =>
      Real.exp (holeH c' η₀ n j x + jEndComb c' x f - 2 * eLeftComb c' f n j x +
          modLogRatio c' η₀ x σ ε f N n j +
          2 * ∫ a in (f : ℝ)..((K : ℝ) + 1 / 2), phiVar c' x a)) atTop
      (𝓝 (Real.exp (holeH c' η₀ n j x + jEndComb c' x f - 2 * eLeftComb c' f n j x +
          modLogRatio c' η₀ x σ ε f N n j + (-c' * slitL x + c' * combPf c' f x)))) :=
    (Real.continuous_exp.tendsto _).comp
      (tendsto_const_nhds.add (tendsto_two_integral_phiVar hc' hx_xi hf))
  have hle := le_of_tendsto_of_tendsto hlim_exp hlim_PD
    (by filter_upwards [eventually_ge_atTop (max N (n + j))] with K hK using hpartial K hK)
  have hexp : Real.exp (holeH c' η₀ n j x + jEndComb c' x f - 2 * eLeftComb c' f n j x +
          modLogRatio c' η₀ x σ ε f N n j + (-c' * slitL x + c' * combPf c' f x)) =
      Real.exp (holeH c' η₀ n j x + jEndComb c' x f - 2 * eLeftComb c' f n j x +
          modLogRatio c' η₀ x σ ε f N n j) * Real.exp (-(c' * slitL x - c' * combPf c' f x)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp] at hle
  have hpos := Real.exp_pos (c' * slitL x - c' * combPf c' f x)
  have h2 : Real.exp (-(c' * slitL x - c' * combPf c' f x)) *
      Real.exp (c' * slitL x - c' * combPf c' f x) = 1 := by
    rw [← Real.exp_add]; simp
  calc Real.exp (holeH c' η₀ n j x + jEndComb c' x f - 2 * eLeftComb c' f n j x +
          modLogRatio c' η₀ x σ ε f N n j)
      = (Real.exp (holeH c' η₀ n j x + jEndComb c' x f - 2 * eLeftComb c' f n j x +
          modLogRatio c' η₀ x σ ε f N n j) * Real.exp (-(c' * slitL x - c' * combPf c' f x))) *
          Real.exp (c' * slitL x - c' * combPf c' f x) := by rw [mul_assoc, h2, mul_one]
    _ ≤ ‖designComb c' f N η₀ σ ε (x : ℂ)‖ * Real.exp (c' * slitL x - c' * combPf c' f x) :=
        mul_le_mul_of_nonneg_right hle hpos.le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.modLogRatio_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.modLogRatio_ge

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.holeShiftCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.holeShiftCost_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.designComb_lower_hole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.designComb_lower_hole
