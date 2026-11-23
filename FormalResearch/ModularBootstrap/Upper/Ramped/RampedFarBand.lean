module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedDesignNearTip
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedDesignPhase

/-!
# The far band of the ramped comb `B_{D_*}`

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma U* (`rem:thmU`), Step 5.

For `x ≥ ξ_* + 1/2`, to the right of every site and every width of the modification,
`0 < B_{D_*}(x) ≤ (1 + C λ) B_ref(x)` with `C` absolute: the first factor `T_y` is decreasing in
`y < x` and `χ'_1 ≥ χ_1`, each pair modulus `q` is increasing in `ε` and Lipschitz in the site
(`pair_ratio_le`), and `Σ_k |Δ_k| + Σ_k ℓ_k² = O(λ)`.

* `pair_ratio_le`: one modified pair against the reference pair.
* `combTail_norm_pos`: the unmodified tail does not vanish at `x` (all its pair moduli are positive).
* `farBand_sum_le`: the exponent sum is `O(λ)`, uniformly in `C_I, C_mid` and `d ∈ [0, 1]`.
* `rampedFarBand`: the far-band comparison, for every `C_I, C_mid ≥ 1`, `d ∈ [0, 1]`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb Upper.Design Upper.Window
  Upper.Holes Upper.Hankel Upper.Positivity

/-- One pair of a modified comb against the reference pair, to the right of the tip window. -/
lemma pair_ratio_le {χ χ' ε' ε0 x : ℝ} (hχ : xiStar ≤ χ) (hχ' : xiStar ≤ χ') (hx : xiStar + 1 / 2 ≤ x)
    (hχu : χ ≤ xiStar + 1 / 4) (hχ'u : χ' ≤ xiStar + 1 / 4) (hε'0 : 0 ≤ ε') (hε' : ε' ≤ ε0)
    (hε0 : ε0 ≤ 1 / 16) :
    blaschkePairQ χ' ε' x ≤
      blaschkePairQ χ ε0 x * Real.exp (2 * (4 + π) * |χ' - χ| + 24 * ε0 ^ 2) := by
  have hxs := xiStar_pos
  have hpi := Real.pi_pos
  have hx0 : 0 < x := by linarith
  have hne : x ≠ χ' := by intro h; linarith
  have hne1 : x ≠ χ := by intro h; linarith
  have hε00 : 0 ≤ ε0 := hε'0.trans hε'
  -- q' ≤ q(χ', ε0)
  have h1 : blaschkePairQ χ' ε' x ≤ blaschkePairQ χ' ε0 x :=
    blaschkePairQ_mono_eps χ' x hε'0 hε' (by linarith)
  have h2 := blaschkePairQ_le_mul hχ' (by linarith : xiStar ≤ x) hne hε00 hε0
  -- ε0²/(x-χ')² ≤ 16 ε0²
  have hd' : (1 : ℝ) / 4 ≤ x - χ' := by linarith
  have h3 : ε0 ^ 2 / (x - χ') ^ 2 ≤ 16 * ε0 ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : (1 / 4 : ℝ) ^ 2 ≤ (x - χ') ^ 2 := pow_le_pow_left₀ (by norm_num) hd' 2
    nlinarith [sq_nonneg ε0]
  have h4 : (1 + ε0 ^ 2 / (x - χ') ^ 2) * (1 + 8 * ε0 ^ 2) ≤ Real.exp (24 * ε0 ^ 2) := by
    have e1 : 1 + ε0 ^ 2 / (x - χ') ^ 2 ≤ Real.exp (16 * ε0 ^ 2) :=
      (by linarith : 1 + ε0 ^ 2 / (x - χ') ^ 2 ≤ 1 + 16 * ε0 ^ 2).trans (by linarith [Real.add_one_le_exp (16 * ε0 ^ 2)])
    have e2 : 1 + 8 * ε0 ^ 2 ≤ Real.exp (8 * ε0 ^ 2) := by linarith [Real.add_one_le_exp (8 * ε0 ^ 2)]
    calc (1 + ε0 ^ 2 / (x - χ') ^ 2) * (1 + 8 * ε0 ^ 2) ≤ Real.exp (16 * ε0 ^ 2) * Real.exp (8 * ε0 ^ 2) :=
          mul_le_mul e1 e2 (by positivity) (Real.exp_pos _).le
      _ = Real.exp (24 * ε0 ^ 2) := by rw [← Real.exp_add]; ring_nf
  -- q(χ',0) = exp(2 f(χ')), q(χ, ε0) ≥ q(χ,0) = exp(2 f(χ))
  have h5 := exp_two_realLogT_eq (by linarith : 0 ≤ χ') hx0 hne.symm
  have h6 := exp_two_realLogT_eq (by linarith : 0 ≤ χ) hx0 hne1.symm
  have h7 : blaschkePairQ χ 0 x ≤ blaschkePairQ χ ε0 x :=
    blaschkePairQ_mono_eps χ x le_rfl hε00 (by linarith)
  -- Lipschitz of f_x
  have h8 : |realLogT x χ' - realLogT x χ| ≤ (1 / (1 / 4) + π) * |χ' - χ| := by
    refine abs_realLogT_sub_le (by linarith) (by linarith) (by linarith) (by norm_num) ?_
    intro y hy
    have : y ≤ xiStar + 1 / 4 := by
      rcases Set.mem_uIcc.mp hy with h | h <;> linarith [h.2]
    rw [abs_of_pos (by linarith)]
    linarith
  have h9 : Real.exp (2 * realLogT x χ') ≤
      Real.exp (2 * realLogT x χ) * Real.exp (2 * (4 + π) * |χ' - χ|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have := (abs_le.1 h8).2
    nlinarith
  have hq0 : 0 < blaschkePairQ χ 0 x := by rw [← h6]; exact Real.exp_pos _
  calc blaschkePairQ χ' ε' x ≤ blaschkePairQ χ' ε0 x := h1
    _ ≤ blaschkePairQ χ' 0 x * ((1 + ε0 ^ 2 / (x - χ') ^ 2) * (1 + 8 * ε0 ^ 2)) := h2
    _ ≤ blaschkePairQ χ' 0 x * Real.exp (24 * ε0 ^ 2) :=
        mul_le_mul_of_nonneg_left h4 (by rw [← h5]; exact (Real.exp_pos _).le)
    _ = Real.exp (2 * realLogT x χ') * Real.exp (24 * ε0 ^ 2) := by rw [h5]
    _ ≤ (Real.exp (2 * realLogT x χ) * Real.exp (2 * (4 + π) * |χ' - χ|)) * Real.exp (24 * ε0 ^ 2) :=
        mul_le_mul_of_nonneg_right h9 (Real.exp_pos _).le
    _ = blaschkePairQ χ 0 x * Real.exp (2 * (4 + π) * |χ' - χ| + 24 * ε0 ^ 2) := by
        rw [h6, Real.exp_add]; ring
    _ ≤ blaschkePairQ χ ε0 x * Real.exp (2 * (4 + π) * |χ' - χ| + 24 * ε0 ^ 2) :=
        mul_le_mul_of_nonneg_right h7 (Real.exp_pos _).le


lemma siteGap_pos' {c' : ℝ} (hc' : 0 < c') {k : ℕ} (hk : 1 ≤ k) : 0 < siteGap c' k := by
  unfold siteGap
  have ha : (1 / 4 : ℝ) ≤ (k : ℝ) := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  exact sub_pos.mpr ((chiQuantile_strictMonoOn hc') (Set.mem_Ici.2 ha)
    (Set.mem_Ici.2 (ha.trans (by linarith))) (by linarith))

/-- The unmodified tail does not vanish at a real `x` where all its pair moduli are positive. -/
lemma combTail_norm_pos {c' x : ℝ} (hc' : 0 < c') (hx0 : 0 ≤ x) {N : ℕ} (hN : 1 ≤ N)
    (hgap : siteGap c' 1 ≤ 1 / 2) (hN_ne : chiQuantile c' N ≠ x)
    (hq : ∀ m : ℕ, 0 < pairModQ c' (1 / 4) x (N + 1 + m)) (hε : ∀ k : ℕ, 1 ≤ k → |1 / 4 * siteGap c' k| ≤ 1 / 8) :
    0 < ‖combTail c' N (1 / 4) (x : ℂ)‖ := by
  have hsum_q := (refComb_norm_log_eq_tsum hc' hx0 hN (η₀ := 1 / 4) (by norm_num) (by norm_num) hgap hN_ne hq).1
  have h_prod_exp : HasProd (fun m : ℕ => pairModQ c' (1 / 4) x (N + 1 + m))
      (Real.exp (∑' m : ℕ, Real.log (pairModQ c' (1 / 4) x (N + 1 + m)))) := by
    refine (Real.continuous_exp.continuousAt.tendsto.comp hsum_q.hasSum).congr fun s => ?_
    dsimp [Function.comp_def]
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun m _ => Real.exp_log (hq m)
  let χ := fun m : ℕ => chiQuantile c' (N + 1 + m : ℕ)
  let ε := fun m : ℕ => 1 / 4 * siteGap c' (N + 1 + m)
  let P : ℕ → ℂ := fun m => pairT (χ m) (ε m) (x : ℂ)
  have hχ_nn : ∀ m : ℕ, 0 ≤ χ m := fun m => by
    have hm1 : (1 : ℝ) ≤ ((N + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N + 1 + m)
    exact xiStar_pos.le.trans (chiQuantile_spec hc' (by linarith)).1
  have hhasProd := (comb_pairProd_hasProdLocallyUniformlyOn χ ε hχ_nn (fun m => hε _ (by omega))
    (summable_exp_neg_pi_chiQuantile hc' N)).hasProd (by simp : (x : ℂ) ∈ {b : ℂ | |b.im| < 7 / 8})
  have hnorm_prod : HasProd (fun m : ℕ => ‖P m‖) ‖∏' m : ℕ, P m‖ := by
    refine (continuous_norm.continuousAt.tendsto.comp hhasProd).congr fun s => ?_
    dsimp [Function.comp_def]
    induction s using Finset.induction with
    | empty => simp
    | @insert a s has ih =>
      rw [Finset.prod_insert has, Finset.prod_insert has, norm_mul, ih]
      exact rfl
  have h_norm_eq : (fun m : ℕ => ‖P m‖) = fun m : ℕ => pairModQ c' (1 / 4) x (N + 1 + m) := by
    ext m; rfl
  rw [h_norm_eq] at hnorm_prod
  have : ‖∏' m : ℕ, P m‖ = Real.exp (∑' m : ℕ, Real.log (pairModQ c' (1 / 4) x (N + 1 + m))) :=
    tendsto_nhds_unique hnorm_prod h_prod_exp
  show 0 < ‖∏' m : ℕ, P m‖
  rw [this]
  exact Real.exp_pos _


lemma tanhProd_eq (x y : ℝ) :
    Real.tanh (π * (x - y) / 2) * Real.tanh (π * (x + y) / 2) =
      (Real.cosh (π * x) - Real.cosh (π * y)) / (Real.cosh (π * x) + Real.cosh (π * y)) := by
  have key : ∀ a b : ℝ, Real.tanh a * Real.tanh b =
      (Real.cosh (a + b) - Real.cosh (a - b)) / (Real.cosh (a + b) + Real.cosh (a - b)) := by
    intro a b
    have hca := Real.cosh_pos a
    have hcb := Real.cosh_pos b
    rw [Real.cosh_add, Real.cosh_sub, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
    field_simp
    ring
  have h := key (π * (x - y) / 2) (π * (x + y) / 2)
  rw [show π * (x - y) / 2 + π * (x + y) / 2 = π * x by ring,
    show π * (x - y) / 2 - π * (x + y) / 2 = -(π * y) by ring, Real.cosh_neg] at h
  exact h

/-- The first factor `T_y(x)` is decreasing in the zero `y ≥ 0`. -/
lemma tanhProd_anti {x y y' : ℝ} (hy : 0 ≤ y) (hyy : y ≤ y') :
    Real.tanh (π * (x - y') / 2) * Real.tanh (π * (x + y') / 2) ≤
      Real.tanh (π * (x - y) / 2) * Real.tanh (π * (x + y) / 2) := by
  rw [tanhProd_eq, tanhProd_eq]
  have hpi := Real.pi_pos
  have hc : Real.cosh (π * y) ≤ Real.cosh (π * y') := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (by positivity), abs_of_nonneg (by nlinarith)]
    nlinarith
  have hA := Real.cosh_pos (π * x)
  have hu := Real.cosh_pos (π * y)
  have hu' := Real.cosh_pos (π * y')
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hc hA.le]

lemma norm_blaschkeT_real {y x : ℝ} (hy : 0 ≤ y) (hyx : y < x) :
    ‖blaschkeT (y : ℂ) (x : ℂ)‖ =
      Real.tanh (π * (x - y) / 2) * Real.tanh (π * (x + y) / 2) := by
  rw [blaschkeT_ofReal_eq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (tanh_prod_pos_of_lt hy hyx)]

/-- The exponent sum of the pair comparison is `O(λ)` (`Σ|Δ_k| = O(λ)`, `Σ ℓ_k² = O(c'^{-1})`). -/
theorem farBand_sum_le : ∃ C : ℝ, 0 < C ∧ ∀ᶠ c' : ℝ in atTop, ∀ (P : RampedParams) (d : ℝ),
    0 ≤ d → d ≤ 1 →
      ∑ k ∈ Finset.Ioc 1 (nCap P c' + 6),
        (2 * (4 + π) * |designSite c' (rampedSigma d c') k - chiQuantile c' (k : ℝ)| +
          24 * (1 / 4 * siteGap c' k) ^ 2) ≤ C * lambdaComb c' := by
  obtain ⟨cg, Cg, c0g, hcg, hCg, hc0g, hgap⟩ := rampedGap_two_sided
  obtain ⟨Cs, hCs, hsh⟩ := rampedShift_le
  have hpi := Real.pi_pos
  refine ⟨2 * (4 + π) * (Cs * 3) + 24 * (Cg ^ 2 * 3 / 16), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max c0g 10000), eventually_lambda_cbrt] with c' hc' hlc P d hd hd1
  have hc'0 : 0 < c' := lt_of_lt_of_le (by positivity) hc'
  have hc'1 : 10000 ≤ c' := (le_max_right _ _).trans hc'
  have hcg' : c0g ≤ c' := (le_max_left _ _).trans hc'
  have hl := lambdaComb_pos' hc'0
  set N := nCap P c' + 6 with hN
  have hNc : (N : ℝ) ≤ c' := by
    have := nCap_le P hc'1
    rw [hN]; push_cast; linarith
  have hNp : (0 : ℝ) < N := by rw [hN]; positivity
  have h2 : ∑ k ∈ Finset.Ioc 1 N, (1 / 4 * siteGap c' k) ^ 2 ≤
      Cg ^ 2 * lambdaComb c' ^ 2 / 16 * (3 * (N : ℝ) ^ (1 / 3 : ℝ)) := by
    have hpt : ∀ k ∈ Finset.Ioc 1 N, (1 / 4 * siteGap c' k) ^ 2 ≤
        Cg ^ 2 * lambdaComb c' ^ 2 / 16 * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
      intro k hk
      have hk' := Finset.mem_Ioc.mp hk
      have hkp : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      obtain ⟨-, hgu⟩ := hgap P c' hcg' k (by omega) (by omega)
      have hg0 : 0 ≤ siteGap c' k := siteGap_nonneg hc'0 (by omega)
      have hkk : ((k : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 = (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hkp.le]; norm_num
      have hsq : siteGap c' k ^ 2 ≤ Cg ^ 2 * lambdaComb c' ^ 2 * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
        have h0 : 0 ≤ Cg * lambdaComb c' * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
        calc siteGap c' k ^ 2 ≤ (Cg * lambdaComb c' * (k : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 :=
              pow_le_pow_left₀ hg0 hgu 2
          _ = Cg ^ 2 * lambdaComb c' ^ 2 * ((k : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 := by ring
          _ = _ := by rw [hkk]
      nlinarith [sq_nonneg (siteGap c' k)]
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum]
    have hsum : ∑ k ∈ Finset.Ioc 1 N, (k : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 3 * (N : ℝ) ^ (1 / 3 : ℝ) := by
      have := sum_Icc_rpow_neg_lt_one (p := 2 / 3) (by norm_num) (by norm_num) N
      have hsub : ∑ k ∈ Finset.Ioc 1 N, (k : ℝ) ^ (-(2 / 3 : ℝ)) ≤
          ∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ (-(2 / 3 : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => by
          simp only [Finset.mem_Ioc, Finset.mem_Icc] at hk ⊢; omega)
          (fun k _ _ => by positivity)
      refine hsub.trans (this.trans ?_)
      rw [show (1 - 2 / 3 : ℝ) = 1 / 3 by norm_num]
      have : (N : ℝ) ^ (1 / 3 : ℝ) / (1 / 3) = 3 * (N : ℝ) ^ (1 / 3 : ℝ) := by ring
      linarith [this]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  have h3 : ∑ k ∈ Finset.Ioc 1 N, |designSite c' (rampedSigma d c') k - chiQuantile c' (k : ℝ)| ≤
      Cs * lambdaComb c' * 3 := by
    have hpt : ∀ k ∈ Finset.Ioc 1 N, |designSite c' (rampedSigma d c') k - chiQuantile c' (k : ℝ)| ≤
        Cs * lambdaComb c' * (k : ℝ) ^ (-(4 / 3 : ℝ)) := fun k hk =>
      hsh c' hc'0 d hd hd1 k (by have := (Finset.mem_Ioc.mp hk).1; omega)
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum]
    have := sum_Ioc_rpow_neg_gt_one (p := 4 / 3) (by norm_num) (a := 1) le_rfl N
    simp only [Nat.cast_one, Real.one_rpow] at this
    have e : (1 : ℝ) / (4 / 3 - 1) = 3 := by norm_num
    exact mul_le_mul_of_nonneg_left (this.trans (by rw [e])) (by positivity)
  have hlN : lambdaComb c' * (N : ℝ) ^ (1 / 3 : ℝ) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hNp.le hNc (by norm_num)) hl.le).trans hlc
  have h4 : Cg ^ 2 * lambdaComb c' ^ 2 / 16 * (3 * (N : ℝ) ^ (1 / 3 : ℝ)) ≤
      Cg ^ 2 * 3 / 16 * lambdaComb c' := by
    calc Cg ^ 2 * lambdaComb c' ^ 2 / 16 * (3 * (N : ℝ) ^ (1 / 3 : ℝ))
        = Cg ^ 2 * 3 / 16 * lambdaComb c' * (lambdaComb c' * (N : ℝ) ^ (1 / 3 : ℝ)) := by ring
      _ ≤ Cg ^ 2 * 3 / 16 * lambdaComb c' * 1 := by gcongr
      _ = _ := by ring
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h5 := add_le_add (mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * (4 + π)))
    (mul_le_mul_of_nonneg_left (h2.trans h4) (by norm_num : (0 : ℝ) ≤ 24))
  refine h5.trans (le_of_eq ?_)
  ring


lemma exp_le_one_add_two_mul {S : ℝ} (h0 : 0 ≤ S) (h1 : S ≤ 1 / 2) : Real.exp S ≤ 1 + 2 * S := by
  have h := Real.add_one_le_exp (-S)
  have hp := Real.exp_pos S
  have hm : Real.exp S * Real.exp (-S) = 1 := by rw [← Real.exp_add]; simp
  have : Real.exp S * (1 - S) ≤ 1 := by
    calc Real.exp S * (1 - S) ≤ Real.exp S * Real.exp (-S) := mul_le_mul_of_nonneg_left (by linarith) hp.le
      _ = 1 := hm
  nlinarith

/-- **Far band of `D_*`** (`rem:thmU`, Step 5): for every `C_I, C_mid ≥ 1`, `d ∈ [0, 1]` and `c'` beyond an
absolute threshold, `0 < B_{D_*}(x) ≤ (1 + C λ) B_ref(x)` for all real `x ≥ ξ_* + 1/2`, with `C` absolute. -/
theorem rampedFarBand : ∃ C : ℝ, 0 < C ∧ ∀ᶠ c' : ℝ in atTop, ∀ (P : RampedParams) (d : ℝ),
    0 ≤ d → d ≤ 1 → ∀ x : ℝ, xiStar + 1 / 2 ≤ x →
      0 < ‖rampedComb P d c' (x : ℂ)‖ ∧
        ‖rampedComb P d c' (x : ℂ)‖ ≤ (1 + C * lambdaComb c') * ‖refComb c' 1 (1 / 4) (x : ℂ)‖ := by
  obtain ⟨Cs, hCs, hsh⟩ := rampedShift_le
  obtain ⟨cg, Cg, c0g, hcg, hCg, hc0g, hgap⟩ := rampedGap_two_sided
  obtain ⟨C1, hC1, hsum⟩ := farBand_sum_le
  obtain ⟨_, _, hsg_ev⟩ := siteGap_eventually_le
  have hpi := Real.pi_pos
  refine ⟨2 * C1, by positivity, ?_⟩
  have hlam_ev : ∀ᶠ c' : ℝ in atTop, (Cs + Cg + C1 + 1) * lambdaComb c' ≤ 1 / 20 := by
    have ht := tendsto_lambdaComb_atTop.const_mul (Cs + Cg + C1 + 1)
    simp only [mul_zero] at ht
    exact ht.eventually_le_const (by norm_num)
  filter_upwards [eventually_ge_atTop (max c0g 10000), hlam_ev, hsum,
    refComb_eq_split_unif 1 (η₀ := 1 / 4) (by norm_num) (by norm_num), hsg_ev]
    with c' hc' hlM hS hsplit ⟨hgap_k, _, _, hgap_1⟩ P d hd hd1 x hx
  have hc'0 : 0 < c' := lt_of_lt_of_le (by positivity) hc'
  have hc'1 : 10000 ≤ c' := (le_max_right _ _).trans hc'
  have hcg' : c0g ≤ c' := (le_max_left _ _).trans hc'
  have hl := lambdaComb_pos' hc'0
  have hxs := xiStar_pos
  have hx0 : 0 < x := by linarith
  set N := nCap P c' + 6 with hN
  have hN1 : 1 ≤ N := by omega
  have hNle : (N : ℝ) ≤ 37 / 1000 * c' := by
    have := nCap_le P hc'1
    rw [hN]; push_cast; linarith
  have hCsl : Cs * lambdaComb c' ≤ 1 / 20 := by nlinarith
  have hCgl : Cg * lambdaComb c' ≤ 1 / 20 := by nlinarith
  have hC1l : C1 * lambdaComb c' ≤ 1 / 20 := by nlinarith
  have hkr : ∀ k : ℕ, 1 ≤ k → (1 : ℝ) ≤ k := fun k hk => by exact_mod_cast hk
  have hchi : ∀ k : ℕ, 1 ≤ k → k ≤ N →
      xiStar ≤ chiQuantile c' (k : ℝ) ∧ chiQuantile c' (k : ℝ) ≤ xiStar + 1 / 5 := by
    intro k hk hkN
    have h1 := hkr k hk
    refine ⟨(chiQuantile_spec hc'0 (by linarith)).1, ?_⟩
    have hkN' : (k : ℝ) ≤ N := by exact_mod_cast hkN
    have := siteRadius_le_fifth hc'0 (by linarith : 1 / 4 ≤ (k : ℝ)) (by linarith)
    unfold siteRadius at this
    linarith
  have hdelta : ∀ k : ℕ, 1 ≤ k →
      |designSite c' (rampedSigma d c') k - chiQuantile c' (k : ℝ)| ≤ 1 / 20 := by
    intro k hk
    refine (hsh c' hc'0 d hd hd1 k hk).trans ?_
    have h1 := hkr k hk
    have : (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num)
    calc Cs * lambdaComb c' * (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ Cs * lambdaComb c' * 1 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ 1 / 20 := by linarith
  have hsite : ∀ k : ℕ, 1 ≤ k → k ≤ N →
      xiStar ≤ designSite c' (rampedSigma d c') k ∧ designSite c' (rampedSigma d c') k ≤ xiStar + 1 / 4 := by
    intro k hk hkN
    refine ⟨?_, ?_⟩
    · unfold designSite
      have := mul_nonneg hl.le (rampedSigma_nonneg hc'0 hd hk)
      linarith
    · have h1 := (abs_le.1 (hdelta k hk)).2
      have h2 := (hchi k hk hkN).2
      linarith
  have hgk_le : ∀ k : ℕ, 1 ≤ k → k ≤ N → siteGap c' k ≤ 1 / 4 := by
    intro k hk hkN
    have h1 := hkr k hk
    refine ((hgap P c' hcg' k hk (by omega)).2).trans ?_
    have : (k : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num)
    calc Cg * lambdaComb c' * (k : ℝ) ^ (-(1 / 3 : ℝ)) ≤ Cg * lambdaComb c' * 1 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ 1 / 4 := by linarith
  have hgk_all : ∀ k : ℕ, 1 ≤ k → siteGap c' k ≤ 1 / 2 := fun k hk => (hgap_k k hk).trans hgap_1
  -- the tail
  have hq_tail : ∀ m : ℕ, 0 < pairModQ c' (1 / 4) x (N + 1 + m) := by
    intro m
    unfold pairModQ
    have hk1 : 1 ≤ N + 1 + m := by omega
    have h1 := hkr _ hk1
    refine blaschkePairQ_pos_of (xiStar_pos.le.trans (chiQuantile_spec hc'0 (by push_cast at h1 ⊢; linarith)).1)
      hx0 (by have := siteGap_nonneg hc'0 hk1; positivity) ?_ (Or.inr (mul_pos (by norm_num) (siteGap_pos' hc'0 hk1)))
    have := hgk_all _ hk1
    linarith
  have hN_ne : chiQuantile c' (N : ℝ) ≠ x := by
    have := (hchi N hN1 le_rfl).2
    intro h; linarith
  have hε_all : ∀ k : ℕ, 1 ≤ k → |1 / 4 * siteGap c' k| ≤ 1 / 8 := by
    intro k hk
    have := hgk_all k hk
    have := siteGap_nonneg hc'0 hk
    rw [abs_of_nonneg (by positivity)]
    linarith
  have ht := combTail_norm_pos hc'0 hx0.le hN1 hgap_1 hN_ne hq_tail hε_all
  set t := ‖combTail c' N (1 / 4) (x : ℂ)‖ with htdef
  -- the two moduli
  have hb : |((x : ℂ)).im| < 7 / 8 := by simp
  have hs1 := hsite 1 le_rfl hN1
  have hc1 := hchi 1 le_rfl hN1
  have hD : ‖rampedComb P d c' (x : ℂ)‖ =
      (Real.tanh (π * (x - designSite c' (rampedSigma d c') 1) / 2) *
        Real.tanh (π * (x + designSite c' (rampedSigma d c') 1) / 2)) *
      (∏ i ∈ Finset.range (N - 1), blaschkePairQ (designSite c' (rampedSigma d c') (1 + 1 + i))
        (rampedEps P c' (1 + 1 + i)) x) * t := by
    unfold rampedComb designComb
    rw [norm_mul, norm_mul, norm_prod, norm_blaschkeT_real (y := designSite c' (rampedSigma d c') 1) (by linarith [hs1.1])
        (by linarith [hs1.2])]
    rfl
  have hc1x : chiQuantile c' ((1 : ℕ) : ℝ) < x := lt_of_le_of_lt hc1.2 (by linarith)
  have hR : ‖refComb c' 1 (1 / 4) (x : ℂ)‖ =
      (Real.tanh (π * (x - chiQuantile c' ((1 : ℕ) : ℝ)) / 2) *
        Real.tanh (π * (x + chiQuantile c' ((1 : ℕ) : ℝ)) / 2)) *
      (∏ i ∈ Finset.range (N - 1), blaschkePairQ (chiQuantile c' ((1 + 1 + i : ℕ) : ℝ))
        (1 / 4 * siteGap c' (1 + 1 + i)) x) * t := by
    rw [hsplit N hN1 hb, norm_mul, norm_mul, norm_prod,
      norm_blaschkeT_real (y := chiQuantile c' ((1 : ℕ) : ℝ)) (by linarith [hc1.1])
        hc1x]
    rfl
  have hT := tanhProd_anti (x := x) (by linarith [hc1.1] : 0 ≤ chiQuantile c' ((1 : ℕ) : ℝ))
    (rampedSite_first_ge hc'0 hd)
  have hT' : 0 < Real.tanh (π * (x - designSite c' (rampedSigma d c') 1) / 2) *
      Real.tanh (π * (x + designSite c' (rampedSigma d c') 1) / 2) :=
    tanh_prod_pos_of_lt (by linarith [hs1.1]) (by linarith [hs1.2])
  have hpair : ∀ i ∈ Finset.range (N - 1),
      blaschkePairQ (designSite c' (rampedSigma d c') (1 + 1 + i)) (rampedEps P c' (1 + 1 + i)) x ≤
        blaschkePairQ (chiQuantile c' ((1 + 1 + i : ℕ) : ℝ)) (1 / 4 * siteGap c' (1 + 1 + i)) x *
          Real.exp (2 * (4 + π) * |designSite c' (rampedSigma d c') (1 + 1 + i) -
              chiQuantile c' ((1 + 1 + i : ℕ) : ℝ)| + 24 * (1 / 4 * siteGap c' (1 + 1 + i)) ^ 2) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hk1 : 1 ≤ 1 + 1 + i := by omega
    have hkN : 1 + 1 + i ≤ N := by omega
    have hg0 := siteGap_nonneg hc'0 hk1
    exact pair_ratio_le (hchi _ hk1 hkN).1 (hsite _ hk1 hkN).1 hx (by linarith [(hchi _ hk1 hkN).2])
      (hsite _ hk1 hkN).2 (mul_nonneg (rampedEta_nonneg P c' _) hg0)
      (mul_le_mul_of_nonneg_right (rampedEta_le P c' _) hg0)
      (by have := hgk_le _ hk1 hkN; linarith)
  have hq'pos : ∀ i ∈ Finset.range (N - 1), 0 <
      blaschkePairQ (designSite c' (rampedSigma d c') (1 + 1 + i)) (rampedEps P c' (1 + 1 + i)) x := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hk1 : 1 ≤ 1 + 1 + i := by omega
    have hkN : 1 + 1 + i ≤ N := by omega
    have hg0 := siteGap_nonneg hc'0 hk1
    refine blaschkePairQ_pos (by linarith [(hsite _ hk1 hkN).1]) hx0.le
      (by have := (hsite _ hk1 hkN).2; intro h; linarith) (mul_nonneg (rampedEta_nonneg P c' _) hg0) ?_
    unfold rampedEps
    have := rampedEta_le P c' (1 + 1 + i)
    have := hgk_le _ hk1 hkN
    nlinarith [rampedEta_nonneg P c' (1 + 1 + i)]
  have hQ : ∏ i ∈ Finset.range (N - 1),
      blaschkePairQ (designSite c' (rampedSigma d c') (1 + 1 + i)) (rampedEps P c' (1 + 1 + i)) x ≤
      (∏ i ∈ Finset.range (N - 1), blaschkePairQ (chiQuantile c' ((1 + 1 + i : ℕ) : ℝ))
        (1 / 4 * siteGap c' (1 + 1 + i)) x) *
        Real.exp (∑ k ∈ Finset.Ioc 1 N, (2 * (4 + π) * |designSite c' (rampedSigma d c') k -
          chiQuantile c' (k : ℝ)| + 24 * (1 / 4 * siteGap c' k) ^ 2)) := by
    have hsr := sum_range_shift (fun k => 2 * (4 + π) * |designSite c' (rampedSigma d c') k -
          chiQuantile c' (k : ℝ)| + 24 * (1 / 4 * siteGap c' k) ^ 2) 1 (N - 1)
    rw [show 1 + (N - 1) = N by omega] at hsr
    rw [← hsr, Real.exp_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun i hi => (hq'pos i hi).le) hpair
  have hSb := hS P d hd hd1
  have hS0 : 0 ≤ ∑ k ∈ Finset.Ioc 1 N, (2 * (4 + π) *
      |designSite c' (rampedSigma d c') k - chiQuantile c' (k : ℝ)| + 24 * (1 / 4 * siteGap c' k) ^ 2) :=
    Finset.sum_nonneg fun k _ => by positivity
  generalize (∑ k ∈ Finset.Ioc 1 N, (2 * (4 + π) *
      |designSite c' (rampedSigma d c') k - chiQuantile c' (k : ℝ)| + 24 * (1 / 4 * siteGap c' k) ^ 2)) = S
    at hQ hSb hS0
  have hexp := exp_le_one_add_two_mul hS0 (by linarith)
  have hQ0 : 0 < ∏ i ∈ Finset.range (N - 1),
      blaschkePairQ (designSite c' (rampedSigma d c') (1 + 1 + i)) (rampedEps P c' (1 + 1 + i)) x :=
    Finset.prod_pos hq'pos
  have hQnn : 0 ≤ ∏ i ∈ Finset.range (N - 1), blaschkePairQ (chiQuantile c' ((1 + 1 + i : ℕ) : ℝ))
      (1 / 4 * siteGap c' (1 + 1 + i)) x := Finset.prod_nonneg fun i _ => by
    unfold blaschkePairQ; positivity
  have hRn : 0 ≤ ‖refComb c' 1 (1 / 4) (x : ℂ)‖ := norm_nonneg _
  refine ⟨?_, ?_⟩
  · rw [hD]; positivity
  · rw [hD]
    have hTQ := mul_le_mul hT hQ hQ0.le (by linarith [hT'])
    have h1 := mul_le_mul_of_nonneg_right hTQ ht.le
    have h2 : 1 + 2 * S ≤ 1 + 2 * C1 * lambdaComb c' := by linarith
    calc _ ≤ _ := h1
      _ = Real.exp S * ‖refComb c' 1 (1 / 4) (x : ℂ)‖ := by rw [hR]; ring
      _ ≤ (1 + 2 * S) * ‖refComb c' 1 (1 / 4) (x : ℂ)‖ := mul_le_mul_of_nonneg_right hexp hRn
      _ ≤ (1 + 2 * C1 * lambdaComb c') * ‖refComb c' 1 (1 / 4) (x : ℂ)‖ :=
          mul_le_mul_of_nonneg_right h2 hRn


/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.pair_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pair_ratio_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.combTail_norm_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combTail_norm_pos

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.farBand_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms farBand_sum_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedFarBand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedFarBand

end FormalResearch.ModularBootstrap.Upper.Ramped
