module

public import FormalResearch.ModularBootstrap.Upper.Holes.Holes

/-!
# Hole Limit, Reference Floor, and Band Overshoot (`cmb:K5`)

Formalizes Lemma K5 (`cmb:K5`) of `CFT/modular_bootstrap/paper/comb_estimates.tex`
(lines 210--240):

* `h0Comb`: real-axis reference comb test $h_0^{\mathrm{ref}(f)}(x) = \operatorname{sech}^2(\pi x/2)\,\operatorname{Re} B_{\mathrm{ref}}^{(f)}(x)$.
* `levComb`: comb reference level $\mathrm{Lev}^{(f)}(x) = 4\operatorname{sech}^2(\pi x/2)\exp(-c' L(x) + c' P^{(f)}(x) + J_{\mathrm{end}}^{(f)}(x))$.
* `muHole`: infimal hole factor $\mu_j(\eta_0) = \inf_{u \in [0,1]} \tfrac{1}{4}\exp(H_j(u, \eta_0))$.
* `refComb_re_nonneg_of_gt`: on $x > \chi_f$, $B_{\mathrm{ref}}^{(f)}(x) \in \mathbb{R}_{\ge 0}$, so $\operatorname{Re} B_{\mathrm{ref}}^{(f)}(x) = \|B_{\mathrm{ref}}^{(f)}(x)\|$.
* `muHole_four_quarter_gt`: $\mu_4(\tfrac14) = \mu_4 > \tfrac{7}{10}$.
* `muHole_one_ge`: $\mu_1(\eta_0) \ge \tfrac{1}{16}\eta_0^2$ for $\eta_0 \in [0, \tfrac14]$.
* `hole_limit_K5`: uniform hole approximation $|\mathcal{H}_{n,j}(x;\eta_0) - H_j(u,\eta_0)| \le C(n^{-1} + \ell_n)$.
* `hole_floor_K5`: reference floor $h_0^{\mathrm{ref}(f)}(x) / \mathrm{Lev}^{(f)}(x) \ge \mu_j(\eta_0)(1 - C(n^{-1} + \ell_n))e^{-2\mathcal{E}_{\mathrm{left}}}$.
* `band_overshoot_K5`: $j=1$ overshoot bound $h_0^{\mathrm{ref}(f)}(x) e^{c' L(x)} \ge c_T \operatorname{sech}^2(\pi x/2) \bigl(\tfrac{2}{\pi(x - \xi_*)}\bigr)^{2n_1}$.
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Holes

open FormalResearch.ModularBootstrap.Upper.Comb

/-! ### Section 1: Reference level, real-axis positivity, and `muHole` bounds -/

/-- Real-axis reference comb test $h_0^{\mathrm{ref}(f)}(x) = \operatorname{sech}^2(\pi x / 2)\,\operatorname{Re} B_{\mathrm{ref}}^{(f)}(x)$. -/
noncomputable def h0Comb (c' : ℝ) (f : ℕ) (η₀ x : ℝ) : ℝ :=
  (1 / Real.cosh (π * x / 2) ^ 2) * (refComb c' f η₀ (x : ℂ)).re

/-- Comb reference level $\mathrm{Lev}^{(f)}(x) = 4\operatorname{sech}^2(\pi x / 2)\exp(-c' L(x) + c' P^{(f)}(x) + J_{\mathrm{end}}^{(f)}(x))$. -/
noncomputable def levComb (c' : ℝ) (f : ℕ) (x : ℝ) : ℝ :=
  4 * (1 / Real.cosh (π * x / 2) ^ 2) *
    Real.exp (-c' * slitL x + c' * combPf c' f x + jEndComb c' x f)

/-- Infimal linearized hole factor $\mu_j(\eta_0) = \inf_{u \in [0,1]} \tfrac{1}{4}\exp(H_j(u, \eta_0))$. -/
noncomputable def muHole (j : ℕ) (η₀ : ℝ) : ℝ :=
  sInf ((fun u : ℝ => (1 / 4 : ℝ) * Real.exp (holeModel j u η₀)) '' Icc 0 1)

private lemma tanh_conj_complex (w : ℂ) :
    Complex.tanh (star w) = star (Complex.tanh w) := by
  change Complex.tanh ((starRingEnd ℂ) w) = (starRingEnd ℂ) (Complex.tanh w)
  rw [Complex.tanh_eq_sinh_div_cosh, Complex.tanh_eq_sinh_div_cosh,
    map_div₀, Complex.sinh_conj, Complex.cosh_conj]

private lemma blaschkeT_conj_real (χ ε x : ℝ) :
    blaschkeT ((χ : ℂ) - (ε : ℂ) * Complex.I) (x : ℂ) =
      star (blaschkeT ((χ : ℂ) + (ε : ℂ) * Complex.I) (x : ℂ)) := by
  unfold blaschkeT
  have h1 : (π : ℂ) * ((x : ℂ) - ((χ : ℂ) - (ε : ℂ) * Complex.I)) / 2 =
      star ((π : ℂ) * ((x : ℂ) - ((χ : ℂ) + (ε : ℂ) * Complex.I)) / 2) := by
    change _ = (starRingEnd ℂ) _
    simp only [map_div₀, map_mul, map_sub, map_add, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  have h2 : (π : ℂ) * ((x : ℂ) + ((χ : ℂ) - (ε : ℂ) * Complex.I)) / 2 =
      star ((π : ℂ) * ((x : ℂ) + ((χ : ℂ) + (ε : ℂ) * Complex.I)) / 2) := by
    change _ = (starRingEnd ℂ) _
    simp only [map_div₀, map_mul, map_add, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  rw [h1, h2, tanh_conj_complex, tanh_conj_complex]
  change _ = (starRingEnd ℂ) _
  rw [map_mul]
  rfl

private lemma blaschkeT_pair_real (χ ε x : ℝ) :
    blaschkeT ((χ : ℂ) + (ε : ℂ) * Complex.I) (x : ℂ) *
        blaschkeT ((χ : ℂ) - (ε : ℂ) * Complex.I) (x : ℂ) =
      ((blaschkePairQ χ ε x : ℝ) : ℂ) := by
  rw [blaschkeT_conj_real]
  set z : ℂ := blaschkeT ((χ : ℂ) + (ε : ℂ) * Complex.I) (x : ℂ)
  have hz : z * star z = ((Complex.normSq z : ℝ) : ℂ) := by
    rw [mul_comm, Complex.normSq_eq_conj_mul_self]
    rfl
  rw [hz, Complex.normSq_eq_norm_sq]
  have hp : blaschkePairQ χ ε x = ‖z‖ ^ 2 := by
    unfold blaschkePairQ
    have hconj : ‖blaschkeT ((χ : ℂ) - (ε : ℂ) * Complex.I) (x : ℂ)‖ = ‖z‖ := by
      rw [blaschkeT_conj_real]
      exact Complex.norm_conj z
    dsimp [z] at hconj ⊢
    rw [norm_mul, hconj, sq]
  rw [hp]

/-- For $x > \chi_f$, $B_{\mathrm{ref}}^{(f)}(x)$ lies in $\mathbb{R}_{\ge 0}$, so
$\operatorname{Re} B_{\mathrm{ref}}^{(f)}(x) = \|B_{\mathrm{ref}}^{(f)}(x)\|$ and $h_0^{\mathrm{ref}(f)}(x) \ge 0$. -/
theorem refComb_re_nonneg_of_gt {c' η₀ x : ℝ} (hc' : 0 < c') (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4)
    (hgap : siteGap c' 1 ≤ 1 / 2) {f : ℕ} (hf : 1 ≤ f) (hx : chiQuantile c' f < x) :
    (refComb c' f η₀ (x : ℂ)).im = 0 ∧ 0 ≤ (refComb c' f η₀ (x : ℂ)).re ∧
      (refComb c' f η₀ (x : ℂ)).re = ‖refComb c' f η₀ (x : ℂ)‖ ∧
      0 ≤ h0Comb c' f η₀ x ∧
      h0Comb c' f η₀ x = (1 / Real.cosh (π * x / 2) ^ 2) * ‖refComb c' f η₀ (x : ℂ)‖ := by
  let χ := fun m : ℕ => chiQuantile c' (f + 1 + m : ℕ)
  let ε := fun m : ℕ => η₀ * siteGap c' (f + 1 + m)
  let P : ℕ → ℂ := fun m =>
    blaschkeT ((χ m : ℂ) + (ε m : ℂ) * Complex.I) (x : ℂ) *
      blaschkeT ((χ m : ℂ) - (ε m : ℂ) * Complex.I) (x : ℂ)
  have hχ_nn : ∀ m : ℕ, 0 ≤ χ m := fun m => by
    have hm1 : (1 : ℝ) ≤ ((f + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ f + 1 + m)
    exact xiStar_pos.le.trans (chiQuantile_spec hc' (by linarith)).1
  have hε_bd : ∀ m : ℕ, |ε m| ≤ 1 / 8 := fun m => by
    dsimp [ε]
    have hgk : siteGap c' (f + 1 + m) ≤ siteGap c' 1 := by
      rcases eq_or_lt_of_le (by omega : 1 ≤ f + 1 + m) with h1 | hgt
      · rw [← h1]
      · have hanti := (siteGap_strictAnti hc').antitone (show 0 ≤ f + 1 + m - 1 by omega)
        have heq : (f + 1 + m - 1) + 1 = f + 1 + m := by omega
        rwa [heq] at hanti
    have hm1 : (1 : ℝ) ≤ ((f + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ f + 1 + m)
    have hgk_nn : 0 ≤ siteGap c' (f + 1 + m) := by
      unfold siteGap
      exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn
        (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith)) (by linarith))
    rw [abs_of_nonneg (mul_nonneg hη₀0 hgk_nn)]
    nlinarith
  have hsum := summable_exp_neg_pi_chiQuantile hc' f
  have hhasProd := (comb_pairProd_hasProdLocallyUniformlyOn χ ε hχ_nn hε_bd hsum).hasProd
    (by simp : (x : ℂ) ∈ {b : ℂ | |b.im| < 7 / 8})
  have hP_eq : ∀ m : ℕ, P m = ((pairModQ c' η₀ x (f + 1 + m) : ℝ) : ℂ) := fun m => by
    dsimp [P, χ, ε]; unfold pairModQ; exact blaschkeT_pair_real _ _ _
  have hq_nn : ∀ m : ℕ, 0 ≤ pairModQ c' η₀ x (f + 1 + m) := fun m => by
    unfold pairModQ blaschkePairQ; positivity
  have hpart : ∀ s : Finset ℕ,
      (∏ m ∈ s, P m).im = 0 ∧ 0 ≤ (∏ m ∈ s, P m).re := fun s => by
    have h_eq : ∏ m ∈ s, P m = ((∏ m ∈ s, pairModQ c' η₀ x (f + 1 + m) : ℝ) : ℂ) := by
      rw [Complex.ofReal_prod]
      exact Finset.prod_congr rfl fun m _ => hP_eq m
    rw [h_eq, Complex.ofReal_im, Complex.ofReal_re]
    exact ⟨rfl, Finset.prod_nonneg fun m _ => hq_nn m⟩
  have him_prod : (∏' m : ℕ, P m).im = 0 :=
    tendsto_nhds_unique (Complex.continuous_im.continuousAt.tendsto.comp hhasProd)
      (tendsto_const_nhds.congr (fun s => (hpart s).1.symm))
  have hre_prod : 0 ≤ (∏' m : ℕ, P m).re :=
    ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp hhasProd)
      (Eventually.of_forall fun s => (hpart s).2)
  have hf1 : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hχf_nn : 0 ≤ chiQuantile c' f := xiStar_pos.le.trans (chiQuantile_spec hc' (by linarith)).1
  have hT_real : blaschkeT (chiQuantile c' f : ℂ) (x : ℂ) =
      ((Real.tanh (π * (x - chiQuantile c' f) / 2) *
        Real.tanh (π * (x + chiQuantile c' f) / 2) : ℝ) : ℂ) := by
    unfold blaschkeT
    have hc1 : Complex.tanh ((π : ℂ) * ((x : ℂ) - (chiQuantile c' f : ℂ)) / 2) =
        ((Real.tanh (π * (x - chiQuantile c' f) / 2) : ℝ) : ℂ) := by
      have h1 : Complex.tanh ((π * (x - chiQuantile c' f) / 2 : ℝ) : ℂ) =
          ((Real.tanh (π * (x - chiQuantile c' f) / 2) : ℝ) : ℂ) := by
        rw [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
          ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, Complex.ofReal_div]
      rw [← h1]; congr 1; push_cast; ring
    have hc2 : Complex.tanh ((π : ℂ) * ((x : ℂ) + (chiQuantile c' f : ℂ)) / 2) =
        ((Real.tanh (π * (x + chiQuantile c' f) / 2) : ℝ) : ℂ) := by
      have h1 : Complex.tanh ((π * (x + chiQuantile c' f) / 2 : ℝ) : ℂ) =
          ((Real.tanh (π * (x + chiQuantile c' f) / 2) : ℝ) : ℂ) := by
        rw [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
          ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, Complex.ofReal_div]
      rw [← h1]; congr 1; push_cast; ring
    rw [hc1, hc2, Complex.ofReal_mul]
  have hT_pos : 0 < Real.tanh (π * (x - chiQuantile c' f) / 2) *
      Real.tanh (π * (x + chiQuantile c' f) / 2) := by
    have h1 : 0 < Real.tanh (π * (x - chiQuantile c' f) / 2) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr (by nlinarith [Real.pi_pos])) (Real.cosh_pos _)
    have h2 : 0 < Real.tanh (π * (x + chiQuantile c' f) / 2) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr (by nlinarith [Real.pi_pos])) (Real.cosh_pos _)
    exact mul_pos h1 h2
  have href_eq : refComb c' f η₀ (x : ℂ) =
      blaschkeT (chiQuantile c' f : ℂ) (x : ℂ) * (∏' m : ℕ, P m) := by
    unfold refComb; rfl
  have him_ref : (refComb c' f η₀ (x : ℂ)).im = 0 := by
    rw [href_eq, hT_real, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, him_prod,
      mul_zero, zero_mul, add_zero]
  have hre_ref : 0 ≤ (refComb c' f η₀ (x : ℂ)).re := by
    rw [href_eq, hT_real]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg hT_pos.le hre_prod
  have hnorm_ref : (refComb c' f η₀ (x : ℂ)).re = ‖refComb c' f η₀ (x : ℂ)‖ := by
    have h_ofReal : refComb c' f η₀ (x : ℂ) = (((refComb c' f η₀ (x : ℂ)).re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simp [him_ref]
    conv_rhs => rw [h_ofReal]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hre_ref]
  have h0_nn : 0 ≤ h0Comb c' f η₀ x := by
    unfold h0Comb
    exact mul_nonneg (div_nonneg one_pos.le (sq_nonneg _)) hre_ref
  have h0_norm : h0Comb c' f η₀ x = (1 / Real.cosh (π * x / 2) ^ 2) * ‖refComb c' f η₀ (x : ℂ)‖ := by
    unfold h0Comb; rw [hnorm_ref]
  exact ⟨him_ref, hre_ref, hnorm_ref, h0_nn, h0_norm⟩

/-- Exact comparison with Lemma `A_II`: $\mu_4(\tfrac14) = \mu_4 > \tfrac{7}{10}$. -/
theorem muHole_four_quarter_gt : (7 / 10 : ℝ) < muHole 4 (1 / 4) := by
  have h_eq : muHole 4 (1 / 4) = muFour := by
    unfold muHole muFour
    apply le_antisymm
    · refine csInf_le ⟨0, by rintro _ ⟨u, _, rfl⟩; positivity⟩ ?_
      refine ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
      dsimp only
      rw [holeModel_quarter_eq_hAII, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    · refine le_csInf ⟨_, ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩⟩ ?_
      rintro y ⟨u, hu, rfl⟩
      dsimp only
      rw [holeModel_quarter_eq_hAII]
      have habs : |u - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hmin := (hAII_min_at_half (Or.inr rfl) habs).1
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hmin) (by norm_num)
  rw [h_eq]
  exact muFour_gt

/-- Lower bound for the $j = 1$ hole constant: $\mu_1(\eta_0) \ge \tfrac{1}{16}\eta_0^2$
for all $\eta_0 \in [0, \tfrac14]$. -/
theorem muHole_one_ge {η₀ : ℝ} (hη₀0 : 0 ≤ η₀) (_hη₀1 : η₀ ≤ 1 / 4) :
    (1 / 16 : ℝ) * η₀ ^ 2 ≤ muHole 1 η₀ := by
  unfold muHole
  refine le_csInf ⟨_, ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩⟩ ?_
  rintro _ ⟨u, hu, rfl⟩
  have h_int_nonpos : ∫ s in (-(1 : ℝ) + 1 / 2)..((1 : ℝ) + 1 / 2), Real.log |u - s| ≤ 0 := by
    have hsplit : ∫ s in (-(1 / 2 : ℝ))..(3 / 2 : ℝ), Real.log |u - s| =
        (∫ s in (-(1 / 2 : ℝ))..u, Real.log |u - s|) +
          ∫ s in u..(3 / 2 : ℝ), Real.log |u - s| := by
      have hi1 : IntervalIntegrable (fun s => Real.log |u - s|) volume (-(1 / 2 : ℝ)) u := by
        have hcomp : IntervalIntegrable (fun s => Real.log (u - s)) volume (-(1 / 2 : ℝ)) u := by
          simpa using (intervalIntegral.intervalIntegrable_log' (a := u - (-(1 / 2 : ℝ))) (b := 0)).comp_sub_left u
        have hac : -(1 / 2 : ℝ) ≤ u := by linarith [hu.1]
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hac] at hcomp ⊢
        exact hcomp.congr_fun (fun s hs => by rw [abs_of_nonneg (sub_nonneg.mpr hs.2)]) measurableSet_Ioc
      have hi2 : IntervalIntegrable (fun s => Real.log |u - s|) volume u (3 / 2 : ℝ) := by
        have hcomp : IntervalIntegrable (fun s => Real.log (s - u)) volume u (3 / 2 : ℝ) := by
          simpa using (intervalIntegral.intervalIntegrable_log' (a := 0) (b := (3 / 2 : ℝ) - u)).comp_sub_right u
        have hcb : u ≤ (3 / 2 : ℝ) := by linarith [hu.2]
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hcb] at hcomp ⊢
        exact hcomp.congr_fun
          (fun s hs => by rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hs.1.le)]) measurableSet_Ioc
      exact (intervalIntegral.integral_add_adjacent_intervals hi1 hi2).symm
    have hleft : ∫ s in (-(1 / 2 : ℝ))..u, Real.log |u - s| =
        (u + 1 / 2) * Real.log (u + 1 / 2) - (u + 1 / 2) := by
      have hcon : ∫ s in (-(1 / 2 : ℝ))..u, Real.log |u - s| =
          ∫ s in (-(1 / 2 : ℝ))..u, Real.log (u - s) := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards with s hs
        rw [Set.uIoc_of_le (by linarith [hu.1])] at hs
        rw [abs_of_nonneg (sub_nonneg.mpr hs.2)]
      rw [hcon, intervalIntegral.integral_comp_sub_left Real.log u, integral_log]
      simp only [sub_zero, zero_mul, sub_self, add_zero]
      ring_nf
    have hright : ∫ s in u..(3 / 2 : ℝ), Real.log |u - s| =
        (3 / 2 - u) * Real.log (3 / 2 - u) - (3 / 2 - u) := by
      have hcon : ∫ s in u..(3 / 2 : ℝ), Real.log |u - s| =
          ∫ s in u..(3 / 2 : ℝ), Real.log (s - u) := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards with s hs
        rw [Set.uIoc_of_le (by linarith [hu.2])] at hs
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hs.1.le)]
      rw [hcon, intervalIntegral.integral_comp_sub_right Real.log u, sub_self, integral_log]
      simp only [zero_mul, sub_zero, add_zero]
    have h_rew : ∫ s in (-(1 : ℝ) + 1 / 2)..((1 : ℝ) + 1 / 2), Real.log |u - s| =
        ∫ s in (-(1 / 2 : ℝ))..(3 / 2 : ℝ), Real.log |u - s| := by
      congr 1 <;> ring
    rw [h_rew, hsplit, hleft, hright]
    have hl1 : Real.log (u + 1 / 2) ≤ 1 := by
      have hp : 0 < u + 1 / 2 := by linarith [hu.1]
      have hle : u + 1 / 2 ≤ Real.exp 1 := by
        have := Real.exp_one_gt_d9
        linarith [hu.2]
      exact (Real.log_le_log hp hle).trans (by rw [Real.log_exp])
    have hl2 : Real.log (3 / 2 - u) ≤ 1 := by
      have hp : 0 < 3 / 2 - u := by linarith [hu.2]
      have hle : 3 / 2 - u ≤ Real.exp 1 := by
        have := Real.exp_one_gt_d9
        linarith [hu.1]
      exact (Real.log_le_log hp hle).trans (by rw [Real.log_exp])
    have hw1 : 0 ≤ u + 1 / 2 := by linarith [hu.1]
    have hw2 : 0 ≤ 3 / 2 - u := by linarith [hu.2]
    nlinarith
  have hprod_ge : (1 / 4 : ℝ) * η₀ ^ 2 ≤ ((u - 1) ^ 2 + η₀ ^ 2) * (u ^ 2 + η₀ ^ 2) := by
    by_cases hu_half : u ≤ 1 / 2
    · have h1 : (1 / 4 : ℝ) ≤ (u - 1) ^ 2 + η₀ ^ 2 := by nlinarith [sq_nonneg η₀]
      have h2 : η₀ ^ 2 ≤ u ^ 2 + η₀ ^ 2 := by nlinarith [sq_nonneg u]
      exact mul_le_mul h1 h2 (sq_nonneg η₀) (by positivity)
    · have h1 : (1 / 4 : ℝ) ≤ u ^ 2 + η₀ ^ 2 := by nlinarith [sq_nonneg η₀]
      have h2 : η₀ ^ 2 ≤ (u - 1) ^ 2 + η₀ ^ 2 := by nlinarith [sq_nonneg (u - 1)]
      calc (1 / 4 : ℝ) * η₀ ^ 2 = η₀ ^ 2 * (1 / 4 : ℝ) := by ring
        _ ≤ ((u - 1) ^ 2 + η₀ ^ 2) * (u ^ 2 + η₀ ^ 2) :=
            mul_le_mul h2 h1 (by norm_num) (by positivity)
  have hexp_ge : (1 / 4 : ℝ) * η₀ ^ 2 ≤ Real.exp (holeModel 1 u η₀) := by
    unfold holeModel
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, sub_zero, add_zero,
      Nat.cast_one]
    by_cases hη0 : η₀ = 0
    · subst hη0; simp; exact (Real.exp_pos _).le
    · have hη_pos : 0 < η₀ := lt_of_le_of_ne hη₀0 (Ne.symm hη0)
      have hpos : 0 < (1 / 4 : ℝ) * η₀ ^ 2 := by positivity
      calc (1 / 4 : ℝ) * η₀ ^ 2
          = Real.exp (Real.log ((1 / 4 : ℝ) * η₀ ^ 2)) := (Real.exp_log hpos).symm
        _ ≤ Real.exp (Real.log (((u - 1) ^ 2 + η₀ ^ 2) * (u ^ 2 + η₀ ^ 2)) -
              2 * ∫ s in (-(1 : ℝ) + 1 / 2)..((1 : ℝ) + 1 / 2), Real.log |u - s|) :=
            Real.exp_le_exp.mpr (by linarith [Real.log_le_log hpos hprod_ge])
  linarith

/-! ### Section 2: Elementary hyperbolic, logarithm, and quantile linearization estimates -/

private lemma log_cosh_le_half_sq (z : ℝ) : Real.log (Real.cosh z) ≤ z ^ 2 / 2 := by
  have h_nn : ∀ w : ℝ, 0 ≤ w → Real.log (Real.cosh w) ≤ w ^ 2 / 2 := fun w hw => by
    let g : ℝ → ℝ := fun t => t ^ 2 / 2 - Real.log (Real.cosh t)
    have hderiv : ∀ t : ℝ, HasDerivAt g (t - Real.tanh t) t := fun t => by
      have h1 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
        simpa using ((hasDerivAt_id t).pow 2).div_const 2
      have h2 : HasDerivAt (fun s : ℝ => Real.log (Real.cosh s)) (Real.sinh t / Real.cosh t) t :=
        (Real.hasDerivAt_cosh t).log (Real.cosh_pos t).ne'
      rw [← Real.tanh_eq_sinh_div_cosh] at h2
      exact h1.sub h2
    have hm := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
      (fun t _ => (hderiv t).continuousAt.continuousWithinAt)
      (fun t _ => (hderiv t).differentiableAt.differentiableWithinAt)
      fun t ht => by
        rw [interior_Ici] at ht
        rw [(hderiv t).deriv]
        have hth := Real.tanh_eq_sinh_div_cosh t
        have hsh_nn : 0 ≤ Real.sinh t := Real.sinh_nonneg_iff.mpr ht.le
        have hch_ge1 : 1 ≤ Real.cosh t := Real.one_le_cosh t
        have h_sh_le : Real.sinh t ≤ t * Real.cosh t := by
          let k : ℝ → ℝ := fun s => s * Real.cosh s - Real.sinh s
          have hk : ∀ s : ℝ, HasDerivAt k (s * Real.sinh s) s := fun s => by
            have hA := (hasDerivAt_id s).mul (Real.hasDerivAt_cosh s)
            have hB := Real.hasDerivAt_sinh s
            exact (hA.sub hB).congr_deriv (by simp)
          have hkm := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
            (fun s _ => (hk s).continuousAt.continuousWithinAt)
            (fun s _ => (hk s).differentiableAt.differentiableWithinAt)
            fun s hs => by
              rw [interior_Ici] at hs
              rw [(hk s).deriv]
              exact mul_nonneg hs.le (Real.sinh_nonneg_iff.mpr hs.le)
          have h0 := hkm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht.le) ht.le
          dsimp [k] at h0; simp only [zero_mul, Real.sinh_zero, sub_self] at h0
          linarith
        rw [hth, sub_nonneg, div_le_iff₀ (Real.cosh_pos t)]
        exact h_sh_le
    have h0 := hm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hw) hw
    dsimp [g] at h0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, Real.cosh_zero,
      Real.log_one, sub_self] at h0
    linarith
  rcases le_total 0 z with hz | hz
  · exact h_nn z hz
  · have := h_nn (-z) (neg_nonneg.mpr hz)
    rwa [Real.cosh_neg, neg_sq] at this

private lemma self_le_sinh_of_nonneg {z : ℝ} (hz : 0 ≤ z) : z ≤ Real.sinh z := by
  let g : ℝ → ℝ := fun t => Real.sinh t - t
  have hd : ∀ t : ℝ, HasDerivAt g (Real.cosh t - 1) t := fun t =>
    (Real.hasDerivAt_sinh t).sub (hasDerivAt_id t)
  have hm := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
    (fun t _ => (hd t).continuousAt.continuousWithinAt)
    (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
    fun t _ => by rw [(hd t).deriv]; linarith [Real.one_le_cosh t]
  have h0 := hm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hz) hz
  dsimp [g] at h0; simp only [Real.sinh_zero, sub_self] at h0; linarith

private lemma sinh_le_add_cube_of_unit {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Real.sinh z ≤ z + z ^ 3 / 2 := by
  let f : ℝ → ℝ := fun t => t + t ^ 3 / 2 - Real.sinh t
  let f' : ℝ → ℝ := fun t => 1 + 3 / 2 * t ^ 2 - Real.cosh t
  let f'' : ℝ → ℝ := fun t => 3 * t - Real.sinh t
  have hd2 : ∀ t : ℝ, HasDerivAt f'' (3 - Real.cosh t) t := fun t => by
    have h := ((hasDerivAt_id t).const_mul 3).sub (Real.hasDerivAt_sinh t)
    exact h.congr_deriv (by simp)
  have hch1 : Real.cosh 1 ≤ 3 := by
    rw [Real.cosh_eq]
    have he1 := Real.exp_one_lt_d9
    have he2 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    linarith
  have hf''_nn : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f'' t := fun t ht => by
    have hm := monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1)
      (fun s _ => (hd2 s).continuousAt.continuousWithinAt)
      (fun s _ => (hd2 s).differentiableAt.differentiableWithinAt)
      fun s hs => by
        rw [interior_Icc] at hs
        rw [(hd2 s).deriv]
        have hcs : Real.cosh s ≤ Real.cosh 1 := by
          rw [Real.cosh_le_cosh, abs_of_nonneg hs.1.le, abs_of_nonneg zero_le_one]
          exact hs.2.le
        linarith
    have h0 := hm (left_mem_Icc.mpr zero_le_one) ht ht.1
    dsimp [f''] at h0; simp only [mul_zero, Real.sinh_zero, sub_self] at h0; exact h0
  have hd1 : ∀ t : ℝ, HasDerivAt f' (f'' t) t := fun t => by
    have h1 := ((hasDerivAt_const t (1 : ℝ)).add (((hasDerivAt_id t).pow 2).const_mul (3 / 2 : ℝ)))
    have h2 := h1.sub (Real.hasDerivAt_cosh t)
    exact h2.congr_deriv (by dsimp [f'']; simp; ring)
  have hf'_nn : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f' t := fun t ht => by
    have hm := monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1)
      (fun s _ => (hd1 s).continuousAt.continuousWithinAt)
      (fun s _ => (hd1 s).differentiableAt.differentiableWithinAt)
      fun s hs => by
        rw [interior_Icc] at hs
        rw [(hd1 s).deriv]
        exact hf''_nn s ⟨hs.1.le, hs.2.le⟩
    have h0 := hm (left_mem_Icc.mpr zero_le_one) ht ht.1
    dsimp [f'] at h0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
      Real.cosh_zero, sub_self] at h0
    exact h0
  have hd0 : ∀ t : ℝ, HasDerivAt f (f' t) t := fun t => by
    have h1 := (hasDerivAt_id t).add (((hasDerivAt_id t).pow 3).div_const 2)
    have h2 := h1.sub (Real.hasDerivAt_sinh t)
    exact h2.congr_deriv (by dsimp [f']; simp; ring)
  have hm := monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1)
    (fun s _ => (hd0 s).continuousAt.continuousWithinAt)
    (fun s _ => (hd0 s).differentiableAt.differentiableWithinAt)
    fun s hs => by
      rw [interior_Icc] at hs
      rw [(hd0 s).deriv]
      exact hf'_nn s ⟨hs.1.le, hs.2.le⟩
  have h0 := hm (left_mem_Icc.mpr zero_le_one) ⟨hz0, hz1⟩ hz0
  dsimp [f] at h0
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, add_zero,
    Real.sinh_zero, sub_self] at h0
  linarith

private lemma sub_cube_le_sin_of_unit {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    z - z ^ 3 / 6 ≤ Real.sin z := by
  let g : ℝ → ℝ := fun t => Real.sin t - (t - t ^ 3 / 6)
  let g' : ℝ → ℝ := fun t => Real.cos t - (1 - t ^ 2 / 2)
  have hd1 : ∀ t : ℝ, HasDerivAt g' (t - Real.sin t) t := fun t => by
    have h1 := (Real.hasDerivAt_cos t).sub
      ((hasDerivAt_const t (1 : ℝ)).sub (((hasDerivAt_id t).pow 2).div_const 2))
    exact h1.congr_deriv (by simp; ring)
  have hg'_nn : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ g' t := fun t ht => by
    have hm := monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1)
      (fun s _ => (hd1 s).continuousAt.continuousWithinAt)
      (fun s _ => (hd1 s).differentiableAt.differentiableWithinAt)
      fun s hs => by
        rw [interior_Icc] at hs
        rw [(hd1 s).deriv]
        have := Real.sin_le hs.1.le
        linarith
    have h0 := hm (left_mem_Icc.mpr zero_le_one) ht ht.1
    dsimp [g'] at h0
    simp only [Real.cos_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      sub_zero, sub_self] at h0
    exact h0
  have hd0 : ∀ t : ℝ, HasDerivAt g (g' t) t := fun t => by
    have h1 := (Real.hasDerivAt_sin t).sub
      ((hasDerivAt_id t).sub (((hasDerivAt_id t).pow 3).div_const 6))
    exact h1.congr_deriv (by dsimp [g']; simp; ring)
  have hm := monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1)
    (fun s _ => (hd0 s).continuousAt.continuousWithinAt)
    (fun s _ => (hd0 s).differentiableAt.differentiableWithinAt)
    fun s hs => by
      rw [interior_Icc] at hs
      rw [(hd0 s).deriv]
      exact hg'_nn s ⟨hs.1.le, hs.2.le⟩
  have h0 := hm (left_mem_Icc.mpr zero_le_one) ⟨hz0, hz1⟩ hz0
  dsimp [g] at h0
  simp only [Real.sin_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    sub_self] at h0
  linarith

private lemma abs_log_tanh_div_self_le {z : ℝ} (hz : z ≠ 0) :
    |Real.log (|Real.tanh z| / |z|)| ≤ z ^ 2 / 2 := by
  have hz_pos : 0 < |z| := abs_pos.mpr hz
  have ht_pos : 0 < |Real.tanh z| := abs_pos.mpr (by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_ne_zero (Real.sinh_ne_zero.mpr hz) (Real.cosh_pos z).ne')
  have h_tabs : |Real.tanh z| = Real.tanh |z| := by
    rcases le_total 0 z with hp | hn
    · have htnn : 0 ≤ Real.tanh z := by
        rw [Real.tanh_eq_sinh_div_cosh]
        exact div_nonneg (Real.sinh_nonneg_iff.mpr hp) (Real.cosh_pos z).le
      rw [abs_of_nonneg htnn, abs_of_nonneg hp]
    · have htneg : Real.tanh z ≤ 0 := by
        rw [Real.tanh_eq_sinh_div_cosh]
        exact div_nonpos_of_nonpos_of_nonneg (Real.sinh_nonpos_iff.mpr hn) (Real.cosh_pos z).le
      rw [abs_of_nonpos htneg, abs_of_nonpos hn, Real.tanh_neg]
  have h_le1 : |Real.tanh z| / |z| ≤ 1 := by
    rw [h_tabs, div_le_one hz_pos, Real.tanh_eq_sinh_div_cosh]
    have hch_ge : 1 ≤ Real.cosh |z| := Real.one_le_cosh |z|
    have hsh_nn : 0 ≤ Real.sinh |z| := Real.sinh_nonneg_iff.mpr hz_pos.le
    have hsh_le : Real.sinh |z| ≤ |z| * Real.cosh |z| := by
      have h1 : Real.sinh |z| / Real.cosh |z| ≤ |z| := by
        let k : ℝ → ℝ := fun t => t - Real.sinh t / Real.cosh t
        have hkd : ∀ t : ℝ, HasDerivAt k (1 - (Real.cosh t)⁻¹ ^ 2) t := fun t => by
          have h := (hasDerivAt_id t).sub
            ((Real.hasDerivAt_sinh t).div (Real.hasDerivAt_cosh t) (Real.cosh_pos t).ne')
          refine h.congr_deriv ?_
          field_simp [(Real.cosh_pos t).ne']
          linarith [Real.cosh_sq_sub_sinh_sq t]
        have hkm := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
          (fun t _ => (hkd t).continuousAt.continuousWithinAt)
          (fun t _ => (hkd t).differentiableAt.differentiableWithinAt)
          fun t _ => by
            rw [(hkd t).deriv]
            have h1 : (Real.cosh t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_cosh t)
            nlinarith [inv_nonneg.mpr (Real.cosh_pos t).le]
        have h0 := hkm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hz_pos.le) hz_pos.le
        dsimp [k] at h0; simp only [Real.sinh_zero, Real.cosh_zero, zero_div, sub_self] at h0
        linarith
      rwa [div_le_iff₀ (Real.cosh_pos |z|)] at h1
    rw [div_le_iff₀ (Real.cosh_pos |z|)]
    exact hsh_le
  have h_ge_inv_cosh : 1 / Real.cosh |z| ≤ |Real.tanh z| / |z| := by
    rw [h_tabs, Real.tanh_eq_sinh_div_cosh, div_div,
      div_le_div_iff₀ (Real.cosh_pos |z|) (mul_pos (Real.cosh_pos |z|) hz_pos)]
    calc 1 * (Real.cosh |z| * |z|) = Real.cosh |z| * |z| := one_mul _
      _ ≤ Real.cosh |z| * Real.sinh |z| :=
          mul_le_mul_of_nonneg_left (self_le_sinh_of_nonneg hz_pos.le) (Real.cosh_pos _).le
      _ = Real.sinh |z| * Real.cosh |z| := by ring
  have h_log_le0 : Real.log (|Real.tanh z| / |z|) ≤ 0 :=
    Real.log_nonpos (div_pos ht_pos hz_pos).le h_le1
  have h_log_ge : -(z ^ 2 / 2) ≤ Real.log (|Real.tanh z| / |z|) := by
    have h1 := Real.log_le_log (one_div_pos.mpr (Real.cosh_pos |z|)) h_ge_inv_cosh
    rw [one_div, Real.log_inv] at h1
    have h2 := log_cosh_le_half_sq |z|
    rw [sq_abs] at h2
    linarith
  rw [abs_of_nonpos h_log_le0]
  linarith

private lemma abs_log_one_add_le {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |Real.log (1 + t)| ≤ 2 * |t| := by
  have ht_pos : 0 < 1 + t := by linarith [(abs_le.mp ht).1]
  rcases le_total 0 t with ht0 | ht0
  · have hl_nn : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
    rw [abs_of_nonneg hl_nn, abs_of_nonneg ht0]
    exact (Real.log_le_sub_one_of_pos ht_pos).trans (by linarith)
  · have hl_np : Real.log (1 + t) ≤ 0 := Real.log_nonpos ht_pos.le (by linarith)
    rw [abs_of_nonpos hl_np, abs_of_nonpos ht0]
    let g : ℝ → ℝ := fun s => Real.log (1 + s) - 2 * s
    have hd : ∀ s ∈ Icc (-(1 / 2 : ℝ)) 0, HasDerivAt g (1 / (1 + s) - 2) s := fun s hs => by
      have hs_pos : 0 < 1 + s := by linarith [hs.1]
      have h1 := ((hasDerivAt_const s (1 : ℝ)).add (hasDerivAt_id s)).log hs_pos.ne'
      have h2 := (hasDerivAt_id s).const_mul (2 : ℝ)
      exact (h1.sub h2).congr_deriv (by simp [one_div])
    have hm := antitoneOn_of_deriv_nonpos (convex_Icc (-(1 / 2 : ℝ)) 0)
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs => by
        rw [interior_Icc] at hs
        exact (hd s ⟨hs.1.le, hs.2.le⟩).differentiableAt.differentiableWithinAt)
      fun s hs => by
        rw [interior_Icc] at hs
        rw [(hd s ⟨hs.1.le, hs.2.le⟩).deriv]
        have hs_pos : 0 < 1 + s := by linarith [hs.1]
        rw [sub_nonpos, div_le_iff₀ hs_pos]
        linarith [hs.1]
    have h_mem : t ∈ Icc (-(1 / 2 : ℝ)) 0 := ⟨(abs_le.mp ht).1, ht0⟩
    have h0 := hm h_mem (right_mem_Icc.mpr (by norm_num)) ht0
    dsimp [g] at h0
    simp only [add_zero, Real.log_one, mul_zero, sub_self] at h0
    linarith

private lemma abs_integral_log_abs_sub_diff {A B c₁ c₂ : ℝ}
    (hAc1 : A + 1 / 2 ≤ c₁) (hc1B : c₁ + 1 / 2 ≤ B)
    (hAc2 : A + 1 / 2 ≤ c₂) (hc2B : c₂ + 1 / 2 ≤ B)
    (_hAB_len : B - A ≤ 2 * (B - c₁) + 2) (_hR : 1 ≤ B - A) :
    |(∫ a in A..B, Real.log |a - c₁|) - (∫ a in A..B, Real.log |a - c₂|)| ≤
      |c₁ - c₂| * (2 * (B - A)) := by
  let F : ℝ → ℝ := fun c => (B - c) * Real.log (B - c) - (B - c) +
    ((c - A) * Real.log (c - A) - (c - A))
  have h_eval : ∀ c : ℝ, A + 1 / 2 ≤ c → c + 1 / 2 ≤ B →
      ∫ a in A..B, Real.log |a - c| = F c := fun c hAc hcB => by
    have hsplit : ∫ a in A..B, Real.log |a - c| =
        (∫ a in A..c, Real.log |a - c|) + ∫ a in c..B, Real.log |a - c| := by
      have hi1 : IntervalIntegrable (fun a => Real.log |a - c|) volume A c := by
        have hcomp : IntervalIntegrable (fun a => Real.log (c - a)) volume A c := by
          simpa using (intervalIntegral.intervalIntegrable_log' (a := c - A) (b := 0)).comp_sub_left c
        have hac : A ≤ c := by linarith
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hac] at hcomp ⊢
        exact hcomp.congr_fun (fun a ha => by rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ha.2)]) measurableSet_Ioc
      have hi2 : IntervalIntegrable (fun a => Real.log |a - c|) volume c B := by
        have hcomp : IntervalIntegrable (fun a => Real.log (a - c)) volume c B := by
          simpa using (intervalIntegral.intervalIntegrable_log' (a := 0) (b := B - c)).comp_sub_right c
        have hcb : c ≤ B := by linarith
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hcb] at hcomp ⊢
        exact hcomp.congr_fun (fun a ha => by rw [abs_of_nonneg (sub_nonneg.mpr ha.1.le)]) measurableSet_Ioc
      exact (intervalIntegral.integral_add_adjacent_intervals hi1 hi2).symm
    have hl : ∫ a in A..c, Real.log |a - c| = (c - A) * Real.log (c - A) - (c - A) := by
      have hcon : ∫ a in A..c, Real.log |a - c| = ∫ a in A..c, Real.log (c - a) := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards with a ha
        rw [Set.uIoc_of_le (by linarith)] at ha
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ha.2)]
      rw [hcon, intervalIntegral.integral_comp_sub_left Real.log c, integral_log]
      simp only [sub_zero, zero_mul, sub_self, add_zero]
    have hr : ∫ a in c..B, Real.log |a - c| = (B - c) * Real.log (B - c) - (B - c) := by
      have hcon : ∫ a in c..B, Real.log |a - c| = ∫ a in c..B, Real.log (a - c) := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards with a ha
        rw [Set.uIoc_of_le (by linarith)] at ha
        rw [abs_of_nonneg (sub_nonneg.mpr ha.1.le)]
      rw [hcon, intervalIntegral.integral_comp_sub_right Real.log c, sub_self, integral_log]
      simp only [zero_mul, sub_zero, add_zero]
    rw [hsplit, hl, hr]
    dsimp [F]; ring
  rw [h_eval c₁ hAc1 hc1B, h_eval c₂ hAc2 hc2B]
  let m := min c₁ c₂
  let M := max c₁ c₂
  have hm_le_M : m ≤ M := min_le_max
  have hAm : A + 1 / 2 ≤ m := le_min hAc1 hAc2
  have hMB : M + 1 / 2 ≤ B := by
    dsimp [M]
    rcases le_total c₁ c₂ with h | h
    · rw [max_eq_right h]; exact hc2B
    · rw [max_eq_left h]; exact hc1B
  have hF_deriv : ∀ c ∈ Icc m M,
      HasDerivAt F (Real.log (c - A) - Real.log (B - c)) c := fun c hc => by
    have hca : 0 < c - A := by linarith [hc.1]
    have hbc : 0 < B - c := by linarith [hc.2]
    have h1 : HasDerivAt (fun t => (B - t) * Real.log (B - t) - (B - t)) (-Real.log (B - c)) c := by
      have ht := ((hasDerivAt_id c).const_sub B)
      have hl := ht.log hbc.ne'
      have hm1 := ht.mul hl
      exact (hm1.sub ht).congr_deriv (by simp; field_simp [hbc.ne']; ring)
    have h2 : HasDerivAt (fun t => (t - A) * Real.log (t - A) - (t - A)) (Real.log (c - A)) c := by
      have ht := ((hasDerivAt_id c).sub_const A)
      have hl := ht.log hca.ne'
      have hm1 := ht.mul hl
      exact (hm1.sub ht).congr_deriv (by simp; field_simp [hca.ne']; ring)
    exact (h1.add h2).congr_deriv (by ring)
  have hF_bound : ∀ c ∈ Icc m M, |Real.log (c - A) - Real.log (B - c)| ≤ 2 * (B - A) := fun c hc => by
    have hca1 : 1 / 2 ≤ c - A := by linarith [hc.1]
    have hbc1 : 1 / 2 ≤ B - c := by linarith [hc.2]
    have hca_le : c - A ≤ B - A := by linarith [hc.2]
    have hbc_le : B - c ≤ B - A := by linarith [hc.1]
    have h1 : |Real.log (c - A)| ≤ B - A := by
      by_cases hge : 1 ≤ c - A
      · rw [abs_of_nonneg (Real.log_nonneg hge)]
        exact (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
      · rw [abs_of_nonpos (Real.log_nonpos (by linarith) (by linarith))]
        have := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hca1
        have hl2 : -Real.log (1 / 2 : ℝ) ≤ 1 := by
          rw [one_div, Real.log_inv, neg_neg]
          exact (Real.log_le_sub_one_of_pos two_pos).trans (by norm_num)
        linarith
    have h2 : |Real.log (B - c)| ≤ B - A := by
      by_cases hge : 1 ≤ B - c
      · rw [abs_of_nonneg (Real.log_nonneg hge)]
        exact (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
      · rw [abs_of_nonpos (Real.log_nonpos (by linarith) (by linarith))]
        have := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hbc1
        have hl2 : -Real.log (1 / 2 : ℝ) ≤ 1 := by
          rw [one_div, Real.log_inv, neg_neg]
          exact (Real.log_le_sub_one_of_pos two_pos).trans (by norm_num)
        linarith
    exact (abs_sub _ _).trans (by linarith)
  have hmvt : ∀ u v : ℝ, u ∈ Icc m M → v ∈ Icc m M → |F u - F v| ≤ (2 * (B - A)) * |u - v| :=
    fun u v hu hv => by
      simpa [Real.norm_eq_abs, abs_sub_comm] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (𝕜 := ℝ) (f := F) (f' := fun c => Real.log (c - A) - Real.log (B - c))
        (s := Icc m M) (C := 2 * (B - A))
        (fun c hc => (hF_deriv c hc).hasDerivWithinAt)
        (fun c hc => hF_bound c hc)
        (convex_Icc m M) hu hv
  rcases le_total c₁ c₂ with hle | hle
  · have hm_eq : m = c₁ := min_eq_left hle
    have hM_eq : M = c₂ := max_eq_right hle
    have h_sub := hmvt c₁ c₂ ⟨by rw [hm_eq], by rw [hM_eq]; exact hle⟩
      ⟨by rw [hm_eq]; exact hle, by rw [hM_eq]⟩
    simpa [mul_comm] using h_sub
  · have hm_eq : m = c₂ := min_eq_right hle
    have hM_eq : M = c₁ := max_eq_left hle
    have h_sub := hmvt c₁ c₂ ⟨by rw [hm_eq]; exact hle, by rw [hM_eq]⟩
      ⟨by rw [hm_eq], by rw [hM_eq]; exact hle⟩
    simpa [mul_comm] using h_sub

/-- Linearization of the quantile sites around `χ_n` on the window `|b - n| ≤ j + 1`: the derivative
`χ'_a` and the gaps `ℓ_m` stay within `1 ± 4(j+1)/n` of `ℓ_n`, and `χ_b - χ_n - (b-n)ℓ_n` is
`O(j²ℓ_n/n)`. -/
lemma quantile_linearization_K5 {c' : ℝ} (hc' : 0 < c') {j n : ℕ}
    (hj : 1 ≤ j) (hn : 4 * (j + 1) ≤ n) :
    let ℓ := siteGap c' n
    0 < ℓ ∧
      (∀ a ∈ Icc ((n : ℝ) - j - 1 / 2) ((n : ℝ) + j + 1),
        (1 - 4 * ((j : ℝ) + 1) / (n : ℝ)) * ℓ ≤ chiDeriv c' a ∧
          chiDeriv c' a ≤ (1 + 4 * ((j : ℝ) + 1) / (n : ℝ)) * ℓ) ∧
      (∀ b ∈ Icc ((n : ℝ) - j - 1 / 2) ((n : ℝ) + j + 1),
        |chiQuantile c' b - chiQuantile c' n - (b - (n : ℝ)) * ℓ| ≤
          4 * ((j : ℝ) + 1) ^ 2 / (n : ℝ) * ℓ) ∧
      (∀ m ∈ Finset.Icc (n - j + 1) (n + j),
        |siteGap c' m - ℓ| ≤ 4 * ((j : ℝ) + 1) / (n : ℝ) * ℓ) := by
  intro ℓ
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1_r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hj1_r : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hnj_lb : (n : ℝ) / 2 ≤ (n : ℝ) - (j : ℝ) - 1 / 2 - 1 / 4 := by
    have : 4 * ((j : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h_ell_pos : 0 < ℓ := by
    unfold ℓ siteGap
    exact sub_pos.mpr (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith))
      (Set.mem_Ici.mpr (by linarith)) (by linarith))
  have h_ratio : ∀ a ∈ Icc ((n : ℝ) - j - 1 / 2) ((n : ℝ) + j + 1),
      ∀ t ∈ Icc (n : ℝ) ((n : ℝ) + 1),
      (1 - 4 * ((j : ℝ) + 1) / (n : ℝ)) * chiDeriv c' t ≤ chiDeriv c' a ∧
        chiDeriv c' a ≤ (1 + 4 * ((j : ℝ) + 1) / (n : ℝ)) * chiDeriv c' t := fun a ha t ht => by
    have ha14 : 1 / 4 < a := by linarith [ha.1]
    have ht14 : 1 / 4 < t := by linarith [ht.1]
    have hca_pos : 0 < chiDeriv c' a := chiDeriv_pos hc' ha14
    have hct_pos : 0 < chiDeriv c' t := chiDeriv_pos hc' ht14
    have h_ub_diff : |a - t| ≤ 2 * ((j : ℝ) + 1) := abs_le.mpr
      ⟨by linarith [ha.1, ht.2], by linarith [ha.2, ht.1]⟩
    have h_min_lb : (n : ℝ) / 2 ≤ min a t - 1 / 4 := by
      have : (n : ℝ) - j - 1 / 2 ≤ min a t := le_min ha.1 (by linarith [ht.1])
      linarith
    have h_quot : ∀ u v : ℝ, (n : ℝ) - j - 1 / 2 ≤ u → u ≤ v → v ≤ (n : ℝ) + j + 1 →
        chiDeriv c' u / chiDeriv c' v ≤ 1 + 4 * ((j : ℝ) + 1) / (n : ℝ) := fun u v hu huv hv => by
      have hu14 : 1 / 4 < u := by linarith
      have hdiv := chiDeriv_div_le hc' hu14 huv
      have hden_pos : 0 < u - 1 / 4 := by linarith
      have h_num : v - u ≤ 2 * ((j : ℝ) + 1) := by linarith
      calc chiDeriv c' u / chiDeriv c' v
          ≤ (v - 1 / 4) / (u - 1 / 4) := hdiv
        _ = ((u - 1 / 4) + (v - u)) / (u - 1 / 4) := by ring
        _ = 1 + (v - u) / (u - 1 / 4) := by rw [add_div, div_self hden_pos.ne']
        _ ≤ 1 + (2 * ((j : ℝ) + 1)) / ((n : ℝ) / 2) := by
            gcongr; linarith
        _ = 1 + 4 * ((j : ℝ) + 1) / (n : ℝ) := by ring
    rcases le_total a t with hat | hta
    · have h_up := h_quot a t ha.1 hat (by linarith [ht.2])
      have h1 : chiDeriv c' t ≤ chiDeriv c' a := by
        rcases eq_or_lt_of_le hat with rfl | hlt
        · exact le_rfl
        · exact (chiDeriv_strictAntiOn hc' (Set.mem_Ioi.mpr ha14)
            (Set.mem_Ioi.mpr ht14) hlt).le
      have h2 : (1 - 4 * ((j : ℝ) + 1) / (n : ℝ)) * chiDeriv c' t ≤ chiDeriv c' a := by
        have h_nonneg : 0 ≤ 4 * ((j : ℝ) + 1) / (n : ℝ) := by positivity
        nlinarith
      exact ⟨h2, (div_le_iff₀ hct_pos).mp h_up⟩
    · have h_up := h_quot t a (by linarith [ht.1]) hta ha.2
      have h1 : chiDeriv c' a ≤ chiDeriv c' t := by
        rcases eq_or_lt_of_le hta with rfl | hlt
        · exact le_rfl
        · exact (chiDeriv_strictAntiOn hc' (Set.mem_Ioi.mpr ht14)
            (Set.mem_Ioi.mpr ha14) hlt).le
      have h2 : chiDeriv c' a ≤ (1 + 4 * ((j : ℝ) + 1) / (n : ℝ)) * chiDeriv c' t := by
        have : 0 ≤ 4 * ((j : ℝ) + 1) / (n : ℝ) := by positivity
        nlinarith
      have h_low : (1 - 4 * ((j : ℝ) + 1) / (n : ℝ)) * chiDeriv c' t ≤ chiDeriv c' a := by
        have ht_le : chiDeriv c' t ≤ (1 + 4 * ((j : ℝ) + 1) / (n : ℝ)) * chiDeriv c' a :=
          (div_le_iff₀ hca_pos).mp h_up
        have h_ε_nn : 0 ≤ 4 * ((j : ℝ) + 1) / (n : ℝ) := by positivity
        nlinarith
      exact ⟨h_low, h2⟩
  have h_ell_eq : ∫ t in (n : ℝ)..((n : ℝ) + 1), chiDeriv c' t = ℓ := by
    have hcont : ContinuousOn (chiDeriv c') (Icc (n : ℝ) ((n : ℝ) + 1)) := fun t ht =>
      (hasDerivAt_chiQuantile hc' (by linarith [ht.1])).2.continuousAt.continuousWithinAt
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => by
        rw [Set.uIcc_of_le (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)] at ht
        exact (hasDerivAt_chiQuantile hc' (by linarith [ht.1])).1)
      (hcont.intervalIntegrable_of_Icc (by linarith))
    unfold ℓ siteGap
    exact h
  have h_deriv_bd : ∀ a ∈ Icc ((n : ℝ) - j - 1 / 2) ((n : ℝ) + j + 1),
      (1 - 4 * ((j : ℝ) + 1) / (n : ℝ)) * ℓ ≤ chiDeriv c' a ∧
        chiDeriv c' a ≤ (1 + 4 * ((j : ℝ) + 1) / (n : ℝ)) * ℓ := fun a ha => by
    have hcont : ContinuousOn (chiDeriv c') (Icc (n : ℝ) ((n : ℝ) + 1)) := fun t ht =>
      (hasDerivAt_chiQuantile hc' (by linarith [ht.1])).2.continuousAt.continuousWithinAt
    have hint : IntervalIntegrable (chiDeriv c') volume (n : ℝ) ((n : ℝ) + 1) :=
      hcont.intervalIntegrable_of_Icc (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)
    have h_low_int := intervalIntegral.integral_mono_on
      (f := fun t => (1 - 4 * ((j : ℝ) + 1) / (n : ℝ)) * chiDeriv c' t)
      (g := fun _ => chiDeriv c' a) (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)
      (hint.const_mul _) (intervalIntegrable_const (μ := volume))
      fun t ht => (h_ratio a ha t ht).1
    have h_up_int := intervalIntegral.integral_mono_on
      (f := fun _ => chiDeriv c' a)
      (g := fun t => (1 + 4 * ((j : ℝ) + 1) / (n : ℝ)) * chiDeriv c' t)
      (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)
      (intervalIntegrable_const (μ := volume)) (hint.const_mul _)
      fun t ht => (h_ratio a ha t ht).2
    have h_const_l : (1 - 4 * ((j : ℝ) + 1) / (n : ℝ)) * ℓ =
        ∫ t in (n : ℝ)..((n : ℝ) + 1), (1 - 4 * ((j : ℝ) + 1) / (n : ℝ)) * chiDeriv c' t := by
      rw [intervalIntegral.integral_const_mul, h_ell_eq]
    have h_const_u : (1 + 4 * ((j : ℝ) + 1) / (n : ℝ)) * ℓ =
        ∫ t in (n : ℝ)..((n : ℝ) + 1), (1 + 4 * ((j : ℝ) + 1) / (n : ℝ)) * chiDeriv c' t := by
      rw [intervalIntegral.integral_const_mul, h_ell_eq]
    have h_r : ∫ _t in (n : ℝ)..((n : ℝ) + 1), chiDeriv c' a = chiDeriv c' a := by
      rw [intervalIntegral.integral_const, smul_eq_mul, show (n : ℝ) + 1 - (n : ℝ) = 1 by ring, one_mul]
    exact ⟨h_const_l ▸ h_r ▸ h_low_int, h_r ▸ h_const_u ▸ h_up_int⟩
  have h_pos_bd : ∀ b ∈ Icc ((n : ℝ) - j - 1 / 2) ((n : ℝ) + j + 1),
      |chiQuantile c' b - chiQuantile c' n - (b - (n : ℝ)) * ℓ| ≤
        4 * ((j : ℝ) + 1) ^ 2 / (n : ℝ) * ℓ := fun b hb => by
    have h_err_bd : ∀ a ∈ Icc ((n : ℝ) - j - 1 / 2) ((n : ℝ) + j + 1),
        |chiDeriv c' a - ℓ| ≤ 4 * ((j : ℝ) + 1) / (n : ℝ) * ℓ := fun a ha => by
      have := h_deriv_bd a ha
      rw [abs_le]; constructor <;> linarith
    have hcont : ContinuousOn (chiDeriv c') (uIcc (n : ℝ) b) := fun t ht => by
      have ht_Icc : t ∈ Icc ((n : ℝ) - j - 1 / 2) ((n : ℝ) + j + 1) := by
        rcases le_total (n : ℝ) b with hnb | hbn
        · rw [Set.uIcc_of_le hnb] at ht
          exact ⟨by linarith [ht.1], ht.2.trans hb.2⟩
        · rw [Set.uIcc_of_ge hbn] at ht
          exact ⟨hb.1.trans ht.1, by linarith [ht.2]⟩
      exact (hasDerivAt_chiQuantile hc' (by linarith [ht_Icc.1])).2.continuousAt.continuousWithinAt
    have h_int_eq : chiQuantile c' b - chiQuantile c' n - (b - (n : ℝ)) * ℓ =
        ∫ a in (n : ℝ)..b, (chiDeriv c' a - ℓ) := by
      have h1 : ∫ a in (n : ℝ)..b, chiDeriv c' a = chiQuantile c' b - chiQuantile c' n := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => ?_)
          (hcont.intervalIntegrable)
        have ht_Icc : t ∈ Icc ((n : ℝ) - j - 1 / 2) ((n : ℝ) + j + 1) := by
          rcases le_total (n : ℝ) b with hnb | hbn
          · rw [Set.uIcc_of_le hnb] at ht; exact ⟨by linarith [ht.1], ht.2.trans hb.2⟩
          · rw [Set.uIcc_of_ge hbn] at ht; exact ⟨hb.1.trans ht.1, by linarith [ht.2]⟩
        exact (hasDerivAt_chiQuantile hc' (by linarith [ht_Icc.1])).1
      have h2 : ∫ a in (n : ℝ)..b, (ℓ : ℝ) = (b - (n : ℝ)) * ℓ := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
      rw [intervalIntegral.integral_sub hcont.intervalIntegrable (intervalIntegrable_const (μ := volume)),
        h1, h2]
    rw [h_int_eq]
    have h_norm := intervalIntegral.norm_integral_le_of_norm_le_const (C := 4 * ((j : ℝ) + 1) / (n : ℝ) * ℓ)
      (a := (n : ℝ)) (b := b) (f := fun a => chiDeriv c' a - ℓ) fun a ha => by
      have ha_Icc : a ∈ Icc ((n : ℝ) - j - 1 / 2) ((n : ℝ) + j + 1) := by
        rcases le_total (n : ℝ) b with hnb | hbn
        · rw [Set.uIoc_of_le hnb] at ha; exact ⟨by linarith [ha.1], ha.2.trans hb.2⟩
        · rw [Set.uIoc_of_ge hbn] at ha; exact ⟨hb.1.trans ha.1.le, by linarith [ha.2]⟩
      simpa [Real.norm_eq_abs] using h_err_bd a ha_Icc
    rw [Real.norm_eq_abs] at h_norm
    have h_dist : |b - (n : ℝ)| ≤ (j : ℝ) + 1 := abs_le.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩
    calc |∫ a in (n : ℝ)..b, (chiDeriv c' a - ℓ)|
        ≤ (4 * ((j : ℝ) + 1) / (n : ℝ) * ℓ) * |b - (n : ℝ)| := h_norm
      _ ≤ (4 * ((j : ℝ) + 1) / (n : ℝ) * ℓ) * ((j : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left h_dist (by positivity)
      _ = 4 * ((j : ℝ) + 1) ^ 2 / (n : ℝ) * ℓ := by ring
  have h_gap_bd : ∀ m ∈ Finset.Icc (n - j + 1) (n + j),
      |siteGap c' m - ℓ| ≤ 4 * ((j : ℝ) + 1) / (n : ℝ) * ℓ := fun m hm => by
    have hm_mem := Finset.mem_Icc.mp hm
    have hm_lb : (n : ℝ) - j - 1 / 2 ≤ (m : ℝ) := by
      have : n - j + 1 ≤ m := hm_mem.1
      have hnj_sub : (n - j : ℕ) ≤ m := by omega
      have hcast : ((n - j : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnj_sub
      have hsub : ((n - j : ℕ) : ℝ) = (n : ℝ) - (j : ℝ) := Nat.cast_sub (by omega)
      linarith
    have hm_ub : (m : ℝ) + 1 ≤ (n : ℝ) + j + 1 := by
      have : (m : ℝ) ≤ (n : ℝ) + (j : ℝ) := by exact_mod_cast hm_mem.2
      linarith
    have hcont : ContinuousOn (chiDeriv c') (Icc (m : ℝ) ((m : ℝ) + 1)) := fun t ht =>
      (hasDerivAt_chiQuantile hc' (by linarith [ht.1])).2.continuousAt.continuousWithinAt
    have h_int : siteGap c' m = ∫ a in (m : ℝ)..((m : ℝ) + 1), chiDeriv c' a := by
      unfold siteGap
      exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => by
          rw [Set.uIcc_of_le (by linarith : (m : ℝ) ≤ (m : ℝ) + 1)] at ht
          exact (hasDerivAt_chiQuantile hc' (by linarith [ht.1])).1)
        (hcont.intervalIntegrable_of_Icc (by linarith))).symm
    have h_diff_int : siteGap c' m - ℓ = ∫ a in (m : ℝ)..((m : ℝ) + 1), (chiDeriv c' a - ℓ) := by
      rw [h_int, intervalIntegral.integral_sub (hcont.intervalIntegrable_of_Icc (by linarith))
        (intervalIntegrable_const (μ := volume)), intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [h_diff_int]
    have h_norm := intervalIntegral.norm_integral_le_of_norm_le_const (C := 4 * ((j : ℝ) + 1) / (n : ℝ) * ℓ)
      (a := (m : ℝ)) (b := (m : ℝ) + 1) (f := fun a => chiDeriv c' a - ℓ) fun a ha => by
      rw [Set.uIoc_of_le (by linarith : (m : ℝ) ≤ (m : ℝ) + 1)] at ha
      have ha_Icc : a ∈ Icc ((n : ℝ) - j - 1 / 2) ((n : ℝ) + j + 1) :=
        ⟨by linarith [ha.1], by linarith [ha.2]⟩
      have := h_deriv_bd a ha_Icc
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
    rw [Real.norm_eq_abs] at h_norm
    have heq : |(m : ℝ) + 1 - (m : ℝ)| = 1 := by norm_num
    rwa [heq, mul_one] at h_norm
  exact ⟨h_ell_pos, h_deriv_bd, h_pos_bd, h_gap_bd⟩

private lemma log_ratio_minus_bound {α β : ℝ} (hα : |α| ≤ 1 / 16) (hβ0 : 0 < β) (hβ : β ≤ 1 / 16) :
    |Real.log (((Real.sinh α ^ 2 + Real.sin β ^ 2) /
      (Real.cosh α ^ 2 - Real.sin β ^ 2)) / (α ^ 2 + β ^ 2))| ≤ 16 * (α ^ 2 + β ^ 2) := by
  have hα2_le : α ^ 2 ≤ 1 / 16 := by
    rw [← sq_abs]; exact (pow_le_pow_left₀ (abs_nonneg _) hα 2).trans (by norm_num)
  have hβ2_le : β ^ 2 ≤ 1 / 16 := (pow_le_pow_left₀ hβ0.le hβ 2).trans (by norm_num)
  have hα2β2_pos : 0 < α ^ 2 + β ^ 2 := by positivity
  have hα2β2_le : α ^ 2 + β ^ 2 ≤ 1 / 16 := by
    have hα2_s : α ^ 2 ≤ 1 / 256 := by
      rw [← sq_abs]; exact (pow_le_pow_left₀ (abs_nonneg _) hα 2).trans (by norm_num)
    have hβ2_s : β ^ 2 ≤ 1 / 256 := (pow_le_pow_left₀ hβ0.le hβ 2).trans (by norm_num)
    linarith
  have h_sh_bd : α ^ 2 ≤ Real.sinh α ^ 2 ∧ Real.sinh α ^ 2 ≤ α ^ 2 + 2 * α ^ 4 := by
    have h_abs : |α| ≤ Real.sinh |α| ∧ Real.sinh |α| ≤ |α| + |α| ^ 3 / 2 :=
      ⟨self_le_sinh_of_nonneg (abs_nonneg _),
        sinh_le_add_cube_of_unit (abs_nonneg _) (hα.trans (by norm_num))⟩
    have hsh_eq : Real.sinh α ^ 2 = Real.sinh |α| ^ 2 := by
      rcases le_total 0 α with ha | ha
      · rw [abs_of_nonneg ha]
      · rw [abs_of_nonpos ha, Real.sinh_neg, neg_sq]
    rw [hsh_eq]
    constructor
    · have := pow_le_pow_left₀ (abs_nonneg _) h_abs.1 2; simpa [sq_abs] using this
    · have h1 := pow_le_pow_left₀ (Real.sinh_nonneg_iff.mpr (abs_nonneg _)) h_abs.2 2
      have h_sq : |α| ^ 2 = α ^ 2 := sq_abs α
      have h_4 : |α| ^ 4 = α ^ 4 := by
        calc |α| ^ 4 = (|α| ^ 2) ^ 2 := by ring
          _ = (α ^ 2) ^ 2 := by rw [h_sq]
          _ = α ^ 4 := by ring
      have ha6 : (α ^ 2) ^ 3 ≤ α ^ 4 := by
        have : α ^ 2 * (α ^ 2) ^ 2 ≤ 1 * (α ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
        linarith [show (α ^ 2) ^ 2 = α ^ 4 by ring, show (α ^ 2) ^ 3 = α ^ 2 * (α ^ 2) ^ 2 by ring]
      have ha4_nn : 0 ≤ α ^ 4 := by positivity
      have h_id : (|α| + |α| ^ 3 / 2) ^ 2 = |α| ^ 2 + |α| ^ 4 + (|α| ^ 2) ^ 3 / 4 := by ring
      rw [h_id, h_sq, h_4] at h1
      linarith
  have h_sin_bd : β ^ 2 - β ^ 4 / 3 ≤ Real.sin β ^ 2 ∧ Real.sin β ^ 2 ≤ β ^ 2 := by
    have h_l : β - β ^ 3 / 6 ≤ Real.sin β := sub_cube_le_sin_of_unit hβ0.le (hβ.trans (by norm_num))
    have h_u : Real.sin β ≤ β := Real.sin_le hβ0.le
    have hsnn : 0 ≤ Real.sin β := Real.sin_nonneg_of_nonneg_of_le_pi hβ0.le (by linarith [Real.pi_gt_three])
    have hb3 : β ^ 3 ≤ β := by
      have : β * β ^ 2 ≤ β * (1 / 16) := mul_le_mul_of_nonneg_left hβ2_le hβ0.le
      linarith [show β ^ 3 = β * β ^ 2 by ring]
    have hlnn : 0 ≤ β - β ^ 3 / 6 := by linarith
    constructor
    · have hpow := pow_le_pow_left₀ hlnn h_l 2
      have hid : (β - β ^ 3 / 6) ^ 2 = β ^ 2 - β ^ 4 / 3 + β ^ 6 / 36 := by ring
      linarith [pow_nonneg hβ0.le 6]
    · exact pow_le_pow_left₀ hsnn h_u 2
  have h_S_le : Real.sin β ^ 2 ≤ 1 / 2 := by linarith [h_sin_bd.2]
  have h_den1_pos : 0 < Real.cosh α ^ 2 - Real.sin β ^ 2 := by
    have hch1 : 1 ≤ Real.cosh α ^ 2 := one_le_pow₀ (Real.one_le_cosh α)
    linarith
  have h_den1_bd : 1 - β ^ 2 ≤ Real.cosh α ^ 2 - Real.sin β ^ 2 ∧
      Real.cosh α ^ 2 - Real.sin β ^ 2 ≤ 1 + 2 * α ^ 2 := by
    have hch_id : Real.cosh α ^ 2 = 1 + Real.sinh α ^ 2 := by
      linarith [Real.cosh_sq_sub_sinh_sq α]
    have ha4 : α ^ 4 ≤ α ^ 2 / 16 := by
      have : α ^ 2 * α ^ 2 ≤ (1 / 16) * α ^ 2 := mul_le_mul_of_nonneg_right hα2_le (sq_nonneg _)
      linarith [show α ^ 4 = α ^ 2 * α ^ 2 by ring]
    constructor
    · linarith [h_sh_bd.1, h_sin_bd.2]
    · linarith [h_sh_bd.2, sq_nonneg (Real.sin β)]
  set s := α ^ 2 + β ^ 2
  set R1 := ((Real.sinh α ^ 2 + Real.sin β ^ 2) /
    (Real.cosh α ^ 2 - Real.sin β ^ 2)) / s
  have hR1_up : R1 ≤ 1 + 8 * s := by
    have ha4_le : α ^ 4 ≤ s ^ 2 := by
      have : α ^ 4 = (α ^ 2) ^ 2 := by ring
      rw [this]
      exact pow_le_pow_left₀ (sq_nonneg _) (by linarith [sq_nonneg β]) 2
    have h_n_up : Real.sinh α ^ 2 + Real.sin β ^ 2 ≤ (1 + 2 * s) * s := by
      calc Real.sinh α ^ 2 + Real.sin β ^ 2
          ≤ (α ^ 2 + 2 * α ^ 4) + β ^ 2 := add_le_add h_sh_bd.2 h_sin_bd.2
        _ ≤ s + 2 * s ^ 2 := by linarith
        _ = (1 + 2 * s) * s := by ring
    have h_d_lo : 1 - s ≤ Real.cosh α ^ 2 - Real.sin β ^ 2 := by linarith [h_den1_bd.1, sq_nonneg α]
    have hs2 : s ^ 2 ≤ s / 8 := by
      have := mul_le_mul_of_nonneg_right hα2β2_le hα2β2_pos.le
      linarith [show s ^ 2 = s * s by ring]
    have h_inv_d : 1 / (Real.cosh α ^ 2 - Real.sin β ^ 2) ≤ 1 + 2 * s := by
      rw [div_le_iff₀ h_den1_pos]
      have hmul : (1 - s) * (1 + 2 * s) ≤ (Real.cosh α ^ 2 - Real.sin β ^ 2) * (1 + 2 * s) :=
        mul_le_mul_of_nonneg_right h_d_lo (by positivity)
      have hid : (1 - s) * (1 + 2 * s) = 1 + s - 2 * s ^ 2 := by ring
      linarith
    have h1 : (Real.sinh α ^ 2 + Real.sin β ^ 2) / s ≤ 1 + 2 * s := (div_le_iff₀ hα2β2_pos).mpr h_n_up
    have h2 : ((Real.sinh α ^ 2 + Real.sin β ^ 2) / s) *
          (1 / (Real.cosh α ^ 2 - Real.sin β ^ 2)) ≤ (1 + 2 * s) * (1 + 2 * s) :=
      mul_le_mul h1 h_inv_d (by positivity) (by positivity)
    have hid2 : (1 + 2 * s) * (1 + 2 * s) = 1 + 4 * s + 4 * s ^ 2 := by ring
    have hr1 : R1 = ((Real.sinh α ^ 2 + Real.sin β ^ 2) / s) *
        (1 / (Real.cosh α ^ 2 - Real.sin β ^ 2)) := by dsimp [R1]; ring
    linarith
  have hR1_lo : 1 - 8 * s ≤ R1 := by
    have hb4_le : β ^ 4 ≤ s ^ 2 := by
      have : β ^ 4 = (β ^ 2) ^ 2 := by ring
      rw [this]
      exact pow_le_pow_left₀ (sq_nonneg _) (by linarith [sq_nonneg α]) 2
    have h_n_lo : (1 - s) * s ≤ Real.sinh α ^ 2 + Real.sin β ^ 2 := by
      have hid : (1 - s) * s = s - s ^ 2 := by ring
      linarith [h_sh_bd.1, h_sin_bd.1]
    have h_inv_d : 1 - 2 * s ≤ 1 / (Real.cosh α ^ 2 - Real.sin β ^ 2) := by
      rw [le_div_iff₀ h_den1_pos]
      have h_d_up : Real.cosh α ^ 2 - Real.sin β ^ 2 ≤ 1 + 2 * s := by
        linarith [h_den1_bd.2, sq_nonneg β]
      have hmul : (1 - 2 * s) * (Real.cosh α ^ 2 - Real.sin β ^ 2) ≤ (1 - 2 * s) * (1 + 2 * s) :=
        mul_le_mul_of_nonneg_left h_d_up (by linarith)
      have hid : (1 - 2 * s) * (1 + 2 * s) = 1 - 4 * s ^ 2 := by ring
      linarith [sq_nonneg s]
    have h1 : 1 - s ≤ (Real.sinh α ^ 2 + Real.sin β ^ 2) / s := (le_div_iff₀ hα2β2_pos).mpr h_n_lo
    have h2 : (1 - s) * (1 - 2 * s) ≤ ((Real.sinh α ^ 2 + Real.sin β ^ 2) / s) *
        (1 / (Real.cosh α ^ 2 - Real.sin β ^ 2)) :=
      mul_le_mul h1 h_inv_d (by linarith) (by positivity)
    have hid2 : (1 - s) * (1 - 2 * s) = 1 - 3 * s + 2 * s ^ 2 := by ring
    have hr1 : R1 = ((Real.sinh α ^ 2 + Real.sin β ^ 2) / s) *
        (1 / (Real.cosh α ^ 2 - Real.sin β ^ 2)) := by dsimp [R1]; ring
    linarith [sq_nonneg s]
  have h_t : |R1 - 1| ≤ 8 * s := abs_le.mpr ⟨by linarith, by linarith⟩
  have h_half : |R1 - 1| ≤ 1 / 2 := h_t.trans (by linarith)
  simpa [R1, s, add_sub_cancel] using (abs_log_one_add_le h_half).trans (by linarith)

private lemma log_ratio_plus_bound {γ β : ℝ} (hγ : π * xiStar ≤ γ) (hβ0 : 0 < β) (hβ : β ≤ 1 / 4) :
    |Real.log (((Real.sinh γ ^ 2 + Real.sin β ^ 2) /
      (Real.cosh γ ^ 2 - Real.sin β ^ 2)) / Real.tanh γ ^ 2)| ≤ 8 * β ^ 2 := by
  have hβ2_le : β ^ 2 ≤ 1 / 16 := (pow_le_pow_left₀ hβ0.le hβ 2).trans (by norm_num)
  have hsb_le : Real.sin β ^ 2 ≤ β ^ 2 :=
    pow_le_pow_left₀ (Real.sin_nonneg_of_nonneg_of_le_pi hβ0.le (by linarith [Real.pi_gt_three]))
      (Real.sin_le hβ0.le) 2
  have hsb_nn : 0 ≤ Real.sin β ^ 2 := sq_nonneg _
  have hsh_ge1 : 1 ≤ Real.sinh γ := by rw [← sinh_pi_mul_xiStar]; exact Real.sinh_le_sinh.mpr hγ
  have hch_ge1 : 1 ≤ Real.cosh γ := Real.one_le_cosh γ
  have hsh2_ge1 : 1 ≤ Real.sinh γ ^ 2 := one_le_pow₀ hsh_ge1
  have hch2_ge1 : 1 ≤ Real.cosh γ ^ 2 := one_le_pow₀ hch_ge1
  set R2 := ((Real.sinh γ ^ 2 + Real.sin β ^ 2) /
    (Real.cosh γ ^ 2 - Real.sin β ^ 2)) / Real.tanh γ ^ 2
  have hR2_eq : R2 = (1 + Real.sin β ^ 2 / Real.sinh γ ^ 2) /
      (1 - Real.sin β ^ 2 / Real.cosh γ ^ 2) := by
    dsimp [R2]; rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [(by linarith : Real.sinh γ ≠ 0), (by linarith : Real.cosh γ ≠ 0)]
  have h1_lo : 1 ≤ 1 + Real.sin β ^ 2 / Real.sinh γ ^ 2 := by
    have : 0 ≤ Real.sin β ^ 2 / Real.sinh γ ^ 2 := by positivity
    linarith
  have h1_up : 1 + Real.sin β ^ 2 / Real.sinh γ ^ 2 ≤ 1 + β ^ 2 := by
    have : Real.sin β ^ 2 / Real.sinh γ ^ 2 ≤ Real.sin β ^ 2 / 1 :=
      div_le_div_of_nonneg_left hsb_nn one_pos hsh2_ge1
    linarith
  have h2_lo : 1 - β ^ 2 ≤ 1 - Real.sin β ^ 2 / Real.cosh γ ^ 2 := by
    have : Real.sin β ^ 2 / Real.cosh γ ^ 2 ≤ Real.sin β ^ 2 / 1 :=
      div_le_div_of_nonneg_left hsb_nn one_pos hch2_ge1
    linarith
  have h2_up : 1 - Real.sin β ^ 2 / Real.cosh γ ^ 2 ≤ 1 := by
    have : 0 ≤ Real.sin β ^ 2 / Real.cosh γ ^ 2 := by positivity
    linarith
  have h2_pos : 0 < 1 - Real.sin β ^ 2 / Real.cosh γ ^ 2 := by linarith
  have hR2_ge1 : 1 ≤ R2 := by rw [hR2_eq, one_le_div h2_pos]; linarith
  have hR2_up : R2 ≤ 1 + 4 * β ^ 2 := by
    rw [hR2_eq, div_le_iff₀ h2_pos]
    have hb4 : β ^ 4 ≤ β ^ 2 / 16 := by
      have := mul_le_mul_of_nonneg_right hβ2_le (sq_nonneg β)
      linarith [show β ^ 4 = β ^ 2 * β ^ 2 by ring]
    have hmul : (1 + 4 * β ^ 2) * (1 - β ^ 2) ≤
        (1 + 4 * β ^ 2) * (1 - Real.sin β ^ 2 / Real.cosh γ ^ 2) :=
      mul_le_mul_of_nonneg_left h2_lo (by positivity)
    have hid : (1 + 4 * β ^ 2) * (1 - β ^ 2) = 1 + 3 * β ^ 2 - 4 * β ^ 4 := by ring
    linarith
  have h_t : |R2 - 1| ≤ 4 * β ^ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have h_half : |R2 - 1| ≤ 1 / 2 := h_t.trans (by linarith)
  simpa [add_sub_cancel] using (abs_log_one_add_le h_half).trans (by linarith)

private lemma hole_site_err_tail {α β γ vTilde η₀ ℓ m_gm n_r j_r : ℝ}
    (hβ_pos : 0 < β) (hℓ_pos : 0 < ℓ) (hgm_pos : 0 < m_gm) (hη₀0 : 0 < η₀) (hη₀1 : η₀ ≤ 1 / 4)
    (hj1 : 1 ≤ j_r) (hℓm_le : m_gm ≤ 2 * ℓ)
    (hα_bd : |α| ≤ π * ((j_r + 2) * ℓ) / 2)
    (hβ_def : β = π * (η₀ * m_gm) / 2)
    (h_b1 : |Real.log (((Real.sinh α ^ 2 + Real.sin β ^ 2) /
        (Real.cosh α ^ 2 - Real.sin β ^ 2)) / (α ^ 2 + β ^ 2))| ≤ 16 * (α ^ 2 + β ^ 2))
    (h_b2 : |Real.log (((Real.sinh γ ^ 2 + Real.sin β ^ 2) /
        (Real.cosh γ ^ 2 - Real.sin β ^ 2)) / Real.tanh γ ^ 2)| ≤ 8 * β ^ 2)
    (h_b3 : |Real.log ((α ^ 2 + β ^ 2) / ((vTilde ^ 2 + η₀ ^ 2) * (π * ℓ / 2) ^ 2))| ≤
        (64 * (j_r + 1) ^ 3 / η₀ ^ 2) / n_r) :
    |Real.log (((Real.sinh α ^ 2 + Real.sin β ^ 2) /
        (Real.cosh α ^ 2 - Real.sin β ^ 2)) / (α ^ 2 + β ^ 2)) +
      Real.log (((Real.sinh γ ^ 2 + Real.sin β ^ 2) /
        (Real.cosh γ ^ 2 - Real.sin β ^ 2)) / Real.tanh γ ^ 2) +
      Real.log ((α ^ 2 + β ^ 2) / ((vTilde ^ 2 + η₀ ^ 2) * (π * ℓ / 2) ^ 2))| ≤
      (64 * (j_r + 1) ^ 3 / η₀ ^ 2) / n_r + 40 * π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2 := by
  have hpi := Real.pi_pos
  have hα_sq : α ^ 2 ≤ π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2 := by
    have hnn : 0 ≤ π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2 := by positivity
    calc α ^ 2 = |α| ^ 2 := (sq_abs α).symm
      _ ≤ (π * ((j_r + 2) * ℓ) / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hα_bd 2
      _ = (1 / 4 : ℝ) * (π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2) := by ring
      _ ≤ 1 * (π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2) :=
          mul_le_mul_of_nonneg_right (by norm_num) hnn
      _ = π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2 := one_mul _
  have hβ_le : β ≤ π * ℓ := by
    have hpiℓ_nn : 0 ≤ π * ℓ := mul_nonneg hpi.le hℓ_pos.le
    have h_prod : η₀ * m_gm ≤ (1 / 4 : ℝ) * (2 * ℓ) :=
      mul_le_mul hη₀1 hℓm_le hgm_pos.le (by norm_num)
    calc β = π * (η₀ * m_gm) / 2 := hβ_def
      _ ≤ π * ((1 / 4 : ℝ) * (2 * ℓ)) / 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h_prod hpi.le) two_pos.le
      _ = (1 / 4 : ℝ) * (π * ℓ) := by ring
      _ ≤ 1 * (π * ℓ) := mul_le_mul_of_nonneg_right (by norm_num) hpiℓ_nn
      _ = π * ℓ := one_mul _
  have hβ_sq : β ^ 2 ≤ π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2 := by
    have hj2 : 1 ≤ (j_r + 2) ^ 2 := one_le_pow₀ (by linarith)
    calc β ^ 2 ≤ (π * ℓ) ^ 2 := pow_le_pow_left₀ hβ_pos.le hβ_le 2
      _ = (π ^ 2 * 1) * ℓ ^ 2 := by ring
      _ ≤ (π ^ 2 * (j_r + 2) ^ 2) * ℓ ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hj2 (sq_nonneg π)) (sq_nonneg ℓ)
      _ = π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2 := by ring
  have hαβ_ℓ : 16 * (α ^ 2 + β ^ 2) + 8 * β ^ 2 ≤ 40 * π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2 := by
    calc 16 * (α ^ 2 + β ^ 2) + 8 * β ^ 2
        ≤ 16 * (π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2 + π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2) +
            8 * (π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2) :=
          add_le_add
            (mul_le_mul_of_nonneg_left (add_le_add hα_sq hβ_sq) (by norm_num))
            (mul_le_mul_of_nonneg_left hβ_sq (by norm_num))
      _ = 40 * π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2 := by ring
  calc |Real.log (((Real.sinh α ^ 2 + Real.sin β ^ 2) /
          (Real.cosh α ^ 2 - Real.sin β ^ 2)) / (α ^ 2 + β ^ 2)) +
        Real.log (((Real.sinh γ ^ 2 + Real.sin β ^ 2) /
          (Real.cosh γ ^ 2 - Real.sin β ^ 2)) / Real.tanh γ ^ 2) +
        Real.log ((α ^ 2 + β ^ 2) / ((vTilde ^ 2 + η₀ ^ 2) * (π * ℓ / 2) ^ 2))|
      ≤ |Real.log (((Real.sinh α ^ 2 + Real.sin β ^ 2) /
          (Real.cosh α ^ 2 - Real.sin β ^ 2)) / (α ^ 2 + β ^ 2))| +
        |Real.log (((Real.sinh γ ^ 2 + Real.sin β ^ 2) /
          (Real.cosh γ ^ 2 - Real.sin β ^ 2)) / Real.tanh γ ^ 2)| +
        |Real.log ((α ^ 2 + β ^ 2) / ((vTilde ^ 2 + η₀ ^ 2) * (π * ℓ / 2) ^ 2))| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 16 * (α ^ 2 + β ^ 2) + 8 * β ^ 2 + (64 * (j_r + 1) ^ 3 / η₀ ^ 2) / n_r :=
          add_le_add (add_le_add h_b1 h_b2) h_b3
    _ ≤ 40 * π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2 + (64 * (j_r + 1) ^ 3 / η₀ ^ 2) / n_r :=
          add_le_add hαβ_ℓ le_rfl
    _ = (64 * (j_r + 1) ^ 3 / η₀ ^ 2) / n_r + 40 * π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2 := by ring

private lemma hole_site_err_K5 {c' x u η₀ : ℝ} {n j : ℕ}
    (hc' : 0 < c') (hj : 1 ≤ j) (hη₀0 : 0 < η₀) (hη₀1 : η₀ ≤ 1 / 4)
    (hx_xi : xiStar ≤ x) (hu_mem : u ∈ Ico (0 : ℝ) 1)
    (hx_eq_u : x - chiQuantile c' n = u * siteGap c' n)
    (hℓ_small : siteGap c' n ≤ 1 / (32 * ((j : ℝ) + 2)))
    (hn_4j : 4 * (j + 1) ≤ n)
    (hn_16 : 16 * (j + 1) ^ 2 ≤ n)
    (hn_ceil : Nat.ceil (64 * ((j : ℝ) + 1) ^ 3 / η₀ ^ 2) ≤ n)
    (h_diff_all : ∀ a ∈ Icc ((n : ℝ) - j - 1 / 2) ((n : ℝ) + j + 1),
      |chiQuantile c' a - chiQuantile c' n - (a - (n : ℝ)) * siteGap c' n| ≤
        4 * ((j : ℝ) + 1) ^ 2 / (n : ℝ) * siteGap c' n)
    (h_gap_all : ∀ m ∈ Finset.Icc (n - j + 1) (n + j),
      |siteGap c' m - siteGap c' n| ≤ 4 * ((j : ℝ) + 1) / (n : ℝ) * siteGap c' n) :
    ∀ m ∈ Finset.Icc (n - j + 1) (n + j),
      |Real.log (pairModQ c' η₀ x m) -
        (Real.log (((u - ((m : ℝ) - (n : ℝ))) ^ 2 + η₀ ^ 2) * (π * siteGap c' n / 2) ^ 2) +
          2 * Real.log (Real.tanh (π * (x + chiQuantile c' m) / 2)))| ≤
        (64 * ((j : ℝ) + 1) ^ 3 / η₀ ^ 2) / (n : ℝ) +
          40 * π ^ 2 * ((j : ℝ) + 2) ^ 2 * siteGap c' n ^ 2 := by
  let ℓ := siteGap c' n
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hℓ_pos : 0 < ℓ := by
    unfold ℓ siteGap
    have hn14 : (1 / 4 : ℝ) < (n : ℝ) := by
      have : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 8 ≤ n)
      linarith
    exact sub_pos.mpr (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr hn14.le)
      (Set.mem_Ici.mpr (by linarith)) (by linarith))
  have hc_pos : 0 < π * ℓ / 2 := div_pos (mul_pos Real.pi_pos hℓ_pos) two_pos
  intro m hm
  have hm_mem := Finset.mem_Icc.mp hm
  have hm2 : 2 ≤ m := by omega
  have hm_r : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hχm_nn : 0 ≤ chiQuantile c' m := xiStar_pos.le.trans (chiQuantile_spec hc' (by linarith)).1
  have hgm_pos : 0 < siteGap c' m := by
    unfold siteGap
    exact sub_pos.mpr (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith))
      (Set.mem_Ici.mpr (by linarith)) (by linarith))
  have h_m_Icc : (m : ℝ) ∈ Icc ((n : ℝ) - j - 1 / 2) ((n : ℝ) + j + 1) := by
    have hnj : (n - j : ℕ) ≤ m := by omega
    have hcast1 : ((n - j : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnj
    have hsub : ((n - j : ℕ) : ℝ) = (n : ℝ) - (j : ℝ) := Nat.cast_sub (by omega)
    have hcast2 : (m : ℝ) ≤ (n : ℝ) + (j : ℝ) := by exact_mod_cast hm_mem.2
    exact ⟨by linarith, by linarith⟩
  let α := π * (x - chiQuantile c' m) / 2
  let β := π * (η₀ * siteGap c' m) / 2
  let γ := π * (x + chiQuantile c' m) / 2
  have hβ_pos : 0 < β := div_pos (mul_pos Real.pi_pos (mul_pos hη₀0 hgm_pos)) two_pos
  have hχm_pos : 0 < chiQuantile c' m := xiStar_pos.trans (xiStar_lt_chiQuantile hc' (by linarith))
  have hx_pos : 0 < x := xiStar_pos.trans_le hx_xi
  have hγ_pos : 0 < γ := div_pos (mul_pos Real.pi_pos (add_pos hx_pos hχm_pos)) two_pos
  have h_diff_pos := h_diff_all (m : ℝ) h_m_Icc
  have h_gap_diff := h_gap_all m hm
  have h_dn1 : 4 * ((j : ℝ) + 1) ^ 2 / (n : ℝ) ≤ 1 / 4 := by
    have h4 : 16 * ((j : ℝ) + 1) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hn_16
    rw [div_le_iff₀ hn_pos]; linarith
  have h_d0 : 4 * ((j : ℝ) + 1) / (n : ℝ) ≤ 1 / 4 := by
    have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast (by omega : 1 ≤ j + 1)
    have hj_sq : (j : ℝ) + 1 ≤ ((j : ℝ) + 1) ^ 2 := by
      calc (j : ℝ) + 1 = 1 * ((j : ℝ) + 1) := (one_mul _).symm
        _ ≤ ((j : ℝ) + 1) * ((j : ℝ) + 1) := mul_le_mul_of_nonneg_right hj1 (by positivity)
        _ = ((j : ℝ) + 1) ^ 2 := by ring
    have hle : 4 * ((j : ℝ) + 1) ≤ 4 * ((j : ℝ) + 1) ^ 2 := by linarith
    exact (div_le_div_of_nonneg_right hle hn_pos.le).trans h_dn1
  have h_xχ_bd : |x - chiQuantile c' m| ≤ ((j : ℝ) + 2) * ℓ := by
    have h_tri : (x - chiQuantile c' m) = (u - ((m : ℝ) - (n : ℝ))) * ℓ -
        (chiQuantile c' m - chiQuantile c' n - ((m : ℝ) - (n : ℝ)) * ℓ) := by
      have hx_u : u * ℓ = x - chiQuantile c' n := by dsimp [ℓ]; exact hx_eq_u.symm
      calc x - chiQuantile c' m
          = (x - chiQuantile c' n - ((m : ℝ) - (n : ℝ)) * ℓ) -
              (chiQuantile c' m - chiQuantile c' n - ((m : ℝ) - (n : ℝ)) * ℓ) := by ring
        _ = (u - ((m : ℝ) - (n : ℝ))) * ℓ -
              (chiQuantile c' m - chiQuantile c' n - ((m : ℝ) - (n : ℝ)) * ℓ) := by
            rw [← hx_u]; ring
    have hu_m : |u - ((m : ℝ) - (n : ℝ))| ≤ (j : ℝ) + 1 := by
      have h1 : (n : ℝ) - (j : ℝ) ≤ (m : ℝ) := by
        have hsub : ((n - j : ℕ) : ℝ) = (n : ℝ) - (j : ℝ) := Nat.cast_sub (by omega)
        have hcast : ((n - j : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : n - j ≤ m)
        linarith
      have h2 : (m : ℝ) ≤ (n : ℝ) + (j : ℝ) := by exact_mod_cast hm_mem.2
      exact abs_le.mpr ⟨by linarith [hu_mem.1], by linarith [hu_mem.2]⟩
    calc |x - chiQuantile c' m|
        ≤ |(u - ((m : ℝ) - (n : ℝ))) * ℓ| +
            |chiQuantile c' m - chiQuantile c' n - ((m : ℝ) - (n : ℝ)) * ℓ| := by
          rw [h_tri]; exact abs_sub _ _
      _ ≤ ((j : ℝ) + 1) * ℓ + 4 * ((j : ℝ) + 1) ^ 2 / (n : ℝ) * ℓ := by
          rw [abs_mul, abs_of_pos hℓ_pos]; gcongr
      _ ≤ ((j : ℝ) + 1) * ℓ + (1 / 4 : ℝ) * ℓ := by gcongr
      _ ≤ ((j : ℝ) + 2) * ℓ := by linarith
  have hℓm_le : siteGap c' m ≤ 2 * ℓ := by
    have h4 : 4 * ((j : ℝ) + 1) / (n : ℝ) * ℓ ≤ (1 / 4 : ℝ) * ℓ :=
      mul_le_mul_of_nonneg_right h_d0 hℓ_pos.le
    linarith [(abs_le.mp h_gap_diff).2]
  have hα_le : |α| ≤ 1 / 16 := by
    dsimp [α]
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]
    have hpi4 : π < 4 := by linarith [Real.pi_lt_d4]
    calc π * |x - chiQuantile c' m| / 2
        ≤ π * (((j : ℝ) + 2) * ℓ) / 2 := by gcongr
      _ ≤ 4 * (((j : ℝ) + 2) * (1 / (32 * ((j : ℝ) + 2)))) / 2 := by
          gcongr
      _ = 1 / 16 := by field_simp [(by positivity : (0 : ℝ) < (j : ℝ) + 2)]; ring
  have hβ_le : β ≤ 1 / 16 := by
    dsimp [β]
    have hpi4 : π < 4 := by linarith [Real.pi_lt_d4]
    calc π * (η₀ * siteGap c' m) / 2
        ≤ 4 * ((1 / 4 : ℝ) * (2 * ℓ)) / 2 := by gcongr
      _ = ℓ := by ring
      _ ≤ 1 / 16 := by
          have : (1 : ℝ) ≤ (j : ℝ) + 2 := by linarith
          calc ℓ ≤ 1 / (32 * ((j : ℝ) + 2)) := hℓ_small
            _ ≤ 1 / (32 * 1) := by gcongr
            _ ≤ 1 / 16 := by norm_num
  have h_S_le : Real.sin β ^ 2 ≤ 1 / 2 := by
    have hsb1 : Real.sin β ≤ 1 / 4 := (Real.sin_le hβ_pos.le).trans (hβ_le.trans (by norm_num))
    have hsnn : 0 ≤ Real.sin β := Real.sin_nonneg_of_nonneg_of_le_pi hβ_pos.le (by linarith [Real.pi_gt_three])
    exact (pow_le_pow_left₀ hsnn hsb1 2).trans (by norm_num)
  have hq_eq : pairModQ c' η₀ x m =
      ((Real.sinh α ^ 2 + Real.sin β ^ 2) / (Real.cosh α ^ 2 - Real.sin β ^ 2)) *
        ((Real.sinh γ ^ 2 + Real.sin β ^ 2) / (Real.cosh γ ^ 2 - Real.sin β ^ 2)) := by
    unfold pairModQ; rw [blaschkePairQ_eq]
  have hα2β2_pos : 0 < α ^ 2 + β ^ 2 := by positivity
  have h_num1_pos : 0 < Real.sinh α ^ 2 + Real.sin β ^ 2 := by
    have hsn : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hβ_pos (by linarith [Real.pi_gt_three])
    positivity
  have h_den1_pos : 0 < Real.cosh α ^ 2 - Real.sin β ^ 2 := by
    have hch1 : 1 ≤ Real.cosh α ^ 2 := one_le_pow₀ (Real.one_le_cosh α)
    linarith
  have h_minus_bd : |Real.log (((Real.sinh α ^ 2 + Real.sin β ^ 2) /
        (Real.cosh α ^ 2 - Real.sin β ^ 2)) / (α ^ 2 + β ^ 2))| ≤
      16 * (α ^ 2 + β ^ 2) := log_ratio_minus_bound hα_le hβ_pos hβ_le
  have hγ_xi : π * xiStar ≤ γ := by
    have hχm_xi : xiStar ≤ chiQuantile c' m := (chiQuantile_spec hc' (by linarith)).1
    dsimp [γ]
    have h1 : xiStar ≤ (x + chiQuantile c' m) / 2 := by linarith
    have hpi := Real.pi_pos
    calc π * xiStar ≤ π * ((x + chiQuantile c' m) / 2) := mul_le_mul_of_nonneg_left h1 hpi.le
      _ = π * (x + chiQuantile c' m) / 2 := by ring
  have h_plus_bd : |Real.log (((Real.sinh γ ^ 2 + Real.sin β ^ 2) /
        (Real.cosh γ ^ 2 - Real.sin β ^ 2)) / Real.tanh γ ^ 2)| ≤ 8 * β ^ 2 :=
    log_ratio_plus_bound hγ_xi hβ_pos (hβ_le.trans (by norm_num))
  have hsh_ge1 : 1 ≤ Real.sinh γ := by rw [← sinh_pi_mul_xiStar]; exact Real.sinh_le_sinh.mpr hγ_xi
  have hch_ge1 : 1 ≤ Real.cosh γ := Real.one_le_cosh γ
  have h_den2_pos : 0 < Real.cosh γ ^ 2 - Real.sin β ^ 2 := by
    have hch2 : 1 ≤ Real.cosh γ ^ 2 := one_le_pow₀ hch_ge1
    linarith [h_S_le]
  let v_m := (x - chiQuantile c' m) / ℓ
  let vTilde := u - ((m : ℝ) - (n : ℝ))
  let η_m := η₀ * (siteGap c' m / ℓ)
  have hden_m_pos : 0 < vTilde ^ 2 + η₀ ^ 2 := by positivity
  have hnum_m_pos : 0 < v_m ^ 2 + η_m ^ 2 := by
    have : 0 < η_m := by positivity
    positivity
  have h_ratio_m_eq : (α ^ 2 + β ^ 2) / ((vTilde ^ 2 + η₀ ^ 2) * (π * ℓ / 2) ^ 2) =
      (v_m ^ 2 + η_m ^ 2) / (vTilde ^ 2 + η₀ ^ 2) := by
    dsimp [α, β, v_m, η_m]; field_simp [Real.pi_ne_zero, hℓ_pos.ne']
  have h_vm_diff : |v_m - vTilde| ≤ 4 * ((j : ℝ) + 1) ^ 2 / (n : ℝ) := by
    have heq : v_m - vTilde = -(chiQuantile c' m - chiQuantile c' n - ((m : ℝ) - (n : ℝ)) * ℓ) / ℓ := by
      have hx_u : u * ℓ = x - chiQuantile c' n := by dsimp [ℓ]; exact hx_eq_u.symm
      dsimp [v_m, vTilde]
      calc (x - chiQuantile c' m) / ℓ - (u - ((m : ℝ) - (n : ℝ)))
          = ((x - chiQuantile c' m) - u * ℓ + ((m : ℝ) - (n : ℝ)) * ℓ) / ℓ := by
              field_simp [hℓ_pos.ne']; ring
        _ = -(chiQuantile c' m - chiQuantile c' n - ((m : ℝ) - (n : ℝ)) * ℓ) / ℓ := by
              rw [hx_u]; ring
    rw [heq, abs_div, abs_neg, abs_of_pos hℓ_pos, div_le_iff₀ hℓ_pos]
    exact h_diff_pos
  have h_ηm_diff : |η_m - η₀| ≤ η₀ * (4 * ((j : ℝ) + 1) / (n : ℝ)) := by
    have heq : η_m - η₀ = η₀ * ((siteGap c' m - ℓ) / ℓ) := by
      dsimp [η_m]; field_simp [hℓ_pos.ne']
    rw [heq, abs_mul, abs_of_pos hη₀0, abs_div, abs_of_pos hℓ_pos]
    refine mul_le_mul_of_nonneg_left ((div_le_iff₀ hℓ_pos).mpr h_gap_diff) hη₀0.le
  have hvTilde_bd : |vTilde| ≤ (j : ℝ) + 1 := by
    have h1 : (n : ℝ) - (j : ℝ) ≤ (m : ℝ) := by
      have hsub : ((n - j : ℕ) : ℝ) = (n : ℝ) - (j : ℝ) := Nat.cast_sub (by omega)
      have hcast : ((n - j : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : n - j ≤ m)
      linarith
    have h2 : (m : ℝ) ≤ (n : ℝ) + (j : ℝ) := by exact_mod_cast hm_mem.2
    exact abs_le.mpr ⟨by dsimp [vTilde]; linarith [hu_mem.1], by dsimp [vTilde]; linarith [hu_mem.2]⟩
  have h_model_bd : |Real.log ((α ^ 2 + β ^ 2) / ((vTilde ^ 2 + η₀ ^ 2) * (π * ℓ / 2) ^ 2))| ≤
      (64 * ((j : ℝ) + 1) ^ 3 / η₀ ^ 2) / (n : ℝ) := by
    rw [h_ratio_m_eq]
    set Rm := (v_m ^ 2 + η_m ^ 2) / (vTilde ^ 2 + η₀ ^ 2)
    have h_num_diff : |(v_m ^ 2 + η_m ^ 2) - (vTilde ^ 2 + η₀ ^ 2)| ≤
        16 * ((j : ℝ) + 1) ^ 3 / (n : ℝ) + 12 * η₀ ^ 2 * ((j : ℝ) + 1) / (n : ℝ) := by
      have h_v : |v_m ^ 2 - vTilde ^ 2| ≤ 16 * ((j : ℝ) + 1) ^ 3 / (n : ℝ) := by
        have hv_sum : |v_m + vTilde| ≤ 2 * ((j : ℝ) + 1) + 1 / 4 := by
          have : v_m + vTilde = 2 * vTilde + (v_m - vTilde) := by ring
          rw [this]
          have hv1 : |2 * vTilde| ≤ 2 * ((j : ℝ) + 1) := by
            rw [abs_mul, abs_two]; linarith
          have hv2 : |v_m - vTilde| ≤ 1 / 4 := h_vm_diff.trans h_dn1
          exact (abs_add_le _ _).trans (by linarith)
        have h_prod : |v_m ^ 2 - vTilde ^ 2| = |v_m - vTilde| * |v_m + vTilde| := by
          rw [show v_m ^ 2 - vTilde ^ 2 = (v_m - vTilde) * (v_m + vTilde) by ring, abs_mul]
        rw [h_prod]
        calc |v_m - vTilde| * |v_m + vTilde|
            ≤ (4 * ((j : ℝ) + 1) ^ 2 / (n : ℝ)) * (2 * ((j : ℝ) + 1) + 1 / 4) :=
              mul_le_mul h_vm_diff hv_sum (abs_nonneg _) (by positivity)
          _ ≤ (4 * ((j : ℝ) + 1) ^ 2 / (n : ℝ)) * (4 * ((j : ℝ) + 1)) := by
              have hj_ge1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith
              gcongr; linarith
          _ = 16 * ((j : ℝ) + 1) ^ 3 / (n : ℝ) := by ring
      have h_η : |η_m ^ 2 - η₀ ^ 2| ≤ 12 * η₀ ^ 2 * ((j : ℝ) + 1) / (n : ℝ) := by
        have hη_sum : |η_m + η₀| ≤ 3 * η₀ := by
          have : η_m + η₀ = 2 * η₀ + (η_m - η₀) := by ring
          rw [this]
          have h1 : |2 * η₀| = 2 * η₀ := abs_of_pos (by positivity)
          have h2 : η₀ * (4 * ((j : ℝ) + 1) / (n : ℝ)) ≤ η₀ * (1 / 4 : ℝ) :=
            mul_le_mul_of_nonneg_left h_d0 hη₀0.le
          exact (abs_add_le _ _).trans (by linarith)
        have h_prod : |η_m ^ 2 - η₀ ^ 2| = |η_m - η₀| * |η_m + η₀| := by
          rw [show η_m ^ 2 - η₀ ^ 2 = (η_m - η₀) * (η_m + η₀) by ring, abs_mul]
        rw [h_prod]
        calc |η_m - η₀| * |η_m + η₀|
            ≤ (η₀ * (4 * ((j : ℝ) + 1) / (n : ℝ))) * (3 * η₀) :=
              mul_le_mul h_ηm_diff hη_sum (abs_nonneg _) (by positivity)
          _ = 12 * η₀ ^ 2 * ((j : ℝ) + 1) / (n : ℝ) := by ring
      have h_rew : (v_m ^ 2 + η_m ^ 2) - (vTilde ^ 2 + η₀ ^ 2) =
          (v_m ^ 2 - vTilde ^ 2) + (η_m ^ 2 - η₀ ^ 2) := by ring
      rw [h_rew]
      exact (abs_add_le _ _).trans (add_le_add h_v h_η)
    have hRm_sub : |Rm - 1| ≤ (32 * ((j : ℝ) + 1) ^ 3 / η₀ ^ 2) / (n : ℝ) := by
      have h_eq : Rm - 1 = ((v_m ^ 2 + η_m ^ 2) - (vTilde ^ 2 + η₀ ^ 2)) / (vTilde ^ 2 + η₀ ^ 2) := by
        dsimp [Rm]; field_simp [hden_m_pos.ne']
      rw [h_eq, abs_div, abs_of_pos hden_m_pos]
      have h_den_η : η₀ ^ 2 ≤ vTilde ^ 2 + η₀ ^ 2 := by linarith [sq_nonneg vTilde]
      calc |(v_m ^ 2 + η_m ^ 2) - (vTilde ^ 2 + η₀ ^ 2)| / (vTilde ^ 2 + η₀ ^ 2)
          ≤ (16 * ((j : ℝ) + 1) ^ 3 / (n : ℝ) + 12 * η₀ ^ 2 * ((j : ℝ) + 1) / (n : ℝ)) / η₀ ^ 2 :=
            div_le_div₀ (by positivity) h_num_diff (sq_pos_of_pos hη₀0) h_den_η
        _ = (16 * ((j : ℝ) + 1) ^ 3 / η₀ ^ 2 + 12 * ((j : ℝ) + 1)) / (n : ℝ) := by
            field_simp [hη₀0.ne', hn_pos.ne']
        _ ≤ (32 * ((j : ℝ) + 1) ^ 3 / η₀ ^ 2) / (n : ℝ) := by
            gcongr
            have hη_le1 : η₀ ^ 2 ≤ 1 := by
              have := pow_le_pow_left₀ hη₀0.le hη₀1 2
              linarith
            have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith
            have hj3 : (j : ℝ) + 1 ≤ ((j : ℝ) + 1) ^ 3 := by
              have := mul_le_mul_of_nonneg_left (one_le_pow₀ (n := 2) hj1) (by linarith : (0 : ℝ) ≤ (j : ℝ) + 1)
              linarith [show ((j : ℝ) + 1) * ((j : ℝ) + 1) ^ 2 = ((j : ℝ) + 1) ^ 3 by ring]
            rw [le_div_iff₀ (sq_pos_of_pos hη₀0)]
            have hcancel : (16 * ((j : ℝ) + 1) ^ 3 / η₀ ^ 2 + 12 * ((j : ℝ) + 1)) * η₀ ^ 2 =
                16 * ((j : ℝ) + 1) ^ 3 + 12 * ((j : ℝ) + 1) * η₀ ^ 2 := by
              field_simp [hη₀0.ne']
            have h12 : 12 * ((j : ℝ) + 1) * η₀ ^ 2 ≤ 12 * ((j : ℝ) + 1) * 1 :=
              mul_le_mul_of_nonneg_left hη_le1 (by positivity)
            linarith
    have hRm_half : |Rm - 1| ≤ 1 / 2 := by
      have hNj_bound : (64 * ((j : ℝ) + 1) ^ 3 / η₀ ^ 2) ≤ (n : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hn_ceil)
      calc |Rm - 1| ≤ (32 * ((j : ℝ) + 1) ^ 3 / η₀ ^ 2) / (n : ℝ) := hRm_sub
        _ ≤ (32 * ((j : ℝ) + 1) ^ 3 / η₀ ^ 2) / (64 * ((j : ℝ) + 1) ^ 3 / η₀ ^ 2) := by
            gcongr
        _ = 1 / 2 := by
            field_simp [(by positivity : (0 : ℝ) < ((j : ℝ) + 1) ^ 3), hη₀0.ne']; ring
    have hmul2 : 2 * |Rm - 1| ≤ (64 * ((j : ℝ) + 1) ^ 3 / η₀ ^ 2) / (n : ℝ) :=
      (mul_le_mul_of_nonneg_left hRm_sub two_pos.le).trans_eq (by ring)
    simpa [add_sub_cancel] using (abs_log_one_add_le hRm_half).trans hmul2
  have hq_pos : 0 < pairModQ c' η₀ x m := by
    rw [hq_eq]
    have hsg_pos : 0 < Real.sinh γ ^ 2 + Real.sin β ^ 2 :=
      add_pos_of_pos_of_nonneg (pow_pos (Real.sinh_pos_iff.mpr hγ_pos) 2) (sq_nonneg _)
    exact mul_pos (div_pos h_num1_pos h_den1_pos) (div_pos hsg_pos h_den2_pos)
  have hthγ_pos : 0 < Real.tanh γ := by
    rw [Real.tanh_eq_sinh_div_cosh]; exact div_pos (Real.sinh_pos_iff.mpr hγ_pos) (Real.cosh_pos _)
  have h_m_pos : 0 < (vTilde ^ 2 + η₀ ^ 2) * (π * ℓ / 2) ^ 2 :=
    mul_pos hden_m_pos (sq_pos_of_pos hc_pos)
  have h_log_id : Real.log (pairModQ c' η₀ x m) -
      (Real.log ((vTilde ^ 2 + η₀ ^ 2) * (π * ℓ / 2) ^ 2) + 2 * Real.log (Real.tanh γ)) =
      Real.log (((Real.sinh α ^ 2 + Real.sin β ^ 2) /
        (Real.cosh α ^ 2 - Real.sin β ^ 2)) / (α ^ 2 + β ^ 2)) +
      Real.log (((Real.sinh γ ^ 2 + Real.sin β ^ 2) /
        (Real.cosh γ ^ 2 - Real.sin β ^ 2)) / Real.tanh γ ^ 2) +
      Real.log ((α ^ 2 + β ^ 2) / ((vTilde ^ 2 + η₀ ^ 2) * (π * ℓ / 2) ^ 2)) := by
    have h1_pos : 0 < (Real.sinh α ^ 2 + Real.sin β ^ 2) / (Real.cosh α ^ 2 - Real.sin β ^ 2) :=
      div_pos h_num1_pos h_den1_pos
    have hsg_pos : 0 < Real.sinh γ ^ 2 + Real.sin β ^ 2 :=
      add_pos_of_pos_of_nonneg (pow_pos (Real.sinh_pos_iff.mpr hγ_pos) 2) (sq_nonneg _)
    have h2_pos : 0 < (Real.sinh γ ^ 2 + Real.sin β ^ 2) / (Real.cosh γ ^ 2 - Real.sin β ^ 2) :=
      div_pos hsg_pos h_den2_pos
    rw [hq_eq, Real.log_mul h1_pos.ne' h2_pos.ne',
      Real.log_div h1_pos.ne' hα2β2_pos.ne',
      Real.log_div h2_pos.ne' (sq_pos_of_pos hthγ_pos).ne',
      Real.log_div hα2β2_pos.ne' h_m_pos.ne',
      Real.log_pow]
    push_cast; ring
  rw [h_log_id]
  have hα_bd : |α| ≤ π * (((j : ℝ) + 2) * ℓ) / 2 := by
    change |π * (x - chiQuantile c' m) / 2| ≤ π * (((j : ℝ) + 2) * ℓ) / 2
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h_xχ_bd Real.pi_pos.le) two_pos.le
  exact hole_site_err_tail hβ_pos hℓ_pos hgm_pos hη₀0 hη₀1 (by exact_mod_cast hj) hℓm_le hα_bd rfl
    h_minus_bd h_plus_bd h_model_bd

private lemma hole_integral_err_K5 {c' x ℓ u aStar : ℝ} {n j : ℕ}
    (hc' : 0 < c') (hj1_r : (1 : ℝ) ≤ (j : ℝ)) (_hn1_r : (1 : ℝ) ≤ (n : ℝ)) (hn_pos : (0 : ℝ) < (n : ℝ))
    (h16_r : 16 * ((j : ℝ) + 1) ^ 2 ≤ (n : ℝ))
    (hfrac_r : 4 * ((j : ℝ) + 1) ^ 2 / (n : ℝ) ≤ 1)
    (hnj_lb : (1 / 4 : ℝ) < (n : ℝ) - (j : ℝ) - 1 / 2)
    (hℓ_pos : 0 < ℓ) (hx_nn : 0 ≤ x) (hu_mem : u ∈ Ico (0 : ℝ) 1)
    (hx_eq_u : x - chiQuantile c' n = u * ℓ)
    (haStar_Ico : aStar ∈ Ico (n : ℝ) ((n : ℝ) + 1)) (haStar_eq : chiQuantile c' aStar = x)
    (h_deriv : ∀ a ∈ Icc ((n : ℝ) - j - 1 / 2) ((n : ℝ) + j + 1),
      (1 - 4 * ((j : ℝ) + 1) / (n : ℝ)) * ℓ ≤ chiDeriv c' a ∧
        chiDeriv c' a ≤ (1 + 4 * ((j : ℝ) + 1) / (n : ℝ)) * ℓ)
    (h_diff : ∀ b ∈ Icc ((n : ℝ) - j - 1 / 2) ((n : ℝ) + j + 1),
      |chiQuantile c' b - chiQuantile c' n - (b - (n : ℝ)) * ℓ| ≤
        4 * ((j : ℝ) + 1) ^ 2 / (n : ℝ) * ℓ) :
    let A : ℝ := (n : ℝ) - (j : ℝ) + 1 / 2
    let B : ℝ := (n : ℝ) + (j : ℝ) + 1 / 2
    |∫ a in A..B, (phiVar c' x a - Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2)) -
        Real.log |aStar - a| - Real.log (π * ℓ / 2))| ≤
      2 * (j : ℝ) * (8 * ((j : ℝ) + 1) / (n : ℝ) + π ^ 2 * ((j : ℝ) + 2) ^ 2 * ℓ ^ 2 / 2) := by
  intro A B
  have hAB : A ≤ B := by dsimp [A, B]; linarith
  have hc_pos : 0 < π * ℓ / 2 := div_pos (mul_pos Real.pi_pos hℓ_pos) two_pos
  have hA14 : 1 / 4 < A := by dsimp [A]; linarith
  let E_int : ℝ → ℝ := fun a =>
    phiVar c' x a - Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2)) -
      Real.log |aStar - a| - Real.log (π * ℓ / 2)
  have h_ae : ∀ᵐ a ∂volume, a ∈ Set.uIoc A B →
      ‖E_int a‖ ≤ 8 * ((j : ℝ) + 1) / (n : ℝ) + π ^ 2 * ((j : ℝ) + 2) ^ 2 * ℓ ^ 2 / 2 := by
    have h_ne_ae : ∀ᵐ a ∂volume, a ≠ aStar := by rw [ae_iff]; simp
    filter_upwards [h_ne_ae] with a hane ha_mem
    rw [Set.uIoc_of_le hAB] at ha_mem
    have ha_gtA : A < a := ha_mem.1
    have ha_leB : a ≤ B := ha_mem.2
    have ha_Icc : a ∈ Icc ((n : ℝ) - j - 1 / 2) ((n : ℝ) + j + 1) :=
      ⟨by dsimp [A] at ha_gtA; linarith, by dsimp [B] at ha_leB; linarith⟩
    have ha14 : 1 / 4 < a := by linarith [hA14]
    have hχa_gt0 : 0 < chiQuantile c' a := xiStar_pos.trans (xiStar_lt_chiQuantile hc' ha14)
    have hχ_ne : x ≠ chiQuantile c' a := by
      rw [← haStar_eq]
      intro heq
      apply hane
      have hsm := chiQuantile_strictMonoOn hc'
      rcases lt_trichotomy a aStar with hlt | rfl | hgt
      · exact absurd heq (hsm (Set.mem_Ici.mpr ha14.le) (Set.mem_Ici.mpr (by linarith [_hn1_r, haStar_Ico.1])) hlt).ne'
      · exact rfl
      · exact absurd heq (hsm (Set.mem_Ici.mpr (by linarith [_hn1_r, haStar_Ico.1])) (Set.mem_Ici.mpr ha14.le) hgt).ne
    let z_a := π * (x - chiQuantile c' a) / 2
    have hza_ne : z_a ≠ 0 := by dsimp [z_a]; exact div_ne_zero (mul_ne_zero Real.pi_ne_zero (sub_ne_zero.mpr hχ_ne)) two_ne_zero
    have h_phi_eq : phiVar c' x a =
        Real.log |Real.tanh z_a| + Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2)) := by
      unfold phiVar realLogT blaschkeT
      have hc1 : Complex.tanh ((π : ℂ) * ((x : ℂ) - (chiQuantile c' a : ℂ)) / 2) =
          ((Real.tanh z_a : ℝ) : ℂ) := by
        have h1 : Complex.tanh ((z_a : ℝ) : ℂ) = ((Real.tanh z_a : ℝ) : ℂ) := by
          rw [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
            ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, Complex.ofReal_div]
        rw [← h1]; congr 1; dsimp [z_a]; push_cast; ring
      have hc2 : Complex.tanh ((π : ℂ) * ((x : ℂ) + (chiQuantile c' a : ℂ)) / 2) =
          ((Real.tanh (π * (x + chiQuantile c' a) / 2) : ℝ) : ℂ) := by
        have h1 : Complex.tanh ((π * (x + chiQuantile c' a) / 2 : ℝ) : ℂ) =
            ((Real.tanh (π * (x + chiQuantile c' a) / 2) : ℝ) : ℂ) := by
          rw [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
            ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, Complex.ofReal_div]
        rw [← h1]; congr 1; push_cast; ring
      rw [hc1, hc2, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      have hth2_pos : 0 < Real.tanh (π * (x + chiQuantile c' a) / 2) := by
        rw [Real.tanh_eq_sinh_div_cosh]
        have h_arg : 0 < π * (x + chiQuantile c' a) / 2 :=
          div_pos (mul_pos Real.pi_pos (by linarith)) two_pos
        exact div_pos (Real.sinh_pos_iff.mpr h_arg) (Real.cosh_pos _)
      have hth1_ne : Real.tanh z_a ≠ 0 := by
        rw [Real.tanh_eq_sinh_div_cosh]; exact div_ne_zero (Real.sinh_ne_zero.mpr hza_ne) (Real.cosh_pos _).ne'
      rw [abs_of_pos hth2_pos, Real.log_mul (abs_pos.mpr hth1_ne).ne' hth2_pos.ne']
    have h_slope_ratio : |Real.log (|x - chiQuantile c' a| / (|aStar - a| * ℓ))| ≤
        8 * ((j : ℝ) + 1) / (n : ℝ) := by
      have hm := min_le_max (a := a) (b := aStar)
      have hmin_ge : (n : ℝ) - j - 1 / 2 ≤ min a aStar := le_min ha_Icc.1 (by linarith [haStar_Ico.1])
      have hmax_le : max a aStar ≤ (n : ℝ) + j + 1 := max_le ha_Icc.2 (by linarith [haStar_Ico.2])
      have hmin14 : 1 / 4 < min a aStar := by linarith [hnj_lb]
      have hcont : ContinuousOn (chiDeriv c') (Icc (min a aStar) (max a aStar)) := fun t ht =>
        (hasDerivAt_chiQuantile hc' (by linarith [hmin14, ht.1])).2.continuousAt.continuousWithinAt
      have h_int : chiQuantile c' (max a aStar) - chiQuantile c' (min a aStar) =
          ∫ t in (min a aStar)..(max a aStar), chiDeriv c' t := by
        refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => ?_)
          (hcont.intervalIntegrable_of_Icc hm)).symm
        rw [Set.uIcc_of_le hm] at ht
        exact (hasDerivAt_chiQuantile hc' (by linarith [hmin14, ht.1])).1
      have h_len : max a aStar - min a aStar = |aStar - a| := by
        rcases le_total a aStar with h | h
        · rw [max_eq_right h, min_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
        · rw [max_eq_left h, min_eq_right h, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h)]
      have h_abs_chi : |x - chiQuantile c' a| =
          chiQuantile c' (max a aStar) - chiQuantile c' (min a aStar) := by
        rw [← haStar_eq]
        rcases le_total a aStar with h | h
        · rw [max_eq_right h, min_eq_left h, abs_of_nonneg]
          exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn
            (Set.mem_Ici.mpr ha14.le) (Set.mem_Ici.mpr (by linarith [_hn1_r, haStar_Ico.1])) h)
        · rw [max_eq_left h, min_eq_right h, abs_sub_comm, abs_of_nonneg]
          exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn
            (Set.mem_Ici.mpr (by linarith [_hn1_r, haStar_Ico.1])) (Set.mem_Ici.mpr ha14.le) h)
      have h_bounds : (1 - 4 * ((j : ℝ) + 1) / (n : ℝ)) * (|aStar - a| * ℓ) ≤
            |x - chiQuantile c' a| ∧
          |x - chiQuantile c' a| ≤ (1 + 4 * ((j : ℝ) + 1) / (n : ℝ)) * (|aStar - a| * ℓ) := by
        have hint_m : IntervalIntegrable (chiDeriv c') volume (min a aStar) (max a aStar) :=
          hcont.intervalIntegrable_of_Icc hm
        have hlo := intervalIntegral.integral_mono_on hm
          (intervalIntegrable_const (μ := volume)) hint_m fun t ht =>
            (h_deriv t ⟨hmin_ge.trans ht.1, ht.2.trans hmax_le⟩).1
        have hup := intervalIntegral.integral_mono_on hm
          hint_m (intervalIntegrable_const (μ := volume)) fun t ht =>
            (h_deriv t ⟨hmin_ge.trans ht.1, ht.2.trans hmax_le⟩).2
        rw [intervalIntegral.integral_const, smul_eq_mul, h_len, ← h_int, ← h_abs_chi] at hlo
        rw [intervalIntegral.integral_const, smul_eq_mul, h_len, ← h_int, ← h_abs_chi] at hup
        exact ⟨by linarith, by linarith⟩
      have h_den_pos : 0 < |aStar - a| * ℓ := mul_pos (abs_pos.mpr (sub_ne_zero.mpr hane.symm)) hℓ_pos
      set Rs := |x - chiQuantile c' a| / (|aStar - a| * ℓ)
      have hRs_t : |Rs - 1| ≤ 4 * ((j : ℝ) + 1) / (n : ℝ) := by
        rw [abs_le]
        constructor
        · have : 1 - 4 * ((j : ℝ) + 1) / (n : ℝ) ≤ Rs := (le_div_iff₀ h_den_pos).mpr h_bounds.1
          linarith
        · have : Rs ≤ 1 + 4 * ((j : ℝ) + 1) / (n : ℝ) := (div_le_iff₀ h_den_pos).mpr h_bounds.2
          linarith
      have h_half : |Rs - 1| ≤ 1 / 2 := hRs_t.trans (by
        have hj_le : (j : ℝ) + 1 ≤ ((j : ℝ) + 1) ^ 2 := by
          calc (j : ℝ) + 1 = 1 * ((j : ℝ) + 1) := (one_mul _).symm
            _ ≤ ((j : ℝ) + 1) * ((j : ℝ) + 1) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
            _ = ((j : ℝ) + 1) ^ 2 := by ring
        have h8 : 8 * ((j : ℝ) + 1) ≤ (n : ℝ) := by linarith
        rw [div_le_iff₀ hn_pos]; linarith)
      simpa [Rs, add_sub_cancel] using
        (abs_log_one_add_le h_half).trans ((mul_le_mul_of_nonneg_left hRs_t two_pos.le).trans_eq (by ring))
    have h_za_sq : z_a ^ 2 / 2 ≤ π ^ 2 * ((j : ℝ) + 2) ^ 2 * ℓ ^ 2 / 2 := by
      have ha_dist : |x - chiQuantile c' a| ≤ ((j : ℝ) + 2) * ℓ := by
        have h_bd_a := h_diff a ha_Icc
        have hu0 : 0 ≤ u := hu_mem.1
        have hu1 : u < 1 := hu_mem.2
        have h_ab_diff : |a - ((n : ℝ) + u)| ≤ (j : ℝ) + 1 := by
          dsimp [A] at ha_gtA
          dsimp [B] at ha_leB
          exact abs_le.mpr ⟨by linarith, by linarith⟩
        have h_rew : x - chiQuantile c' a = (((n : ℝ) + u) - a) * ℓ -
            (chiQuantile c' a - chiQuantile c' n - (a - (n : ℝ)) * ℓ) := by
          calc x - chiQuantile c' a
              = (x - chiQuantile c' n + ((n : ℝ) - a) * ℓ) -
                  (chiQuantile c' a - chiQuantile c' n - (a - (n : ℝ)) * ℓ) := by ring
            _ = (u * ℓ + ((n : ℝ) - a) * ℓ) -
                  (chiQuantile c' a - chiQuantile c' n - (a - (n : ℝ)) * ℓ) := by rw [hx_eq_u]
            _ = (((n : ℝ) + u) - a) * ℓ -
                  (chiQuantile c' a - chiQuantile c' n - (a - (n : ℝ)) * ℓ) := by ring
        calc |x - chiQuantile c' a|
            ≤ |(((n : ℝ) + u) - a) * ℓ| +
                |chiQuantile c' a - chiQuantile c' n - (a - (n : ℝ)) * ℓ| := by
              rw [h_rew]; exact abs_sub _ _
          _ ≤ ((j : ℝ) + 1) * ℓ + 4 * ((j : ℝ) + 1) ^ 2 / (n : ℝ) * ℓ := by
              rw [abs_mul, abs_of_pos hℓ_pos, abs_sub_comm ((n : ℝ) + u) a]; gcongr
          _ ≤ ((j : ℝ) + 2) * ℓ := by
              have hmul : (4 * ((j : ℝ) + 1) ^ 2 / (n : ℝ)) * ℓ ≤ 1 * ℓ :=
                mul_le_mul_of_nonneg_right hfrac_r hℓ_pos.le
              linarith
      have hza_bd : |z_a| ≤ π * (((j : ℝ) + 2) * ℓ) / 2 := by
        dsimp [z_a]; rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]; gcongr
      have hza_sq_le : z_a ^ 2 ≤ (π * (((j : ℝ) + 2) * ℓ) / 2) ^ 2 := by
        rw [← sq_abs z_a]; exact pow_le_pow_left₀ (abs_nonneg _) hza_bd 2
      calc z_a ^ 2 / 2 ≤ (π * (((j : ℝ) + 2) * ℓ) / 2) ^ 2 / 2 := by linarith
        _ = (1 / 4 : ℝ) * (π ^ 2 * ((j : ℝ) + 2) ^ 2 * ℓ ^ 2 / 2) := by ring
        _ ≤ π ^ 2 * ((j : ℝ) + 2) ^ 2 * ℓ ^ 2 / 2 := by
            have hnn : 0 ≤ π ^ 2 * ((j : ℝ) + 2) ^ 2 * ℓ ^ 2 / 2 := by positivity
            linarith
    have hE_eq : E_int a = Real.log (|Real.tanh z_a| / |z_a|) +
        Real.log (|x - chiQuantile c' a| / (|aStar - a| * ℓ)) := by
      dsimp [E_int]
      rw [h_phi_eq]
      have hth_ne : Real.tanh z_a ≠ 0 := by
        rw [Real.tanh_eq_sinh_div_cosh]; exact div_ne_zero (Real.sinh_ne_zero.mpr hza_ne) (Real.cosh_pos _).ne'
      have hxa_ne : x - chiQuantile c' a ≠ 0 := sub_ne_zero.mpr hχ_ne
      have has_ne : aStar - a ≠ 0 := sub_ne_zero.mpr hane.symm
      rw [Real.log_div (abs_pos.mpr hth_ne).ne' (abs_pos.mpr hza_ne).ne',
        Real.log_div (abs_pos.mpr hxa_ne).ne' (mul_ne_zero (abs_pos.mpr has_ne).ne' hℓ_pos.ne'),
        Real.log_mul (abs_pos.mpr has_ne).ne' hℓ_pos.ne']
      have hz_eq : |z_a| = (π * ℓ / 2) * (|x - chiQuantile c' a| / ℓ) := by
        dsimp [z_a]
        rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]
        field_simp [hℓ_pos.ne']
      have h_z_log : Real.log |z_a| = Real.log (π * ℓ / 2) + Real.log |x - chiQuantile c' a| - Real.log ℓ := by
        rw [hz_eq, Real.log_mul hc_pos.ne' (div_pos (abs_pos.mpr hxa_ne) hℓ_pos).ne',
          Real.log_div (abs_pos.mpr hxa_ne).ne' hℓ_pos.ne']
        ring
      rw [h_z_log]; ring
    rw [Real.norm_eq_abs, hE_eq]
    exact (abs_add_le _ _).trans
      ((add_le_add ((abs_log_tanh_div_self_le hza_ne).trans h_za_sq) h_slope_ratio).trans_eq (add_comm _ _))
  have h_norm_int := intervalIntegral.norm_integral_le_of_norm_le_const_ae h_ae
  rw [Real.norm_eq_abs] at h_norm_int
  have heq_len : |B - A| = 2 * (j : ℝ) := by
    dsimp [A, B]; rw [abs_of_nonneg (by linarith)]; ring
  rw [heq_len, mul_comm] at h_norm_int
  exact h_norm_int

private lemma hole_plus_cell_err_K5 {c' x ℓ : ℝ} {n j m : ℕ}
    (hc' : 0 < c') (hj1_r : (1 : ℝ) ≤ (j : ℝ)) (hn_pos : (0 : ℝ) < (n : ℝ)) (hn_4j : 4 * (j + 1) ≤ n)
    (hnj_lb : (1 / 4 : ℝ) < (n : ℝ) - (j : ℝ) - 1 / 2)
    (hℓ_pos : 0 < ℓ) (hx_xi : xiStar ≤ x)
    (hm : m ∈ Finset.Icc (n - j + 1) (n + j))
    (h_deriv : ∀ a ∈ Icc ((n : ℝ) - j - 1 / 2) ((n : ℝ) + j + 1),
      (1 - 4 * ((j : ℝ) + 1) / (n : ℝ)) * ℓ ≤ chiDeriv c' a ∧
        chiDeriv c' a ≤ (1 + 4 * ((j : ℝ) + 1) / (n : ℝ)) * ℓ) :
    |Real.log (Real.tanh (π * (x + chiQuantile c' m) / 2)) -
      ∫ a in ((m : ℝ) - 1 / 2)..((m : ℝ) + 1 / 2),
        Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2))| ≤
      6 * π * ((j : ℝ) + 1) * ℓ := by
  have hm_mem := Finset.mem_Icc.mp hm
  have hnj_le_m : (n : ℝ) - (j : ℝ) + 1 ≤ (m : ℝ) := by
    have hcast1 : ((n - j + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_mem.1
    have hsub : ((n - j : ℕ) : ℝ) = (n : ℝ) - (j : ℝ) := Nat.cast_sub (by omega)
    push_cast at hcast1; linarith
  have hm_le_nj : (m : ℝ) ≤ (n : ℝ) + (j : ℝ) := by exact_mod_cast hm_mem.2
  have h_cont_th : Continuous Real.tanh := by
    rw [show Real.tanh = fun y => Real.sinh y / Real.cosh y from funext Real.tanh_eq_sinh_div_cosh]
    exact Real.continuous_sinh.div Real.continuous_cosh (fun y => (Real.cosh_pos y).ne')
  have hx_nn : 0 ≤ x := xiStar_pos.le.trans hx_xi
  have h_diff_eq : Real.log (Real.tanh (π * (x + chiQuantile c' m) / 2)) -
      ∫ a in ((m : ℝ) - 1 / 2)..((m : ℝ) + 1 / 2),
        Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2)) =
      ∫ a in ((m : ℝ) - 1 / 2)..((m : ℝ) + 1 / 2),
        (Real.log (Real.tanh (π * (x + chiQuantile c' m) / 2)) -
          Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2))) := by
    have hcont : ContinuousOn (fun a => Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2)))
        (Icc ((m : ℝ) - 1 / 2) ((m : ℝ) + 1 / 2)) := by
      refine ContinuousOn.log ?_ fun a ha => ?_
      · refine h_cont_th.comp_continuousOn ?_
        refine (continuousOn_const.mul (continuousOn_const.add ?_)).div_const 2
        intro t ht
        exact (hasDerivAt_chiQuantile hc' (by linarith [hnj_lb, ht.1])).1.continuousAt.continuousWithinAt
      · have ha14 : 1 / 4 < a := by linarith [hnj_lb, ha.1]
        have hχ_pos : 0 < chiQuantile c' a := xiStar_pos.trans (xiStar_lt_chiQuantile hc' ha14)
        rw [Real.tanh_eq_sinh_div_cosh]
        have h_arg : 0 < π * (x + chiQuantile c' a) / 2 :=
          div_pos (mul_pos Real.pi_pos (by linarith)) two_pos
        exact (div_pos (Real.sinh_pos_iff.mpr h_arg) (Real.cosh_pos _)).ne'
    rw [intervalIntegral.integral_sub (intervalIntegrable_const (μ := volume))
      (hcont.intervalIntegrable_of_Icc (by linarith)), intervalIntegral.integral_const, smul_eq_mul]
    have : (m : ℝ) + 1 / 2 - ((m : ℝ) - 1 / 2) = 1 := by ring
    rw [this, one_mul]
  rw [h_diff_eq]
  have h_norm := intervalIntegral.norm_integral_le_of_norm_le_const (C := 6 * π * ((j : ℝ) + 1) * ℓ)
    (a := (m : ℝ) - 1 / 2) (b := (m : ℝ) + 1 / 2)
    (f := fun a => Real.log (Real.tanh (π * (x + chiQuantile c' m) / 2)) -
      Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2))) fun a ha => by
    rw [Set.uIoc_of_le (by linarith : (m : ℝ) - 1 / 2 ≤ (m : ℝ) + 1 / 2)] at ha
    have ha_Icc : a ∈ Icc ((n : ℝ) - j - 1 / 2) ((n : ℝ) + j + 1) :=
      ⟨by linarith [ha.1], by linarith [ha.2]⟩
    have hm_Icc : (m : ℝ) ∈ Icc ((n : ℝ) - j - 1 / 2) ((n : ℝ) + j + 1) :=
      ⟨by linarith, by linarith⟩
    have ha14 : 1 / 4 < a := by linarith [hnj_lb, ha_Icc.1]
    have hm14 : 1 / 4 < (m : ℝ) := by linarith [hnj_lb, hm_Icc.1]
    have h_χ_diff : |chiQuantile c' m - chiQuantile c' a| ≤ 2 * ℓ := by
      have hmin14 : 1 / 4 < min a (m : ℝ) := lt_min ha14 hm14
      have hcont : ContinuousOn (chiDeriv c') (Icc (min a (m : ℝ)) (max a (m : ℝ))) := fun t ht =>
        (hasDerivAt_chiQuantile hc' (by linarith [hmin14, ht.1])).2.continuousAt.continuousWithinAt
      have hm_le := min_le_max (a := a) (b := (m : ℝ))
      have h_int : chiQuantile c' (max a (m : ℝ)) - chiQuantile c' (min a (m : ℝ)) =
          ∫ t in (min a (m : ℝ))..(max a (m : ℝ)), chiDeriv c' t := by
        refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => ?_)
          (hcont.intervalIntegrable_of_Icc hm_le)).symm
        rw [Set.uIcc_of_le hm_le] at ht
        exact (hasDerivAt_chiQuantile hc' (by linarith [hmin14, ht.1])).1
      have hint_mm : IntervalIntegrable (chiDeriv c') volume (min a (m : ℝ)) (max a (m : ℝ)) :=
        hcont.intervalIntegrable_of_Icc hm_le
      have h_up := intervalIntegral.integral_mono_on hm_le hint_mm
        (intervalIntegrable_const (μ := volume) (c := 2 * ℓ)) fun t ht => by
          have ht_Icc : t ∈ Icc ((n : ℝ) - j - 1 / 2) ((n : ℝ) + j + 1) :=
            ⟨(le_min ha_Icc.1 hm_Icc.1).trans ht.1, ht.2.trans (max_le ha_Icc.2 hm_Icc.2)⟩
          have hlin_ub := (h_deriv t ht_Icc).2
          have hd0 : 4 * ((j : ℝ) + 1) / (n : ℝ) ≤ 1 := by
            have : 4 * ((j : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast hn_4j
            rw [div_le_one hn_pos]; exact this
          have hmul := mul_le_mul_of_nonneg_right hd0 hℓ_pos.le
          linarith
      rw [intervalIntegral.integral_const, smul_eq_mul, ← h_int] at h_up
      have h_len : max a (m : ℝ) - min a (m : ℝ) ≤ 1 := by
        rcases le_total a (m : ℝ) with h | h
        · rw [max_eq_right h, min_eq_left h]; linarith [ha.1, ha.2]
        · rw [max_eq_left h, min_eq_right h]; linarith [ha.1, ha.2]
      have h_eq : |chiQuantile c' m - chiQuantile c' a| =
          chiQuantile c' (max a (m : ℝ)) - chiQuantile c' (min a (m : ℝ)) := by
        rcases le_total a (m : ℝ) with h | h
        · rw [max_eq_right h, min_eq_left h, abs_of_nonneg]
          exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn
            (Set.mem_Ici.mpr ha14.le) (Set.mem_Ici.mpr hm14.le) h)
        · rw [max_eq_left h, min_eq_right h, abs_sub_comm, abs_of_nonneg]
          exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn
            (Set.mem_Ici.mpr hm14.le) (Set.mem_Ici.mpr ha14.le) h)
      have hmul := mul_le_mul_of_nonneg_right h_len (by positivity : (0 : ℝ) ≤ 2 * ℓ)
      linarith
    let y1 := π * (x + chiQuantile c' m) / 2
    let y2 := π * (x + chiQuantile c' a) / 2
    have h_lb1 : π * xiStar ≤ y1 := by
      have hm_xi : xiStar ≤ chiQuantile c' m := (chiQuantile_spec hc' hm14.le).1
      dsimp [y1]
      have h1 : xiStar ≤ (x + chiQuantile c' m) / 2 := by linarith [hx_xi]
      exact (mul_le_mul_of_nonneg_left h1 Real.pi_pos.le).trans_eq (by ring)
    have h_lb2 : π * xiStar ≤ y2 := by
      have ha_xi : xiStar ≤ chiQuantile c' a := (chiQuantile_spec hc' ha14.le).1
      dsimp [y2]
      have h1 : xiStar ≤ (x + chiQuantile c' a) / 2 := by linarith [hx_xi]
      exact (mul_le_mul_of_nonneg_left h1 Real.pi_pos.le).trans_eq (by ring)
    have hm_le := min_le_max (a := y1) (b := y2)
    have hd_th : ∀ y ∈ Icc (min y1 y2) (max y1 y2),
        HasDerivAt (fun t => Real.log (Real.tanh t)) (1 / (Real.sinh y * Real.cosh y)) y := fun y hy => by
      have hy_ge : π * xiStar ≤ y := (le_min h_lb1 h_lb2).trans hy.1
      have hsh_ge1 : 1 ≤ Real.sinh y := by rw [← sinh_pi_mul_xiStar]; exact Real.sinh_le_sinh.mpr hy_ge
      have hch_ge1 : 1 ≤ Real.cosh y := Real.one_le_cosh y
      have hth_pos : 0 < Real.tanh y := by
        rw [Real.tanh_eq_sinh_div_cosh]; exact div_pos (by linarith) (by linarith)
      have h_tanh_d : HasDerivAt Real.tanh (1 / Real.cosh y ^ 2) y := by
        rw [show Real.tanh = fun t => Real.sinh t / Real.cosh t from funext Real.tanh_eq_sinh_div_cosh]
        refine ((Real.hasDerivAt_sinh y).div (Real.hasDerivAt_cosh y) (Real.cosh_pos y).ne').congr_deriv ?_
        field_simp [(Real.cosh_pos y).ne']
        linarith [Real.cosh_sq_sub_sinh_sq y]
      have hdt := h_tanh_d.log hth_pos.ne'
      refine hdt.congr_deriv ?_
      rw [Real.tanh_eq_sinh_div_cosh]
      field_simp [Real.cosh_pos y |>.ne', (by linarith : Real.sinh y ≠ 0)]
    have h_mvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (𝕜 := ℝ) (f := fun t => Real.log (Real.tanh t))
      (f' := fun y => 1 / (Real.sinh y * Real.cosh y))
      (s := Icc (min y1 y2) (max y1 y2)) (C := 1)
      (fun y hy => (hd_th y hy).hasDerivWithinAt)
      (fun y hy => by
        have hy_ge : π * xiStar ≤ y := (le_min h_lb1 h_lb2).trans hy.1
        have hsh_ge1 : 1 ≤ Real.sinh y := by rw [← sinh_pi_mul_xiStar]; exact Real.sinh_le_sinh.mpr hy_ge
        have hch_ge1 : 1 ≤ Real.cosh y := Real.one_le_cosh y
        rw [Real.norm_eq_abs, abs_of_pos (by positivity), one_div_le (by positivity) one_pos]
        have hmul : 1 * 1 ≤ Real.sinh y * Real.cosh y :=
          mul_le_mul hsh_ge1 hch_ge1 zero_le_one (by linarith)
        linarith)
      (convex_Icc _ _) (⟨min_le_left _ _, le_max_left _ _⟩) (⟨min_le_right _ _, le_max_right _ _⟩)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul] at h_mvt
    have hy_diff : |y1 - y2| ≤ π * ℓ := by
      have heq : y1 - y2 = (π / 2) * (chiQuantile c' m - chiQuantile c' a) := by dsimp [y1, y2]; ring
      have hpi2 : 0 < π / 2 := div_pos Real.pi_pos two_pos
      rw [heq, abs_mul, abs_of_pos hpi2]
      exact (mul_le_mul_of_nonneg_left h_χ_diff hpi2.le).trans_eq (by ring)
    have h_final := h_mvt.trans (abs_sub_comm y1 y2 ▸ hy_diff)
    rw [Real.norm_eq_abs]
    have hpiℓ_nn : 0 ≤ π * ℓ := mul_nonneg Real.pi_pos.le hℓ_pos.le
    have h6 : π * ℓ ≤ (6 * ((j : ℝ) + 1)) * (π * ℓ) := by
      have h61 : (1 : ℝ) ≤ 6 * ((j : ℝ) + 1) := by linarith [hj1_r]
      simpa using mul_le_mul_of_nonneg_right h61 hpiℓ_nn
    calc |Real.log (Real.tanh y1) - Real.log (Real.tanh y2)|
        = |Real.log (Real.tanh y2) - Real.log (Real.tanh y1)| := abs_sub_comm _ _
      _ ≤ π * ℓ := h_final
      _ ≤ (6 * ((j : ℝ) + 1)) * (π * ℓ) := h6
      _ = 6 * π * ((j : ℝ) + 1) * ℓ := by ring
  rw [Real.norm_eq_abs] at h_norm
  have h_len1 : |((m : ℝ) + 1 / 2) - ((m : ℝ) - 1 / 2)| = 1 := by norm_num
  rwa [h_len1, mul_one] at h_norm

/-! ### Section 3: Hole limit, reference floor, and $j=1$ band overshoot (`cmb:K5`) -/

private lemma hole_limit_K5_combine {j_r n_r η₀ ℓ : ℝ}
    (hj_nn : 0 ≤ j_r) (hn_pos : 0 < n_r) (hℓ_pos : 0 < ℓ) (hℓ_le1 : ℓ ≤ 1) (hη₀_pos : 0 < η₀) :
    let C_1 : ℝ := 2 * j_r * (64 * (j_r + 1) ^ 3 / η₀ ^ 2 + 32 * (j_r + 1))
    let C_2 : ℝ := 2 * j_r * (40 * π ^ 2 * (j_r + 2) ^ 2 + 12 * π * (j_r + 1)) +
      2 * (4 * j_r * (4 * j_r + 2) * 4 * (j_r + 1) +
        8 * j_r * (j_r + 1) + 2 * j_r * π ^ 2 * (j_r + 2) ^ 2)
    let C : ℝ := C_1 + C_2 + 1
    2 * j_r * ((64 * (j_r + 1) ^ 3 / η₀ ^ 2) / n_r + 40 * π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2) +
      2 * j_r * (12 * π * (j_r + 1) * ℓ) +
      2 * (2 * j_r * (8 * (j_r + 1) / n_r + π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2 / 2)) +
      2 * (4 * (j_r + 1) / n_r * (2 * (2 * j_r))) ≤ C * (1 / n_r + ℓ) := by
  intro C_1 C_2 C
  have hpi := Real.pi_pos
  have hℓ_sq : ℓ ^ 2 ≤ ℓ := by
    simpa [pow_two] using mul_le_mul_of_nonneg_left hℓ_le1 hℓ_pos.le
  have hA1 : 0 ≤ 2 * j_r * (40 * π ^ 2 * (j_r + 2) ^ 2) := by positivity
  have hA2 : 0 ≤ 2 * j_r * π ^ 2 * (j_r + 2) ^ 2 := by positivity
  have h_ell_part :
      2 * j_r * (40 * π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2) +
        2 * j_r * (12 * π * (j_r + 1) * ℓ) +
        2 * (2 * j_r * (π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2 / 2)) ≤ C_2 * ℓ := by
    have h1 : 2 * j_r * (40 * π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2) ≤
        (2 * j_r * (40 * π ^ 2 * (j_r + 2) ^ 2)) * ℓ :=
      (le_of_eq (by ring)).trans (mul_le_mul_of_nonneg_left hℓ_sq hA1)
    have h2 : 2 * (2 * j_r * (π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2 / 2)) ≤
        (2 * j_r * π ^ 2 * (j_r + 2) ^ 2) * ℓ :=
      (le_of_eq (by ring)).trans (mul_le_mul_of_nonneg_left hℓ_sq hA2)
    have h12 : 2 * j_r * (40 * π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2) +
          2 * j_r * (12 * π * (j_r + 1) * ℓ) +
          2 * (2 * j_r * (π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2 / 2)) ≤
        (2 * j_r * (40 * π ^ 2 * (j_r + 2) ^ 2)) * ℓ +
          2 * j_r * (12 * π * (j_r + 1) * ℓ) +
          (2 * j_r * π ^ 2 * (j_r + 2) ^ 2) * ℓ :=
      add_le_add (add_le_add h1 le_rfl) h2
    have hdiff : 0 ≤ C_2 * ℓ -
        ((2 * j_r * (40 * π ^ 2 * (j_r + 2) ^ 2)) * ℓ +
          2 * j_r * (12 * π * (j_r + 1) * ℓ) +
          (2 * j_r * π ^ 2 * (j_r + 2) ^ 2) * ℓ) := by
      have hid : C_2 * ℓ -
          ((2 * j_r * (40 * π ^ 2 * (j_r + 2) ^ 2)) * ℓ +
            2 * j_r * (12 * π * (j_r + 1) * ℓ) +
            (2 * j_r * π ^ 2 * (j_r + 2) ^ 2) * ℓ) =
          (2 * (4 * j_r * (4 * j_r + 2) * 4 * (j_r + 1) + 8 * j_r * (j_r + 1)) +
            2 * j_r * π ^ 2 * (j_r + 2) ^ 2) * ℓ := by
        dsimp [C_2]; ring
      rw [hid]; positivity
    linarith
  have h_n_part :
      2 * j_r * ((64 * (j_r + 1) ^ 3 / η₀ ^ 2) / n_r) +
        2 * (2 * j_r * (8 * (j_r + 1) / n_r)) +
        2 * (4 * (j_r + 1) / n_r * (2 * (2 * j_r))) ≤ (C_1 + C_2) * (1 / n_r) := by
    have hC2_nn : 0 ≤ C_2 := by dsimp [C_2]; positivity
    have h_eq : 2 * j_r * ((64 * (j_r + 1) ^ 3 / η₀ ^ 2) / n_r) +
          2 * (2 * j_r * (8 * (j_r + 1) / n_r)) +
          2 * (4 * (j_r + 1) / n_r * (2 * (2 * j_r))) =
          C_1 * (1 / n_r) := by
      dsimp [C_1]; ring
    rw [h_eq]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC2_nn) (by positivity)
  have hC1_nn : 0 ≤ C_1 := by dsimp [C_1]; positivity
  calc 2 * j_r * ((64 * (j_r + 1) ^ 3 / η₀ ^ 2) / n_r + 40 * π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2) +
        2 * j_r * (12 * π * (j_r + 1) * ℓ) +
        2 * (2 * j_r * (8 * (j_r + 1) / n_r + π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2 / 2)) +
        2 * (4 * (j_r + 1) / n_r * (2 * (2 * j_r)))
      = (2 * j_r * ((64 * (j_r + 1) ^ 3 / η₀ ^ 2) / n_r) +
          2 * (2 * j_r * (8 * (j_r + 1) / n_r)) +
          2 * (4 * (j_r + 1) / n_r * (2 * (2 * j_r)))) +
        (2 * j_r * (40 * π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2) +
          2 * j_r * (12 * π * (j_r + 1) * ℓ) +
          2 * (2 * j_r * (π ^ 2 * (j_r + 2) ^ 2 * ℓ ^ 2 / 2))) := by ring
    _ ≤ (C_1 + C_2) * (1 / n_r) + C_2 * ℓ := add_le_add h_n_part h_ell_part
    _ ≤ (C_1 + C_2) * (1 / n_r) + (C_1 + C_2) * ℓ :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC1_nn) hℓ_pos.le)
    _ = (C_1 + C_2) * (1 / n_r + ℓ) := by ring
    _ ≤ C * (1 / n_r + ℓ) :=
        mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (add_pos (one_div_pos.mpr hn_pos) hℓ_pos).le

/-- Uniform hole limit (`cmb:K5`, `comb_estimates.tex`, line 213):
for fixed $j \ge 1$ and $\eta_0 \in (0, \tfrac14]$,
$|\mathcal{H}_{n,j}(x; \eta_0) - H_j(u, \eta_0)| \le C (n^{-1} + \ell_n)$
uniformly in $n \ge N_j$ and $x = \chi_n + u\ell_n \in [\chi_n, \chi_{n+1})$ for large $c'$. -/
theorem hole_limit_K5 {j : ℕ} {η₀ : ℝ} (hj : 1 ≤ j) (hη₀0 : 0 < η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∃ (N_j : ℕ) (C : ℝ), 1 ≤ N_j ∧ 0 < C ∧
      ∀ᶠ c' in atTop, ∀ (n : ℕ) (x : ℝ), N_j ≤ n → inCell c' n x →
        |holeH c' η₀ n j x - holeModel j ((x - chiQuantile c' n) / siteGap c' n) η₀| ≤
          C * (1 / (n : ℝ) + siteGap c' n) := by
  let K_M : ℝ := 16 * ((j : ℝ) + 1) ^ 2
  let N_j : ℕ := Nat.ceil (64 * ((j : ℝ) + 1) ^ 3 / η₀ ^ 2) + 16 * (j + 1) ^ 2 + 64
  have hNj1 : 1 ≤ N_j := by omega
  let C_1 : ℝ := 2 * (j : ℝ) * (64 * ((j : ℝ) + 1) ^ 3 / η₀ ^ 2 + 32 * ((j : ℝ) + 1))
  let C_2 : ℝ := 2 * (j : ℝ) * (40 * π ^ 2 * ((j : ℝ) + 2) ^ 2 + 12 * π * ((j : ℝ) + 1)) +
    2 * (4 * (j : ℝ) * (4 * (j : ℝ) + 2) * 4 * ((j : ℝ) + 1) +
      8 * (j : ℝ) * ((j : ℝ) + 1) + 2 * (j : ℝ) * π ^ 2 * ((j : ℝ) + 2) ^ 2)
  let C : ℝ := C_1 + C_2 + 1
  have hj_pos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hC1_nn : 0 ≤ C_1 := by dsimp [C_1]; positivity
  have hC2_nn : 0 ≤ C_2 := by dsimp [C_2]; positivity
  have hC_pos : 0 < C := by dsimp [C]; linarith
  refine ⟨N_j, C, hNj1, hC_pos, ?_⟩
  obtain ⟨C_gap, hC_gap, hgap_ev⟩ := siteGap_eventually_le
  have h_lam_ev : ∀ᶠ c' in atTop, C_gap * lambdaComb c' ≤ 1 / (32 * ((j : ℝ) + 2)) := by
    have htend : Tendsto lambdaComb atTop (𝓝 0) := by
      unfold lambdaComb
      have h_mul : Tendsto (fun c' : ℝ => kTip * c') atTop atTop :=
        tendsto_atTop_atTop.mpr fun M => ⟨M / kTip, fun x hx => by
          rw [div_le_iff₀ kTip_pos] at hx; linarith⟩
      exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp h_mul
    have hmul := htend.const_mul C_gap
    rw [mul_zero] at hmul
    exact hmul.eventually (eventually_le_nhds (by positivity))
  filter_upwards [hgap_ev, h_lam_ev, eventually_gt_atTop (0 : ℝ)] with c' hgap_c hlam_c hc'
  have hgap1 : siteGap c' 1 ≤ 1 / 2 := hgap_c.2.2.2
  have hgap_small : siteGap c' 1 ≤ 1 / (32 * ((j : ℝ) + 2)) := hgap_c.2.1.trans (hgap_c.2.2.1.trans hlam_c)
  intro n x hn hx
  have hn_Nj : N_j ≤ n := hn
  have hsq : j + 1 ≤ (j + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hn_4j : 4 * (j + 1) ≤ n := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h16_r : 16 * ((j : ℝ) + 1) ^ 2 ≤ (n : ℝ) := by
    have : 16 * (j + 1) ^ 2 ≤ n := by omega
    exact_mod_cast this
  have hfrac_r : 4 * ((j : ℝ) + 1) ^ 2 / (n : ℝ) ≤ 1 := by rw [div_le_one hn_pos]; linarith
  have h_lin := quantile_linearization_K5 hc' hj hn_4j
  set ℓ : ℝ := siteGap c' n
  have hℓ_pos : 0 < ℓ := h_lin.1
  have hℓ_le1 : ℓ ≤ siteGap c' 1 := by
    have hn1 : 1 ≤ n := by omega
    rcases eq_or_lt_of_le hn1 with h1 | hgt
    · dsimp [ℓ]; rw [← h1]
    · have hanti := (siteGap_strictAnti hc').antitone (show 0 ≤ n - 1 by omega)
      have heq : (n - 1) + 1 = n := by omega
      dsimp [ℓ]; rwa [heq] at hanti
  have hℓ_small : ℓ ≤ 1 / (32 * ((j : ℝ) + 2)) := hℓ_le1.trans hgap_small
  set u : ℝ := (x - chiQuantile c' n) / ℓ
  have hu_mem : u ∈ Ico (0 : ℝ) 1 := by
    dsimp [u]
    refine ⟨div_nonneg (sub_nonneg.mpr hx.1) hℓ_pos.le, ?_⟩
    rw [div_lt_one hℓ_pos]
    unfold ℓ siteGap
    have h_cast : chiQuantile c' ((n + 1 : ℕ) : ℝ) = chiQuantile c' ((n : ℝ) + 1) := by push_cast; rfl
    rw [← h_cast]; linarith [hx.2]
  have hx_eq_u : x - chiQuantile c' n = u * ℓ := by dsimp [u]; field_simp [hℓ_pos.ne']
  have hn1_r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hj1_r : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hnj_lb : (1 / 4 : ℝ) < (n : ℝ) - (j : ℝ) - 1 / 2 := by
    have h4j : 4 * ((j : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast hn_4j
    linarith [hj1_r]
  have hx_xi : xiStar ≤ x := (chiQuantile_spec hc' (by linarith [hn1_r])).1.trans hx.1
  have hx0 : 0 ≤ x := xiStar_pos.le.trans hx_xi
  -- Step 1: Rewrite `holeModel j u η₀` over `Icc (n - j + 1) (n + j)`
  have h_model_sum :
      ∑ k ∈ Finset.range j,
          Real.log (((u - (k : ℝ) - 1) ^ 2 + η₀ ^ 2) * ((u + (k : ℝ)) ^ 2 + η₀ ^ 2)) =
        ∑ m ∈ Finset.Icc (n - j + 1) (n + j), Real.log ((u - ((m : ℝ) - (n : ℝ))) ^ 2 + η₀ ^ 2) := by
    have hsplit : Finset.Icc (n - j + 1) (n + j) =
        Finset.Icc (n - j + 1) n ∪ Finset.Icc (n + 1) (n + j) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj : Disjoint (Finset.Icc (n - j + 1) n) (Finset.Icc (n + 1) (n + j)) := by
      rw [Finset.disjoint_left]; intro m h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
    have h_bij1 : Finset.Icc (n - j + 1) n = (Finset.range j).image (fun k => n - k) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · intro ⟨h1, h2⟩; exact ⟨n - m, by omega, by omega⟩
      · rintro ⟨k, hk, rfl⟩; omega
    have h_bij2 : Finset.Icc (n + 1) (n + j) = (Finset.range j).image (fun k => n + 1 + k) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · intro ⟨h1, h2⟩; exact ⟨m - (n + 1), by omega, by omega⟩
      · rintro ⟨k, hk, rfl⟩; omega
    rw [hsplit, Finset.sum_union hdisj, h_bij1, h_bij2,
      Finset.sum_image (fun a ha b hb heq => by simp only [Finset.mem_coe, Finset.mem_range] at ha hb; omega),
      Finset.sum_image (fun a _ b _ heq => by omega), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk_lt : k < j := Finset.mem_range.mp hk
    have hkn : k ≤ n := by omega
    have hcast1 : ((n - k : ℕ) : ℝ) - (n : ℝ) = -(k : ℝ) := by
      rw [Nat.cast_sub hkn]; ring
    have hcast2 : ((n + 1 + k : ℕ) : ℝ) - (n : ℝ) = (k : ℝ) + 1 := by
      push_cast; ring
    rw [hcast1, hcast2]
    have h1 : 0 < (u - (k : ℝ) - 1) ^ 2 + η₀ ^ 2 := by positivity
    have h2 : 0 < (u + (k : ℝ)) ^ 2 + η₀ ^ 2 := by positivity
    rw [Real.log_mul h1.ne' h2.ne']
    ring_nf
  have h_model_int :
      ∫ s in (-(j : ℝ) + 1 / 2)..((j : ℝ) + 1 / 2), Real.log |u - s| =
        ∫ a in ((n : ℝ) - (j : ℝ) + 1 / 2)..((n : ℝ) + (j : ℝ) + 1 / 2),
          Real.log |((n : ℝ) + u) - a| := by
    have hcomp := intervalIntegral.integral_comp_sub_right
      (fun s : ℝ => Real.log |u - s|) (n : ℝ)
      (a := (n : ℝ) - (j : ℝ) + 1 / 2) (b := (n : ℝ) + (j : ℝ) + 1 / 2)
    have hrew : (fun a : ℝ => Real.log |u - (a - (n : ℝ))|) =
        fun a : ℝ => Real.log |((n : ℝ) + u) - a| := by
      ext a; congr 1; congr 1; ring
    rw [hrew] at hcomp
    rw [show (-(j : ℝ) + 1 / 2) = ((n : ℝ) - (j : ℝ) + 1 / 2) - (n : ℝ) by ring,
      show ((j : ℝ) + 1 / 2) = ((n : ℝ) + (j : ℝ) + 1 / 2) - (n : ℝ) by ring]
    exact hcomp.symm
  -- Cancellation constant `2 * (2 * j) * log (π * ℓ / 2)`
  have hc_pos : 0 < π * ℓ / 2 := div_pos (mul_pos Real.pi_pos hℓ_pos) two_pos
  have h_sum_shift :
      ∑ m ∈ Finset.Icc (n - j + 1) (n + j), Real.log ((u - ((m : ℝ) - (n : ℝ))) ^ 2 + η₀ ^ 2) +
          2 * ((2 * (j : ℝ)) * Real.log (π * ℓ / 2)) =
        ∑ m ∈ Finset.Icc (n - j + 1) (n + j),
          Real.log (((u - ((m : ℝ) - (n : ℝ))) ^ 2 + η₀ ^ 2) * (π * ℓ / 2) ^ 2) := by
    have hcard : (Finset.Icc (n - j + 1) (n + j)).card = 2 * j := by
      rw [Nat.card_Icc]; omega
    have hconst : 2 * ((2 * (j : ℝ)) * Real.log (π * ℓ / 2)) =
        ∑ _m ∈ Finset.Icc (n - j + 1) (n + j), (2 : ℝ) * Real.log (π * ℓ / 2) := by
      rw [Finset.sum_const, hcard, nsmul_eq_mul]; push_cast; ring
    rw [hconst, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hp1 : 0 < (u - ((m : ℝ) - (n : ℝ))) ^ 2 + η₀ ^ 2 := by positivity
    rw [Real.log_mul hp1.ne' (sq_pos_of_pos hc_pos).ne', Real.log_pow]; norm_num
  -- Split `holeH - holeModel` into site sum error and integral error
  -- First, bound each site term for `m ∈ Icc (n - j + 1) (n + j)`
  have h_site_err :
      ∀ m ∈ Finset.Icc (n - j + 1) (n + j),
        |Real.log (pairModQ c' η₀ x m) -
          (Real.log (((u - ((m : ℝ) - (n : ℝ))) ^ 2 + η₀ ^ 2) * (π * ℓ / 2) ^ 2) +
            2 * Real.log (Real.tanh (π * (x + chiQuantile c' m) / 2)))| ≤
          (64 * ((j : ℝ) + 1) ^ 3 / η₀ ^ 2) / (n : ℝ) + 40 * π ^ 2 * ((j : ℝ) + 2) ^ 2 * ℓ ^ 2 :=
    hole_site_err_K5 hc' hj hη₀0 hη₀1 hx_xi hu_mem hx_eq_u hℓ_small hn_4j (by omega) (by omega)
      h_lin.2.2.1 h_lin.2.2.2


  -- Step 2: Existence of `a_* ∈ [n, n + 1)` with `chiQuantile c' a_* = x`
  have ha_star_ex : ∃ aStar ∈ Ico (n : ℝ) ((n : ℝ) + 1), chiQuantile c' aStar = x := by
    have hcont : ContinuousOn (chiQuantile c') (Icc (n : ℝ) ((n : ℝ) + 1)) := fun t ht =>
      (hasDerivAt_chiQuantile hc' (by linarith [ht.1])).1.continuousAt.continuousWithinAt
    have h_cast : chiQuantile c' ((n + 1 : ℕ) : ℝ) = chiQuantile c' ((n : ℝ) + 1) := by push_cast; rfl
    have h_mem : x ∈ Icc (chiQuantile c' n) (chiQuantile c' ((n : ℝ) + 1)) :=
      ⟨hx.1, h_cast ▸ hx.2.le⟩
    obtain ⟨aStar, ha_Icc, ha_eq⟩ := intermediate_value_Icc (by linarith : (n : ℝ) ≤ (n : ℝ) + 1) hcont h_mem
    have ha_lt : aStar < (n : ℝ) + 1 := by
      rcases eq_or_lt_of_le ha_Icc.2 with rfl | hlt
      · exfalso; have hx2 := hx.2; rw [h_cast] at hx2; linarith [hx2, ha_eq]
      · exact hlt
    exact ⟨aStar, ⟨ha_Icc.1, ha_lt⟩, ha_eq⟩
  rcases ha_star_ex with ⟨aStar, haStar_Ico, haStar_eq⟩
  have haStar_diff : |aStar - ((n : ℝ) + u)| ≤ 4 * ((j : ℝ) + 1) / (n : ℝ) := by
    have hcont : ContinuousOn (chiDeriv c') (Icc (n : ℝ) aStar) := fun t ht =>
      (hasDerivAt_chiQuantile hc' (by linarith [haStar_Ico.1, ht.1])).2.continuousAt.continuousWithinAt
    have hint_eq : -(u * ℓ - (aStar - (n : ℝ)) * ℓ) = ∫ t in (n : ℝ)..aStar, (ℓ - chiDeriv c' t) := by
      have h_int : chiQuantile c' aStar - chiQuantile c' n = ∫ t in (n : ℝ)..aStar, chiDeriv c' t := by
        refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => ?_)
          (hcont.intervalIntegrable_of_Icc haStar_Ico.1)).symm
        rw [Set.uIcc_of_le haStar_Ico.1] at ht
        exact (hasDerivAt_chiQuantile hc' (by linarith [hn1_r, ht.1])).1
      rw [← hx_eq_u, ← haStar_eq, intervalIntegral.integral_sub
        (intervalIntegrable_const (μ := volume)) (hcont.intervalIntegrable_of_Icc haStar_Ico.1),
        intervalIntegral.integral_const, smul_eq_mul, ← h_int]
      ring
    have h_norm := intervalIntegral.norm_integral_le_of_norm_le_const (C := 4 * ((j : ℝ) + 1) / (n : ℝ) * ℓ)
      (a := (n : ℝ)) (b := aStar) (f := fun t => ℓ - chiDeriv c' t) fun t ht => by
      rw [Set.uIoc_of_le haStar_Ico.1] at ht
      have ht_Icc : t ∈ Icc ((n : ℝ) - j - 1 / 2) ((n : ℝ) + j + 1) :=
        ⟨by linarith [ht.1], by linarith [ht.2, haStar_Ico.2]⟩
      have := h_lin.2.1 t ht_Icc
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
    rw [Real.norm_eq_abs, ← hint_eq, abs_neg] at h_norm
    have h_dist : |aStar - (n : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith [haStar_Ico.1], by linarith [haStar_Ico.2]⟩
    have h_mul_le : |aStar - ((n : ℝ) + u)| * ℓ ≤ (4 * ((j : ℝ) + 1) / (n : ℝ)) * ℓ := by
      calc |aStar - ((n : ℝ) + u)| * ℓ = |u * ℓ - (aStar - (n : ℝ)) * ℓ| := by
            rw [show u * ℓ - (aStar - (n : ℝ)) * ℓ = -(aStar - ((n : ℝ) + u)) * ℓ by ring,
              abs_mul, abs_neg, abs_of_pos hℓ_pos]
        _ ≤ (4 * ((j : ℝ) + 1) / (n : ℝ) * ℓ) * |aStar - (n : ℝ)| := h_norm
        _ ≤ (4 * ((j : ℝ) + 1) / (n : ℝ) * ℓ) * 1 := mul_le_mul_of_nonneg_left h_dist (by positivity)
        _ = (4 * ((j : ℝ) + 1) / (n : ℝ)) * ℓ := by ring
    exact le_of_mul_le_mul_right h_mul_le hℓ_pos
  -- Step 3: Integral bounds on `A..B` where `A = n - j + 1/2`, `B = n + j + 1/2`
  let A : ℝ := (n : ℝ) - (j : ℝ) + 1 / 2
  let B : ℝ := (n : ℝ) + (j : ℝ) + 1 / 2
  have hAB : A ≤ B := by dsimp [A, B]; linarith
  have hA_Icc : A ∈ Icc ((n : ℝ) - j - 1 / 2) ((n : ℝ) + j + 1) := by
    dsimp [A]; constructor <;> linarith
  have hB_Icc : B ∈ Icc ((n : ℝ) - j - 1 / 2) ((n : ℝ) + j + 1) := by
    dsimp [B]; constructor <;> linarith
  have hA1 : 1 ≤ A := by
    have h4j : 4 * ((j : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast hn_4j
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    dsimp [A]; linarith
  have hA14 : 1 / 4 < A := by linarith
  have hint_phi : IntervalIntegrable (phiVar c' x) volume A B := by
    obtain ⟨_, hint_14, _, _, _⟩ := riesz_real_identities hc' hx0 1 le_rfl
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hAB).mpr
      (hint_14.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by linarith))))
  have h_cont_th : Continuous Real.tanh := by
    rw [show Real.tanh = fun y => Real.sinh y / Real.cosh y from funext Real.tanh_eq_sinh_div_cosh]
    exact Real.continuous_sinh.div Real.continuous_cosh (fun y => (Real.cosh_pos y).ne')
  have hint_plus : IntervalIntegrable (fun a => Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2))) volume A B := by
    have hcont : ContinuousOn (fun a => Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2))) (Icc A B) := by
      refine ContinuousOn.log ?_ fun a ha => ?_
      · refine h_cont_th.comp_continuousOn ?_
        refine (continuousOn_const.mul (continuousOn_const.add ?_)).div_const 2
        intro t ht
        exact (hasDerivAt_chiQuantile hc' (by linarith [hA14, ht.1])).1.continuousAt.continuousWithinAt
      · have ha14 : 1 / 4 < a := by linarith [hA14, ha.1]
        have hχ_pos : 0 < chiQuantile c' a := xiStar_pos.trans (xiStar_lt_chiQuantile hc' ha14)
        rw [Real.tanh_eq_sinh_div_cosh]
        have hx_nn : 0 ≤ x := xiStar_pos.le.trans ((chiQuantile_spec hc' (by linarith [hn1_r])).1.trans hx.1)
        have h_arg : 0 < π * (x + chiQuantile c' a) / 2 :=
          div_pos (mul_pos Real.pi_pos (by linarith)) two_pos
        exact (div_pos (Real.sinh_pos_iff.mpr h_arg) (Real.cosh_pos _)).ne'
    exact hcont.intervalIntegrable_of_Icc hAB
  have hint_aStar : IntervalIntegrable (fun a => Real.log |aStar - a|) volume A B := by
    have h_abs_eq : (fun a => Real.log |aStar - a|) = (fun a => Real.log |a - aStar|) := by
      ext a; rw [abs_sub_comm]
    rw [h_abs_eq]
    have hAc : A ≤ aStar := by dsimp [A]; linarith [haStar_Ico.1, hj1_r]
    have hcB : aStar ≤ B := by dsimp [B]; linarith [haStar_Ico.2, hj1_r]
    have hi1 : IntervalIntegrable (fun a => Real.log |a - aStar|) volume A aStar := by
      have hcomp : IntervalIntegrable (fun a => Real.log (aStar - a)) volume A aStar := by
        simpa using (intervalIntegral.intervalIntegrable_log' (a := aStar - A) (b := 0)).comp_sub_left aStar
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hAc] at hcomp ⊢
      exact hcomp.congr_fun (fun a ha => by rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ha.2)]) measurableSet_Ioc
    have hi2 : IntervalIntegrable (fun a => Real.log |a - aStar|) volume aStar B := by
      have hcomp : IntervalIntegrable (fun a => Real.log (a - aStar)) volume aStar B := by
        simpa using (intervalIntegral.intervalIntegrable_log' (a := 0) (b := B - aStar)).comp_sub_right aStar
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hcB] at hcomp ⊢
      exact hcomp.congr_fun (fun a ha => by rw [abs_of_nonneg (sub_nonneg.mpr ha.1.le)]) measurableSet_Ioc
    exact hi1.trans hi2
  -- Compare `2 * ∫ A..B, (phiVar - log tanh^+ - log |aStar - a| - log (π * ℓ / 2))`
  let E_int : ℝ → ℝ := fun a =>
    phiVar c' x a - Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2)) -
      Real.log |aStar - a| - Real.log (π * ℓ / 2)
  have hE_int_bd : |∫ a in A..B, E_int a| ≤
      2 * (j : ℝ) * (8 * ((j : ℝ) + 1) / (n : ℝ) + π ^ 2 * ((j : ℝ) + 2) ^ 2 * ℓ ^ 2 / 2) :=
    hole_integral_err_K5 hc' hj1_r hn1_r hn_pos h16_r hfrac_r hnj_lb hℓ_pos hx0 hu_mem
      hx_eq_u haStar_Ico haStar_eq h_lin.2.1 h_lin.2.2.1
  -- Step 4: Plus-tanh variation over each cell `[m - 1/2, m + 1/2]`
  have h_plus_cell : ∀ m ∈ Finset.Icc (n - j + 1) (n + j),
      |Real.log (Real.tanh (π * (x + chiQuantile c' m) / 2)) -
        ∫ a in ((m : ℝ) - 1 / 2)..((m : ℝ) + 1 / 2),
          Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2))| ≤
        6 * π * ((j : ℝ) + 1) * ℓ := fun m hm =>
    hole_plus_cell_err_K5 hc' hj1_r hn_pos hn_4j hnj_lb hℓ_pos hx_xi hm h_lin.2.1
  -- Step 5: Assemble the full bound on `|holeH - holeModel|`
  have h_unit_sum_plus :
      ∑ m ∈ Finset.Icc (n - j + 1) (n + j),
          ∫ a in ((m : ℝ) - 1 / 2)..((m : ℝ) + 1 / 2),
            Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2)) =
        ∫ a in A..B, Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2)) := by
    have h_unit : ∀ K : ℕ, n - j + 1 ≤ K →
        ∑ m ∈ Finset.Icc (n - j + 1) K,
            ∫ a in ((m : ℝ) - 1 / 2)..((m : ℝ) + 1 / 2),
              Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2)) =
          ∫ a in A..((K : ℝ) + 1 / 2),
            Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2)) := by
      intro K hK
      have hcont : ContinuousOn (fun a => Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2)))
          (Icc A ((K : ℝ) + 1 / 2)) := by
        refine ContinuousOn.log ?_ fun a ha => ?_
        · refine h_cont_th.comp_continuousOn ?_
          refine (continuousOn_const.mul (continuousOn_const.add ?_)).div_const 2
          intro t ht; exact (hasDerivAt_chiQuantile hc' (by dsimp [A] at ht; linarith [ht.1])).1.continuousAt.continuousWithinAt
        · have ha14 : 1 / 4 < a := by dsimp [A] at ha; linarith [ha.1]
          have hχ_pos : 0 < chiQuantile c' a := xiStar_pos.trans (xiStar_lt_chiQuantile hc' ha14)
          rw [Real.tanh_eq_sinh_div_cosh]
          have hx_nn : 0 ≤ x := xiStar_pos.le.trans ((chiQuantile_spec hc' (by linarith [hn1_r])).1.trans hx.1)
          have h_arg : 0 < π * (x + chiQuantile c' a) / 2 :=
            div_pos (mul_pos Real.pi_pos (by linarith)) two_pos
          exact (div_pos (Real.sinh_pos_iff.mpr h_arg) (Real.cosh_pos _)).ne'
      induction K, hK using Nat.le_induction with
      | base =>
        simp only [Finset.Icc_self, Finset.sum_singleton]
        have heq1 : ((n - j + 1 : ℕ) : ℝ) - 1 / 2 = A := by
          have hsub : ((n - j : ℕ) : ℝ) = (n : ℝ) - (j : ℝ) := Nat.cast_sub (by omega)
          dsimp [A]; push_cast; rw [hsub]; ring
        have heq2 : ((n - j + 1 : ℕ) : ℝ) + 1 / 2 = ((n - j + 1 : ℕ) : ℝ) + 1 / 2 := rfl
        rw [heq1]
      | succ K hK ih =>
        have hsub : Finset.Icc (n - j + 1) (K + 1) = insert (K + 1) (Finset.Icc (n - j + 1) K) := by
          ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hsub, Finset.sum_insert (by simp)]
        have h_sub_Icc : Icc A ((K : ℝ) + 1 / 2) ⊆ Icc A (((K + 1 : ℕ) : ℝ) + 1 / 2) :=
          Icc_subset_Icc_right (by push_cast; linarith)
        rw [ih (hcont.mono h_sub_Icc), add_comm]
        have hAK : A ≤ (K : ℝ) + 1 / 2 := by
          have hcast : ((n - j + 1 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
          have hsub2 : ((n - j : ℕ) : ℝ) = (n : ℝ) - (j : ℝ) := Nat.cast_sub (by omega)
          dsimp [A]; push_cast at hcast; rw [hsub2] at hcast; linarith
        have hi1 : IntervalIntegrable
            (fun a => Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2)))
            volume A ((K : ℝ) + 1 / 2) :=
          (hcont.mono h_sub_Icc).intervalIntegrable_of_Icc hAK
        have hK_le : ((K + 1 : ℕ) : ℝ) - 1 / 2 = (K : ℝ) + 1 / 2 := by push_cast; ring
        have hi2 : IntervalIntegrable (fun a => Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2)))
            volume ((K : ℝ) + 1 / 2) (((K + 1 : ℕ) : ℝ) + 1 / 2) :=
          (hcont.mono (Icc_subset_Icc_left hAK)).intervalIntegrable_of_Icc (by push_cast; linarith)
        rw [hK_le]
        exact intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have h_res := h_unit (n + j) (by omega)
    have hB_eq : ((n + j : ℕ) : ℝ) + 1 / 2 = B := by dsimp [B]; push_cast; ring
    rwa [hB_eq] at h_res
  have h_abs_log_diff :
      |(∫ a in A..B, Real.log |aStar - a|) - (∫ a in A..B, Real.log |((n : ℝ) + u) - a|)| ≤
        4 * ((j : ℝ) + 1) / (n : ℝ) * (2 * (2 * (j : ℝ))) := by
    have h_rew1 : ∫ a in A..B, Real.log |aStar - a| = ∫ a in A..B, Real.log |a - aStar| := by
      congr 1; ext a; rw [abs_sub_comm]
    have h_rew2 : ∫ a in A..B, Real.log |((n : ℝ) + u) - a| =
        ∫ a in A..B, Real.log |a - ((n : ℝ) + u)| := by
      congr 1; ext a; rw [abs_sub_comm]
    rw [h_rew1, h_rew2]
    have h_bd := abs_integral_log_abs_sub_diff (A := A) (B := B) (c₁ := aStar) (c₂ := (n : ℝ) + u)
      (by dsimp [A]; linarith [haStar_Ico.1]) (by dsimp [B]; linarith [haStar_Ico.2])
      (by dsimp [A]; linarith [hu_mem.1]) (by dsimp [B]; linarith [hu_mem.2])
      (by dsimp [A, B]; linarith [haStar_Ico.2]) (by dsimp [A, B]; linarith)
    have hBA_eq : B - A = 2 * (j : ℝ) := by dsimp [A, B]; ring
    rw [hBA_eq] at h_bd
    exact h_bd.trans (mul_le_mul_of_nonneg_right haStar_diff (by positivity))
  -- Put everything together for `|holeH - holeModel|`
  have h_diff_eq : holeH c' η₀ n j x - holeModel j u η₀ =
      (∑ m ∈ Finset.Icc (n - j + 1) (n + j),
        (Real.log (pairModQ c' η₀ x m) -
          (Real.log (((u - ((m : ℝ) - (n : ℝ))) ^ 2 + η₀ ^ 2) * (π * ℓ / 2) ^ 2) +
            2 * Real.log (Real.tanh (π * (x + chiQuantile c' m) / 2))))) +
      2 * ∑ m ∈ Finset.Icc (n - j + 1) (n + j),
        (Real.log (Real.tanh (π * (x + chiQuantile c' m) / 2)) -
          ∫ a in ((m : ℝ) - 1 / 2)..((m : ℝ) + 1 / 2),
            Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2))) -
      2 * (∫ a in A..B, E_int a) -
      2 * ((∫ a in A..B, Real.log |aStar - a|) - (∫ a in A..B, Real.log |((n : ℝ) + u) - a|)) := by
    unfold holeH holeModel
    rw [h_model_sum, h_model_int]
    have h_AB_l : ((n : ℝ) - (j : ℝ) + 1 / 2) = A := rfl
    have h_AB_r : ((n : ℝ) + (j : ℝ) + 1 / 2) = B := rfl
    rw [h_AB_l, h_AB_r]
    have h_int_E : ∫ a in A..B, E_int a =
        (∫ a in A..B, phiVar c' x a) -
          (∫ a in A..B, Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2))) -
          (∫ a in A..B, Real.log |aStar - a|) - (2 * (j : ℝ)) * Real.log (π * ℓ / 2) := by
      have hi_c : IntervalIntegrable (fun _ : ℝ => Real.log (π * ℓ / 2)) volume A B :=
        intervalIntegrable_const
      have he1 : ∫ a in A..B, E_int a =
          (∫ a in A..B, (phiVar c' x a - Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2)) -
            Real.log |aStar - a|)) - ∫ a in A..B, Real.log (π * ℓ / 2) :=
        intervalIntegral.integral_sub ((hint_phi.sub hint_plus).sub hint_aStar) hi_c
      have he2 : ∫ a in A..B, (phiVar c' x a - Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2)) -
            Real.log |aStar - a|) =
          (∫ a in A..B, (phiVar c' x a - Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2)))) -
            ∫ a in A..B, Real.log |aStar - a| :=
        intervalIntegral.integral_sub (hint_phi.sub hint_plus) hint_aStar
      have he3 : ∫ a in A..B, (phiVar c' x a - Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2))) =
          (∫ a in A..B, phiVar c' x a) -
            ∫ a in A..B, Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2)) :=
        intervalIntegral.integral_sub hint_phi hint_plus
      rw [he1, he2, he3, intervalIntegral.integral_const, smul_eq_mul]
      have hBA : B - A = 2 * (j : ℝ) := by dsimp [A, B]; ring
      rw [hBA]
    rw [h_int_E]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [h_unit_sum_plus, ← h_sum_shift]
    ring
  rw [h_diff_eq]
  have hcard : ((Finset.Icc (n - j + 1) (n + j)).card : ℝ) = 2 * (j : ℝ) := by
    rw [Nat.card_Icc]
    have hsub : n + j + 1 - (n - j + 1) = 2 * j := by omega
    rw [hsub]; push_cast; ring
  have h_sum1 : |∑ m ∈ Finset.Icc (n - j + 1) (n + j),
      (Real.log (pairModQ c' η₀ x m) -
        (Real.log (((u - ((m : ℝ) - (n : ℝ))) ^ 2 + η₀ ^ 2) * (π * ℓ / 2) ^ 2) +
          2 * Real.log (Real.tanh (π * (x + chiQuantile c' m) / 2))))| ≤
      2 * (j : ℝ) * ((64 * ((j : ℝ) + 1) ^ 3 / η₀ ^ 2) / (n : ℝ) + 40 * π ^ 2 * ((j : ℝ) + 2) ^ 2 * ℓ ^ 2) := by
    calc |∑ m ∈ Finset.Icc (n - j + 1) (n + j), _|
        ≤ ∑ m ∈ Finset.Icc (n - j + 1) (n + j), |_| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _m ∈ Finset.Icc (n - j + 1) (n + j),
            ((64 * ((j : ℝ) + 1) ^ 3 / η₀ ^ 2) / (n : ℝ) + 40 * π ^ 2 * ((j : ℝ) + 2) ^ 2 * ℓ ^ 2) :=
          Finset.sum_le_sum h_site_err
      _ = 2 * (j : ℝ) * _ := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have h_sum2 : |2 * ∑ m ∈ Finset.Icc (n - j + 1) (n + j),
      (Real.log (Real.tanh (π * (x + chiQuantile c' m) / 2)) -
        ∫ a in ((m : ℝ) - 1 / 2)..((m : ℝ) + 1 / 2),
          Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2)))| ≤
      2 * (j : ℝ) * (12 * π * ((j : ℝ) + 1) * ℓ) := by
    rw [abs_mul, abs_of_pos two_pos]
    calc 2 * |∑ m ∈ Finset.Icc (n - j + 1) (n + j), _|
        ≤ 2 * ∑ m ∈ Finset.Icc (n - j + 1) (n + j), |_| := by
          gcongr; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ 2 * ∑ _m ∈ Finset.Icc (n - j + 1) (n + j), (6 * π * ((j : ℝ) + 1) * ℓ) := by
          exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m hm => h_plus_cell m hm) two_pos.le
      _ = 2 * (j : ℝ) * (12 * π * ((j : ℝ) + 1) * ℓ) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]; ring
  have hℓ1 : ℓ ≤ 1 := hℓ_le1.trans (hgap1.trans (by norm_num))
  have h_tri1 :
      |(∑ m ∈ Finset.Icc (n - j + 1) (n + j),
            (Real.log (pairModQ c' η₀ x m) -
              (Real.log (((u - ((m : ℝ) - (n : ℝ))) ^ 2 + η₀ ^ 2) * (π * ℓ / 2) ^ 2) +
                2 * Real.log (Real.tanh (π * (x + chiQuantile c' m) / 2))))) +
          2 * ∑ m ∈ Finset.Icc (n - j + 1) (n + j),
            (Real.log (Real.tanh (π * (x + chiQuantile c' m) / 2)) -
              ∫ a in ((m : ℝ) - 1 / 2)..((m : ℝ) + 1 / 2),
                Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2))) -
          2 * (∫ a in A..B, E_int a) -
          2 * ((∫ a in A..B, Real.log |aStar - a|) - (∫ a in A..B, Real.log |((n : ℝ) + u) - a|))| ≤
      |∑ m ∈ Finset.Icc (n - j + 1) (n + j),
            (Real.log (pairModQ c' η₀ x m) -
              (Real.log (((u - ((m : ℝ) - (n : ℝ))) ^ 2 + η₀ ^ 2) * (π * ℓ / 2) ^ 2) +
                2 * Real.log (Real.tanh (π * (x + chiQuantile c' m) / 2))))| +
        |2 * ∑ m ∈ Finset.Icc (n - j + 1) (n + j),
            (Real.log (Real.tanh (π * (x + chiQuantile c' m) / 2)) -
              ∫ a in ((m : ℝ) - 1 / 2)..((m : ℝ) + 1 / 2),
                Real.log (Real.tanh (π * (x + chiQuantile c' a) / 2)))| +
        2 * |∫ a in A..B, E_int a| +
        2 * |(∫ a in A..B, Real.log |aStar - a|) - (∫ a in A..B, Real.log |((n : ℝ) + u) - a|)| := by
    have t1 : ∀ a b : ℝ, |a - 2 * b| ≤ |a| + 2 * |b| := fun a b =>
      calc |a - 2 * b| ≤ |a| + |2 * b| := abs_sub _ _
        _ = |a| + 2 * |b| := by rw [abs_mul, abs_two]
    exact (t1 _ _).trans (add_le_add ((t1 _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
  have hE2 := mul_le_mul_of_nonneg_left hE_int_bd two_pos.le
  have hL2 := mul_le_mul_of_nonneg_left h_abs_log_diff two_pos.le
  have h_alg := hole_limit_K5_combine hj_pos.le hn_pos hℓ_pos hℓ1 hη₀0
  exact h_tri1.trans ((add_le_add (add_le_add (add_le_add h_sum1 h_sum2) hE2) hL2).trans h_alg)

/-- **General reference floor** (`cmb:K5`, `comb_estimates.tex`, line 217): the hole limit `hole_limit_K5`
turned into a floor for any quantity `B ≥ 0` (a norm `‖B_D(x)‖` of a comb) that satisfies the exponential
lower bound `exp(𝓗_{n,j} - 2𝓔_left + W) ≤ B e^{c' L - c' P^{(f)} - J_end}` with a modification term `W ∈ ℝ`:
`μ_j (1 - C(1/n + ℓ_n)) e^{-2𝓔_left + W} ≤ ¼ B e^{c' L} e^{-(c' P^{(f)} + J_end)}`.
`hole_floor_K5` is the case of the reference comb (`B = ‖B_ref(x)‖`, `W = 0`) and
`Upper.Holes.designComb_floor` the case of a finite modification. -/
theorem hole_floor_general {j : ℕ} {η₀ : ℝ} (hj : 1 ≤ j) (hη₀0 : 0 < η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∃ (N_j : ℕ) (C : ℝ), 1 ≤ N_j ∧ 0 < C ∧
      ∀ᶠ c' in atTop, ∀ (f n : ℕ) (x : ℝ), 1 ≤ f → max N_j (f + j) ≤ n → inCell c' n x →
        ∀ B W : ℝ, 0 ≤ B →
          Real.exp (holeH c' η₀ n j x - 2 * eLeftComb c' f n j x + W) ≤
            B * Real.exp (c' * slitL x) * Real.exp (-(c' * combPf c' f x + jEndComb c' x f)) →
          muHole j η₀ * (1 - C * (1 / (n : ℝ) + siteGap c' n)) *
              Real.exp (-2 * eLeftComb c' f n j x + W) ≤
            (1 / 4 : ℝ) * (B * Real.exp (c' * slitL x) *
              Real.exp (-(c' * combPf c' f x + jEndComb c' x f))) := by
  obtain ⟨N_j, C, hNj, hC_pos, h_ev⟩ := hole_limit_K5 hj hη₀0 hη₀1
  refine ⟨N_j, C, hNj, hC_pos, ?_⟩
  filter_upwards [h_ev, eventually_gt_atTop (0 : ℝ)] with c' h_lim hc'
  intro f n x hf hn_max hx B W hB0 hB
  have hn_Nj : N_j ≤ n := (le_max_left _ _).trans hn_max
  have hfnj : f + j ≤ n := (le_max_right _ _).trans hn_max
  have hf1 : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hfn : (f : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : f < n)
  have h_hole_lim := h_lim n x hn_Nj hx
  set u := (x - chiQuantile c' n) / siteGap c' n
  have hu_mem : u ∈ Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (sub_nonneg.mpr hx.1) (by
      unfold siteGap
      exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn
        (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith)) (by linarith))), ?_⟩
    have hℓ_pos : 0 < siteGap c' n := by
      unfold siteGap
      exact sub_pos.mpr (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith))
        (Set.mem_Ici.mpr (by linarith)) (by linarith))
    rw [div_le_one hℓ_pos]
    unfold siteGap
    have h_cast : chiQuantile c' ((n + 1 : ℕ) : ℝ) = chiQuantile c' ((n : ℝ) + 1) := by
      push_cast; rfl
    rw [← h_cast]; linarith [hx.2]
  have h_mu_le : muHole j η₀ ≤ (1 / 4 : ℝ) * Real.exp (holeModel j u η₀) := by
    unfold muHole
    exact csInf_le ⟨0, by rintro _ ⟨v, _, rfl⟩; positivity⟩ ⟨u, hu_mem, rfl⟩
  have h_lin_exp : 1 - C * (1 / (n : ℝ) + siteGap c' n) ≤
      Real.exp (-(C * (1 / (n : ℝ) + siteGap c' n))) := by
    linarith [Real.add_one_le_exp (-(C * (1 / (n : ℝ) + siteGap c' n)))]
  have h_hole_ge : holeModel j u η₀ - C * (1 / (n : ℝ) + siteGap c' n) ≤ holeH c' η₀ n j x :=
    by linarith [(abs_le.mp h_hole_lim).1]
  have h_exp_hole : Real.exp (holeModel j u η₀) * (1 - C * (1 / (n : ℝ) + siteGap c' n)) ≤
      Real.exp (holeH c' η₀ n j x) := by
    calc Real.exp (holeModel j u η₀) * (1 - C * (1 / (n : ℝ) + siteGap c' n))
        ≤ Real.exp (holeModel j u η₀) * Real.exp (-(C * (1 / (n : ℝ) + siteGap c' n))) :=
          mul_le_mul_of_nonneg_left h_lin_exp (Real.exp_pos _).le
      _ = Real.exp (holeModel j u η₀ - C * (1 / (n : ℝ) + siteGap c' n)) := by
          rw [← Real.exp_add, ← sub_eq_add_neg]
      _ ≤ Real.exp (holeH c' η₀ n j x) := Real.exp_le_exp.mpr h_hole_ge
  have h_mu_nn : 0 ≤ muHole j η₀ := by
    unfold muHole; exact le_csInf ⟨_, ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩⟩ fun _ ⟨_, _, h⟩ => h ▸ by positivity
  by_cases hpos : 0 ≤ 1 - C * (1 / (n : ℝ) + siteGap c' n)
  · calc muHole j η₀ * (1 - C * (1 / (n : ℝ) + siteGap c' n)) * Real.exp (-2 * eLeftComb c' f n j x + W)
        ≤ ((1 / 4 : ℝ) * Real.exp (holeModel j u η₀)) * (1 - C * (1 / (n : ℝ) + siteGap c' n)) *
            Real.exp (-2 * eLeftComb c' f n j x + W) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h_mu_le hpos) (Real.exp_pos _).le
      _ = (1 / 4 : ℝ) * (Real.exp (holeModel j u η₀) * (1 - C * (1 / (n : ℝ) + siteGap c' n))) *
            Real.exp (-2 * eLeftComb c' f n j x + W) := by ring
      _ ≤ (1 / 4 : ℝ) * Real.exp (holeH c' η₀ n j x) * Real.exp (-2 * eLeftComb c' f n j x + W) := by
            gcongr
      _ = (1 / 4 : ℝ) * Real.exp (holeH c' η₀ n j x - 2 * eLeftComb c' f n j x + W) := by
            rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ (1 / 4 : ℝ) * (B * Real.exp (c' * slitL x) *
            Real.exp (-(c' * combPf c' f x + jEndComb c' x f))) := by
            gcongr
  · push Not at hpos
    have h_lhs_np : muHole j η₀ * (1 - C * (1 / (n : ℝ) + siteGap c' n)) *
        Real.exp (-2 * eLeftComb c' f n j x + W) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos h_mu_nn hpos.le) (Real.exp_pos _).le
    have h_rhs_nn : 0 ≤ (1 / 4 : ℝ) * (B * Real.exp (c' * slitL x) *
        Real.exp (-(c' * combPf c' f x + jEndComb c' x f))) := by positivity
    exact h_lhs_np.trans h_rhs_nn


/-- Reference floor (`cmb:K5`, `comb_estimates.tex`, line 217):
for fixed $j \ge 1$ and $\eta_0 \in (0, \tfrac14]$, there exist $N_j \ge 1$ and $C > 0$
independent of $f$ such that for large $c'$, every $f \ge 1$, every $n \ge \max(N_j, f + j)$,
and every $x \in [\chi_n, \chi_{n+1})$,
$h_0^{\mathrm{ref}(f)}(x) / \mathrm{Lev}^{(f)}(x) \ge \mu_j(\eta_0)(1 - C(n^{-1} + \ell_n)) e^{-2\mathcal{E}_{\mathrm{left}}}$. -/
theorem hole_floor_K5 {j : ℕ} {η₀ : ℝ} (hj : 1 ≤ j) (hη₀0 : 0 < η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∃ (N_j : ℕ) (C : ℝ), 1 ≤ N_j ∧ 0 < C ∧
      ∀ᶠ c' in atTop, ∀ (f n : ℕ) (x : ℝ), 1 ≤ f → max N_j (f + j) ≤ n → inCell c' n x →
        muHole j η₀ * (1 - C * (1 / (n : ℝ) + siteGap c' n)) *
            Real.exp (-2 * eLeftComb c' f n j x) ≤
          h0Comb c' f η₀ x / levComb c' f x := by
  obtain ⟨N_j, C, hNj, hC_pos, h_ev⟩ := hole_floor_general hj hη₀0 hη₀1
  obtain ⟨_, _, hgap_ev⟩ := siteGap_eventually_le
  refine ⟨N_j, C, hNj, hC_pos, ?_⟩
  filter_upwards [h_ev, hgap_ev, eventually_gt_atTop (0 : ℝ)] with c' h_gen hgap_c hc'
  have hgap1 : siteGap c' 1 ≤ 1 / 2 := hgap_c.2.2.2
  intro f n x hf hn_max hx
  have hn_Nj : N_j ≤ n := (le_max_left _ _).trans hn_max
  have hfnj : f + j ≤ n := (le_max_right _ _).trans hn_max
  have hf1 : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hfn : (f : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : f < n)
  have hχf_lt : chiQuantile c' f < x :=
    (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith))
      (Set.mem_Ici.mpr (by linarith)) hfn).trans_le hx.1
  obtain ⟨_, _, _, _, h0_norm⟩ := refComb_re_nonneg_of_gt hc' hη₀0.le hη₀1 hgap1 hf hχf_lt
  have h_quot_eq : h0Comb c' f η₀ x / levComb c' f x =
      (1 / 4 : ℝ) * (‖refComb c' f η₀ (x : ℂ)‖ * Real.exp (c' * slitL x) *
        Real.exp (-(c' * combPf c' f x + jEndComb c' x f))) := by
    rw [h0_norm]
    unfold levComb
    have hch_ne : Real.cosh (π * x / 2) ≠ 0 := (Real.cosh_pos _).ne'
    have hexp_mul : Real.exp (-c' * slitL x + c' * combPf c' f x + jEndComb c' x f) =
        Real.exp (-(c' * slitL x)) * Real.exp (c' * combPf c' f x + jEndComb c' x f) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hexp_mul, Real.exp_neg, Real.exp_neg]
    field_simp [hch_ne, (Real.exp_pos _).ne']
  have h_low := (hole_lower_K4 hc' hη₀0.le hη₀1 hgap1 hf hj hfnj hx).2
  have href_pos : 0 < ‖refComb c' f η₀ (x : ℂ)‖ := by
    have hlog := (lambdaHole_summable_and_le hc' hη₀0.le hη₀1 hgap1 hf (by omega : f + 1 ≤ n) hx).2.2
      (Or.inl hη₀0)
    by_contra hnp
    have h0 : ‖refComb c' f η₀ (x : ℂ)‖ = 0 := le_antisymm (not_lt.mp hnp) (norm_nonneg _)
    -- From `HasSum log(q_m)` we get `HasProd q_m (exp (∑' log q_m))`, showing `∏' P m ≠ 0`.
    exfalso
    have hχn_nn : 0 ≤ chiQuantile c' n := xiStar_pos.le.trans (chiQuantile_spec hc' (by linarith)).1
    have hx0 : 0 ≤ x := hχn_nn.trans hx.1
    have hf_ne : chiQuantile c' f ≠ x := hχf_lt.ne
    have hq_all : ∀ m : ℕ, 0 < pairModQ c' η₀ x (f + 1 + m) := fun m => by
      by_cases hkn : f + 1 + m = n
      · rw [hkn]; exact pairModQ_pos hc' hη₀0.le hη₀1 hgap1 (by omega) hx (Or.inl hη₀0)
      · exact pairModQ_pos hc' hη₀0.le hη₀1 hgap1 (by omega) hx (Or.inl hη₀0)
    have hsum_q := (lambdaHole_summable_and_le hc' hη₀0.le hη₀1 hgap1 hf (by omega : f + 1 ≤ n) hx).1
    have h_prod_exp : HasProd (fun m : ℕ => pairModQ c' η₀ x (f + 1 + m))
        (Real.exp (∑' m : ℕ, Real.log (pairModQ c' η₀ x (f + 1 + m)))) := by
      have h_ts := hsum_q.hasSum
      have h_exp := (Real.continuous_exp.continuousAt.tendsto.comp h_ts)
      refine h_exp.congr fun s => ?_
      dsimp [Function.comp_def]
      rw [Real.exp_sum]
      exact Finset.prod_congr rfl fun m _ => Real.exp_log (hq_all m)
    -- And `comb_pairProd_hasProdLocallyUniformlyOn` gives `∏' m, P m`!
    let χ := fun m : ℕ => chiQuantile c' (f + 1 + m : ℕ)
    let ε := fun m : ℕ => η₀ * siteGap c' (f + 1 + m)
    let P : ℕ → ℂ := fun m =>
      blaschkeT ((χ m : ℂ) + (ε m : ℂ) * Complex.I) (x : ℂ) *
        blaschkeT ((χ m : ℂ) - (ε m : ℂ) * Complex.I) (x : ℂ)
    have hχ_nn : ∀ m : ℕ, 0 ≤ χ m := fun m => by
      have hm1 : (1 : ℝ) ≤ ((f + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ f + 1 + m)
      exact xiStar_pos.le.trans (chiQuantile_spec hc' (by linarith)).1
    have hε_bd : ∀ m : ℕ, |ε m| ≤ 1 / 8 := fun m => by
      dsimp [ε]
      have hgk : siteGap c' (f + 1 + m) ≤ siteGap c' 1 := by
        have hanti := (siteGap_strictAnti hc').antitone (show 0 ≤ f + 1 + m - 1 by omega)
        have heq : (f + 1 + m - 1) + 1 = f + 1 + m := by omega
        rwa [heq] at hanti
      have hm1 : (1 : ℝ) ≤ ((f + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ f + 1 + m)
      have hgk_nn : 0 ≤ siteGap c' (f + 1 + m) := by
        unfold siteGap
        exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn
          (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith)) (by linarith))
      rw [abs_of_nonneg (mul_nonneg hη₀0.le hgk_nn)]; nlinarith only [hgk, hgap1, hgk_nn, hη₀0, hη₀1]
    have hhasProd := (comb_pairProd_hasProdLocallyUniformlyOn χ ε hχ_nn hε_bd
      (summable_exp_neg_pi_chiQuantile hc' f)).hasProd
      (by simp : (x : ℂ) ∈ {b : ℂ | |b.im| < 7 / 8})
    have h_tprod_nz : (∏' m : ℕ, P m) =
        ((Real.exp (∑' m : ℕ, Real.log (pairModQ c' η₀ x (f + 1 + m))) : ℝ) : ℂ) := by
      refine tendsto_nhds_unique hhasProd ?_
      have h_ev2 := Complex.continuous_ofReal.continuousAt.tendsto.comp h_prod_exp
      refine h_ev2.congr fun s => ?_
      dsimp [Function.comp_def]
      rw [Complex.ofReal_prod]
      exact Finset.prod_congr rfl fun m _ => by
        dsimp [P, χ, ε]; unfold pairModQ; exact (blaschkeT_pair_real _ _ _).symm
    have hTf_ne : blaschkeT (chiQuantile c' f : ℂ) (x : ℂ) ≠ 0 := by
      unfold blaschkeT
      have h1 : Complex.tanh ((π : ℂ) * ((x : ℂ) - (chiQuantile c' f : ℂ)) / 2) ≠ 0 := by
        have hc1 : Complex.tanh ((π : ℂ) * ((x : ℂ) - (chiQuantile c' f : ℂ)) / 2) =
            ((Real.tanh (π * (x - chiQuantile c' f) / 2) : ℝ) : ℂ) := by
          have h1' : Complex.tanh ((π * (x - chiQuantile c' f) / 2 : ℝ) : ℂ) =
              ((Real.tanh (π * (x - chiQuantile c' f) / 2) : ℝ) : ℂ) := by
            rw [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
              ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, Complex.ofReal_div]
          rw [← h1']; congr 1; push_cast; ring
        rw [hc1, Complex.ofReal_ne_zero, Real.tanh_eq_sinh_div_cosh]
        exact div_ne_zero (Real.sinh_ne_zero.mpr (by nlinarith only [Real.pi_pos, hχf_lt])) (Real.cosh_pos _).ne'
      have h2 : Complex.tanh ((π : ℂ) * ((x : ℂ) + (chiQuantile c' f : ℂ)) / 2) ≠ 0 := by
        have hc2 : Complex.tanh ((π : ℂ) * ((x : ℂ) + (chiQuantile c' f : ℂ)) / 2) =
            ((Real.tanh (π * (x + chiQuantile c' f) / 2) : ℝ) : ℂ) := by
          have h1' : Complex.tanh ((π * (x + chiQuantile c' f) / 2 : ℝ) : ℂ) =
              ((Real.tanh (π * (x + chiQuantile c' f) / 2) : ℝ) : ℂ) := by
            rw [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
              ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, Complex.ofReal_div]
          rw [← h1']; congr 1; push_cast; ring
        rw [hc2, Complex.ofReal_ne_zero, Real.tanh_eq_sinh_div_cosh]
        have hχf_pos : 0 < chiQuantile c' f := xiStar_pos.trans (xiStar_lt_chiQuantile hc' (by linarith [hf1]))
        have hx_pos : 0 < x := hχf_pos.trans hχf_lt
        have harg : π * (x + chiQuantile c' f) / 2 ≠ 0 :=
          (div_pos (mul_pos Real.pi_pos (add_pos hx_pos hχf_pos)) two_pos).ne'
        exact div_ne_zero (Real.sinh_ne_zero.mpr harg) (Real.cosh_pos _).ne'
      exact mul_ne_zero h1 h2
    have href_eq : refComb c' f η₀ (x : ℂ) =
        blaschkeT (chiQuantile c' f : ℂ) (x : ℂ) * (∏' m : ℕ, P m) := rfl
    have href_ne : refComb c' f η₀ (x : ℂ) ≠ 0 := by
      rw [href_eq, h_tprod_nz]
      exact mul_ne_zero hTf_ne (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')
    exact href_ne (norm_eq_zero.mp h0)
  have h_exp_low : Real.exp (holeH c' η₀ n j x - 2 * eLeftComb c' f n j x) ≤
      ‖refComb c' f η₀ (x : ℂ)‖ * Real.exp (c' * slitL x) *
        Real.exp (-(c' * combPf c' f x + jEndComb c' x f)) := by
    have h_log_bd : holeH c' η₀ n j x - 2 * eLeftComb c' f n j x ≤
        Real.log ‖refComb c' f η₀ (x : ℂ)‖ + c' * slitL x - (c' * combPf c' f x + jEndComb c' x f) := by
      linarith
    have h1 := Real.exp_le_exp.mpr h_log_bd
    have heq_rhs : Real.exp (Real.log ‖refComb c' f η₀ (x : ℂ)‖ + c' * slitL x -
          (c' * combPf c' f x + jEndComb c' x f)) =
        ‖refComb c' f η₀ (x : ℂ)‖ * Real.exp (c' * slitL x) *
          Real.exp (-(c' * combPf c' f x + jEndComb c' x f)) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_log href_pos]
    exact h1.trans_eq heq_rhs
  rw [h_quot_eq]
  have hg := h_gen f n x hf hn_max hx ‖refComb c' f η₀ (x : ℂ)‖ 0 (norm_nonneg _)
    (by rw [add_zero]; exact h_exp_low)
  rwa [add_zero] at hg

/-- Band $j = 1$ overshoot (`cmb:K5`, `comb_estimates.tex`, line 222):
for fixed $\eta_0 \in (0, \tfrac14]$, there exist $N_{\mathrm{ov}} \ge 1$ and $c_T > 0$
such that for large $c'$, every $f \ge 1$, and every $x \ge \chi_{\max(N_{\mathrm{ov}}, f + 1)}$,
$h_0^{\mathrm{ref}(f)}(x)\,e^{c' L(x)} \ge c_T \operatorname{sech}^2(\pi x/2)\,\bigl(\tfrac{2}{\pi(x - \xi_*)}\bigr)^{2n_1}$. -/
theorem band_overshoot_K5 {η₀ : ℝ} (hη₀0 : 0 < η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∃ (N_ov : ℕ) (c_T : ℝ), 1 ≤ N_ov ∧ 0 < c_T ∧
      ∀ᶠ c' in atTop, ∀ (f : ℕ) (x : ℝ), 1 ≤ f →
        chiQuantile c' (max N_ov (f + 1) : ℕ) ≤ x →
          c_T * (1 / Real.cosh (π * x / 2) ^ 2) * (2 / (π * (x - xiStar))) ^ (2 * n1Comb f) ≤
            h0Comb c' f η₀ x * Real.exp (c' * slitL x) := by
  obtain ⟨N_1, C_1, hN1_1, hC1_pos, h_floor⟩ := hole_floor_K5 (j := 1) le_rfl hη₀0 hη₀1
  obtain ⟨C_L, hCL_pos, h_eL⟩ := eLeftComb_bounds
  obtain ⟨C_gap, hCgap_pos, h_gap_ev⟩ := siteGap_eventually_le
  -- Choose `N_ov` large enough that `C_1 * (1 / n + ℓ_n) ≤ 1 / 2` AND `2 * C_L * λ / (x - ξ_*) ≤ 1`
  let K_r : ℕ := Nat.ceil ((2 * C_L * (1 + c1K0) ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ)) + 2
  let N_ov : ℕ := max N_1 (max (Nat.ceil (4 * C_1) + 2) K_r)
  let c_T : ℝ := (1 / 32 : ℝ) * η₀ ^ 2 * Real.exp (-1)
  have hNov_pos : 1 ≤ N_ov := le_trans hN1_1 (le_max_left _ _)
  have hcT_pos : 0 < c_T := by dsimp [c_T]; positivity
  refine ⟨N_ov, c_T, hNov_pos, hcT_pos, ?_⟩
  have h_lam_ev : ∀ᶠ c' in atTop, C_gap * lambdaComb c' ≤ 1 / (4 * C_1) ∧
      2 * C_L * lambdaComb c' ≤ 1 := by
    have htend : Tendsto lambdaComb atTop (𝓝 0) := by
      unfold lambdaComb
      have h_mul : Tendsto (fun c' : ℝ => kTip * c') atTop atTop :=
        tendsto_atTop_atTop.mpr fun M => ⟨M / kTip, fun x hx => by
          rw [div_le_iff₀ kTip_pos] at hx; linarith⟩
      exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp h_mul
    exact ((htend.const_mul C_gap).eventually (by
      rw [mul_zero]; exact eventually_le_nhds (by positivity : (0 : ℝ) < 1 / (4 * C_1)))).and
      ((htend.const_mul (2 * C_L)).eventually (by
        rw [mul_zero]; exact eventually_le_nhds one_pos))
  filter_upwards [h_floor, h_eL, h_gap_ev, h_lam_ev, eventually_gt_atTop (0 : ℝ)] with
    c' hfl heL hgap_c hlam_c hc'
  intro f x hf hx_ge
  let M : ℕ := max N_ov (f + 1)
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
  have h_cell_ex : ∃ n : ℕ, M ≤ n ∧ inCell c' n x := by
    have htend := tendsto_chiQuantile_atTop hc'
    obtain ⟨K, hK⟩ := (htend.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop x |>.exists
    let S := (Finset.Icc M (max M K)).filter (fun m : ℕ => chiQuantile c' m ≤ x)
    have hM_mem : M ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, le_max_left _ _⟩, hx_ge⟩
    have hne : S.Nonempty := ⟨M, hM_mem⟩
    let n := S.max' hne
    have hn_mem := Finset.mem_filter.mp (Finset.max'_mem S hne)
    have hn_Icc := Finset.mem_Icc.mp hn_mem.1
    have hn1_lt : x < chiQuantile c' (n + 1 : ℕ) := by
      by_contra hle
      push Not at hle
      have hn_lt_maxK : n < max M K := by
        rcases eq_or_lt_of_le hn_Icc.2 with heq | hlt
        · exfalso
          have hmax_le : x < chiQuantile c' ((max M K : ℕ) : ℝ) := by
            by_cases hMK : M ≤ K
            · rw [max_eq_right hMK]; exact hK
            · push Not at hMK
              have hlt' : (K : ℝ) < (M : ℝ) := by exact_mod_cast hMK
              have hK14 : (1 / 4 : ℝ) ≤ (K : ℝ) := by
                by_cases hK0 : K = 0
                · exfalso
                  rw [hK0] at hK
                  dsimp only [Function.comp_def] at hK
                  rw [Nat.cast_zero] at hK
                  have h0 : chiQuantile c' 0 = xiStar := by
                    unfold chiQuantile
                    split_ifs with h
                    · exfalso; linarith
                    · rfl
                  rw [h0] at hK
                  have hMxi : xiStar < chiQuantile c' M := xiStar_lt_chiQuantile hc' (by linarith)
                  linarith
                · have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : 1 ≤ K)
                  linarith
              have hmax1 : (1 : ℝ) ≤ ((max M K : ℕ) : ℝ) := by exact_mod_cast (le_trans (by omega : 1 ≤ M) (le_max_left _ _))
              rw [max_eq_left hMK.le]
              exact hK.trans (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith [hK14]))
                (Set.mem_Ici.mpr (by linarith)) hlt')
          rw [heq] at hn_mem
          linarith [hn_mem.2]
        · exact hlt
      have hn1_mem : n + 1 ∈ S := Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hle⟩
      have := Finset.le_max' S (n + 1) hn1_mem
      omega
    exact ⟨n, hn_Icc.1, hn_mem.2, hn1_lt⟩
  rcases h_cell_ex with ⟨n, hnM, hx_cell⟩
  have hn_max1 : max N_1 (f + 1) ≤ n :=
    (max_le (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)).trans hnM
  have hfl_n := hfl f n x hf hn_max1 hx_cell
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h_C1_n : C_1 * (1 / (n : ℝ)) ≤ 1 / 4 := by
    have hn_ce : Nat.ceil (4 * C_1) + 2 ≤ n :=
      (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))).trans hnM
    have h4c : 4 * C_1 ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (by omega : Nat.ceil (4 * C_1) ≤ n))
    rw [mul_one_div, div_le_iff₀ hn_pos]; linarith
  have h_gap_n : siteGap c' n ≤ siteGap c' 1 := by
    have hn1 : 1 ≤ n := by omega
    rcases eq_or_lt_of_le hn1 with h1 | hgt
    · rw [← h1]
    · have hanti := (siteGap_strictAnti hc').antitone (show 0 ≤ n - 1 by omega)
      have heq : (n - 1) + 1 = n := by omega
      rwa [heq] at hanti
  have h_C1_gap : C_1 * siteGap c' n ≤ 1 / 4 := by
    calc C_1 * siteGap c' n ≤ C_1 * (C_gap * lambdaComb c') := by
          gcongr; exact h_gap_n.trans (hgap_c.2.1.trans hgap_c.2.2.1)
      _ ≤ C_1 * (1 / (4 * C_1)) := by gcongr; exact hlam_c.1
      _ = 1 / 4 := by field_simp [hC1_pos.ne']
  have h_fac_half : (1 / 2 : ℝ) ≤ 1 - C_1 * (1 / (n : ℝ) + siteGap c' n) := by linarith
  have h_mu1 : (1 / 16 : ℝ) * η₀ ^ 2 ≤ muHole 1 η₀ := muHole_one_ge hη₀0.le hη₀1
  have hn_K_r : K_r ≤ n :=
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))).trans hnM
  have hn1_r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hn14 : (1 / 4 : ℝ) < (n : ℝ) := by linarith
  have hx_xi : xiStar < x := (xiStar_lt_chiQuantile hc' hn14).trans_le hx_cell.1
  have hs_pos : 0 < x - xiStar := sub_pos.mpr hx_xi
  have h_eL_bd : 2 * eLeftComb c' f n 1 x ≤ 1 := by
    have h_eL_ub := (heL f n 1 x hf hx_xi).2
    have h_rad_lb : 2 * C_L * lambdaComb c' ≤ x - xiStar := by
      by_cases hr1 : siteRadius c' n ≤ 1
      · have hsr := (siteRadius_le_one_bounds hc' hn14 hr1).1
        have h_n_ge : (2 * C_L * (1 + c1K0) ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) ≤ (n : ℝ) - 1 / 4 := by
          have : Nat.ceil ((2 * C_L * (1 + c1K0) ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ)) + 1 ≤ n := by
            have : K_r ≤ n := hn_K_r
            omega
          have h1 : (2 * C_L * (1 + c1K0) ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) ≤
              ((Nat.ceil ((2 * C_L * (1 + c1K0) ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ)) : ℕ) : ℝ) := Nat.le_ceil _
          have h2 : ((Nat.ceil ((2 * C_L * (1 + c1K0) ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ)) : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
            exact_mod_cast this
          linarith
        have hc1k0_pos : 0 < 1 + c1K0 := by linarith [c1K0_pos]
        have h_rpow := Real.rpow_le_rpow (by positivity) h_n_ge (by norm_num : (0 : ℝ) ≤ 2 / 3)
        have h_simp : (((2 * C_L * (1 + c1K0) ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ)) : ℝ) ^ (2 / 3 : ℝ) =
            2 * C_L * (1 + c1K0) ^ (2 / 3 : ℝ) := by
          rw [← Real.rpow_mul (by positivity)]
          norm_num
        rw [h_simp] at h_rpow
        have h_sr_le : siteRadius c' n ≤ x - xiStar := by unfold siteRadius; linarith [hx_cell.1]
        have h_comb_ge : 2 * C_L ≤ (1 + c1K0) ^ (-(2 / 3 : ℝ)) * ((n : ℝ) - 1 / 4) ^ (2 / 3 : ℝ) := by
          rw [Real.rpow_neg hc1k0_pos.le]
          have hpos : 0 < (1 + c1K0) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc1k0_pos _
          calc 2 * C_L = ((1 + c1K0) ^ (2 / 3 : ℝ))⁻¹ * (2 * C_L * (1 + c1K0) ^ (2 / 3 : ℝ)) := by
                field_simp [hpos.ne']
            _ ≤ ((1 + c1K0) ^ (2 / 3 : ℝ))⁻¹ * ((n : ℝ) - 1 / 4) ^ (2 / 3 : ℝ) := by gcongr
        have hlam_pos : 0 < lambdaComb c' := by unfold lambdaComb; have := kTip_pos; positivity
        calc 2 * C_L * lambdaComb c'
            ≤ ((1 + c1K0) ^ (-(2 / 3 : ℝ)) * phiQuantile n) * lambdaComb c' := by
              unfold phiQuantile; exact mul_le_mul_of_nonneg_right h_comb_ge hlam_pos.le
          _ = (1 + c1K0) ^ (-(2 / 3 : ℝ)) * (lambdaComb c' * phiQuantile n) := by ring
          _ ≤ siteRadius c' n := hsr
          _ ≤ x - xiStar := h_sr_le
      · push Not at hr1
        have : siteRadius c' n ≤ x - xiStar := by unfold siteRadius; linarith [hx_cell.1]
        linarith [hlam_c.2]
    calc 2 * eLeftComb c' f n 1 x
        ≤ 2 * (C_L * lambdaComb c' / (x - xiStar)) := by linarith
      _ = (2 * C_L * lambdaComb c') / (x - xiStar) := by ring
      _ ≤ (x - xiStar) / (x - xiStar) := by gcongr
      _ = 1 := div_self hs_pos.ne'
  have h_floor_num : c_T ≤ h0Comb c' f η₀ x / levComb c' f x := by
    calc c_T = ((1 / 16 : ℝ) * η₀ ^ 2) * (1 / 2 : ℝ) * Real.exp (-1) := by dsimp [c_T]; ring
      _ ≤ muHole 1 η₀ * (1 - C_1 * (1 / (n : ℝ) + siteGap c' n)) *
            Real.exp (-2 * eLeftComb c' f n 1 x) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul h_mu1 h_fac_half (by norm_num)
              (le_trans (by positivity) h_mu1)) (Real.exp_pos _).le |>.trans
            (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
              (mul_nonneg (le_trans (by positivity) h_mu1) (by linarith)))
      _ ≤ h0Comb c' f η₀ x / levComb c' f x := hfl_n
  have hf1_r : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hfn_r : (f : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : f < n)
  have hfn_half_lt : (f : ℝ) + 1 / 2 < (n : ℝ) := by
    have : f + 1 ≤ n := by omega
    have h1 : (f : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast this
    linarith
  have hχf_lt : chiQuantile c' f < x :=
    (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith))
      (Set.mem_Ici.mpr (by linarith)) hfn_r).trans_le hx_cell.1
  have hχf12_lt : chiQuantile c' ((f : ℝ) + 1 / 2) < x :=
    (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith))
      (Set.mem_Ici.mpr (by linarith)) hfn_half_lt).trans_le hx_cell.1
  have hj_nn : 0 ≤ jEndComb c' x f := (jEndComb_bounds hc' hf hχf12_lt).1
  have hPf_exp := (combPf_bounds_K4 hc' hf hχf_lt).2.2
  have hlev_pos : 0 < levComb c' f x := by
    unfold levComb
    exact mul_pos (mul_pos (by norm_num) (div_pos one_pos (sq_pos_of_pos (Real.cosh_pos _))))
      (Real.exp_pos _)
  have h_mul_lev : c_T * (levComb c' f x * Real.exp (c' * slitL x)) ≤
      h0Comb c' f η₀ x * Real.exp (c' * slitL x) := by
    have h1 := (le_div_iff₀ hlev_pos).mp h_floor_num
    calc c_T * (levComb c' f x * Real.exp (c' * slitL x))
        = (c_T * levComb c' f x) * Real.exp (c' * slitL x) := by ring
      _ ≤ h0Comb c' f η₀ x * Real.exp (c' * slitL x) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have h_lev_exp_ge2 : (1 / Real.cosh (π * x / 2) ^ 2) *
        (2 / (π * (x - xiStar))) ^ (2 * n1Comb f) ≤
      levComb c' f x * Real.exp (c' * slitL x) := by
    unfold levComb
    have h_exp_prod : Real.exp (-c' * slitL x + c' * combPf c' f x + jEndComb c' x f) *
          Real.exp (c' * slitL x) = Real.exp (c' * combPf c' f x + jEndComb c' x f) := by
      rw [← Real.exp_add]; congr 1; ring
    have h_exp_ge : Real.exp (c' * combPf c' f x) ≤
        Real.exp (c' * combPf c' f x + jEndComb c' x f) :=
      Real.exp_le_exp.mpr (by linarith)
    calc (1 / Real.cosh (π * x / 2) ^ 2) * (2 / (π * (x - xiStar))) ^ (2 * n1Comb f)
        ≤ (1 / Real.cosh (π * x / 2) ^ 2) * Real.exp (c' * combPf c' f x) :=
          mul_le_mul_of_nonneg_left hPf_exp (div_nonneg one_pos.le (sq_nonneg _))
      _ ≤ (1 / Real.cosh (π * x / 2) ^ 2) * Real.exp (c' * combPf c' f x + jEndComb c' x f) :=
          mul_le_mul_of_nonneg_left h_exp_ge (div_nonneg one_pos.le (sq_nonneg _))
      _ ≤ 4 * (1 / Real.cosh (π * x / 2) ^ 2) *
            Real.exp (c' * combPf c' f x + jEndComb c' x f) := by
          have hnn : 0 ≤ (1 / Real.cosh (π * x / 2) ^ 2) *
              Real.exp (c' * combPf c' f x + jEndComb c' x f) := by positivity
          nlinarith only [hnn]
      _ = 4 * (1 / Real.cosh (π * x / 2) ^ 2) *
            Real.exp (-c' * slitL x + c' * combPf c' f x + jEndComb c' x f) *
            Real.exp (c' * slitL x) := by
          rw [mul_assoc (4 * (1 / Real.cosh (π * x / 2) ^ 2)), h_exp_prod]
  calc c_T * (1 / Real.cosh (π * x / 2) ^ 2) * (2 / (π * (x - xiStar))) ^ (2 * n1Comb f)
      = c_T * ((1 / Real.cosh (π * x / 2) ^ 2) * (2 / (π * (x - xiStar))) ^ (2 * n1Comb f)) := by ring
    _ ≤ c_T * (levComb c' f x * Real.exp (c' * slitL x)) :=
        mul_le_mul_of_nonneg_left h_lev_exp_ge2 hcT_pos.le
    _ ≤ h0Comb c' f η₀ x * Real.exp (c' * slitL x) := h_mul_lev

/-! ### Section 4: Axiom verification -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.muHole_four_quarter_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms muHole_four_quarter_gt

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.muHole_one_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms muHole_one_ge

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.hole_limit_K5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hole_limit_K5

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.hole_floor_K5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hole_floor_K5

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.band_overshoot_K5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms band_overshoot_K5

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.hole_floor_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.hole_floor_general

end FormalResearch.ModularBootstrap.Upper.Holes

end
