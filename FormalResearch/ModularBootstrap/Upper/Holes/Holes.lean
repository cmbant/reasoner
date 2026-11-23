module

public import FormalResearch.ModularBootstrap.Upper.Holes.Peano
public import FormalResearch.ModularBootstrap.Upper.Holes.AII

/-!
# Two-Sided Hole Comparison (`cmb:K4`)

Formalizes Lemma K4 (`cmb:K4`) of `CFT/modular_bootstrap/paper/comb_estimates.tex`
(lines 138--209):

* `jEndComb`, `holeH`, `holeModel`, `eLeftCell`, `eLeftComb`, `lambdaHole`:
  endpoint error $J_{\mathrm{end}}^{(f)}(x)$, hole residual $\mathcal{H}_{n,j}(x;\eta_0)$,
  linearized hole model $H_j(u,\eta_0)$, left curvature error $\mathcal{E}_{\mathrm{left}}$,
  and formal hole series $\Lambda^{(f)}(x;\eta_0)$.
* `holeModel_quarter_eq_hAII`: exact identity $H_j(u, \tfrac14) = h_j(u - \tfrac12)$ with `hAII`.
* `jEndComb_bounds` and `combPf_bounds_K4`: endpoint integral error and profile $P^{(f)}(x)$ bounds.
* `eLeftComb_bounds`: $0 \le \mathcal{E}_{\mathrm{left}} \le C_L \lambda(c') / (x - \xi_*)$ eventually in $c'$.
* `hole_lower_K4`: unconditional two-sided lower bound on $\Lambda^{(f)}(x;\eta_0)$ and
  $\log|B^{(f)}(x)| + c' L(x) - c' P^{(f)}(x)$ (valid even when $\eta_0 = 0, x = \chi_n$).
* `hole_upper_K4`, `hole_upper_K4_log`: upper bound on $B^{(f)}(x)$ in both unconditional
  multiplicative form and logarithmic form away from $(\eta_0 = 0, x = \chi_n)$.
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Holes

open FormalResearch.ModularBootstrap.Upper.Comb

/-! ### Section 1: K4 definitions and hole model identity -/

/-- Endpoint Euler--Maclaurin defect $J_{\mathrm{end}}^{(f)}(x) = \varphi(f) - 2\int_f^{f+1/2}\varphi(a)\,da$. -/
noncomputable def jEndComb (c' x : ℝ) (f : ℕ) : ℝ :=
  phiVar c' x f - 2 * ∫ a in (f : ℝ)..((f : ℝ) + 1 / 2), phiVar c' x a

/-- Hole residual $\mathcal{H}_{n,j}(x;\eta_0)$ on the $2j$ sites $k \in [n - j + 1, n + j]$. -/
noncomputable def holeH (c' η₀ : ℝ) (n j : ℕ) (x : ℝ) : ℝ :=
  (∑ k ∈ Finset.Icc (n - j + 1) (n + j), Real.log (pairModQ c' η₀ x k)) -
    2 * ∫ a in ((n : ℝ) - (j : ℝ) + 1 / 2)..((n : ℝ) + (j : ℝ) + 1 / 2), phiVar c' x a

/-- Linearized hole model $H_j(u, \eta_0)$ (`comb_estimates.tex`, `K4`/`K5`). -/
noncomputable def holeModel (j : ℕ) (u η₀ : ℝ) : ℝ :=
  (∑ k ∈ Finset.range j,
    Real.log (((u - (k : ℝ) - 1) ^ 2 + η₀ ^ 2) * ((u + (k : ℝ)) ^ 2 + η₀ ^ 2))) -
    2 * ∫ s in (-(j : ℝ) + 1 / 2)..((j : ℝ) + 1 / 2), Real.log |u - s|

/-- Single-cell left curvature bound at site $k \ge 2$. -/
noncomputable def eLeftCell (c' x : ℝ) (k : ℕ) : ℝ :=
  (1 / 12 : ℝ) * (2 / (x - xiStar)) *
    (chiDeriv c' ((k : ℝ) - 1 / 2) ^ 2 / siteRadius c' ((k : ℝ) - 1 / 2))

/-- Total left curvature error $\mathcal{E}_{\mathrm{left}}^{(f,n,j)}(x)$ over $k \in [f + 1, n - j]$. -/
noncomputable def eLeftComb (c' : ℝ) (f n j : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc (f + 1) (n - j), eLeftCell c' x k

/-- Formal log-comb series $\varphi(f) + \sum_{k \ge f+1} \log q_k(x)$, finite-valued even at zeroes. -/
noncomputable def lambdaHole (c' η₀ x : ℝ) (f : ℕ) : ℝ :=
  phiVar c' x f + ∑' m : ℕ, Real.log (pairModQ c' η₀ x (f + 1 + m))

/-- At $\eta_0 = \frac14$, $H_j(u, \frac14) = h_j(u - \frac12)$ (`hAII` from Lemma `A_II`). -/
theorem holeModel_quarter_eq_hAII (j : ℕ) (u : ℝ) :
    holeModel j u (1 / 4) = hAII j (u - 1 / 2) := by
  unfold holeModel hAII
  have hsum : ∑ k ∈ Finset.range j,
      Real.log (((u - (k : ℝ) - 1) ^ 2 + (1 / 4 : ℝ) ^ 2) *
        ((u + (k : ℝ)) ^ 2 + (1 / 4 : ℝ) ^ 2)) =
      ∑ k ∈ Finset.range j,
        Real.log ((((u - 1 / 2) - (k : ℝ) - 1 / 2) ^ 2 + (1 / 4 : ℝ) ^ 2) *
          (((u - 1 / 2) + (k : ℝ) + 1 / 2) ^ 2 + (1 / 4 : ℝ) ^ 2)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1; ring
  have hint : ∫ s in (-(j : ℝ) + 1 / 2)..((j : ℝ) + 1 / 2), Real.log |u - s| =
      ∫ w in (-(j : ℝ))..(j : ℝ), Real.log |(u - 1 / 2) - w| := by
    have hcomp := intervalIntegral.integral_comp_add_right
      (fun s : ℝ => Real.log |u - s|) (1 / 2 : ℝ) (a := -(j : ℝ)) (b := (j : ℝ))
    have h_eq : (fun w : ℝ => Real.log |u - (w + 1 / 2)|) =
        fun w : ℝ => Real.log |(u - 1 / 2) - w| := by
      ext w; congr 1; congr 1; ring
    rw [h_eq] at hcomp
    rw [← hcomp]
  rw [hsum, hint]

/-! ### Section 2: Endpoint error `jEndComb` and profile `combPf` bounds -/

private lemma tanh_le_of_nonneg {t : ℝ} (ht : 0 ≤ t) : Real.tanh t ≤ t := by
  let h : ℝ → ℝ := fun s => Real.tanh s - s
  have hfn : Real.tanh = fun s : ℝ => Real.sinh s / Real.cosh s :=
    funext Real.tanh_eq_sinh_div_cosh
  have hderiv : ∀ s ∈ Icc 0 t, HasDerivAt h ((Real.cosh s)⁻¹ ^ 2 - 1) s := fun s _ => by
    have h1 : HasDerivAt Real.tanh ((Real.cosh s)⁻¹ ^ 2) s := by
      rw [hfn]
      have hq := (Real.hasDerivAt_sinh s).div (Real.hasDerivAt_cosh s) (Real.cosh_pos s).ne'
      refine hq.congr_deriv ?_
      have hid := Real.cosh_sq_sub_sinh_sq s
      field_simp [(Real.cosh_pos s).ne']
      linarith
    exact h1.sub (hasDerivAt_id s)
  have hcont : ContinuousOn h (Icc 0 t) := fun s hs =>
    (hderiv s hs).continuousAt.continuousWithinAt
  have hm := antitoneOn_of_deriv_nonpos (convex_Icc 0 t) hcont
    (fun s hs => by
      rw [interior_Icc] at hs
      exact (hderiv s ⟨hs.1.le, hs.2.le⟩).differentiableAt.differentiableWithinAt)
    (fun s hs => by
      rw [interior_Icc] at hs
      rw [(hderiv s ⟨hs.1.le, hs.2.le⟩).deriv]
      have hch : 1 ≤ Real.cosh s := Real.one_le_cosh s
      have hch_inv : (Real.cosh s)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hch
      have hsq : (Real.cosh s)⁻¹ ^ 2 ≤ 1 := by nlinarith [inv_nonneg.mpr (Real.cosh_pos s).le]
      linarith)
  have h0 := hm (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht) ht
  dsimp [h] at h0
  simp only [Real.tanh_zero, sub_zero] at h0
  linarith

private lemma abs_tanh_le_one {t : ℝ} : |Real.tanh t| ≤ 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, abs_div, abs_of_pos (Real.cosh_pos t),
    div_le_one (Real.cosh_pos t), abs_le]
  rw [Real.sinh_eq, Real.cosh_eq]
  constructor <;> linarith [Real.exp_pos t, Real.exp_pos (-t)]

private lemma phiVar_continuousOn {c' x a b : ℝ} (hc' : 0 < c') (hx : 0 ≤ x) (ha : 1 / 4 < a)
    (_hab : a ≤ b) (hne : ∀ t ∈ Icc a b, chiQuantile c' t ≠ x) :
    ContinuousOn (phiVar c' x) (Icc a b) := fun t ht =>
  (phiVar_hasDerivAt hc' hx (lt_of_lt_of_le ha ht.1) (hne t ht)).1.continuousAt.continuousWithinAt

/-- Endpoint error bounds (`comb_estimates.tex`, line 174):
for $f \ge 1$ and $x > \chi_{f+1/2}$, $0 \le J_{\mathrm{end}}^{(f)}(x) \le \frac{\ell_f}{2(x - \chi_{f+1/2})}$. -/
theorem jEndComb_bounds {c' x : ℝ} (hc' : 0 < c') {f : ℕ} (hf : 1 ≤ f)
    (hx : chiQuantile c' ((f : ℝ) + 1 / 2) < x) :
    0 ≤ jEndComb c' x f ∧
      jEndComb c' x f ≤ (1 / 2 : ℝ) * siteGap c' f / (x - chiQuantile c' ((f : ℝ) + 1 / 2)) := by
  have hf1 : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hf14 : 1 / 4 < (f : ℝ) := by linarith
  have hx0 : 0 ≤ x :=
    (xiStar_pos.le.trans (chiQuantile_spec hc' (by linarith)).1).trans hx.le
  have hχ_lt : ∀ t ∈ Icc (f : ℝ) ((f : ℝ) + 1 / 2), chiQuantile c' t < x := fun t ht => by
    rcases eq_or_lt_of_le ht.2 with rfl | hlt
    · exact hx
    · exact (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith [ht.1]))
        (Set.mem_Ici.mpr (by linarith)) hlt).trans hx
  have hne : ∀ t ∈ Icc (f : ℝ) ((f : ℝ) + 1 / 2), chiQuantile c' t ≠ x := fun t ht =>
    (hχ_lt t ht).ne
  have hcont_phi : ContinuousOn (phiVar c' x) (Icc (f : ℝ) ((f : ℝ) + 1 / 2)) :=
    phiVar_continuousOn hc' hx0 hf14 (by linarith) hne
  have hint_phi : IntervalIntegrable (phiVar c' x) volume (f : ℝ) ((f : ℝ) + 1 / 2) :=
    hcont_phi.intervalIntegrable_of_Icc (by linarith)
  have hderiv_phi : ∀ t ∈ Icc (f : ℝ) ((f : ℝ) + 1 / 2),
      HasDerivAt (phiVar c' x) (phiVarDeriv c' x t) t := fun t ht =>
    (phiVar_hasDerivAt hc' hx0 (lt_of_lt_of_le hf14 ht.1) (hne t ht)).1
  have hderiv_nonpos : ∀ t ∈ Icc (f : ℝ) ((f : ℝ) + 1 / 2), phiVarDeriv c' x t ≤ 0 := by
    intro t ht
    have hlt := hχ_lt t ht
    have ht14 : 1 / 4 < t := lt_of_lt_of_le hf14 ht.1
    have hχ_nn : 0 ≤ chiQuantile c' t := xiStar_pos.le.trans (chiQuantile_spec hc' ht14.le).1
    have hbd := ((realLogT_deriv_bounds hx0 hχ_nn hlt.ne).2.1 hlt).1
    exact mul_nonpos_of_nonpos_of_nonneg hbd (chiDeriv_pos hc' ht14).le
  have h_anti : AntitoneOn (phiVar c' x) (Icc (f : ℝ) ((f : ℝ) + 1 / 2)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont_phi
      (fun t ht => by
        rw [interior_Icc] at ht
        exact (hderiv_phi t ⟨ht.1.le, ht.2.le⟩).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [interior_Icc] at ht
        rw [(hderiv_phi t ⟨ht.1.le, ht.2.le⟩).deriv]
        exact hderiv_nonpos t ⟨ht.1.le, ht.2.le⟩)
  have h_lb : 0 ≤ jEndComb c' x f := by
    have hm := intervalIntegral.integral_mono_on (by linarith : (f : ℝ) ≤ (f : ℝ) + 1 / 2)
      hint_phi (intervalIntegrable_const (μ := volume)) fun t ht =>
        h_anti (left_mem_Icc.mpr (by linarith)) ht ht.1
    rw [intervalIntegral.integral_const, smul_eq_mul] at hm
    unfold jEndComb
    linarith
  refine ⟨h_lb, ?_⟩
  have hd_pos : 0 < x - chiQuantile c' ((f : ℝ) + 1 / 2) := sub_pos.mpr hx
  let M := chiDeriv c' f / (x - chiQuantile c' ((f : ℝ) + 1 / 2))
  have h_slope_bd : ∀ t ∈ Icc (f : ℝ) ((f : ℝ) + 1 / 2), -phiVarDeriv c' x t ≤ M := by
    intro t ht
    have ht14 : 1 / 4 < t := lt_of_lt_of_le hf14 ht.1
    have hlt := hχ_lt t ht
    have hχ_nn : 0 ≤ chiQuantile c' t := xiStar_pos.le.trans (chiQuantile_spec hc' ht14.le).1
    have hbd := (realLogT_deriv_bounds hx0 hχ_nn hlt.ne).2.1 hlt
    have h_abs : -realLogTDeriv x (chiQuantile c' t) ≤ 1 / (x - chiQuantile c' t) := by
      rw [← abs_of_nonpos hbd.1]; exact hbd.2.2.le
    have h_diff : x - chiQuantile c' ((f : ℝ) + 1 / 2) ≤ x - chiQuantile c' t := by
      rcases eq_or_lt_of_le ht.2 with rfl | hlt_t
      · exact le_rfl
      · have := chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith [ht.1]))
          (Set.mem_Ici.mpr (by linarith)) hlt_t
        linarith
    have h_inv : 1 / (x - chiQuantile c' t) ≤ 1 / (x - chiQuantile c' ((f : ℝ) + 1 / 2)) :=
      one_div_le_one_div_of_le hd_pos h_diff
    have h_cd : chiDeriv c' t ≤ chiDeriv c' f := by
      rcases eq_or_lt_of_le ht.1 with rfl | hgt_t
      · exact le_rfl
      · exact (chiDeriv_strictAntiOn hc' (Set.mem_Ioi.mpr hf14) (Set.mem_Ioi.mpr ht14) hgt_t).le
    have hcd_pos := chiDeriv_pos hc' ht14
    calc -phiVarDeriv c' x t
        = (-realLogTDeriv x (chiQuantile c' t)) * chiDeriv c' t := by unfold phiVarDeriv; ring
      _ ≤ (1 / (x - chiQuantile c' ((f : ℝ) + 1 / 2))) * chiDeriv c' f :=
          mul_le_mul (h_abs.trans h_inv) h_cd hcd_pos.le (by positivity)
      _ = M := by dsimp [M]; ring
  have h_pt_diff : ∀ a ∈ Icc (f : ℝ) ((f : ℝ) + 1 / 2),
      phiVar c' x f - (a - (f : ℝ)) * M ≤ phiVar c' x a := by
    intro a ha
    let g : ℝ → ℝ := fun t => phiVar c' x t + (t - (f : ℝ)) * M
    have hg_cont : ContinuousOn g (Icc (f : ℝ) a) :=
      (hcont_phi.mono (Icc_subset_Icc le_rfl ha.2)).add
        (((continuous_id.sub continuous_const).mul continuous_const).continuousOn)
    have hg_deriv : ∀ t ∈ Ioo (f : ℝ) a, HasDerivAt g (phiVarDeriv c' x t + M) t := fun t ht => by
      have htIcc : t ∈ Icc (f : ℝ) ((f : ℝ) + 1 / 2) := ⟨ht.1.le, ht.2.le.trans ha.2⟩
      have h_lin : HasDerivAt (fun y : ℝ => (y - (f : ℝ)) * M) M t := by
        simpa using ((hasDerivAt_id t).sub_const (f : ℝ)).mul_const M
      exact (hderiv_phi t htIcc).add h_lin
    have hm := monotoneOn_of_deriv_nonneg (convex_Icc (f : ℝ) a) hg_cont
      (fun t ht => (hg_deriv t (by rwa [interior_Icc] at ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [interior_Icc] at ht
        have htIcc : t ∈ Icc (f : ℝ) ((f : ℝ) + 1 / 2) := ⟨ht.1.le, ht.2.le.trans ha.2⟩
        rw [(hg_deriv t ht).deriv]
        linarith [h_slope_bd t htIcc])
    have h0 := hm (left_mem_Icc.mpr ha.1) (right_mem_Icc.mpr ha.1) ha.1
    dsimp [g] at h0
    simp only [sub_self, zero_mul, add_zero] at h0
    linarith
  have h_int_m :
      (∫ a in (f : ℝ)..((f : ℝ) + 1 / 2), (phiVar c' x f - (a - (f : ℝ)) * M)) ≤
        ∫ a in (f : ℝ)..((f : ℝ) + 1 / 2), phiVar c' x a :=
    intervalIntegral.integral_mono_on (by linarith : (f : ℝ) ≤ (f : ℝ) + 1 / 2)
      ((continuous_const.sub ((continuous_id.sub continuous_const).mul continuous_const)).intervalIntegrable _ _)
      hint_phi h_pt_diff
  have h_lin_eval : ∫ a in (f : ℝ)..((f : ℝ) + 1 / 2), (phiVar c' x f - (a - (f : ℝ)) * M) =
      (1 / 2 : ℝ) * phiVar c' x f - (1 / 8 : ℝ) * M := by
    have hd : ∀ a ∈ uIcc (f : ℝ) ((f : ℝ) + 1 / 2),
        HasDerivAt (fun s : ℝ => s * phiVar c' x f - ((s - (f : ℝ)) ^ 2 / 2) * M)
          (phiVar c' x f - (a - (f : ℝ)) * M) a := by
      intro a _
      have h1 : HasDerivAt (fun s : ℝ => s * phiVar c' x f) (phiVar c' x f) a := by
        simpa using (hasDerivAt_id a).mul_const _
      have h2 := ((((hasDerivAt_id a).sub_const (f : ℝ)).pow 2).div_const 2).mul_const M
      exact (h1.sub h2).congr_deriv
        (by simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]; ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => s * phiVar c' x f - ((s - (f : ℝ)) ^ 2 / 2) * M) hd
      ((continuous_const.sub ((continuous_id.sub continuous_const).mul continuous_const)).intervalIntegrable _ _)]
    ring
  rw [h_lin_eval] at h_int_m
  have h_gap := siteGap_ge_half_chiDeriv hc' hf
  have hj_le : jEndComb c' x f ≤ (1 / 4 : ℝ) * M := by
    unfold jEndComb; linarith
  have hcd_pos : 0 ≤ chiDeriv c' f := (chiDeriv_pos hc' hf14).le
  calc jEndComb c' x f
      ≤ (1 / 4 : ℝ) * M := hj_le
    _ = (1 / 4 : ℝ) * chiDeriv c' f / (x - chiQuantile c' ((f : ℝ) + 1 / 2)) := by dsimp [M]; ring
    _ ≤ (1 / 2 : ℝ) * siteGap c' f / (x - chiQuantile c' ((f : ℝ) + 1 / 2)) :=
        div_le_div_of_nonneg_right (by linarith) hd_pos.le

/-- Bounds on $c' P^{(f)}(x)$ for $x > \chi_f$ (`comb_estimates.tex`, line 148):
$2 n_1 |f_x(\xi_*)| \le c' P^{(f)}(x) \le 2 n_1 |f_x(\chi_f)|$ and
$(\frac{2}{\pi(x - \xi_*)})^{2 n_1} \le \exp(c' P^{(f)}(x))$. -/
theorem combPf_bounds_K4 {c' x : ℝ} (hc' : 0 < c') {f : ℕ} (hf : 1 ≤ f)
    (hx : chiQuantile c' f < x) :
    2 * n1Comb f * (-realLogT x xiStar) ≤ c' * combPf c' f x ∧
      c' * combPf c' f x ≤ 2 * n1Comb f * (-realLogT x (chiQuantile c' f)) ∧
      (2 / (π * (x - xiStar))) ^ (2 * n1Comb f) ≤ Real.exp (c' * combPf c' f x) := by
  have hf1 : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hf14 : (1 / 4 : ℝ) < (f : ℝ) := by linarith
  have hχf_pos : xiStar < chiQuantile c' f := xiStar_lt_chiQuantile hc' hf14
  have hx_xi : xiStar < x := hχf_pos.trans hx
  have hx0 : 0 ≤ x := xiStar_pos.le.trans hx_xi.le
  rw [combPf_eq_quantile_integral hc' f hf x]
  have hanti_y : AntitoneOn (realLogT x) (Icc xiStar (chiQuantile c' f)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
    · intro y hy
      exact (realLogT_hasDerivAt hx0 (xiStar_pos.le.trans hy.1) (hy.2.trans_lt hx).ne).1.continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact (realLogT_hasDerivAt hx0 (xiStar_pos.le.trans hy.1.le)
        (hy.2.le.trans_lt hx).ne).1.differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have hy_lt : y < x := hy.2.le.trans_lt hx
      have hy0 : 0 ≤ y := xiStar_pos.le.trans hy.1.le
      rw [(realLogT_hasDerivAt hx0 hy0 hy_lt.ne).1.deriv]
      exact ((realLogT_deriv_bounds hx0 hy0 hy_lt.ne).2.1 hy_lt).1
  obtain ⟨_, hint_14, _, _, _⟩ := riesz_real_identities hc' hx0 f hf
  have hint_seg : IntervalIntegrable (fun a => realLogT x (chiQuantile c' a)) volume (1 / 4 : ℝ) (f : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr
      (hint_14.mono_set Ioc_subset_Ioi_self)
  have h_pt_bounds : ∀ a ∈ Icc (1 / 4 : ℝ) (f : ℝ),
      realLogT x (chiQuantile c' f) ≤ realLogT x (chiQuantile c' a) ∧
        realLogT x (chiQuantile c' a) ≤ realLogT x xiStar := by
    intro a ha
    have ha_mem : chiQuantile c' a ∈ Icc xiStar (chiQuantile c' f) :=
      ⟨(chiQuantile_spec hc' ha.1).1,
        (chiQuantile_strictMonoOn hc').monotoneOn (Set.mem_Ici.mpr ha.1)
          (Set.mem_Ici.mpr hf14.le) ha.2⟩
    refine ⟨hanti_y ha_mem (right_mem_Icc.mpr hχf_pos.le) ha_mem.2,
      hanti_y (left_mem_Icc.mpr hχf_pos.le) ha_mem ha_mem.1⟩
  have h_int_lb := intervalIntegral.integral_mono_on (by linarith : (1 / 4 : ℝ) ≤ (f : ℝ))
    (intervalIntegrable_const (μ := volume)) hint_seg fun a ha => (h_pt_bounds a ha).1
  have h_int_ub := intervalIntegral.integral_mono_on (by linarith : (1 / 4 : ℝ) ≤ (f : ℝ))
    hint_seg (intervalIntegrable_const (μ := volume)) fun a ha => (h_pt_bounds a ha).2
  rw [intervalIntegral.integral_const, smul_eq_mul] at h_int_lb h_int_ub
  have h1 : 2 * n1Comb f * (-realLogT x xiStar) ≤ -2 * ∫ a in (1 / 4 : ℝ)..(f : ℝ), realLogT x (chiQuantile c' a) := by
    unfold n1Comb; linarith
  have h2 : -2 * ∫ a in (1 / 4 : ℝ)..(f : ℝ), realLogT x (chiQuantile c' a) ≤
      2 * n1Comb f * (-realLogT x (chiQuantile c' f)) := by
    unfold n1Comb; linarith
  refine ⟨h1, h2, ?_⟩
  have hs_pos : 0 < x - xiStar := sub_pos.mpr hx_xi
  have h_t1 : Real.tanh (π * (x - xiStar) / 2) ≤ π * (x - xiStar) / 2 :=
    tanh_le_of_nonneg (by positivity [Real.pi_pos])
  have h_t1_pos : 0 < Real.tanh (π * (x - xiStar) / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by positivity [Real.pi_pos])) (Real.cosh_pos _)
  have h_t2_pos : 0 < Real.tanh (π * (x + xiStar) / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by positivity [Real.pi_pos, xiStar_pos])) (Real.cosh_pos _)
  have h_t2_le1 : Real.tanh (π * (x + xiStar) / 2) ≤ 1 := by
    simpa [abs_of_pos h_t2_pos] using (abs_tanh_le_one (t := π * (x + xiStar) / 2))
  have h_prod_pos : 0 < Real.tanh (π * (x - xiStar) / 2) * Real.tanh (π * (x + xiStar) / 2) :=
    mul_pos h_t1_pos h_t2_pos
  have h_prod_le : Real.tanh (π * (x - xiStar) / 2) * Real.tanh (π * (x + xiStar) / 2) ≤
      π * (x - xiStar) / 2 := by
    calc Real.tanh (π * (x - xiStar) / 2) * Real.tanh (π * (x + xiStar) / 2)
        ≤ (π * (x - xiStar) / 2) * 1 := mul_le_mul h_t1 h_t2_le1 h_t2_pos.le (by positivity [Real.pi_pos])
      _ = π * (x - xiStar) / 2 := mul_one _
  have h_blaschke_eq : ‖blaschkeT (xiStar : ℂ) (x : ℂ)‖ =
      Real.tanh (π * (x - xiStar) / 2) * Real.tanh (π * (x + xiStar) / 2) := by
    unfold blaschkeT
    have hc1 : Complex.tanh ((π : ℂ) * ((x : ℂ) - (xiStar : ℂ)) / 2) =
        ((Real.tanh (π * (x - xiStar) / 2) : ℝ) : ℂ) := by
      have h1 : Complex.tanh ((π * (x - xiStar) / 2 : ℝ) : ℂ) =
          ((Real.tanh (π * (x - xiStar) / 2) : ℝ) : ℂ) := by
        rw [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
          ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, Complex.ofReal_div]
      rw [← h1]; congr 1; push_cast; ring
    have hc2 : Complex.tanh ((π : ℂ) * ((x : ℂ) + (xiStar : ℂ)) / 2) =
        ((Real.tanh (π * (x + xiStar) / 2) : ℝ) : ℂ) := by
      have h1 : Complex.tanh ((π * (x + xiStar) / 2 : ℝ) : ℂ) =
          ((Real.tanh (π * (x + xiStar) / 2) : ℝ) : ℂ) := by
        rw [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
          ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, Complex.ofReal_div]
      rw [← h1]; congr 1; push_cast; ring
    rw [hc1, hc2, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h_prod_pos]
  have hlog_xi : realLogT x xiStar ≤ -Real.log (2 / (π * (x - xiStar))) := by
    unfold realLogT
    rw [h_blaschke_eq]
    calc Real.log (Real.tanh (π * (x - xiStar) / 2) * Real.tanh (π * (x + xiStar) / 2))
        ≤ Real.log (π * (x - xiStar) / 2) := Real.log_le_log h_prod_pos h_prod_le
      _ = Real.log ((2 / (π * (x - xiStar)))⁻¹) := by congr 1; field_simp [Real.pi_ne_zero, hs_pos.ne']
      _ = -Real.log (2 / (π * (x - xiStar))) := Real.log_inv _
  have hn1_nn : 0 ≤ 2 * n1Comb f := by unfold n1Comb; linarith
  have h_exp_arg : Real.log (2 / (π * (x - xiStar))) * (2 * n1Comb f) ≤
      -2 * ∫ a in (1 / 4 : ℝ)..(f : ℝ), realLogT x (chiQuantile c' a) := by
    have hlog_ge : Real.log (2 / (π * (x - xiStar))) ≤ -realLogT x xiStar := by linarith
    calc Real.log (2 / (π * (x - xiStar))) * (2 * n1Comb f)
        = 2 * n1Comb f * Real.log (2 / (π * (x - xiStar))) := by ring
      _ ≤ 2 * n1Comb f * (-realLogT x xiStar) := mul_le_mul_of_nonneg_left hlog_ge hn1_nn
      _ ≤ -2 * ∫ a in (1 / 4 : ℝ)..(f : ℝ), realLogT x (chiQuantile c' a) := h1
  rw [Real.rpow_def_of_pos (by positivity [Real.pi_pos])]
  exact Real.exp_le_exp.mpr h_exp_arg

/-! ### Section 3: Left curvature error bound `eLeftComb_bounds` -/

private lemma rhoU_le_four_thirds_mul {y : ℝ} (hy : xiStar < y) : rhoU y ≤ (4 / 3 : ℝ) * y := by
  unfold rhoU
  split_ifs with h
  · exact absurd hy (not_lt.mpr h)
  · have hpi := Real.pi_pos
    have hy_pos : 0 < y := xiStar_pos.trans hy
    have hsh_gt1 : 1 < Real.sinh (π * y) := by
      rw [← sinh_pi_mul_xiStar]; exact Real.sinh_lt_sinh.mpr (by nlinarith)
    have hsh_pos : 0 < Real.sinh (π * y) := zero_lt_one.trans hsh_gt1
    have h_arc_le : arccoshR (Real.sinh (π * y)) ≤ π * y := by
      unfold arccoshR
      have hsqrt_le : √(Real.sinh (π * y) ^ 2 - 1) ≤ Real.sinh (π * y) := by
        have hsq : Real.sinh (π * y) ^ 2 - 1 ≤ Real.sinh (π * y) ^ 2 := by linarith
        simpa [Real.sqrt_sq hsh_pos.le] using Real.sqrt_le_sqrt hsq
      have h2sh : 2 * Real.sinh (π * y) ≤ Real.exp (π * y) := by
        have : 2 * Real.sinh (π * y) = Real.exp (π * y) - Real.exp (-(π * y)) := by
          rw [Real.sinh_eq]; ring
        linarith [Real.exp_pos (-(π * y))]
      have hlog := Real.log_le_log (by positivity)
        (by linarith : Real.sinh (π * y) + √(Real.sinh (π * y) ^ 2 - 1) ≤ Real.exp (π * y))
      rwa [Real.log_exp] at hlog
    calc 4 / (3 * π) * arccoshR (Real.sinh (π * y))
        ≤ 4 / (3 * π) * (π * y) := mul_le_mul_of_nonneg_left h_arc_le (by positivity)
      _ = 4 / 3 * y := by field_simp [Real.pi_ne_zero]

private lemma cumulN_le_sq_of_one_le {r : ℝ} (hr : 1 ≤ r) :
    cumulN (xiStar + r) ≤ (2 / 3 : ℝ) * (xiStar + 1) * r ^ 2 := by
  unfold cumulN
  have h_int_le : ∫ t in xiStar..(xiStar + r), rhoU t ≤ r * ((4 / 3 : ℝ) * (xiStar + r)) := by
    have hcont : ContinuousOn rhoU (Icc xiStar (xiStar + r)) :=
      continuousOn_rhoU.mono Set.Icc_subset_Ici_self
    have hm := intervalIntegral.integral_mono_on (g := fun _ => (4 / 3 : ℝ) * (xiStar + r))
      (by linarith : xiStar ≤ xiStar + r)
      (hcont.intervalIntegrable_of_Icc (by linarith)) (intervalIntegrable_const (μ := volume))
      fun t ht => by
        rcases eq_or_lt_of_le ht.1 with rfl | hgt
        · rw [rhoU_xiStar]
          positivity [xiStar_pos]
        · exact (rhoU_le_four_thirds_mul hgt).trans (by nlinarith [ht.2])
    rw [intervalIntegral.integral_const, smul_eq_mul] at hm
    have heq : xiStar + r - xiStar = r := by ring
    rwa [heq] at hm
  calc (1 / 2 : ℝ) * ∫ t in xiStar..(xiStar + r), rhoU t
      ≤ (1 / 2 : ℝ) * (r * ((4 / 3 : ℝ) * (xiStar + r))) := by linarith
    _ = (2 / 3 : ℝ) * r * (xiStar + r) := by ring
    _ ≤ (2 / 3 : ℝ) * r * ((xiStar + 1) * r) := by gcongr; nlinarith [xiStar_pos]
    _ = (2 / 3 : ℝ) * (xiStar + 1) * r ^ 2 := by ring

private lemma sum_Icc_rpow_integral_telescope (k0 N : ℕ) (hk0 : 2 ≤ k0) (hkN : k0 ≤ N)
    {p : ℝ} (hp : 1 < p) :
    (∑ k ∈ Finset.Icc k0 N, ∫ t in ((k : ℝ) - 7 / 4)..((k : ℝ) - 3 / 4), t ^ (-p)) ≤
      ((k0 : ℝ) - 7 / 4) ^ (1 - p) / (p - 1) := by
  have hk2 : (2 : ℝ) ≤ (k0 : ℝ) := by exact_mod_cast hk0
  have h_tele : ∀ M ≥ k0,
      (∑ k ∈ Finset.Icc k0 M, ∫ t in ((k : ℝ) - 7 / 4)..((k : ℝ) - 3 / 4), t ^ (-p)) =
        ∫ t in ((k0 : ℝ) - 7 / 4)..((M : ℝ) - 3 / 4), t ^ (-p) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp [Finset.Icc_self]
    | succ M hM ih =>
      have hsub : Finset.Icc k0 (M + 1) = insert (M + 1) (Finset.Icc k0 M) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsub, Finset.sum_insert (by simp), ih, add_comm]
      have hk0M_nat : (k0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      have hM1 : ((M : ℝ) - 3 / 4) ≤ ((M + 1 : ℕ) : ℝ) - 3 / 4 := by push_cast; linarith
      have hk0M : ((k0 : ℝ) - 7 / 4) ≤ ((M : ℝ) - 3 / 4) := by linarith
      have hcont : ContinuousOn (fun t : ℝ => t ^ (-p))
          (Icc ((k0 : ℝ) - 7 / 4) (((M + 1 : ℕ) : ℝ) - 3 / 4)) :=
        ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl (by linarith [ht.1])
      have hi1 : IntervalIntegrable (fun t : ℝ => t ^ (-p)) volume ((k0 : ℝ) - 7 / 4) ((M : ℝ) - 3 / 4) :=
        (hcont.mono (Icc_subset_Icc_right hM1)).intervalIntegrable_of_Icc hk0M
      have h_eq_lim : ((M + 1 : ℕ) : ℝ) - 7 / 4 = (M : ℝ) - 3 / 4 := by push_cast; ring
      have hi2 : IntervalIntegrable (fun t : ℝ => t ^ (-p)) volume
          ((M : ℝ) - 3 / 4) (((M + 1 : ℕ) : ℝ) - 3 / 4) :=
        (hcont.mono (Icc_subset_Icc_left hk0M)).intervalIntegrable_of_Icc hM1
      rw [h_eq_lim]
      exact intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  rw [h_tele N hkN]
  have hk0N : (k0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkN
  have ha_pos : 0 < (k0 : ℝ) - 7 / 4 := by linarith
  have hb_pos : 0 < (N : ℝ) - 3 / 4 := by linarith
  have hab : (k0 : ℝ) - 7 / 4 ≤ (N : ℝ) - 3 / 4 := by linarith
  have hd : ∀ t ∈ uIcc ((k0 : ℝ) - 7 / 4) ((N : ℝ) - 3 / 4),
      HasDerivAt (fun s : ℝ => s ^ (1 - p) / (1 - p)) (t ^ (-p)) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht_pos : 0 < t := ha_pos.trans_le ht.1
    have hrp := (Real.hasDerivAt_rpow_const (p := 1 - p) (Or.inl ht_pos.ne')).div_const (1 - p)
    refine hrp.congr_deriv ?_
    have hp_ne : 1 - p ≠ 0 := by linarith
    have heq : 1 - p - 1 = -p := by ring
    rw [heq]; field_simp [hp_ne]
  have hint : IntervalIntegrable (fun t : ℝ => t ^ (-p)) volume ((k0 : ℝ) - 7 / 4) ((N : ℝ) - 3 / 4) :=
    (ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl (ha_pos.trans_le ht.1).ne').intervalIntegrable_of_Icc hab
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  have hnb_nn : 0 ≤ ((N : ℝ) - 3 / 4) ^ (1 - p) := Real.rpow_nonneg hb_pos.le _
  have hneg : ((N : ℝ) - 3 / 4) ^ (1 - p) / (1 - p) ≤ 0 :=
    div_nonpos_of_nonneg_of_nonpos hnb_nn (by linarith)
  have h_eq : -(((k0 : ℝ) - 7 / 4) ^ (1 - p) / (1 - p)) =
      ((k0 : ℝ) - 7 / 4) ^ (1 - p) / (p - 1) := by
    have hp_ne : 1 - p ≠ 0 := by linarith
    have hp_ne2 : p - 1 ≠ 0 := by linarith
    field_simp [hp_ne, hp_ne2]; ring
  linarith

private lemma sum_filter_rpow_inv_le (S : Finset ℕ) (hS : ∀ k ∈ S, 2 ≤ k) {p A : ℝ}
    (hp : 1 < p) (hA : 0 < A) (hA_le : ∀ k ∈ S, A ≤ (k : ℝ) - 7 / 4) :
    ∑ k ∈ S, ((k : ℝ) - 3 / 4) ^ (-p) ≤ A ^ (1 - p) / (p - 1) := by
  classical
  by_cases hne : S.Nonempty
  · let k0 := S.min' hne
    let N := S.max' hne
    have hk0_mem : k0 ∈ S := Finset.min'_mem S hne
    have hk0_ge2 : 2 ≤ k0 := hS k0 hk0_mem
    have hk0_le_N : k0 ≤ N := Finset.min'_le S N (Finset.max'_mem S hne)
    have hsub : S ⊆ Finset.Icc k0 N := fun k hk =>
      Finset.mem_Icc.mpr ⟨Finset.min'_le S k hk, Finset.le_max' S k hk⟩
    have hA_k0 : A ≤ (k0 : ℝ) - 7 / 4 := hA_le k0 hk0_mem
    have hrpow_le : ((k0 : ℝ) - 7 / 4) ^ (1 - p) ≤ A ^ (1 - p) :=
      Real.rpow_le_rpow_of_nonpos hA hA_k0 (by linarith)
    calc ∑ k ∈ S, ((k : ℝ) - 3 / 4) ^ (-p)
        ≤ ∑ k ∈ S, ∫ t in ((k : ℝ) - 7 / 4)..((k : ℝ) - 3 / 4), t ^ (-p) := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hkA : A ≤ (k : ℝ) - 7 / 4 := hA_le k hk
            have hcont : ContinuousOn (fun t : ℝ => t ^ (-p)) (Icc ((k : ℝ) - 7 / 4) ((k : ℝ) - 3 / 4)) :=
              ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl (by linarith [ht.1, hkA])
            have hm := intervalIntegral.integral_mono_on (by linarith : (k : ℝ) - 7 / 4 ≤ (k : ℝ) - 3 / 4)
              (intervalIntegrable_const (μ := volume)) (hcont.intervalIntegrable_of_Icc (by linarith))
              fun t ht => Real.rpow_le_rpow_of_nonpos (by linarith [ht.1, hkA]) ht.2 (by linarith)
            rw [intervalIntegral.integral_const, smul_eq_mul] at hm
            linarith
      _ ≤ ∑ k ∈ Finset.Icc k0 N, ∫ t in ((k : ℝ) - 7 / 4)..((k : ℝ) - 3 / 4), t ^ (-p) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun k hk _ => ?_
            have hk_ge : (k0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).1
            exact intervalIntegral.integral_nonneg (by linarith) fun t ht =>
              Real.rpow_nonneg (by linarith [ht.1, hA_k0]) _
      _ ≤ ((k0 : ℝ) - 7 / 4) ^ (1 - p) / (p - 1) := sum_Icc_rpow_integral_telescope k0 N hk0_ge2 hk0_le_N hp
      _ ≤ A ^ (1 - p) / (p - 1) := by gcongr
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
    exact div_nonneg (Real.rpow_nonneg hA.le _) (by linarith)

/-- Left-curvature error bound (`comb_estimates.tex`, line 172):
$\exists C_L > 0,\ \forall^\infty c',\ 0 \le \mathcal{E}_{\mathrm{left}}^{(f,n,j)}(x) \le \frac{C_L \lambda(c')}{x - \xi_*}$. -/
theorem eLeftComb_bounds :
    ∃ C_L > 0, ∀ᶠ c' in atTop, ∀ (f n j : ℕ) (x : ℝ),
      1 ≤ f → xiStar < x →
        0 ≤ eLeftComb c' f n j x ∧ eLeftComb c' f n j x ≤ C_L * lambdaComb c' / (x - xiStar) := by
  let C1 : ℝ := (2 / 3 * (1 + c1K0) ^ (1 / 3 : ℝ)) ^ 2 / (1 + c1K0) ^ (-(2 / 3 : ℝ)) *
    ((1 / 4 : ℝ) ^ (-(1 / 3 : ℝ)) / (1 / 3 : ℝ))
  let C_N : ℝ := (2 / 3 : ℝ) * (xiStar + 1)
  let C2 : ℝ := (9 / 4 : ℝ) * C_N ^ (3 / 2 : ℝ) * (2 * 2 ^ (1 / 2 : ℝ) * kTip ^ (1 / 2 : ℝ))
  let C_L : ℝ := (1 / 6 : ℝ) * (C1 + C2) + 1
  have hc1k0_pos : 0 < 1 + c1K0 := by unfold c1K0; positivity
  have hC1_nn : 0 ≤ C1 := by dsimp [C1]; positivity
  have hC2_nn : 0 ≤ C2 := by dsimp [C2, C_N]; positivity [xiStar_pos, kTip_pos]
  have hCL_pos : 0 < C_L := by dsimp [C_L]; linarith
  refine ⟨C_L, hCL_pos, ?_⟩
  have h_large : ∀ᶠ c' : ℝ in atTop, max 1 (2 / kTip) ≤ c' ∧ kTip * c' ≥ 1 := by
    refine (eventually_ge_atTop _).and ?_
    exact (tendsto_const_nhds.pos_mul_atTop kTip_pos tendsto_id).eventually_ge_atTop 1
  filter_upwards [h_large] with c' ⟨hc'_ge, hkc_ge⟩
  have hc' : 0 < c' := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans hc'_ge)
  intro f n j x _hf hx
  have hs_pos : 0 < x - xiStar := sub_pos.mpr hx
  have h_cell_nn : ∀ k ∈ Finset.Icc (f + 1) (n - j), 0 ≤ eLeftCell c' x k := fun k hk => by
    have hk2 : 2 ≤ k := by have := (Finset.mem_Icc.mp hk).1; omega
    have hk2_r : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    have hk14 : 1 / 4 < (k : ℝ) - 1 / 2 := by linarith
    have hr_pos : 0 < siteRadius c' ((k : ℝ) - 1 / 2) := sub_pos.mpr (xiStar_lt_chiQuantile hc' hk14)
    unfold eLeftCell; positivity
  refine ⟨Finset.sum_nonneg h_cell_nn, ?_⟩
  let S : Finset ℕ := Finset.Icc (f + 1) (n - j)
  let S1 : Finset ℕ := S.filter (fun k : ℕ => siteRadius c' ((k : ℝ) - 1 / 2) ≤ 1)
  let S2 : Finset ℕ := S.filter (fun k : ℕ => 1 < siteRadius c' ((k : ℝ) - 1 / 2))
  have hS_ge2 : ∀ k ∈ S, 2 ≤ k := fun k hk => by have := (Finset.mem_Icc.mp hk).1; omega
  have hsplit : (∑ k ∈ S, chiDeriv c' ((k : ℝ) - 1 / 2) ^ 2 / siteRadius c' ((k : ℝ) - 1 / 2)) =
      (∑ k ∈ S1, chiDeriv c' ((k : ℝ) - 1 / 2) ^ 2 / siteRadius c' ((k : ℝ) - 1 / 2)) +
        ∑ k ∈ S2, chiDeriv c' ((k : ℝ) - 1 / 2) ^ 2 / siteRadius c' ((k : ℝ) - 1 / 2) := by
    have h := Finset.sum_filter_add_sum_filter_not S (fun k : ℕ => siteRadius c' ((k : ℝ) - 1 / 2) ≤ 1)
      (fun k : ℕ => chiDeriv c' ((k : ℝ) - 1 / 2) ^ 2 / siteRadius c' ((k : ℝ) - 1 / 2))
    simpa [S1, S2, not_le] using h.symm
  have hlam_pos : 0 < lambdaComb c' := by unfold lambdaComb; positivity [kTip_pos]
  have h1_term : ∀ k ∈ S1,
      chiDeriv c' ((k : ℝ) - 1 / 2) ^ 2 / siteRadius c' ((k : ℝ) - 1 / 2) ≤
        ((2 / 3 * (1 + c1K0) ^ (1 / 3 : ℝ)) ^ 2 / (1 + c1K0) ^ (-(2 / 3 : ℝ))) *
          lambdaComb c' * ((k : ℝ) - 3 / 4) ^ (-(4 / 3 : ℝ)) := by
    intro k hk
    have hkS := (Finset.mem_filter.mp hk).1
    have hr1 := (Finset.mem_filter.mp hk).2
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hS_ge2 k hkS
    have ha14 : 1 / 4 < (k : ℝ) - 1 / 2 := by linarith
    obtain ⟨hr_lb, hcd_ub⟩ := siteRadius_le_one_bounds hc' ha14 hr1
    have ha_sub_pos : 0 < (k : ℝ) - 3 / 4 := by linarith
    have hphi_eq : phiQuantile ((k : ℝ) - 1 / 2) = ((k : ℝ) - 3 / 4) ^ (2 / 3 : ℝ) := by
      unfold phiQuantile; ring_nf
    have hcd_eq : ((k : ℝ) - 1 / 2 - 1 / 4) ^ (-(1 / 3 : ℝ)) = ((k : ℝ) - 3 / 4) ^ (-(1 / 3 : ℝ)) := by
      ring_nf
    rw [hphi_eq] at hr_lb; rw [hcd_eq] at hcd_ub
    have h_num_sq : chiDeriv c' ((k : ℝ) - 1 / 2) ^ 2 ≤
        (2 / 3 * (1 + c1K0) ^ (1 / 3 : ℝ)) ^ 2 * lambdaComb c' ^ 2 *
          (((k : ℝ) - 3 / 4) ^ (-(1 / 3 : ℝ))) ^ 2 := by
      have hsq := pow_le_pow_left₀ (chiDeriv_pos hc' ha14).le hcd_ub 2
      refine hsq.trans_eq ?_; ring
    have h_den_lb : 0 < (1 + c1K0) ^ (-(2 / 3 : ℝ)) * (lambdaComb c' * ((k : ℝ) - 3 / 4) ^ (2 / 3 : ℝ)) := by
      positivity
    calc chiDeriv c' ((k : ℝ) - 1 / 2) ^ 2 / siteRadius c' ((k : ℝ) - 1 / 2)
        ≤ ((2 / 3 * (1 + c1K0) ^ (1 / 3 : ℝ)) ^ 2 * lambdaComb c' ^ 2 *
            (((k : ℝ) - 3 / 4) ^ (-(1 / 3 : ℝ))) ^ 2) /
            ((1 + c1K0) ^ (-(2 / 3 : ℝ)) * (lambdaComb c' * ((k : ℝ) - 3 / 4) ^ (2 / 3 : ℝ))) :=
            div_le_div₀ (by positivity) h_num_sq h_den_lb hr_lb
      _ = ((2 / 3 * (1 + c1K0) ^ (1 / 3 : ℝ)) ^ 2 / (1 + c1K0) ^ (-(2 / 3 : ℝ))) *
            lambdaComb c' * ((((k : ℝ) - 3 / 4) ^ (-(1 / 3 : ℝ))) ^ 2 / ((k : ℝ) - 3 / 4) ^ (2 / 3 : ℝ)) := by
            field_simp [hlam_pos.ne']
      _ = ((2 / 3 * (1 + c1K0) ^ (1 / 3 : ℝ)) ^ 2 / (1 + c1K0) ^ (-(2 / 3 : ℝ))) *
            lambdaComb c' * ((k : ℝ) - 3 / 4) ^ (-(4 / 3 : ℝ)) := by
            congr 1
            rw [← Real.rpow_natCast (((k : ℝ) - 3 / 4) ^ (-(1 / 3 : ℝ))) 2,
              ← Real.rpow_mul ha_sub_pos.le, ← Real.rpow_sub ha_sub_pos]
            norm_num
  have hS1_sum : ∑ k ∈ S1, chiDeriv c' ((k : ℝ) - 1 / 2) ^ 2 / siteRadius c' ((k : ℝ) - 1 / 2) ≤
      C1 * lambdaComb c' := by
    have hs_le := Finset.sum_le_sum h1_term
    rw [← Finset.mul_sum] at hs_le
    have h_int_bd := sum_filter_rpow_inv_le S1 (fun k hk => hS_ge2 k (Finset.mem_filter.mp hk).1)
      (p := 4 / 3) (A := 1 / 4) (by norm_num) (by norm_num) fun k hk => by
        have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hS_ge2 k (Finset.mem_filter.mp hk).1
        linarith
    have h_int_bd' : ∑ k ∈ S1, ((k : ℝ) - 3 / 4) ^ (-(4 / 3 : ℝ)) ≤
        (1 / 4 : ℝ) ^ (-(1 / 3 : ℝ)) / (1 / 3 : ℝ) := by
      simpa [show (1 : ℝ) - 4 / 3 = -(1 / 3 : ℝ) by norm_num,
        show (4 / 3 : ℝ) - 1 = 1 / 3 by norm_num] using h_int_bd
    calc ∑ k ∈ S1, chiDeriv c' ((k : ℝ) - 1 / 2) ^ 2 / siteRadius c' ((k : ℝ) - 1 / 2)
        ≤ ((2 / 3 * (1 + c1K0) ^ (1 / 3 : ℝ)) ^ 2 / (1 + c1K0) ^ (-(2 / 3 : ℝ))) *
            lambdaComb c' * ∑ k ∈ S1, ((k : ℝ) - 3 / 4) ^ (-(4 / 3 : ℝ)) := hs_le
      _ ≤ ((2 / 3 * (1 + c1K0) ^ (1 / 3 : ℝ)) ^ 2 / (1 + c1K0) ^ (-(2 / 3 : ℝ))) *
            lambdaComb c' * ((1 / 4 : ℝ) ^ (-(1 / 3 : ℝ)) / (1 / 3 : ℝ)) := by
            gcongr
      _ = C1 * lambdaComb c' := by dsimp [C1]; ring
  have h2_k_lb : ∀ k ∈ S2, kTip * c' ≤ (k : ℝ) - 3 / 4 := fun k hk => by
    have hkS := (Finset.mem_filter.mp hk).1
    have hr1 : 1 < siteRadius c' ((k : ℝ) - 1 / 2) := (Finset.mem_filter.mp hk).2
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hS_ge2 k hkS
    have ha14 : 1 / 4 ≤ (k : ℝ) - 1 / 2 := by linarith
    have hspec := chiQuantile_spec hc' ha14
    have hχ_gt : xiStar + 1 < chiQuantile c' ((k : ℝ) - 1 / 2) := by
      unfold siteRadius at hr1; linarith
    have hcum_le := (cumulN_strictMonoOn.le_iff_le (by linarith : xiStar ≤ xiStar + 1) hspec.1).mpr hχ_gt.le
    have hcum1 : kTip ≤ cumulN (xiStar + 1) := by simpa using (cumulN_bounds zero_le_one).1
    have h_eq : c' * cumulN (chiQuantile c' ((k : ℝ) - 1 / 2)) = (k : ℝ) - 3 / 4 := by
      have := hspec.2; linarith
    calc kTip * c' = c' * kTip := mul_comm _ _
      _ ≤ c' * cumulN (xiStar + 1) := mul_le_mul_of_nonneg_left hcum1 hc'.le
      _ ≤ c' * cumulN (chiQuantile c' ((k : ℝ) - 1 / 2)) := mul_le_mul_of_nonneg_left hcum_le hc'.le
      _ = (k : ℝ) - 3 / 4 := h_eq
  have h2_term : ∀ k ∈ S2,
      chiDeriv c' ((k : ℝ) - 1 / 2) ^ 2 / siteRadius c' ((k : ℝ) - 1 / 2) ≤
        (9 / 4 : ℝ) * C_N ^ (3 / 2 : ℝ) * c' ^ (-(1 / 2 : ℝ)) *
          ((k : ℝ) - 3 / 4) ^ (-(3 / 2 : ℝ)) := by
    intro k hk
    have hkS := (Finset.mem_filter.mp hk).1
    have hr1 : 1 < siteRadius c' ((k : ℝ) - 1 / 2) := (Finset.mem_filter.mp hk).2
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hS_ge2 k hkS
    have ha14 : 1 / 4 < (k : ℝ) - 1 / 2 := by linarith
    have hspec := chiQuantile_spec hc' ha14.le
    set r := siteRadius c' ((k : ℝ) - 1 / 2)
    have hr_ge : 1 ≤ r := hr1.le
    have hr_nn : 0 ≤ r := zero_le_one.trans hr_ge
    have hχ_eq : xiStar + r = chiQuantile c' ((k : ℝ) - 1 / 2) := by dsimp [r, siteRadius]; ring
    have hρ_lb : (4 / 3 : ℝ) * r ≤ rhoU (chiQuantile c' ((k : ℝ) - 1 / 2)) := by
      rw [← hχ_eq]
      exact (le_max_right _ _).trans (rhoU_ge_max hr_nn)
    have hcd_ub : chiDeriv c' ((k : ℝ) - 1 / 2) ≤ (3 / 2 : ℝ) / (c' * r) := by
      unfold chiDeriv
      have hden : 0 < c' * ((4 / 3 : ℝ) * r) := by positivity
      calc 2 / (c' * rhoU (chiQuantile c' ((k : ℝ) - 1 / 2)))
          ≤ 2 / (c' * ((4 / 3 : ℝ) * r)) := div_le_div_of_nonneg_left two_pos.le hden
            (mul_le_mul_of_nonneg_left hρ_lb hc'.le)
        _ = (3 / 2 : ℝ) / (c' * r) := by ring
    have hCN_val_pos : 0 < C_N := mul_pos (by norm_num) (by linarith [xiStar_pos])
    have hCN_nn : 0 ≤ C_N := hCN_val_pos.le
    have hr_lb_N : (k : ℝ) - 3 / 4 ≤ c' * C_N * r ^ 2 := by
      have h_eq : (k : ℝ) - 3 / 4 = c' * cumulN (xiStar + r) := by
        rw [hχ_eq, hspec.2]; ring
      rw [h_eq]
      exact (mul_le_mul_of_nonneg_left (cumulN_le_sq_of_one_le hr_ge) hc'.le).trans_eq
        (by dsimp [C_N]; ring)
    have h_cube_lb : (((k : ℝ) - 3 / 4) / (c' * C_N)) ^ (3 / 2 : ℝ) ≤ r ^ 3 := by
      have hCN_pos : 0 < c' * C_N := mul_pos hc' hCN_val_pos
      have hk34_nn : 0 ≤ (k : ℝ) - 3 / 4 := by linarith
      have hsq : ((k : ℝ) - 3 / 4) / (c' * C_N) ≤ r ^ 2 := by
        rw [div_le_iff₀ hCN_pos]; linarith
      have hpow := Real.rpow_le_rpow (div_nonneg hk34_nn hCN_pos.le) hsq (by norm_num : (0 : ℝ) ≤ 3 / 2)
      refine hpow.trans_eq ?_
      rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr_nn]
      norm_num
    have hcd_pos := chiDeriv_pos hc' ha14
    have h_cubed : chiDeriv c' ((k : ℝ) - 1 / 2) ^ 2 / r ≤ (9 / 4 : ℝ) / (c' ^ 2 * r ^ 3) := by
      have hsq := pow_le_pow_left₀ hcd_pos.le hcd_ub 2
      have hr_pos : 0 < r := zero_lt_one.trans_le hr_ge
      calc chiDeriv c' ((k : ℝ) - 1 / 2) ^ 2 / r
          ≤ ((3 / 2 : ℝ) / (c' * r)) ^ 2 / r := by gcongr
        _ = (9 / 4 : ℝ) / (c' ^ 2 * r ^ 3) := by
            field_simp [hc'.ne', hr_pos.ne']; ring
    have h_inv_r3 : 1 / r ^ 3 ≤ (c' * C_N) ^ (3 / 2 : ℝ) * ((k : ℝ) - 3 / 4) ^ (-(3 / 2 : ℝ)) := by
      have hk34_pos : 0 < (k : ℝ) - 3 / 4 := by linarith
      have hCN_pos : 0 < c' * C_N := mul_pos hc' hCN_val_pos
      have hdiv : 1 / r ^ 3 ≤ 1 / (((k : ℝ) - 3 / 4) / (c' * C_N)) ^ (3 / 2 : ℝ) :=
        one_div_le_one_div_of_le (by positivity) h_cube_lb
      refine hdiv.trans_eq ?_
      rw [Real.div_rpow hk34_pos.le hCN_pos.le, Real.rpow_neg hk34_pos.le]
      field_simp [hk34_pos.ne']
    calc chiDeriv c' ((k : ℝ) - 1 / 2) ^ 2 / r
        ≤ (9 / 4 : ℝ) / c' ^ 2 * (1 / r ^ 3) := by
            linarith [show (9 / 4 : ℝ) / (c' ^ 2 * r ^ 3) = (9 / 4 : ℝ) / c' ^ 2 * (1 / r ^ 3) by ring]
      _ ≤ (9 / 4 : ℝ) / c' ^ 2 * ((c' * C_N) ^ (3 / 2 : ℝ) * ((k : ℝ) - 3 / 4) ^ (-(3 / 2 : ℝ))) := by
          gcongr
      _ = (9 / 4 : ℝ) * C_N ^ (3 / 2 : ℝ) * (c' ^ (3 / 2 : ℝ) / c' ^ 2) * ((k : ℝ) - 3 / 4) ^ (-(3 / 2 : ℝ)) := by
          rw [Real.mul_rpow hc'.le hCN_nn]; ring
      _ = (9 / 4 : ℝ) * C_N ^ (3 / 2 : ℝ) * c' ^ (-(1 / 2 : ℝ)) * ((k : ℝ) - 3 / 4) ^ (-(3 / 2 : ℝ)) := by
          congr 2; rw [← Real.rpow_natCast c' 2, ← Real.rpow_sub hc']; norm_num
  have hS2_sum : ∑ k ∈ S2, chiDeriv c' ((k : ℝ) - 1 / 2) ^ 2 / siteRadius c' ((k : ℝ) - 1 / 2) ≤
      C2 * lambdaComb c' := by
    have hs_le := Finset.sum_le_sum h2_term
    rw [← Finset.mul_sum] at hs_le
    have h_A : ∀ k ∈ S2, kTip * c' / 2 ≤ (k : ℝ) - 7 / 4 := fun k hk => by
      have hk_lb := h2_k_lb k hk
      have hkc2 : 2 ≤ kTip * c' := by
        calc (2 : ℝ) = kTip * (2 / kTip) := by field_simp [kTip_pos.ne']
          _ ≤ kTip * c' := mul_le_mul_of_nonneg_left ((le_max_right 1 _).trans hc'_ge) kTip_pos.le
      linarith
    have h_int_bd := sum_filter_rpow_inv_le S2 (fun k hk => hS_ge2 k (Finset.mem_filter.mp hk).1)
      (p := 3 / 2) (A := kTip * c' / 2) (by norm_num) (by positivity [kTip_pos]) h_A
    have h_pow_c : c' ^ (-(1 / 2 : ℝ)) * ((kTip * c' / 2) ^ (1 - (3 / 2 : ℝ)) / (3 / 2 - 1 : ℝ)) =
        (2 * 2 ^ (1 / 2 : ℝ) / kTip ^ (1 / 2 : ℝ)) * (1 / c') := by
      have h_eq : (kTip * c' / 2) ^ (1 - (3 / 2 : ℝ)) =
          2 ^ (1 / 2 : ℝ) * kTip ^ (-(1 / 2 : ℝ)) * c' ^ (-(1 / 2 : ℝ)) := by
        rw [show (1 - (3 / 2 : ℝ)) = -(1 / 2 : ℝ) by norm_num]
        rw [Real.div_rpow (mul_nonneg kTip_pos.le hc'.le) zero_le_two,
          Real.mul_rpow kTip_pos.le hc'.le,
          Real.rpow_neg kTip_pos.le, Real.rpow_neg hc'.le,
          Real.rpow_neg zero_le_two, div_eq_mul_inv, inv_inv]
        ring
      rw [h_eq]
      have hcc : c' ^ (-(1 / 2 : ℝ)) * c' ^ (-(1 / 2 : ℝ)) = 1 / c' := by
        rw [← Real.rpow_add hc', show -(1 / 2 : ℝ) + -(1 / 2 : ℝ) = -1 by norm_num,
          Real.rpow_neg_one, one_div]
      have hkt : kTip ^ (-(1 / 2 : ℝ)) = 1 / kTip ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_neg kTip_pos.le, inv_eq_one_div]
      calc c' ^ (-(1 / 2 : ℝ)) *
            (2 ^ (1 / 2 : ℝ) * kTip ^ (-(1 / 2 : ℝ)) * c' ^ (-(1 / 2 : ℝ)) / (3 / 2 - 1 : ℝ))
          = 2 * 2 ^ (1 / 2 : ℝ) * kTip ^ (-(1 / 2 : ℝ)) *
              (c' ^ (-(1 / 2 : ℝ)) * c' ^ (-(1 / 2 : ℝ))) := by ring
        _ = (2 * 2 ^ (1 / 2 : ℝ) / kTip ^ (1 / 2 : ℝ)) * (1 / c') := by rw [hcc, hkt]; ring
    have hk_le : 1 / c' ≤ kTip * lambdaComb c' := by
      unfold lambdaComb
      have hpow := Real.rpow_le_rpow_of_exponent_le hkc_ge
        (show -(1 : ℝ) ≤ -(2 / 3 : ℝ) by norm_num)
      rw [Real.rpow_neg_one] at hpow
      calc 1 / c' = kTip * (kTip * c')⁻¹ := by field_simp [kTip_pos.ne', hc'.ne']
        _ ≤ kTip * (kTip * c') ^ (-(2 / 3 : ℝ)) := mul_le_mul_of_nonneg_left hpow kTip_pos.le
    have hCN_nn : 0 ≤ C_N := mul_nonneg (by norm_num) (by linarith [xiStar_pos])
    have hcoef_nn : 0 ≤ (9 / 4 : ℝ) * C_N ^ (3 / 2 : ℝ) * c' ^ (-(1 / 2 : ℝ)) := by positivity
    calc ∑ k ∈ S2, chiDeriv c' ((k : ℝ) - 1 / 2) ^ 2 / siteRadius c' ((k : ℝ) - 1 / 2)
        ≤ (9 / 4 : ℝ) * C_N ^ (3 / 2 : ℝ) * c' ^ (-(1 / 2 : ℝ)) *
            ∑ k ∈ S2, ((k : ℝ) - 3 / 4) ^ (-(3 / 2 : ℝ)) := hs_le
      _ ≤ (9 / 4 : ℝ) * C_N ^ (3 / 2 : ℝ) *
            (c' ^ (-(1 / 2 : ℝ)) * ((kTip * c' / 2) ^ (1 - (3 / 2 : ℝ)) / (3 / 2 - 1 : ℝ))) := by
          nlinarith [mul_le_mul_of_nonneg_left h_int_bd hcoef_nn]
      _ = (9 / 4 : ℝ) * C_N ^ (3 / 2 : ℝ) * (2 * 2 ^ (1 / 2 : ℝ) / kTip ^ (1 / 2 : ℝ)) * (1 / c') := by
          rw [h_pow_c]; ring
      _ ≤ (9 / 4 : ℝ) * C_N ^ (3 / 2 : ℝ) * (2 * 2 ^ (1 / 2 : ℝ) / kTip ^ (1 / 2 : ℝ)) *
            (kTip * lambdaComb c') := by
          have hkt_nn : 0 ≤ (9 / 4 : ℝ) * C_N ^ (3 / 2 : ℝ) * (2 * 2 ^ (1 / 2 : ℝ) / kTip ^ (1 / 2 : ℝ)) := by
            positivity [kTip_pos]
          exact mul_le_mul_of_nonneg_left hk_le hkt_nn
      _ = C2 * lambdaComb c' := by
          have hsq : kTip / kTip ^ (1 / 2 : ℝ) = kTip ^ (1 / 2 : ℝ) := by
            have hk12_pos : 0 < kTip ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos kTip_pos _
            rw [div_eq_iff hk12_pos.ne', ← Real.rpow_add kTip_pos]
            norm_num
          calc (9 / 4 : ℝ) * C_N ^ (3 / 2 : ℝ) * (2 * 2 ^ (1 / 2 : ℝ) / kTip ^ (1 / 2 : ℝ)) * (kTip * lambdaComb c')
              = (9 / 4 : ℝ) * C_N ^ (3 / 2 : ℝ) * (2 * 2 ^ (1 / 2 : ℝ) * (kTip / kTip ^ (1 / 2 : ℝ))) * lambdaComb c' := by ring
            _ = C2 * lambdaComb c' := by rw [hsq]
  have hsum_cells : ∑ k ∈ S, chiDeriv c' ((k : ℝ) - 1 / 2) ^ 2 / siteRadius c' ((k : ℝ) - 1 / 2) ≤
      (C1 + C2) * lambdaComb c' := by
    rw [hsplit]; linarith
  calc eLeftComb c' f n j x
      = (1 / 6 : ℝ) / (x - xiStar) *
          ∑ k ∈ S, chiDeriv c' ((k : ℝ) - 1 / 2) ^ 2 / siteRadius c' ((k : ℝ) - 1 / 2) := by
          unfold eLeftComb eLeftCell
          rw [← Finset.mul_sum]
          congr 1; ring
    _ ≤ (1 / 6 : ℝ) / (x - xiStar) * ((C1 + C2) * lambdaComb c') := by gcongr
    _ = ((1 / 6 : ℝ) * (C1 + C2)) * lambdaComb c' / (x - xiStar) := by ring
    _ ≤ C_L * lambdaComb c' / (x - xiStar) := by
        gcongr; dsimp [C_L]; linarith

/-! ### Section 4: Unconditional `lambdaHole` and lower bound `hole_lower_K4` -/

private lemma chiQuantile_nat_zero (c' : ℝ) : chiQuantile c' ((0 : ℕ) : ℝ) = xiStar := by
  unfold chiQuantile
  split_ifs with h
  · exact absurd h.2 (by norm_num)
  · rfl

private lemma refComb_eq_zero_at_zero_node {c' x : ℝ} (hc' : 0 < c') {f n : ℕ}
    (hf : 1 ≤ f) (hn : f + 1 ≤ n) (hx_eq : x = chiQuantile c' n) :
    refComb c' f 0 (x : ℂ) = 0 := by
  let χ := fun m : ℕ => chiQuantile c' (f + 1 + m : ℕ)
  let ε := fun _ : ℕ => (0 : ℝ)
  let P : ℕ → ℂ := fun m =>
    blaschkeT ((χ m : ℂ) + (ε m : ℂ) * Complex.I) (x : ℂ) *
      blaschkeT ((χ m : ℂ) - (ε m : ℂ) * Complex.I) (x : ℂ)
  have hχ_nn : ∀ m : ℕ, 0 ≤ χ m := fun m => by
    have hm1 : (1 : ℝ) ≤ ((f + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ f + 1 + m)
    exact xiStar_pos.le.trans (chiQuantile_spec hc' (by linarith)).1
  have hε_bd : ∀ m : ℕ, |ε m| ≤ 1 / 8 := fun m => by simp [ε]
  have hsum := summable_exp_neg_pi_chiQuantile hc' f
  have hhasProd := (comb_pairProd_hasProdLocallyUniformlyOn χ ε hχ_nn hε_bd hsum).hasProd
    (by simp : (x : ℂ) ∈ {b : ℂ | |b.im| < 7 / 8})
  have hm0_zero : P (n - (f + 1)) = 0 := by
    have hidx : f + 1 + (n - (f + 1)) = n := by omega
    have hχ_eq : χ (n - (f + 1)) = x := by dsimp [χ]; rw [hidx, hx_eq]
    simp [P, ε, hχ_eq, blaschkeT]
  have htprod0 : (∏' m : ℕ, P m) = 0 := by
    have h_ev : ∀ᶠ s : Finset ℕ in atTop, ∏ m ∈ s, P m = 0 := by
      rw [Filter.eventually_atTop]
      exact ⟨{n - (f + 1)}, fun s hs => Finset.prod_eq_zero (hs (Finset.mem_singleton_self _)) hm0_zero⟩
    exact tendsto_nhds_unique hhasProd (tendsto_const_nhds.congr' (h_ev.mono fun s hs => hs.symm))
  unfold refComb
  have htprod_eq : (∏' m : ℕ,
      blaschkeT (↑(chiQuantile c' ↑(f + 1 + m)) + ↑(0 * siteGap c' (f + 1 + m)) * Complex.I) ↑x *
        blaschkeT (↑(chiQuantile c' ↑(f + 1 + m)) - ↑(0 * siteGap c' (f + 1 + m)) * Complex.I) ↑x) =
      ∏' m : ℕ, P m := by
    refine tprod_congr fun m => ?_
    simp [P, χ, ε]
  rw [htprod_eq, htprod0, mul_zero]

private lemma pairModQ_pos_of_ne {c' η₀ x : ℝ} (hc' : 0 < c') (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4)
    (hgap : siteGap c' 1 ≤ 1 / 2) {n k : ℕ} (hk : 1 ≤ k) (hx : inCell c' n x) (hne_idx : k ≠ n) :
    0 < pairModQ c' η₀ x k := by
  by_cases hx_eq : x = chiQuantile c' n
  · subst hx_eq
    unfold pairModQ; rw [blaschkePairQ_eq]
    have hgk : siteGap c' k ≤ siteGap c' 1 := by
      rcases eq_or_lt_of_le hk with rfl | hgt
      · exact le_rfl
      · have hanti := (siteGap_strictAnti hc').antitone (show 0 ≤ k - 1 by omega)
        have heq : (k - 1) + 1 = k := by omega
        simpa [heq] using hanti
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hgk_pos : 0 < siteGap c' k := by
      unfold siteGap
      exact sub_pos.mpr (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith))
        (Set.mem_Ici.mpr (by linarith)) (by linarith))
    have hε_nn : 0 ≤ η₀ * siteGap c' k := mul_nonneg hη₀0 hgk_pos.le
    have hε_le : η₀ * siteGap c' k ≤ 1 / 8 := by nlinarith
    have hS_lt : Real.sin (π * (η₀ * siteGap c' k) / 2) ^ 2 ≤ 1 / 2 := by
      have hpi := Real.pi_pos
      have h1 : |Real.sin (π * (η₀ * siteGap c' k) / 2)| ≤ 1 / 2 := by
        rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith))]
        exact (Real.sin_le (by positivity)).trans (by nlinarith [Real.pi_lt_d4])
      nlinarith [sq_abs (Real.sin (π * (η₀ * siteGap c' k) / 2)),
        abs_nonneg (Real.sin (π * (η₀ * siteGap c' k) / 2))]
    have hden1 : 0 < Real.cosh (π * (chiQuantile c' n - chiQuantile c' k) / 2) ^ 2 -
        Real.sin (π * (η₀ * siteGap c' k) / 2) ^ 2 := by
      have := Real.one_le_cosh (π * (chiQuantile c' n - chiQuantile c' k) / 2); nlinarith
    have hden2 : 0 < Real.cosh (π * (chiQuantile c' n + chiQuantile c' k) / 2) ^ 2 -
        Real.sin (π * (η₀ * siteGap c' k) / 2) ^ 2 := by
      have := Real.one_le_cosh (π * (chiQuantile c' n + chiQuantile c' k) / 2); nlinarith
    have hχk_pos : 0 < chiQuantile c' k := xiStar_pos.trans (xiStar_lt_chiQuantile hc' (by linarith))
    have hχn_nn : 0 ≤ chiQuantile c' n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn_pos
      · rw [chiQuantile_nat_zero]; exact xiStar_pos.le
      · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
        exact xiStar_pos.le.trans (chiQuantile_spec hc' (by linarith)).1
    have hne_val : chiQuantile c' n ≠ chiQuantile c' k := by
      intro h_eq
      rcases Nat.eq_zero_or_pos n with rfl | hn_pos
      · rw [chiQuantile_nat_zero] at h_eq
        linarith [xiStar_lt_chiQuantile hc' (by linarith : 1 / 4 < (k : ℝ))]
      · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
        have heq_r : (k : ℝ) = (n : ℝ) := (chiQuantile_strictMonoOn hc').injOn
          (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith)) h_eq.symm
        exact hne_idx (Nat.cast_injective heq_r)
    have hnum1 : 0 < Real.sinh (π * (chiQuantile c' n - chiQuantile c' k) / 2) ^ 2 +
        Real.sin (π * (η₀ * siteGap c' k) / 2) ^ 2 := by
      have hsh : Real.sinh (π * (chiQuantile c' n - chiQuantile c' k) / 2) ≠ 0 :=
        Real.sinh_ne_zero.mpr (by have := Real.pi_pos; positivity [sub_ne_zero.mpr hne_val])
      positivity
    have hnum2 : 0 < Real.sinh (π * (chiQuantile c' n + chiQuantile c' k) / 2) ^ 2 +
        Real.sin (π * (η₀ * siteGap c' k) / 2) ^ 2 := by
      have hsh : 0 < Real.sinh (π * (chiQuantile c' n + chiQuantile c' k) / 2) :=
        Real.sinh_pos_iff.mpr (by positivity [Real.pi_pos])
      positivity
    exact mul_pos (div_pos hnum1 hden1) (div_pos hnum2 hden2)
  · exact pairModQ_pos hc' hη₀0 hη₀1 hgap hk hx (Or.inr hx_eq)

private lemma log_pairModQ_eq_phiVar_add_delta {c' η₀ x : ℝ} (hc' : 0 < c') (hη₀0 : 0 ≤ η₀)
    (hη₀1 : η₀ ≤ 1 / 4) (hgap : siteGap c' 1 ≤ 1 / 2) {n k : ℕ} (hk : 1 ≤ k)
    (hx : inCell c' n x) (hne_idx : k ≠ n) :
    Real.log (pairModQ c' η₀ x k) =
      2 * phiVar c' x k + deltaDetune (chiQuantile c' k) (η₀ * siteGap c' k) x := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hχk_pos : 0 < chiQuantile c' k := xiStar_pos.trans (xiStar_lt_chiQuantile hc' (by linarith))
  have hq_pos := pairModQ_pos_of_ne hc' hη₀0 hη₀1 hgap hk hx hne_idx
  have hne_val : x ≠ chiQuantile c' k := by
    rcases lt_or_gt_of_ne hne_idx with hlt | hgt
    · have hk_lt : (k : ℝ) < (n : ℝ) := by exact_mod_cast hlt
      have hχ_lt := chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith))
        (Set.mem_Ici.mpr (by linarith)) hk_lt
      linarith [hx.1]
    · have hn1 : ((n + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hgt
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hχ_le := (chiQuantile_strictMonoOn hc').monotoneOn
        (Set.mem_Ici.mpr (by push_cast; linarith))
        (Set.mem_Ici.mpr (by linarith)) hn1
      linarith [hx.2]
  have h_sq_pos : 0 < (Real.tanh (π * (x - chiQuantile c' k) / 2) *
      Real.tanh (π * (x + chiQuantile c' k) / 2)) ^ 2 := by
    have ht1 : Real.tanh (π * (x - chiQuantile c' k) / 2) ≠ 0 := by
      rw [Real.tanh_eq_sinh_div_cosh, div_ne_zero_iff]
      exact ⟨Real.sinh_ne_zero.mpr (by have := Real.pi_pos; positivity [sub_ne_zero.mpr hne_val]),
        (Real.cosh_pos _).ne'⟩
    have hx0 : 0 ≤ x := by
      rcases Nat.eq_zero_or_pos n with rfl | hn_pos
      · have h0 := chiQuantile_nat_zero c'
        linarith [hx.1, xiStar_pos]
      · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
        exact (xiStar_pos.le.trans (chiQuantile_spec hc' (by linarith)).1).trans hx.1
    have ht2 : Real.tanh (π * (x + chiQuantile c' k) / 2) ≠ 0 := by
      rw [Real.tanh_eq_sinh_div_cosh, div_ne_zero_iff]
      exact ⟨(Real.sinh_pos_iff.mpr (by positivity [Real.pi_pos])).ne', (Real.cosh_pos _).ne'⟩
    exact sq_pos_of_ne_zero (mul_ne_zero ht1 ht2)
  have h_t_eq : ‖blaschkeT (chiQuantile c' k : ℂ) (x : ℂ)‖ =
      |Real.tanh (π * (x - chiQuantile c' k) / 2) * Real.tanh (π * (x + chiQuantile c' k) / 2)| := by
    unfold blaschkeT
    have hc1 : Complex.tanh ((π : ℂ) * ((x : ℂ) - (chiQuantile c' k : ℂ)) / 2) =
        ((Real.tanh (π * (x - chiQuantile c' k) / 2) : ℝ) : ℂ) := by
      have h1 : Complex.tanh ((π * (x - chiQuantile c' k) / 2 : ℝ) : ℂ) =
          ((Real.tanh (π * (x - chiQuantile c' k) / 2) : ℝ) : ℂ) := by
        rw [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
          ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, Complex.ofReal_div]
      rw [← h1]; congr 1; push_cast; ring
    have hc2 : Complex.tanh ((π : ℂ) * ((x : ℂ) + (chiQuantile c' k : ℂ)) / 2) =
        ((Real.tanh (π * (x + chiQuantile c' k) / 2) : ℝ) : ℂ) := by
      have h1 : Complex.tanh ((π * (x + chiQuantile c' k) / 2 : ℝ) : ℂ) =
          ((Real.tanh (π * (x + chiQuantile c' k) / 2) : ℝ) : ℂ) := by
        rw [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
          ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, Complex.ofReal_div]
      rw [← h1]; congr 1; push_cast; ring
    rw [hc1, hc2, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs]
  have h2phi : 2 * phiVar c' x k =
      Real.log ((Real.tanh (π * (x - chiQuantile c' k) / 2) *
        Real.tanh (π * (x + chiQuantile c' k) / 2)) ^ 2) := by
    unfold phiVar realLogT
    rw [h_t_eq]
    calc 2 * Real.log |Real.tanh (π * (x - chiQuantile c' k) / 2) *
            Real.tanh (π * (x + chiQuantile c' k) / 2)|
        = ((2 : ℕ) : ℝ) * Real.log |Real.tanh (π * (x - chiQuantile c' k) / 2) *
            Real.tanh (π * (x + chiQuantile c' k) / 2)| := by norm_num
      _ = Real.log (|Real.tanh (π * (x - chiQuantile c' k) / 2) *
            Real.tanh (π * (x + chiQuantile c' k) / 2)| ^ 2) := (Real.log_pow _ 2).symm
      _ = Real.log ((Real.tanh (π * (x - chiQuantile c' k) / 2) *
            Real.tanh (π * (x + chiQuantile c' k) / 2)) ^ 2) := by rw [sq_abs]
  unfold deltaDetune pairModQ at *
  rw [h2phi, Real.log_div hq_pos.ne' h_sq_pos.ne']
  ring

/-- Unconditional summability of `lambdaHole` and comparison `lambdaHole ≤ Real.log ‖refComb‖`
(valid even at $\eta_0 = 0, x = \chi_n$). -/
theorem lambdaHole_summable_and_le {c' η₀ x : ℝ} (hc' : 0 < c') (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4)
    (hgap : siteGap c' 1 ≤ 1 / 2) {f n : ℕ} (hf : 1 ≤ f) (hn : f + 1 ≤ n) (hx : inCell c' n x) :
    Summable (fun m : ℕ => Real.log (pairModQ c' η₀ x (f + 1 + m))) ∧
      lambdaHole c' η₀ x f ≤ Real.log ‖refComb c' f η₀ (x : ℂ)‖ ∧
      ((0 < η₀ ∨ x ≠ chiQuantile c' n) →
        Real.log ‖refComb c' f η₀ (x : ℂ)‖ = lambdaHole c' η₀ x f) := by
  have hx0 : 0 ≤ x := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    exact (xiStar_pos.le.trans (chiQuantile_spec hc' (by linarith)).1).trans hx.1
  have h_sum_uncond : Summable (fun m : ℕ => Real.log (pairModQ c' η₀ x (f + 1 + m))) := by
    have hn1_ne : chiQuantile c' (n + 1 : ℕ) ≠ x := hx.2.ne'
    have hq_tail : ∀ m : ℕ, 0 < pairModQ c' η₀ x (n + 1 + 1 + m) := fun m =>
      pairModQ_pos_of_ne hc' hη₀0 hη₀1 hgap (by omega) hx (by omega)
    have htail := (refComb_norm_log_eq_tsum hc' hx0 (f := n + 1) (by omega) hη₀0 hη₀1 hgap
      hn1_ne hq_tail).1
    have hshift : Summable (fun m : ℕ => Real.log (pairModQ c' η₀ x (f + 1 + (m + (n + 1 - f))))) := by
      refine htail.congr fun m => ?_
      have heq : n + 1 + 1 + m = f + 1 + (m + (n + 1 - f)) := by omega
      rw [heq]
    exact (summable_nat_add_iff (n + 1 - f)).mp hshift
  refine ⟨h_sum_uncond, ?_, ?_⟩
  · by_cases hnz : 0 < η₀ ∨ x ≠ chiQuantile c' n
    · have hf_ne : chiQuantile c' f ≠ x := by
        have hf1 : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
        have hfn : (f : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : f < n)
        exact ((chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith))
          (Set.mem_Ici.mpr (by linarith)) hfn).trans_le hx.1).ne
      have hq_all : ∀ m : ℕ, 0 < pairModQ c' η₀ x (f + 1 + m) := fun m => by
        by_cases hkn : f + 1 + m = n
        · rw [hkn]; exact pairModQ_pos hc' hη₀0 hη₀1 hgap (by omega) hx hnz
        · exact pairModQ_pos_of_ne hc' hη₀0 hη₀1 hgap (by omega) hx hkn
      have h_eq := (refComb_norm_log_eq_tsum hc' hx0 hf hη₀0 hη₀1 hgap hf_ne hq_all).2
      unfold lambdaHole; linarith
    · push Not at hnz
      have hη0 : η₀ = 0 := le_antisymm hnz.1 hη₀0
      have hx_eq : x = chiQuantile c' n := hnz.2
      have hphi_le0 : phiVar c' x f ≤ 0 := by
        unfold phiVar realLogT blaschkeT
        have hf1 : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
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
        rw [hc1, hc2, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        exact Real.log_nonpos (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          (by
            have ht1 : |Real.tanh (π * (x - chiQuantile c' f) / 2)| ≤ 1 := abs_tanh_le_one
            have ht2 : |Real.tanh (π * (x + chiQuantile c' f) / 2)| ≤ 1 := abs_tanh_le_one
            nlinarith [abs_nonneg (Real.tanh (π * (x - chiQuantile c' f) / 2)),
              abs_nonneg (Real.tanh (π * (x + chiQuantile c' f) / 2))])
      have hterm_le0 : ∀ m : ℕ, Real.log (pairModQ c' η₀ x (f + 1 + m)) ≤ 0 := fun m => by
        have hle1 := @pairModQ_le_one c' η₀ x hc' hη₀0 hη₀1 hgap (f + 1 + m) (by omega)
        by_cases h0 : pairModQ c' η₀ x (f + 1 + m) = 0
        · rw [h0, Real.log_zero]
        · have hnn : 0 ≤ pairModQ c' η₀ x (f + 1 + m) := by
            unfold pairModQ blaschkePairQ; positivity
          exact Real.log_nonpos hnn hle1
      have hts_le0 : ∑' m : ℕ, Real.log (pairModQ c' η₀ x (f + 1 + m)) ≤ 0 :=
        tsum_nonpos hterm_le0
      have hlam_le0 : lambdaHole c' η₀ x f ≤ 0 := by unfold lambdaHole; linarith
      have h_ref0 := refComb_eq_zero_at_zero_node hc' hf hn hx_eq
      rw [hη0, h_ref0, norm_zero, Real.log_zero]
      rwa [hη0] at hlam_le0
  · intro hnz
    have hf_ne : chiQuantile c' f ≠ x := by
      have hf1 : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
      have hfn : (f : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : f < n)
      exact ((chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith))
        (Set.mem_Ici.mpr (by linarith)) hfn).trans_le hx.1).ne
    have hq_all : ∀ m : ℕ, 0 < pairModQ c' η₀ x (f + 1 + m) := fun m => by
      by_cases hkn : f + 1 + m = n
      · rw [hkn]; exact pairModQ_pos hc' hη₀0 hη₀1 hgap (by omega) hx hnz
      · exact pairModQ_pos_of_ne hc' hη₀0 hη₀1 hgap (by omega) hx hkn
    exact (refComb_norm_log_eq_tsum hc' hx0 hf hη₀0 hη₀1 hgap hf_ne hq_all).2

private lemma DK_split_identity {c' η₀ x : ℝ} (hc' : 0 < c') {f n j K : ℕ}
    (hf : 1 ≤ f) (hj : 1 ≤ j) (hfnj : f + j ≤ n) (hK : n + j ≤ K) (hx : inCell c' n x) :
    phiVar c' x f + (∑ k ∈ Finset.Icc (f + 1) K, Real.log (pairModQ c' η₀ x k)) -
        2 * ∫ a in (f : ℝ)..((K : ℝ) + 1 / 2), phiVar c' x a =
      jEndComb c' x f + holeH c' η₀ n j x +
        (∑ k ∈ Finset.Icc (f + 1) (n - j),
          (Real.log (pairModQ c' η₀ x k) - 2 * ∫ a in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), phiVar c' x a)) +
        ∑ k ∈ Finset.Icc (n + j + 1) K,
          (Real.log (pairModQ c' η₀ x k) - 2 * ∫ a in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), phiVar c' x a) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hx0 : 0 ≤ x := (xiStar_pos.le.trans (chiQuantile_spec hc' (by linarith)).1).trans hx.1
  obtain ⟨_, hint_14, _, _, _⟩ := riesz_real_identities hc' hx0 f hf
  have h_ii : ∀ {a b : ℝ}, 1 / 4 < a → a ≤ b → IntervalIntegrable (phiVar c' x) volume a b := by
    intro a b ha hab
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      (hint_14.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ha.le)))
  have h_sum_split :
      (∑ k ∈ Finset.Icc (f + 1) K, Real.log (pairModQ c' η₀ x k)) =
        (∑ k ∈ Finset.Icc (n - j + 1) (n + j), Real.log (pairModQ c' η₀ x k)) +
          (∑ k ∈ Finset.Icc (f + 1) (n - j), Real.log (pairModQ c' η₀ x k)) +
          ∑ k ∈ Finset.Icc (n + j + 1) K, Real.log (pairModQ c' η₀ x k) := by
    have h1 : Finset.Icc (f + 1) K = Finset.Icc (f + 1) (n + j) ∪ Finset.Icc (n + j + 1) K := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hd1 : Disjoint (Finset.Icc (f + 1) (n + j)) (Finset.Icc (n + j + 1) K) := by
      rw [Finset.disjoint_left]; intro k h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
    have h2 : Finset.Icc (f + 1) (n + j) =
        Finset.Icc (f + 1) (n - j) ∪ Finset.Icc (n - j + 1) (n + j) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hd2 : Disjoint (Finset.Icc (f + 1) (n - j)) (Finset.Icc (n - j + 1) (n + j)) := by
      rw [Finset.disjoint_left]; intro k h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
    rw [h1, Finset.sum_union hd1, h2, Finset.sum_union hd2]; ring
  have h_unit_sum : ∀ A B : ℕ, 1 ≤ A → A ≤ B →
      (∑ k ∈ Finset.Icc A B, ∫ a in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), phiVar c' x a) =
        ∫ a in ((A : ℝ) - 1 / 2)..((B : ℝ) + 1 / 2), phiVar c' x a := by
    intro A B hA hAB
    induction B, hAB using Nat.le_induction with
    | base => simp [Finset.Icc_self]
    | succ B hB ih =>
      have hsub : Finset.Icc A (B + 1) = insert (B + 1) (Finset.Icc A B) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsub, Finset.sum_insert (by simp), ih, add_comm]
      have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
      have hAB1 : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
      have h_eq_lim : (B : ℝ) + 1 / 2 = ((B + 1 : ℕ) : ℝ) - 1 / 2 := by push_cast; ring
      have hi1 := h_ii (by linarith : 1 / 4 < (A : ℝ) - 1 / 2)
        (by linarith : (A : ℝ) - 1 / 2 ≤ (B : ℝ) + 1 / 2)
      have hi2 : IntervalIntegrable (phiVar c' x) volume ((B : ℝ) + 1 / 2)
          (((B + 1 : ℕ) : ℝ) + 1 / 2) :=
        h_ii (by linarith : 1 / 4 < (B : ℝ) + 1 / 2) (by push_cast; linarith)
      have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
      have h_eq2 : (B : ℝ) + 1 / 2 = ((B + 1 : ℕ) : ℝ) - 1 / 2 := by push_cast; ring
      simpa only [h_eq2] using hsplit
  have hf1 : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have h_left_int : (∑ k ∈ Finset.Icc (f + 1) (n - j),
      ∫ a in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), phiVar c' x a) =
      ∫ a in ((f : ℝ) + 1 / 2)..((n : ℝ) - (j : ℝ) + 1 / 2), phiVar c' x a := by
    by_cases h_le : f + 1 ≤ n - j
    · rw [h_unit_sum (f + 1) (n - j) (by omega) h_le]
      have h_cast : ((n - j : ℕ) : ℝ) = (n : ℝ) - (j : ℝ) := Nat.cast_sub (by omega)
      push_cast; rw [h_cast]; ring_nf
    · have h_eq : n - j = f := by omega
      have h_emp : Finset.Icc (f + 1) (n - j) = ∅ := Finset.Icc_eq_empty (by omega)
      have h_cast : (n : ℝ) - (j : ℝ) = (f : ℝ) := by
        have := Nat.cast_sub (R := ℝ) (by omega : j ≤ n)
        rw [← this, h_eq]
      rw [h_emp, Finset.sum_empty, h_cast, intervalIntegral.integral_same]
  have h_right_int : (∑ k ∈ Finset.Icc (n + j + 1) K,
      ∫ a in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), phiVar c' x a) =
      ∫ a in ((n : ℝ) + (j : ℝ) + 1 / 2)..((K : ℝ) + 1 / 2), phiVar c' x a := by
    by_cases h_le : n + j + 1 ≤ K
    · rw [h_unit_sum (n + j + 1) K (by omega) h_le]
      push_cast; ring_nf
    · have h_eq : K = n + j := by omega
      have h_emp : Finset.Icc (n + j + 1) K = ∅ := Finset.Icc_eq_empty (by omega)
      rw [h_emp, Finset.sum_empty, h_eq]; push_cast; rw [intervalIntegral.integral_same]
  have h_int_split :
      ∫ a in (f : ℝ)..((K : ℝ) + 1 / 2), phiVar c' x a =
        (∫ a in (f : ℝ)..((f : ℝ) + 1 / 2), phiVar c' x a) +
          (∫ a in ((f : ℝ) + 1 / 2)..((n : ℝ) - (j : ℝ) + 1 / 2), phiVar c' x a) +
          (∫ a in ((n : ℝ) - (j : ℝ) + 1 / 2)..((n : ℝ) + (j : ℝ) + 1 / 2), phiVar c' x a) +
          (∫ a in ((n : ℝ) + (j : ℝ) + 1 / 2)..((K : ℝ) + 1 / 2), phiVar c' x a) := by
    have hfnj_r : (f : ℝ) ≤ (n : ℝ) - (j : ℝ) := by
      have hle : (f : ℝ) + (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hfnj
      linarith
    have hj_r : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hK_r : (n : ℝ) + (j : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    have hi1 := h_ii (by linarith : 1 / 4 < (f : ℝ)) (by linarith : (f : ℝ) ≤ (f : ℝ) + 1 / 2)
    have hi2 := h_ii (by linarith : 1 / 4 < (f : ℝ) + 1 / 2)
      (by linarith : (f : ℝ) + 1 / 2 ≤ (n : ℝ) - (j : ℝ) + 1 / 2)
    have hi3 := h_ii (by linarith : 1 / 4 < (n : ℝ) - (j : ℝ) + 1 / 2)
      (by linarith : (n : ℝ) - (j : ℝ) + 1 / 2 ≤ (n : ℝ) + (j : ℝ) + 1 / 2)
    have hi4 := h_ii (by linarith : 1 / 4 < (n : ℝ) + (j : ℝ) + 1 / 2)
      (by linarith : (n : ℝ) + (j : ℝ) + 1 / 2 ≤ (K : ℝ) + 1 / 2)
    have s1 := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have s2 := intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3
    have s3 := intervalIntegral.integral_add_adjacent_intervals ((hi1.trans hi2).trans hi3) hi4
    linarith
  unfold jEndComb holeH
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [h_sum_split, h_left_int, h_right_int, h_int_split]
  ring

private lemma left_cell_lower_K4 {c' η₀ x : ℝ} (hc' : 0 < c') (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4)
    (hgap : siteGap c' 1 ≤ 1 / 2) {f n j k : ℕ} (hf : 1 ≤ f) (hj : 1 ≤ j)
    (hx : inCell c' n x) (hk : k ∈ Finset.Icc (f + 1) (n - j)) :
    -2 * eLeftCell c' x k ≤
      Real.log (pairModQ c' η₀ x k) -
        2 * ∫ a in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), phiVar c' x a := by
  have hk_mem := Finset.mem_Icc.mp hk
  have hk2 : 2 ≤ k := by omega
  have hk_lt_n : k < n := by omega
  have hne_idx : k ≠ n := hk_lt_n.ne
  have h_log_ge : 2 * phiVar c' x k ≤ Real.log (pairModQ c' η₀ x k) := by
    rw [log_pairModQ_eq_phiVar_add_delta hc' hη₀0 hη₀1 hgap (by omega) hx hne_idx]
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
    have hχk_nn : 0 ≤ chiQuantile c' k := xiStar_pos.le.trans (chiQuantile_spec hc' (by linarith)).1
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hx0 : 0 ≤ x := by
      have hkn : (k : ℝ) < (n : ℝ) := by exact_mod_cast hk_lt_n
      exact hχk_nn.trans ((chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith))
        (Set.mem_Ici.mpr (by linarith)) hkn).le.trans hx.1)
    have hne_val : x ≠ chiQuantile c' k := by
      have hk_lt : (k : ℝ) < (n : ℝ) := by exact_mod_cast hk_lt_n
      exact ((chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith))
        (Set.mem_Ici.mpr (by linarith)) hk_lt).trans_le hx.1).ne'
    have hgk_nn : 0 ≤ siteGap c' k := by
      unfold siteGap
      exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn
        (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith)) (by linarith))
    have hgk_le : siteGap c' k ≤ siteGap c' 1 := by
      have hanti := (siteGap_strictAnti hc').antitone (show 0 ≤ k - 1 by omega)
      have heq : (k - 1) + 1 = k := by omega
      simpa [heq] using hanti
    have hd_nn := (deltaDetune_bounds_universal hχk_nn hx0 hne_val (mul_nonneg hη₀0 hgk_nn)
      (by nlinarith)).1
    linarith
  have hk2_r : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have ha14 : 1 / 4 < (k : ℝ) - 1 / 2 := by linarith
  have hχk12_lt : chiQuantile c' ((k : ℝ) + 1 / 2) < x := by
    have hk1_le : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hk_lt_n
    have hkn : (k : ℝ) + 1 / 2 < (n : ℝ) := by linarith
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    exact (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith))
      (Set.mem_Ici.mpr (by linarith)) hkn).trans_le hx.1
  have hχ_lt_Icc : ∀ a ∈ Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2), chiQuantile c' a < x := fun a ha => by
    rcases eq_or_lt_of_le ha.2 with rfl | hlt
    · exact hχk12_lt
    · exact (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith [ha.1]))
        (Set.mem_Ici.mpr (by linarith)) hlt).trans hχk12_lt
  have hne_Icc : ∀ a ∈ Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2), chiQuantile c' a ≠ x := fun a ha =>
    (hχ_lt_Icc a ha).ne
  have hx0 : 0 ≤ x := (xiStar_pos.le.trans (chiQuantile_spec hc' ha14.le).1).trans
    (hχ_lt_Icc _ (left_mem_Icc.mpr (by linarith))).le
  have hs_pos : 0 < x - xiStar := sub_pos.mpr
    ((xiStar_lt_chiQuantile hc' ha14).trans (hχ_lt_Icc _ (left_mem_Icc.mpr (by linarith))))
  have hM_bd : ∀ a ∈ Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2),
      phiVarSecond c' x a ≤ (2 / (x - xiStar)) *
        (chiDeriv c' ((k : ℝ) - 1 / 2) ^ 2 / siteRadius c' ((k : ℝ) - 1 / 2)) := by
    intro a ha
    have ha_gt : 1 / 4 < a := lt_of_lt_of_le ha14 ha.1
    have h1 := phiVarSecond_le_G hc' ha_gt (hχ_lt_Icc a ha)
    have hcd_le : chiDeriv c' a ≤ chiDeriv c' ((k : ℝ) - 1 / 2) := by
      rcases eq_or_lt_of_le ha.1 with rfl | hgt
      · exact le_rfl
      · exact (chiDeriv_strictAntiOn hc' (Set.mem_Ioi.mpr ha14) (Set.mem_Ioi.mpr ha_gt) hgt).le
    have hr_ge : siteRadius c' ((k : ℝ) - 1 / 2) ≤ siteRadius c' a := by
      rcases eq_or_lt_of_le ha.1 with rfl | hgt
      · exact le_rfl
      · unfold siteRadius
        linarith [chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr ha14.le)
          (Set.mem_Ici.mpr ha_gt.le) hgt]
    have hcd_pos := chiDeriv_pos hc' ha_gt
    have hr_pos : 0 < siteRadius c' ((k : ℝ) - 1 / 2) := sub_pos.mpr (xiStar_lt_chiQuantile hc' ha14)
    have h_ratio : chiDeriv c' a ^ 2 / siteRadius c' a ≤
        chiDeriv c' ((k : ℝ) - 1 / 2) ^ 2 / siteRadius c' ((k : ℝ) - 1 / 2) :=
      div_le_div₀ (by positivity) (pow_le_pow_left₀ hcd_pos.le hcd_le 2) hr_pos hr_ge
    exact h1.trans (mul_le_mul_of_nonneg_left h_ratio (by positivity))
  have hpeano := midpoint_peano_ge
    (g := phiVar c' x) (g' := phiVarDeriv c' x) (g'' := phiVarSecond c' x)
    (k := (k : ℝ)) (M := (2 / (x - xiStar)) *
      (chiDeriv c' ((k : ℝ) - 1 / 2) ^ 2 / siteRadius c' ((k : ℝ) - 1 / 2)))
    (fun t ht => (phiVar_hasDerivAt hc' hx0 (lt_of_lt_of_le ha14 ht.1) (hne_Icc t ht)).1)
    (fun t ht => (phiVar_hasDerivAt hc' hx0 (lt_of_lt_of_le ha14 ht.1) (hne_Icc t ht)).2)
    (continuousOn_phiVarSecond hc' hx0 ha14 (by linarith) hne_Icc)
    hM_bd
  have hM_nn : 0 ≤ (2 / (x - xiStar)) *
      (chiDeriv c' ((k : ℝ) - 1 / 2) ^ 2 / siteRadius c' ((k : ℝ) - 1 / 2)) := by
    have hcd_nn : 0 ≤ chiDeriv c' ((k : ℝ) - 1 / 2) := (chiDeriv_pos hc' ha14).le
    have hr_pos : 0 < siteRadius c' ((k : ℝ) - 1 / 2) := sub_pos.mpr (xiStar_lt_chiQuantile hc' ha14)
    exact mul_nonneg (div_nonneg two_pos.le hs_pos.le) (div_nonneg (sq_nonneg _) hr_pos.le)
  unfold eLeftCell
  linarith

private lemma right_cell_lower_K4 {c' η₀ x : ℝ} (hc' : 0 < c') (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4)
    (hgap : siteGap c' 1 ≤ 1 / 2) {n j k : ℕ} (hj : 1 ≤ j) (hk : n + j + 1 ≤ k)
    (hx : inCell c' n x) :
    0 ≤ Real.log (pairModQ c' η₀ x k) -
      2 * ∫ a in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), phiVar c' x a := by
  have hk_ge3 : 2 ≤ k := by omega
  have hk3_r : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge3
  have hne_idx : k ≠ n := by omega
  have hχk_nn : 0 ≤ chiQuantile c' k := xiStar_pos.le.trans (chiQuantile_spec hc' (by linarith)).1
  have hn1 : ((n + 1 : ℕ) : ℝ) ≤ (k : ℝ) - 1 / 2 := by
    have hle_nat : (n + 2 : ℕ) ≤ k := by omega
    have hle_r : ((n + 2 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hle_nat
    push_cast at hle_r ⊢; linarith
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hx_lt_k12 : x < chiQuantile c' ((k : ℝ) - 1 / 2) := by
    have hle := (chiQuantile_strictMonoOn hc').monotoneOn
      (Set.mem_Ici.mpr (by push_cast; linarith))
      (Set.mem_Ici.mpr (by linarith)) hn1
    exact hx.2.trans_le hle
  have hx0 : 0 ≤ x := by
    rcases Nat.eq_zero_or_pos n with rfl | hn_pos
    · unfold inCell at hx; rw [chiQuantile_nat_zero] at hx; exact xiStar_pos.le.trans hx.1
    · have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
      exact (xiStar_pos.le.trans (chiQuantile_spec hc' (by linarith)).1).trans hx.1
  have h_log_ge : 2 * phiVar c' x k ≤ Real.log (pairModQ c' η₀ x k) := by
    rw [log_pairModQ_eq_phiVar_add_delta hc' hη₀0 hη₀1 hgap (by omega) hx hne_idx]
    have hgk_nn : 0 ≤ siteGap c' k := by
      unfold siteGap
      exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn
        (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith)) (by linarith))
    have hgk_le : siteGap c' k ≤ siteGap c' 1 := by
      have hanti := (siteGap_strictAnti hc').antitone (show 0 ≤ k - 1 by omega)
      have heq : (k - 1) + 1 = k := by omega
      simpa [heq] using hanti
    have hχk_gt : x < chiQuantile c' k := hx_lt_k12.trans
      (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith))
        (Set.mem_Ici.mpr (by linarith)) (by linarith))
    have hd_nn := (deltaDetune_bounds_universal hχk_nn hx0 hχk_gt.ne (mul_nonneg hη₀0 hgk_nn)
      (by nlinarith)).1
    linarith
  have ha14 : 1 / 4 < (k : ℝ) - 1 / 2 := by linarith
  have hχ_gt_Icc : ∀ a ∈ Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2), x < chiQuantile c' a := fun a ha => by
    rcases eq_or_lt_of_le ha.1 with rfl | hgt
    · exact hx_lt_k12
    · exact hx_lt_k12.trans (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr ha14.le)
        (Set.mem_Ici.mpr (ha14.le.trans ha.1)) hgt)
  have hne_Icc : ∀ a ∈ Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2), chiQuantile c' a ≠ x := fun a ha =>
    (hχ_gt_Icc a ha).ne'
  have hM_bd : ∀ a ∈ Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2), phiVarSecond c' x a ≤ 0 := fun a ha =>
    (phiVar_deriv_sign_of_gt hc' hx0 (lt_of_lt_of_le ha14 ha.1) (hχ_gt_Icc a ha)).2.le
  have hpeano := midpoint_peano_ge
    (g := phiVar c' x) (g' := phiVarDeriv c' x) (g'' := phiVarSecond c' x)
    (k := (k : ℝ)) (M := 0)
    (fun t ht => (phiVar_hasDerivAt hc' hx0 (lt_of_lt_of_le ha14 ht.1) (hne_Icc t ht)).1)
    (fun t ht => (phiVar_hasDerivAt hc' hx0 (lt_of_lt_of_le ha14 ht.1) (hne_Icc t ht)).2)
    (continuousOn_phiVarSecond hc' hx0 ha14 (by linarith) hne_Icc)
    hM_bd
  linarith

/-- Lower hole comparison (`cmb:K4` lower bound, `comb_estimates.tex`, line 146):
valid unconditionally for all $\eta_0 \in [0, \frac14]$ and $x \in [\chi_n, \chi_{n+1})$,
even at $(\eta_0 = 0, x = \chi_n)$, for both `lambdaHole` and `Real.log ‖refComb‖`. -/
theorem hole_lower_K4 {c' η₀ x : ℝ} (hc' : 0 < c') (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4)
    (hgap : siteGap c' 1 ≤ 1 / 2) {f n j : ℕ} (hf : 1 ≤ f) (hj : 1 ≤ j) (hfnj : f + j ≤ n)
    (hx : inCell c' n x) :
    holeH c' η₀ n j x + jEndComb c' x f - 2 * eLeftComb c' f n j x ≤
        lambdaHole c' η₀ x f + c' * slitL x - c' * combPf c' f x ∧
      holeH c' η₀ n j x + jEndComb c' x f - 2 * eLeftComb c' f n j x ≤
        Real.log ‖refComb c' f η₀ (x : ℂ)‖ + c' * slitL x - c' * combPf c' f x := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hx_xi : xiStar ≤ x := (chiQuantile_spec hc' (by linarith)).1.trans hx.1
  have hx0 : 0 ≤ x := xiStar_pos.le.trans hx_xi
  obtain ⟨hsum_q, hlam_le, _⟩ := lambdaHole_summable_and_le hc' hη₀0 hη₀1 hgap hf (by omega) hx
  have h_part : ∀ K ≥ n + j,
      holeH c' η₀ n j x + jEndComb c' x f - 2 * eLeftComb c' f n j x ≤
        phiVar c' x f + (∑ k ∈ Finset.Icc (f + 1) K, Real.log (pairModQ c' η₀ x k)) -
          2 * ∫ a in (f : ℝ)..((K : ℝ) + 1 / 2), phiVar c' x a := by
    intro K hK
    rw [DK_split_identity hc' hf hj hfnj hK hx]
    have hL : -2 * eLeftComb c' f n j x ≤ ∑ k ∈ Finset.Icc (f + 1) (n - j),
        (Real.log (pairModQ c' η₀ x k) - 2 * ∫ a in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), phiVar c' x a) := by
      unfold eLeftComb
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun k hk => left_cell_lower_K4 hc' hη₀0 hη₀1 hgap hf hj hx hk
    have hR : 0 ≤ ∑ k ∈ Finset.Icc (n + j + 1) K,
        (Real.log (pairModQ c' η₀ x k) - 2 * ∫ a in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), phiVar c' x a) :=
      Finset.sum_nonneg fun k hk =>
        right_cell_lower_K4 hc' hη₀0 hη₀1 hgap hj (Finset.mem_Icc.mp hk).1 hx
    linarith
  have hsum_tend : Tendsto (fun K : ℕ =>
      phiVar c' x f + ∑ k ∈ Finset.Icc (f + 1) K, Real.log (pairModQ c' η₀ x k))
      atTop (𝓝 (lambdaHole c' η₀ x f)) := by
    unfold lambdaHole
    refine tendsto_const_nhds.add ?_
    have hts := hsum_q.hasSum.tendsto_sum_nat
    have h_shift : ∀ K ≥ f,
        ∑ k ∈ Finset.Icc (f + 1) K, Real.log (pairModQ c' η₀ x k) =
          ∑ m ∈ Finset.range (K - f), Real.log (pairModQ c' η₀ x (f + 1 + m)) := by
      intro K hK
      have h_eq : Finset.Icc (f + 1) K = (Finset.range (K - f)).image (fun m => f + 1 + m) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
        constructor
        · intro ⟨h1, h2⟩; exact ⟨k - (f + 1), by omega, by omega⟩
        · rintro ⟨m, hm, rfl⟩; omega
      rw [h_eq, Finset.sum_image (fun a _ b _ h => by omega)]
    have h_sub_tend : Tendsto (fun K : ℕ => K - f) atTop atTop :=
      tendsto_atTop_atTop.mpr fun N => ⟨N + f, fun K hK => Nat.le_sub_of_add_le hK⟩
    exact (hts.comp h_sub_tend).congr'
      (by filter_upwards [eventually_ge_atTop f] with K hK; exact (h_shift K hK).symm)
  obtain ⟨_, hint_14, _, _, hriesz⟩ := riesz_real_identities hc' hx0 f hf
  have h_riesz_f := (hriesz hx_xi).2
  have hf1 : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hint_f : IntegrableOn (phiVar c' x) (Ioi (f : ℝ)) volume :=
    hint_14.mono_set (Ioi_subset_Ioi (by linarith))
  have h_int_tend : Tendsto (fun K : ℕ => 2 * ∫ a in (f : ℝ)..((K : ℝ) + 1 / 2), phiVar c' x a)
      atTop (𝓝 (-c' * slitL x + c' * combPf c' f x)) := by
    rw [← h_riesz_f]
    exact tendsto_const_nhds.mul
      (intervalIntegral_tendsto_integral_Ioi (f : ℝ) hint_f
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
  have h_DK_tend : Tendsto (fun K : ℕ =>
      phiVar c' x f + (∑ k ∈ Finset.Icc (f + 1) K, Real.log (pairModQ c' η₀ x k)) -
        2 * ∫ a in (f : ℝ)..((K : ℝ) + 1 / 2), phiVar c' x a)
      atTop (𝓝 (lambdaHole c' η₀ x f + c' * slitL x - c' * combPf c' f x)) := by
    rw [show lambdaHole c' η₀ x f + c' * slitL x - c' * combPf c' f x =
        lambdaHole c' η₀ x f - (-c' * slitL x + c' * combPf c' f x) by ring]
    exact hsum_tend.sub h_int_tend
  have h_lb_lam := ge_of_tendsto h_DK_tend
    (by filter_upwards [eventually_ge_atTop (n + j)] with K hK; exact h_part K hK)
  refine ⟨h_lb_lam, h_lb_lam.trans (by linarith)⟩

/-! ### Section 5: Upper hole comparison `hole_upper_K4` -/

private lemma sum_Icc_inv_sq_le (K : ℕ) :
    (∑ m ∈ Finset.Icc 1 K, (1 : ℝ) / (m : ℝ) ^ 2) ≤ 2 := by
  have h1 : ∀ m ∈ Finset.Icc 1 K,
      (1 : ℝ) / (m : ℝ) ^ 2 ≤ 2 * ((1 : ℝ) / (m : ℝ) - 1 / ((m : ℝ) + 1)) := by
    intro m hm
    have hm_r : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
    have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
    have heq : 2 * ((1 : ℝ) / (m : ℝ) - 1 / ((m : ℝ) + 1)) = 2 / ((m : ℝ) * ((m : ℝ) + 1)) := by
      field_simp [hm_pos.ne', hm1_pos.ne']; ring
    rw [heq, div_le_div_iff₀ (sq_pos_of_pos hm_pos) (mul_pos hm_pos hm1_pos)]
    nlinarith
  have htele : (∑ m ∈ Finset.Icc 1 K, ((1 : ℝ) / (m : ℝ) - 1 / ((m : ℝ) + 1))) ≤ 1 := by
    cases K with
    | zero => simp
    | succ K =>
      have h_eq : ∀ N : ℕ, ∑ m ∈ Finset.Icc 1 (N + 1), ((1 : ℝ) / (m : ℝ) - 1 / ((m : ℝ) + 1)) =
          1 - 1 / ((N + 1 : ℕ) + 1 : ℝ) := by
        intro N
        induction N with
        | zero => norm_num [Finset.Icc_self]
        | succ N ih =>
          have hsub : Finset.Icc 1 (N + 2) = insert (N + 2) (Finset.Icc 1 (N + 1)) := by
            ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hsub, Finset.sum_insert (by simp), ih]
          push_cast; ring
      rw [h_eq K]
      have : (0 : ℝ) ≤ 1 / ((K + 1 : ℕ) + 1 : ℝ) := by positivity
      linarith
  calc ∑ m ∈ Finset.Icc 1 K, (1 : ℝ) / (m : ℝ) ^ 2
      ≤ ∑ m ∈ Finset.Icc 1 K, 2 * ((1 : ℝ) / (m : ℝ) - 1 / ((m : ℝ) + 1)) :=
          Finset.sum_le_sum h1
    _ = 2 * ∑ m ∈ Finset.Icc 1 K, ((1 : ℝ) / (m : ℝ) - 1 / ((m : ℝ) + 1)) := by rw [← Finset.mul_sum]
    _ ≤ 2 * 1 := by linarith
    _ = 2 := by ring

private lemma sum_Icc_midpoint_telescope {g g' : ℝ → ℝ} (A B : ℕ) (hAB : A ≤ B)
    (hg : ∀ t ∈ Icc ((A : ℝ) - 1 / 2) ((B : ℝ) + 1 / 2), HasDerivAt g (g' t) t)
    (hg'_anti : AntitoneOn g' (Icc ((A : ℝ) - 1 / 2) ((B : ℝ) + 1 / 2))) :
    (∑ k ∈ Finset.Icc A B, (2 * g k - 2 * ∫ t in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), g t)) ≤
      (1 / 4 : ℝ) * (g' ((A : ℝ) - 1 / 2) - g' ((B : ℝ) + 1 / 2)) := by
  induction B, hAB using Nat.le_induction with
  | base =>
    simp only [Finset.Icc_self, Finset.sum_singleton]
    exact (midpoint_concave_telescope hg hg'_anti).2
  | succ B hB ih =>
    have hAB_r : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    have h_sub_Icc : Icc ((A : ℝ) - 1 / 2) ((B : ℝ) + 1 / 2) ⊆
        Icc ((A : ℝ) - 1 / 2) (((B + 1 : ℕ) : ℝ) + 1 / 2) :=
      Icc_subset_Icc_right (by push_cast; linarith)
    have h_cell_Icc : Icc (((B + 1 : ℕ) : ℝ) - 1 / 2) (((B + 1 : ℕ) : ℝ) + 1 / 2) ⊆
        Icc ((A : ℝ) - 1 / 2) (((B + 1 : ℕ) : ℝ) + 1 / 2) :=
      Icc_subset_Icc_left (by push_cast; linarith)
    have h_prev := ih (fun t ht => hg t (h_sub_Icc ht)) (hg'_anti.mono h_sub_Icc)
    have h_last := (midpoint_concave_telescope
      (fun t ht => hg t (h_cell_Icc ht)) (hg'_anti.mono h_cell_Icc)).2
    have hsub : Finset.Icc A (B + 1) = insert (B + 1) (Finset.Icc A B) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hsub, Finset.sum_insert (by simp)]
    have h_eq : ((B + 1 : ℕ) : ℝ) - 1 / 2 = (B : ℝ) + 1 / 2 := by push_cast; ring
    have heq_int : ∫ t in (((B + 1 : ℕ) : ℝ) - 1 / 2)..(((B + 1 : ℕ) : ℝ) + 1 / 2), g t =
        ∫ t in ((B : ℝ) + 1 / 2)..(((B + 1 : ℕ) : ℝ) + 1 / 2), g t := by rw [h_eq]
    rw [h_eq] at h_last
    rw [heq_int]
    linarith

private lemma siteGap_sum_ge_mul {c' : ℝ} (hc' : 0 < c') {n k : ℕ} (hn1 : 1 ≤ n) (hk : n + 2 ≤ k) :
    ((k - (n + 1) : ℕ) : ℝ) * siteGap c' k ≤ chiQuantile c' k - chiQuantile c' (n + 1 : ℕ) := by
  have hk_ge : n + 1 ≤ k := by omega
  have h_tele : ∑ m ∈ Finset.Ico (n + 1) k, siteGap c' m =
      chiQuantile c' k - chiQuantile c' (n + 1 : ℕ) := by
    clear hk
    induction k, hk_ge using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      rw [Finset.sum_Ico_succ_top hm, ih]
      unfold siteGap; push_cast; ring
  have h_le_each : ∀ m ∈ Finset.Ico (n + 1) k, siteGap c' k ≤ siteGap c' m := fun m hm => by
    have hm1 : 1 ≤ m := by have := (Finset.mem_Ico.mp hm).1; omega
    have hm_lt : m < k := (Finset.mem_Ico.mp hm).2
    have hanti := (siteGap_strictAnti hc').antitone (show m - 1 ≤ k - 1 by omega)
    have heq1 : (m - 1) + 1 = m := by omega
    have heq2 : (k - 1) + 1 = k := by omega
    simpa [heq1, heq2] using hanti
  have hs_ge := Finset.sum_le_sum h_le_each
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, h_tele] at hs_ge
  exact hs_ge

private lemma right_midpoint_upper_K4 {c' x : ℝ} (hc' : 0 < c') (hgap : siteGap c' 1 ≤ 1 / 2)
    {n j K : ℕ} (hj : 1 ≤ j) (hn3 : 3 ≤ n) (hK : n + j + 1 ≤ K) (hx : inCell c' n x) :
    (∑ k ∈ Finset.Icc (n + j + 1) K,
        (2 * phiVar c' x k - 2 * ∫ a in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), phiVar c' x a)) ≤
      1 / 2 + π / 4 := by
  let A := n + j + 1
  have hA_ge : n + 2 ≤ A := by omega
  have hA4 : (4 : ℝ) ≤ (A : ℝ) := by exact_mod_cast (by omega : 4 ≤ A)
  have ha14 : 1 / 4 < (A : ℝ) - 1 / 2 := by linarith
  have hAn2 : (n : ℝ) + 2 ≤ (A : ℝ) := by exact_mod_cast hA_ge
  have hAK_r : (A : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hn1_14 : (1 / 4 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; push_cast; linarith
  have hχ_gt : ∀ a ∈ Icc ((A : ℝ) - 1 / 2) ((K : ℝ) + 1 / 2), x < chiQuantile c' a := fun a ha => by
    have hA_cast : ((n + 1 : ℕ) : ℝ) < (A : ℝ) - 1 / 2 := by push_cast; linarith
    exact hx.2.trans (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr hn1_14)
      (Set.mem_Ici.mpr (ha14.le.trans ha.1)) (hA_cast.trans_le ha.1))
  have h_deriv : ∀ a ∈ Icc ((A : ℝ) - 1 / 2) ((K : ℝ) + 1 / 2),
      HasDerivAt (phiVar c' x) (phiVarDeriv c' x a) a := fun a ha => by
    have hn_pos : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hx0 : 0 ≤ x := (xiStar_pos.le.trans (chiQuantile_spec hc' (by linarith)).1).trans hx.1
    exact (phiVar_hasDerivAt hc' hx0 (lt_of_lt_of_le ha14 ha.1) (hχ_gt a ha).ne').1
  have hn_pos : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hx0 : 0 ≤ x := (xiStar_pos.le.trans (chiQuantile_spec hc' (by linarith)).1).trans hx.1
  have h_anti_g' : AntitoneOn (phiVarDeriv c' x) (Icc ((A : ℝ) - 1 / 2) ((K : ℝ) + 1 / 2)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
    · intro a ha
      exact (phiVar_hasDerivAt hc' hx0 (lt_of_lt_of_le ha14 ha.1) (hχ_gt a ha).ne').2.continuousAt.continuousWithinAt
    · intro a ha
      rw [interior_Icc] at ha
      exact (phiVar_hasDerivAt hc' hx0 (lt_of_lt_of_le ha14 ha.1.le)
        (hχ_gt a ⟨ha.1.le, ha.2.le⟩).ne').2.differentiableAt.differentiableWithinAt
    · intro a ha
      rw [interior_Icc] at ha
      have haI : a ∈ Icc ((A : ℝ) - 1 / 2) ((K : ℝ) + 1 / 2) := ⟨ha.1.le, ha.2.le⟩
      rw [(phiVar_hasDerivAt hc' hx0 (lt_of_lt_of_le ha14 ha.1.le) (hχ_gt a haI).ne').2.deriv]
      exact (phiVar_deriv_sign_of_gt hc' hx0 (lt_of_lt_of_le ha14 ha.1.le) (hχ_gt a haI)).2.le
  have h_tele := sum_Icc_midpoint_telescope A K hK h_deriv h_anti_g'
  have h_g'K_pos : 0 < phiVarDeriv c' x ((K : ℝ) + 1 / 2) :=
    (phiVar_deriv_sign_of_gt hc' hx0 (by linarith) (hχ_gt _ (right_mem_Icc.mpr (by linarith)))).1
  have hχA_gt := hχ_gt _ (left_mem_Icc.mpr (by linarith))
  have hχA_xi : xiStar ≤ chiQuantile c' ((A : ℝ) - 1 / 2) := (chiQuantile_spec hc' ha14.le).1
  have hbd := (realLogT_deriv_bounds hx0 (xiStar_pos.le.trans hχA_xi) hχA_gt.ne').2.2 hχA_gt
  have h_diff_lb : (1 / 2 : ℝ) * chiDeriv c' ((A : ℝ) - 1 / 2) ≤ chiQuantile c' ((A : ℝ) - 1 / 2) - x := by
    have h_len : (1 / 2 : ℝ) ≤ (A : ℝ) - 1 / 2 - ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
    have h_le_an : ((n + 1 : ℕ) : ℝ) ≤ (A : ℝ) - 1 / 2 := by linarith
    have hn1_gt : (1 / 4 : ℝ) < ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
    have hcont : ContinuousOn (chiDeriv c') (Icc ((n + 1 : ℕ) : ℝ) ((A : ℝ) - 1 / 2)) := fun t ht =>
      (hasDerivAt_chiQuantile hc' (lt_of_lt_of_le hn1_gt ht.1)).2.continuousAt.continuousWithinAt
    have h_int : chiQuantile c' ((A : ℝ) - 1 / 2) - chiQuantile c' ((n + 1 : ℕ) : ℝ) =
        ∫ t in ((n + 1 : ℕ) : ℝ)..((A : ℝ) - 1 / 2), chiDeriv c' t := by
      refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => ?_)
        (hcont.intervalIntegrable_of_Icc h_le_an)).symm
      rw [Set.uIcc_of_le h_le_an] at ht
      exact (hasDerivAt_chiQuantile hc' (lt_of_lt_of_le hn1_gt ht.1)).1
    have hm := intervalIntegral.integral_mono_on h_le_an (intervalIntegrable_const (μ := volume))
      (hcont.intervalIntegrable_of_Icc h_le_an) fun t ht => by
        rcases eq_or_lt_of_le ht.2 with rfl | hlt
        · exact le_rfl
        · exact (chiDeriv_strictAntiOn hc' (Set.mem_Ioi.mpr (lt_of_lt_of_le hn1_gt ht.1))
            (Set.mem_Ioi.mpr ha14) hlt).le
    rw [intervalIntegral.integral_const, smul_eq_mul, ← h_int] at hm
    have hcd_pos := chiDeriv_pos hc' ha14
    nlinarith [hx.2]
  have hcd_le1 : chiDeriv c' ((A : ℝ) - 1 / 2) ≤ 1 := by
    have h1 := (chiDeriv_strictAntiOn hc' (Set.mem_Ioi.mpr (by linarith : 1 / 4 < (n : ℝ)))
      (Set.mem_Ioi.mpr ha14) (by linarith)).le
    have h2 := chiDeriv_le_two_siteGap hc' hn3
    have h3 : siteGap c' n ≤ siteGap c' 1 := by
      have hanti := (siteGap_strictAnti hc').antitone (show 0 ≤ n - 1 by omega)
      have heq : (n - 1) + 1 = n := by omega
      simpa [heq] using hanti
    linarith
  have hcd_pos := chiDeriv_pos hc' ha14
  have h_inv_le : chiDeriv c' ((A : ℝ) - 1 / 2) / (chiQuantile c' ((A : ℝ) - 1 / 2) - x) ≤ 2 := by
    rw [div_le_iff₀ (sub_pos.mpr hχA_gt)]; linarith
  have h_g'A_bd : phiVarDeriv c' x ((A : ℝ) - 1 / 2) ≤ 2 + π := by
    unfold phiVarDeriv
    calc realLogTDeriv x (chiQuantile c' ((A : ℝ) - 1 / 2)) * chiDeriv c' ((A : ℝ) - 1 / 2)
        ≤ (1 / (chiQuantile c' ((A : ℝ) - 1 / 2) - x) + π) * chiDeriv c' ((A : ℝ) - 1 / 2) :=
          mul_le_mul_of_nonneg_right (hbd.2 hχA_xi) hcd_pos.le
      _ = chiDeriv c' ((A : ℝ) - 1 / 2) / (chiQuantile c' ((A : ℝ) - 1 / 2) - x) +
            π * chiDeriv c' ((A : ℝ) - 1 / 2) := by ring
      _ ≤ 2 + π * 1 := by gcongr
      _ = 2 + π := by ring
  linarith

private lemma right_detune_upper_K4 {c' η₀ x C_δ : ℝ} (hc' : 0 < c') (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4)
    (hgap : siteGap c' 1 ≤ 1 / 2) (hC_δ : 0 < C_δ)
    (hdet : ∀ {χ ε x : ℝ}, xiStar ≤ χ → 0 ≤ x → x ≠ χ → 0 ≤ ε → ε ≤ 1 / 8 →
      deltaDetune χ ε x ≤ ε ^ 2 / (x - χ) ^ 2 + C_δ * ε ^ 2 * Real.exp (-π * |x - χ|))
    {n j K : ℕ} (hj : 1 ≤ j) (hn1_nat : 1 ≤ n) (hK : n + j + 1 ≤ K) (hx : inCell c' n x) :
    (∑ k ∈ Finset.Icc (n + j + 1) K, deltaDetune (chiQuantile c' k) (η₀ * siteGap c' k) x) ≤
      1 / 8 + C_δ / (32 * π) * Real.exp (π / 2) := by
  have hn1_r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1_nat
  have hx0 : 0 ≤ x := (xiStar_pos.le.trans (chiQuantile_spec hc' (by linarith)).1).trans hx.1
  have h_term : ∀ k ∈ Finset.Icc (n + j + 1) K,
      deltaDetune (chiQuantile c' k) (η₀ * siteGap c' k) x ≤
        (1 / 16 : ℝ) / ((k - (n + 1) : ℕ) : ℝ) ^ 2 +
          C_δ * (1 / 32 : ℝ) * Real.exp (π / 2) *
            ∫ t in (chiQuantile c' k)..(chiQuantile c' (k + 1 : ℕ)),
              Real.exp (-π * (t - chiQuantile c' (n + 1 : ℕ))) := by
    intro k hk
    have hk_mem := Finset.mem_Icc.mp hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
    have hχk_xi : xiStar ≤ chiQuantile c' k := (chiQuantile_spec hc' (by linarith)).1
    have hgk_pos : 0 < siteGap c' k := by
      unfold siteGap
      exact sub_pos.mpr (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith))
        (Set.mem_Ici.mpr (by linarith)) (by linarith))
    have hgk_le : siteGap c' k ≤ siteGap c' 1 := by
      have hanti := (siteGap_strictAnti hc').antitone (show 0 ≤ k - 1 by omega)
      have heq : (k - 1) + 1 = k := by omega
      simpa [heq] using hanti
    have hχk_gt : x < chiQuantile c' k := by
      have hn1_lt : ((n + 1 : ℕ) : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : n + 1 < k)
      have hn1_14 : (1 / 4 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact hx.2.trans (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr hn1_14)
        (Set.mem_Ici.mpr (by linarith)) hn1_lt)
    have hd_bd := hdet hχk_xi hx0 hχk_gt.ne (mul_nonneg hη₀0 hgk_pos.le) (by nlinarith)
    have h_gap_sum := siteGap_sum_ge_mul hc' hn1_nat (by omega : n + 2 ≤ k)
    have hm_pos : (0 : ℝ) < ((k - (n + 1) : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k - (n + 1))
    have h_dist : ((k - (n + 1) : ℕ) : ℝ) * siteGap c' k ≤ |x - chiQuantile c' k| := by
      rw [abs_of_neg (sub_neg.mpr hχk_gt), neg_sub]; linarith [hx.2]
    have h_sq_dist : (((k - (n + 1) : ℕ) : ℝ) * siteGap c' k) ^ 2 ≤ (x - chiQuantile c' k) ^ 2 := by
      simpa [sq_abs] using pow_le_pow_left₀ (by positivity) h_dist 2
    have h_alg : (η₀ * siteGap c' k) ^ 2 / (x - chiQuantile c' k) ^ 2 ≤
        (1 / 16 : ℝ) / ((k - (n + 1) : ℕ) : ℝ) ^ 2 := by
      have hη_sq : η₀ ^ 2 ≤ 1 / 16 := by nlinarith
      have h_num : (η₀ * siteGap c' k) ^ 2 ≤ (1 / 16 : ℝ) * siteGap c' k ^ 2 := by
        calc (η₀ * siteGap c' k) ^ 2 = η₀ ^ 2 * siteGap c' k ^ 2 := by ring
          _ ≤ (1 / 16 : ℝ) * siteGap c' k ^ 2 := mul_le_mul_of_nonneg_right hη_sq (sq_nonneg _)
      calc (η₀ * siteGap c' k) ^ 2 / (x - chiQuantile c' k) ^ 2
          ≤ ((1 / 16 : ℝ) * siteGap c' k ^ 2) / (((k - (n + 1) : ℕ) : ℝ) * siteGap c' k) ^ 2 :=
            div_le_div₀ (by positivity) h_num (by positivity) h_sq_dist
        _ = (1 / 16 : ℝ) / ((k - (n + 1) : ℕ) : ℝ) ^ 2 := by
            field_simp [hgk_pos.ne', hm_pos.ne']
    have h_chi_le : chiQuantile c' k ≤ chiQuantile c' (k + 1 : ℕ) := by
      unfold siteGap at hgk_pos; push_cast; linarith
    have h_gap_eq : chiQuantile c' (k + 1 : ℕ) - chiQuantile c' k = siteGap c' k := by
      unfold siteGap; push_cast; ring
    have h_int_lb : siteGap c' k * Real.exp (-π * (chiQuantile c' (k + 1 : ℕ) - chiQuantile c' (n + 1 : ℕ))) ≤
        ∫ t in (chiQuantile c' k)..(chiQuantile c' (k + 1 : ℕ)),
          Real.exp (-π * (t - chiQuantile c' (n + 1 : ℕ))) := by
      have hcont : Continuous (fun t : ℝ => Real.exp (-π * (t - chiQuantile c' (n + 1 : ℕ)))) :=
        Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))
      have hm := intervalIntegral.integral_mono_on
        (f := fun _ => Real.exp (-π * (chiQuantile c' (k + 1 : ℕ) - chiQuantile c' (n + 1 : ℕ))))
        h_chi_le (intervalIntegrable_const (μ := volume))
        (hcont.intervalIntegrable _ _) fun t ht => by
          apply Real.exp_le_exp.mpr
          nlinarith [Real.pi_pos, ht.2]
      rw [intervalIntegral.integral_const, smul_eq_mul, h_gap_eq] at hm
      exact hm
    have h_exp_shift : Real.exp (-π * |x - chiQuantile c' k|) ≤
        Real.exp (π / 2) * Real.exp (-π * (chiQuantile c' (k + 1 : ℕ) - chiQuantile c' (n + 1 : ℕ))) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      rw [abs_of_neg (sub_neg.mpr hχk_gt), neg_sub]
      nlinarith [Real.pi_pos, hx.2]
    have h_sq_le : (η₀ * siteGap c' k) ^ 2 ≤ (1 / 32 : ℝ) * siteGap c' k := by
      have h1 : η₀ ^ 2 * siteGap c' k ≤ (1 / 16 : ℝ) * (1 / 2 : ℝ) := by nlinarith
      calc (η₀ * siteGap c' k) ^ 2 = (η₀ ^ 2 * siteGap c' k) * siteGap c' k := by ring
        _ ≤ (1 / 32 : ℝ) * siteGap c' k := mul_le_mul_of_nonneg_right (by linarith) hgk_pos.le
    have h_exp_bd : C_δ * (η₀ * siteGap c' k) ^ 2 * Real.exp (-π * |x - chiQuantile c' k|) ≤
        C_δ * (1 / 32 : ℝ) * Real.exp (π / 2) *
          ∫ t in (chiQuantile c' k)..(chiQuantile c' (k + 1 : ℕ)),
            Real.exp (-π * (t - chiQuantile c' (n + 1 : ℕ))) := by
      calc C_δ * (η₀ * siteGap c' k) ^ 2 * Real.exp (-π * |x - chiQuantile c' k|)
          ≤ C_δ * ((1 / 32 : ℝ) * siteGap c' k) *
              (Real.exp (π / 2) * Real.exp (-π * (chiQuantile c' (k + 1 : ℕ) - chiQuantile c' (n + 1 : ℕ)))) := by
              gcongr
        _ = C_δ * (1 / 32 : ℝ) * Real.exp (π / 2) *
              (siteGap c' k * Real.exp (-π * (chiQuantile c' (k + 1 : ℕ) - chiQuantile c' (n + 1 : ℕ)))) := by ring
        _ ≤ C_δ * (1 / 32 : ℝ) * Real.exp (π / 2) *
              ∫ t in (chiQuantile c' k)..(chiQuantile c' (k + 1 : ℕ)),
                Real.exp (-π * (t - chiQuantile c' (n + 1 : ℕ))) := by gcongr
    exact hd_bd.trans (add_le_add h_alg h_exp_bd)
  have h_sum_alg : (∑ k ∈ Finset.Icc (n + j + 1) K, (1 / 16 : ℝ) / ((k - (n + 1) : ℕ) : ℝ) ^ 2) ≤ 1 / 8 := by
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc_left (b := K) (by omega : n + 2 ≤ n + j + 1))
      (f := fun k => (1 / 16 : ℝ) / ((k - (n + 1) : ℕ) : ℝ) ^ 2) (fun _ _ _ => by positivity)
    have h_bij : Finset.Icc (n + 2) K = (Finset.Icc 1 (K - (n + 1))).image (fun m => n + 1 + m) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_image]
      constructor
      · intro ⟨h1, h2⟩; exact ⟨k - (n + 1), ⟨by omega, by omega⟩, by omega⟩
      · rintro ⟨m, ⟨hm1, hm2⟩, rfl⟩; omega
    rw [h_bij, Finset.sum_image (fun a _ b _ h => by omega)] at hsub
    have h_rew : ∑ m ∈ Finset.Icc 1 (K - (n + 1)), (1 / 16 : ℝ) / ((n + 1 + m - (n + 1) : ℕ) : ℝ) ^ 2 =
        (1 / 16 : ℝ) * ∑ m ∈ Finset.Icc 1 (K - (n + 1)), (1 : ℝ) / (m : ℝ) ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => ?_
      have heq : n + 1 + m - (n + 1) = m := by omega
      rw [heq]; ring
    rw [h_rew] at hsub
    linarith [sum_Icc_inv_sq_le (K - (n + 1))]
  have h_sum_exp :
      (∑ k ∈ Finset.Icc (n + j + 1) K, C_δ * (1 / 32 : ℝ) * Real.exp (π / 2) *
        ∫ t in (chiQuantile c' k)..(chiQuantile c' (k + 1 : ℕ)),
          Real.exp (-π * (t - chiQuantile c' (n + 1 : ℕ)))) ≤
        C_δ / (32 * π) * Real.exp (π / 2) := by
    rw [← Finset.mul_sum]
    have h_tele_int : ∀ M ≥ n + j + 1,
        (∑ k ∈ Finset.Icc (n + j + 1) M,
          ∫ t in (chiQuantile c' k)..(chiQuantile c' (k + 1 : ℕ)),
            Real.exp (-π * (t - chiQuantile c' (n + 1 : ℕ)))) =
          ∫ t in (chiQuantile c' (n + j + 1))..(chiQuantile c' (M + 1 : ℕ)),
            Real.exp (-π * (t - chiQuantile c' (n + 1 : ℕ))) := by
      intro M hM
      induction M, hM using Nat.le_induction with
      | base => simp [Finset.Icc_self]
      | succ M hM ih =>
        have hsub : Finset.Icc (n + j + 1) (M + 1) = insert (M + 1) (Finset.Icc (n + j + 1) M) := by
          ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hsub, Finset.sum_insert (by simp), ih, add_comm]
        have hcont : Continuous (fun t : ℝ => Real.exp (-π * (t - chiQuantile c' (n + 1 : ℕ)))) :=
          Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))
        exact intervalIntegral.integral_add_adjacent_intervals
          (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
    rw [h_tele_int K hK]
    have hcont : Continuous (fun t : ℝ => Real.exp (-π * (t - chiQuantile c' (n + 1 : ℕ)))) :=
      Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))
    have hd : ∀ t ∈ uIcc (chiQuantile c' (n + j + 1)) (chiQuantile c' (K + 1 : ℕ)),
        HasDerivAt (fun s : ℝ => -(Real.exp (-π * (s - chiQuantile c' (n + 1 : ℕ))) / π))
          (Real.exp (-π * (t - chiQuantile c' (n + 1 : ℕ)))) t := fun t _ => by
      have h1 := ((hasDerivAt_id t).sub_const (chiQuantile c' (n + 1 : ℕ))).const_mul (-π)
      have h2 := (h1.exp.div_const π).neg
      refine h2.congr_deriv ?_
      have h_id : -π * (id t - chiQuantile c' (n + 1 : ℕ)) = -π * (t - chiQuantile c' (n + 1 : ℕ)) := rfl
      rw [h_id]
      field_simp [Real.pi_ne_zero]
    have h_eval : ∫ t in (chiQuantile c' (n + j + 1))..(chiQuantile c' (K + 1 : ℕ)),
        Real.exp (-π * (t - chiQuantile c' (n + 1 : ℕ))) ≤ 1 / π := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)]
      have h_ge_0 : 0 ≤ chiQuantile c' (n + j + 1) - chiQuantile c' (n + 1 : ℕ) := by
        have h1 : (2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ n + 1)
        have h2 : (2 : ℝ) ≤ ((n + j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ n + j + 1)
        have hle := (chiQuantile_strictMonoOn hc').monotoneOn
          (a := ((n + 1 : ℕ) : ℝ)) (b := ((n + j + 1 : ℕ) : ℝ))
          (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith))
          (by exact_mod_cast (by omega : n + 1 ≤ n + j + 1))
        push_cast at hle ⊢
        linarith
      have h_exp1 : Real.exp (-π * (chiQuantile c' (n + j + 1) - chiQuantile c' (n + 1 : ℕ))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
      have h_exp2 : 0 ≤ Real.exp (-π * (chiQuantile c' (K + 1 : ℕ) - chiQuantile c' (n + 1 : ℕ))) :=
        (Real.exp_pos _).le
      linarith [div_nonneg h_exp2 Real.pi_pos.le, div_le_div_of_nonneg_right h_exp1 Real.pi_pos.le]
    have hcoef_nn : 0 ≤ C_δ * (1 / 32 : ℝ) * Real.exp (π / 2) := by positivity
    calc C_δ * (1 / 32 : ℝ) * Real.exp (π / 2) * _
        ≤ C_δ * (1 / 32 : ℝ) * Real.exp (π / 2) * (1 / π) := mul_le_mul_of_nonneg_left h_eval hcoef_nn
      _ = C_δ / (32 * π) * Real.exp (π / 2) := by ring
  calc ∑ k ∈ Finset.Icc (n + j + 1) K, deltaDetune (chiQuantile c' k) (η₀ * siteGap c' k) x
      ≤ ∑ k ∈ Finset.Icc (n + j + 1) K,
          ((1 / 16 : ℝ) / ((k - (n + 1) : ℕ) : ℝ) ^ 2 +
            C_δ * (1 / 32 : ℝ) * Real.exp (π / 2) *
              ∫ t in (chiQuantile c' k)..(chiQuantile c' (k + 1 : ℕ)),
                Real.exp (-π * (t - chiQuantile c' (n + 1 : ℕ)))) := Finset.sum_le_sum h_term
    _ = (∑ k ∈ Finset.Icc (n + j + 1) K, (1 / 16 : ℝ) / ((k - (n + 1) : ℕ) : ℝ) ^ 2) +
          ∑ k ∈ Finset.Icc (n + j + 1) K, C_δ * (1 / 32 : ℝ) * Real.exp (π / 2) *
            ∫ t in (chiQuantile c' k)..(chiQuantile c' (k + 1 : ℕ)),
              Real.exp (-π * (t - chiQuantile c' (n + 1 : ℕ))) := Finset.sum_add_distrib
    _ ≤ 1 / 8 + C_δ / (32 * π) * Real.exp (π / 2) := add_le_add h_sum_alg h_sum_exp

private lemma right_sum_upper_K4 {c' η₀ x C_δ : ℝ} (hc' : 0 < c') (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4)
    (hgap : siteGap c' 1 ≤ 1 / 2) (hC_δ : 0 < C_δ)
    (hdet : ∀ {χ ε x : ℝ}, xiStar ≤ χ → 0 ≤ x → x ≠ χ → 0 ≤ ε → ε ≤ 1 / 8 →
      deltaDetune χ ε x ≤ ε ^ 2 / (x - χ) ^ 2 + C_δ * ε ^ 2 * Real.exp (-π * |x - χ|))
    {n j K : ℕ} (hj : 1 ≤ j) (hn3 : 3 ≤ n) (hK : n + j ≤ K) (hx : inCell c' n x) :
    (∑ k ∈ Finset.Icc (n + j + 1) K,
        (Real.log (pairModQ c' η₀ x k) - 2 * ∫ a in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), phiVar c' x a)) ≤
      (1 / 2 + π / 4) + (1 / 8 + C_δ / (32 * π) * Real.exp (π / 2)) := by
  by_cases h_emp : K < n + j + 1
  · have he : Finset.Icc (n + j + 1) K = ∅ := Finset.Icc_eq_empty (by omega)
    rw [he, Finset.sum_empty]
    positivity [Real.pi_pos]
  push Not at h_emp
  have h_split : (∑ k ∈ Finset.Icc (n + j + 1) K,
        (Real.log (pairModQ c' η₀ x k) - 2 * ∫ a in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), phiVar c' x a)) =
      (∑ k ∈ Finset.Icc (n + j + 1) K,
        (2 * phiVar c' x k - 2 * ∫ a in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), phiVar c' x a)) +
        ∑ k ∈ Finset.Icc (n + j + 1) K, deltaDetune (chiQuantile c' k) (η₀ * siteGap c' k) x := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk_mem := Finset.mem_Icc.mp hk
    rw [log_pairModQ_eq_phiVar_add_delta hc' hη₀0 hη₀1 hgap (by omega) hx (by omega)]
    ring
  rw [h_split]
  exact add_le_add (right_midpoint_upper_K4 hc' hgap hj hn3 h_emp hx)
    (right_detune_upper_K4 hc' hη₀0 hη₀1 hgap hC_δ @hdet hj (by omega) h_emp hx)

private lemma left_chiDeriv_sq_div_le {c' x : ℝ} (hc' : 0 < c') {n k : ℕ}
    (hk2 : 2 ≤ k) (hkn : k ≤ n - 1) (hx : inCell c' n x) {a : ℝ}
    (ha : a ∈ Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2)) :
    chiDeriv c' a ^ 2 / (x - chiQuantile c' a) ^ 2 ≤
      if siteRadius c' ((k : ℝ) + 1 / 2) ≤ (x - xiStar) / 2
      then 144 * siteGap c' k / (x - xiStar)
      else 144 / ((n - k : ℕ) : ℝ) ^ 2 := by
  have hk_r : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hkn_r : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : k + 1 ≤ n)
  have ha14 : 1 / 4 < a := by linarith [ha.1]
  have hca := (chiDeriv_le_six_siteGap hc' hk2 ha.1 (ha.2.trans (by linarith))).1
  have h2gap := (chiDeriv_le_six_siteGap hc' hk2 (by linarith : (k : ℝ) - 1 / 2 ≤ (k : ℝ) + 1 / 2)
    (by linarith)).2
  have hχa_le : chiQuantile c' a ≤ chiQuantile c' ((k : ℝ) + 1 / 2) := by
    rcases eq_or_lt_of_le ha.2 with rfl | hlt
    · exact le_rfl
    · exact (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr ha14.le)
        (Set.mem_Ici.mpr (by linarith)) hlt).le
  have hχk12_lt : chiQuantile c' ((k : ℝ) + 1 / 2) < x :=
    (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith))
      (Set.mem_Ici.mpr (by linarith)) (by linarith)).trans_le hx.1
  have hx_xi : xiStar < x := (xiStar_lt_chiQuantile hc' ha14).trans (hχa_le.trans_lt hχk12_lt)
  have hs_pos : 0 < x - xiStar := sub_pos.mpr hx_xi
  have hcd_pos := chiDeriv_pos hc' ha14
  split_ifs with hrad
  · have h_xa_ge : (x - xiStar) / 2 ≤ x - chiQuantile c' a := by
      have h_k12 : x - chiQuantile c' ((k : ℝ) + 1 / 2) = (x - xiStar) - siteRadius c' ((k : ℝ) + 1 / 2) := by
        unfold siteRadius; ring
      linarith
    have h_sq_ge : ((x - xiStar) / 2) ^ 2 ≤ (x - chiQuantile c' a) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h_xa_ge 2
    have h_cd_le : chiDeriv c' a ≤ 6 * siteGap c' k := hca.trans (by linarith)
    have h_gap_le_s : siteGap c' k ≤ x - xiStar := by
      unfold siteGap
      have hχk_ge : xiStar ≤ chiQuantile c' k := (chiQuantile_spec hc' (by linarith)).1
      have hχk1_le : chiQuantile c' ((k : ℝ) + 1) ≤ chiQuantile c' n := by
        rcases eq_or_lt_of_le hkn_r with heq | hlt
        · rw [heq]
        · exact (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith))
            (Set.mem_Ici.mpr (by linarith)) hlt).le
      linarith [hx.1]
    have h_gap_nn : 0 ≤ siteGap c' k := by
      unfold siteGap
      exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn
        (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith)) (by linarith))
    calc chiDeriv c' a ^ 2 / (x - chiQuantile c' a) ^ 2
        ≤ (6 * siteGap c' k) ^ 2 / ((x - xiStar) / 2) ^ 2 :=
          div_le_div₀ (by positivity) (pow_le_pow_left₀ hcd_pos.le h_cd_le 2) (by positivity) h_sq_ge
      _ = 144 * (siteGap c' k / (x - xiStar)) * (siteGap c' k / (x - xiStar)) := by
          field_simp [hs_pos.ne']; ring
      _ ≤ 144 * (siteGap c' k / (x - xiStar)) * 1 := by
          gcongr; rwa [div_le_one hs_pos]
      _ = 144 * siteGap c' k / (x - xiStar) := by ring
  · push Not at hrad
    have hrn_lt : siteRadius c' ((k : ℝ) + 1 / 2) < siteRadius c' n := by
      unfold siteRadius
      linarith [chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith))
        (Set.mem_Ici.mpr (by linarith)) (by linarith : (k : ℝ) + 1 / 2 < (n : ℝ))]
    have hrn_pos : 0 < siteRadius c' n := sub_pos.mpr (xiStar_lt_chiQuantile hc' (by linarith))
    have hrk12_pos : 0 < siteRadius c' ((k : ℝ) + 1 / 2) :=
      sub_pos.mpr (xiStar_lt_chiQuantile hc' (by linarith))
    let θ := siteRadius c' ((k : ℝ) + 1 / 2) / siteRadius c' n
    have hθ0 : 0 ≤ 1 - θ := sub_nonneg.mpr ((div_le_one hrn_pos).mpr hrn_lt.le)
    have hθ1 : 0 ≤ θ := div_nonneg hrk12_pos.le hrn_pos.le
    have hθ_sum : (1 - θ) + θ = 1 := by ring
    have h_pt_eq : (1 - θ) • xiStar + θ • chiQuantile c' n = chiQuantile c' ((k : ℝ) + 1 / 2) := by
      rw [smul_eq_mul, smul_eq_mul]
      dsimp [θ]
      unfold siteRadius
      have hden_ne : chiQuantile c' n - xiStar ≠ 0 :=
        (sub_pos.mpr (xiStar_lt_chiQuantile hc' (by linarith))).ne'
      field_simp [hden_ne]
      ring
    have h_conc := rhoU_strictConcaveOn.concaveOn.2
      (Set.mem_Ici.mpr le_rfl)
      (Set.mem_Ici.mpr (xiStar_lt_chiQuantile hc' (by linarith : (1 / 4 : ℝ) < (n : ℝ))).le)
      hθ0 hθ1 hθ_sum
    rw [h_pt_eq, smul_eq_mul, smul_eq_mul, rhoU_xiStar, mul_zero, zero_add] at h_conc
    have hrn_le_s : siteRadius c' n ≤ x - xiStar := by unfold siteRadius; linarith [hx.1]
    have hθ_ge_half : (1 / 2 : ℝ) ≤ θ := by
      dsimp [θ]; rw [le_div_iff₀ hrn_pos]; linarith
    have hρn_pos : 0 < rhoU (chiQuantile c' n) := rhoU_pos (xiStar_lt_chiQuantile hc' (by linarith))
    have hρ_k12_ge : (1 / 2 : ℝ) * rhoU (chiQuantile c' n) ≤ rhoU (chiQuantile c' ((k : ℝ) + 1 / 2)) :=
      (mul_le_mul_of_nonneg_right hθ_ge_half hρn_pos.le).trans h_conc
    have hcd_k12_le : chiDeriv c' ((k : ℝ) + 1 / 2) ≤ 2 * chiDeriv c' n := by
      unfold chiDeriv
      have hden : 0 < c' * ((1 / 2 : ℝ) * rhoU (chiQuantile c' n)) := by positivity
      calc 2 / (c' * rhoU (chiQuantile c' ((k : ℝ) + 1 / 2)))
          ≤ 2 / (c' * ((1 / 2 : ℝ) * rhoU (chiQuantile c' n))) :=
            div_le_div_of_nonneg_left two_pos.le hden (mul_le_mul_of_nonneg_left hρ_k12_ge hc'.le)
        _ = 2 * (2 / (c' * rhoU (chiQuantile c' n))) := by ring
    have h_diff_ge : ((n : ℝ) - (k : ℝ) - 1 / 2) * chiDeriv c' n ≤ x - chiQuantile c' a := by
      have h_le_kn : (k : ℝ) + 1 / 2 ≤ (n : ℝ) := by linarith
      have hcont : ContinuousOn (chiDeriv c') (Icc ((k : ℝ) + 1 / 2) (n : ℝ)) := fun t ht =>
        (hasDerivAt_chiQuantile hc' (by linarith [ht.1])).2.continuousAt.continuousWithinAt
      have h_int : chiQuantile c' n - chiQuantile c' ((k : ℝ) + 1 / 2) =
          ∫ t in ((k : ℝ) + 1 / 2)..(n : ℝ), chiDeriv c' t := by
        refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => ?_)
          (hcont.intervalIntegrable_of_Icc h_le_kn)).symm
        rw [Set.uIcc_of_le h_le_kn] at ht
        exact (hasDerivAt_chiQuantile hc' (by linarith [ht.1])).1
      have hm := intervalIntegral.integral_mono_on h_le_kn (intervalIntegrable_const (μ := volume))
        (hcont.intervalIntegrable_of_Icc h_le_kn) fun t ht => by
          rcases eq_or_lt_of_le ht.2 with rfl | hlt
          · exact le_rfl
          · exact (chiDeriv_strictAntiOn hc' (Set.mem_Ioi.mpr (by linarith [ht.1]))
              (Set.mem_Ioi.mpr (by linarith)) hlt).le
      rw [intervalIntegral.integral_const, smul_eq_mul, ← h_int] at hm
      linarith [hx.1]
    have h_nk_pos : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - k)
    have h_nk_ge1 : (1 : ℝ) ≤ ((n - k : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n - k)
    have h_cast : (n : ℝ) - (k : ℝ) = ((n - k : ℕ) : ℝ) := (Nat.cast_sub (by omega : k ≤ n)).symm
    have h_len_ge : (1 / 2 : ℝ) * ((n - k : ℕ) : ℝ) ≤ (n : ℝ) - (k : ℝ) - 1 / 2 := by
      rw [h_cast]; linarith
    have hcdn_pos := chiDeriv_pos hc' (by linarith : 1 / 4 < (n : ℝ))
    have h_xa_ge2 : (1 / 2 : ℝ) * ((n - k : ℕ) : ℝ) * chiDeriv c' n ≤ x - chiQuantile c' a :=
      (mul_le_mul_of_nonneg_right h_len_ge hcdn_pos.le).trans h_diff_ge
    have h_ca_le2 : chiDeriv c' a ≤ 6 * chiDeriv c' n := hca.trans (by linarith)
    calc chiDeriv c' a ^ 2 / (x - chiQuantile c' a) ^ 2
        ≤ (6 * chiDeriv c' n) ^ 2 / ((1 / 2 : ℝ) * ((n - k : ℕ) : ℝ) * chiDeriv c' n) ^ 2 :=
          div_le_div₀ (by positivity) (pow_le_pow_left₀ hcd_pos.le h_ca_le2 2)
            (by positivity) (pow_le_pow_left₀ (by positivity) h_xa_ge2 2)
      _ = 144 / ((n - k : ℕ) : ℝ) ^ 2 := by
          field_simp [hcdn_pos.ne', h_nk_pos.ne']; ring

private lemma left_B_sum_le {c' x : ℝ} (hc' : 0 < c') {f n j : ℕ}
    (hf : 1 ≤ f) (hj : 1 ≤ j) (hfnj : f + j ≤ n) (hx : inCell c' n x) :
    (∑ k ∈ Finset.Icc (f + 1) (n - j),
      if siteRadius c' ((k : ℝ) + 1 / 2) ≤ (x - xiStar) / 2
      then 144 * siteGap c' k / (x - xiStar)
      else 144 / ((n - k : ℕ) : ℝ) ^ 2) ≤ 144 + 288 := by
  classical
  let s := x - xiStar
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hs_pos : 0 < s := sub_pos.mpr ((xiStar_lt_chiQuantile hc' (by linarith)).trans_le hx.1)
  let L : Finset ℕ := Finset.Icc (f + 1) (n - j)
  let B : ℕ → ℝ := fun k =>
    if siteRadius c' ((k : ℝ) + 1 / 2) ≤ s / 2 then 144 * siteGap c' k / s
    else 144 / ((n - k : ℕ) : ℝ) ^ 2
  let L1 : Finset ℕ := L.filter (fun k : ℕ => siteRadius c' ((k : ℝ) + 1 / 2) ≤ s / 2)
  let L2 : Finset ℕ := L.filter (fun k : ℕ => ¬ siteRadius c' ((k : ℝ) + 1 / 2) ≤ s / 2)
  have hsplit_B : ∑ k ∈ L, B k = (∑ k ∈ L1, 144 * siteGap c' k / s) +
      ∑ k ∈ L2, 144 / ((n - k : ℕ) : ℝ) ^ 2 := by
    have h := Finset.sum_filter_add_sum_filter_not L (fun k : ℕ => siteRadius c' ((k : ℝ) + 1 / 2) ≤ s / 2) B
    rw [← h]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      dsimp [B]; split_ifs with hcond
      · rfl
      · exact absurd (Finset.mem_filter.mp hk).2 hcond
    · refine Finset.sum_congr rfl fun k hk => ?_
      dsimp [B]; split_ifs with hcond
      · exact absurd hcond (Finset.mem_filter.mp hk).2
      · rfl
  have hL1_bd : ∑ k ∈ L1, 144 * siteGap c' k / s ≤ 144 := by
    have hsub : L1 ⊆ Finset.Icc (f + 1) (n - 1) :=
      (Finset.filter_subset _ _).trans (Finset.Icc_subset_Icc_right (by omega))
    have h_nonneg : ∀ k ∈ Finset.Icc (f + 1) (n - 1), 0 ≤ 144 * siteGap c' k / s := fun k hk => by
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by have := (Finset.mem_Icc.mp hk).1; omega : 1 ≤ k)
      have hgk : 0 ≤ siteGap c' k := by
        unfold siteGap
        exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn
          (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith)) (by linarith))
      positivity
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub fun k hk _ => h_nonneg k hk
    have hsum_gap : ∑ k ∈ Finset.Icc (f + 1) (n - 1), siteGap c' k ≤ s := by
      by_cases hf_n1 : f + 1 ≤ n - 1
      · have h_tele_m : ∀ M ≥ f + 1, ∑ k ∈ Finset.Icc (f + 1) M, siteGap c' k =
            chiQuantile c' (M + 1 : ℕ) - chiQuantile c' (f + 1 : ℕ) := by
          intro M hM
          induction M, hM using Nat.le_induction with
          | base => simp only [Finset.Icc_self, Finset.sum_singleton]; unfold siteGap; push_cast; ring
          | succ M hM ih =>
            have hsub2 : Finset.Icc (f + 1) (M + 1) = insert (M + 1) (Finset.Icc (f + 1) M) := by
              ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            rw [hsub2, Finset.sum_insert (by simp), ih]
            unfold siteGap; push_cast; ring
        have heq : n - 1 + 1 = n := by omega
        rw [h_tele_m (n - 1) hf_n1, heq]
        have hf1_2 : (2 : ℝ) ≤ ((f + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ f + 1)
        have hχ_ge := (chiQuantile_spec hc' (by linarith : (1 / 4 : ℝ) ≤ ((f + 1 : ℕ) : ℝ))).1
        dsimp [s]; linarith [hx.1]
      · have he : Finset.Icc (f + 1) (n - 1) = ∅ := Finset.Icc_eq_empty (by omega)
        rw [he, Finset.sum_empty]; exact hs_pos.le
    have h_rew : ∑ k ∈ Finset.Icc (f + 1) (n - 1), 144 * siteGap c' k / s =
        (144 / s) * ∑ k ∈ Finset.Icc (f + 1) (n - 1), siteGap c' k := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
    refine h1.trans ?_
    rw [h_rew]
    calc (144 / s) * ∑ k ∈ Finset.Icc (f + 1) (n - 1), siteGap c' k
        ≤ (144 / s) * s := mul_le_mul_of_nonneg_left hsum_gap (by positivity)
      _ = 144 := by field_simp [hs_pos.ne']
  have hL2_bd : ∑ k ∈ L2, 144 / ((n - k : ℕ) : ℝ) ^ 2 ≤ 288 := by
    have h_map : Finset.image (fun k : ℕ => n - k) L2 ⊆ Finset.Icc 1 n := by
      intro m hm
      rw [Finset.mem_image] at hm
      rcases hm with ⟨k, hk, rfl⟩
      have hkL := Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have h1 := Finset.sum_le_sum_of_injOn (fun k : ℕ => n - k)
      (by
        intro k₁ h1 k₂ h2 heq
        dsimp only at heq
        have hk1 := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_coe.mp h1)).1
        have hk2 := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_coe.mp h2)).1
        omega)
      h_map (fun k _ => le_rfl) (fun m _ _ => by positivity)
      (f := fun k : ℕ => 144 / ((n - k : ℕ) : ℝ) ^ 2)
      (g := fun m : ℕ => (144 : ℝ) / (m : ℝ) ^ 2)
    have h_rew : ∑ m ∈ Finset.Icc 1 n, (144 : ℝ) / (m : ℝ) ^ 2 =
        144 * ∑ m ∈ Finset.Icc 1 n, (1 : ℝ) / (m : ℝ) ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => by ring
    rw [h_rew] at h1
    linarith [sum_Icc_inv_sq_le n]
  change ∑ k ∈ L, B k ≤ 144 + 288
  rw [hsplit_B]; linarith

private lemma left_sum_upper_K4 {c' η₀ x C_neg C_δ : ℝ} (hc' : 0 < c') (hη₀0 : 0 ≤ η₀)
    (hη₀1 : η₀ ≤ 1 / 4) (hgap : siteGap c' 1 ≤ 1 / 2) (hC_neg : 0 < C_neg) (hC_δ : 0 < C_δ)
    (hneg : ∀ {c' x a : ℝ}, 0 < c' → 1 / 4 < a → chiQuantile c' a < x →
      -phiVarSecond c' x a ≤ C_neg * chiDeriv c' a ^ 2 / (x - chiQuantile c' a) ^ 2)
    (hdet : ∀ {χ ε x : ℝ}, xiStar ≤ χ → 0 ≤ x → x ≠ χ → 0 ≤ ε → ε ≤ 1 / 8 →
      deltaDetune χ ε x ≤ ε ^ 2 / (x - χ) ^ 2 + C_δ * ε ^ 2 * Real.exp (-π * |x - χ|))
    {f n j : ℕ} (hf : 1 ≤ f) (hj : 1 ≤ j) (hfnj : f + j ≤ n) (hx : inCell c' n x) :
    (∑ k ∈ Finset.Icc (f + 1) (n - j),
        (Real.log (pairModQ c' η₀ x k) - 2 * ∫ a in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), phiVar c' x a)) ≤
      (C_neg / 12 + 1 / 16) * (144 + 288) + C_δ / (32 * π) := by
  let L : Finset ℕ := Finset.Icc (f + 1) (n - j)
  have h_split : (∑ k ∈ L, (Real.log (pairModQ c' η₀ x k) -
        2 * ∫ a in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), phiVar c' x a)) =
      (∑ k ∈ L, (2 * phiVar c' x k -
        2 * ∫ a in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), phiVar c' x a)) +
        ∑ k ∈ L, deltaDetune (chiQuantile c' k) (η₀ * siteGap c' k) x := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk_mem := Finset.mem_Icc.mp hk
    rw [log_pairModQ_eq_phiVar_add_delta hc' hη₀0 hη₀1 hgap (by omega) hx (by omega)]
    ring
  rw [h_split]
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hx0 : 0 ≤ x := (xiStar_pos.le.trans (chiQuantile_spec hc' (by linarith)).1).trans hx.1
  let B : ℕ → ℝ := fun k =>
    if siteRadius c' ((k : ℝ) + 1 / 2) ≤ (x - xiStar) / 2
    then 144 * siteGap c' k / (x - xiStar)
    else 144 / ((n - k : ℕ) : ℝ) ^ 2
  have hB_sum : ∑ k ∈ L, B k ≤ 144 + 288 := left_B_sum_le hc' hf hj hfnj hx
  have h_mid_bd : (∑ k ∈ L, (2 * phiVar c' x k -
      2 * ∫ a in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), phiVar c' x a)) ≤
      (C_neg / 12) * ∑ k ∈ L, B k := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk_mem := Finset.mem_Icc.mp hk
    have hk2 : 2 ≤ k := by omega
    have hkn : k ≤ n - 1 := by omega
    have hk2_r : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    have ha14 : 1 / 4 < (k : ℝ) - 1 / 2 := by linarith
    have hχ_lt_Icc : ∀ a ∈ Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2), chiQuantile c' a < x := fun a ha => by
      have h_kn : (k : ℝ) + 1 / 2 < (n : ℝ) := by
        have : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : k + 1 ≤ n)
        linarith
      have hle := (chiQuantile_strictMonoOn hc').monotoneOn
        (Set.mem_Ici.mpr (ha14.le.trans ha.1)) (Set.mem_Ici.mpr (by linarith)) ha.2
      have hlt := chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith))
        (Set.mem_Ici.mpr (by linarith)) h_kn
      exact (hle.trans_lt hlt).trans_le hx.1
    have hne_Icc : ∀ a ∈ Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2), chiQuantile c' a ≠ x := fun a ha =>
      (hχ_lt_Icc a ha).ne
    have hpeano := midpoint_peano_le
      (g := phiVar c' x) (g' := phiVarDeriv c' x) (g'' := phiVarSecond c' x)
      (k := (k : ℝ)) (M := C_neg * B k)
      (fun t ht => (phiVar_hasDerivAt hc' hx0 (lt_of_lt_of_le ha14 ht.1) (hne_Icc t ht)).1)
      (fun t ht => (phiVar_hasDerivAt hc' hx0 (lt_of_lt_of_le ha14 ht.1) (hne_Icc t ht)).2)
      (continuousOn_phiVarSecond hc' hx0 ha14 (by linarith) hne_Icc)
      (fun a ha => by
        have h1 : -phiVarSecond c' x a ≤ C_neg * (chiDeriv c' a ^ 2 / (x - chiQuantile c' a) ^ 2) := by
          simpa only [mul_div_assoc] using hneg hc' (lt_of_lt_of_le ha14 ha.1) (hχ_lt_Icc a ha)
        have h2 := left_chiDeriv_sq_div_le hc' hk2 hkn hx ha
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hC_neg.le))
    linarith
  have h_det_term : ∀ k ∈ L,
      deltaDetune (chiQuantile c' k) (η₀ * siteGap c' k) x ≤
        (1 / 16 : ℝ) * B k + C_δ * (1 / 32 : ℝ) *
          ∫ t in (chiQuantile c' k)..(chiQuantile c' (k + 1 : ℕ)), Real.exp (-π * (x - t)) := by
    intro k hk
    have hk_mem := Finset.mem_Icc.mp hk
    have hk2 : 2 ≤ k := by omega
    have hkn : k ≤ n - 1 := by omega
    have hk_r : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    have hχk_xi : xiStar ≤ chiQuantile c' k := (chiQuantile_spec hc' (by linarith)).1
    have hχk_lt : chiQuantile c' k < x := by
      have hlt_n : (k : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : k < n)
      exact (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr (by linarith))
        (Set.mem_Ici.mpr (by linarith)) hlt_n).trans_le hx.1
    have hgk_nn : 0 ≤ siteGap c' k := by
      unfold siteGap
      exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn
        (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith)) (by linarith))
    have hgk_le : siteGap c' k ≤ siteGap c' 1 := by
      have hanti := (siteGap_strictAnti hc').antitone (show 0 ≤ k - 1 by omega)
      have heq : (k - 1) + 1 = k := by omega
      simpa [heq] using hanti
    have hd_bd := hdet hχk_xi hx0 hχk_lt.ne' (mul_nonneg hη₀0 hgk_nn) (by nlinarith)
    have h_gap_le_cd : siteGap c' k ≤ chiDeriv c' (k : ℝ) := by
      unfold siteGap
      have hcont : ContinuousOn (chiDeriv c') (Icc (k : ℝ) ((k : ℝ) + 1)) := fun t ht =>
        (hasDerivAt_chiQuantile hc' (by linarith [ht.1])).2.continuousAt.continuousWithinAt
      have h_int : chiQuantile c' ((k : ℝ) + 1) - chiQuantile c' (k : ℝ) =
          ∫ t in (k : ℝ)..((k : ℝ) + 1), chiDeriv c' t := by
        refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => ?_)
          (hcont.intervalIntegrable_of_Icc (by linarith))).symm
        rw [Set.uIcc_of_le (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)] at ht
        exact (hasDerivAt_chiQuantile hc' (by linarith [ht.1])).1
      have hm := intervalIntegral.integral_mono_on (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)
        (hcont.intervalIntegrable_of_Icc (by linarith)) (intervalIntegrable_const (μ := volume))
        fun t ht => by
          rcases eq_or_lt_of_le ht.1 with rfl | hgt
          · exact le_rfl
          · exact (chiDeriv_strictAntiOn hc' (Set.mem_Ioi.mpr (by linarith))
              (Set.mem_Ioi.mpr (by linarith [ht.1])) hgt).le
      rw [intervalIntegral.integral_const, smul_eq_mul, ← h_int] at hm
      linarith
    have h_Bk := left_chiDeriv_sq_div_le hc' hk2 hkn hx (a := (k : ℝ)) ⟨by linarith, by linarith⟩
    have h_alg : (η₀ * siteGap c' k) ^ 2 / (x - chiQuantile c' k) ^ 2 ≤ (1 / 16 : ℝ) * B k := by
      have hη_sq : η₀ ^ 2 ≤ 1 / 16 := by nlinarith
      have h1 : (η₀ * siteGap c' k) ^ 2 ≤ (1 / 16 : ℝ) * siteGap c' k ^ 2 := by
        calc (η₀ * siteGap c' k) ^ 2 = η₀ ^ 2 * siteGap c' k ^ 2 := by ring
          _ ≤ (1 / 16 : ℝ) * siteGap c' k ^ 2 := mul_le_mul_of_nonneg_right hη_sq (sq_nonneg _)
      calc (η₀ * siteGap c' k) ^ 2 / (x - chiQuantile c' k) ^ 2
          ≤ ((1 / 16 : ℝ) * siteGap c' k ^ 2) / (x - chiQuantile c' k) ^ 2 :=
            div_le_div_of_nonneg_right h1 (sq_nonneg _)
        _ = (1 / 16 : ℝ) * (siteGap c' k ^ 2 / (x - chiQuantile c' k) ^ 2) := by ring
        _ ≤ (1 / 16 : ℝ) * (chiDeriv c' (k : ℝ) ^ 2 / (x - chiQuantile c' (k : ℝ)) ^ 2) := by gcongr
        _ ≤ (1 / 16 : ℝ) * B k := by gcongr
    have h_chi_le : chiQuantile c' k ≤ chiQuantile c' (k + 1 : ℕ) := by
      unfold siteGap at hgk_nn; push_cast; linarith
    have h_gap_eq : chiQuantile c' (k + 1 : ℕ) - chiQuantile c' k = siteGap c' k := by
      unfold siteGap; push_cast; ring
    have h_int_lb : siteGap c' k * Real.exp (-π * (x - chiQuantile c' k)) ≤
        ∫ t in (chiQuantile c' k)..(chiQuantile c' (k + 1 : ℕ)), Real.exp (-π * (x - t)) := by
      have hcont : Continuous (fun t : ℝ => Real.exp (-π * (x - t))) :=
        Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))
      have hm := intervalIntegral.integral_mono_on
        (f := fun _ => Real.exp (-π * (x - chiQuantile c' k)))
        h_chi_le (intervalIntegrable_const (μ := volume))
        (hcont.intervalIntegrable _ _) fun t ht => by
          apply Real.exp_le_exp.mpr
          nlinarith [Real.pi_pos, ht.1]
      rw [intervalIntegral.integral_const, smul_eq_mul, h_gap_eq] at hm
      exact hm
    have h_sq_le : (η₀ * siteGap c' k) ^ 2 ≤ (1 / 32 : ℝ) * siteGap c' k := by
      have h1 : η₀ ^ 2 * siteGap c' k ≤ (1 / 16 : ℝ) * (1 / 2 : ℝ) := by nlinarith
      calc (η₀ * siteGap c' k) ^ 2 = (η₀ ^ 2 * siteGap c' k) * siteGap c' k := by ring
        _ ≤ (1 / 32 : ℝ) * siteGap c' k := mul_le_mul_of_nonneg_right (by linarith) hgk_nn
    have h_exp_bd : C_δ * (η₀ * siteGap c' k) ^ 2 * Real.exp (-π * |x - chiQuantile c' k|) ≤
        C_δ * (1 / 32 : ℝ) * ∫ t in (chiQuantile c' k)..(chiQuantile c' (k + 1 : ℕ)),
          Real.exp (-π * (x - t)) := by
      rw [abs_of_pos (sub_pos.mpr hχk_lt)]
      calc C_δ * (η₀ * siteGap c' k) ^ 2 * Real.exp (-π * (x - chiQuantile c' k))
          ≤ C_δ * ((1 / 32 : ℝ) * siteGap c' k) * Real.exp (-π * (x - chiQuantile c' k)) := by gcongr
        _ = C_δ * (1 / 32 : ℝ) * (siteGap c' k * Real.exp (-π * (x - chiQuantile c' k))) := by ring
        _ ≤ C_δ * (1 / 32 : ℝ) * ∫ t in (chiQuantile c' k)..(chiQuantile c' (k + 1 : ℕ)),
              Real.exp (-π * (x - t)) := by gcongr
    exact hd_bd.trans (add_le_add h_alg h_exp_bd)
  have h_exp_sum : (∑ k ∈ L, C_δ * (1 / 32 : ℝ) *
      ∫ t in (chiQuantile c' k)..(chiQuantile c' (k + 1 : ℕ)), Real.exp (-π * (x - t))) ≤
      C_δ / (32 * π) := by
    rw [← Finset.mul_sum]
    by_cases hL_ne : f + 1 ≤ n - j
    · have h_tele : ∀ M ≥ f + 1,
          (∑ k ∈ Finset.Icc (f + 1) M,
            ∫ t in (chiQuantile c' k)..(chiQuantile c' (k + 1 : ℕ)), Real.exp (-π * (x - t))) =
            ∫ t in (chiQuantile c' (f + 1))..(chiQuantile c' (M + 1 : ℕ)),
              Real.exp (-π * (x - t)) := by
        intro M hM
        induction M, hM using Nat.le_induction with
        | base => simp [Finset.Icc_self]
        | succ M hM ih =>
          have hsub : Finset.Icc (f + 1) (M + 1) = insert (M + 1) (Finset.Icc (f + 1) M) := by
            ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hsub, Finset.sum_insert (by simp), ih, add_comm]
          have hcont : Continuous (fun t : ℝ => Real.exp (-π * (x - t))) :=
            Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))
          exact intervalIntegral.integral_add_adjacent_intervals
            (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
      dsimp [L]
      rw [h_tele (n - j) hL_ne]
      have h_ub : chiQuantile c' (n - j + 1 : ℕ) ≤ x := by
        have h2 : (2 : ℝ) ≤ ((n - j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ n - j + 1)
        have hle : ((n - j + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : n - j + 1 ≤ n)
        exact ((chiQuantile_strictMonoOn hc').monotoneOn
          (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith)) hle).trans hx.1
      have hcont : Continuous (fun t : ℝ => Real.exp (-π * (x - t))) :=
        Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))
      have hd : ∀ t ∈ uIcc (chiQuantile c' (f + 1)) (chiQuantile c' (n - j + 1 : ℕ)),
          HasDerivAt (fun s : ℝ => Real.exp (-π * (x - s)) / π) (Real.exp (-π * (x - t))) t := fun t _ => by
        have h1 := ((hasDerivAt_id t).const_sub x).const_mul (-π)
        refine (h1.exp.div_const π).congr_deriv ?_
        have h_id : x - id t = x - t := rfl
        rw [h_id]
        field_simp [Real.pi_ne_zero]
      have h_eval : ∫ t in (chiQuantile c' (f + 1))..(chiQuantile c' (n - j + 1 : ℕ)),
          Real.exp (-π * (x - t)) ≤ 1 / π := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)]
        have h1 : Real.exp (-π * (x - chiQuantile c' (n - j + 1 : ℕ))) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
        have h2 : 0 ≤ Real.exp (-π * (x - chiQuantile c' (f + 1))) := (Real.exp_pos _).le
        calc Real.exp (-π * (x - chiQuantile c' (n - j + 1 : ℕ))) / π -
              Real.exp (-π * (x - chiQuantile c' (f + 1))) / π
            ≤ 1 / π - 0 := sub_le_sub (div_le_div_of_nonneg_right h1 Real.pi_pos.le)
              (div_nonneg h2 Real.pi_pos.le)
          _ = 1 / π := sub_zero _
      calc C_δ * (1 / 32 : ℝ) * _ ≤ C_δ * (1 / 32 : ℝ) * (1 / π) :=
            mul_le_mul_of_nonneg_left h_eval (by positivity)
        _ = C_δ / (32 * π) := by ring
    · have he : L = ∅ := Finset.Icc_eq_empty (by omega)
      rw [he, Finset.sum_empty, mul_zero]; positivity [Real.pi_pos]
  have h_det_bd : (∑ k ∈ L, deltaDetune (chiQuantile c' k) (η₀ * siteGap c' k) x) ≤
      (1 / 16 : ℝ) * (∑ k ∈ L, B k) + C_δ / (32 * π) := by
    calc ∑ k ∈ L, deltaDetune (chiQuantile c' k) (η₀ * siteGap c' k) x
        ≤ ∑ k ∈ L, ((1 / 16 : ℝ) * B k + C_δ * (1 / 32 : ℝ) *
            ∫ t in (chiQuantile c' k)..(chiQuantile c' (k + 1 : ℕ)), Real.exp (-π * (x - t))) :=
          Finset.sum_le_sum h_det_term
      _ = (1 / 16 : ℝ) * ∑ k ∈ L, B k + ∑ k ∈ L, C_δ * (1 / 32 : ℝ) *
            ∫ t in (chiQuantile c' k)..(chiQuantile c' (k + 1 : ℕ)), Real.exp (-π * (x - t)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ (1 / 16 : ℝ) * ∑ k ∈ L, B k + C_δ / (32 * π) := by linarith
  have hB1 : (C_neg / 12) * ∑ k ∈ L, B k ≤ (C_neg / 12) * (144 + 288) :=
    mul_le_mul_of_nonneg_left hB_sum (by positivity)
  have hB2 : (1 / 16 : ℝ) * ∑ k ∈ L, B k ≤ (1 / 16 : ℝ) * (144 + 288) :=
    mul_le_mul_of_nonneg_left hB_sum (by norm_num)
  linarith

/-- Logarithmic upper hole comparison (`cmb:K4` upper bound, `comb_estimates.tex`, line 146)
away from the zero $(\eta_0 = 0, x = \chi_n)$. -/
theorem hole_upper_K4_log :
    ∃ C_U > 0, ∀ᶠ c' in atTop, ∀ (f n j : ℕ) (η₀ x : ℝ),
      1 ≤ f → 1 ≤ j → max (f + j) (2 * j + 1) ≤ n →
        0 ≤ η₀ → η₀ ≤ 1 / 4 → inCell c' n x → (0 < η₀ ∨ x ≠ chiQuantile c' n) →
        Real.log ‖refComb c' f η₀ (x : ℂ)‖ + c' * slitL x ≤
          c' * combPf c' f x + holeH c' η₀ n j x + jEndComb c' x f + C_U := by
  obtain ⟨C_neg, hC_neg, hneg⟩ := neg_phiVarSecond_le_of_lt
  obtain ⟨C_δ, hC_δ, hdet⟩ := deltaDetune_le_of_xiStar_le
  obtain ⟨_, _, hgap_ev⟩ := siteGap_eventually_le
  let C_U : ℝ :=
    ((1 / 2 + π / 4) + (1 / 8 + C_δ / (32 * π) * Real.exp (π / 2))) +
      ((C_neg / 12 + 1 / 16) * (144 + 288) + C_δ / (32 * π))
  have hCU_pos : 0 < C_U := by dsimp [C_U]; positivity [Real.pi_pos]
  refine ⟨C_U, hCU_pos, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ), hgap_ev] with c' hc' hgap_all
  have hgap : siteGap c' 1 ≤ 1 / 2 := hgap_all.2.2.2
  intro f n j η₀ x hf hj h_max hη₀0 hη₀1 hx_cell hnz
  have hfnj : f + j ≤ n := (le_max_left _ _).trans h_max
  have hn_2j1 : 2 * j + 1 ≤ n := (le_max_right _ _).trans h_max
  have hn3 : 3 ≤ n := by omega
  have hn1 : f + 1 ≤ n := by omega
  have hx_xi : xiStar ≤ x := by
    have hn1_r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    exact (chiQuantile_spec hc' (by linarith)).1.trans hx_cell.1
  have h_lim := DK_limit hc' hx_xi hf hn1 hη₀0 hη₀1 hgap hx_cell hnz
  have h_ev : ∀ K ≥ n + j,
      phiVar c' x f + (∑ k ∈ Finset.Icc (f + 1) K, Real.log (pairModQ c' η₀ x k)) -
          2 * ∫ a in (f : ℝ)..((K : ℝ) + 1 / 2), phiVar c' x a ≤
        jEndComb c' x f + holeH c' η₀ n j x + C_U := by
    intro K hK
    rw [DK_split_identity hc' hf hj hfnj hK hx_cell]
    have hR := right_sum_upper_K4 hc' hη₀0 hη₀1 hgap hC_δ @hdet hj hn3 hK hx_cell
    have hL := left_sum_upper_K4 hc' hη₀0 hη₀1 hgap hC_neg hC_δ @hneg @hdet hf hj hfnj hx_cell
    dsimp [C_U]
    linarith
  have h_lim_le := le_of_tendsto h_lim (by
    filter_upwards [eventually_ge_atTop (n + j)] with K hK
    exact h_ev K hK)
  linarith

/-- Unconditional multiplicative upper hole comparison (`cmb:K4` upper bound),
valid for all $\eta_0 \in [0, \frac14]$ and all $x \in [\chi_n, \chi_{n+1})$. -/
theorem hole_upper_K4 :
    ∃ C_U > 0, ∀ᶠ c' in atTop, ∀ (f n j : ℕ) (η₀ x : ℝ),
      1 ≤ f → 1 ≤ j → max (f + j) (2 * j + 1) ≤ n →
        0 ≤ η₀ → η₀ ≤ 1 / 4 → inCell c' n x →
        ‖refComb c' f η₀ (x : ℂ)‖ * Real.exp (c' * slitL x) ≤
          Real.exp (c' * combPf c' f x + holeH c' η₀ n j x + jEndComb c' x f + C_U) := by
  obtain ⟨C_U, hCU, h_ev⟩ := hole_upper_K4_log
  refine ⟨C_U, hCU, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ), h_ev] with c' hc' hlog f n j η₀ x hf hj hmax hη₀0 hη₀1 hx_cell
  by_cases h0 : ‖refComb c' f η₀ (x : ℂ)‖ = 0
  · rw [h0, zero_mul]
    exact (Real.exp_pos _).le
  · have hnz : 0 < η₀ ∨ x ≠ chiQuantile c' n := by
      by_contra h_neg
      push Not at h_neg
      have hη0 : η₀ = 0 := le_antisymm h_neg.1 hη₀0
      have href0 := refComb_eq_zero_at_zero_node hc' hf (by omega : f + 1 ≤ n) h_neg.2
      exact h0 (by rw [hη0, href0, norm_zero])
    have href_pos : 0 < ‖refComb c' f η₀ (x : ℂ)‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have hbd := hlog f n j η₀ x hf hj hmax hη₀0 hη₀1 hx_cell hnz
    have hexp := Real.exp_le_exp.mpr hbd
    rw [Real.exp_add, Real.exp_log href_pos] at hexp
    exact hexp

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.holeModel_quarter_eq_hAII' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.holeModel_quarter_eq_hAII

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.jEndComb_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.jEndComb_bounds

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.combPf_bounds_K4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.combPf_bounds_K4

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.eLeftComb_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.eLeftComb_bounds

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.hole_lower_K4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.hole_lower_K4

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.hole_upper_K4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.hole_upper_K4
