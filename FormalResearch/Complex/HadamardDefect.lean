module

public import FormalResearch.Complex.HadamardRadii

/-!
# The `p`-th derivative of `f'/f - (log-derivative of the canonical product)` vanishes (Hadamard, milestone H4a)

Let `f` be entire, `f 0 ≠ 0`, `‖f z‖ ≤ C exp (C ‖z‖^σ)`, `σ < p + 1`, and `a` a `Listing` of the nonzero zeros.  With
`Λ(w) = Σ'_i (w/a_i)^p/(w - a_i)` (the logarithmic derivative of the genus-`p` canonical product, summable by H2):

* `Hadamard.tendstoLocallyUniformlyOn_partial`: the partial sums of `Λ` converge locally uniformly on `ℂ`
  (Weierstrass `M`-test off the finitely many `‖a_i‖ < 2r`);
* `Hadamard.iteratedDeriv_defect_eq_zero`: for every `z` with `f z ≠ 0`, `(d/dw)^p (f'/f - Λ) |_{w=z} = 0`.

Proof: limit `R_k → ∞` of `Hadamard.core_estimate`, using `Hadamard.tendstoLocallyUniformlyOn_iteratedDeriv`
(derivatives of locally uniform limits).  All **proved**.
-/

@[expose] public section

open Complex Filter Topology Finset Metric Set
open scoped BigOperators ComplexConjugate Classical Nat

namespace FormalResearch.Hadamard

variable {ι : Type*}

/-- The summand `(w/a)^p/(w-a)`. -/
noncomputable def term (p : ℕ) (a w : ℂ) : ℂ := (w / a) ^ p / (w - a)

lemma norm_term_le (p : ℕ) {a w : ℂ} {r : ℝ} (hr : 0 < r) (ha0 : a ≠ 0) (hw : ‖w‖ ≤ r)
    (ha : 2 * r ≤ ‖a‖) : ‖term p a w‖ ≤ 2 * r ^ p * (‖a‖ ^ (p + 1))⁻¹ := by
  have hai : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hza : ‖a‖ / 2 ≤ ‖w - a‖ := by
    have := norm_sub_norm_le a w
    rw [norm_sub_rev] at this
    linarith
  unfold term
  rw [norm_div, norm_pow, norm_div]
  have hpos : 0 < ‖w - a‖ := lt_of_lt_of_le (by positivity) hza
  rw [div_le_iff₀ hpos]
  calc (‖w‖ / ‖a‖) ^ p ≤ (r / ‖a‖) ^ p := by gcongr
    _ = r ^ p * (‖a‖ ^ p)⁻¹ := by rw [div_pow, div_eq_mul_inv]
    _ = (2 * r ^ p * (‖a‖ ^ (p + 1))⁻¹) * (‖a‖ / 2) := by
      rw [pow_succ]; field_simp
    _ ≤ (2 * r ^ p * (‖a‖ ^ (p + 1))⁻¹) * ‖w - a‖ := by gcongr

lemma differentiableAt_term (p : ℕ) {a w : ℂ} (hwa : w ≠ a) :
    DifferentiableAt ℂ (term p a) w := by
  unfold term
  exact ((differentiableAt_id.div_const a).pow p).div (differentiableAt_id.sub_const a)
    (sub_ne_zero.mpr hwa)

section lim

variable {p : ℕ} {a : ι → ℂ} (CD : CanonData p a)
include CD

/-- Partial sums of the logarithmic derivative of the canonical product converge locally uniformly. -/
lemma tendstoLocallyUniformlyOn_partial :
    TendstoLocallyUniformlyOn (fun (t : Finset ι) (w : ℂ) => ∑ i ∈ t, term p (a i) w)
      (fun w => ∑' i, term p (a i) w) atTop Set.univ := by
  refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun x _ => ?_
  set r : ℝ := ‖x‖ + 1 with hr
  have hr0 : 0 < r := by positivity
  refine ⟨ball (0 : ℂ) r, ?_, ?_⟩
  · rw [nhdsWithin_univ]
    exact isOpen_ball.mem_nhds (by simp [hr])
  · refine tendstoUniformlyOn_tsum_of_cofinite_eventually
      (u := fun i => 2 * r ^ p * (‖a i‖ ^ (p + 1))⁻¹) (CD.summable.mul_left _) ?_
    filter_upwards [CD.eventually_ge (2 * r)] with i hi w hw
    exact norm_term_le p hr0 (CD.ne_zero i) (mem_ball_zero_iff.mp hw).le hi

end lim

/-- Precomposing the filter of a locally uniformly convergent family. -/
lemma tendstoLocallyUniformlyOn_comp_filter {α β γ δ : Type*} [TopologicalSpace α] [UniformSpace β]
    {F : γ → α → β} {f : α → β} {s : Set α} {p : Filter γ} {q : Filter δ} {g : δ → γ}
    (h : TendstoLocallyUniformlyOn F f p s) (hg : Tendsto g q p) :
    TendstoLocallyUniformlyOn (fun n => F (g n)) f q s := by
  intro u hu x hx
  obtain ⟨t, ht, hev⟩ := h u hu x hx
  exact ⟨t, ht, hg.eventually hev⟩

lemma analyticAt_term (p : ℕ) {a w : ℂ} (hwa : w ≠ a) : AnalyticAt ℂ (term p a) w := by
  have hd : DifferentiableOn ℂ (term p a) ({a}ᶜ : Set ℂ) := fun x hx =>
    (differentiableAt_term p (by simpa using hx)).differentiableWithinAt
  exact hd.analyticOnNhd isOpen_compl_singleton w (by simpa using hwa)

section defect

variable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) {a : ι → ℂ} (L : Listing f a)
  {C σ : ℝ} (hC : 1 ≤ C) (hb : ∀ z, ‖f z‖ ≤ C * Real.exp (C * ‖z‖ ^ σ)) (hσ : 0 < σ)
  {p : ℕ} (hp : σ < p + 1)
include hf h0 L hC hb hσ hp

/-- **H4a.** `(d/dw)^p (f'/f - Λ)` vanishes wherever `f ≠ 0`. -/
theorem iteratedDeriv_defect_eq_zero {z : ℂ} (hz : f z ≠ 0) :
    iteratedDeriv p (fun w => logDeriv f w - ∑' i, term p (a i) w) z = 0 := by
  have CD : CanonData p a := L.canonData hf h0 hC hb hσ.le hp
  obtain ⟨R, hRrange, hRz⟩ := exists_good_radii hf h0
  have hRtend : Tendsto R atTop atTop :=
    tendsto_atTop_mono (fun k => (hRrange k).1.le)
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hR1 : ∀ k, 1 ≤ R k := fun k => by
    have := (hRrange k).1; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hTk : ∀ k, {i | a i ∈ ball (0 : ℂ) (R k)}.Finite := fun k =>
    (L.finite_idx hf h0 (R k)).subset fun i hi => by simpa using (mem_ball_zero_iff.mp hi).le
  set Tk : ℕ → Finset ι := fun k => (hTk k).toFinset with hTkdef
  set Lam : ℕ → ℂ → ℂ := fun k w => ∑ i ∈ Tk k, term p (a i) w with hLam
  set LamS : ℂ → ℂ := fun w => ∑' i, term p (a i) w with hLamS
  set U : Set ℂ := {w | f w ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne_fun hf.continuous continuous_const
  have hzU : z ∈ U := hz
  have hzA : ∀ i, z ≠ a i := fun i h => hz (h ▸ L.f_a hf h0 i)
  have hUa : ∀ w ∈ U, ∀ i, w ≠ a i := fun w hw i h => hw (h ▸ L.f_a hf h0 i)
  -- convergence of partial sums
  have hlim0 := tendstoLocallyUniformlyOn_partial CD
  have hTkT : Tendsto Tk atTop atTop := by
    refine tendsto_atTop.2 fun F => ?_
    have : ∀ᶠ k in atTop, ∀ i ∈ F, ‖a i‖ < R k := by
      rw [eventually_all_finset]
      intro i _
      exact hRtend.eventually_gt_atTop _
    filter_upwards [this] with k hk i hi
    exact (hTk k).mem_toFinset.mpr (mem_ball_zero_iff.mpr (hk i hi))
  have hlim : TendstoLocallyUniformlyOn Lam LamS atTop U :=
    (tendstoLocallyUniformlyOn_comp_filter hlim0 hTkT).mono (Set.subset_univ _)
  have hdiffk : ∀ k, DifferentiableOn ℂ (Lam k) U := fun k w hw =>
    (DifferentiableAt.fun_sum fun i _ => differentiableAt_term p (hUa w hw i)).differentiableWithinAt
  have hLamdiff : DifferentiableOn ℂ LamS U := hlim.differentiableOn (Eventually.of_forall hdiffk) hUo
  have htend : Tendsto (fun k => iteratedDeriv p (Lam k) z) atTop (𝓝 (iteratedDeriv p LamS z)) :=
    (tendstoLocallyUniformlyOn_iteratedDeriv hUo p Lam LamS hdiffk hlim).tendsto_at hzU
  -- analyticity at z
  have hqan : AnalyticAt ℂ (logDeriv f) z := by
    have h1 : logDeriv f = fun w => deriv f w / f w := by funext w; rw [logDeriv_apply]
    rw [h1]
    exact ((hf.analyticAt z).deriv).div (hf.analyticAt z) hz
  have hLamkan : ∀ k, AnalyticAt ℂ (Lam k) z := fun k =>
    Finset.analyticAt_fun_sum _ fun i _ => analyticAt_term p (hzA i)
  have hLamSan : AnalyticAt ℂ LamS z := hLamdiff.analyticOnNhd hUo z hzU
  have hlin : ∀ k, iteratedDeriv p (fun w => logDeriv f w - Lam k w) z =
      iteratedDeriv p (logDeriv f) z - iteratedDeriv p (Lam k) z := fun k =>
    iteratedDeriv_fun_sub hqan.contDiffAt (hLamkan k).contDiffAt
  have hlin' : iteratedDeriv p (fun w => logDeriv f w - LamS w) z =
      iteratedDeriv p (logDeriv f) z - iteratedDeriv p LamS z :=
    iteratedDeriv_fun_sub hqan.contDiffAt hLamSan.contDiffAt
  -- the bound
  set K : ℝ := (Real.log C + C * 2 ^ σ + |Real.log ‖f 0‖|) / Real.log 2 with hK
  obtain ⟨c3, hc3⟩ := core_bound_le (σ := σ) (C := C) hσ hC p (Real.log ‖f 0‖) K
  have hbound : ∀ᶠ k in atTop, ‖iteratedDeriv p (fun w => logDeriv f w - Lam k w) z‖ ≤
      c3 * R k ^ (σ - ((p + 1 : ℕ) : ℝ)) := by
    filter_upwards [hRtend.eventually_gt_atTop (4 * ‖z‖)] with k hk
    have hzk : ‖z‖ < R k / 4 := by linarith
    have hM1 : 1 ≤ C * Real.exp (C * R k ^ σ) := by
      have : 1 ≤ Real.exp (C * R k ^ σ) := by
        apply Real.one_le_exp
        exact mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith [hR1 k]) _)
      nlinarith
    have hMb : ∀ w : ℂ, ‖w‖ = R k → ‖f w‖ ≤ C * Real.exp (C * R k ^ σ) := fun w hw => by
      have := hb w; rwa [hw] at this
    have hce := core_estimate hf h0 L (by linarith [hR1 k]) (hRz k) (hTk k) hM1 hMb p hzk hz
    refine hce.trans ?_
    have hncard : ((Tk k).card : ℝ) ≤ K * R k ^ σ := by
      have h1 : (Tk k).card ≤ Set.ncard {i | ‖a i‖ ≤ R k} := by
        rw [← Set.ncard_coe_finset]
        refine Set.ncard_le_ncard (fun i hi => ?_) (L.finite_idx hf h0 _)
        have := (hTk k).mem_toFinset.mp (by simpa [hTkdef] using hi)
        exact (mem_ball_zero_iff.mp this).le
      exact (Nat.cast_le.mpr h1).trans (Listing.ncard_le_mul_rpow hf h0 L hC hb hσ.le (hR1 k))
    exact hc3 (R k) (hR1 k) _ (Nat.cast_nonneg _) hncard
  have hy : 0 < ((p + 1 : ℕ) : ℝ) - σ := by push_cast; linarith
  have hzero : Tendsto (fun k => c3 * R k ^ (σ - ((p + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    have h1 := (tendsto_rpow_neg_atTop hy).comp hRtend
    have h2 : (fun k => c3 * R k ^ (σ - ((p + 1 : ℕ) : ℝ))) =
        fun k => c3 * (fun x : ℝ => x ^ (-(((p + 1 : ℕ) : ℝ) - σ))) (R k) := by
      funext k; congr 2; ring
    rw [h2]
    simpa using h1.const_mul c3
  have hT0 : Tendsto (fun k => iteratedDeriv p (fun w => logDeriv f w - Lam k w) z) atTop (𝓝 0) :=
    squeeze_zero_norm' hbound hzero
  have hT1 : Tendsto (fun k => iteratedDeriv p (fun w => logDeriv f w - Lam k w) z) atTop
      (𝓝 (iteratedDeriv p (logDeriv f) z - iteratedDeriv p LamS z)) := by
    simp only [hlin]
    exact tendsto_const_nhds.sub htend
  have := tendsto_nhds_unique hT1 hT0
  rw [hlin']
  exact this

end defect

end FormalResearch.Hadamard
