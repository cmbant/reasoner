module

public import FormalResearch.ModularBootstrap.Spin.SpinMomentComb

/-!
# SPIN-M part 3b: Vacuum-source limit (`sd:spinmoment-ref-limit`)

Formalises the vacuum-source upper limit in
`CFT/modular_bootstrap/paper/spinning_airy_moment_proof.tex` (`sd:spinmoment-proof-sec`):

* `lobe_left_exp_decay`: exponential smallness of the deep left lobe `t ∈ (0, c'(ξ_*/2)²/3]`
  using `lobe_upper_K6b_blaschke` and `majorant_add_L_eq_neg_slitDeficit`.
* `bumpG_hat_vac_source_le`: `|∫₀^∞ (𝓗₅ h₅)(t) H_C(t) dt| ≤ C c'` by Fubini and
  `StripContinuation.vacuum_kernel`.
* `spinMoment_vac_source_limsup_le`:
  `limsup (π c' C_* FKc 1 1 c')⁻¹ ∫₀^∞ g₅(t) H_C(t) dt ≤ (ξ_*³/(3π)) windowIntegralSig`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Design
open FormalResearch.ModularBootstrap.Upper.Holes
open FormalResearch.ModularBootstrap.Upper.Membership
open FormalResearch.ModularBootstrap.Upper.Positivity
open FormalResearch.ModularBootstrap.Upper.Bump
open FormalResearch.ModularBootstrap.Upper.Ramped
open FormalResearch.ModularBootstrap.Upper.Window
open FormalResearch.ModularBootstrap.Upper.Window.Cardy
open FormalResearch.ModularBootstrap.Upper.Window.Tail
open FormalResearch.ModularBootstrap.Upper.Assembly
open FormalResearch.ModularBootstrap.Upper.Rigidity

private lemma tanh_strictMono' : StrictMono Real.tanh := by
  refine strictMono_of_deriv_pos (f := Real.tanh) fun x => ?_
  have hcs : Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq x
  have hd : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
    rw [show Real.tanh = fun t => Real.sinh t / Real.cosh t from funext Real.tanh_eq_sinh_div_cosh]
    have hdiv := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
    have heq : (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2 =
        1 / Real.cosh x ^ 2 := by
      rw [← sq, ← sq, hcs]
    rwa [heq] at hdiv
  rw [hd.deriv]; positivity

private lemma tanh_neg' (z : ℝ) : Real.tanh (-z) = -Real.tanh z := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, Real.sinh_neg, Real.cosh_neg, neg_div]

private lemma abs_tanh_eq (z : ℝ) : |Real.tanh z| = Real.tanh |z| := by
  rcases le_total 0 z with hz | hz
  · have hpos : 0 ≤ Real.tanh z := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg (Real.sinh_nonneg_iff.mpr hz) (Real.cosh_pos z).le
    rw [abs_of_nonneg hz, abs_of_nonneg hpos]
  · have hneg : 0 ≤ Real.tanh (-z) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg (Real.sinh_nonneg_iff.mpr (neg_nonneg.mpr hz)) (Real.cosh_pos _).le
    rw [abs_of_nonpos hz, show Real.tanh z = -Real.tanh (-z) by rw [tanh_neg', neg_neg], abs_neg,
      abs_of_nonneg hneg]

/-- Comparison `‖designComb‖ ≤ K_N ‖refComb‖` on `[0, ξ_*/2]`: every zero and pair center of `refComb`
is `≥ χ₁ > ξ_*`, at distance `≥ ξ_*/2` from `x`. -/
private lemma norm_designComb_le_mul_refComb_left (N : ℕ) (hN : 1 ≤ N) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ c' in atTop, ∀ x ∈ Icc 0 (xiStar / 2),
      ‖designComb c' 1 N (1 / 4) σs (designWidth1 c' η) (x : ℂ)‖ ≤ K * ‖refComb c' 1 (1 / 4) (x : ℂ)‖ := by
  have hxi := xiStar_pos
  have hpi := Real.pi_pos
  let τ : ℝ := Real.tanh (π * xiStar / 8)
  have hτ : 0 < τ := tanh_pos_of_pos (by positivity)
  let P : ℝ := τ ^ (2 + 4 * (N - 1))
  have hP : 0 < P := by positivity
  refine ⟨P⁻¹, inv_pos.mpr hP, ?_⟩
  obtain ⟨_, _, h_ev⟩ := siteGap_eventually_le
  filter_upwards [refComb_eq_split 1 N hN (by norm_num) le_rfl,
    designWidth1_admissible N hN hη0 hη1 σs, h_ev, eventually_gt_atTop (0 : ℝ)]
    with c' hsp hA ⟨hgap_k, _, _, hgap_1⟩ hc' x hx
  have hgap_nn : ∀ k, 1 ≤ k → 0 ≤ siteGap c' k := fun k hk => siteGap_nonneg hc' hk
  have hsp_x := hsp (by simp : |((x : ℂ)).im| < 7 / 8)
  have hnorm_ref : ‖refComb c' 1 (1 / 4) (x : ℂ)‖ =
      (‖blaschkeT (chiQuantile c' (1 : ℕ) : ℂ) (x : ℂ)‖ *
        ∏ i ∈ Finset.range (N - 1), blaschkePairQ (chiQuantile c' (1 + 1 + i : ℕ))
          ((1 / 4 : ℝ) * siteGap c' (1 + 1 + i)) x) * ‖combTail c' N (1 / 4) (x : ℂ)‖ := by
    rw [hsp_x, norm_mul, norm_mul, norm_prod]; rfl
  have hnorm_D : ‖designComb c' 1 N (1 / 4) σs (designWidth1 c' η) (x : ℂ)‖ =
      (‖blaschkeT (designSite c' σs 1 : ℂ) (x : ℂ)‖ *
        ∏ i ∈ Finset.range (N - 1), blaschkePairQ (designSite c' σs (1 + 1 + i))
          (designWidth1 c' η (1 + 1 + i)) x) * ‖combTail c' N (1 / 4) (x : ℂ)‖ := by
    unfold designComb; rw [norm_mul, norm_mul, norm_prod]; rfl
  have hbim : |((x : ℂ)).im| ≤ 1 / 2 := by simp
  have hD1 : ‖blaschkeT (designSite c' σs 1 : ℂ) (x : ℂ)‖ *
      ∏ i ∈ Finset.range (N - 1), blaschkePairQ (designSite c' σs (1 + 1 + i))
        (designWidth1 c' η (1 + 1 + i)) x ≤ 1 := by
    have h1 := norm_blaschkeT_real_le_one (designSite c' σs 1) hbim
    have h2 : ∏ i ∈ Finset.range (N - 1), blaschkePairQ (designSite c' σs (1 + 1 + i))
        (designWidth1 c' η (1 + 1 + i)) x ≤ 1 :=
      Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i hi =>
        norm_pair_blaschkeT_le_one _ _ ((hA.width i (Finset.mem_range.mp hi)).trans (by norm_num)) hbim
    exact (mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one).trans (by norm_num)
  have hbt : ∀ {y : ℝ}, xiStar ≤ y → τ ^ 2 ≤ ‖blaschkeT (y : ℂ) (x : ℂ)‖ := fun {y} hy => by
    have habs1 : |π * (x - y) / 2| = π * |x - y| / 2 := by
      simp only [abs_div, abs_mul, abs_of_pos hpi, show |(2 : ℝ)| = 2 by norm_num]
    have habs2 : |π * (x + y) / 2| = π * (x + y) / 2 :=
      abs_of_nonneg (div_nonneg (mul_nonneg hpi.le (by linarith [hx.1, hy, hxi])) zero_le_two)
    rw [norm_blaschkeT_ofReal, abs_mul, abs_tanh_eq, abs_tanh_eq, habs1, habs2]
    have h1 : τ ≤ Real.tanh (π * |x - y| / 2) := by
      have : xiStar / 4 ≤ |x - y| := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith [hx.2])]; linarith [hx.2]
      exact tanh_strictMono'.monotone (by nlinarith)
    have h2 : τ ≤ Real.tanh (π * (x + y) / 2) :=
      tanh_strictMono'.monotone (by nlinarith [hx.1])
    calc τ ^ 2 = τ * τ := by ring
      _ ≤ Real.tanh (π * |x - y| / 2) * Real.tanh (π * (x + y) / 2) :=
        mul_le_mul h1 h2 hτ.le (hτ.le.trans h1)
  have hχ_ge14 : ∀ k : ℕ, 1 ≤ k → (1 / 4 : ℝ) ≤ (k : ℝ) := fun k hk => by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hχ_ge : ∀ k : ℕ, 1 ≤ k → xiStar ≤ chiQuantile c' (k : ℝ) := fun k hk =>
    (chiQuantile_spec hc' (hχ_ge14 k hk)).1
  have hR0 : τ ^ 2 * (τ ^ 4) ^ (N - 1) ≤
      ‖blaschkeT (chiQuantile c' (1 : ℕ) : ℂ) (x : ℂ)‖ *
        ∏ i ∈ Finset.range (N - 1), blaschkePairQ (chiQuantile c' (1 + 1 + i : ℕ))
          ((1 / 4 : ℝ) * siteGap c' (1 + 1 + i)) x := by
    refine mul_le_mul (hbt (hχ_ge 1 le_rfl)) ?_ (by positivity) (norm_nonneg _)
    calc (τ ^ 4) ^ (N - 1) = ∏ _i ∈ Finset.range (N - 1), τ ^ 4 := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => by positivity) fun i hi => by
          have hk1 : 1 ≤ 1 + 1 + i := by omega
          have hgap_i := (hgap_k (1 + 1 + i) hk1).trans hgap_1
          have hε0 : 0 ≤ (1 / 4 : ℝ) * siteGap c' (1 + 1 + i) := mul_nonneg (by norm_num) (hgap_nn _ hk1)
          have hε1 : (1 / 4 : ℝ) * siteGap c' (1 + 1 + i) ≤ 1 / 2 := by linarith
          have hsq := blaschkePairQ_ge_sq (chiQuantile c' (1 + 1 + i : ℕ)) ((1 / 4 : ℝ) * siteGap c' (1 + 1 + i)) x hε0 hε1
          have hb := hbt (hχ_ge _ hk1)
          have hsq' : ‖blaschkeT (chiQuantile c' (1 + 1 + i : ℕ) : ℂ) (x : ℂ)‖ ^ 2 ≤
              blaschkePairQ (chiQuantile c' (1 + 1 + i : ℕ)) ((1 / 4 : ℝ) * siteGap c' (1 + 1 + i)) x := by
            rw [norm_blaschkeT_ofReal, sq_abs]
            exact hsq
          have : τ ^ 4 ≤ ‖blaschkeT (chiQuantile c' (1 + 1 + i : ℕ) : ℂ) (x : ℂ)‖ ^ 2 := by
            calc τ ^ 4 = (τ ^ 2) ^ 2 := by ring
              _ ≤ _ := pow_le_pow_left₀ (by positivity) hb 2
          exact this.trans hsq'
  have hP_eq : P = τ ^ 2 * (τ ^ 4) ^ (N - 1) := by dsimp [P]; rw [pow_add, ← pow_mul]
  have ht_nn := norm_nonneg (combTail c' N (1 / 4) (x : ℂ))
  have hP_norm : P * ‖designComb c' 1 N (1 / 4) σs (designWidth1 c' η) (x : ℂ)‖ ≤
      ‖refComb c' 1 (1 / 4) (x : ℂ)‖ := by
    rw [hnorm_ref, hnorm_D, hP_eq]
    nlinarith [mul_le_mul_of_nonneg_right hR0 ht_nn, mul_le_mul_of_nonneg_right hD1 ht_nn,
      mul_nonneg (by positivity : 0 ≤ τ ^ 2 * (τ ^ 4) ^ (N - 1)) ht_nn]
  rw [← div_eq_inv_mul, le_div_iff₀' hP]
  exact hP_norm

private lemma tsum_even_pow_div_factorial_le (z : ℝ) (hz : 0 ≤ z) :
    (∑' k : ℕ, z ^ (2 * k) / ((2 * k).factorial : ℝ)) ≤ Real.exp z := by
  have hsumm : Summable fun k : ℕ => z ^ (2 * k) / ((2 * k).factorial : ℝ) :=
    (Real.summable_pow_div_factorial z).comp_injective (fun _ _ h => by omega)
  have hexp_tsum : Real.exp z = ∑' n : ℕ, z ^ n / (n.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [hexp_tsum]
  exact hsumm.tsum_le_tsum_of_inj (fun k => 2 * k) (fun _ _ h => by dsimp only at h; omega)
    (fun _ _ => by positivity) (fun _ => le_rfl) (Real.summable_pow_div_factorial z)

/-- Uniform sub-exponential upper envelope for `kernelK 5 a t` (`a, t ≥ 0`). -/
private lemma kernelK5_le_sub_exp {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    kernelK 5 a t ≤ (2 * π) ^ 4 * (1 + t) ^ 4 * Real.exp (4 * π * √(a * t)) := by
  unfold kernelK
  have hsum_le : ∑' k : ℕ, kernelKTerm 5 a t k ≤ Real.exp (4 * π * √(a * t)) := by
    have hterm : ∀ k : ℕ, kernelKTerm 5 a t k ≤
        (4 * π * √(a * t)) ^ (2 * k) / ((2 * k).factorial : ℝ) := fun k => by
      have hsq : (4 * π * √(a * t)) ^ (2 * k) = 4 ^ k * (4 * π ^ 2 * a * t) ^ k := by
        have hbase : (4 * π * √(a * t)) ^ 2 = 4 * (4 * π ^ 2 * a * t) := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg ha ht)]; ring
        rw [pow_mul, hbase, mul_pow]
      have hchoose : (2 * k).choose k ≤ 2 ^ (2 * k) := by
        calc (2 * k).choose k ≤ ∑ i ∈ Finset.range (2 * k + 1), (2 * k).choose i :=
              Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
          _ = 2 ^ (2 * k) := Nat.sum_range_choose (2 * k)
      have hfac : ((2 * k).factorial : ℝ) ≤ 4 ^ k * (k.factorial : ℝ) * ((k + 4).factorial : ℝ) := by
        have hmul : (2 * k).factorial = (2 * k).choose k * (k.factorial * k.factorial) := by
          have := Nat.choose_mul_factorial_mul_factorial (by omega : k ≤ 2 * k)
          rw [show 2 * k - k = k by omega, mul_assoc] at this; exact this.symm
        have hkf : k.factorial ≤ (k + 4).factorial := Nat.factorial_le (by omega)
        have h2kN : (2 * k).choose k * (k.factorial * k.factorial) ≤
            2 ^ (2 * k) * (k.factorial * (k + 4).factorial) :=
          Nat.mul_le_mul hchoose (Nat.mul_le_mul_left k.factorial hkf)
        have h2k : ((2 * k).factorial : ℝ) ≤
            (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) * ((k + 4).factorial : ℝ)) := by
          exact_mod_cast (by simpa [hmul] using h2kN)
        rw [show (2 : ℝ) ^ (2 * k) = 4 ^ k by rw [pow_mul]; norm_num] at h2k
        linarith
      unfold kernelKTerm
      rw [show k + 5 - 1 = k + 4 by omega]
      have hnum : 0 ≤ (4 * π ^ 2 * a * t) ^ k := by positivity
      have hd1 : 0 < (k.factorial : ℝ) * ((k + 4).factorial : ℝ) := by positivity
      have hd2 : 0 < ((2 * k).factorial : ℝ) := by positivity
      rw [div_le_div_iff₀ hd1 hd2, hsq]
      calc (4 * π ^ 2 * a * t) ^ k * ((2 * k).factorial : ℝ)
          ≤ (4 * π ^ 2 * a * t) ^ k * (4 ^ k * (k.factorial : ℝ) * ((k + 4).factorial : ℝ)) :=
            mul_le_mul_of_nonneg_left hfac hnum
        _ = _ := by ring
    have hsumm : Summable fun k : ℕ => (4 * π * √(a * t)) ^ (2 * k) / ((2 * k).factorial : ℝ) :=
      (Real.summable_pow_div_factorial _).comp_injective (fun _ _ h => by omega)
    exact ((summable_kernelKTerm 5 a t).tsum_le_tsum hterm hsumm).trans
      (tsum_even_pow_div_factorial_le _ (by positivity))
  have hpow : (2 * π * t) ^ (5 - 1) ≤ (2 * π) ^ 4 * (1 + t) ^ 4 := by
    rw [show (5 - 1 : ℕ) = 4 by rfl, mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht (by linarith) 4) (by positivity)
  calc (2 * π * t) ^ (5 - 1) * ∑' k, kernelKTerm 5 a t k
      ≤ ((2 * π) ^ 4 * (1 + t) ^ 4) * Real.exp (4 * π * √(a * t)) :=
        mul_le_mul hpow hsum_le (tsum_nonneg fun k => by unfold kernelKTerm; positivity) (by positivity)
    _ = (2 * π) ^ 4 * (1 + t) ^ 4 * Real.exp (4 * π * √(a * t)) := by ring

private lemma exp_poly_squeeze_bound {A₀ δ₀ c' : ℝ} (hA₀ : 0 ≤ A₀) (hδ₀ : 0 < δ₀) (hc1 : 1 ≤ c')
    (h1 : 2 * (c' / 12) + 4 ≤ c') :
    A₀ * (2 * (c' / 12) + 4) * (1 + c' * (xiStar / 2) ^ 2 / 3) ^ 4 * Real.exp (-c' * δ₀) ≤
      (A₀ * (1 + (xiStar / 2) ^ 2 / 3) ^ 4 / δ₀ ^ 5) * ((δ₀ * c') ^ 5 * Real.exp (-(δ₀ * c'))) := by
  have h2 : (1 + c' * (xiStar / 2) ^ 2 / 3) ^ 4 ≤ (1 + (xiStar / 2) ^ 2 / 3) ^ 4 * c' ^ 4 := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ 4
    rw [add_mul, one_mul, mul_comm ((xiStar / 2) ^ 2 / 3) c']
    linarith
  have h3 : (2 * (c' / 12) + 4) * (1 + c' * (xiStar / 2) ^ 2 / 3) ^ 4 ≤
      (1 + (xiStar / 2) ^ 2 / 3) ^ 4 * c' ^ 5 := by
    calc (2 * (c' / 12) + 4) * (1 + c' * (xiStar / 2) ^ 2 / 3) ^ 4
        ≤ c' * ((1 + (xiStar / 2) ^ 2 / 3) ^ 4 * c' ^ 4) :=
          mul_le_mul h1 h2 (by positivity) (by linarith)
      _ = (1 + (xiStar / 2) ^ 2 / 3) ^ 4 * c' ^ 5 := by ring
  have h4 : A₀ * ((2 * (c' / 12) + 4) * (1 + c' * (xiStar / 2) ^ 2 / 3) ^ 4) * Real.exp (-c' * δ₀) ≤
      A₀ * ((1 + (xiStar / 2) ^ 2 / 3) ^ 4 * c' ^ 5) * Real.exp (-c' * δ₀) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hA₀) (Real.exp_pos _).le
  have h5 : A₀ * ((1 + (xiStar / 2) ^ 2 / 3) ^ 4 * c' ^ 5) * Real.exp (-c' * δ₀) =
      (A₀ * (1 + (xiStar / 2) ^ 2 / 3) ^ 4 / δ₀ ^ 5) * ((δ₀ * c') ^ 5 * Real.exp (-(δ₀ * c'))) := by
    rw [show -(δ₀ * c') = -c' * δ₀ by ring]
    field_simp [hδ₀.ne']
  linarith [show A₀ * (2 * (c' / 12) + 4) * (1 + c' * (xiStar / 2) ^ 2 / 3) ^ 4 * Real.exp (-c' * δ₀) =
    A₀ * ((2 * (c' / 12) + 4) * (1 + c' * (xiStar / 2) ^ 2 / 3) ^ 4) * Real.exp (-c' * δ₀) by ring]

/-- Exponential smallness of the deep left lobe `t ∈ (0, c' (ξ_*/2)² / 3]`:
`∫_{0 < t ≤ c'(ξ_*/2)²/3} |h₅(t) H_C(t)| dt / (c' FKc 1 1 c') → 0`. -/
lemma lobe_left_exp_decay (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4)
    (σs : ℕ → ℝ) :
    Tendsto (fun c' => (∫ t in Ioc 0 (c' * (xiStar / 2) ^ 2 / 3),
        |combProfile c' (bumpBc (rpParams 4).bumpData N η σs c') t * spinVacHC (c' / 12) t|) /
        (c' * FKc 1 1 c')) atTop (𝓝 0) := by
  let d5 := (rpParams 4).bumpData
  obtain ⟨C6, hC6, hK6⟩ := lobe_upper_K6b_blaschke
  obtain ⟨K_N, hKN, h_cmp⟩ := norm_designComb_le_mul_refComb_left N hN hη0.le hη1 σs
  have hxi := xiStar_pos
  let δ₀ : ℝ := slitDeficit (xiStar / 2)
  have hδ₀_pos : 0 < δ₀ := slitDeficit_pos_of_lt (half_pos xiStar_pos) (half_lt_self xiStar_pos)
  let τξ : ℝ := Real.tanh (π * xiStar / 4) ^ 2
  have hτξ : 0 < τξ := pow_pos (tanh_pos_of_pos (by have := Real.pi_pos; positivity)) 2
  let M_T' : ℝ := τξ ^ (-(2 * n1Comb 1))
  have hbumpC_pos : 0 < bumpC d5 (1 / 4) := by
    obtain ⟨c0, hc0⟩ := ((bumpFactor_one_le d5 (η₀ := 1 / 4) (by norm_num) le_rfl).and
      (bumpFactor_le d5 (η₀ := 1 / 4) (by norm_num) le_rfl)).exists
    have h1 := hc0.1 1 1 0
    have h2 := hc0.2 1 1 0 le_rfl
    linarith
  let A₀ : ℝ := bumpC d5 (1 / 4) * K_N * C6 * M_T' * (2 * π) * (2 * π) ^ 4 * ((xiStar / 2) ^ 2 / 3)
  have h_bound : ∀ᶠ c' in atTop,
      (∫ t in Ioc 0 (c' * (xiStar / 2) ^ 2 / 3),
        |combProfile c' (bumpBc d5 N η σs c') t * spinVacHC (c' / 12) t|) / (c' * FKc 1 1 c') ≤
        A₀ * (2 * (c' / 12) + 4) * (1 + c' * (xiStar / 2) ^ 2 / 3) ^ 4 * Real.exp (-c' * δ₀) := by
    filter_upwards [hK6, h_cmp, bumpFactor_le d5 (η₀ := 1 / 4) (by norm_num) le_rfl,
      bumpFactor_one_le d5 (η₀ := 1 / 4) (by norm_num) le_rfl,
      combProfile_bumped_eq d5,
      bumpSig_phaseHyp d5 N hN hη0.le hη1 σs,
      designComb_innerCombHyp_of_admissible 1 le_rfl (η₀ := 1 / 4) (by norm_num) (by norm_num),
      FKc_ge_mul_sqrt_of_pos one_pos 1, eventually_ge_atTop (24 : ℝ)]
      with c' hK6c hcmpc hbfc hbf1 hvalc hph hin hFK1 hc24
    have hcpos : 0 < c' := by linarith
    have hc1 : 1 ≤ c' := by linarith
    have hFK_ge1 : 1 ≤ FKc 1 1 c' := by
      have hsc : 1 ≤ √c' := by simpa using Real.sqrt_le_sqrt hc1
      linarith [show 1 * √c' ≤ FKc 1 1 c' from hFK1]
    obtain ⟨hfN, hA, -⟩ := hph (bumpCut d5 N c') (le_bumpCut d5 N c')
    have hI : InnerCombHyp c' (bumpBc d5 N η σs c') := hin (bumpCut d5 N c') _ _ hfN hA
    have h_pt : ∀ t ∈ Ioc 0 (c' * (xiStar / 2) ^ 2 / 3),
        |combProfile c' (bumpBc d5 N η σs c') t * spinVacHC (c' / 12) t| ≤
          bumpC d5 (1 / 4) * K_N * C6 * M_T' * (2 * π) * (2 * π) ^ 4 *
            (2 * (c' / 12) + 4) * (1 + c' * (xiStar / 2) ^ 2 / 3) ^ 4 * Real.exp (-c' * δ₀) := by
      intro t ht
      have ht0 : 0 < t := ht.1
      set x : ℝ := xOf c' t
      have hx0 : 0 < x := by dsimp [x]; unfold xOf; exact Real.sqrt_pos.mpr (by positivity)
      have hx_le : x ≤ xiStar / 2 := by
        dsimp [x]; unfold xOf
        calc √(3 * t / c') ≤ √((xiStar / 2) ^ 2) := Real.sqrt_le_sqrt (by rw [div_le_iff₀ hcpos]; linarith [ht.2])
          _ = xiStar / 2 := Real.sqrt_sq (by positivity)
      have hx_lt : x < xiStar := by linarith
      have ht_eq : t = c' * x ^ 2 / 3 := by
        unfold x xOf; rw [Real.sq_sqrt (by positivity)]; field_simp
      have h4pi : 4 * π * √((c' / 12) * t) = c' * slitL x := by
        rw [ht_eq, show (c' / 12) * (c' * x ^ 2 / 3) = (c' * x / 6) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]
        unfold slitL; rw [abs_of_pos hx0]; ring
      have hK5_bd : kernelK 5 (c' / 12) t ≤
          (2 * π) ^ 4 * (1 + c' * (xiStar / 2) ^ 2 / 3) ^ 4 * Real.exp (c' * slitL x) := by
        have h1 := kernelK5_le_sub_exp (a := c' / 12) (t := t) (by linarith) ht0.le
        rw [h4pi] at h1
        have h1t : (1 + t) ^ 4 ≤ (1 + c' * (xiStar / 2) ^ 2 / 3) ^ 4 :=
          pow_le_pow_left₀ (by linarith) (by linarith [ht.2]) 4
        exact h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1t (by positivity)) (Real.exp_pos _).le)
      have hHC_bd : |spinVacHC (c' / 12) t| ≤ (2 * (c' / 12) + 4) * (2 * π) *
          ((2 * π) ^ 4 * (1 + c' * (xiStar / 2) ^ 2 / 3) ^ 4) * Real.exp (c' * slitL x) := by
        have h1 := spinVacHC_abs_le (a := c' / 12) (by linarith) ht0.le
        unfold spinVacuumD at h1
        calc |spinVacHC (c' / 12) t| ≤ (2 * (c' / 12) + 4) * (2 * π * kernelK 5 (c' / 12) t) := h1
          _ ≤ (2 * (c' / 12) + 4) * (2 * π * ((2 * π) ^ 4 * (1 + c' * (xiStar / 2) ^ 2 / 3) ^ 4 * Real.exp (c' * slitL x))) := by
              gcongr
          _ = _ := by ring
      have hdef_maj : majorantReal x + slitL x ≤ -δ₀ := by
        have hid := majorant_add_L_eq_neg_slitDeficit (x := x) (by rw [abs_of_pos hx0]; exact hx_lt.le)
        rw [abs_of_pos hx0] at hid
        have hmono_slit : δ₀ ≤ slitDeficit (xiStar - x) := by
          dsimp [δ₀]; unfold slitDeficit
          rw [show xiStar - xiStar / 2 = xiStar / 2 by ring, sub_sub_cancel]
          gcongr
          have hg_cont : Continuous fun s : ℝ => Real.arccos (Real.sinh (π * s)) :=
            Real.continuous_arccos.comp (Real.continuous_sinh.comp (continuous_const.mul continuous_id))
          have hI : ∫ s in x..xiStar, Real.arccos (Real.sinh (π * s)) =
              (∫ s in x..(xiStar / 2), Real.arccos (Real.sinh (π * s))) +
                ∫ s in (xiStar / 2)..xiStar, Real.arccos (Real.sinh (π * s)) :=
            (intervalIntegral.integral_add_adjacent_intervals (hg_cont.intervalIntegrable _ _)
              (hg_cont.intervalIntegrable _ _)).symm
          have hnn : 0 ≤ ∫ s in x..(xiStar / 2), Real.arccos (Real.sinh (π * s)) :=
            intervalIntegral.integral_nonneg hx_le fun s _ => Real.arccos_nonneg _
          rw [hI]; linarith
        linarith
      have hT_ge : τξ ≤ ‖blaschkeT (xiStar : ℂ) (x : ℂ)‖ := by
        have habs1 : |π * (x - xiStar) / 2| = π * |x - xiStar| / 2 := by
          simp only [abs_div, abs_mul, abs_of_pos Real.pi_pos, show |(2 : ℝ)| = 2 by norm_num]
        have habs2 : |π * (x + xiStar) / 2| = π * (x + xiStar) / 2 :=
          abs_of_nonneg (div_nonneg (mul_nonneg Real.pi_pos.le (by linarith)) zero_le_two)
        rw [norm_blaschkeT_ofReal, abs_mul, abs_tanh_eq, abs_tanh_eq, habs1, habs2]
        have h1 : Real.tanh (π * xiStar / 4) ≤ Real.tanh (π * |x - xiStar| / 2) := by
          have : xiStar / 2 ≤ |x - xiStar| := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
          exact tanh_strictMono'.monotone (by have := Real.pi_pos; nlinarith)
        have h2 : Real.tanh (π * xiStar / 4) ≤ Real.tanh (π * (x + xiStar) / 2) :=
          tanh_strictMono'.monotone (by have := Real.pi_pos; nlinarith)
        have hpos : 0 ≤ Real.tanh (π * xiStar / 4) := (tanh_pos_of_pos (by have := Real.pi_pos; positivity)).le
        dsimp [τξ]; nlinarith
      have hT_pow : ‖blaschkeT (xiStar : ℂ) (x : ℂ)‖ ^ (-(2 * n1Comb 1)) ≤ M_T' := by
        dsimp [M_T']
        have hn : -(2 * n1Comb 1) ≤ 0 := by unfold n1Comb; norm_num
        exact Real.rpow_le_rpow_of_nonpos hτξ hT_ge hn
      have h_ref_bd := (hK6c 1 (1 / 4) x le_rfl (by norm_num) le_rfl ⟨hx0.le, hx_lt⟩).2
      have h_ref_bd1 := (hK6c 1 (1 / 4) x le_rfl (by norm_num) le_rfl ⟨hx0.le, hx_lt⟩).1
      have h_comb_bd : |combProfile c' (bumpBc d5 N η σs c') t| * Real.exp (c' * slitL x) ≤
          bumpC d5 (1 / 4) * K_N * C6 * M_T' * Real.exp (-c' * δ₀) := by
        have hval := hvalc N (bumpCut d5 N c') σs (designWidth1 c' η) hN (le_bumpCut d5 N c') t
        have hb_eq : bumpBc d5 N η σs c' =
            bumpedComb d5 c' 1 N (bumpCut d5 N c') (1 / 4) σs (designWidth1 c' η) := rfl
        rw [← hb_eq] at hval
        have hbf := hbfc N (bumpCut d5 N c') x hx0.le
        have hbf0 : 0 ≤ bumpFactor d5 c' (1 / 4) N (bumpCut d5 N c') x :=
          zero_le_one.trans (hbf1 N (bumpCut d5 N c') x)
        have hprof_le : |combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t| ≤
            ‖designComb c' 1 N (1 / 4) σs (designWidth1 c' η) (x : ℂ)‖ := by
          unfold combProfile; rw [show xOf c' t = x from rfl]
          refine (Complex.abs_re_le_norm _).trans ?_
          unfold combH0; rw [norm_mul, Upper.Membership.sechSqProfile_ofReal, Complex.norm_real,
            Real.norm_of_nonneg (by positivity)]
          have hch : (1 : ℝ) / Real.cosh (π * x / 2) ^ 2 ≤ 1 :=
            div_le_one_of_le₀ (one_le_pow₀ (Real.one_le_cosh _)) (by positivity)
          exact mul_le_of_le_one_left (norm_nonneg _) hch
        have hcmp' := hcmpc x ⟨hx0.le, hx_le⟩
        have hexp_maj : Real.exp (c' * (majorantReal x + slitL x)) ≤ Real.exp (-c' * δ₀) :=
          Real.exp_le_exp.mpr (by nlinarith)
        have href_1 : C6 * ‖blaschkeT (xiStar : ℂ) (x : ℂ)‖ ^ (-(2 * n1Comb 1)) *
              Real.exp (c' * (majorantReal x + slitL x)) ≤ C6 * M_T' * Real.exp (-c' * δ₀) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hT_pow hC6.le) hexp_maj (Real.exp_pos _).le (by positivity)
        have href_all : ‖refComb c' 1 (1 / 4) (x : ℂ)‖ * Real.exp (c' * slitL x) ≤
            C6 * M_T' * Real.exp (-c' * δ₀) := h_ref_bd1.trans (h_ref_bd.trans href_1)
        have hstep1 : |combProfile c' (bumpBc d5 N η σs c') t| * Real.exp (c' * slitL x) ≤
            (bumpC d5 (1 / 4) * (K_N * ‖refComb c' 1 (1 / 4) (x : ℂ)‖)) * Real.exp (c' * slitL x) := by
          rw [hval, abs_mul, abs_of_nonneg hbf0]
          have hbf_abs : bumpFactor d5 c' (1 / 4) N (bumpCut d5 N c') x *
              |combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t| ≤
              bumpC d5 (1 / 4) * (K_N * ‖refComb c' 1 (1 / 4) (x : ℂ)‖) :=
            mul_le_mul hbf (hprof_le.trans hcmp') (abs_nonneg _) hbumpC_pos.le
          exact mul_le_mul_of_nonneg_right hbf_abs (Real.exp_pos _).le
        have hstep2 : (bumpC d5 (1 / 4) * (K_N * ‖refComb c' 1 (1 / 4) (x : ℂ)‖)) * Real.exp (c' * slitL x) ≤
            bumpC d5 (1 / 4) * K_N * (C6 * M_T' * Real.exp (-c' * δ₀)) := by
          rw [show (bumpC d5 (1 / 4) * (K_N * ‖refComb c' 1 (1 / 4) (x : ℂ)‖)) * Real.exp (c' * slitL x) =
            bumpC d5 (1 / 4) * K_N * (‖refComb c' 1 (1 / 4) (x : ℂ)‖ * Real.exp (c' * slitL x)) by ring]
          exact mul_le_mul_of_nonneg_left href_all (by positivity)
        exact (hstep1.trans hstep2).trans_eq (by ring)
      have hexp_id : Real.exp (-c' * slitL x) * Real.exp (c' * slitL x) = 1 := by rw [← Real.exp_add]; simp
      have hHC_neg : |spinVacHC (c' / 12) t| * Real.exp (-c' * slitL x) ≤
          (2 * (c' / 12) + 4) * (2 * π) * ((2 * π) ^ 4 * (1 + c' * (xiStar / 2) ^ 2 / 3) ^ 4) := by
        calc |spinVacHC (c' / 12) t| * Real.exp (-c' * slitL x)
            ≤ ((2 * (c' / 12) + 4) * (2 * π) * ((2 * π) ^ 4 * (1 + c' * (xiStar / 2) ^ 2 / 3) ^ 4) *
                Real.exp (c' * slitL x)) * Real.exp (-c' * slitL x) :=
              mul_le_mul_of_nonneg_right hHC_bd (Real.exp_pos _).le
          _ = _ := by
              rw [mul_assoc, ← Real.exp_add, show c' * slitL x + -c' * slitL x = 0 by ring,
                Real.exp_zero, mul_one]
      have h_abs_eq : |combProfile c' (bumpBc d5 N η σs c') t * spinVacHC (c' / 12) t| =
          (|combProfile c' (bumpBc d5 N η σs c') t| * Real.exp (c' * slitL x)) *
            (|spinVacHC (c' / 12) t| * Real.exp (-c' * slitL x)) := by
        rw [abs_mul]; linear_combination -(|combProfile c' (bumpBc d5 N η σs c') t| * |spinVacHC (c' / 12) t|) * hexp_id
      rw [h_abs_eq]
      calc _ ≤ (bumpC d5 (1 / 4) * K_N * C6 * M_T' * Real.exp (-c' * δ₀)) *
              ((2 * (c' / 12) + 4) * (2 * π) * ((2 * π) ^ 4 * (1 + c' * (xiStar / 2) ^ 2 / 3) ^ 4)) :=
            mul_le_mul h_comb_bd hHC_neg (by positivity) (by positivity)
        _ = _ := by ring
    let Mpt : ℝ := bumpC d5 (1 / 4) * K_N * C6 * M_T' * (2 * π) * (2 * π) ^ 4 *
        (2 * (c' / 12) + 4) * (1 + c' * (xiStar / 2) ^ 2 / 3) ^ 4 * Real.exp (-c' * δ₀)
    have hcont_prod : ContinuousOn (fun t => |combProfile c' (bumpBc d5 N η σs c') t * spinVacHC (c' / 12) t|)
        (Icc 0 (c' * (xiStar / 2) ^ 2 / 3)) :=
      ((hI.continuousOn_combProfile hcpos).mono Icc_subset_Ici_self).mul
        (continuous_spinVacHC _).continuousOn |>.abs
    have hInt_f : IntegrableOn (fun t => |combProfile c' (bumpBc d5 N η σs c') t * spinVacHC (c' / 12) t|)
        (Ioc 0 (c' * (xiStar / 2) ^ 2 / 3)) :=
      hcont_prod.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hInt_bd : ∫ t in Ioc 0 (c' * (xiStar / 2) ^ 2 / 3),
        |combProfile c' (bumpBc d5 N η σs c') t * spinVacHC (c' / 12) t| ≤
          (c' * (xiStar / 2) ^ 2 / 3) * Mpt := by
      have h_mono := setIntegral_mono_on hInt_f (integrableOn_const (by simp)) measurableSet_Ioc
        fun t ht => h_pt t ht
      rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le (by positivity), sub_zero] at h_mono
      exact h_mono
    have hden_ge : c' ≤ c' * FKc 1 1 c' := le_mul_of_one_le_right hcpos.le hFK_ge1
    calc (∫ t in Ioc 0 (c' * (xiStar / 2) ^ 2 / 3),
          |combProfile c' (bumpBc d5 N η σs c') t * spinVacHC (c' / 12) t|) / (c' * FKc 1 1 c')
        ≤ ((c' * (xiStar / 2) ^ 2 / 3) * Mpt) / c' :=
          div_le_div₀ (by positivity) hInt_bd hcpos hden_ge
      _ = A₀ * (2 * (c' / 12) + 4) * (1 + c' * (xiStar / 2) ^ 2 / 3) ^ 4 * Real.exp (-c' * δ₀) := by
          dsimp [A₀, Mpt]; field_simp [hcpos.ne']
  -- Squeeze `A₀ * (2*(c'/12) + 4) * (1 + c' * ...)^4 * exp(-c' * δ₀) → 0`:
  let Kpol : ℝ := A₀ * (1 + (xiStar / 2) ^ 2 / 3) ^ 4 / δ₀ ^ 5
  have hKpol_nn : 0 ≤ Kpol := by dsimp [Kpol, A₀]; positivity
  have hlim_zero : Tendsto (fun c' : ℝ => Kpol * ((δ₀ * c') ^ 5 * Real.exp (-(δ₀ * c')))) atTop (𝓝 0) := by
    have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 5).comp (tendsto_id.const_mul_atTop hδ₀_pos)
    simpa [Function.comp, mul_zero] using h1.const_mul Kpol
  refine squeeze_zero' (Eventually.of_forall fun c' => by
      rcases le_total c' 0 with hc | hc
      · have : Ioc (0 : ℝ) (c' * (xiStar / 2) ^ 2 / 3) = ∅ :=
          Ioc_eq_empty (by nlinarith [show (0 : ℝ) ≤ (xiStar / 2) ^ 2 / 3 by positivity])
        simp [this]
      · have hFK0 : 0 ≤ c' * FKc 1 1 c' := by
          rcases eq_or_lt_of_le hc with rfl | hcpos
          · simp
          · exact mul_nonneg hcpos.le (FKc_pos one_pos 1 hcpos).le
        exact div_nonneg (integral_nonneg fun _ => abs_nonneg _) hFK0)
    ?_ hlim_zero
  filter_upwards [h_bound, eventually_ge_atTop (24 : ℝ)] with c' hc' hc24
  have hA₀_nn : 0 ≤ A₀ := by dsimp [A₀]; positivity
  exact hc'.trans (exp_poly_squeeze_bound hA₀_nn hδ₀_pos (by linarith) (by linarith))

/-! ### Section 2b: Hankel transform vacuum source (`O(c')`) and full vacuum-source upper limit -/

private lemma norm_sechSqProfile_I_mul_le {y : ℝ} (hy : |y| ≤ 1 / 2) :
    ‖Upper.Hankel.sechSqProfile ((y : ℂ) * Complex.I)‖ ≤ 2 := by
  have hθ : |π * y / 2| ≤ π / 4 := by
    have h1 : |π * y / 2| = π * |y| / 2 := by
      simp only [abs_div, abs_mul, abs_of_pos Real.pi_pos, show |(2 : ℝ)| = 2 by norm_num]
    rw [h1]; nlinarith [Real.pi_pos]
  have hcos_ge : √2 / 2 ≤ Real.cos (π * y / 2) := by
    have h0 : 0 ≤ π / 4 := by positivity
    have hpi4 : π / 4 ≤ π := by linarith [Real.pi_pos]
    have hmono := Real.strictAntiOn_cos.antitoneOn ⟨abs_nonneg _, hθ.trans hpi4⟩ ⟨h0, hpi4⟩ hθ
    rw [Real.cos_abs, Real.cos_pi_div_four] at hmono
    exact hmono
  have hcos_pos : 0 < Real.cos (π * y / 2) := lt_of_lt_of_le (by positivity) hcos_ge
  have hcos_sq : (1 / 2 : ℝ) ≤ Real.cos (π * y / 2) ^ 2 := by
    have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ √2 / 2) hcos_ge 2
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  unfold Upper.Hankel.sechSqProfile
  have harg : (π : ℂ) * ((y : ℂ) * Complex.I) / 2 = ((π * y / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [harg, Complex.cosh_mul_I, ← Complex.ofReal_cos, norm_div, norm_one, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg hcos_pos.le, one_div]
  exact inv_le_of_inv_le₀ (by norm_num) (by simpa using hcos_sq)

private lemma measurable_kernelK5 : Measurable (fun p : ℝ × ℝ => kernelK 5 p.1 p.2) := by
  unfold kernelK
  have hlim : ∀ p : ℝ × ℝ,
      Tendsto (fun n : ℕ => (2 * π * p.2) ^ (5 - 1) * ∑ k ∈ Finset.range n, kernelKTerm 5 p.1 p.2 k)
        atTop (𝓝 ((2 * π * p.2) ^ (5 - 1) * ∑' k, kernelKTerm 5 p.1 p.2 k)) := fun p =>
    tendsto_const_nhds.mul (summable_kernelKTerm 5 p.1 p.2).hasSum.tendsto_sum_nat
  refine measurable_of_tendsto_metrizable
    (f := fun n (p : ℝ × ℝ) => (2 * π * p.2) ^ (5 - 1) * ∑ k ∈ Finset.range n, kernelKTerm 5 p.1 p.2 k)
    (fun n => (by fun_prop : Measurable fun p : ℝ × ℝ => (2 * π * p.2) ^ (5 - 1)).mul
      (Finset.measurable_sum _ fun k _ => by unfold kernelKTerm; fun_prop))
    (tendsto_pi_nhds.mpr hlim)

private lemma kernelK_le_of_le {w : ℕ} {a₁ a₂ t : ℝ} (ha₁ : 0 ≤ a₁) (ha : a₁ ≤ a₂) (ht : 0 ≤ t) :
    kernelK w a₁ t ≤ kernelK w a₂ t := by
  unfold kernelK
  refine mul_le_mul_of_nonneg_left ((summable_kernelKTerm w a₁ t).tsum_le_tsum (fun k => ?_)
    (summable_kernelKTerm w a₂ t)) (by positivity)
  unfold kernelKTerm
  gcongr

lemma FVc_q_eq (q c' : ℝ) : FVc q c' = q * FVc 1 c' := by
  unfold FVc; ring

lemma FKc_q_eq (q : ℝ) (f : ℕ) (c' : ℝ) : FKc q f c' = q * FKc 1 f c' := by
  unfold FKc; rw [FVc_q_eq]; ring

/-- The Hankel-transform vacuum integral `∫₀^∞ (𝓗₅ h₅)(t) H_C(t) dt` is `O(c')`:
from `spinVacB_eq_integral`, Fubini exchange, and `StripContinuation.vacuum_kernel`. -/
lemma bumpG_hat_vac_source_le (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4)
    (σs : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ c' in atTop,
      IntegrableOn (fun t =>
        hankelTransform 5 (combProfile c' (bumpBc (rpParams 4).bumpData N η σs c')) t *
          spinVacHC (c' / 12) t) (Ioi 0) ∧
      |∫ t in Ioi 0,
        hankelTransform 5 (combProfile c' (bumpBc (rpParams 4).bumpData N η σs c')) t *
          spinVacHC (c' / 12) t| ≤ C * c' := by
  let d5 := (rpParams 4).bumpData
  refine ⟨1, zero_le_one, ?_⟩
  filter_upwards [bumpSig_phaseHyp d5 N hN hη0 hη1 σs,
    bumpSig_k7W spinMomentW5Prob d5 N hN hη0 hη1 σs,
    designComb_innerCombHyp_of_admissible 1 le_rfl (η₀ := 1 / 4) (by norm_num) (by norm_num),
    eventually_ge_atTop (48 : ℝ)] with c' hph hk7 hin hc48
  have hcpos : 0 < c' := by linarith
  have ha4 : 4 ≤ c' / 12 := by linarith
  have ha2 : 2 ≤ c' / 12 := by linarith
  let a : ℝ := c' / 12
  let B := bumpBc d5 N η σs c'
  let h₅ := combProfile c' B
  let ĥ₅ := hankelTransform 5 h₅
  obtain ⟨hfN, hA, -⟩ := hph (bumpCut d5 N c') (le_bumpCut d5 N c')
  have hI : InnerCombHyp c' B := hin (bumpCut d5 N c') _ _ hfN hA
  obtain ⟨C₀, -, hd1, hd2, -⟩ := hk7 (bumpCut d5 N c') (le_bumpCut d5 N c')
  have hcont : ContinuousOn h₅ (Ici 0) := hI.continuousOn_combProfile hcpos
  have hint_h : Integrable (radialLift 5 h₅) :=
    radialLift_integrable_of_decay (by norm_num) hcpos hcont hd1
  have hcont' : ContinuousOn ĥ₅ (Ici 0) := continuousOn_hankelTransform (by norm_num) hint_h
  have hint_h' : Integrable (radialLift 5 ĥ₅) :=
    radialLift_integrable_of_decay (by norm_num) hcpos hcont' hd2
  have hp : RadialFourierPair 5 h₅ ĥ₅ :=
    radialFourierPair_hankelTransform (by norm_num) hcont hint_h hint_h'
  have hk' : KernelIntegrable 5 a ĥ₅ :=
    kernelIntegrable_of_decay (by norm_num) hcpos hcont' hd2
  have hS : StripContinuation c' h₅ (combH0 B) := hI.stripContinuation hcpos
  have hvac_int : ∀ α ∈ Icc 0 a,
      |∫ t in Ioi 0, ĥ₅ t * spinVacuumD 5 α t| ≤ 2 := fun α hα => by
    have hvk := hS.vacuum_kernel (by norm_num : 1 ≤ 5) hcpos hp hk' hα.1 hα.2
    have h2pi_eq : ∫ t in Ioi 0, ĥ₅ t * spinVacuumD 5 α t =
        2 * π * ∫ t in Ioi 0, ĥ₅ t * kernelK 5 α t := by
      unfold spinVacuumD
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
    have hy_le : |√(3 * α / c')| ≤ 1 / 2 := by
      have harg0 : 0 ≤ 3 * α / c' := div_nonneg (mul_nonneg (by norm_num) hα.1) hcpos.le
      have harg1 : 3 * α / c' ≤ (1 / 2 : ℝ) ^ 2 := by
        rw [div_le_iff₀ hcpos]; dsimp [a] at hα; linarith [hα.2]
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact (Real.sqrt_le_sqrt harg1).trans_eq (Real.sqrt_sq (by norm_num))
    have hb_im : |(bAlpha c' α).im| ≤ 1 / 2 := by
      unfold bAlpha; simpa using hy_le
    have hsech : ‖Upper.Hankel.sechSqProfile (bAlpha c' α)‖ ≤ 2 := by
      unfold bAlpha
      simpa [mul_comm Complex.I] using norm_sechSqProfile_I_mul_le hy_le
    have hcomb_bd : ‖combH0 B (bAlpha c' α)‖ ≤ 2 := by
      unfold combH0
      rw [norm_mul]
      exact (mul_le_mul hsech (hI.bound _ hb_im) (norm_nonneg _) (by positivity)).trans (by norm_num)
    rw [h2pi_eq, ← Real.norm_eq_abs, ← Complex.norm_real, hvk]
    exact hcomb_bd
  have hInt_hat_HC : IntegrableOn (fun t => ĥ₅ t * spinVacHC a t) (Ioi 0) := by
    refine (hk'.const_mul ((2 * a + 4) * (2 * π))).mono' ?_
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
    · exact ((hcont'.mono Ioi_subset_Ici_self).mul (continuous_spinVacHC a).continuousOn).aestronglyMeasurable
        measurableSet_Ioi
    · have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
      have hHC := spinVacHC_abs_le ha2 ht0
      unfold spinVacuumD at hHC
      rw [Real.norm_eq_abs, abs_mul]
      calc |ĥ₅ t| * |spinVacHC a t|
          ≤ |ĥ₅ t| * ((2 * a + 4) * (2 * π * kernelK 5 a t)) :=
            mul_le_mul_of_nonneg_left hHC (abs_nonneg _)
        _ = (2 * a + 4) * (2 * π) * (|ĥ₅ t| * kernelK 5 a t) := by ring
  have h_piece_fubini : ∀ (α₁ α₂ : ℝ) (w : ℝ → ℝ), Continuous w →
      0 ≤ α₁ → α₁ < α₂ → α₂ ≤ a → ∀ (M : ℝ), (∀ α ∈ Ioc α₁ α₂, |w α| ≤ M) →
      IntegrableOn (fun t => ĥ₅ t * ∫ α in α₁..α₂, w α * spinVacuumD 5 α t) (Ioi 0) ∧
      |∫ t in Ioi 0, ĥ₅ t * ∫ α in α₁..α₂, w α * spinVacuumD 5 α t| ≤ (α₂ - α₁) * M * 2 := by
    intro α₁ α₂ w hw_cont hα0 hα12 hα2 M hwM
    have hM_nn : 0 ≤ M := (abs_nonneg (w α₂)).trans (hwM α₂ ⟨hα12, le_rfl⟩)
    let F : ℝ → ℝ → ℝ := fun t α => ĥ₅ t * (w α * spinVacuumD 5 α t)
    have h_meas_prod : AEStronglyMeasurable (Function.uncurry F)
        ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioc α₁ α₂))) := by
      have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => ĥ₅ p.1)
          ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioc α₁ α₂))) :=
        ((hcont'.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi).comp_quasiMeasurePreserving
          Measure.quasiMeasurePreserving_fst
      have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => w p.2)
          ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioc α₁ α₂))) :=
        (hw_cont.measurable.comp measurable_snd).aestronglyMeasurable
      have h3 : AEStronglyMeasurable (fun p : ℝ × ℝ => spinVacuumD 5 p.2 p.1)
          ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioc α₁ α₂))) := by
        unfold spinVacuumD
        exact (measurable_const.mul (measurable_kernelK5.comp (measurable_snd.prodMk measurable_fst))).aestronglyMeasurable
      exact h1.mul (h2.mul h3)
    have h_dom_t : Integrable (fun t : ℝ => (2 * π * M) * (|ĥ₅ t| * kernelK 5 a t))
        (volume.restrict (Ioi 0)) := hk'.const_mul (2 * π * M)
    have h_dom_α : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc α₁ α₂)) :=
      integrableOn_const (by simp)
    have hInt_prod : Integrable (Function.uncurry F)
        ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioc α₁ α₂))) := by
      refine (h_dom_t.mul_prod h_dom_α).mono' h_meas_prod ?_
      have hm1 : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi 0)), t ∈ Ioi 0 :=
        (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun _ h => h)
      have hm2 : ∀ᵐ α : ℝ ∂(volume.restrict (Ioc α₁ α₂)), α ∈ Ioc α₁ α₂ :=
        (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun _ h => h)
      have hae : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioc α₁ α₂))),
          p.1 ∈ Ioi (0 : ℝ) ∧ p.2 ∈ Ioc α₁ α₂ :=
        (Measure.quasiMeasurePreserving_fst.ae hm1).and (Measure.quasiMeasurePreserving_snd.ae hm2)
      filter_upwards [hae] with p hp
      · rcases hp with ⟨ht, hα⟩
        have ht0 : 0 ≤ p.1 := (mem_Ioi.mp ht).le
        have hα_nn : 0 ≤ p.2 := hα0.trans hα.1.le
        have hK_le : kernelK 5 p.2 p.1 ≤ kernelK 5 a p.1 := kernelK_le_of_le hα_nn (hα.2.trans hα2) ht0
        have hK_nn : 0 ≤ kernelK 5 p.2 p.1 := by
          unfold kernelK
          exact mul_nonneg (by positivity) (tsum_nonneg fun k => by unfold kernelKTerm; positivity)
        rw [Real.norm_eq_abs]
        show |ĥ₅ p.1 * (w p.2 * (2 * π * kernelK 5 p.2 p.1))| ≤
          (2 * π * M) * (|ĥ₅ p.1| * kernelK 5 a p.1) * 1
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos Real.two_pi_pos, abs_of_nonneg hK_nn]
        calc |ĥ₅ p.1| * (|w p.2| * (2 * π * kernelK 5 p.2 p.1))
            ≤ |ĥ₅ p.1| * (M * (2 * π * kernelK 5 a p.1)) := by
              gcongr; exact hwM p.2 hα
          _ = (2 * π * M) * (|ĥ₅ p.1| * kernelK 5 a p.1) * 1 := by ring
    have h_eq_t : ∀ t ∈ Ioi 0, ĥ₅ t * ∫ α in α₁..α₂, w α * spinVacuumD 5 α t =
        ∫ α in Ioc α₁ α₂, F t α := fun t _ => by
      rw [intervalIntegral.integral_of_le hα12.le, ← integral_const_mul]
    have hInt_t : IntegrableOn (fun t => ĥ₅ t * ∫ α in α₁..α₂, w α * spinVacuumD 5 α t) (Ioi 0) :=
      hInt_prod.integral_prod_left.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => (h_eq_t t ht).symm)
    refine ⟨hInt_t, ?_⟩
    have h_swap : ∫ t in Ioi 0, ĥ₅ t * ∫ α in α₁..α₂, w α * spinVacuumD 5 α t =
        ∫ α in Ioc α₁ α₂, ∫ t in Ioi 0, F t α := by
      rw [setIntegral_congr_fun measurableSet_Ioi h_eq_t]
      exact integral_integral_swap hInt_prod
    have h_inner : ∀ α ∈ Ioc α₁ α₂, |∫ t in Ioi 0, F t α| ≤ M * 2 := fun α hα => by
      have h1 : ∫ t in Ioi 0, F t α = w α * ∫ t in Ioi 0, ĥ₅ t * spinVacuumD 5 α t := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => by dsimp [F]; ring
      rw [h1, abs_mul]
      exact mul_le_mul (hwM α hα) (hvac_int α ⟨hα0.trans hα.1.le, hα.2.trans hα2⟩) (abs_nonneg _) hM_nn
    rw [h_swap]
    calc |∫ α in Ioc α₁ α₂, ∫ t in Ioi 0, F t α|
        ≤ ∫ α in Ioc α₁ α₂, |∫ t in Ioi 0, F t α| := abs_integral_le_integral_abs
      _ ≤ ∫ _ in Ioc α₁ α₂, M * 2 :=
          setIntegral_mono_on (hInt_prod.integral_prod_right.abs) (integrableOn_const (by simp))
            measurableSet_Ioc h_inner
      _ = (α₂ - α₁) * M * 2 := by
          rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hα12.le]; ring
  have ha4' : 4 ≤ a := ha4
  have hw1 : ∀ α ∈ Ioc (a - 2) (a - 1), |(α - 3 * a + 6) / 2| ≤ a := fun α hα => by
    rw [abs_le]; constructor <;> linarith [hα.1, hα.2, ha4']
  have hw2 : ∀ α ∈ Ioc (a - 1) a, |(3 * a - α) / 2| ≤ 2 * a := fun α hα => by
    rw [abs_le]; constructor <;> linarith [hα.1, hα.2, ha4']
  obtain ⟨hInt1, hbd1⟩ := h_piece_fubini (a - 2) (a - 1) (fun α => (α - 3 * a + 6) / 2)
    (by fun_prop) (by linarith) (by linarith) (by linarith) a hw1
  obtain ⟨hInt2, hbd2⟩ := h_piece_fubini (a - 1) a (fun α => (3 * a - α) / 2)
    (by fun_prop) (by linarith) (by linarith) le_rfl (2 * a) hw2
  have hInt3 : IntegrableOn (fun t => 2 * (ĥ₅ t * spinVacuumD 5 (a - 1) t)) (Ioi 0) := by
    have h3 : IntegrableOn (fun t => ĥ₅ t * spinVacuumD 5 (a - 1) t) (Ioi 0) := by
      have hk_sh := hk'.shift hcont' (by linarith [ha4'] : 0 ≤ a - 1) (by linarith)
      exact (hk_sh.const_mul (2 * π)).congr (ae_restrict_of_forall_mem measurableSet_Ioi fun t _ => by
        unfold spinVacuumD; ring)
    exact h3.const_mul 2
  have h_eq_fn : ∀ t : ℝ, ĥ₅ t * spinVacHC a t =
      ((ĥ₅ t * ∫ α in (a - 2)..(a - 1), (α - 3 * a + 6) / 2 * spinVacuumD 5 α t) +
        (ĥ₅ t * ∫ α in (a - 1)..a, (3 * a - α) / 2 * spinVacuumD 5 α t)) -
        2 * (ĥ₅ t * spinVacuumD 5 (a - 1) t) := fun t => by
    unfold spinVacHC; rw [spinVacB_eq_integral]; ring
  refine ⟨hInt_hat_HC, ?_⟩
  have h_int_split : ∫ t in Ioi 0, ĥ₅ t * spinVacHC a t =
      ((∫ t in Ioi 0, ĥ₅ t * ∫ α in (a - 2)..(a - 1), (α - 3 * a + 6) / 2 * spinVacuumD 5 α t) +
        (∫ t in Ioi 0, ĥ₅ t * ∫ α in (a - 1)..a, (3 * a - α) / 2 * spinVacuumD 5 α t)) -
        ∫ t in Ioi 0, 2 * (ĥ₅ t * spinVacuumD 5 (a - 1) t) := by
    simp_rw [h_eq_fn]
    have hsub := integral_sub (hInt1.add hInt2) hInt3
    simp only [Pi.add_apply] at hsub
    have hadd := integral_add hInt1 hInt2
    exact hsub.trans (by rw [hadd])
  have hbd3 : |∫ t in Ioi 0, 2 * (ĥ₅ t * spinVacuumD 5 (a - 1) t)| ≤ 4 := by
    rw [integral_const_mul, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    linarith [hvac_int (a - 1) ⟨by linarith [ha4'], by linarith [ha4']⟩]
  rw [h_int_split]
  have htri1 := abs_sub ((∫ t in Ioi 0, ĥ₅ t * ∫ α in (a - 2)..(a - 1), (α - 3 * a + 6) / 2 * spinVacuumD 5 α t) +
    (∫ t in Ioi 0, ĥ₅ t * ∫ α in (a - 1)..a, (3 * a - α) / 2 * spinVacuumD 5 α t))
    (∫ t in Ioi 0, 2 * (ĥ₅ t * spinVacuumD 5 (a - 1) t))
  have htri2 := abs_add_le
    (∫ t in Ioi 0, ĥ₅ t * ∫ α in (a - 2)..(a - 1), (α - 3 * a + 6) / 2 * spinVacuumD 5 α t)
    (∫ t in Ioi 0, ĥ₅ t * ∫ α in (a - 1)..a, (3 * a - α) / 2 * spinVacuumD 5 α t)
  dsimp [a] at hbd1 hbd2 ha4 ⊢
  linarith

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Spin.lobe_left_exp_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lobe_left_exp_decay

/-- info: 'FormalResearch.ModularBootstrap.Spin.bumpG_hat_vac_source_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bumpG_hat_vac_source_le

end FormalResearch.ModularBootstrap.Spin
