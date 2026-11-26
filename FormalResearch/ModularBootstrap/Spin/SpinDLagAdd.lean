module

public import FormalResearch.ModularBootstrap.Spin.SpinDDefs
public import FormalResearch.ModularBootstrap.LP.Cayley

/-!
# Multivariate Laguerre addition formula (`dsl:lag-add`) and shifted Cauchy bound (`sd:eCauchy`)

Proves:
- `spin_lagL_add`: `lagL (w₁ + w₂) k (x₁ + x₂) = ∑ i ∈ range (k + 1), lagL w₁ i x₁ * lagL w₂ (k - i) x₂`
  for all `w₁, w₂ > 0`, `k : ℕ`, `x₁, x₂ : ℝ`.
- `spin_lagP_comp_add_mem_polySpace`: for `Odd k`, `k ≤ N`, the radial function
  `(t_L, t_R) ↦ lagP 1 k (t_L + t_R)` belongs to `spinOddLagPolySpace N`.
- `spin_abs_lagPsi_le_shifted`: for `w > 0`, `0 < θ < 1`, `B ≥ 0`, `t ≥ -B`,
  `|lagPsi w k t| ≤ (1 - θ)^{-w} exp(2π B / s_θ) θ^{-k} exp(-2π s_θ t)` (`sd:eCauchy`).
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set Finset
open scoped Real

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.LP

/-! ### Section 1: Laguerre addition formula (`dsl:lag-add`) -/

private lemma summable_norm_lagL_mul_pow {w : ℝ} (hw : 0 < w) (x : ℝ) {z : ℝ} (hz : |z| < 1) :
    Summable (fun k : ℕ => ‖lagL w k x * z ^ k‖) := by
  set r : ℝ := (|z| + 1) / 2 with hr
  have hr_pos : 0 < r := by rw [hr]; linarith [abs_nonneg z]
  have hr_lt1 : r < 1 := by rw [hr]; linarith
  have hz_lt_r : |z| < r := by rw [hr]; linarith
  have hhas := hasSum_lagL_gen_real hw x (z := r) (by rwa [abs_of_pos hr_pos])
  have htend : Tendsto (fun k : ℕ => lagL w k x * r ^ k) atTop (𝓝 0) :=
    hhas.summable.tendsto_atTop_zero
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp htend 1 one_pos)
  let M : ℝ := max 1 ((Finset.range (N + 1)).sup' ⟨0, by simp⟩ (fun k => |lagL w k x * r ^ k|))
  have hM_ge1 : 1 ≤ M := le_max_left _ _
  have hbd : ∀ k : ℕ, |lagL w k x| * r ^ k ≤ M := by
    intro k
    by_cases hk : k < N + 1
    · have hle := Finset.le_sup' (f := fun j => |lagL w j x * r ^ j|) (Finset.mem_range.mpr hk)
      rw [abs_mul, abs_pow, abs_of_pos hr_pos] at hle
      exact hle.trans (le_max_right _ _)
    · have hge : N ≤ k := by omega
      have hdist := hN k hge
      rw [Real.dist_eq, sub_zero, abs_mul, abs_pow, abs_of_pos hr_pos] at hdist
      exact hdist.le.trans hM_ge1
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    ((summable_geometric_of_lt_one (by positivity : 0 ≤ |z| / r)
      ((div_lt_one hr_pos).mpr hz_lt_r)).mul_left M)
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  have heq : |lagL w k x| * |z| ^ k = (|lagL w k x| * r ^ k) * (|z| / r) ^ k := by
    rw [mul_assoc, ← mul_pow, mul_div_cancel₀ _ hr_pos.ne']
  rw [heq]
  exact mul_le_mul_of_nonneg_right (hbd k) (by positivity)

/-- **Multivariate Laguerre addition formula** (`dsl:lag-add`, `d = 2`):
`L_k^{(w₁ + w₂ - 1)}(x₁ + x₂) = ∑_{i=0}^k L_i^{(w₁ - 1)}(x₁) L_{k - i}^{(w₂ - 1)}(x₂)`. -/
theorem spin_lagL_add {w₁ w₂ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (k : ℕ) (x₁ x₂ : ℝ) :
    lagL (w₁ + w₂) k (x₁ + x₂) =
      ∑ i ∈ Finset.range (k + 1), lagL w₁ i x₁ * lagL w₂ (k - i) x₂ := by
  have hzero : ∀ z : ℝ, |z| < 1 →
      HasSum (fun m : ℕ =>
        (lagL (w₁ + w₂) m (x₁ + x₂) -
          ∑ i ∈ Finset.range (m + 1), lagL w₁ i x₁ * lagL w₂ (m - i) x₂) * z ^ m) 0 := by
    intro z hz
    have h1 := hasSum_lagL_gen_real hw₁ x₁ hz
    have h2 := hasSum_lagL_gen_real hw₂ x₂ hz
    have h12 := hasSum_lagL_gen_real (add_pos hw₁ hw₂) (x₁ + x₂) hz
    let a : ℕ → ℝ := fun i => lagL w₁ i x₁ * z ^ i
    let b : ℕ → ℝ := fun j => lagL w₂ j x₂ * z ^ j
    have ha_norm : Summable (fun i => ‖a i‖) := summable_norm_lagL_mul_pow hw₁ x₁ hz
    have hb_norm : Summable (fun j => ‖b j‖) := summable_norm_lagL_mul_pow hw₂ x₂ hz
    let f : ℕ × ℕ → ℝ := fun p => a p.1 * b p.2
    have hf_norm : Summable (fun p : ℕ × ℕ => ‖f p‖) := by
      have h1 : Summable (fun p : ℕ × ℕ => ‖a p.1‖ * ‖b p.2‖) :=
        ha_norm.mul_of_nonneg hb_norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      exact h1.congr fun p => (norm_mul (a p.1) (b p.2)).symm
    have hf_sum : Summable f := hf_norm.of_norm
    have hf_has : HasSum f (lagGenReal w₁ x₁ z * lagGenReal w₂ x₂ z) := by
      have hfib : ∀ i : ℕ, HasSum (fun j => f (i, j)) (a i * lagGenReal w₂ x₂ z) :=
        fun i => h2.mul_left (a i)
      have houter : HasSum (fun i => a i * lagGenReal w₂ x₂ z)
          (lagGenReal w₁ x₁ z * lagGenReal w₂ x₂ z) := h1.mul_right _
      have h1' := hf_sum.hasSum.prod_fiberwise hfib
      have heq : ∑' p, f p = lagGenReal w₁ x₁ z * lagGenReal w₂ x₂ z := h1'.unique houter
      rw [← heq]; exact hf_sum.hasSum
    have hgen_mul : lagGenReal w₁ x₁ z * lagGenReal w₂ x₂ z = lagGenReal (w₁ + w₂) (x₁ + x₂) z := by
      unfold lagGenReal
      have h1z : 0 < 1 - z := by linarith [(abs_lt.1 hz).2]
      have hpow : (1 - z) ^ (-w₁) * (1 - z) ^ (-w₂) = (1 - z) ^ (-(w₁ + w₂)) := by
        rw [← Real.rpow_add h1z]; congr 1; ring
      have hexp : Real.exp (-x₁ * z / (1 - z)) * Real.exp (-x₂ * z / (1 - z)) =
          Real.exp (-(x₁ + x₂) * z / (1 - z)) := by
        rw [← Real.exp_add]; congr 1; ring
      calc (1 - z) ^ (-w₁) * Real.exp (-x₁ * z / (1 - z)) *
            ((1 - z) ^ (-w₂) * Real.exp (-x₂ * z / (1 - z)))
          = ((1 - z) ^ (-w₁) * (1 - z) ^ (-w₂)) *
            (Real.exp (-x₁ * z / (1 - z)) * Real.exp (-x₂ * z / (1 - z))) := by ring
        _ = (1 - z) ^ (-(w₁ + w₂)) * Real.exp (-(x₁ + x₂) * z / (1 - z)) := by rw [hpow, hexp]
    rw [hgen_mul] at hf_has
    have hσ : HasSum (f ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd)
        (lagGenReal (w₁ + w₂) (x₁ + x₂) z) := (Equiv.hasSum_iff _).2 hf_has
    have hprod_range : HasSum
        (fun m : ℕ => (∑ i ∈ Finset.range (m + 1), lagL w₁ i x₁ * lagL w₂ (m - i) x₂) * z ^ m)
        (lagGenReal (w₁ + w₂) (x₁ + x₂) z) := by
      refine hσ.sigma fun m => ?_
      convert hasSum_fintype (fun c : Finset.HasAntidiagonal.antidiagonal m =>
        (f ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) ⟨m, c⟩) using 1
      simp only [Function.comp, Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
      rw [Finset.sum_coe_sort (Finset.HasAntidiagonal.antidiagonal m) f,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hpow : z ^ i * z ^ (m - i) = z ^ m := by
        rw [← pow_add, Nat.add_sub_cancel' him]
      dsimp only [f]
      calc lagL w₁ i x₁ * lagL w₂ (m - i) x₂ * z ^ m
          = lagL w₁ i x₁ * lagL w₂ (m - i) x₂ * (z ^ i * z ^ (m - i)) := by rw [hpow]
        _ = lagL w₁ i x₁ * z ^ i * (lagL w₂ (m - i) x₂ * z ^ (m - i)) := by ring
    have hsub := h12.sub hprod_range
    rw [sub_self] at hsub
    convert hsub using 1
    ext m; ring
  have hk := coeff_zero_of_hasSum_zero one_pos hzero k
  linarith

/-- For `Odd k` and `k ≤ N`, `(t_L, t_R) ↦ lagP 1 k (t_L + t_R)` lies in `spinOddLagPolySpace N`. -/
theorem spin_lagP_comp_add_mem_polySpace {k N : ℕ} (hk : Odd k) (hkN : k ≤ N) :
    (fun p : ℝ × ℝ => lagP 1 k (p.1 + p.2)) ∈ spinOddLagPolySpace N := by
  have hlagL : (fun p : ℝ × ℝ => lagL 1 k (4 * π * (p.1 + p.2))) =
      ∑ i ∈ Finset.range (k + 1), spinOddLagPolyBasis i (k - i) := by
    ext p
    rw [Finset.sum_apply, show (1 : ℝ) = (1 / 2 : ℝ) + (1 / 2 : ℝ) by norm_num,
      show 4 * π * (p.1 + p.2) = 4 * π * p.1 + 4 * π * p.2 by ring,
      spin_lagL_add (by norm_num) (by norm_num)]
    have hrefl : ∑ i ∈ Finset.range (k + 1),
        lagL (1 / 2) i (4 * π * p.2) * lagL (1 / 2) (k - i) (4 * π * p.1) =
        ∑ i ∈ Finset.range (k + 1),
        lagL (1 / 2) i (4 * π * p.1) * lagL (1 / 2) (k - i) (4 * π * p.2) := by
      rw [← Finset.sum_range_reflect (fun i => lagL (1 / 2) i (4 * π * p.2) * lagL (1 / 2) (k - i) (4 * π * p.1)) (k + 1)]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [show k + 1 - 1 - i = k - i by omega, show k - (k - i) = i by omega, mul_comm]
    have hsum_basis : ∑ i ∈ Finset.range (k + 1), spinOddLagPolyBasis i (k - i) p =
        (1 / 2 : ℝ) * ((∑ i ∈ Finset.range (k + 1),
            lagL (1 / 2) i (4 * π * p.1) * lagL (1 / 2) (k - i) (4 * π * p.2)) +
          (∑ i ∈ Finset.range (k + 1),
            lagL (1 / 2) i (4 * π * p.2) * lagL (1 / 2) (k - i) (4 * π * p.1))) := by
      unfold spinOddLagPolyBasis
      rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [hsum_basis, hrefl]
    ring
  have hmemL : (fun p : ℝ × ℝ => lagL 1 k (4 * π * (p.1 + p.2))) ∈ spinOddLagPolySpace N := by
    rw [hlagL]
    refine Submodule.sum_mem _ fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    refine Submodule.subset_span ⟨i, k - i, ?_, ?_, rfl⟩
    · rwa [Nat.add_sub_cancel' hik]
    · omega
  have hscale : (fun p : ℝ × ℝ => lagP 1 k (p.1 + p.2)) =
      ((-1 : ℝ) ^ k * (k.factorial : ℝ) / (4 * π) ^ k) •
        (fun p : ℝ × ℝ => lagL 1 k (4 * π * (p.1 + p.2))) := by
    ext p
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [lagP_eq]
  rw [hscale]
  exact Submodule.smul_mem _ _ hmemL

/-! ### Section 2: Shifted Cauchy bound (`sd:eCauchy`) for `t ≥ -B` -/

private lemma lagL_nonneg_of_nonpos {w : ℝ} (hw : 0 < w) {x : ℝ} (hx : x ≤ 0) (k : ℕ) :
    0 ≤ lagL w k x := by
  rw [lagL_eq_sum]
  refine Finset.sum_nonneg fun j _ => ?_
  have h1 : 0 ≤ (-x) ^ j := pow_nonneg (by linarith) j
  have h2 : 0 ≤ lagCoef w j (k - j) := (lagCoef_pos hw j (k - j)).le
  have h3 : (-1 : ℝ) ^ j * x ^ j = (-x) ^ j := by
    rw [← mul_pow]; ring_nf
  have heq : (-1 : ℝ) ^ j * lagCoef w j (k - j) / (j.factorial : ℝ) * x ^ j =
      lagCoef w j (k - j) * ((-1 : ℝ) ^ j * x ^ j) / (j.factorial : ℝ) := by ring
  rw [heq, h3]
  positivity

private lemma abs_lagL_le_nonpos {w : ℝ} (hw : 0 < w) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {x : ℝ} (hx : x ≤ 0) (k : ℕ) :
    |lagL w k x| ≤ θ⁻¹ ^ k * ((1 - θ) ^ (-w) * Real.exp (-x * θ / (1 - θ))) := by
  have hnn : ∀ j : ℕ, 0 ≤ lagL w j x * θ ^ j := fun j =>
    mul_nonneg (lagL_nonneg_of_nonpos hw hx j) (pow_nonneg hθ0.le j)
  have hhas := hasSum_lagL_gen_real hw x (z := θ) (by rwa [abs_of_pos hθ0])
  have hle : lagL w k x * θ ^ k ≤ lagGenReal w x θ := by
    rw [← hhas.tsum_eq]
    exact hhas.summable.le_tsum k fun j _ => hnn j
  rw [abs_of_nonneg (lagL_nonneg_of_nonpos hw hx k)]
  have hth : 0 < θ ^ k := pow_pos hθ0 k
  calc lagL w k x = (lagL w k x * θ ^ k) * θ⁻¹ ^ k := by
        rw [inv_pow]; field_simp [hth.ne']
    _ ≤ lagGenReal w x θ * θ⁻¹ ^ k := mul_le_mul_of_nonneg_right hle (by positivity)
    _ = θ⁻¹ ^ k * ((1 - θ) ^ (-w) * Real.exp (-x * θ / (1 - θ))) := by
        unfold lagGenReal; ring

/-- **Shifted Cauchy bound** (`sd:eCauchy`): for `w > 0`, `0 < θ < 1`, `B ≥ 0`, and `t ≥ -B`,
`|lagPsi w k t| ≤ (1 - θ)^{-w} exp(2π B / s_θ) θ^{-k} exp(-2π s_θ t)`. -/
theorem spin_abs_lagPsi_le_shifted {w : ℝ} (hw : 0 < w) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {B t : ℝ} (hB : 0 ≤ B) (ht : -B ≤ t) (k : ℕ) :
    |lagPsi w k t| ≤
      (1 - θ) ^ (-w) * Real.exp (2 * π * B / sTheta θ) * θ⁻¹ ^ k *
        Real.exp (-2 * π * sTheta θ * t) := by
  have hs0 : 0 < sTheta θ := sTheta_pos hθ0 hθ1
  rcases le_total 0 t with ht0 | ht0
  · have h := abs_lagPsi_le hw hθ0 hθ1 ht0 k
    have hexp1 : (1 : ℝ) ≤ Real.exp (2 * π * B / sTheta θ) :=
      Real.one_le_exp (by positivity)
    have h1θ : 0 ≤ (1 - θ) ^ (-w) := Real.rpow_nonneg (by linarith) _
    have hth : 0 ≤ θ⁻¹ ^ k := by positivity
    have he : 0 ≤ Real.exp (-2 * π * sTheta θ * t) := (Real.exp_pos _).le
    calc |lagPsi w k t|
        ≤ (1 - θ) ^ (-w) * θ⁻¹ ^ k * Real.exp (-2 * π * sTheta θ * t) := h
      _ = (1 - θ) ^ (-w) * 1 * θ⁻¹ ^ k * Real.exp (-2 * π * sTheta θ * t) := by ring
      _ ≤ (1 - θ) ^ (-w) * Real.exp (2 * π * B / sTheta θ) * θ⁻¹ ^ k *
          Real.exp (-2 * π * sTheta θ * t) := by gcongr
  · have hx : 4 * π * t ≤ 0 := by nlinarith [Real.pi_pos]
    have h := abs_lagL_le_nonpos hw hθ0 hθ1 hx k
    unfold lagPsi
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1θ : 0 < 1 - θ := by linarith
    have hexp : Real.exp (-2 * π * t) * Real.exp (-(4 * π * t) * θ / (1 - θ)) ≤
        Real.exp (2 * π * B / sTheta θ) * Real.exp (-2 * π * sTheta θ * t) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have h1 : -2 * π * t + -(4 * π * t) * θ / (1 - θ) = -2 * π * t / sTheta θ := by
        unfold sTheta; field_simp [h1θ.ne', (show 1 + θ ≠ 0 by linarith)]; ring
      rw [h1]
      have hs_lt1 : sTheta θ < 1 := by
        unfold sTheta; exact (div_lt_one (by linarith)).mpr (by linarith)
      have hdiff_pos : 0 ≤ 1 / sTheta θ - sTheta θ := by
        have : sTheta θ ≤ 1 / sTheta θ := by
          rw [le_div_iff₀ hs0]; nlinarith
        linarith
      have hnt : 0 ≤ -t := by linarith
      have hntB : -t ≤ B := by linarith
      have hbound1 : 2 * π * (-t) * (1 / sTheta θ - sTheta θ) ≤ 2 * π * B / sTheta θ := by
        have hstep1 : 2 * π * (-t) * (1 / sTheta θ - sTheta θ) ≤
            2 * π * B * (1 / sTheta θ - sTheta θ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hntB (by positivity)) hdiff_pos
        have hstep2 : 2 * π * B * (1 / sTheta θ - sTheta θ) ≤ 2 * π * B / sTheta θ := by
          have : 0 ≤ 2 * π * B * sTheta θ := by positivity
          have : 2 * π * B * (1 / sTheta θ - sTheta θ) = 2 * π * B / sTheta θ - 2 * π * B * sTheta θ := by
            ring
          linarith
        exact hstep1.trans hstep2
      have hident : -2 * π * t / sTheta θ =
          -2 * π * sTheta θ * t + 2 * π * (-t) * (1 / sTheta θ - sTheta θ) := by ring
      linarith
    calc Real.exp (-2 * π * t) * |lagL w k (4 * π * t)|
        ≤ Real.exp (-2 * π * t) *
            (θ⁻¹ ^ k * ((1 - θ) ^ (-w) * Real.exp (-(4 * π * t) * θ / (1 - θ)))) := by gcongr
      _ = (1 - θ) ^ (-w) * θ⁻¹ ^ k *
            (Real.exp (-2 * π * t) * Real.exp (-(4 * π * t) * θ / (1 - θ))) := by ring
      _ ≤ (1 - θ) ^ (-w) * θ⁻¹ ^ k *
            (Real.exp (2 * π * B / sTheta θ) * Real.exp (-2 * π * sTheta θ * t)) := by
          gcongr
      _ = (1 - θ) ^ (-w) * Real.exp (2 * π * B / sTheta θ) * θ⁻¹ ^ k *
            Real.exp (-2 * π * sTheta θ * t) := by ring

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Spin.spin_lagL_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spin_lagL_add

/-- info: 'FormalResearch.ModularBootstrap.Spin.spin_lagP_comp_add_mem_polySpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spin_lagP_comp_add_mem_polySpace

/-- info: 'FormalResearch.ModularBootstrap.Spin.spin_abs_lagPsi_le_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spin_abs_lagPsi_le_shifted

end FormalResearch.ModularBootstrap.Spin
