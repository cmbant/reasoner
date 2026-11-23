module

public import FormalResearch.ModularBootstrap.Upper.Ramped.CombToAirySm
public import FormalResearch.ModularBootstrap.Upper.Ramped.CombToAiryXiSum
public import FormalResearch.ModularBootstrap.Upper.Window.Identification
public import FormalResearch.ModularBootstrap.Upper.Window.ContinuumPotential

/-!
# Exact splitting of the comb potential: Step 1 of Proposition 1.2(2) (`rem:P1.2`)

`E_K(x) = f_x(χ'_1) + ∑_{k=2}^K log q'_k - 2∫_{1/4}^{K+1/2} f_x(χ_a) da` equals, for every `K ≥ 1` and every
`x ∈ [ξ_*/2, ξ_* + 1/2]` that is not a site of the design,
`-(3/2) log λ + P_K + Sm_K + ∑_{k=2}^K Ξ_k` (`combEK_eq`), where
`P_K = log|σ - σ_1| + ∑_{k=2}^K log((σ - σ_k)² + ε̂_k²) + FQ_{A_K}(σ)` (`pBracket`) is the logarithm of the
window approximant `M_K(σ)` of `upper_transfer.tex` Lemma W (up to `-2π σ_-^{3/2}` and the sign), `σ = τ(x)/λ`.
-/

@[expose] public section

open Filter Topology Set Finset MeasureTheory
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Window

/-- `E_K(x) = f_x(χ'_1) + ∑_{k=2}^K log q'_k - 2∫_{1/4}^{K+1/2} f_x(χ_a) da`. -/
noncomputable def combEK (c' : ℝ) (σ η : ℕ → ℝ) (x : ℝ) (K : ℕ) : ℝ :=
  realLogT x (siteX c' σ 1) + ∑ k ∈ Finset.Icc 2 K, Real.log (qPair c' σ η k x) -
    2 * ∫ a in (1 / 4 : ℝ)..((K : ℝ) + 1 / 2), realLogT x (chiQuantile c' a)

/-- The window widths `ε̂_k = η_k (Φ_{k+1} - Φ_k)`. -/
noncomputable def epsHat (η : ℕ → ℝ) (k : ℕ) : ℝ :=
  η k * (phiQuantile ((k : ℝ) + 1) - phiQuantile (k : ℝ))

/-- `P_K = log|σ - σ_1| + ∑_{k=2}^K log((σ - σ_k)² + ε̂_k²) + FQ_{A_K}(σ)`, `σ = τ(x)/λ`. -/
noncomputable def pBracket (c' : ℝ) (σ η : ℕ → ℝ) (x : ℝ) (K : ℕ) : ℝ :=
  Real.log |sigmaOf c' x - σ 1| +
    ∑ k ∈ Finset.Icc 2 K, Real.log ((sigmaOf c' x - σ k) ^ 2 + epsHat η k ^ 2) +
    continuumFQ (continuumAK K) (sigmaOf c' x)

lemma phiQuantile_injOn : Set.InjOn phiQuantile (Set.Ici (1 / 4 : ℝ)) := by
  intro a ha b hb hab
  have h := (Real.strictMonoOn_rpow_Ici_of_exponent_pos (by norm_num : (0 : ℝ) < 2 / 3)).injOn
    (show a - 1 / 4 ∈ Set.Ici (0 : ℝ) from sub_nonneg.2 ha)
    (show b - 1 / 4 ∈ Set.Ici (0 : ℝ) from sub_nonneg.2 hb) hab
  linarith

/-- `∫_{1/4}^{K+1/2} f_x(χ_a) da = (K + 1/4) log λ - FQ_{A_K}(σ)/2 + ∫_{1/4}^{K+1/2} 𝒦(x, χ_a) da`. -/
theorem integral_realLogT_eq {c' : ℝ} (hc' : 0 < c') {x : ℝ} (hx : x ∈ langerX (1 / 2)) (K : ℕ) :
    ∫ a in (1 / 4 : ℝ)..((K : ℝ) + 1 / 2), realLogT x (chiQuantile c' a) =
      ((K : ℝ) + 1 / 4) * Real.log (lambdaComb c') - continuumFQ (continuumAK K) (sigmaOf c' x) / 2 +
        ∫ a in (1 / 4 : ℝ)..((K : ℝ) + 1 / 2), langerK x (chiQuantile c' a) := by
  obtain ⟨A, hA, hK⟩ := kernelHyp_langerK
  have hG := hK x hx
  have hlp := lamPos hc'
  have hxpos : 0 < x := by have := xiStar_pos; linarith [hx.1]
  have hKle : (1 / 4 : ℝ) ≤ (K : ℝ) + 1 / 2 := by linarith [Nat.cast_nonneg (α := ℝ) K]
  have hI1 : IntervalIntegrable (fun a : ℝ => Real.log |sigmaOf c' x - phiQuantile a|) volume
      (1 / 4) ((K : ℝ) + 1 / 2) := intervalIntegrable_log_abs_phiQuantile _ _ hKle
  have hI2 := intervalIntegrable_comp_chi hc' hG (show (1 / 4 : ℝ) ≤ 1 / 4 from le_rfl) hKle
  have hae : ∀ᵐ a ∂volume, a ∈ Ι (1 / 4 : ℝ) ((K : ℝ) + 1 / 2) →
      realLogT x (chiQuantile c' a) =
        Real.log (lambdaComb c') + Real.log |sigmaOf c' x - phiQuantile a| +
          langerK x (chiQuantile c' a) := by
    have hcount : Set.Countable {a : ℝ | 1 / 4 ≤ a ∧ phiQuantile a = sigmaOf c' x} := by
      refine Set.Subsingleton.countable ?_
      intro a ha b hb
      exact phiQuantile_injOn (Set.mem_Ici.2 ha.1) (Set.mem_Ici.2 hb.1) (ha.2.trans hb.2.symm)
    filter_upwards [hcount.ae_notMem volume] with a ha hmem
    rw [Set.uIoc_of_le (by linarith : (1 / 4 : ℝ) ≤ (K : ℝ) + 1 / 2)] at hmem
    have ha14 : (1 / 4 : ℝ) ≤ a := hmem.1.le
    have hne : phiQuantile a ≠ sigmaOf c' x := fun h => ha ⟨ha14, h⟩
    have hχ := (chiQuantile_spec hc' ha14).1
    have hypos : 0 < chiQuantile c' a := by have := xiStar_pos; linarith
    have hτ := langerTau_chiQuantile hc' ha14
    have hτx : langerTau x = lambdaComb c' * sigmaOf c' x := by unfold sigmaOf; field_simp
    have hxy : chiQuantile c' a ≠ x := by
      intro h0
      apply hne
      have : lambdaComb c' * phiQuantile a = lambdaComb c' * sigmaOf c' x := by
        rw [← hτ, ← hτx, h0]
      exact mul_left_cancel₀ hlp.ne' this
    rw [realLogT_eq_log_add_langerK hxpos hypos hxy, hτ, hτx, ← mul_sub, abs_mul,
      abs_of_pos hlp, Real.log_mul hlp.ne' (abs_ne_zero.2 (sub_ne_zero.2 (Ne.symm hne)))]
  rw [intervalIntegral.integral_congr_ae hae]
  rw [intervalIntegral.integral_add ((intervalIntegrable_const).add hI1) hI2,
    intervalIntegral.integral_add intervalIntegrable_const hI1, intervalIntegral.integral_const,
    continuumFQ_AK_eq]
  simp only [smul_eq_mul]
  have : ((K : ℝ) + 1 / 2 - 1 / 4) = (K : ℝ) + 1 / 4 := by ring
  rw [this]
  ring

lemma langerTau_eq_lam_sigmaOf {c' : ℝ} (hc' : 0 < c') (x : ℝ) :
    langerTau x = lambdaComb c' * sigmaOf c' x := by
  have := (lamPos hc').ne'
  unfold sigmaOf; field_simp

lemma widthT_eq {c' : ℝ} (hc' : 0 < c') (η : ℕ → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    widthT c' η k = lambdaComb c' * epsHat η k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold widthT epsHat
  rw [langerTau_chiQuantile hc' (by linarith : (1 / 4 : ℝ) ≤ (k : ℝ) + 1),
    langerTau_chiQuantile hc' (by linarith : (1 / 4 : ℝ) ≤ (k : ℝ))]
  ring

/-- Splitting of one pair: `log q'_k = Ξ_k + 2 log λ + log((σ - σ_k)² + ε̂_k²) + 2 𝒦(x, χ'_k)`. -/
lemma log_qPair_split {c' : ℝ} (hc' : 0 < c') {σ η : ℕ → ℝ} {x : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hσk : 0 ≤ σ k) (hxpos : 0 < x) (hxy : x ≠ siteX c' σ k) :
    Real.log (qPair c' σ η k x) = xiPair c' σ η x k + 2 * Real.log (lambdaComb c') +
      Real.log ((sigmaOf c' x - σ k) ^ 2 + epsHat η k ^ 2) + 2 * langerK x (siteX c' σ k) := by
  have hlp := lamPos hc'
  have hy : 0 < siteX c' σ k := lt_of_lt_of_le xiStar_pos (xiStar_le_siteX hc' hσk)
  have hD : langerTau x - langerTau (siteX c' σ k) = lambdaComb c' * (sigmaOf c' x - σ k) := by
    rw [langerTau_eq_lam_sigmaOf hc' x, langerTau_siteX hc' hσk]; ring
  have hΔ : sigmaOf c' x - σ k ≠ 0 := by
    intro h0
    have : langerTau x = langerTau (siteX c' σ k) := by
      have := hD; rw [h0, mul_zero] at this; linarith
    exact hxy (langerTau_strictMonoOn.injOn (Set.mem_Ioi.2 hxpos) (Set.mem_Ioi.2 hy) this)
  have hpos : 0 < (sigmaOf c' x - σ k) ^ 2 + epsHat η k ^ 2 := by positivity
  have e : (langerTau x - langerTau (siteX c' σ k)) ^ 2 + widthT c' η k ^ 2 =
      lambdaComb c' ^ 2 * ((sigmaOf c' x - σ k) ^ 2 + epsHat η k ^ 2) := by
    rw [hD, widthT_eq hc' η hk]; ring
  have hlog : Real.log ((langerTau x - langerTau (siteX c' σ k)) ^ 2 + widthT c' η k ^ 2) =
      2 * Real.log (lambdaComb c') + Real.log ((sigmaOf c' x - σ k) ^ 2 + epsHat η k ^ 2) := by
    rw [e, Real.log_mul (by positivity) hpos.ne', Real.log_pow]; push_cast; ring
  unfold xiPair
  rw [hlog]
  ring

/-- **Exact splitting** `E_K = -(3/2) log λ + P_K + Sm_K + ∑_{k=2}^K Ξ_k`. -/
theorem combEK_eq {Csh csep : ℝ} {c' : ℝ} (hc' : 0 < c') {σ η : ℕ → ℝ}
    (h : CombDesignHyp Csh csep σ η) {x : ℝ} (hx : x ∈ langerX (1 / 2))
    (hxk : ∀ k : ℕ, 1 ≤ k → x ≠ siteX c' σ k) (K : ℕ) (hK : 1 ≤ K) :
    combEK c' σ η x K = -(3 / 2) * Real.log (lambdaComb c') + pBracket c' σ η x K +
      smPartial c' σ x K + ∑ k ∈ Finset.Icc 2 K, xiPair c' σ η x k := by
  have hlp := lamPos hc'
  have hxpos : 0 < x := by have := xiStar_pos; linarith [hx.1]
  have hy1 : 0 < siteX c' σ 1 := lt_of_lt_of_le xiStar_pos (xiStar_le_siteX hc' (h.nonneg 1 le_rfl))
  have hΔ1 : sigmaOf c' x - σ 1 ≠ 0 := by
    intro h0
    have hD : langerTau x - langerTau (siteX c' σ 1) = lambdaComb c' * (sigmaOf c' x - σ 1) := by
      rw [langerTau_eq_lam_sigmaOf hc' x, langerTau_siteX hc' (h.nonneg 1 le_rfl)]; ring
    have : langerTau x = langerTau (siteX c' σ 1) := by
      have := hD; rw [h0, mul_zero] at this; linarith
    exact hxk 1 le_rfl (langerTau_strictMonoOn.injOn (Set.mem_Ioi.2 hxpos) (Set.mem_Ioi.2 hy1) this)
  have hf1 : realLogT x (siteX c' σ 1) = Real.log (lambdaComb c') + Real.log |sigmaOf c' x - σ 1| +
      langerK x (siteX c' σ 1) := by
    have hxy : siteX c' σ 1 ≠ x := (hxk 1 le_rfl).symm
    rw [realLogT_eq_log_add_langerK hxpos hy1 hxy, langerTau_eq_lam_sigmaOf hc' x,
      langerTau_siteX hc' (h.nonneg 1 le_rfl), ← mul_sub, abs_mul, abs_of_pos hlp,
      Real.log_mul hlp.ne' (abs_ne_zero.2 hΔ1)]
  have hsum : ∑ k ∈ Finset.Icc 2 K, Real.log (qPair c' σ η k x) =
      ∑ k ∈ Finset.Icc 2 K, (xiPair c' σ η x k + 2 * Real.log (lambdaComb c') +
        Real.log ((sigmaOf c' x - σ k) ^ 2 + epsHat η k ^ 2) + 2 * langerK x (siteX c' σ k)) :=
    Finset.sum_congr rfl fun k hk => by
      have hk2 := (Finset.mem_Icc.1 hk).1
      exact log_qPair_split hc' (by omega) (h.nonneg k (by omega)) hxpos (hxk k (by omega))
  have hcard : ((Finset.Icc 2 K).card : ℝ) = (K : ℝ) - 1 := by
    rw [Nat.card_Icc]; rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hsplit : ∑ k ∈ Finset.Icc 2 K, (xiPair c' σ η x k + 2 * Real.log (lambdaComb c') +
        Real.log ((sigmaOf c' x - σ k) ^ 2 + epsHat η k ^ 2) + 2 * langerK x (siteX c' σ k)) =
      ∑ k ∈ Finset.Icc 2 K, xiPair c' σ η x k + ((K : ℝ) - 1) * (2 * Real.log (lambdaComb c')) +
        ∑ k ∈ Finset.Icc 2 K, Real.log ((sigmaOf c' x - σ k) ^ 2 + epsHat η k ^ 2) +
        2 * ∑ k ∈ Finset.Icc 2 K, langerK x (siteX c' σ k) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul, hcard, ← Finset.mul_sum]
  have hI := integral_realLogT_eq hc' hx K
  unfold combEK pBracket smPartial
  rw [hI, hf1, hsum, hsplit]
  ring

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.combEK_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combEK_eq

end FormalResearch.ModularBootstrap.Upper.Ramped
