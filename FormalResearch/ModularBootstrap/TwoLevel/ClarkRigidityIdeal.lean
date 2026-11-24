module

public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidityNodes

/-!
# Ideal two-simple-zero windows and their Clark node values (`virasoro_two_level.tex`, `gt:2.5`, `gt:2.6`)

An *ideal datum* `δ = (p, q, K, s)` is the limit `ε_k → 0`, `N → ∞` of the modified-pair data of a two-simple-zero
design `𝔇` (`TwoZeroDesign`): zeros `p, q`, double zeros at the sites `s_k` for `3 ≤ k ≤ K`, and double zeros at the
Airy zeros `a_k` for `k > K`.  Its window is the entire function `F_δ` with

`F_δ(u) ∏_{k=1}^K (u - a_k)² = Ai(u)² (u - p)(u - q) ∏_{k=3}^K (u - s_k)²`.

* `IdealDatum.F`, `F_spec`, `F_bound` (`F_δ ∈ 𝒢_{-5/2}` for `K ≥ 2`);
* `IdealDatum.win δ x = Re F_δ(x)`: the real window, continuous and integrable;
* `IdealDatum.tau α δ i`: the Clark node value `F_δ(z_{i+1})/K_{i+1} = N_δ(z_{i+1})/(D(z_{i+1})² (cot²α - z_{i+1}))`
  (`win_cNode_mul_cWeight`) and the Clark summation `∫ F_δ = Σ_i τ_i(δ)` (`hasSum_tau`).

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.SignUncertainty

/-- An ideal datum: zeros `p`, `q`, double zeros at `s k` for `3 ≤ k ≤ K`, ideal (Airy) double zeros beyond `K`. -/
structure IdealDatum where
  p : ℝ
  q : ℝ
  K : ℕ
  s : ℕ → ℝ

namespace IdealDatum

variable (δ : IdealDatum)

/-- `N_δ(u) = (u - p)(u - q) ∏_{k=3}^K (u - s_k)²`. -/
noncomputable def N (u : ℂ) : ℂ :=
  (u - (δ.p : ℂ)) * (u - (δ.q : ℂ)) * ∏ k ∈ Finset.Icc 3 δ.K, (u - (δ.s k : ℂ)) ^ 2

/-- The real form of `N_δ`. -/
noncomputable def Nr (x : ℝ) : ℝ :=
  (x - δ.p) * (x - δ.q) * ∏ k ∈ Finset.Icc 3 δ.K, (x - δ.s k) ^ 2

lemma N_ofReal (x : ℝ) : δ.N (x : ℂ) = ((δ.Nr x : ℝ) : ℂ) := by
  unfold N Nr; push_cast; rfl

lemma differentiable_N : Differentiable ℂ δ.N := by
  unfold N; fun_prop

theorem exists_F : ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
    ∀ u, airyAiC u ^ 2 * δ.N u = H u * windowD δ.K u ^ 2 := by
  refine FormalResearch.EntireDiv.entire_exists_div_sq
    (φ := fun u => airyAiC u ^ 2 * δ.N u) (ψ := windowD δ.K)
    (differentiable_airyAiC.pow 2 |>.mul δ.differentiable_N)
    (differentiable_windowD δ.K) ?_
  intro z hz
  unfold windowD at hz
  obtain ⟨k, hk, hzk⟩ := Finset.prod_eq_zero_iff.mp hz
  have hzk' : z = (airyZero k : ℂ) := sub_eq_zero.mp hzk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hA : airyAiC z = 0 := by rw [hzk']; exact airyAiC_airyZero k
  refine ⟨by simp [hA], ?_, ?_⟩
  · have hd : HasDerivAt (fun u => airyAiC u ^ 2 * δ.N u)
        (2 * airyAiC z * deriv airyAiC z * δ.N z + airyAiC z ^ 2 * deriv δ.N z) z := by
      have h1 := (differentiable_airyAiC.differentiableAt (x := z)).hasDerivAt.pow 2
      have h2 := (δ.differentiable_N.differentiableAt (x := z)).hasDerivAt
      convert h1.mul h2 using 1
      simp
    rw [hd.deriv, hA]; simp
  · have hfun : windowD δ.K = fun u => (u - (airyZero k : ℂ)) *
        ∏ j ∈ (Finset.Icc 1 δ.K).erase k, (u - (airyZero j : ℂ)) := by
      funext u; unfold windowD; rw [Finset.mul_prod_erase _ (fun j => u - (airyZero j : ℂ)) hk]
    have hd : HasDerivAt (windowD δ.K) (∏ j ∈ (Finset.Icc 1 δ.K).erase k, (z - (airyZero j : ℂ))) z := by
      rw [hfun]
      have h1 : HasDerivAt (fun u : ℂ => u - (airyZero k : ℂ)) 1 z := (hasDerivAt_id z).sub_const _
      have h2 : Differentiable ℂ (fun u : ℂ => ∏ j ∈ (Finset.Icc 1 δ.K).erase k, (u - (airyZero j : ℂ))) := by
        fun_prop
      have := h1.mul (h2.differentiableAt (x := z)).hasDerivAt
      convert this using 1
      rw [hzk']; simp
    rw [hd.deriv]
    refine Finset.prod_ne_zero_iff.mpr (fun j hj => ?_)
    obtain ⟨hjk, hj'⟩ := Finset.mem_erase.mp hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj').1
    rw [hzk']
    intro h0
    have : airyZero k = airyZero j := Complex.ofReal_injective (sub_eq_zero.mp h0)
    exact hjk (airyZero_inj hj1 hk1 this.symm)

/-- The ideal window `F_δ` (an entire solution of the cleared-denominator identity). -/
noncomputable def F : ℂ → ℂ := Classical.choose δ.exists_F

lemma differentiable_F : Differentiable ℂ δ.F := (Classical.choose_spec δ.exists_F).1

/-- `F_δ(u) ∏_{k=1}^K (u - a_k)² = Ai(u)² N_δ(u)`. -/
lemma F_spec (u : ℂ) : airyAiC u ^ 2 * δ.N u = δ.F u * windowD δ.K u ^ 2 :=
  (Classical.choose_spec δ.exists_F).2 u

lemma norm_N_le (hK : 2 ≤ δ.K) : ∃ C : ℝ, 0 ≤ C ∧ ∀ u, ‖δ.N u‖ ≤ C * (1 + ‖u‖) ^ (2 * δ.K - 2) := by
  set P : ℝ := ∏ k ∈ Finset.Icc 3 δ.K, (1 + |δ.s k|) with hP
  have hP0 : 0 ≤ P := Finset.prod_nonneg (fun k _ => by positivity)
  refine ⟨(1 + |δ.p|) * (1 + |δ.q|) * P ^ 2, by positivity, fun u => ?_⟩
  have h1 : ‖u - (δ.p : ℂ)‖ ≤ (1 + |δ.p|) * (1 + ‖u‖) := by
    have := norm_prod_sub_le {1} (fun _ => δ.p) u
    simpa using this
  have h2 : ‖u - (δ.q : ℂ)‖ ≤ (1 + |δ.q|) * (1 + ‖u‖) := by
    have := norm_prod_sub_le {0} (fun _ => δ.q) u
    simpa using this
  have h3 := norm_prod_sub_le (Finset.Icc 3 δ.K) (fun k => δ.s k) u
  have hcard : (Finset.Icc 3 δ.K).card = δ.K - 2 := by simp
  rw [hcard] at h3
  unfold N
  rw [norm_mul, norm_mul, Finset.prod_pow, norm_pow]
  have hx : 0 ≤ 1 + ‖u‖ := by positivity
  have h3' : ‖∏ k ∈ Finset.Icc 3 δ.K, (u - (δ.s k : ℂ))‖ ^ 2 ≤ (P * (1 + ‖u‖) ^ (δ.K - 2)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h3 2
  have hexp : (1 + ‖u‖) ^ (2 * δ.K - 2) = (1 + ‖u‖) * (1 + ‖u‖) * ((1 + ‖u‖) ^ (δ.K - 2)) ^ 2 := by
    rw [← pow_mul, ← pow_two, ← pow_add]; congr 1; omega
  rw [hexp]
  calc ‖u - (δ.p : ℂ)‖ * ‖u - (δ.q : ℂ)‖ * ‖∏ k ∈ Finset.Icc 3 δ.K, (u - (δ.s k : ℂ))‖ ^ 2
      ≤ ((1 + |δ.p|) * (1 + ‖u‖)) * ((1 + |δ.q|) * (1 + ‖u‖)) * (P * (1 + ‖u‖) ^ (δ.K - 2)) ^ 2 := by
        gcongr
    _ = _ := by ring

/-- **`F_δ ∈ 𝒢_{-5/2}`**: `‖F_δ(u)‖ ≤ C (1 + ‖u‖)^{-5/2} e(u)`. -/
theorem F_bound (hK : 2 ≤ δ.K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, ‖δ.F u‖ ≤ C * (1 + ‖u‖) ^ (-(5 / 2) : ℝ) * airyEnv u := by
  obtain ⟨CN, hCN, hN⟩ := δ.norm_N_le hK
  have hφ : ∀ u : ℂ, ‖airyAiC u ^ 2 * δ.N u‖ ≤
      (9 * CN) * (1 + ‖u‖) ^ ((-(1 / 2) : ℝ) + (2 * δ.K - 2 : ℕ)) * airyEnv u := by
    intro u
    have hx : 0 < 1 + ‖u‖ := by positivity
    rw [norm_mul, norm_pow]
    have hA := airyAiC_norm_sq_le u
    have hpow : (1 + ‖u‖) ^ ((-(1 / 2) : ℝ) + (2 * δ.K - 2 : ℕ)) =
        (1 + ‖u‖) ^ (-(1 / 2) : ℝ) * (1 + ‖u‖) ^ (2 * δ.K - 2) := by
      rw [Real.rpow_add hx, Real.rpow_natCast]
    rw [hpow]
    calc ‖airyAiC u‖ ^ 2 * ‖δ.N u‖
        ≤ (9 * (1 + ‖u‖) ^ (-(1 / 2) : ℝ) * airyEnv u) * (CN * (1 + ‖u‖) ^ (2 * δ.K - 2)) :=
          mul_le_mul hA (hN u) (norm_nonneg _) (by have := airyEnv_pos u; positivity)
      _ = _ := by ring
  obtain ⟨C', hC', hb⟩ := div_bound δ.differentiable_F (s := Finset.Icc 1 δ.K)
    (t := fun k => airyZero k) (by positivity) hφ (fun u => by
      have := δ.F_spec u
      unfold windowD at this
      exact this)
  refine ⟨C', hC', fun u => ?_⟩
  have hcard : ((Finset.Icc 1 δ.K).card : ℝ) = δ.K := by simp
  have hexp : (-(1 / 2) : ℝ) + ((2 * δ.K - 2 : ℕ) : ℝ) - 2 * ((Finset.Icc 1 δ.K).card : ℝ) = -(5 / 2) := by
    rw [hcard]
    have : ((2 * δ.K - 2 : ℕ) : ℝ) = 2 * δ.K - 2 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this]; ring
  have := hb u
  rwa [hexp] at this

/-- The real ideal window `Re F_δ`. -/
noncomputable def win (x : ℝ) : ℝ := (δ.F (x : ℂ)).re

lemma continuous_win : Continuous δ.win :=
  Complex.continuous_re.comp (δ.differentiable_F.continuous.comp Complex.continuous_ofReal)

/-- Real form of the defining identity: `win(x) D(x)² = Ai(x)² N_δ(x)`. -/
lemma win_spec (x : ℝ) : δ.win x * windowDr δ.K x ^ 2 = airyAi x ^ 2 * δ.Nr x := by
  have h := δ.F_spec (x : ℂ)
  rw [windowD_ofReal, δ.N_ofReal, airyAiC_ofReal] at h
  have h2 : δ.F (x : ℂ) * (((windowDr δ.K x ^ 2 : ℝ)) : ℂ) = ((airyAi x ^ 2 * δ.Nr x : ℝ) : ℂ) := by
    push_cast at h ⊢
    exact h.symm
  have := congrArg Complex.re h2
  rwa [Complex.re_mul_ofReal] at this

lemma integrable_win (hK : 2 ≤ δ.K) : Integrable δ.win := by
  obtain ⟨C, hC, hb⟩ := δ.F_bound hK
  have := airy_integrable_real δ.differentiable_F hC (by norm_num : (-(5 / 2) : ℝ) < -1) hb
  exact this.re

/-- The Clark node value `τ_i(δ) = F_δ(z_{i+1})/K_{i+1} = N_δ(z)/(D(z)² (cot²α - z))`, `z = z_{i+1}`. -/
noncomputable def tau (α : ℝ) (i : ℕ) : ℝ :=
  δ.Nr (cNode α i) / (windowDr δ.K (cNode α i) ^ 2 * (cotC α ^ 2 - cNode α i))

lemma clarkKernel_eq (α : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    clarkKernel α n = airyAi (clarkNode α n) ^ 2 * (cotC α ^ 2 - clarkNode α n) := by
  unfold clarkKernel
  rw [clarkNode_airyAi' hn]; ring

lemma cotC_sq_sub_pos (α : ℝ) {n : ℕ} (hn : 1 ≤ n) : 0 < cotC α ^ 2 - clarkNode α n := by
  have h := clarkKernel_pos α n
  rw [clarkKernel_eq α hn] at h
  have hA2 : 0 < airyAi (clarkNode α n) ^ 2 := by
    have := clarkNode_airyAi_ne (α := α) hn
    positivity
  exact (mul_pos_iff_of_pos_left hA2).mp h

lemma win_cNode_mul_cWeight (α : ℝ) (i : ℕ) : δ.win (cNode α i) * cWeight α i = δ.tau α i := by
  have hn : 1 ≤ i + 1 := by omega
  have hD := windowDr_node_ne α δ.K hn
  have hA := clarkNode_airyAi_ne (α := α) hn
  have hc : 0 < cotC α ^ 2 - cNode α i := cotC_sq_sub_pos α hn
  have hspec := δ.win_spec (cNode α i)
  unfold tau cWeight
  rw [show cNode α i = clarkNode α (i + 1) from rfl] at hspec hc ⊢
  rw [clarkKernel_eq α hn]
  have hA2 : airyAi (clarkNode α (i + 1)) ^ 2 ≠ 0 := pow_ne_zero 2 hA
  have hD2 : windowDr δ.K (clarkNode α (i + 1)) ^ 2 ≠ 0 := pow_ne_zero 2 hD
  field_simp
  linear_combination hspec

/-- **Clark summation of the ideal window**: `∫ F_δ = Σ_i τ_i(δ)`. -/
theorem hasSum_tau {α : ℝ} (hα : Real.sin α ≠ 0) (hK : 2 ≤ δ.K) :
    HasSum (δ.tau α) (∫ x, δ.win x) := by
  obtain ⟨C, hC, hb⟩ := δ.F_bound hK
  have h := clark_node_hasSum hα δ.differentiable_F hC (by norm_num : (-(5 / 2) : ℝ) < -1) hb
  have hre := Complex.hasSum_re h
  have hfi := airy_integrable_real δ.differentiable_F hC (by norm_num : (-(5 / 2) : ℝ) < -1) hb
  have hint : (∫ x : ℝ, δ.F (x : ℂ)).re = ∫ x : ℝ, δ.win x := by
    simpa [win] using (integral_re hfi).symm
  rw [hint] at hre
  convert hre using 1
  funext i
  have hn : 1 ≤ i + 1 := by omega
  have hcast : (deriv airyAiC (clarkNode α (i + 1) : ℂ)) ^ 2 -
      (clarkNode α (i + 1) : ℂ) * airyAiC (clarkNode α (i + 1) : ℂ) ^ 2 =
      ((clarkKernel α (i + 1) : ℝ) : ℂ) := by
    unfold clarkKernel
    rw [deriv_airyAiC_ofReal, airyAiC_ofReal]; push_cast; ring
  rw [hcast]
  have hK0 := clarkKernel_pos α (i + 1)
  rw [Complex.div_ofReal_re, ← win_cNode_mul_cWeight]
  unfold cWeight win cNode
  ring

end IdealDatum

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.IdealDatum.hasSum_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IdealDatum.hasSum_tau

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.IdealDatum.F_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IdealDatum.F_bound

end FormalResearch.ModularBootstrap.TwoLevel
