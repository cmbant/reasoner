module

public import FormalResearch.ModularBootstrap.TwoLevel.IdealApproxDesign

/-!
# Node values of the approximating windows and the Airy quadrature of `F_δ` (`virasoro_two_level.tex`, `gt:2.6`)

By the Airy quadrature `∫ W_𝔇 = Σ_ν Re nodeC 𝔇 ν`.  For the designs of an ideal datum with `K` sites:

* `intWr_decomp`: `∫ W_𝔇 = Σ_{ν ≤ K} Re nodeC ν + Σ_{ν > K} Re nodeC ν` for every design;
* `tendsto_nodeC`: the node values of a `UnifTail` family with convergent zeros, sites and widths converge
  (Tannery for infinite products, `NegativeVacuum.tendsto_tailExcept`), for every `ν ≥ 1`;
* `intWin_eq_sum`: `∫ Re F_δ = Σ_{ν ≤ K} Re nodeC p q (idealLim s K) 0 ν` (the node values of the limit data vanish for
  `ν > K`).

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel.IdealApprox

open FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Window
open FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum

lemma airyProdFactor_at_airyZero (S W : ℕ → ℝ) (n k : ℕ) :
    airyProdFactor S W k (airyZero n : ℂ) =
      ((((airyZero n - S k) ^ 2 + (W k) ^ 2) / (airyZero n - airyZero k) ^ 2 : ℝ) : ℂ) := by
  unfold airyProdFactor
  push_cast
  rfl

lemma norm_ofReal_sub_one' (x : ℝ) : ‖(x : ℂ) - 1‖ = |x - 1| := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- **Uniform `1/k²` bound on `factor - 1` at the Airy zero `a_n`** (`k ≠ n`) for a `UnifTail` family. -/
lemma exists_node_bound {S W : ℕ → ℕ → ℝ} (hU : UnifTail S W) {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j k : ℕ), 3 ≤ k → k ≠ n →
      ‖airyProdFactor (S j) (W j) k (airyZero n : ℂ) - 1‖ ≤ C / (k : ℝ) ^ 2 := by
  obtain ⟨A, hA, hb⟩ := hU
  obtain ⟨N₀, hN₀, C₁, hC₁, hbd⟩ := exists_tail_bound ⟨A, hA, hb⟩ |airyZero n|
  set Bk : ℕ → ℝ := fun k => ((|airyZero n| + |airyZero k| + A) ^ 2 + A ^ 2) / (airyZero n - airyZero k) ^ 2 + 1
    with hBk
  have hBk0 : ∀ k, 0 ≤ Bk k := fun k => by positivity
  set SB : ℝ := ∑ k ∈ Finset.Icc 3 N₀, Bk k * (k : ℝ) ^ 2 with hSB
  have hSB0 : 0 ≤ SB := Finset.sum_nonneg fun k _ => mul_nonneg (hBk0 k) (by positivity)
  refine ⟨C₁ + SB, by positivity, fun j k hk3 hkn => ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  by_cases hk : N₀ ≤ k
  · have hn' : ‖((airyZero n : ℝ) : ℂ)‖ ≤ |airyZero n| := by rw [Complex.norm_real, Real.norm_eq_abs]
    refine (hbd j (airyZero n : ℂ) hn' k hk).trans ?_
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  · have hk' : k ∈ Finset.Icc 3 N₀ := Finset.mem_Icc.mpr ⟨hk3, by omega⟩
    obtain ⟨h1, h2⟩ := hb j k (by omega)
    have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    have hp1 : (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hk1' (by norm_num)
    have hp2 : (k : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hk1' (by norm_num)
    have hS : |S j k - airyZero k| ≤ A := h1.trans (by nlinarith)
    have hWk : |W j k| ≤ A := h2.trans (by nlinarith)
    have hSk : |S j k| ≤ |airyZero k| + A := by
      have : S j k = airyZero k + (S j k - airyZero k) := by ring
      calc |S j k| = |airyZero k + (S j k - airyZero k)| := by rw [← this]
        _ ≤ |airyZero k| + |S j k - airyZero k| := abs_add_le _ _
        _ ≤ |airyZero k| + A := by linarith
    have hxS : |airyZero n - S j k| ≤ |airyZero n| + |airyZero k| + A := by
      calc |airyZero n - S j k| ≤ |airyZero n| + |S j k| := abs_sub _ _
        _ ≤ _ := by linarith
    have hden : 0 < (airyZero n - airyZero k) ^ 2 := by
      have : airyZero n ≠ airyZero k := fun h => hkn (airyZero_injective_on (by omega) hn h.symm)
      have := sub_ne_zero.mpr this
      positivity
    rw [airyProdFactor_at_airyZero, norm_ofReal_sub_one']
    set x : ℝ := ((airyZero n - S j k) ^ 2 + W j k ^ 2) / (airyZero n - airyZero k) ^ 2 with hx
    have hx0 : 0 ≤ x := by positivity
    have hx1 : x ≤ Bk k - 1 := by
      rw [hx, hBk]
      simp only [add_sub_cancel_right]
      refine div_le_div_of_nonneg_right ?_ hden.le
      have a1 : (airyZero n - S j k) ^ 2 ≤ (|airyZero n| + |airyZero k| + A) ^ 2 := by
        rw [← sq_abs (airyZero n - S j k)]
        exact pow_le_pow_left₀ (abs_nonneg _) hxS 2
      have a2 : W j k ^ 2 ≤ A ^ 2 := by
        rw [← sq_abs (W j k)]
        exact pow_le_pow_left₀ (abs_nonneg _) hWk 2
      linarith
    have habs : |x - 1| ≤ Bk k := by
      rw [abs_le]; constructor <;> linarith
    have hle : Bk k * (k : ℝ) ^ 2 ≤ SB :=
      Finset.single_le_sum (f := fun k : ℕ => Bk k * (k : ℝ) ^ 2) (fun k _ => mul_nonneg (hBk0 k) (by positivity)) hk'
    calc |x - 1| ≤ Bk k := habs
      _ = Bk k * (k : ℝ) ^ 2 / (k : ℝ) ^ 2 := by field_simp
      _ ≤ SB / (k : ℝ) ^ 2 := div_le_div_of_nonneg_right hle (by positivity)
      _ ≤ (C₁ + SB) / (k : ℝ) ^ 2 := div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- **Convergence of the node values** of a `UnifTail` family with convergent zeros, sites and widths. -/
theorem tendsto_nodeC {S W : ℕ → ℕ → ℝ} (hU : UnifTail S W) {p : ℕ → ℝ} {p' q : ℝ}
    (hp : Tendsto p atTop (𝓝 p')) (S' W' : ℕ → ℝ)
    (hS : ∀ k, 3 ≤ k → Tendsto (fun j => S j k) atTop (𝓝 (S' k)))
    (hW : ∀ k, 3 ≤ k → Tendsto (fun j => W j k) atTop (𝓝 (W' k))) {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun j => nodeC (p j) q (S j) (W j) n) atTop (𝓝 (nodeC p' q S' W' n)) := by
  obtain ⟨Cb, hCb0, hCb⟩ := exists_node_bound hU hn
  have hpc : Tendsto (fun j => ((p j : ℝ) : ℂ)) atTop (𝓝 ((p' : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hp
  have h1 : Tendsto (fun j => ((airyZero n : ℂ) - ((p j : ℝ) : ℂ)) * ((airyZero n : ℂ) - q) /
      (∏ k ∈ (Finset.Icc 1 2).erase n, ((airyZero n : ℂ) - airyZero k) ^ 2)) atTop
      (𝓝 (((airyZero n : ℂ) - p') * ((airyZero n : ℂ) - q) /
      (∏ k ∈ (Finset.Icc 1 2).erase n, ((airyZero n : ℂ) - airyZero k) ^ 2))) :=
    ((tendsto_const_nhds.sub hpc).mul tendsto_const_nhds).div_const _
  have h2 : Tendsto (fun j => if 3 ≤ n then ((airyZero n : ℂ) - S j n) ^ 2 + ((W j n : ℝ) : ℂ) ^ 2 else 1)
      atTop (𝓝 (if 3 ≤ n then ((airyZero n : ℂ) - S' n) ^ 2 + ((W' n : ℝ) : ℂ) ^ 2 else 1)) := by
    by_cases h3 : 3 ≤ n
    · simp only [h3, ↓reduceIte]
      have h1' := Complex.continuous_ofReal.continuousAt.tendsto.comp (hS n h3)
      have h2' := Complex.continuous_ofReal.continuousAt.tendsto.comp (hW n h3)
      exact ((tendsto_const_nhds.sub h1').pow 2).add (h2'.pow 2)
    · simp only [h3, ↓reduceIte]; exact tendsto_const_nhds
  have h3 := tendsto_tailExcept hn S W S' W' (fun m => Cb / ((m : ℝ) + 3) ^ 2)
    (by
      have h := ((summable_nat_add_iff 3).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))).mul_left Cb
      refine h.congr fun m => ?_
      push_cast
      rw [mul_one_div])
    (fun k hk3 _ => hS k hk3) (fun k hk3 _ => hW k hk3)
    (Eventually.of_forall fun j k hk3 hkn => by
      refine (hCb j k hk3 hkn).trans (le_of_eq ?_)
      have : ((k - 3 : ℕ) : ℝ) + 3 = k := by
        rw [Nat.cast_sub hk3]; push_cast; ring
      rw [this])
    (fun m => by positivity)
  unfold nodeC
  exact (h1.mul h2).mul h3

/-- The node values of the limit data vanish beyond `K`. -/
lemma nodeC_idealLim_eq_zero (s : ℕ → ℝ) {K : ℕ} (hK : 2 ≤ K) (p q : ℝ) {n : ℕ} (hn : K < n) :
    nodeC p q (idealLim s K) (fun _ => 0) n = 0 := by
  unfold nodeC idealLim
  simp [show 3 ≤ n by omega, show ¬(n ≤ K) by omega]

/-- **`∫ Re F_δ` as a finite sum of node values.** -/
theorem intWin_eq_sum (δ : IdealDatum) (hK : 2 ≤ δ.K) :
    ∫ u, δ.win u = ∑ m ∈ Finset.range δ.K,
      (nodeC δ.p δ.q (idealLim δ.s δ.K) (fun _ => 0) (m + 1)).re := by
  obtain ⟨C, hC, hb⟩ := δ.F_bound hK
  have h := airy_quadrature δ.differentiable_F hC (by norm_num : (-(5 / 2) : ℝ) < -1) hb
  have hfi := airy_integrable_real δ.differentiable_F hC (by norm_num : (-(5 / 2) : ℝ) < -1) hb
  have hre := Complex.hasSum_re h
  have hint : (∫ x : ℝ, δ.F (x : ℂ)).re = ∫ u, δ.win u := by
    simpa [IdealDatum.win] using (integral_re hfi).symm
  rw [hint] at hre
  have hterm : ∀ m : ℕ, (δ.F (airyZero (m + 1) : ℂ) / (deriv airyAiC (airyZero (m + 1) : ℂ)) ^ 2).re =
      (nodeC δ.p δ.q (idealLim δ.s δ.K) (fun _ => 0) (m + 1)).re := by
    intro m
    rw [F_eq_winC δ hK, winC_node _ _ _ _ (by omega)]
  have hre' : HasSum (fun m : ℕ => (nodeC δ.p δ.q (idealLim δ.s δ.K) (fun _ => 0) (m + 1)).re)
      (∫ u, δ.win u) := by
    convert hre using 1
    funext m; exact (hterm m).symm
  have hfin : HasSum (fun m : ℕ => (nodeC δ.p δ.q (idealLim δ.s δ.K) (fun _ => 0) (m + 1)).re)
      (∑ m ∈ Finset.range δ.K, (nodeC δ.p δ.q (idealLim δ.s δ.K) (fun _ => 0) (m + 1)).re) := by
    refine hasSum_sum_of_ne_finset_zero fun m hm => ?_
    rw [nodeC_idealLim_eq_zero δ.s hK _ _ (by simp only [Finset.mem_range] at hm; omega)]
    simp
  exact hre'.unique hfin

/-- The Airy quadrature of the window of a design in node form: `∫ W_2 = Σ_ν Re nodeC D ν`. -/
lemma intWr_hasSum' {n : ℕ} (d : TwoZeroDesign n) :
    HasSum (fun m : ℕ => (nodeC d.p d.q d.site d.width (m + 1)).re) (∫ u, d.Wr u) := by
  have h := Complex.hasSum_re d.W_hasSum
  have hint : (∫ x : ℝ, d.W (x : ℂ)).re = ∫ u, d.Wr u := by
    have : ∫ x : ℝ, (d.W (x : ℂ)).re = (∫ x : ℝ, d.W (x : ℂ)).re := by
      simpa using integral_re d.W_integrable
    exact this.symm
  rw [hint] at h
  convert h using 2 with m
  have := winC_node d.p d.q d.site d.width (n := m + 1) (by omega)
  rw [← this]
  rfl

/-- Node decomposition of `∫ W_2`: nodes `ν ≤ K`, then the tail. -/
lemma intWr_decomp' {n : ℕ} (d : TwoZeroDesign n) (K : ℕ) :
    ∫ u, d.Wr u = ∑ m ∈ Finset.range K, (nodeC d.p d.q d.site d.width (m + 1)).re +
      ∑' m : ℕ, (nodeC d.p d.q d.site d.width (K + 1 + m)).re := by
  have h' := intWr_hasSum' d
  have hs := h'.summable.sum_add_tsum_nat_add K
  rw [h'.tsum_eq] at hs
  rw [← hs]
  congr 1
  refine tsum_congr fun m => ?_
  have : m + K + 1 = K + 1 + m := by omega
  simp only [this]

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.IdealApprox.tendsto_nodeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_nodeC

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.IdealApprox.intWin_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms intWin_eq_sum

end FormalResearch.ModularBootstrap.TwoLevel.IdealApprox
