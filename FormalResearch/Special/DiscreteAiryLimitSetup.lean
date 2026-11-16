module

public import FormalResearch.Special.DiscreteAiryLimitFields

/-!
# Discrete-to-Airy limit, step 5: all window hypotheses for perturbed simple-turn coefficients

Part of the wiring module `DiscreteAiryLimit*`.  `dal_window_hyp` is the heart of the wiring: from the window data
`DalTurnWin` of a simple turn (`dal_turn_data`), the lattice indices of `dal_lattice_window`, the exact-coefficient defect of M7b
(`dal_exact_defect`) it verifies *every* hypothesis of the window theorems of M5/M6 for coefficient sequences
`a, c : ℤ → ℝ` that are `O(h²)`-perturbations of the exact data:

`|a_k - A(q_k - h/2)| ≤ E h²`, `|c_k - 2A(q_k)u(q_k)| ≤ E h²`  (`h = δ³`, `k` in the window),

which is the paper's `A_k = a₀(s) + O(h²)` (P3 `A:870-880`), `B_k = β₀ q_k² + O(h²)` for the Hahn/Racah chains.
The conclusion is `AiryWindowHyp X ψ a c J m N δ W c₁ B c_a κ₁ κ₂ C₀ Λ S Sg Qq w₀` for
`X = dalX ζ`, `ψ = dalPsi g ζ`, with explicit formulas for the constants in terms of the `DalTurnWin` constants (see the
proof): `κ₁ = g_min/20`, `κ₂ = 6 g_max`, `W = 25 g_max`, `c_a = A_min/2`, `B = c₂ r/2`, `S = A₀ + c₂`,
`Sg = 2 A_max L_u (A₀/c₂+1) + L_A + 3E`, `Qq = L_A + 2E`, `w₀ = (2/9)κ₁`; `C₀`, `Λ` from the exact defect constants.

Proved.  Constants are existential (those of M7b are existential).
-/

@[expose] public section

open FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **All hypotheses of M5/M6 for simple-turn coefficients.**  See the module docstring. -/
theorem dal_window_hyp {U : Set ℝ} {ζ g A u : ℝ → ℝ}
    {c0 r c1 c2 gmin gmax Amin Amax LA Lg Lu : ℝ}
    (T : DalTurnWin ζ g A u c0 r c1 c2 gmin gmax Amin Amax LA Lg Lu)
    (hU : IsOpen U) (hsub : Set.Icc (c0 - r) (c0 + r) ⊆ U) (hζ : ContDiffOn ℝ 3 ζ U)
    (hA : ContDiffOn ℝ 2 A U) (hg : ContDiffOn ℝ 2 g U)
    (hrel : ∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1)
    (heik : ∀ q ∈ U, langerCosh (ζ q * deriv ζ q ^ 2) = u q) (E A0 : ℝ) (hE : 0 ≤ E) (hA0 : 0 < A0) :
    ∃ (δ1 D W ca B κ1 κ2 C0 Λ S Sg Qq w0 : ℝ), 0 < δ1 ∧ δ1 ≤ 1 ∧ 0 < D ∧ 0 < W ∧ 0 < ca ∧ 0 ≤ B ∧ 0 < κ1 ∧
      κ1 ≤ κ2 ∧ 0 ≤ C0 ∧ 0 ≤ Λ ∧ 0 ≤ S ∧ 0 ≤ Sg ∧ 0 ≤ Qq ∧ 0 < w0 ∧
      ∀ δ q₀ : ℝ, 0 < δ → δ ≤ δ1 → ∃ J m N : ℤ, J ≤ m ∧ m ≤ N ∧
        (∀ k ∈ Finset.Icc J (N + 1), dalQ q₀ δ k ∈ Set.Icc (c0 - r) (c0 + r)) ∧
        c0 - D * δ ^ 2 ≤ dalQ q₀ δ J ∧ dalQ q₀ δ J ≤ c0 ∧ c0 ≤ dalQ q₀ δ m ∧
        dalQ q₀ δ m < c0 + δ ^ 3 ∧ c0 + r / 4 ≤ dalQ q₀ δ N ∧ dalQ q₀ δ (N + 1) ≤ c0 + r / 2 ∧
        c1 * (r / 4) / δ ^ 2 ≤ dalX ζ q₀ δ N ∧
        ∀ a c : ℤ → ℝ,
          (∀ k ∈ Finset.Icc (J + 1) (N + 1), |a k - A (dalQ q₀ δ k - δ ^ 3 / 2)| ≤ E * δ ^ 6) →
          (∀ k ∈ Finset.Icc (J + 1) N, |c k - 2 * A (dalQ q₀ δ k) * u (dalQ q₀ δ k)| ≤ E * δ ^ 6) →
          AiryWindowHyp (dalX ζ q₀ δ) (dalPsi g ζ q₀ δ) a c J m N δ W c1 B ca κ1 κ2 C0 Λ S Sg Qq w0 := by
  have hc2 : 0 < c2 := lt_of_lt_of_le T.c1_pos T.c1_le
  obtain ⟨δL, hδL, hδL1, hL⟩ := dal_lattice_window_struct T.r_pos T.c1_pos T.c1_le hA0 T.zeta0 (fun q hq => T.der q hq)
  obtain ⟨K, K', δE, hK, hK', hδE, hδE1, hEx⟩ := dal_exact_defect hU hsub hζ hA hg hrel heik
  set κ1 : ℝ := gmin / 20 with hκ1
  set κ2 : ℝ := 6 * gmax with hκ2
  set W : ℝ := 25 * gmax with hW
  set B : ℝ := c2 * (r / 2) with hB
  set Cn : ℝ := 6 / 5 * Real.exp (c2 * √(1 + B)) with hCn
  set D : ℝ := A0 / c2 + 1 with hD
  have hgmin := T.gmin_pos
  have hgmax : 0 < gmax := lt_of_lt_of_le hgmin T.gmin_le
  have hκ1p : 0 < κ1 := by rw [hκ1]; positivity
  have hκ12 : κ1 ≤ κ2 := by rw [hκ1, hκ2]; linarith [T.gmin_le]
  have hWp : 0 < W := by rw [hW]; positivity
  have hCn0 : 0 ≤ Cn := by rw [hCn]; positivity
  have hB0 : 0 ≤ B := by have := T.r_pos; rw [hB]; positivity
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  set C0 : ℝ := (K' + E * (1 + 2 * κ2 * Cn / κ1)) + (K / W + 3 * E) with hC0
  have hC00 : 0 ≤ C0 := by
    rw [hC0]
    have : 0 ≤ E * (1 + 2 * κ2 * Cn / κ1) := by
      have : 0 ≤ 2 * κ2 * Cn / κ1 := by
        have := hκ1p.le.trans hκ12
        positivity
      positivity
    have : 0 ≤ K / W + 3 * E := by positivity
    linarith
  set Λ : ℝ := (25 * Lg + 265000 * gmax * c2) / W with hΛ
  have hΛ0 : 0 ≤ Λ := by
    have := T.Lg_nonneg
    rw [hΛ]; positivity
  set S : ℝ := A0 + c2 with hS
  set Sg : ℝ := 2 * Amax * Lu * D + LA + 3 * E with hSg
  set Qq : ℝ := LA + 2 * E with hQq
  have hAmax : 0 < Amax := lt_of_lt_of_le T.Amin_pos T.Amin_le
  have hSg0 : 0 ≤ Sg := by
    have := T.Lu_nonneg; have := T.LA_nonneg
    rw [hSg]; positivity
  have hQq0 : 0 ≤ Qq := by
    have := T.LA_nonneg
    rw [hQq]; positivity
  set ca : ℝ := Amin / 2 with hca
  have hcap : 0 < ca := by have := T.Amin_pos; rw [hca]; positivity
  set w0 : ℝ := κ1 * (2 / 9) with hw0
  have hw0p : 0 < w0 := by rw [hw0]; positivity
  set δ1 : ℝ := min (min δL δE) (min (1 / (2 * c2)) (Amin / (2 * (E + 1)))) with hδ1
  have hδ1p : 0 < δ1 := by
    have := T.Amin_pos
    exact lt_min (lt_min hδL hδE) (lt_min (by positivity) (by positivity))
  refine ⟨δ1, D, W, ca, B, κ1, κ2, C0, Λ, S, Sg, Qq, w0, hδ1p,
    (min_le_left _ _).trans ((min_le_left _ _).trans hδL1), by rw [hD]; positivity, hWp, hcap, hB0, hκ1p, hκ12, hC00, hΛ0,
    (by rw [hS]; linarith), hSg0, hQq0, hw0p, ?_⟩
  intro δ q₀ hδ hδδ1
  have hδL' : δ ≤ δL := hδδ1.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδE' : δ ≤ δE := hδδ1.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδc : δ ≤ 1 / (2 * c2) := hδδ1.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδa : δ ≤ Amin / (2 * (E + 1)) := hδδ1.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδ1' : δ ≤ 1 := hδL'.trans hδL1
  have h2p : 0 < δ ^ 2 := by positivity
  have h3δ : δ ^ 3 ≤ δ ^ 2 := by
    calc δ ^ 3 = δ ^ 2 * δ := by ring
      _ ≤ δ ^ 2 * 1 := mul_le_mul_of_nonneg_left hδ1' h2p.le
      _ = δ ^ 2 := mul_one _
  have h6δ : δ ^ 6 ≤ δ := by
    have h1 : δ ^ 5 ≤ 1 := pow_le_one₀ hδ.le hδ1'
    calc δ ^ 6 = δ * δ ^ 5 := by ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left h1 hδ.le
      _ = δ := mul_one _
  have hEδ : E * δ ^ 6 ≤ Amin / 2 := by
    have h1 : δ * (2 * (E + 1)) ≤ Amin := by rwa [le_div_iff₀ (by positivity)] at hδa
    have t1 : E * δ ^ 6 ≤ E * δ := mul_le_mul_of_nonneg_left h6δ hE
    linarith
  have hc2δ : c2 * δ ≤ 1 / 2 := by
    rw [le_div_iff₀ (by positivity)] at hδc; linarith
  obtain ⟨J, m, N, L⟩ := hL δ q₀ hδ hδL'
  refine ⟨J, m, N, L.J_le, L.m_le, L.win, ?_, L.qJc, L.qm1, L.qm2, L.qN, L.qN1, L.XN, ?_⟩
  · have h4 := L.qJ
    have e1 : A0 * δ ^ 2 / c2 = A0 / c2 * δ ^ 2 := by ring
    have e2 : D * δ ^ 2 = A0 / c2 * δ ^ 2 + δ ^ 2 := by rw [hD]; ring
    linarith
  intro a c ha hc
  have hdef := hEx δ q₀ hδ hδE'
  have hK1 : 0 ≤ K' + E * (1 + 2 * κ2 * Cn / κ1) := by
    have : 0 ≤ 2 * κ2 * Cn / κ1 := by
      have := hκ1p.le.trans hκ12
      positivity
    positivity
  have hK2 : 0 ≤ K / W + 3 * E := by positivity
  refine ⟨dal_f_lat T L hδ hδ1', dal_f_cmp T L, ?_, L.span, dal_f_alow T L hδ ha hEδ,
    dal_f_hyp T L hδ hδ1' hE ha hc, dal_f_lipa T L hδ hδ1' hE ha, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have hk' := Finset.mem_Ico.1 hk
    exact (L.gap k (by rw [Finset.mem_Icc]; have := L.m_le; omega)).1
  · -- relative defect on the top window
    have key := dal_f_defT T L hδ hδ1' hc2δ hE ha hc (K' := K') (fun k hk hX =>
      (hdef k (L.win k hk)).2 hX)
    intro i hi
    have hmi : i ∈ Finset.Icc m (N + 1) := by
      have := Finset.mem_Icc.1 hi; rw [Finset.mem_Icc]; omega
    have hψ := (dal_f_cmp T L).pos hmi
    refine (key i hi).trans ?_
    have h6' : 0 ≤ δ ^ 6 * dalPsi g ζ q₀ δ i := by positivity
    have hle : K' + E * (1 + 2 * (6 * gmax) * (6 / 5 * Real.exp (c2 * √(1 + c2 * (r / 2)))) / (gmin / 20)) ≤ C0 := by
      have : C0 = (K' + E * (1 + 2 * (6 * gmax) * (6 / 5 * Real.exp (c2 * √(1 + c2 * (r / 2)))) / (gmin / 20))) +
        (K / W + 3 * E) := rfl
      linarith
    calc _ = (K' + E * (1 + 2 * (6 * gmax) * (6 / 5 * Real.exp (c2 * √(1 + c2 * (r / 2)))) / (gmin / 20))) *
          (δ ^ 6 * dalPsi g ζ q₀ δ i) := by ring
      _ ≤ C0 * (δ ^ 6 * dalPsi g ζ q₀ δ i) := mul_le_mul_of_nonneg_right hle h6'
      _ = _ := by ring
  · -- absolute defect on the oscillatory window
    have key := dal_f_defW T L hE ha hc (K := K) (fun k hk => (hdef k (L.win k hk)).1)
    intro i hi
    refine (key i hi).trans ?_
    have h6' : 0 ≤ δ ^ 6 * W := by positivity
    have hle : K / (25 * gmax) + 3 * E ≤ C0 := by
      have : C0 = (K' + E * (1 + 2 * (6 * gmax) * (6 / 5 * Real.exp (c2 * √(1 + c2 * (r / 2)))) / (gmin / 20))) +
        (K / (25 * gmax) + 3 * E) := rfl
      have h7 : 0 ≤ K' + E * (1 + 2 * (6 * gmax) * (6 / 5 * Real.exp (c2 * √(1 + c2 * (r / 2)))) / (gmin / 20)) := hK1
      linarith
    calc _ = (K / (25 * gmax) + 3 * E) * (δ ^ 6 * (25 * gmax)) := by ring
      _ ≤ C0 * (δ ^ 6 * (25 * gmax)) := mul_le_mul_of_nonneg_right hle (by positivity)
      _ = _ := by ring
  · exact (le_abs_self _).trans (dal_f_psim T L (k := m) (by
      rw [Finset.mem_Icc]; have := L.J_le; have := L.m_le; omega))
  · have := dal_f_junc T L hδ hδ1' hc2δ
    refine this.trans (le_of_eq ?_)
    rw [hΛ]; field_simp
  · exact dal_f_low T L hc2δ
  · exact fun k hk => dal_f_psim T L hk
  · exact fun k hk => L.X0 k hk

/-- info: 'FormalResearch.Special.dal_window_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dal_window_hyp

end FormalResearch.Special
