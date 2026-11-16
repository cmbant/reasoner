module

public import FormalResearch.Special.DiscreteAiryOscDecomp
public import FormalResearch.Special.DiscreteAiryOscAssemble
public import FormalResearch.Special.AiryRecessiveSums

/-!
# The non-recessive Airy pair and the oscillatory side: conclusion with explicit `δ³` constants

`DaoConclusion a c X g J m N δ C Cmu`: there are exact solutions `f` (recessive normalisation `f = g Ai(X)` at `N, N+1`) and `F₂`
(`F₂ = g Bi(X)` at `m, m+1`) of the three-term recurrence on the rows `J+1..N` with

* `|f - g Ai(X)| ≤ C δ³ airyWt(X)` and `|F₂ - g Bi(X)| ≤ C δ³ airyBiWt(X)` on **all** of `[J, N]` (the bulk of the oscillatory side included:
  `airyWt, airyBiWt ≍ (2+|X|)^{-1/4}` where `X ≤ 0`);
* the Casoratian `cas(f, F₂)` constant on `[J, N]` and `≥ δ/C`;
* every exact solution `Y` equals `κ f + μ F₂` on `[J, N+1]`, with `|μ| ≤ Cmu Ymax e^{-ξ(X_N)}/δ` if `|Y_N|, |Y_{N+1}| ≤ Ymax`.

`dao_conclusion` proves it from the hypotheses `DaoPair` of `DiscreteAiryOscPair` (lattice gaps, amplitude bounds,
`a ≥ c_a`, the `Ai` and `Bi` defects `K δ⁶ w`) and the size condition `C_λ δ³ ≤ 1/4`,
with `C_λ = 475 g_max K · 8√(2+M)/c₁ / (c_a g_min² c₁/(8π))`.

**Claim class: proved** (abstract lattice form; the smooth-data corollary is `dao_turn_conclusion`).
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- The conclusion packaged (see the module docstring). -/
def DaoConclusion (a c X g : ℤ → ℝ) (J m N : ℤ) (δ C Cmu : ℝ) : Prop :=
  ∃ f F₂ : ℤ → ℝ,
    (∀ k ∈ Icc (J + 1) N, jac a c f k = 0) ∧ f N = daoPhi g X N ∧ f (N + 1) = daoPhi g X (N + 1) ∧
    (∀ k ∈ Icc J N, |f k - daoPhi g X k| ≤ C * δ ^ 3 * airyWt (X k)) ∧
    (∀ k ∈ Icc (J + 1) N, jac a c F₂ k = 0) ∧ F₂ m = daoPsi g X m ∧ F₂ (m + 1) = daoPsi g X (m + 1) ∧
    (∀ k ∈ Icc J N, |F₂ k - daoPsi g X k| ≤ C * δ ^ 3 * airyBiWt (X k)) ∧
    δ / C ≤ cas a f F₂ N ∧ (∀ k ∈ Icc J N, cas a f F₂ k = cas a f F₂ N) ∧
    ∀ (Y : ℤ → ℝ) (Ymax : ℝ), (∀ k ∈ Icc (J + 1) N, jac a c Y k = 0) → |Y N| ≤ Ymax → |Y (N + 1)| ≤ Ymax →
      ∃ κ μ : ℝ, (∀ k ∈ Icc J (N + 1), Y k = κ * f k + μ * F₂ k) ∧
        |μ| ≤ Cmu * Ymax * Real.exp (-airyXi (X N)) / δ

/-- `e^Λ - 1 ≤ 2Λ ≤ 1/2` for `0 ≤ Λ ≤ 1/4`. -/
lemma dao_exp_small {Λ : ℝ} (h0 : 0 ≤ Λ) (h1 : Λ ≤ 1 / 4) :
    Real.exp Λ - 1 ≤ 2 * Λ ∧ Real.exp Λ - 1 ≤ 1 / 2 := by
  have h := Real.exp_bound_div_one_sub_of_interval h0 (by linarith)
  have h2 : 1 / (1 - Λ) - 1 ≤ 2 * Λ := by
    have : 0 < 1 - Λ := by linarith
    rw [div_sub_one this.ne', div_le_iff₀ this]
    nlinarith
  constructor <;> linarith

lemma dao_airyWt_le_exp (X : ℝ) : airyWt X ≤ Real.exp (-airyXi X) := by
  unfold airyWt
  have h1 : (2 + |X|) ^ (-(1 / 4) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg X]) (by norm_num)
  calc _ ≤ 1 * Real.exp (-airyXi X) := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = _ := by ring

lemma dao_airyXi_le_one {X : ℝ} (h : X ≤ 1) : airyXi X ≤ 1 := by
  unfold airyXi
  have h0 : max X 0 ≤ 1 := max_le h (by norm_num)
  have h1 : (max X 0) ^ (3 / 2 : ℝ) ≤ 1 :=
    Real.rpow_le_one (le_max_right _ _) h0 (by norm_num)
  linarith


/-- The bound on the non-recessive coefficient `μ`: `μ cas(f,F₂)_N = cas(f,Y)_N`, `f = φ` at `N, N+1`. -/
lemma dao_mu_bound {X g a c f F₂ Y : ℤ → ℝ} {J N : ℤ} {δ c1 c2 gmin gmax ca K M Aa γ0 Q Ymax μ : ℝ}
    (hP : DaoPair X g a c J N δ c1 c2 gmin gmax ca K M) (hJN : J ≤ N)
    (hfN : f N = daoPhi g X N) (hfN1 : f (N + 1) = daoPhi g X (N + 1)) (haN : a (N + 1) ≤ Aa)
    (hγ0p : 0 < γ0) (hγ : γ0 ≤ cas a f F₂ N) (hQp : 0 < Q) (hγQ : δ = Q * γ0)
    (hμ : μ * cas a f F₂ N = cas a f Y N) (hYN : |Y N| ≤ Ymax) (hYN1 : |Y (N + 1)| ≤ Ymax) :
    |μ| ≤ 50 * gmax * Aa * Q * Ymax * Real.exp (-airyXi (X N)) / δ := by
  have hgmax := hP.gmax_pos hJN
  have hca := hP.ca_pos
  have hδ := hP.δ_pos
  have hc1 := hP.c1_pos
  have hNm : N ∈ Icc J (N + 1) := mem_Icc.2 ⟨hJN, by omega⟩
  have hN1m : N + 1 ∈ Icc J (N + 1) := mem_Icc.2 ⟨by omega, le_rfl⟩
  have hphi0 := hP.phi_abs hNm
  have hphi1 := hP.phi_abs hN1m
  have hXN : X N ≤ X (N + 1) := by
    have := (hP.gap N (mem_Icc.2 ⟨hJN, le_rfl⟩)).1; nlinarith [hc1, hδ]
  set E0 : ℝ := Real.exp (-airyXi (X N)) with hE0
  have hE0p : 0 < E0 := Real.exp_pos _
  have w0 : airyWt (X N) ≤ E0 := dao_airyWt_le_exp _
  have w1 : airyWt (X (N + 1)) ≤ E0 :=
    (dao_airyWt_le_exp _).trans (Real.exp_le_exp.2 (by linarith [airyXi_mono hXN]))
  have haN0 : 0 < a (N + 1) := hca.trans_le (hP.alow (N + 1) (mem_Icc.2 ⟨by omega, le_rfl⟩))
  have hYm : 0 ≤ Ymax := (abs_nonneg _).trans hYN
  have hcas : |cas a f Y N| ≤ 50 * gmax * Aa * E0 * Ymax := by
    unfold cas
    rw [hfN, hfN1, abs_mul, abs_of_pos haN0]
    have p0 : |daoPhi g X N| ≤ 25 * gmax * E0 := hphi0.trans (mul_le_mul_of_nonneg_left w0 (by positivity))
    have p1 : |daoPhi g X (N + 1)| ≤ 25 * gmax * E0 := hphi1.trans (mul_le_mul_of_nonneg_left w1 (by positivity))
    have t : |daoPhi g X N * Y (N + 1) - daoPhi g X (N + 1) * Y N| ≤ 50 * gmax * E0 * Ymax := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul]
      have := mul_le_mul p0 hYN1 (abs_nonneg _) (by positivity)
      have := mul_le_mul p1 hYN (abs_nonneg _) (by positivity)
      nlinarith
    calc a (N + 1) * |daoPhi g X N * Y (N + 1) - daoPhi g X (N + 1) * Y N|
        ≤ Aa * (50 * gmax * E0 * Ymax) := mul_le_mul haN t (abs_nonneg _) (haN0.le.trans haN)
      _ = _ := by ring
  have hμγ : |μ| * γ0 ≤ 50 * gmax * Aa * E0 * Ymax := by
    calc |μ| * γ0 ≤ |μ| * cas a f F₂ N := mul_le_mul_of_nonneg_left hγ (abs_nonneg _)
      _ = |μ * cas a f F₂ N| := by
          rw [abs_mul, abs_of_nonneg (hγ0p.le.trans hγ)]
      _ = |cas a f Y N| := by rw [hμ]
      _ ≤ _ := hcas
  rw [le_div_iff₀ hδ]
  calc |μ| * δ = Q * (|μ| * γ0) := by rw [hγQ]; ring
    _ ≤ Q * (50 * gmax * Aa * E0 * Ymax) := mul_le_mul_of_nonneg_left hμγ hQp.le
    _ = _ := by ring

lemma dao_arith_f {gmax Cl t ε C : ℝ} (hg : 0 ≤ gmax) (hCl : 0 ≤ Cl) (ht : 0 ≤ t)
    (hε : ε ≤ 2 * (Cl * t)) (hC : 7200 * gmax * Cl ≤ C) : 450 * gmax * ε ≤ C * t := by
  have h1 : 450 * gmax * ε ≤ 450 * gmax * (2 * (Cl * t)) := mul_le_mul_of_nonneg_left hε (by positivity)
  have h2 : 900 * gmax * Cl * t ≤ C * t := mul_le_mul_of_nonneg_right
    (by nlinarith [mul_nonneg hg hCl]) ht
  nlinarith

lemma dao_arith_F {gmax Cl t ε C e : ℝ} (hg : 0 ≤ gmax) (ht : 0 ≤ t)
    (hε : ε ≤ 2 * (Cl * t)) (hε0 : 0 ≤ ε) (hC : 7200 * gmax * Cl ≤ C) (he : e ≤ 8) :
    450 * gmax * e * ε ≤ C * t := by
  have h1 : e * ε ≤ 8 * (2 * (Cl * t)) := mul_le_mul he hε hε0 (by norm_num)
  have h2 : 450 * gmax * (e * ε) ≤ 450 * gmax * (8 * (2 * (Cl * t))) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : 7200 * gmax * Cl * t ≤ C * t := mul_le_mul_of_nonneg_right hC ht
  nlinarith

lemma dao_exp_two_le : Real.exp 2 ≤ 8 := by
  have h := Real.exp_one_lt_d9
  have h1 := Real.exp_pos 1
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [this]; nlinarith

/-- **The conclusion from `DaoPair`** (abstract lattice form).  `Cλ δ³ ≤ 1/4` is the smallness condition. -/
theorem dao_conclusion {X g a c : ℤ → ℝ} {J N : ℤ} {δ c1 c2 gmin gmax ca K M Aa : ℝ}
    (hP : DaoPair X g a c J N δ c1 c2 gmin gmax ca K M) {m : ℤ} (hm : m ∈ Icc J N)
    (hX0 : 0 ≤ X m) (hX1 : X m ≤ c2 * δ) (hc2 : c2 * δ ≤ 1 / 8) (haN : a (N + 1) ≤ Aa)
    (hsmall : 475 * gmax * K * (8 * √(2 + M) / c1) / (ca * gmin ^ 2 * c1 / (8 * Real.pi)) * δ ^ 3 ≤ 1 / 4) :
    DaoConclusion a c X g J m N δ
      (7200 * gmax * (475 * gmax * K * (8 * √(2 + M) / c1) / (ca * gmin ^ 2 * c1 / (8 * Real.pi))) +
        4 * Real.pi / (ca * gmin ^ 2 * c1))
      (50 * gmax * Aa * (4 * Real.pi / (ca * gmin ^ 2 * c1))) := by
  have hm2 := mem_Icc.1 hm
  have hJN : J ≤ N := hm2.1.trans hm2.2
  have hgmax := hP.gmax_pos hJN
  have hK := hP.K_nonneg
  have hδ := hP.δ_pos
  have hc1 := hP.c1_pos
  have hca := hP.ca_pos
  have hgmin := hP.gmin_pos
  have hπ := Real.pi_pos
  have hM2 : 0 ≤ √(2 + M) := Real.sqrt_nonneg _
  set L : ℝ := 475 * gmax * K * (8 * √(2 + M) / c1) with hL
  set γ1 : ℝ := ca * gmin ^ 2 * c1 / (8 * Real.pi) with hγ1
  have hγ1p : 0 < γ1 := by rw [hγ1]; positivity
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  set Cl : ℝ := L / γ1 with hCl
  have hCl0 : 0 ≤ Cl := by positivity
  set γ0 : ℝ := ca * gmin ^ 2 * (c1 * δ) / (4 * Real.pi) with hγ0
  have hγ0p : 0 < γ0 := by rw [hγ0]; positivity
  have hγ0h : γ0 / 2 = γ1 * δ := by rw [hγ0, hγ1]; field_simp; ring
  have hlhs : 475 * gmax * K * δ ^ 6 * (8 * √(2 + M) / (c1 * δ ^ 2)) = L * δ ^ 4 := by
    rw [hL]; field_simp
  have hΛeq : 475 * gmax * K * δ ^ 6 * (8 * √(2 + M) / (c1 * δ ^ 2)) / (γ0 / 2) = Cl * δ ^ 3 := by
    rw [hlhs, hγ0h, hCl]; field_simp
  have hΛ0 : 0 ≤ Cl * δ ^ 3 := by positivity
  have hsm : 475 * gmax * K * δ ^ 6 * (8 * √(2 + M) / (c1 * δ ^ 2)) ≤ γ0 / 2 := by
    have h1 : Cl * δ ^ 3 ≤ 1 := by linarith
    have h2 : L * δ ^ 4 ≤ γ1 * δ := by
      have : L / γ1 * δ ^ 3 ≤ 1 := h1
      rw [div_mul_eq_mul_div, div_le_one hγ1p] at this
      nlinarith [pow_pos hδ 3]
    rw [hlhs, hγ0h]; exact h2
  obtain ⟨hE1, hE2⟩ := dao_exp_small hΛ0 (by linarith)
  obtain ⟨f, F₂, hf, hfN, hfN1, hfd, hF, hFm, hFm1, hFd1, hFd2, hγ, hcc, hY⟩ :=
    dao_decomposition hP hm hX0 hX1 hc2 hγ0 hsm hΛeq.le (by linarith)
  set C : ℝ := 7200 * gmax * Cl + 4 * Real.pi / (ca * gmin ^ 2 * c1) with hC
  have hCp : 0 < C := by rw [hC]; positivity
  have hδ3 : 0 ≤ δ ^ 3 := by positivity
  set Q : ℝ := 4 * Real.pi / (ca * gmin ^ 2 * c1) with hQ
  have hQp : 0 < Q := by rw [hQ]; positivity
  have hγQ : δ = Q * γ0 := by rw [hQ, hγ0]; field_simp
  set ε : ℝ := Real.exp (Cl * δ ^ 3) - 1 with hε
  have hε2 : ε ≤ 2 * (Cl * δ ^ 3) := hE1
  have hε0 : 0 ≤ ε := by
    rw [hε]; have := Real.add_one_le_exp (Cl * δ ^ 3); linarith
  have hCl' : 7200 * gmax * Cl ≤ C := by rw [hC]; linarith [hQp]
  have hfε : 450 * gmax * ε ≤ C * δ ^ 3 := dao_arith_f hgmax.le hCl0 hδ3 hε2 hCl'
  have hxi : airyXi (X m) ≤ 1 := dao_airyXi_le_one (by linarith)
  have he : Real.exp (2 * airyXi (X m)) ≤ 8 :=
    (Real.exp_le_exp.2 (by linarith)).trans dao_exp_two_le
  have hFε : 450 * gmax * Real.exp (2 * airyXi (X m)) * ε ≤ C * δ ^ 3 :=
    dao_arith_F hgmax.le hδ3 hε2 hε0 hCl' he
  refine ⟨f, F₂, hf, hfN, hfN1, fun k hk => ?_, hF, hFm, hFm1, fun k hk => ?_, ?_, hcc, ?_⟩
  · refine (hfd k hk).trans ?_
    exact mul_le_mul_of_nonneg_right hfε (airyWt_pos _).le |>.trans_eq (by ring)
  · have hk' := mem_Icc.1 hk
    rcases le_total m k with hmk | hkm
    · refine (hFd1 k (mem_Icc.2 ⟨hmk, hk'.2⟩)).trans ?_
      exact mul_le_mul_of_nonneg_right hfε (airyBiWt_pos _).le |>.trans_eq (by ring)
    · refine (hFd2 k (mem_Icc.2 ⟨hk'.1, hkm⟩)).trans ?_
      calc _ ≤ (C * δ ^ 3) * airyWt (X k) := mul_le_mul_of_nonneg_right hFε (airyWt_pos _).le
        _ ≤ (C * δ ^ 3) * airyBiWt (X k) := mul_le_mul_of_nonneg_left (airyWt_le_airyBiWt _) (by positivity)
        _ = _ := by ring
  · have : δ / C ≤ γ0 := by
      rw [div_le_iff₀ hCp]
      have : γ0 * Q ≤ γ0 * C := mul_le_mul_of_nonneg_left (by rw [hC]; linarith [mul_nonneg hgmax.le hCl0]) hγ0p.le
      nlinarith
    exact this.trans hγ
  · intro Y Ymax hYex hYN hYN1
    obtain ⟨κ, μ, hYeq, hμ⟩ := hY Y hYex
    exact ⟨κ, μ, hYeq, dao_mu_bound hP hJN hfN hfN1 haN hγ0p hγ hQp hγQ hμ hYN hYN1⟩

/-- **Pointwise form.**  Every exact solution `Y` is `κ g Ai(X) + μ g Bi(X)` up to `C δ³ (|κ| airyWt + |μ| airyBiWt)` on all of `[J, N]`,
with `|μ| ≤ Cmu Ymax e^{-ξ(X_N)}/δ`. -/
theorem DaoConclusion.pointwise {a c X g : ℤ → ℝ} {J m N : ℤ} {δ C Cmu : ℝ}
    (h : DaoConclusion a c X g J m N δ C Cmu) (Y : ℤ → ℝ) (Ymax : ℝ)
    (hY : ∀ k ∈ Icc (J + 1) N, jac a c Y k = 0) (hYN : |Y N| ≤ Ymax) (hYN1 : |Y (N + 1)| ≤ Ymax) :
    ∃ κ μ : ℝ, |μ| ≤ Cmu * Ymax * Real.exp (-airyXi (X N)) / δ ∧
      ∀ k ∈ Icc J N, |Y k - (κ * daoPhi g X k + μ * daoPsi g X k)| ≤
        C * δ ^ 3 * (|κ| * airyWt (X k) + |μ| * airyBiWt (X k)) := by
  obtain ⟨f, F₂, -, -, -, hf, -, -, -, hF, -, -, hYd⟩ := h
  obtain ⟨κ, μ, hYeq, hμ⟩ := hYd Y Ymax hY hYN hYN1
  refine ⟨κ, μ, hμ, fun k hk => ?_⟩
  have hk1 : k ∈ Icc J (N + 1) := by rw [mem_Icc] at hk ⊢; omega
  have e : Y k - (κ * daoPhi g X k + μ * daoPsi g X k) =
      κ * (f k - daoPhi g X k) + μ * (F₂ k - daoPsi g X k) := by rw [hYeq k hk1]; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have h1 := mul_le_mul_of_nonneg_left (hf k hk) (abs_nonneg κ)
  have h2 := mul_le_mul_of_nonneg_left (hF k hk) (abs_nonneg μ)
  nlinarith

/-- info: 'FormalResearch.Special.dao_conclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dao_conclusion

/-- info: 'FormalResearch.Special.DaoConclusion.pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.DaoConclusion.pointwise

end FormalResearch.Special
