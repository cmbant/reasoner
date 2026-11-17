module

public import FormalResearch.Special.DiscreteAiryOscMain
public import FormalResearch.Special.DiscreteAiryPhysFull

/-!
# The abstract discrete-to-Airy machinery at defect order `δ^{6+3m}` (error `δ^{3+3m}`)

The abstract statements `dao_conclusion` (`DiscreteAiryOscMain`) and `dai_extend` (`DiscreteAiryPhysFull`) are written for the
*first-order* parametrix: row defect `K δ⁶ w` (`δ⁶ = h²`) and error `C δ³ w` (`δ³ = h`).  Here the **exponent is
tracked**: a parametrix pair `(g Ai(X), g Bi(X))` (any lattice positions `X`, in particular `X = h^{-2/3} ζ̂` with the
second-order Langer variable `ζ̂ = ζ + h² B`) with row defect `≤ K δ^{6+3m} w` shadows the exact solutions to
`C δ^{3+3m} w`.  `m = 0` is the first-order statement, `m = 1` (defect `h³ = δ⁹`, error `h² = δ⁶`) is what the second-order
Airy parametrix (not formalised here) needs.

**Where the exponent enters** (this answers the question of the hand-off).  In `DaoPair` the defect size enters only through the
product `K δ⁶`; the Casoratian `cas(φ, ψ) ≍ δ` (a base-site fact, independent of the defects) and the lattice sum
`Σ (2+|X_i|)^{-1/2} ≤ 8√(2+M)/(c₁ δ²)` do not depend on the order.  Hence the Grönwall exponent is
`Λ = 475 g_max K' δ⁶ · 8√(2+M)/(c₁ δ²) / (γ₀/2) = Cl K' δ³`, linear in the defect constant `K'`: for `K' = K δ^{3m}` it is
`O(δ^{3+3m})`.  So `DaoPair` and `dao_decomposition` are used **unchanged** with the scaled constant `K' = K δ^{3m}`
(this is possible because `DaoPair` carries `K` as a free parameter at fixed `δ`).  What does *not* scale is the Casoratian
constant of the pair (`δ/C ≤ cas`, `C = 4π/(c_a g_min² c₁)`): the old `DaoConclusion` used a single constant `C` for the
error and for the Casoratian, which hides the gain; `DaoConclusionR` separates them (error `Ce ρ`, Casoratian `δ/Cc`).

* `DaoConclusionR`, `dao_conclusion_rate`: `DaoConclusion` with error rate `ρ` (and `|μ| ≤ Cmu Ymax e^{-ξ(X_N)}/δ`, unchanged).
* `DaiFullR`, `dai_extend_rate`: the unified conclusion on `[J, N+1]` with error rate `ρ` (one more row for the site `N+1`).
* `dao_pair_rate`: from the exact-coefficient defects `K₀ δ^{6+3m} w` and coefficient closeness `E δ^{6+3m}` to the `DaoPair` with
  `K' = δ^{3m} (K₀ + E · 450 g_max (2C_n + 1))`.
* `dai_full_rate`: the composition, with `ρ = δ^{3+3m}` and explicit constants.

**Claim class: proved** (abstract lattice form; no new analysis, only exponent bookkeeping).  Not formalised: the second-order
parametrix itself (the defect hypothesis).
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- `DaoConclusion` with a general error rate `ρ` and separate Casoratian constant. -/
def DaoConclusionR (a c X g : ℤ → ℝ) (J m N : ℤ) (δ ρ Ce Cc Cmu : ℝ) : Prop :=
  ∃ f F₂ : ℤ → ℝ,
    (∀ k ∈ Icc (J + 1) N, jac a c f k = 0) ∧ f N = daoPhi g X N ∧ f (N + 1) = daoPhi g X (N + 1) ∧
    (∀ k ∈ Icc J N, |f k - daoPhi g X k| ≤ Ce * ρ * airyWt (X k)) ∧
    (∀ k ∈ Icc (J + 1) N, jac a c F₂ k = 0) ∧ F₂ m = daoPsi g X m ∧ F₂ (m + 1) = daoPsi g X (m + 1) ∧
    (∀ k ∈ Icc J N, |F₂ k - daoPsi g X k| ≤ Ce * ρ * airyBiWt (X k)) ∧
    δ / Cc ≤ cas a f F₂ N ∧ (∀ k ∈ Icc J N, cas a f F₂ k = cas a f F₂ N) ∧
    ∀ (Y : ℤ → ℝ) (Ymax : ℝ), (∀ k ∈ Icc (J + 1) N, jac a c Y k = 0) → |Y N| ≤ Ymax → |Y (N + 1)| ≤ Ymax →
      ∃ κ μ : ℝ, (∀ k ∈ Icc J (N + 1), Y k = κ * f k + μ * F₂ k) ∧
        |μ| ≤ Cmu * Ymax * Real.exp (-airyXi (X N)) / δ

/-- **The conclusion from `DaoPair` at a general rate.**  With `Λ₀ := 475 g_max K' (8√(2+M)/c₁)/(c_a g_min² c₁/(8π))`
(`K'` the defect constant of `DaoPair`, i.e. defect `K' δ⁶ w`), `Λ₀ δ³ ≤ 1/4` and `7200 g_max Λ₀ δ³ ≤ Ce ρ`:
errors `Ce ρ`, Casoratian `≥ δ/Q`, `Q = 4π/(c_a g_min² c₁)`. -/
theorem dao_conclusion_rate {X g a c : ℤ → ℝ} {J N : ℤ} {δ c1 c2 gmin gmax ca K M Aa ρ Ce : ℝ}
    (hP : DaoPair X g a c J N δ c1 c2 gmin gmax ca K M) {m : ℤ} (hm : m ∈ Icc J N)
    (hX0 : 0 ≤ X m) (hX1 : X m ≤ c2 * δ) (hc2 : c2 * δ ≤ 1 / 8) (haN : a (N + 1) ≤ Aa)
    (hsmall : 475 * gmax * K * (8 * √(2 + M) / c1) / (ca * gmin ^ 2 * c1 / (8 * Real.pi)) * δ ^ 3 ≤ 1 / 4)
    (hCe : 7200 * gmax * (475 * gmax * K * (8 * √(2 + M) / c1) / (ca * gmin ^ 2 * c1 / (8 * Real.pi)) * δ ^ 3) ≤
      Ce * ρ) :
    DaoConclusionR a c X g J m N δ ρ Ce (4 * Real.pi / (ca * gmin ^ 2 * c1))
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
  have hδ3 : 0 ≤ δ ^ 3 := by positivity
  set Q : ℝ := 4 * Real.pi / (ca * gmin ^ 2 * c1) with hQ
  have hQp : 0 < Q := by rw [hQ]; positivity
  have hγQ : δ = Q * γ0 := by rw [hQ, hγ0]; field_simp
  set ε : ℝ := Real.exp (Cl * δ ^ 3) - 1 with hε
  have hε2 : ε ≤ 2 * (Cl * δ ^ 3) := hE1
  have hε0 : 0 ≤ ε := by
    rw [hε]; have := Real.add_one_le_exp (Cl * δ ^ 3); linarith
  have hfε : 450 * gmax * ε ≤ Ce * ρ := by
    have h1 : 450 * gmax * ε ≤ 450 * gmax * (2 * (Cl * δ ^ 3)) :=
      mul_le_mul_of_nonneg_left hε2 (by positivity)
    have h2 : 450 * gmax * (2 * (Cl * δ ^ 3)) ≤ 7200 * gmax * (Cl * δ ^ 3) := by
      have : 0 ≤ gmax * (Cl * δ ^ 3) := by positivity
      nlinarith
    exact h1.trans (h2.trans (by simpa [hCl, hL] using hCe))
  have hxi : airyXi (X m) ≤ 1 := dao_airyXi_le_one (by linarith)
  have he : Real.exp (2 * airyXi (X m)) ≤ 8 :=
    (Real.exp_le_exp.2 (by linarith)).trans dao_exp_two_le
  have hFε : 450 * gmax * Real.exp (2 * airyXi (X m)) * ε ≤ Ce * ρ := by
    have h1 : Real.exp (2 * airyXi (X m)) * ε ≤ 8 * (2 * (Cl * δ ^ 3)) :=
      mul_le_mul he hε2 hε0 (by norm_num)
    have h2 : 450 * gmax * (Real.exp (2 * airyXi (X m)) * ε) ≤ 450 * gmax * (8 * (2 * (Cl * δ ^ 3))) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 450 * gmax * (8 * (2 * (Cl * δ ^ 3))) = 7200 * gmax * (Cl * δ ^ 3) := by ring
    have h4 := h3 ▸ h2
    have : 450 * gmax * Real.exp (2 * airyXi (X m)) * ε =
        450 * gmax * (Real.exp (2 * airyXi (X m)) * ε) := by ring
    rw [this]
    exact h4.trans (by simpa [hCl, hL] using hCe)
  have hρ0 : 0 ≤ Ce * ρ := (by positivity : 0 ≤ 450 * gmax * ε).trans hfε
  refine ⟨f, F₂, hf, hfN, hfN1, fun k hk => ?_, hF, hFm, hFm1, fun k hk => ?_, ?_, hcc, ?_⟩
  · exact (hfd k hk).trans (mul_le_mul_of_nonneg_right hfε (airyWt_pos _).le)
  · have hk' := mem_Icc.1 hk
    rcases le_total m k with hmk | hkm
    · exact (hFd1 k (mem_Icc.2 ⟨hmk, hk'.2⟩)).trans
        (mul_le_mul_of_nonneg_right hfε (airyBiWt_pos _).le)
    · refine (hFd2 k (mem_Icc.2 ⟨hk'.1, hkm⟩)).trans ?_
      calc _ ≤ (Ce * ρ) * airyWt (X k) := mul_le_mul_of_nonneg_right hFε (airyWt_pos _).le
        _ ≤ (Ce * ρ) * airyBiWt (X k) := mul_le_mul_of_nonneg_left (airyWt_le_airyBiWt _) hρ0
  · have : δ / Q ≤ γ0 := by
      rw [div_le_iff₀ hQp]; linarith [hγQ, mul_comm Q γ0]
    exact this.trans hγ
  · intro Y Ymax hYex hYN hYN1
    obtain ⟨κ, μ, hYeq, hμ⟩ := hY Y hYex
    exact ⟨κ, μ, hYeq, dao_mu_bound hP hJN hfN hfN1 haN hγ0p hγ hQp hγQ hμ hYN hYN1⟩

/-- **The unified conclusion at a general rate** (`DaiFull` with error rate `ρ`, separate Casoratian constant). -/
def DaiFullR (a c X g : ℤ → ℝ) (J m N : ℤ) (δ ρ Ce Cc Cmu ξ0 : ℝ) : Prop :=
  ξ0 / δ ^ 3 ≤ airyXi (X N) ∧ (∀ k ∈ Icc (J + 1) (N + 1), 0 < a k) ∧
  ∃ f F₂ : ℤ → ℝ,
    ((∀ k ∈ Icc (J + 1) N, jac a c f k = 0) ∧ f N = daoPhi g X N ∧ f (N + 1) = daoPhi g X (N + 1) ∧
      (∀ f' : ℤ → ℝ, (∀ k ∈ Icc (J + 1) N, jac a c f' k = 0) → f' N = daoPhi g X N →
        f' (N + 1) = daoPhi g X (N + 1) → ∀ k ∈ Icc J (N + 1), f' k = f k) ∧
      (∀ k ∈ Icc J (N + 1), |f k - daoPhi g X k| ≤ Ce * ρ * airyWt (X k))) ∧
    ((∀ k ∈ Icc (J + 1) N, jac a c F₂ k = 0) ∧ F₂ m = daoPsi g X m ∧ F₂ (m + 1) = daoPsi g X (m + 1) ∧
      (∀ F' : ℤ → ℝ, (∀ k ∈ Icc (J + 1) N, jac a c F' k = 0) → F' m = daoPsi g X m →
        F' (m + 1) = daoPsi g X (m + 1) → ∀ k ∈ Icc J (N + 1), F' k = F₂ k) ∧
      (∀ k ∈ Icc J (N + 1), |F₂ k - daoPsi g X k| ≤ Ce * ρ * airyBiWt (X k))) ∧
    δ / Cc ≤ cas a f F₂ N ∧ (∀ k ∈ Icc J N, cas a f F₂ k = cas a f F₂ N) ∧
    ∀ (Y : ℤ → ℝ) (Ymax : ℝ), (∀ k ∈ Icc (J + 1) N, jac a c Y k = 0) → |Y N| ≤ Ymax → |Y (N + 1)| ≤ Ymax →
      ∃ κ μ : ℝ, (∀ k ∈ Icc J (N + 1), Y k = κ * f k + μ * F₂ k) ∧
        |μ| ≤ Cmu * Ymax * Real.exp (-airyXi (X N)) / δ

/-- **Pointwise form of `DaiFullR`.**  Every exact solution `Y` with `|Y_N|, |Y_{N+1}| ≤ Y_max` is
`κ g Ai(X) + μ g Bi(X)` up to `Ce ρ (|κ| airyWt + |μ| airyBiWt)` on all of `[J, N+1]`. -/
theorem DaiFullR.pointwise {a c X g : ℤ → ℝ} {J m N : ℤ} {δ ρ Ce Cc Cmu ξ0 : ℝ}
    (h : DaiFullR a c X g J m N δ ρ Ce Cc Cmu ξ0)
    (Y : ℤ → ℝ) (Ymax : ℝ) (hY : ∀ k ∈ Icc (J + 1) N, jac a c Y k = 0) (hYN : |Y N| ≤ Ymax)
    (hYN1 : |Y (N + 1)| ≤ Ymax) :
    ∃ κ μ : ℝ, |μ| ≤ Cmu * Ymax * Real.exp (-airyXi (X N)) / δ ∧
      ∀ k ∈ Icc J (N + 1), |Y k - (κ * daoPhi g X k + μ * daoPsi g X k)| ≤
        Ce * ρ * (|κ| * airyWt (X k) + |μ| * airyBiWt (X k)) := by
  obtain ⟨-, -, f, F₂, ⟨-, -, -, -, hf⟩, ⟨-, -, -, -, hF⟩, -, -, hYd⟩ := h
  obtain ⟨κ, μ, hYeq, hμ⟩ := hYd Y Ymax hY hYN hYN1
  refine ⟨κ, μ, hμ, fun k hk => ?_⟩
  have e : Y k - (κ * daoPhi g X k + μ * daoPsi g X k) =
      κ * (f k - daoPhi g X k) + μ * (F₂ k - daoPsi g X k) := by rw [hYeq k hk]; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have h1 := mul_le_mul_of_nonneg_left (hf k hk) (abs_nonneg κ)
  have h2 := mul_le_mul_of_nonneg_left (hF k hk) (abs_nonneg μ)
  nlinarith

/-- **Extension to the site `N+1` at a general rate.**  As `dai_extend`, with the row defect at `N` bounded by
`D_r ρ airyBiWt` (`K δ⁶ ≤ D_r ρ`) and the diagonal bound `|c_N| ≤ Cd`; the error constant becomes
`Ce' = Ce + C_n (Cd Ce + A_a Ce C_n + D_r)/c_a`. -/
theorem dai_extend_rate {X g a c : ℤ → ℝ} {J m N : ℤ} {δ c1 c2 gmin gmax ca K M Aa Cd Ce Cc Cmu ξ0 ρ Dr : ℝ}
    (hP : DaoPair X g a c J N δ c1 c2 gmin gmax ca K M) (hJN : J < N) (hJm : J ≤ m) (hmN : m ≤ N)
    (hc2 : 0 ≤ c2) (hM : 0 ≤ M) (haN : a N ≤ Aa) (hcN : |c N| ≤ Cd) (hCe : 0 ≤ Ce) (hρ : 0 ≤ ρ) (hDr0 : 0 ≤ Dr)
    (hD : K * δ ^ 6 ≤ Dr * ρ) (hxi : ξ0 / δ ^ 3 ≤ airyXi (X N))
    (h : DaoConclusionR a c X g J m N δ ρ Ce Cc Cmu) :
    DaiFullR a c X g J m N δ ρ
      (Ce + 6 / 5 * Real.exp (c2 * √(1 + M)) *
        (Cd * Ce + Aa * Ce * (6 / 5 * Real.exp (c2 * √(1 + M))) + Dr) / ca) Cc Cmu ξ0 := by
  obtain ⟨f, F₂, hf, hfN, hfN1, hfd, hF, hFm, hFm1, hFd, hcas, hcc, hY⟩ := h
  have hδ := hP.δ_pos
  have hca := hP.ca_pos
  have hK := hP.K_nonneg
  set Cn : ℝ := 6 / 5 * Real.exp (c2 * √(1 + M)) with hCn
  have hCn0 : 0 < Cn := by positivity
  have hCd : 0 ≤ Cd := (abs_nonneg _).trans hcN
  have haNpos : ca ≤ a N := hP.alow N (by rw [mem_Icc]; omega)
  have hAa : 0 ≤ Aa := hca.le.trans (haNpos.trans haN)
  have hDr : 0 ≤ Dr * ρ := mul_nonneg hDr0 hρ
  set Ce' : ℝ := Ce + Cn * (Cd * Ce + Aa * Ce * Cn + Dr) / ca with hCe'
  have hC'0 : 0 ≤ Cn * (Cd * Ce + Aa * Ce * Cn + Dr) / ca := by positivity
  have hCeCe' : Ce ≤ Ce' := by rw [hCe']; linarith
  have hCe'p : 0 ≤ Ce' := hCe.trans hCeCe'
  have halow : ∀ k ∈ Icc (J + 1) (N + 1), 0 < a k := fun k hk => hca.trans_le (hP.alow k hk)
  have hane : ∀ k ∈ Icc (J + 1) (N + 1), a k ≠ 0 := fun k hk => (halow k hk).ne'
  have hNJ : N ∈ Icc (J + 1) N := by rw [mem_Icc]; omega
  have hNm1 : N - 1 ∈ Icc J N := by rw [mem_Icc]; omega
  have hNJ' : N ∈ Icc J N := by rw [mem_Icc]; omega
  have hgapN := hP.gap N hNJ'
  have hgapN1 := hP.gap (N - 1) hNm1
  rw [show N - 1 + 1 = N by ring] at hgapN1
  have hd1 : |X N - X (N + 1)| ≤ c2 * δ := by
    rw [abs_le]; constructor <;> nlinarith [hgapN.1, hgapN.2, hP.c1_pos, hδ]
  have hd2 : |X (N - 1) - X N| ≤ c2 * δ := by
    rw [abs_le]; constructor <;> nlinarith [hgapN1.1, hgapN1.2, hP.c1_pos, hδ]
  have hw1 : airyBiWt (X N) ≤ Cn * airyBiWt (X (N + 1)) :=
    dao_airyBiWt_nbr hδ hP.δ_le hc2 hP.c2δ (hP.Xabs (N + 1) (by rw [mem_Icc]; omega)) hM hd1
  have hw2 : airyBiWt (X (N - 1)) ≤ Cn * airyBiWt (X N) :=
    dao_airyBiWt_nbr hδ hP.δ_le hc2 hP.c2δ (hP.Xabs N (by rw [mem_Icc]; omega)) hM hd2
  have hstep := dap_one_step (a := a) (c := c) (y := F₂) (p := daoPsi g X) (N := N)
    (E0 := Ce * ρ * airyBiWt (X (N - 1))) (E1 := Ce * ρ * airyBiWt (X N))
    (D := K * δ ^ 6 * airyBiWt (X N)) (Cc := Cd) (Aa := Aa) (ca := ca)
    (hF N hNJ) (hP.defB N hNJ) (hFd N hNJ') (hFd (N - 1) hNm1) hcN (hca.le.trans haNpos) haN hca
    (hP.alow (N + 1) (by rw [mem_Icc]; omega))
  have hwb0 := airyBiWt_pos (X (N + 1))
  have hwbN := airyBiWt_pos (X N)
  have hCeρ : 0 ≤ Ce * ρ := by positivity
  have hFN1 : |F₂ (N + 1) - daoPsi g X (N + 1)| ≤ Ce' * ρ * airyBiWt (X (N + 1)) := by
    refine hstep.trans ?_
    rw [div_le_iff₀ hca]
    have e1 : Ce * ρ * airyBiWt (X (N - 1)) ≤ Ce * ρ * (Cn * (Cn * airyBiWt (X (N + 1)))) :=
      mul_le_mul_of_nonneg_left (hw2.trans (mul_le_mul_of_nonneg_left hw1 hCn0.le)) hCeρ
    have e2 : K * δ ^ 6 * airyBiWt (X N) ≤ Dr * ρ * (Cn * airyBiWt (X (N + 1))) :=
      mul_le_mul hD hw1 hwbN.le hDr
    have e3 : Ce * ρ * airyBiWt (X N) ≤ Ce * ρ * (Cn * airyBiWt (X (N + 1))) :=
      mul_le_mul_of_nonneg_left hw1 hCeρ
    have e4 : Cd * (Ce * ρ * airyBiWt (X N)) + Aa * (Ce * ρ * airyBiWt (X (N - 1))) +
        K * δ ^ 6 * airyBiWt (X N) ≤
        Cd * (Ce * ρ * (Cn * airyBiWt (X (N + 1)))) +
          Aa * (Ce * ρ * (Cn * (Cn * airyBiWt (X (N + 1))))) + Dr * ρ * (Cn * airyBiWt (X (N + 1))) := by
      have := mul_le_mul_of_nonneg_left e3 hCd
      have := mul_le_mul_of_nonneg_left e1 hAa
      linarith
    refine e4.trans ?_
    rw [hCe']
    have e5 : (Ce + Cn * (Cd * Ce + Aa * Ce * Cn + Dr) / ca) * ρ * airyBiWt (X (N + 1)) * ca =
        Ce * ρ * airyBiWt (X (N + 1)) * ca + Cn * (Cd * Ce + Aa * Ce * Cn + Dr) * ρ * airyBiWt (X (N + 1)) := by
      field_simp
    rw [e5]
    have h0 : 0 ≤ Ce * ρ * airyBiWt (X (N + 1)) * ca := by positivity
    have eA : Cd * (Ce * ρ * (Cn * airyBiWt (X (N + 1)))) +
        Aa * (Ce * ρ * (Cn * (Cn * airyBiWt (X (N + 1))))) + Dr * ρ * (Cn * airyBiWt (X (N + 1))) =
        Cn * (Cd * Ce + Aa * Ce * Cn + Dr) * ρ * airyBiWt (X (N + 1)) := by ring
    rw [eA]
    linarith
  have hCeρ' : Ce * ρ ≤ Ce' * ρ := mul_le_mul_of_nonneg_right hCeCe' hρ
  refine ⟨hxi, halow, f, F₂, ⟨hf, hfN, hfN1, ?_, ?_⟩, ⟨hF, hFm, hFm1, ?_, ?_⟩, hcas, hcc, ?_⟩
  · intro f' hf' hN hN1 k hk
    have := eq_of_final_values a c f' f (fun _ => 0) (J + 1) N (by omega)
      (fun k hk => hf' k hk) (fun k hk => hf k hk) (fun k hk => hane k hk) (by rw [hN, hfN]) (by rw [hN1, hfN1])
    exact this k (by rw [mem_Icc] at hk ⊢; omega)
  · intro k hk
    rw [mem_Icc] at hk
    rcases eq_or_lt_of_le hk.2 with h1 | h1
    · rw [h1, hfN1, sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg hCe'p hρ) (airyWt_pos _).le
    · exact (hfd k (by rw [mem_Icc]; omega)).trans (mul_le_mul_of_nonneg_right hCeρ' (airyWt_pos _).le)
  · intro F' hF' h0 h1 k hk
    have hsub : ∀ k ∈ Icc (J + 1) N, jac a c (fun i => F' i - F₂ i) k = 0 := by
      intro k hk
      have := hF' k hk; have := hF k hk
      simp only [jac] at *; linarith
    have := eq_zero_of_two_values a c (fun i => F' i - F₂ i) (J + 1) N m hsub hane
      (by rw [mem_Icc]; omega) (by simp [h0, hFm]) (by simp [h1, hFm1])
    have h2 := this k (by rw [mem_Icc] at hk ⊢; omega)
    simpa [sub_eq_zero] using h2
  · intro k hk
    rw [mem_Icc] at hk
    rcases eq_or_lt_of_le hk.2 with h1 | h1
    · rw [h1]; exact hFN1
    · exact (hFd k (by rw [mem_Icc]; omega)).trans (mul_le_mul_of_nonneg_right hCeρ' (airyBiWt_pos _).le)
  · intro Y Ymax hYex hYN hYN1
    exact hY Y Ymax hYex hYN hYN1

/-- **`DaoPair` at defect order `δ^{6+3m}`.**  Exact-coefficient defects `K₀ δ^{6+3m} w` of `g Ai`, `g Bi` and coefficient
closeness `E δ^{6+3m}` give the `DaoPair` of `DiscreteAiryOscPair` with `K' = δ^{3m} (K₀ + E · 450 g_max (2C_n+1))`
(`dao_pair_of_defects`, scaled; the structure carries `K` as a free parameter at fixed `δ`). -/
theorem dao_pair_rate {X g a c a0 c0 : ℤ → ℝ} {J N : ℤ} {δ c1 c2 gmin gmax ca K0 E M : ℝ} (m : ℕ)
    (hJN : J ≤ N) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc1 : 0 < c1) (hc2δ : c2 * δ ≤ 1) (hM : 0 ≤ M) (hc2 : 0 ≤ c2)
    (hgap : ∀ k ∈ Icc J N, c1 * δ ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ c2 * δ)
    (hXabs : ∀ k ∈ Icc J (N + 1), |X k| ≤ M / δ ^ 2)
    (hgmin : 0 < gmin) (hgb : ∀ k ∈ Icc J (N + 1), gmin ≤ g k ∧ g k ≤ gmax)
    (hca : 0 < ca) (halow : ∀ k ∈ Icc (J + 1) (N + 1), ca ≤ a k) (hK0 : 0 ≤ K0) (hE : 0 ≤ E)
    (ha : ∀ k ∈ Icc (J + 1) (N + 1), |a k - a0 k| ≤ E * δ ^ (6 + 3 * m))
    (hc : ∀ k ∈ Icc (J + 1) N, |c k - c0 k| ≤ E * δ ^ (6 + 3 * m))
    (hdA : ∀ k ∈ Icc (J + 1) N, |jac a0 c0 (daoPhi g X) k| ≤ K0 * δ ^ (6 + 3 * m) * airyWt (X k))
    (hdB : ∀ k ∈ Icc (J + 1) N, |jac a0 c0 (daoPsi g X) k| ≤ K0 * δ ^ (6 + 3 * m) * airyBiWt (X k)) :
    DaoPair X g a c J N δ c1 c2 gmin gmax ca
      (δ ^ (3 * m) * (K0 + E * (450 * gmax * (2 * (6 / 5 * Real.exp (c2 * √(1 + M))) + 1)))) M := by
  have e : ∀ x : ℝ, x * δ ^ (6 + 3 * m) = (x * δ ^ (3 * m)) * δ ^ 6 := fun x => by
    rw [pow_add]; ring
  have hp : 0 ≤ δ ^ (3 * m) := by positivity
  have := dao_pair_of_defects (X := X) (g := g) (a := a) (c := c) (a0 := a0) (c0 := c0) (K0 := K0 * δ ^ (3 * m))
    (E := E * δ ^ (3 * m)) hJN hδ hδ1 hc1 hc2δ hM hc2 hgap hXabs hgmin hgb hca halow (by positivity)
    (by positivity) (fun k hk => by rw [← e]; exact ha k hk) (fun k hk => by rw [← e]; exact hc k hk)
    (fun k hk => (hdA k hk).trans_eq (by rw [pow_add]; ring))
    (fun k hk => (hdB k hk).trans_eq (by rw [pow_add]; ring))
  convert this using 2
  ring

/-- **The abstract second-order (general `n`) conclusion.**  Parametrix pair `(g Ai(X), g Bi(X))` on a lattice `X`
(gaps `∈ [c₁δ, c₂δ]`, `|X| ≤ M δ⁻²`, base site `m₀` with `0 ≤ X_{m₀} ≤ c₂δ ≤ 1/8`) with exact-coefficient row defects
`K₀ δ^{6+3n} w`, coefficients within `E δ^{6+3n}` of the exact ones, `a ≥ c_a`, `a_N, a_{N+1} ≤ A_a`, `|c_N| ≤ C_d`, and
the smallness `Λ₁ δ^{3+3n} ≤ 1/4` with `Λ₁ = 475 g_max K₁ (8√(2+M)/c₁)/(c_a g_min² c₁/(8π))`,
`K₁ = K₀ + E · 450 g_max (2C_n + 1)`, `C_n = (6/5) e^{c₂ √(1+M)}`.  Then `DaiFullR` holds with
error rate `ρ = δ^{3+3n}`, `Ce = 7200 g_max Λ₁ + C_n (C_d Ce₀ + A_a Ce₀ C_n + K₁)/c_a` (`Ce₀ = 7200 g_max Λ₁`),
Casoratian constant `Q = 4π/(c_a g_min² c₁)`, `Cmu = 50 g_max A_a Q`.  `n = 0` is the first-order statement
(`dai_extend` ∘ `dao_conclusion` ∘ `dao_pair_of_defects`), `n = 1` the second-order one. -/
theorem dai_full_rate {X g a c a0 c0 : ℤ → ℝ} {J m0 N : ℤ}
    {δ c1 c2 gmin gmax ca K0 E M Aa Cd ξ0 : ℝ} (n : ℕ)
    (hJN : J < N) (hJm : J ≤ m0) (hmN : m0 ≤ N) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc1 : 0 < c1) (hc2δ : c2 * δ ≤ 1)
    (hM : 0 ≤ M) (hc2 : 0 ≤ c2)
    (hgap : ∀ k ∈ Icc J N, c1 * δ ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ c2 * δ)
    (hXabs : ∀ k ∈ Icc J (N + 1), |X k| ≤ M / δ ^ 2)
    (hgmin : 0 < gmin) (hgb : ∀ k ∈ Icc J (N + 1), gmin ≤ g k ∧ g k ≤ gmax)
    (hca : 0 < ca) (halow : ∀ k ∈ Icc (J + 1) (N + 1), ca ≤ a k) (hK0 : 0 ≤ K0) (hE : 0 ≤ E)
    (ha : ∀ k ∈ Icc (J + 1) (N + 1), |a k - a0 k| ≤ E * δ ^ (6 + 3 * n))
    (hc : ∀ k ∈ Icc (J + 1) N, |c k - c0 k| ≤ E * δ ^ (6 + 3 * n))
    (hdA : ∀ k ∈ Icc (J + 1) N, |jac a0 c0 (daoPhi g X) k| ≤ K0 * δ ^ (6 + 3 * n) * airyWt (X k))
    (hdB : ∀ k ∈ Icc (J + 1) N, |jac a0 c0 (daoPsi g X) k| ≤ K0 * δ ^ (6 + 3 * n) * airyBiWt (X k))
    (hX0 : 0 ≤ X m0) (hX1 : X m0 ≤ c2 * δ) (hc8 : c2 * δ ≤ 1 / 8)
    (haN : a N ≤ Aa) (haN1 : a (N + 1) ≤ Aa) (hcN : |c N| ≤ Cd) (hxi : ξ0 / δ ^ 3 ≤ airyXi (X N))
    (hsmall : 475 * gmax * (K0 + E * (450 * gmax * (2 * (6 / 5 * Real.exp (c2 * √(1 + M))) + 1))) *
        (8 * √(2 + M) / c1) / (ca * gmin ^ 2 * c1 / (8 * Real.pi)) * δ ^ (3 + 3 * n) ≤ 1 / 4) :
    DaiFullR a c X g J m0 N δ (δ ^ (3 + 3 * n))
      (7200 * gmax * (475 * gmax * (K0 + E * (450 * gmax * (2 * (6 / 5 * Real.exp (c2 * √(1 + M))) + 1))) *
          (8 * √(2 + M) / c1) / (ca * gmin ^ 2 * c1 / (8 * Real.pi))) +
        6 / 5 * Real.exp (c2 * √(1 + M)) *
          (Cd * (7200 * gmax * (475 * gmax * (K0 + E * (450 * gmax * (2 * (6 / 5 * Real.exp (c2 * √(1 + M))) + 1))) *
              (8 * √(2 + M) / c1) / (ca * gmin ^ 2 * c1 / (8 * Real.pi)))) +
            Aa * (7200 * gmax * (475 * gmax * (K0 + E * (450 * gmax * (2 * (6 / 5 * Real.exp (c2 * √(1 + M))) + 1))) *
              (8 * √(2 + M) / c1) / (ca * gmin ^ 2 * c1 / (8 * Real.pi)))) * (6 / 5 * Real.exp (c2 * √(1 + M))) +
            (K0 + E * (450 * gmax * (2 * (6 / 5 * Real.exp (c2 * √(1 + M))) + 1)))) / ca)
      (4 * Real.pi / (ca * gmin ^ 2 * c1)) (50 * gmax * Aa * (4 * Real.pi / (ca * gmin ^ 2 * c1))) ξ0 := by
  set Cn : ℝ := 6 / 5 * Real.exp (c2 * √(1 + M)) with hCn
  set K1 : ℝ := K0 + E * (450 * gmax * (2 * Cn + 1)) with hK1
  have hP := dao_pair_rate (X := X) (g := g) (a := a) (c := c) (a0 := a0) (c0 := c0) n (hJN.le) hδ hδ1 hc1 hc2δ hM hc2
    hgap hXabs hgmin hgb hca halow hK0 hE ha hc hdA hdB
  rw [← hCn, ← hK1] at hP
  have hgmax : 0 < gmax := by
    have := hgb J (by rw [mem_Icc]; omega)
    linarith [this.1, this.2]
  have hγ1p : 0 < ca * gmin ^ 2 * c1 / (8 * Real.pi) := by positivity
  set Λ1 : ℝ := 475 * gmax * K1 * (8 * √(2 + M) / c1) / (ca * gmin ^ 2 * c1 / (8 * Real.pi)) with hΛ1
  have hK1nn : 0 ≤ K1 := by
    have : 0 ≤ E * (450 * gmax * (2 * Cn + 1)) := by positivity
    rw [hK1]; linarith
  have hΛ1nn : 0 ≤ Λ1 := by rw [hΛ1]; positivity
  have hpow : δ ^ (3 + 3 * n) = δ ^ 3 * δ ^ (3 * n) := by rw [pow_add]
  have hlhs : 475 * gmax * (δ ^ (3 * n) * K1) * (8 * √(2 + M) / c1) /
        (ca * gmin ^ 2 * c1 / (8 * Real.pi)) * δ ^ 3 = Λ1 * δ ^ (3 + 3 * n) := by
    rw [hΛ1, hpow]; ring
  have hconc := dao_conclusion_rate (ρ := δ ^ (3 + 3 * n)) (Ce := 7200 * gmax * Λ1) (Aa := Aa) hP
    (m := m0) (mem_Icc.2 ⟨hJm, hmN⟩) hX0 hX1 hc8 haN1 (by rw [hlhs]; exact hsmall)
    (by rw [hlhs]; ring_nf; exact le_rfl)
  have hD : δ ^ (3 * n) * K1 * δ ^ 6 ≤ K1 * (δ ^ (3 + 3 * n)) := by
    have h1 : δ ^ (3 * n + 6) ≤ δ ^ (3 * n + 3) := pow_le_pow_of_le_one hδ.le hδ1 (by omega)
    have e1 : δ ^ (3 * n) * K1 * δ ^ 6 = K1 * δ ^ (3 * n + 6) := by rw [pow_add]; ring
    have e2 : K1 * δ ^ (3 + 3 * n) = K1 * δ ^ (3 * n + 3) := by rw [add_comm 3 (3 * n)]
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left h1 hK1nn
  exact dai_extend_rate (Dr := K1) hP hJN hJm hmN hc2 hM haN hcN (by positivity) (by positivity) hK1nn hD hxi hconc

/-- info: 'FormalResearch.Special.dai_full_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dai_full_rate

/-- info: 'FormalResearch.Special.dao_pair_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dao_pair_rate

/-- info: 'FormalResearch.Special.dao_conclusion_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dao_conclusion_rate

/-- info: 'FormalResearch.Special.dai_extend_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dai_extend_rate

/-- info: 'FormalResearch.Special.DaiFullR.pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.DaiFullR.pointwise

end FormalResearch.Special
