module

public import FormalResearch.Special.DiscreteAiryOscMarch
public import FormalResearch.Special.DiscreteJacobiExtras
public import FormalResearch.Special.DiscreteJacobiCalculusComparison

/-!
# The exact pair `(f, F₂)` shadowing `(g Ai, g Bi)` and the two-sided decomposition of every solution

Abstract lattice version (hypotheses: `DaoPair`, a base site `m` with `0 ≤ X_m ≤ c₂ δ ≤ 1/8`, the smallness
`475 g_max K δ⁶ · 8√(2+M)/(c₁δ²) ≤ γ₀/2` for `γ₀ = c_a g_min² c₁ δ/(4π)`).  Notation `φ = g Ai(X)`, `ψ = g Bi(X)`.

`dao_decomposition` produces two **exact** solutions of the rows `Icc (J+1) N`:

* the *recessive* solution `f` (`f = φ` at the last two sites): `|f_k - φ_k| ≤ 450 g_max (e^Λ - 1) airyWt(X_k)` for **all**
  `k ∈ [J, N]` (relative `O(δ³)` on `X ≥ 0`, absolute `O(δ³)·(2+|X|)^{-1/4}` on the oscillatory side, no `e^{A₀²}`);
* the *non-recessive* solution `F₂` (`F₂ = ψ` at `m, m+1`): `|F₂_k - ψ_k| ≤ 450 g_max (e^Λ - 1) airyBiWt(X_k)` for
  `m ≤ k ≤ N`, and `≤ 450 g_max e^{2ξ(X_m)} (e^Λ - 1) airyWt(X_k)` for `J ≤ k ≤ m`;
* the Casoratian `cas(f, F₂) ≡ γ_* ≥ γ₀` (constant on `Icc J N`, `γ_* = α^f_m cas(φ, ψ)_m`, `α^f_m ≥ 1/2`);
* every exact solution `Y` of the rows is `Y = κ f + μ F₂` on `Icc J (N+1)`, with `μ · γ_* = cas(f, Y)_N`.

Proof.  `f` from `exists_final_solution_hom` (backward recursion); the backward Grönwall march `dao_down` from the bond `N`
(where the Cramer coefficients are exactly `(1, 0)`) controls `f - φ`; `F₂` from `dao_exists_two_site` (two final-value
solutions and Cramer), its coefficients at `m` are exactly `(0, 1)`, and `dao_up`/`dao_down` from `m` control `F₂ - ψ`; the
Casoratian of the exact pair is `cas(f, ψ)_m = α^f_m cas(φ, ψ)_m`.

**Claim class: proved** (explicit constants).  `μ` is the coefficient of the non-recessive solution; for a solution
bounded at the last two sites it is exponentially small (`dao_mu_bound`).
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **Exact solution with prescribed values at two adjacent sites** (`a ≠ 0` on the rows). -/
theorem dao_exists_two_site (a c w : ℤ → ℝ) (J N m : ℤ) (hJm : J ≤ m) (hmN : m ≤ N)
    (ha : ∀ k ∈ Icc (J + 1) (N + 1), a k ≠ 0) :
    ∃ y : ℤ → ℝ, (∀ k ∈ Icc (J + 1) N, jac a c y k = 0) ∧ y m = w m ∧ y (m + 1) = w (m + 1) := by
  have ha' : ∀ k ∈ Icc (J + 1) N, a k ≠ 0 := fun k hk => ha k (by rw [mem_Icc] at hk ⊢; omega)
  obtain ⟨f1, h1, h1N, h1N1⟩ := exists_final_solution_hom a c (J + 1) N 1 0 ha'
  obtain ⟨f2, h2, h2N, h2N1⟩ := exists_final_solution_hom a c (J + 1) N 0 1 ha'
  have hcN : cas a f1 f2 N = a (N + 1) := by unfold cas; rw [h1N, h1N1, h2N, h2N1]; ring
  have haN : a (N + 1) ≠ 0 := ha (N + 1) (by rw [mem_Icc]; omega)
  have hcm : cas a f1 f2 m ≠ 0 := by
    have := cas_eq_of_sol a c f1 f2 (J + 1) N h1 h2 m (by rw [mem_Icc]; omega)
    rw [this, hcN]; exact haN
  refine ⟨fun k => vocA a w f1 f2 m * f1 k + vocB a w f1 f2 m * f2 k, fun k hk => ?_, ?_, ?_⟩
  · have e1 := h1 k hk
    have e2 := h2 k hk
    simp only [jac] at e1 e2 ⊢
    linear_combination (vocA a w f1 f2 m) * e1 + (vocB a w f1 f2 m) * e2
  · exact ((voc_repr a w f1 f2 m hcm).1).symm
  · exact ((voc_repr a w f1 f2 m hcm).2).symm

/-- **Two-sided decomposition** (abstract lattice form).  See the module docstring. -/
theorem dao_decomposition {X g a c : ℤ → ℝ} {J N : ℤ} {δ c1 c2 gmin gmax ca K M : ℝ}
    (hP : DaoPair X g a c J N δ c1 c2 gmin gmax ca K M) {m : ℤ} {γ0 Λ : ℝ}
    (hm : m ∈ Icc J N) (hX0 : 0 ≤ X m) (hX1 : X m ≤ c2 * δ) (hc2 : c2 * δ ≤ 1 / 8)
    (hγ0 : γ0 = ca * gmin ^ 2 * (c1 * δ) / (4 * Real.pi))
    (hsm : 475 * gmax * K * δ ^ 6 * (8 * √(2 + M) / (c1 * δ ^ 2)) ≤ γ0 / 2)
    (hΛ : 475 * gmax * K * δ ^ 6 * (8 * √(2 + M) / (c1 * δ ^ 2)) / (γ0 / 2) ≤ Λ)
    (hΛ1 : Real.exp Λ - 1 ≤ 1 / 2) :
    ∃ f F₂ : ℤ → ℝ,
      (∀ k ∈ Icc (J + 1) N, jac a c f k = 0) ∧ f N = daoPhi g X N ∧ f (N + 1) = daoPhi g X (N + 1) ∧
      (∀ k ∈ Icc J N, |f k - daoPhi g X k| ≤ 450 * gmax * (Real.exp Λ - 1) * airyWt (X k)) ∧
      (∀ k ∈ Icc (J + 1) N, jac a c F₂ k = 0) ∧ F₂ m = daoPsi g X m ∧ F₂ (m + 1) = daoPsi g X (m + 1) ∧
      (∀ k ∈ Icc m N, |F₂ k - daoPsi g X k| ≤ 450 * gmax * (Real.exp Λ - 1) * airyBiWt (X k)) ∧
      (∀ k ∈ Icc J m, |F₂ k - daoPsi g X k| ≤
        450 * gmax * Real.exp (2 * airyXi (X m)) * (Real.exp Λ - 1) * airyWt (X k)) ∧
      γ0 ≤ cas a f F₂ N ∧ (∀ k ∈ Icc J N, cas a f F₂ k = cas a f F₂ N) ∧
      ∀ Y : ℤ → ℝ, (∀ k ∈ Icc (J + 1) N, jac a c Y k = 0) →
        ∃ κ μ : ℝ, (∀ k ∈ Icc J (N + 1), Y k = κ * f k + μ * F₂ k) ∧ μ * cas a f F₂ N = cas a f Y N := by
  have hm2 := mem_Icc.1 hm
  have hJN : J ≤ N := hm2.1.trans hm2.2
  have hgmax := hP.gmax_pos hJN
  have hK := hP.K_nonneg
  have hδ := hP.δ_pos
  have hc1 := hP.c1_pos
  have hπ := Real.pi_pos
  have hγ0pos : 0 < γ0 := by rw [hγ0]; have := hP.ca_pos; have := hP.gmin_pos; positivity
  have hEnn : 0 ≤ 475 * gmax * K * δ ^ 6 * (8 * √(2 + M) / (c1 * δ ^ 2)) := by positivity
  have hE0 : 0 ≤ 475 * gmax * K * δ ^ 6 * (8 * √(2 + M) / (c1 * δ ^ 2)) / (γ0 / 2) := by positivity
  have hΛ0 : 0 ≤ Λ := hE0.trans hΛ
  have haN : ∀ k ∈ Icc (J + 1) (N + 1), a k ≠ 0 := fun k hk => (hP.ca_pos.trans_le (hP.alow k hk)).ne'
  have haN' : ∀ k ∈ Icc (J + 1) N, a k ≠ 0 := fun k hk => haN k (by rw [mem_Icc] at hk ⊢; omega)
  set φ := daoPhi g X with hφ
  set ψ := daoPsi g X with hψ
  -- base Casoratian at `m`
  have hDm : 2 * γ0 ≤ cas a φ ψ m := by
    have h := dao_cas_base (X := X) (g := g) (a := a) (m := m) hc1 hδ hc2 hP.gmin_pos hP.ca_pos hX0 hX1
      (hP.gap m hm).1 (hP.gap m hm).2 (hP.gb m (by rw [mem_Icc]; omega)).1
      (hP.gb (m + 1) (by rw [mem_Icc]; omega)).1 (hP.alow (m + 1) (by rw [mem_Icc]; omega))
    have e : ca * gmin ^ 2 * (c1 * δ) / (2 * Real.pi) = 2 * γ0 := by rw [hγ0]; field_simp; ring
    rw [e] at h; exact h
  have hDm' : 2 * γ0 ≤ |cas a φ ψ m| := hDm.trans (le_abs_self _)
  -- Casoratian at `N`
  have hvarN := hP.cas_vary hm (show N ∈ Icc J N by rw [mem_Icc]; omega)
  have hDN : 2 * (γ0 / 2) ≤ |cas a φ ψ N| := by
    have h2 := abs_sub_abs_le_abs_sub (cas a φ ψ m) (cas a φ ψ N)
    rw [abs_sub_comm] at h2
    have : |cas a φ ψ m| = cas a φ ψ m := abs_of_nonneg (by linarith)
    linarith
  -- `f`
  obtain ⟨f, hf, hfN, hfN1⟩ := exists_final_solution_hom a c (J + 1) N (φ N) (φ (N + 1)) haN'
  -- the coefficients of `f` at `N`
  have hfα : vocA a f φ ψ N = 1 := by
    have hDne : cas a φ ψ N ≠ 0 := by
      intro h; rw [h, abs_zero] at hDN; linarith
    unfold vocA
    rw [div_eq_one_iff_eq hDne]
    unfold cas; rw [hfN, hfN1]
  have hfβ : vocB a f φ ψ N = 0 := by
    have h0 : cas a φ f N = 0 := by unfold cas; rw [hfN, hfN1]; ring
    unfold vocB; rw [h0, zero_div]
  have hdf := dao_down hP (Y := f) (b := N) (γ := γ0 / 2) (Λ := Λ) (show N ∈ Icc J N by rw [mem_Icc]; omega)
    (by positivity) hDN hsm hΛ hf
  -- `F₂`
  obtain ⟨F, hF, hFm, hFm1⟩ := dao_exists_two_site a c ψ J N m hm2.1 hm2.2 haN
  have hDne : cas a φ ψ m ≠ 0 := by intro h; rw [h] at hDm; linarith
  have hFα : vocA a F φ ψ m = 0 := by
    have h0 : cas a F ψ m = 0 := by unfold cas; rw [hFm, hFm1]; ring
    unfold vocA; rw [h0, zero_div]
  have hFβ : vocB a F φ ψ m = 1 := by
    unfold vocB
    rw [div_eq_one_iff_eq hDne]
    unfold cas; rw [hFm, hFm1]
  have hmup : γ0 ≤ 2 * γ0 := by linarith
  have hsm1 : 475 * gmax * K * δ ^ 6 * (8 * √(2 + M) / (c1 * δ ^ 2)) ≤ γ0 := by linarith
  have hΛm : 475 * gmax * K * δ ^ 6 * (8 * √(2 + M) / (c1 * δ ^ 2)) / γ0 ≤ Λ := by
    refine le_trans ?_ hΛ
    exact div_le_div_of_nonneg_left hEnn (by positivity) (by linarith)
  have hFup := dao_up hP (Y := F) (b := m) (γ := γ0) (Λ := Λ) hm hγ0pos hDm' hsm1 hΛm
    (fun k hk => hF k (by rw [mem_Icc] at hk ⊢; omega))
  have hFdn := dao_down hP (Y := F) (b := m) (γ := γ0) (Λ := Λ) hm hγ0pos hDm' hsm1 hΛm
    (fun k hk => hF k (by rw [mem_Icc] at hk ⊢; omega))
  -- `α^f_m ≥ 1/2` and the exact Casoratian
  have hαm : 1 / 2 ≤ vocA a f φ ψ m := by
    have h := (hdf m hm).1
    rw [hfα, hfβ] at h
    simp only [sub_zero, abs_zero, mul_zero, add_zero, abs_one, one_mul] at h
    have hnn : 0 ≤ Real.exp (2 * airyXi (X m)) * |vocB a f φ ψ m| := by positivity
    have h1 : |vocA a f φ ψ m - 1| ≤ 1 / 2 := by linarith
    have := (abs_le.1 h1).1
    linarith
  have hcasm : cas a f F m = vocA a f φ ψ m * cas a φ ψ m := by
    unfold vocA
    rw [div_mul_cancel₀ _ hDne]
    unfold cas; rw [hFm, hFm1]
  have hcasN : ∀ k ∈ Icc J N, cas a f F k = cas a f F N := by
    intro k hk
    have := cas_eq_of_sol a c f F (J + 1) N hf hF k (by rw [mem_Icc] at hk ⊢; omega)
    exact this
  have hγstar : γ0 ≤ cas a f F N := by
    rw [← hcasN m hm, hcasm]
    nlinarith
  refine ⟨f, F, hf, hfN, hfN1, ?_, hF, hFm, hFm1, ?_, ?_, hγstar, hcasN, ?_⟩
  · intro k hk
    have := (hdf k (by rw [mem_Icc] at hk ⊢; omega)).2
    rw [hfα, hfβ] at this
    simpa using this
  · intro k hk
    have := (hFup k hk).2
    rw [hFα, hFβ] at this
    simpa using this
  · intro k hk
    have := (hFdn k hk).2
    rw [hFα, hFβ] at this
    simpa using this
  · intro Y hY
    have hW : cas a f F N ≠ 0 := by linarith
    obtain ⟨κ, μ, hκμ⟩ := exists_combination a c f F Y (J + 1) N (by omega) hf hF hY haN hW
    refine ⟨κ, μ, fun k hk => hκμ k (by rw [mem_Icc] at hk ⊢; omega), ?_⟩
    have h1 := hκμ N (by rw [mem_Icc]; omega)
    have h2 := hκμ (N + 1) (by rw [mem_Icc]; omega)
    unfold cas
    rw [h1, h2]
    ring

/-- info: 'FormalResearch.Special.dao_exists_two_site' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dao_exists_two_site

/-- info: 'FormalResearch.Special.dao_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dao_decomposition

end FormalResearch.Special
