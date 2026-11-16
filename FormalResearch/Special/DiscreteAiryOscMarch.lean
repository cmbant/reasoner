module

public import FormalResearch.Special.DiscreteAiryOscPair

/-!
# The two Grönwall marches for the `Ai`/`Bi` parametrix pair

`dao_up` and `dao_down` (see `DiscreteAiryOscPair` for the setting): for an exact solution `Y` of the rows and its Cramer
coefficients `(α_b, β_b)` at a base bond `b`, the coefficients move by at most `e^Λ - 1` in the weighted `ℓ¹` norms
(`e^{-2ξ}|α| + |β|` forward, `|α| + e^{2ξ}|β|` backward), `Λ = 475 g_max K δ⁶ · 8√(2+M)/(c₁δ²)/γ = O(δ³)` for `γ ≍ δ`.

* `dao_up` (rows `Icc (b+1) N`): `|Y_k - α_b φ_k - β_b ψ_k| ≤ 450 g_max (e^{-2ξ(X_b)}|α_b| + |β_b|)(e^Λ - 1) airyBiWt(X_k)`,
  `b ≤ k ≤ N`: stable for the growing partner, error *relative to `airyBiWt`*;
* `dao_down` (rows `Icc (J+1) b`): `|Y_k - α_b φ_k - β_b ψ_k| ≤ 450 g_max (|α_b| + e^{2ξ(X_b)}|β_b|)(e^Λ - 1) airyWt(X_k)`,
  `J ≤ k ≤ b`: stable for the *decaying* partner (this is the recessive-solution comparison: start from `α = 1, β = 0`
  at the last bond and march to the turn and beyond, error relative to `airyWt`).

**Claim class: proved.**
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

section marches
variable {X g a c Y : ℤ → ℝ} {J N : ℤ} {δ c1 c2 gmin gmax ca K M : ℝ}

/-- `e^{-2ξ} · airyBiWt = airyWt`. -/
lemma dao_exp_mul (x : ℝ) : Real.exp (-2 * airyXi x) * airyBiWt x = airyWt x := by
  rw [airyBiWt_eq_mul]
  have : Real.exp (-2 * airyXi x) * Real.exp (2 * airyXi x) = 1 := by rw [← Real.exp_add]; simp
  calc Real.exp (-2 * airyXi x) * (airyWt x * Real.exp (2 * airyXi x)) =
      airyWt x * (Real.exp (-2 * airyXi x) * Real.exp (2 * airyXi x)) := by ring
    _ = _ := by rw [this, mul_one]

/-- `e^{2ξ} · airyWt = airyBiWt`. -/
lemma dao_exp_mul' (x : ℝ) : Real.exp (2 * airyXi x) * airyWt x = airyBiWt x := by
  rw [airyBiWt_eq_mul]; ring

/-- The Casoratian is bounded below by `γ` on the whole lattice once it is `≥ 2γ` at one bond. -/
lemma DaoPair.cas_lower (hP : DaoPair X g a c J N δ c1 c2 gmin gmax ca K M) {b : ℤ} {γ : ℝ}
    (hb : b ∈ Icc J N) (hDb : 2 * γ ≤ |cas a (daoPhi g X) (daoPsi g X) b|)
    (hsm : 475 * gmax * K * δ ^ 6 * (8 * √(2 + M) / (c1 * δ ^ 2)) ≤ γ) :
    ∀ k ∈ Icc J N, γ ≤ |cas a (daoPhi g X) (daoPsi g X) k| := by
  intro k hk
  have h := hP.cas_vary hb hk
  have h2 := abs_sub_abs_le_abs_sub (cas a (daoPhi g X) (daoPsi g X) b) (cas a (daoPhi g X) (daoPsi g X) k)
  rw [abs_sub_comm] at h2
  linarith

/-- **Forward march** (weight `e^{-2ξ}`): see the module docstring. -/
theorem dao_up (hP : DaoPair X g a c J N δ c1 c2 gmin gmax ca K M) {b : ℤ} {γ Λ : ℝ}
    (hb : b ∈ Icc J N) (hγ : 0 < γ) (hDb : 2 * γ ≤ |cas a (daoPhi g X) (daoPsi g X) b|)
    (hsm : 475 * gmax * K * δ ^ 6 * (8 * √(2 + M) / (c1 * δ ^ 2)) ≤ γ)
    (hΛ : 475 * gmax * K * δ ^ 6 * (8 * √(2 + M) / (c1 * δ ^ 2)) / γ ≤ Λ)
    (hY : ∀ k ∈ Icc (b + 1) N, jac a c Y k = 0) :
    ∀ k ∈ Icc b N,
      |Y k - vocA a Y (daoPhi g X) (daoPsi g X) b * daoPhi g X k -
          vocB a Y (daoPhi g X) (daoPsi g X) b * daoPsi g X k| ≤
        450 * gmax * (Real.exp (-2 * airyXi (X b)) * |vocA a Y (daoPhi g X) (daoPsi g X) b| +
          |vocB a Y (daoPhi g X) (daoPsi g X) b|) * (Real.exp Λ - 1) * airyBiWt (X k) := by
  have hb2 := mem_Icc.1 hb
  have hJN : J ≤ N := hb2.1.trans hb2.2
  have hgmax := hP.gmax_pos hJN
  have hK := hP.K_nonneg
  have hδ := hP.δ_pos
  have hE : 0 ≤ 475 * gmax * K * δ ^ 6 := by positivity
  have hDk := hP.cas_lower hb hDb hsm
  set E : ℝ := 475 * gmax * K * δ ^ 6 with hEdef
  set ω : ℤ → ℝ := fun k => Real.exp (-2 * airyXi (X k)) with hω
  set lam : ℤ → ℝ := fun i => E * (√(2 + |X i|))⁻¹ / γ with hlam
  have hlamγ : ∀ i, lam i * γ = E * (√(2 + |X i|))⁻¹ := by
    intro i; simp only [hlam]; field_simp
  have hq0 : ∀ i, 0 ≤ (√(2 + |X i|))⁻¹ := fun i => by positivity
  have hmono : ∀ k ∈ Icc (b + 1) N, X (k - 1) ≤ X k := by
    intro k hk
    rw [mem_Icc] at hk
    have := (hP.gap (k - 1) (by rw [mem_Icc]; omega)).1
    have e : k - 1 + 1 = k := by ring
    rw [e] at this
    have := mul_pos hP.c1_pos hδ
    linarith [(hP.gap (k - 1) (by rw [mem_Icc]; omega)).1]
  have hωd : ∀ k ∈ Icc (b + 1) N, ω k ≤ ω (k - 1) := by
    intro k hk
    simp only [hω]
    apply Real.exp_le_exp.2
    have := airyXi_mono (hmono k hk)
    linarith
  have hMarch := voc_march_up (a := a) (c := c) (Y := Y) (φ := daoPhi g X) (ψ := daoPsi g X) (ω := ω)
    (lam := lam) (m := b) (K := N) (γ := γ) (Λ := Λ) hγ hY (fun k hk => hDk k (by rw [mem_Icc] at hk ⊢; omega))
    (Real.exp_pos _) (fun k hk => ⟨Real.exp_pos _, hωd k hk⟩)
    (fun k hk => by have := hq0 k; simp only [hlam]; positivity)
    (by
      intro k hk
      have hk' : k ∈ Icc J (N + 1) := by rw [mem_Icc] at hk ⊢; omega
      have hk'' : k ∈ Icc (J + 1) N := by rw [mem_Icc] at hk ⊢; omega
      have h1 := hP.phi_abs hk'
      have h2 := hP.psi_abs hk'
      have h3 := hP.defA k hk''
      have hw := airyWt_mul_airyBiWt (X k)
      have hT : ω k * |daoPsi g X k| + |daoPhi g X k| ≤ 475 * gmax * airyWt (X k) := by
        have : ω k * |daoPsi g X k| ≤ ω k * (450 * gmax * airyBiWt (X k)) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
        have e : ω k * (450 * gmax * airyBiWt (X k)) = 450 * gmax * airyWt (X k) := by
          simp only [hω]; rw [← dao_exp_mul (X k)]; ring
        linarith
      have hwt := airyWt_pos (X k)
      have hwbk : airyWt (X k) * airyWt (X k) = (√(2 + |X k|))⁻¹ * ω k := by
        rw [← hw]; simp only [hω]; rw [← dao_exp_mul (X k)]; ring
      rw [hlamγ]
      have hq := hq0 k
      have hωk : 0 < ω k := Real.exp_pos _
      calc (ω k * |daoPsi g X k| + |daoPhi g X k|) * |jac a c (daoPhi g X) k|
          ≤ (475 * gmax * airyWt (X k)) * (K * δ ^ 6 * airyWt (X k)) :=
            mul_le_mul hT h3 (abs_nonneg _) (by positivity)
        _ = E * (airyWt (X k) * airyWt (X k)) := by simp only [hEdef]; ring
        _ = E * ((√(2 + |X k|))⁻¹ * ω k) := by rw [hwbk]
        _ ≤ E * ((√(2 + |X k|))⁻¹ * ω (k - 1)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hωd k hk) hq) hE
        _ = _ := by ring)
    (by
      intro k hk
      have hk' : k ∈ Icc J (N + 1) := by rw [mem_Icc] at hk ⊢; omega
      have hk'' : k ∈ Icc (J + 1) N := by rw [mem_Icc] at hk ⊢; omega
      have h1 := hP.phi_abs hk'
      have h2 := hP.psi_abs hk'
      have h4 := hP.defB k hk''
      have hw := airyWt_mul_airyBiWt (X k)
      have hT : ω k * |daoPsi g X k| + |daoPhi g X k| ≤ 475 * gmax * airyWt (X k) := by
        have : ω k * |daoPsi g X k| ≤ ω k * (450 * gmax * airyBiWt (X k)) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
        have e : ω k * (450 * gmax * airyBiWt (X k)) = 450 * gmax * airyWt (X k) := by
          simp only [hω]; rw [← dao_exp_mul (X k)]; ring
        linarith
      have hwt := airyWt_pos (X k)
      have hwb := airyBiWt_pos (X k)
      rw [hlamγ]
      calc (ω k * |daoPsi g X k| + |daoPhi g X k|) * |jac a c (daoPsi g X) k|
          ≤ (475 * gmax * airyWt (X k)) * (K * δ ^ 6 * airyBiWt (X k)) :=
            mul_le_mul hT h4 (abs_nonneg _) (by positivity)
        _ = E * (airyWt (X k) * airyBiWt (X k)) := by simp only [hEdef]; ring
        _ = _ := by rw [hw])
    (by
      intro k hk
      have hk2 := mem_Icc.1 hk
      have hI : Ioc b k = Ico (b + 1) (k + 1) := by
        ext i; simp only [mem_Ioc, mem_Ico]; omega
      rw [hI]
      have hs := hP.psum (p := b + 1) (q := k + 1) (by omega) (by omega) (by omega)
      have : ∑ i ∈ Ico (b + 1) (k + 1), lam i = E / γ * ∑ i ∈ Ico (b + 1) (k + 1), (√(2 + |X i|))⁻¹ := by
        rw [mul_sum]; apply sum_congr rfl; intro i _; simp only [hlam]; ring
      rw [this]
      refine le_trans ?_ hΛ
      calc E / γ * ∑ i ∈ Ico (b + 1) (k + 1), (√(2 + |X i|))⁻¹ ≤ E / γ * (8 * √(2 + M) / (c1 * δ ^ 2)) :=
            mul_le_mul_of_nonneg_left hs (by positivity)
        _ = _ := by simp only [hEdef]; ring)
  intro k hk
  have hk2 := mem_Icc.1 hk
  have hkJN : k ∈ Icc J N := by rw [mem_Icc]; omega
  obtain ⟨-, hE2⟩ := hMarch k hk
  have hrep := (voc_repr a Y (daoPhi g X) (daoPsi g X) k (by
    have := hDk k hkJN; intro h; rw [h, abs_zero] at this; linarith)).1
  have hk' : k ∈ Icc J (N + 1) := by rw [mem_Icc]; omega
  have h1 := hP.phi_abs hk'
  have h2 := hP.psi_abs hk'
  set α0 := vocA a Y (daoPhi g X) (daoPsi g X) b
  set β0 := vocB a Y (daoPhi g X) (daoPsi g X) b
  set αk := vocA a Y (daoPhi g X) (daoPsi g X) k
  set βk := vocB a Y (daoPhi g X) (daoPsi g X) k
  have e : Y k - α0 * daoPhi g X k - β0 * daoPsi g X k =
      (αk - α0) * daoPhi g X k + (βk - β0) * daoPsi g X k := by rw [hrep]; ring
  rw [e]
  have hwb := airyBiWt_pos (X k)
  have hωk : 0 < ω k := Real.exp_pos _
  have hAW : airyWt (X k) = ω k * airyBiWt (X k) := by simp only [hω]; rw [dao_exp_mul]
  calc |(αk - α0) * daoPhi g X k + (βk - β0) * daoPsi g X k|
      ≤ |αk - α0| * |daoPhi g X k| + |βk - β0| * |daoPsi g X k| := by
        refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
    _ ≤ |αk - α0| * (25 * gmax * airyWt (X k)) + |βk - β0| * (450 * gmax * airyBiWt (X k)) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
    _ = gmax * airyBiWt (X k) * (25 * (ω k * |αk - α0|) + 450 * |βk - β0|) := by rw [hAW]; ring
    _ ≤ gmax * airyBiWt (X k) * (450 * (ω k * |αk - α0| + |βk - β0|)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [mul_nonneg hωk.le (abs_nonneg (αk - α0))]
    _ ≤ gmax * airyBiWt (X k) * (450 * ((ω b * |α0| + |β0|) * (Real.exp Λ - 1))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : (0 : ℝ) ≤ 450 := by norm_num
        exact mul_le_mul_of_nonneg_left hE2 this
    _ = _ := by simp only [hω]; ring

/-- **Backward march** (weight `e^{+2ξ}`): see the module docstring. -/
theorem dao_down (hP : DaoPair X g a c J N δ c1 c2 gmin gmax ca K M) {b : ℤ} {γ Λ : ℝ}
    (hb : b ∈ Icc J N) (hγ : 0 < γ) (hDb : 2 * γ ≤ |cas a (daoPhi g X) (daoPsi g X) b|)
    (hsm : 475 * gmax * K * δ ^ 6 * (8 * √(2 + M) / (c1 * δ ^ 2)) ≤ γ)
    (hΛ : 475 * gmax * K * δ ^ 6 * (8 * √(2 + M) / (c1 * δ ^ 2)) / γ ≤ Λ)
    (hY : ∀ k ∈ Icc (J + 1) b, jac a c Y k = 0) :
    ∀ k ∈ Icc J b,
      |Y k - vocA a Y (daoPhi g X) (daoPsi g X) b * daoPhi g X k -
          vocB a Y (daoPhi g X) (daoPsi g X) b * daoPsi g X k| ≤
        450 * gmax * (|vocA a Y (daoPhi g X) (daoPsi g X) b| +
          Real.exp (2 * airyXi (X b)) * |vocB a Y (daoPhi g X) (daoPsi g X) b|) * (Real.exp Λ - 1) *
          airyWt (X k) := by
  have hb2 := mem_Icc.1 hb
  have hJN : J ≤ N := hb2.1.trans hb2.2
  have hgmax := hP.gmax_pos hJN
  have hK := hP.K_nonneg
  have hδ := hP.δ_pos
  have hE : 0 ≤ 475 * gmax * K * δ ^ 6 := by positivity
  have hDk := hP.cas_lower hb hDb hsm
  set E : ℝ := 475 * gmax * K * δ ^ 6 with hEdef
  set ω : ℤ → ℝ := fun k => Real.exp (2 * airyXi (X k)) with hω
  set lam : ℤ → ℝ := fun i => E * (√(2 + |X i|))⁻¹ / γ with hlam
  have hlamγ : ∀ i, lam i * γ = E * (√(2 + |X i|))⁻¹ := by
    intro i; simp only [hlam]; field_simp
  have hq0 : ∀ i, 0 ≤ (√(2 + |X i|))⁻¹ := fun i => by positivity
  have hmono : ∀ k ∈ Icc (J + 1) b, X (k - 1) ≤ X k := by
    intro k hk
    rw [mem_Icc] at hk
    have h := (hP.gap (k - 1) (by rw [mem_Icc]; omega)).1
    have e : k - 1 + 1 = k := by ring
    rw [e] at h
    have := mul_pos hP.c1_pos hδ
    linarith
  have hωd : ∀ k ∈ Icc (J + 1) b, ω (k - 1) ≤ ω k := by
    intro k hk
    simp only [hω]
    apply Real.exp_le_exp.2
    have := airyXi_mono (hmono k hk)
    linarith
  have hMarch := voc_march_down (a := a) (c := c) (Y := Y) (φ := daoPhi g X) (ψ := daoPsi g X) (ω := ω)
    (lam := lam) (J := J) (m := b) (γ := γ) (Λ := Λ) hγ hY
    (fun k hk => hDk k (by rw [mem_Icc] at hk ⊢; omega))
    (Real.exp_pos _) (fun k hk => ⟨Real.exp_pos _, hωd k hk⟩)
    (fun k hk => by have := hq0 k; simp only [hlam]; positivity)
    (by
      intro k hk
      have hk' : k ∈ Icc J (N + 1) := by rw [mem_Icc] at hk ⊢; omega
      have hk'' : k ∈ Icc (J + 1) N := by rw [mem_Icc] at hk ⊢; omega
      have h1 := hP.phi_abs hk'
      have h2 := hP.psi_abs hk'
      have h3 := hP.defA k hk''
      have hw := airyWt_mul_airyBiWt (X k)
      have hT : |daoPsi g X k| + ω (k - 1) * |daoPhi g X k| ≤ 475 * gmax * airyBiWt (X k) := by
        have hω1 : ω (k - 1) * |daoPhi g X k| ≤ ω k * (25 * gmax * airyWt (X k)) :=
          mul_le_mul (hωd k hk) h1 (abs_nonneg _) (Real.exp_pos _).le
        have e : ω k * (25 * gmax * airyWt (X k)) = 25 * gmax * airyBiWt (X k) := by
          simp only [hω]; rw [← dao_exp_mul' (X k)]; ring
        linarith
      have hwb := airyBiWt_pos (X k)
      rw [hlamγ]
      calc (|daoPsi g X k| + ω (k - 1) * |daoPhi g X k|) * |jac a c (daoPhi g X) k|
          ≤ (475 * gmax * airyBiWt (X k)) * (K * δ ^ 6 * airyWt (X k)) :=
            mul_le_mul hT h3 (abs_nonneg _) (by positivity)
        _ = E * (airyWt (X k) * airyBiWt (X k)) := by simp only [hEdef]; ring
        _ = _ := by rw [hw])
    (by
      intro k hk
      have hk' : k ∈ Icc J (N + 1) := by rw [mem_Icc] at hk ⊢; omega
      have hk'' : k ∈ Icc (J + 1) N := by rw [mem_Icc] at hk ⊢; omega
      have h1 := hP.phi_abs hk'
      have h2 := hP.psi_abs hk'
      have h4 := hP.defB k hk''
      have hw := airyWt_mul_airyBiWt (X k)
      have hT : |daoPsi g X k| + ω (k - 1) * |daoPhi g X k| ≤ 475 * gmax * airyBiWt (X k) := by
        have hω1 : ω (k - 1) * |daoPhi g X k| ≤ ω k * (25 * gmax * airyWt (X k)) :=
          mul_le_mul (hωd k hk) h1 (abs_nonneg _) (Real.exp_pos _).le
        have e : ω k * (25 * gmax * airyWt (X k)) = 25 * gmax * airyBiWt (X k) := by
          simp only [hω]; rw [← dao_exp_mul' (X k)]; ring
        linarith
      have hwb := airyBiWt_pos (X k)
      have hwt := airyWt_pos (X k)
      have hbb : airyBiWt (X k) * airyBiWt (X k) = (√(2 + |X k|))⁻¹ * ω k := by
        rw [← hw]; simp only [hω]; rw [← dao_exp_mul' (X k)]; ring
      have hq := hq0 k
      rw [hlamγ]
      calc (|daoPsi g X k| + ω (k - 1) * |daoPhi g X k|) * |jac a c (daoPsi g X) k|
          ≤ (475 * gmax * airyBiWt (X k)) * (K * δ ^ 6 * airyBiWt (X k)) :=
            mul_le_mul hT h4 (abs_nonneg _) (by positivity)
        _ = E * (airyBiWt (X k) * airyBiWt (X k)) := by simp only [hEdef]; ring
        _ = E * ((√(2 + |X k|))⁻¹ * ω k) := by rw [hbb]
        _ = _ := by ring)
    (by
      intro k hk
      have hk2 := mem_Icc.1 hk
      have hI : Icc (k + 1) b = Ico (k + 1) (b + 1) := by
        ext i; simp only [mem_Icc, mem_Ico]; omega
      rw [hI]
      have hs := hP.psum (p := k + 1) (q := b + 1) (by omega) (by omega) (by omega)
      have : ∑ i ∈ Ico (k + 1) (b + 1), lam i = E / γ * ∑ i ∈ Ico (k + 1) (b + 1), (√(2 + |X i|))⁻¹ := by
        rw [mul_sum]; apply sum_congr rfl; intro i _; simp only [hlam]; ring
      rw [this]
      refine le_trans ?_ hΛ
      calc E / γ * ∑ i ∈ Ico (k + 1) (b + 1), (√(2 + |X i|))⁻¹ ≤ E / γ * (8 * √(2 + M) / (c1 * δ ^ 2)) :=
            mul_le_mul_of_nonneg_left hs (by positivity)
        _ = _ := by simp only [hEdef]; ring)
  intro k hk
  have hk2 := mem_Icc.1 hk
  have hkJN : k ∈ Icc J N := by rw [mem_Icc]; omega
  obtain ⟨-, hE2⟩ := hMarch k hk
  have hrep := (voc_repr a Y (daoPhi g X) (daoPsi g X) k (by
    have := hDk k hkJN; intro h; rw [h, abs_zero] at this; linarith)).1
  have hk' : k ∈ Icc J (N + 1) := by rw [mem_Icc]; omega
  have h1 := hP.phi_abs hk'
  have h2 := hP.psi_abs hk'
  set α0 := vocA a Y (daoPhi g X) (daoPsi g X) b
  set β0 := vocB a Y (daoPhi g X) (daoPsi g X) b
  set αk := vocA a Y (daoPhi g X) (daoPsi g X) k
  set βk := vocB a Y (daoPhi g X) (daoPsi g X) k
  have e : Y k - α0 * daoPhi g X k - β0 * daoPsi g X k =
      (αk - α0) * daoPhi g X k + (βk - β0) * daoPsi g X k := by rw [hrep]; ring
  rw [e]
  have hwt := airyWt_pos (X k)
  have hωk : 0 < ω k := Real.exp_pos _
  have hAW : airyBiWt (X k) = ω k * airyWt (X k) := by simp only [hω]; rw [dao_exp_mul']
  calc |(αk - α0) * daoPhi g X k + (βk - β0) * daoPsi g X k|
      ≤ |αk - α0| * |daoPhi g X k| + |βk - β0| * |daoPsi g X k| := by
        refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
    _ ≤ |αk - α0| * (25 * gmax * airyWt (X k)) + |βk - β0| * (450 * gmax * airyBiWt (X k)) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
    _ = gmax * airyWt (X k) * (25 * |αk - α0| + 450 * (ω k * |βk - β0|)) := by rw [hAW]; ring
    _ ≤ gmax * airyWt (X k) * (450 * (|αk - α0| + ω k * |βk - β0|)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [abs_nonneg (αk - α0)]
    _ ≤ gmax * airyWt (X k) * (450 * ((|α0| + ω b * |β0|) * (Real.exp Λ - 1))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : (0 : ℝ) ≤ 450 := by norm_num
        exact mul_le_mul_of_nonneg_left hE2 this
    _ = _ := by simp only [hω]; ring

end marches

/-- info: 'FormalResearch.Special.dao_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dao_up

/-- info: 'FormalResearch.Special.dao_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dao_down

end FormalResearch.Special
