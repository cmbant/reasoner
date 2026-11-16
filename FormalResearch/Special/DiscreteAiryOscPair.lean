module

public import FormalResearch.Special.DiscreteAiryOscVoC
public import FormalResearch.Special.DiscreteAiryOscSum
public import FormalResearch.Special.DiscreteAiryOscBi
public import FormalResearch.Special.AiryParametrixShift
public import FormalResearch.Special.AiryWt
public import FormalResearch.Special.AiryRecessiveSums

/-!
# The `Ai`/`Bi` parametrix pair on a lattice: Casoratian, step bounds and the two Grönwall marches

Let `φ_k = g_k Ai(X_k)`, `ψ_k = g_k Bi(X_k)` (the parametrix pair of a simple turn; `g` the Langer amplitude) on a lattice
with steps `c₁ δ ≤ X_{k+1} - X_k ≤ c₂ δ` and `|X_k| ≤ M δ⁻²`, and let `a, c` be coefficients with the parametrix defects
`|jac a c φ_k| ≤ K δ⁶ airyWt(X_k)`, `|jac a c ψ_k| ≤ K δ⁶ airyBiWt(X_k)` (the `h² = δ⁶` defects of `airyParametrix_defect_uniform_lattice`
and `dao_bi_defect_lattice`).  This module turns that into the hypotheses of the abstract Grönwall marches of
`DiscreteAiryOscVoC`:

* `dao_cas_eq`: `cas(φ, ψ)_k = a_{k+1} g_k g_{k+1} S(X_k, X_{k+1} - X_k)/π` (`S` the Airy shift function; the Wronskian
  `Ai Bi' - Ai' Bi = 1/π` enters through `airyShiftS`); `dao_S_lower`: `S(X, s) ≥ s/2` for `0 ≤ X ≤ 1/8`, `0 < s ≤ 1/8`
  (`apx_S_taylor`), hence `cas(φ, ψ)_m ≥ c_a g_min² c₁ δ/(2π)` at a base site `X_m ∈ [0, c₂δ]`;
* `dao_cas_vary`: **the Casoratian of the approximate pair is conserved up to the defect sums**:
  `|cas_k - cas_b| ≤ E δ⁶ Σ (2+|X_i|)^{-1/2} ≤ E δ⁶ · 8√(2+M)/(c₁δ²)` (`E = 475 g_max K`), because
  `cas_k - cas_{k-1} = φ_k jac ψ_k - ψ_k jac φ_k` (Lagrange identity) and `airyWt · airyBiWt = (2+|X|)^{-1/2}`.  This replaces
  any lower bound for `S(X, s)` at large `|X|` (where `s √|X| = O(1)` and `S ≠ s`): it comes for free from the amplitude
  relation through `hrel`, via the defects;
* `dao_up`, `dao_down`: for every exact solution `Y`, with `α_b, β_b` its Cramer coefficients at a base bond `b`:
  up (`b ≤ k ≤ N`, weight `e^{-2ξ}`): `|Y_k - α_b φ_k - β_b ψ_k| ≤ 450 g_max (e^{-2ξ(X_b)}|α_b| + |β_b|)(e^Λ - 1) airyBiWt(X_k)`;
  down (`J ≤ k ≤ b`, weight `e^{+2ξ}`): `|Y_k - α_b φ_k - β_b ψ_k| ≤ 450 g_max (|α_b| + e^{2ξ(X_b)}|β_b|)(e^Λ - 1) airyWt(X_k)`,
  with `Λ = E δ⁶ · 8√(2+M)/(c₁ δ²) / γ`, `γ = ½ |cas_b|` (hypothesis `E δ⁶ Pbd ≤ γ`).  With `γ ≍ δ`, `Λ = O(δ³)`.

**Claim class: proved** (no hypothesis beyond those stated; constants explicit).
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- `φ_k = g_k Ai(X_k)`. -/
noncomputable def daoPhi (g X : ℤ → ℝ) : ℤ → ℝ := fun i => g i * airyAi (X i)

/-- `ψ_k = g_k Bi(X_k)`. -/
noncomputable def daoPsi (g X : ℤ → ℝ) : ℤ → ℝ := fun i => g i * airyBi (X i)

/-- The lattice data of the `Ai`/`Bi` parametrix pair on the sites `J..N+1` (rows `J+1..N`). -/
structure DaoPair (X g a c : ℤ → ℝ) (J N : ℤ) (δ c1 c2 gmin gmax ca K M : ℝ) : Prop where
  δ_pos : 0 < δ
  δ_le : δ ≤ 1
  c1_pos : 0 < c1
  c2δ : c2 * δ ≤ 1
  gap : ∀ k ∈ Icc J N, c1 * δ ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ c2 * δ
  Xabs : ∀ k ∈ Icc J (N + 1), |X k| ≤ M / δ ^ 2
  gmin_pos : 0 < gmin
  gb : ∀ k ∈ Icc J (N + 1), gmin ≤ g k ∧ g k ≤ gmax
  ca_pos : 0 < ca
  alow : ∀ k ∈ Icc (J + 1) (N + 1), ca ≤ a k
  K_nonneg : 0 ≤ K
  defA : ∀ k ∈ Icc (J + 1) N, |jac a c (daoPhi g X) k| ≤ K * δ ^ 6 * airyWt (X k)
  defB : ∀ k ∈ Icc (J + 1) N, |jac a c (daoPsi g X) k| ≤ K * δ ^ 6 * airyBiWt (X k)

/-- `S(X, s) ≥ s/2` for `0 ≤ X ≤ 1/8`, `0 < s ≤ 1/8`. -/
lemma dao_S_lower {X s : ℝ} (hX0 : 0 ≤ X) (hX1 : X ≤ 1 / 8) (hs0 : 0 < s) (hs1 : s ≤ 1 / 8) :
    s / 2 ≤ airyShiftS X s := by
  have hs : |s| ≤ 1 := by rw [abs_of_pos hs0]; linarith
  have hu : |s| * √(1 + |X|) ≤ 1 := by
    rw [abs_of_pos hs0, abs_of_nonneg hX0]
    have : √(1 + X) ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; nlinarith
    nlinarith
  have h := apx_S_taylor hs hu
  rw [abs_of_pos hs0, abs_of_nonneg hX0] at h
  have hexp : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hsq : √(1 + X) ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  have hsq0 : 0 ≤ √(1 + X) := Real.sqrt_nonneg _
  have h6 : (1 + X) ^ 2 * √(1 + X) * s ^ 6 ≤ 4 * (1 / 8) ^ 5 * s := by
    have e1 : (1 + X) ^ 2 ≤ 2 := by nlinarith
    have e2 : s ^ 6 ≤ (1 / 8) ^ 5 * s := by
      have : s ^ 5 ≤ (1 / 8) ^ 5 := pow_le_pow_left₀ hs0.le hs1 5
      nlinarith [pow_pos hs0 5]
    calc (1 + X) ^ 2 * √(1 + X) * s ^ 6 ≤ (2 * 2) * ((1 / 8) ^ 5 * s) := by
          apply mul_le_mul (mul_le_mul e1 hsq hsq0 (by norm_num)) e2 (by positivity) (by norm_num)
      _ = _ := by ring
  have hrem : 11 * Real.exp 1 * ((1 + X) ^ 2 * √(1 + X)) * s ^ 6 ≤ 33 * (4 * (1 / 8) ^ 5 * s) := by
    calc 11 * Real.exp 1 * ((1 + X) ^ 2 * √(1 + X)) * s ^ 6 = (11 * Real.exp 1) * ((1 + X) ^ 2 * √(1 + X) * s ^ 6) := by ring
      _ ≤ 33 * (4 * (1 / 8) ^ 5 * s) := by
          apply mul_le_mul (by linarith) h6 (by positivity) (by norm_num)
  have hlow := (abs_le.1 h).1
  have t1 : X * s ^ 3 / 6 ≤ s / 100 := by
    have : s ^ 2 ≤ 1 / 64 := by nlinarith
    nlinarith [mul_nonneg hX0 hs0.le, mul_nonneg hX0 (sq_nonneg s)]
  have t2 : s ^ 4 / 12 ≤ s / 100 := by
    have : s ^ 3 ≤ 1 / 512 := by
      have := pow_le_pow_left₀ hs0.le hs1 3; norm_num at this; linarith
    nlinarith [pow_pos hs0 3]
  have t3 : X ^ 2 * s ^ 5 / 120 ≤ s / 100 := by
    have h5 : s ^ 4 ≤ 1 / 4096 := by
      have := pow_le_pow_left₀ hs0.le hs1 4; norm_num at this; linarith
    have hX2 : X ^ 2 ≤ 1 / 64 := by nlinarith
    nlinarith [pow_pos hs0 4, mul_nonneg (sq_nonneg X) (pow_pos hs0 4).le]
  have n1 : 0 ≤ X * s ^ 3 / 6 := by positivity
  have n2 : 0 ≤ s ^ 4 / 12 := by positivity
  have n3 : 0 ≤ X ^ 2 * s ^ 5 / 120 := by positivity
  have : (4 : ℝ) * (1 / 8) ^ 5 * 33 ≤ 1 / 4 := by norm_num
  nlinarith [hs0]

/-- `cas(φ, ψ)_k = a_{k+1} g_k g_{k+1} S(X_k, X_{k+1} - X_k)/π`. -/
lemma dao_cas_eq (a g X : ℤ → ℝ) (k : ℤ) :
    cas a (daoPhi g X) (daoPsi g X) k =
      a (k + 1) * g k * g (k + 1) * airyShiftS (X k) (X (k + 1) - X k) / Real.pi := by
  have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
  have e : X k + (X (k + 1) - X k) = X (k + 1) := by ring
  unfold cas daoPhi daoPsi airyShiftS
  rw [e]
  field_simp

/-- Lower bound for the Casoratian at a base site with `0 ≤ X_m ≤ c₂ δ ≤ 1/8`. -/
lemma dao_cas_base {X g a : ℤ → ℝ} {m : ℤ} {δ c1 c2 gmin ca : ℝ} (hc1 : 0 < c1) (hδ : 0 < δ)
    (hc2δ : c2 * δ ≤ 1 / 8) (hgmin : 0 < gmin) (hca : 0 < ca)
    (hX0 : 0 ≤ X m) (hX1 : X m ≤ c2 * δ) (hs1 : c1 * δ ≤ X (m + 1) - X m)
    (hs2 : X (m + 1) - X m ≤ c2 * δ) (hg : gmin ≤ g m) (hg1 : gmin ≤ g (m + 1)) (ha : ca ≤ a (m + 1)) :
    ca * gmin ^ 2 * (c1 * δ) / (2 * Real.pi) ≤ cas a (daoPhi g X) (daoPsi g X) m := by
  rw [dao_cas_eq]
  have hs0 : 0 < X (m + 1) - X m := lt_of_lt_of_le (mul_pos hc1 hδ) hs1
  have hS := dao_S_lower hX0 (by linarith) hs0 (by linarith)
  have hπ := Real.pi_pos
  rw [div_le_div_iff₀ (by positivity) hπ]
  have h1 : ca * gmin ^ 2 ≤ a (m + 1) * g m * g (m + 1) := by
    have e1 : 0 ≤ gmin := hgmin.le
    calc ca * gmin ^ 2 = ca * (gmin * gmin) := by ring
      _ ≤ a (m + 1) * (g m * g (m + 1)) := by
          apply mul_le_mul ha (mul_le_mul hg hg1 e1 (e1.trans hg)) (by positivity) (hca.le.trans ha)
      _ = _ := by ring
  have h2 : c1 * δ / 2 ≤ airyShiftS (X m) (X (m + 1) - X m) := by linarith
  have hA : 0 ≤ ca * gmin ^ 2 := by positivity
  have hb : 0 ≤ (a (m + 1) * g m * g (m + 1)) * (2 * Real.pi) := by
    have e1 : 0 ≤ a (m + 1) := hca.le.trans ha
    have e2 : 0 ≤ g m := hgmin.le.trans hg
    have e3 : 0 ≤ g (m + 1) := hgmin.le.trans hg1
    positivity
  calc ca * gmin ^ 2 * (c1 * δ) * Real.pi = (ca * gmin ^ 2) * (2 * Real.pi) * (c1 * δ / 2) := by ring
    _ ≤ (a (m + 1) * g m * g (m + 1)) * (2 * Real.pi) * (airyShiftS (X m) (X (m + 1) - X m)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right h1 (by positivity)) h2 (by positivity) hb
    _ = _ := by ring

section lattice
variable {X g a c : ℤ → ℝ} {J N : ℤ} {δ c1 c2 gmin gmax ca K M : ℝ}

lemma DaoPair.gmax_pos (hP : DaoPair X g a c J N δ c1 c2 gmin gmax ca K M) (hJN : J ≤ N) : 0 < gmax := by
  have := hP.gb J (by rw [mem_Icc]; omega)
  linarith [hP.gmin_pos]

/-- `|φ_k| ≤ 25 g_max airyWt(X_k)`. -/
lemma DaoPair.phi_abs (hP : DaoPair X g a c J N δ c1 c2 gmin gmax ca K M) {k : ℤ}
    (hk : k ∈ Icc J (N + 1)) : |daoPhi g X k| ≤ 25 * gmax * airyWt (X k) := by
  obtain ⟨h1, h2⟩ := hP.gb k hk
  have hg0 : 0 ≤ g k := hP.gmin_pos.le.trans h1
  unfold daoPhi
  rw [abs_mul, abs_of_nonneg hg0]
  have := (apx_airy_global (X k)).1
  calc g k * |airyAi (X k)| ≤ gmax * (25 * airyWt (X k)) := mul_le_mul h2 this (abs_nonneg _) (hg0.trans h2)
    _ = _ := by ring

/-- `|ψ_k| ≤ 450 g_max airyBiWt(X_k)`. -/
lemma DaoPair.psi_abs (hP : DaoPair X g a c J N δ c1 c2 gmin gmax ca K M) {k : ℤ}
    (hk : k ∈ Icc J (N + 1)) : |daoPsi g X k| ≤ 450 * gmax * airyBiWt (X k) := by
  obtain ⟨h1, h2⟩ := hP.gb k hk
  have hg0 : 0 ≤ g k := hP.gmin_pos.le.trans h1
  unfold daoPsi
  rw [abs_mul, abs_of_nonneg hg0]
  have := (apx_airyBi_global (X k)).1
  calc g k * |airyBi (X k)| ≤ gmax * (450 * airyBiWt (X k)) := mul_le_mul h2 this (abs_nonneg _) (hg0.trans h2)
    _ = _ := by ring

/-- The sum of the amplitude squares over the lattice: `Σ_{Ico p q} (2+|X_i|)^{-1/2} ≤ 8√(2+M)/(c₁δ²)`. -/
lemma DaoPair.psum (hP : DaoPair X g a c J N δ c1 c2 gmin gmax ca K M) {p q : ℤ} (hpq : p ≤ q)
    (hp : J ≤ p) (hq : q ≤ N + 1) :
    ∑ i ∈ Ico p q, (√(2 + |X i|))⁻¹ ≤ 8 * √(2 + M) / (c1 * δ ^ 2) := by
  have hδ := hP.δ_pos
  have hc1 := hP.c1_pos
  have hg : 0 < c1 * δ := mul_pos hc1 hδ
  have hgap : ∀ i ∈ Ico p q, c1 * δ ≤ X (i + 1) - X i ∧ X (i + 1) - X i ≤ 1 := by
    intro i hi
    rw [mem_Ico] at hi
    obtain ⟨h1, h2⟩ := hP.gap i (by rw [mem_Icc]; omega)
    exact ⟨h1, h2.trans hP.c2δ⟩
  have h := dao_sum_p hg hgap
  have hM : 0 ≤ M := by
    have := hP.Xabs p (by rw [mem_Icc]; omega)
    have h0 : 0 ≤ |X p| := abs_nonneg _
    have : 0 ≤ M / δ ^ 2 := h0.trans this
    by_contra hneg
    have : M / δ ^ 2 < 0 := div_neg_of_neg_of_pos (not_le.1 hneg) (by positivity)
    linarith
  have hs : ∀ i ∈ Icc J (N + 1), √(2 + |X i|) ≤ √(2 + M) / δ := by
    intro i hi
    have := hP.Xabs i hi
    rw [le_div_iff₀ hδ, ← Real.sqrt_sq hδ.le, ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    have h2 : (2 + M / δ ^ 2) * δ ^ 2 = 2 * δ ^ 2 + M := by field_simp
    have hδ2 : δ ^ 2 ≤ 1 := by nlinarith [hP.δ_le]
    have : (2 + |X i|) * δ ^ 2 ≤ (2 + M / δ ^ 2) * δ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith
  have h1 := hs p (by rw [mem_Icc]; omega)
  have h2 := hs q (by rw [mem_Icc]; omega)
  refine h.trans ?_
  have e : 4 / (c1 * δ) * (√(2 + M) / δ + √(2 + M) / δ) = 8 * √(2 + M) / (c1 * δ ^ 2) := by
    field_simp; ring
  rw [← e]
  gcongr

end lattice

section lattice2
variable {X g a c : ℤ → ℝ} {J N : ℤ} {δ c1 c2 gmin gmax ca K M : ℝ}

/-- **Casoratian step**: `|cas_k - cas_{k-1}| ≤ 475 g_max K δ⁶ (2+|X_k|)^{-1/2}`. -/
lemma DaoPair.cas_step (hP : DaoPair X g a c J N δ c1 c2 gmin gmax ca K M) {k : ℤ}
    (hk : k ∈ Icc (J + 1) N) :
    |cas a (daoPhi g X) (daoPsi g X) k - cas a (daoPhi g X) (daoPsi g X) (k - 1)| ≤
      475 * gmax * K * δ ^ 6 * (√(2 + |X k|))⁻¹ := by
  have hk' : k ∈ Icc J (N + 1) := by rw [mem_Icc] at hk ⊢; omega
  have e := cas_sub a c (daoPhi g X) (daoPsi g X) k
  rw [e]
  have h1 := hP.phi_abs hk'
  have h2 := hP.psi_abs hk'
  have h3 := hP.defA k hk
  have h4 := hP.defB k hk
  have hw := airyWt_mul_airyBiWt (X k)
  have hg0 : 0 ≤ gmax := (hP.gmax_pos (by rw [mem_Icc] at hk; omega)).le
  have hK := hP.K_nonneg
  have hδ6 : 0 ≤ δ ^ 6 := by have := hP.δ_pos; positivity
  have hw1 := airyWt_pos (X k)
  have hw2 := airyBiWt_pos (X k)
  have t1 : |daoPhi g X k * jac a c (daoPsi g X) k| ≤ 25 * gmax * K * δ ^ 6 * (√(2 + |X k|))⁻¹ := by
    rw [abs_mul]
    calc |daoPhi g X k| * |jac a c (daoPsi g X) k| ≤ (25 * gmax * airyWt (X k)) * (K * δ ^ 6 * airyBiWt (X k)) :=
          mul_le_mul h1 h4 (abs_nonneg _) (by positivity)
      _ = 25 * gmax * K * δ ^ 6 * (airyWt (X k) * airyBiWt (X k)) := by ring
      _ = _ := by rw [hw]
  have t2 : |daoPsi g X k * jac a c (daoPhi g X) k| ≤ 450 * gmax * K * δ ^ 6 * (√(2 + |X k|))⁻¹ := by
    rw [abs_mul]
    calc |daoPsi g X k| * |jac a c (daoPhi g X) k| ≤ (450 * gmax * airyBiWt (X k)) * (K * δ ^ 6 * airyWt (X k)) :=
          mul_le_mul h2 h3 (abs_nonneg _) (by positivity)
      _ = 450 * gmax * K * δ ^ 6 * (airyWt (X k) * airyBiWt (X k)) := by ring
      _ = _ := by rw [hw]
  calc _ ≤ |daoPhi g X k * jac a c (daoPsi g X) k| + |daoPsi g X k * jac a c (daoPhi g X) k| := abs_sub _ _
    _ ≤ _ := by linarith

/-- **Conservation of the Casoratian up to the defect sums**: for `b, k ∈ Icc J N`,
`|cas_k - cas_b| ≤ 475 g_max K δ⁶ · 8√(2+M)/(c₁δ²)`. -/
theorem DaoPair.cas_vary (hP : DaoPair X g a c J N δ c1 c2 gmin gmax ca K M) {b k : ℤ}
    (hb : b ∈ Icc J N) (hk : k ∈ Icc J N) :
    |cas a (daoPhi g X) (daoPsi g X) k - cas a (daoPhi g X) (daoPsi g X) b| ≤
      475 * gmax * K * δ ^ 6 * (8 * √(2 + M) / (c1 * δ ^ 2)) := by
  have key : ∀ b' k' : ℤ, J ≤ b' → b' ≤ k' → k' ≤ N →
      |cas a (daoPhi g X) (daoPsi g X) k' - cas a (daoPhi g X) (daoPsi g X) b'| ≤
        475 * gmax * K * δ ^ 6 * ∑ i ∈ Ico (b' + 1) (k' + 1), (√(2 + |X i|))⁻¹ := by
    intro b' k' hb' hbk hkN
    refine dao_int_up_induction (P := fun n => n ≤ N →
      |cas a (daoPhi g X) (daoPsi g X) n - cas a (daoPhi g X) (daoPsi g X) b'| ≤
        475 * gmax * K * δ ^ 6 * ∑ i ∈ Ico (b' + 1) (n + 1), (√(2 + |X i|))⁻¹) b' ?_ ?_ k' hbk hkN
    · intro _; simp
    · intro n hn ih hn1
      have hI : Ico (b' + 1) (n + 1 + 1) = insert (n + 1) (Ico (b' + 1) (n + 1)) := by
        ext i; simp only [mem_Ico, mem_insert]; omega
      rw [hI, sum_insert (by simp)]
      have h1 := hP.cas_step (k := n + 1) (by rw [mem_Icc]; omega)
      simp only [add_sub_cancel_right] at h1
      have h2 := ih (by omega)
      have := abs_add_le (cas a (daoPhi g X) (daoPsi g X) (n + 1) - cas a (daoPhi g X) (daoPsi g X) n)
        (cas a (daoPhi g X) (daoPsi g X) n - cas a (daoPhi g X) (daoPsi g X) b')
      have e : cas a (daoPhi g X) (daoPsi g X) (n + 1) - cas a (daoPhi g X) (daoPsi g X) n +
          (cas a (daoPhi g X) (daoPsi g X) n - cas a (daoPhi g X) (daoPsi g X) b') =
          cas a (daoPhi g X) (daoPsi g X) (n + 1) - cas a (daoPhi g X) (daoPsi g X) b' := by ring
      rw [e] at this
      nlinarith
  have hb2 := mem_Icc.1 hb
  have hk2 := mem_Icc.1 hk
  have hsum : ∀ b' k' : ℤ, J ≤ b' → b' ≤ k' → k' ≤ N →
      ∑ i ∈ Ico (b' + 1) (k' + 1), (√(2 + |X i|))⁻¹ ≤ 8 * √(2 + M) / (c1 * δ ^ 2) := by
    intro b' k' hb' hbk hkN
    exact hP.psum (by omega) (by omega) (by omega)
  have hE : 0 ≤ 475 * gmax * K * δ ^ 6 := by
    have := (hP.gmax_pos (by omega : J ≤ N)).le
    have := hP.K_nonneg
    have := hP.δ_pos
    positivity
  rcases le_total b k with hbk | hkb
  · refine (key b k hb2.1 hbk hk2.2).trans ?_
    exact mul_le_mul_of_nonneg_left (hsum b k hb2.1 hbk hk2.2) hE
  · rw [abs_sub_comm]
    refine (key k b hk2.1 hkb hb2.2).trans ?_
    exact mul_le_mul_of_nonneg_left (hsum k b hk2.1 hkb hb2.2) hE

end lattice2

/-- info: 'FormalResearch.Special.DaoPair.cas_vary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.DaoPair.cas_vary

/-- info: 'FormalResearch.Special.dao_cas_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dao_cas_base

end FormalResearch.Special
