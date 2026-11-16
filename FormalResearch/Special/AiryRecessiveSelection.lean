module

public import FormalResearch.Special.AiryRecessive
public import FormalResearch.Special.DiscreteJacobiCalculusComparison

/-!
# The recessive Airy solution, part 2: the second solution, recessive selection, packaged theorem

Continuation of `AiryRecessive` (see there for the setting, the hypotheses `AiryLattice`, `AiryComparison`, `hdef`, and the
numerics).  All **proved**; nothing about `Bi`.

* `physical_decomposition`: `Y = κ f + μ f₂` with `f₂ = secondSol a f m`, `cas a f f₂ ≡ 1`, exact `μ`;
* `abs_mu_le`, `abs_mu_le_airy` (`A:1160`): `|μ| ≤ 3 κ₂ a_{N+1} Y_max e^{-ξ(X_N)}`;
* `secondSol_le`, `secondSol_ge`: `1/(a_k f_{k-1}) ≤ f₂_k` and `0 ≤ f₂_k ≤ C₂ δ⁻¹/airyWt(X_k)`;
* `recessive_selection_airy` (W1 `lem:recessive`, est:291-299, exact `f₂`): `|μ| ≤ 4|κ| f_{k₀} A₁ (3κ₂/2) airyWt(X_{k₁-1})` from two
  nodes with `|Y_{k₁}| ≤ |Y_{k₀}|`, `f_{k₁} ≤ f_{k₀}` and the `ξ`-gap condition `2C₂δ⁻¹/airyWt(X_{k₀}) ≤ 1/(A₁(3κ₂/2)airyWt(X_{k₁-1}))`
  (the two nodes must be separated by `ξ(X_{k₁-1}) - ξ(X_{k₀}) ≳ log(1/δ)` plus a constant: this is *not* implied by
  W1's nodes `X₀ = (3/4 log 1/h)^{2/3}`, `X₀ + 2`, whose `ξ`-gap is only about `2√X₀`; with nodes spread this way it holds,
  numerically on the model chain); `Y_{k₀} ≠ 0 ⇒ κ ≠ 0`;
* `recessive_airy_selection`: everything packaged (the interface for the window lemma M6).

**Not formalised:** the sharper `(1+X⁺)^{-1/2}` saving in the bound for `f₂`; the monotone decay hypothesis `|Y_{k₁}| ≤ |Y_{k₀}|`
(from `hardEdge_abs_antitone`, M1b); the oscillatory side.
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-! ### The physical solution: recessive selection -/

lemma airyWt_le_exp_neg (X : ℝ) : airyWt X ≤ Real.exp (-airyXi X) := by
  unfold airyWt
  have h : (2 + |X|) ^ (-(1 / 4) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg X]) (by norm_num)
  have := Real.exp_pos (-airyXi X)
  nlinarith

/-- **Two-solution decomposition with the exact second solution** (`A:1155-1160`).  Let `f > 0` on `Icc m (N+1)` solve the
rows `Icc (m+1) N` (`a > 0`), `f₂ = secondSol a f m` (reduction of order).  Then `f₂` solves the rows, the Casoratian
`cas a f f₂` is `≡ 1` on `Icc m N`, and every solution `Y` of the rows is `κ f + μ f₂` on `Icc m (N+1)` with the exact
`μ = a_{N+1} (f_N Y_{N+1} - f_{N+1} Y_N)` (the Casoratian at the last bond, divided by `W = 1`). -/
theorem physical_decomposition (a c f Y : ℤ → ℝ) (m N : ℤ) (hmN : m ≤ N)
    (ha : ∀ k ∈ Icc (m + 1) (N + 1), 0 < a k) (hf : ∀ k ∈ Icc m (N + 1), 0 < f k)
    (hfrow : ∀ k ∈ Icc (m + 1) N, jac a c f k = 0) (hY : ∀ k ∈ Icc (m + 1) N, jac a c Y k = 0) :
    (∀ k ∈ Icc (m + 1) N, jac a c (secondSol a f m) k = 0) ∧
      (∀ k ∈ Icc m N, cas a f (secondSol a f m) k = 1) ∧
      ∃ κ μ : ℝ, (∀ k ∈ Icc m (N + 1), Y k = κ * f k + μ * secondSol a f m k) ∧
        μ = a (N + 1) * (f N * Y (N + 1) - f (N + 1) * Y N) := by
  have hmem : ∀ k, m ≤ k → k ≤ N + 1 → k ∈ Icc m (N + 1) := fun k h1 h2 => by
    simp only [mem_Icc]; exact ⟨h1, h2⟩
  have hamem : ∀ k, m + 1 ≤ k → k ≤ N + 1 → 0 < a k := fun k h1 h2 =>
    ha k (by simp only [mem_Icc]; exact ⟨h1, h2⟩)
  have hf2 : ∀ k ∈ Icc (m + 1) N, jac a c (secondSol a f m) k = 0 := by
    intro k hk
    rw [mem_Icc] at hk
    exact jac_secondSol a c f m k hk.1 (hamem (k + 1) (by omega) (by omega)).ne'
      (hamem k hk.1 (by omega)).ne' (hf (k - 1) (hmem _ (by omega) (by omega))).ne'
      (hf k (hmem _ (by omega) (by omega))).ne' (hf (k + 1) (hmem _ (by omega) (by omega))).ne'
      (hfrow k (by simp only [mem_Icc]; omega))
  have hcas : ∀ k ∈ Icc m N, cas a f (secondSol a f m) k = 1 := by
    intro k hk
    rw [mem_Icc] at hk
    exact cas_secondSol a f m k hk.1 (hamem (k + 1) (by omega) (by omega)).ne'
      (hf k (hmem _ hk.1 (by omega))).ne' (hf (k + 1) (hmem _ (by omega) (by omega))).ne'
  refine ⟨hf2, hcas, ?_⟩
  have hW : cas a f (secondSol a f m) N ≠ 0 := by
    rw [hcas N (by simp only [mem_Icc]; omega)]; exact one_ne_zero
  obtain ⟨κ, μ, hcomb⟩ := exists_combination a c f (secondSol a f m) Y (m + 1) N (by omega) hfrow hf2 hY
    (fun k hk => (ha k hk).ne') hW
  have hcomb' : ∀ k ∈ Icc m (N + 1), Y k = κ * f k + μ * secondSol a f m k := by
    intro k hk
    exact hcomb k (by rw [mem_Icc] at hk ⊢; omega)
  refine ⟨κ, μ, hcomb', ?_⟩
  have h0 := hcomb' N (hmem N hmN (by omega))
  have h1 := hcomb' (N + 1) (hmem (N + 1) (by omega) le_rfl)
  have hc1 := hcas N (by simp only [mem_Icc]; omega)
  unfold cas at hc1
  rw [h0, h1]
  linear_combination (-μ) * hc1

/-- **`|μ|` bound** (`A:1160`).  Abstract form: `|μ| ≤ a_{N+1} (f_N |Y_{N+1}| + f_{N+1} |Y_N|)`. -/
theorem abs_mu_le (a f Y : ℤ → ℝ) (N : ℤ) (μ : ℝ) (hμ : μ = a (N + 1) * (f N * Y (N + 1) - f (N + 1) * Y N))
    (ha : 0 ≤ a (N + 1)) (hf0 : 0 ≤ f N) (hf1 : 0 ≤ f (N + 1)) :
    |μ| ≤ a (N + 1) * (f N * |Y (N + 1)| + f (N + 1) * |Y N|) := by
  rw [hμ, abs_mul, abs_of_nonneg ha]
  apply mul_le_mul_of_nonneg_left _ ha
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hf0, abs_of_nonneg hf1]

/-- **Recessive selection with the Airy envelope** (`A:1160`): if `f ≤ 3ψ/2`, `ψ ≤ κ₂ airyWt(X)` at the last two sites,
`X_N ≤ X_{N+1}` and `|Y_N|, |Y_{N+1}| ≤ Y_max`, then `|μ| ≤ 3 κ₂ a_{N+1} Y_max e^{-ξ(X_N)}`.  (Papers:
`|μ_h| ≤ C N^{m+1/3} e^{-ξ_end}`; the extra `N^{1/3}` is the Casoratian `≍ h^{1/3}` of the Bi-normalised `f₂`.) -/
theorem abs_mu_le_airy (a f Y ψ X : ℤ → ℝ) (N : ℤ) (μ κ2 Ymax : ℝ)
    (hμ : μ = a (N + 1) * (f N * Y (N + 1) - f (N + 1) * Y N)) (ha : 0 ≤ a (N + 1))
    (hfN : f N ≤ 3 / 2 * ψ N) (hfN1 : f (N + 1) ≤ 3 / 2 * ψ (N + 1)) (hf0 : 0 ≤ f N) (hf1 : 0 ≤ f (N + 1))
    (hψN : ψ N ≤ κ2 * airyWt (X N)) (hψN1 : ψ (N + 1) ≤ κ2 * airyWt (X (N + 1)))
    (hX : X N ≤ X (N + 1)) (hYN : |Y N| ≤ Ymax) (hYN1 : |Y (N + 1)| ≤ Ymax) (hκ2 : 0 ≤ κ2) :
    |μ| ≤ 3 * κ2 * a (N + 1) * Ymax * Real.exp (-airyXi (X N)) := by
  have h := abs_mu_le a f Y N μ hμ ha hf0 hf1
  have eN : f N ≤ 3 / 2 * κ2 * Real.exp (-airyXi (X N)) := by
    have := airyWt_le_exp_neg (X N)
    nlinarith
  have eN1 : f (N + 1) ≤ 3 / 2 * κ2 * Real.exp (-airyXi (X N)) := by
    have h1 := airyWt_le_exp_neg (X (N + 1))
    have h2 : Real.exp (-airyXi (X (N + 1))) ≤ Real.exp (-airyXi (X N)) :=
      Real.exp_le_exp.2 (by linarith [airyXi_mono hX])
    nlinarith
  have hYm : 0 ≤ Ymax := (abs_nonneg _).trans hYN
  refine h.trans ?_
  have : f N * |Y (N + 1)| + f (N + 1) * |Y N| ≤
      3 / 2 * κ2 * Real.exp (-airyXi (X N)) * Ymax + 3 / 2 * κ2 * Real.exp (-airyXi (X N)) * Ymax := by
    gcongr
  calc a (N + 1) * (f N * |Y (N + 1)| + f (N + 1) * |Y N|)
      ≤ a (N + 1) * (3 / 2 * κ2 * Real.exp (-airyXi (X N)) * Ymax +
          3 / 2 * κ2 * Real.exp (-airyXi (X N)) * Ymax) := mul_le_mul_of_nonneg_left this ha
    _ = _ := by ring

/-! ### Size of the exact second solution -/

/-- The constant of `secondSol_le`. -/
noncomputable def secondConst (c1 ca κ1 κ2 : ℝ) : ℝ :=
  6 * κ2 / (ca * κ1 ^ 2) * (9 / 4) * (Real.exp (8 / 3) * (1 + 3 / (4 * c1)))

/-- **Size of the reduction-of-order solution** (`|f₂| ≤ C M E` of `A:1105`(ii), in the normalisation `W = 1`):
if `ψ/2 ≤ f ≤ 3ψ/2` with `ψ ≍ airyWt` and `a ≥ c_a`, then `0 ≤ f₂ = secondSol a f m ≤ C₂ δ⁻¹ / airyWt(X_k)` on
`Icc m (N+1)`, with `C₂ = secondConst`.  (`1/airyWt = (2+|X|)^{1/4} e^{ξ}`; the paper's sharper `(1+X⁺)^{-1/2}`
saving is not proved here.) -/
theorem secondSol_le {X ψ a f : ℤ → ℝ} {m N : ℤ} {c1 B δ κ1 κ2 ca : ℝ}
    (hL : AiryLattice X m N c1 B δ) (hψ : AiryComparison ψ X m N κ1 κ2) (hca : 0 < ca)
    (ha : ∀ k ∈ Icc (m + 1) (N + 1), ca ≤ a k)
    (hf : ∀ k ∈ Icc m (N + 1), ψ k / 2 ≤ f k ∧ f k ≤ 3 / 2 * ψ k) :
    ∀ k ∈ Icc m (N + 1), 0 ≤ secondSol a f m k ∧
      secondSol a f m k ≤ secondConst c1 ca κ1 κ2 / δ / airyWt (X k) := by
  intro k hk
  rw [mem_Icc] at hk
  have hδ := hL.δ_pos
  have hc := hL.c1_pos
  have hκ1 := hψ.κ1_pos
  have hκ2 : 0 < κ2 := lt_of_lt_of_le hκ1 hψ.κ1_le
  have hmem : ∀ k, m ≤ k → k ≤ N + 1 → k ∈ Icc m (N + 1) := fun k h1 h2 => by
    simp only [mem_Icc]; exact ⟨h1, h2⟩
  have hfpos : ∀ j, m ≤ j → j ≤ N + 1 → 0 < f j := fun j h1 h2 =>
    lt_of_lt_of_le (by have := hψ.pos (hmem j h1 h2); positivity) (hf j (hmem j h1 h2)).1
  have hWk := airyWt_pos (X k)
  have hfk := hfpos k hk.1 hk.2
  -- termwise bound
  have hterm : ∀ i ∈ Ico m k, 0 ≤ f k * (1 / (a (i + 1) * f i * f (i + 1))) ∧
      f k * (1 / (a (i + 1) * f i * f (i + 1))) ≤
        6 * κ2 / (ca * κ1 ^ 2) * (9 / 4) / airyWt (X k) *
          Real.exp (-2 * (airyXi (X k) - airyXi (X (i + 1)))) := by
    intro i hi
    rw [mem_Ico] at hi
    have hfi := hfpos i hi.1 (by omega)
    have hfi1 := hfpos (i + 1) (by omega) (by omega)
    have hai : ca ≤ a (i + 1) := ha (i + 1) (by simp only [mem_Icc]; omega)
    have hapos : 0 < a (i + 1) := lt_of_lt_of_le hca hai
    refine ⟨by positivity, ?_⟩
    have hx := hL.lo i (hmem i hi.1 (by omega))
    have hxy : X i ≤ X (i + 1) := hL.mono hi.1 (by omega) (by omega)
    have hyz : X (i + 1) ≤ X k := hL.mono (by omega) (by omega) hk.2
    have hW := airyWt_sq_le_exp_mul hx hxy hyz
    set E := Real.exp (-2 * (airyXi (X k) - airyXi (X (i + 1)))) with hE
    have hE0 : 0 < E := Real.exp_pos _
    have wi := airyWt_pos (X i)
    have wi1 := airyWt_pos (X (i + 1))
    have lo_i := (hψ.lower i (hmem i hi.1 (by omega)))
    have lo_i1 := (hψ.lower (i + 1) (hmem (i + 1) (by omega) (by omega)))
    have up_k := hψ.upper k (hmem k hk.1 hk.2)
    have hfk' := (hf k (hmem k hk.1 hk.2)).2
    have hfi' := (hf i (hmem i hi.1 (by omega))).1
    have hfi1' := (hf (i + 1) (hmem (i + 1) (by omega) (by omega))).1
    -- f_i f_{i+1} ≥ κ₁² Wt_i Wt_{i+1} / 4
    have hprod : κ1 ^ 2 * (airyWt (X i) * airyWt (X (i + 1))) / 4 ≤ f i * f (i + 1) := by
      have h1 : κ1 * airyWt (X i) / 2 ≤ f i := by linarith
      have h2 : κ1 * airyWt (X (i + 1)) / 2 ≤ f (i + 1) := by linarith
      have := mul_le_mul h1 h2 (by positivity) hfi.le
      nlinarith
    have hfkW : f k ≤ 3 / 2 * (κ2 * airyWt (X k)) := by linarith
    rw [← mul_div_assoc, mul_one, div_le_iff₀ (by positivity)]
    calc f k ≤ 3 / 2 * (κ2 * airyWt (X k)) := hfkW
      _ = (6 * κ2 / (ca * κ1 ^ 2) * (9 / 4) / airyWt (X k) * E) *
          (ca * (κ1 ^ 2 * (airyWt (X i) * airyWt (X (i + 1))) / 4)) *
          (airyWt (X k) ^ 2 / (9 / 4 * E * (airyWt (X i) * airyWt (X (i + 1))))) := by
          field_simp
          ring
      _ ≤ (6 * κ2 / (ca * κ1 ^ 2) * (9 / 4) / airyWt (X k) * E) *
          (ca * (κ1 ^ 2 * (airyWt (X i) * airyWt (X (i + 1))) / 4)) * 1 := by
          gcongr
          rw [div_le_one (by positivity)]
          exact hW
      _ ≤ (6 * κ2 / (ca * κ1 ^ 2) * (9 / 4) / airyWt (X k) * E) * (a (i + 1) * (f i * f (i + 1))) := by
          rw [mul_one]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc ca * (κ1 ^ 2 * (airyWt (X i) * airyWt (X (i + 1))) / 4)
              ≤ a (i + 1) * (κ1 ^ 2 * (airyWt (X i) * airyWt (X (i + 1))) / 4) := by gcongr
            _ ≤ a (i + 1) * (f i * f (i + 1)) := by gcongr
      _ = _ := by ring
  unfold secondSol redSum
  refine ⟨?_, ?_⟩
  · rw [mul_sum]
    exact sum_nonneg fun i hi => (hterm i hi).1
  · rw [mul_sum]
    refine (sum_le_sum fun i hi => (hterm i hi).2).trans ?_
    rw [← mul_sum]
    have hsum : ∑ i ∈ Ico m k, Real.exp (-2 * (airyXi (X k) - airyXi (X (i + 1)))) =
        ∑ p ∈ Ioc m k, Real.exp (-2 * (airyXi (X k) - airyXi (X p))) := by
      refine Finset.sum_nbij' (fun j => j + 1) (fun p => p - 1) ?_ ?_ ?_ ?_ ?_
      · intro j hj; simp only [mem_Ico, mem_Ioc] at hj ⊢; omega
      · intro p hp; simp only [mem_Ico, mem_Ioc] at hp ⊢; omega
      · intro j _; simp
      · intro p _; simp
      · intro j _; rfl
    rw [hsum]
    have hb := expBack_le hL hk.2 (k := k)
    have hC : 0 ≤ 6 * κ2 / (ca * κ1 ^ 2) * (9 / 4) / airyWt (X k) := by positivity
    calc 6 * κ2 / (ca * κ1 ^ 2) * (9 / 4) / airyWt (X k) *
          ∑ p ∈ Ioc m k, Real.exp (-2 * (airyXi (X k) - airyXi (X p)))
        ≤ 6 * κ2 / (ca * κ1 ^ 2) * (9 / 4) / airyWt (X k) *
            (Real.exp (8 / 3) * (1 + 3 / (4 * c1 * δ))) := mul_le_mul_of_nonneg_left hb hC
      _ ≤ 6 * κ2 / (ca * κ1 ^ 2) * (9 / 4) / airyWt (X k) *
            (Real.exp (8 / 3) * (1 + 3 / (4 * c1)) / δ) := by
          apply mul_le_mul_of_nonneg_left _ hC
          have h4 : (1 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith [hL.δ_le_one]
          have : 1 + 3 / (4 * c1 * δ) ≤ (1 + 3 / (4 * c1)) / δ := by
            rw [add_div]
            have : 3 / (4 * c1 * δ) = 3 / (4 * c1) / δ := by field_simp
            rw [this]; linarith
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
      _ = secondConst c1 ca κ1 κ2 / δ / airyWt (X k) := by
          unfold secondConst
          field_simp

/-- Lower bound for the reduction-of-order solution: `1/(a_k f_{k-1}) ≤ f₂_k` for `k ≥ m+1` (only the last term
of `Σ 1/(a f f)` is kept). -/
theorem secondSol_ge (a f : ℤ → ℝ) (m k : ℤ) (hk : m + 1 ≤ k) (ha : ∀ j ∈ Icc (m + 1) k, 0 < a j)
    (hf : ∀ j ∈ Icc m k, 0 < f j) : 1 / (a k * f (k - 1)) ≤ secondSol a f m k := by
  unfold secondSol redSum
  have hkm : k - 1 ∈ Ico m k := by simp only [mem_Ico]; omega
  have hpos : ∀ i ∈ Ico m k, 0 ≤ 1 / (a (i + 1) * f i * f (i + 1)) := by
    intro i hi
    rw [mem_Ico] at hi
    have h1 := hf i (by simp only [mem_Icc]; omega)
    have h2 := hf (i + 1) (by simp only [mem_Icc]; omega)
    have h3 := ha (i + 1) (by simp only [mem_Icc]; omega)
    positivity
  have hsingle := single_le_sum hpos hkm
  have hfk := hf k (by simp only [mem_Icc]; omega)
  have hfk1 := hf (k - 1) (by simp only [mem_Icc]; omega)
  have hak := ha k (by simp only [mem_Icc]; omega)
  have e : f k * (1 / (a (k - 1 + 1) * f (k - 1) * f (k - 1 + 1))) = 1 / (a k * f (k - 1)) := by
    rw [sub_add_cancel]; field_simp
  rw [← e]
  exact mul_le_mul_of_nonneg_left hsingle hfk.le

/-- **Recessive selection with the exact second solution** (W1 `lem:recessive`, est:291-299, in the normalisation `W = 1`;
`A:1160` is `abs_mu_le_airy`, not a special case of this lemma).  Let `Y = κ f + μ f₂` on `Icc m (N+1)`, nodes `m ≤ k₀ ≤ k₁ ≤ N+1`
(`k₁ ≥ m+1`) with `|Y_{k₁}| ≤ |Y_{k₀}|`, `f_{k₁} ≤ f_{k₀}`, `a_{k₁} ≤ A₁` and the growth condition
`2 C₂ δ⁻¹ / airyWt(X_{k₀}) ≤ 1/(A₁ (3κ₂/2) airyWt(X_{k₁-1}))` (i.e. `ξ(X_{k₁-1}) - ξ(X_{k₀}) ≳ log(1/δ) + const`, which
the nodes of W1 `lem:recessive` do not satisfy as stated; they have to be spread further apart).  Then
`|μ| ≤ 4 |κ| f_{k₀} A₁ (3κ₂/2) airyWt(X_{k₁-1})`, and `κ ≠ 0` if `Y_{k₀} ≠ 0`. -/
theorem recessive_selection_airy {X ψ a f f2 Y : ℤ → ℝ} {m N : ℤ} {c1 B δ κ1 κ2 ca A1 κ μ : ℝ}
    (hL : AiryLattice X m N c1 B δ) (hψ : AiryComparison ψ X m N κ1 κ2) (hca : 0 < ca)
    (ha : ∀ k ∈ Icc (m + 1) (N + 1), ca ≤ a k)
    (hf : ∀ k ∈ Icc m (N + 1), ψ k / 2 ≤ f k ∧ f k ≤ 3 / 2 * ψ k) (hf2 : f2 = secondSol a f m)
    (hdec : ∀ k ∈ Icc m (N + 1), Y k = κ * f k + μ * f2 k) {k0 k1 : ℤ} (hk0 : m ≤ k0) (hk01 : k0 ≤ k1)
    (hk1 : m + 1 ≤ k1) (hk1N : k1 ≤ N + 1) (hmono : |Y k1| ≤ |Y k0|) (hfmono : f k1 ≤ f k0)
    (hA1 : a k1 ≤ A1) (hgrow : 2 * (secondConst c1 ca κ1 κ2 / δ / airyWt (X k0)) ≤
      1 / (A1 * (3 / 2 * κ2 * airyWt (X (k1 - 1))))) :
    |μ| ≤ 4 * |κ| * f k0 * (A1 * (3 / 2 * κ2 * airyWt (X (k1 - 1)))) ∧ (Y k0 ≠ 0 → κ ≠ 0) := by
  have hκ1 := hψ.κ1_pos
  have hκ2 : 0 < κ2 := lt_of_lt_of_le hκ1 hψ.κ1_le
  have hmem : ∀ k, m ≤ k → k ≤ N + 1 → k ∈ Icc m (N + 1) := fun k h1 h2 => by
    simp only [mem_Icc]; exact ⟨h1, h2⟩
  have hfpos : ∀ j, m ≤ j → j ≤ N + 1 → 0 < f j := fun j h1 h2 =>
    lt_of_lt_of_le (by have := hψ.pos (hmem j h1 h2); positivity) (hf j (hmem j h1 h2)).1
  have hapos : ∀ j, m + 1 ≤ j → j ≤ N + 1 → 0 < a j := fun j h1 h2 =>
    lt_of_lt_of_le hca (ha j (by simp only [mem_Icc]; exact ⟨h1, h2⟩))
  have hA1pos : 0 < A1 := lt_of_lt_of_le (hapos k1 hk1 hk1N) hA1
  have hW1 := airyWt_pos (X (k1 - 1))
  set L := 1 / (A1 * (3 / 2 * κ2 * airyWt (X (k1 - 1)))) with hL'
  have hLpos : 0 < L := by rw [hL']; positivity
  -- bounds on f₂ at the two nodes
  have hup := (secondSol_le hL hψ hca ha hf k0 (hmem k0 hk0 (by omega))).2
  have hlow : L ≤ secondSol a f m k1 := by
    have h1 := secondSol_ge a f m k1 hk1 (fun j hj => by rw [mem_Icc] at hj; exact hapos j hj.1 (by omega))
      (fun j hj => by rw [mem_Icc] at hj; exact hfpos j hj.1 (by omega))
    refine le_trans ?_ h1
    rw [hL']
    apply one_div_le_one_div_of_le (by
      have := hfpos (k1 - 1) (by omega) (by omega)
      have := hapos k1 hk1 hk1N
      positivity)
    have hfk := (hf (k1 - 1) (hmem _ (by omega) (by omega))).2
    have hup1 := hψ.upper (k1 - 1) (hmem _ (by omega) (by omega))
    have hfpos1 := hfpos (k1 - 1) (by omega) (by omega)
    calc a k1 * f (k1 - 1) ≤ A1 * f (k1 - 1) := by gcongr
      _ ≤ A1 * (3 / 2 * κ2 * airyWt (X (k1 - 1))) := by
          gcongr
          linarith
  have hf20 : secondSol a f m k0 ≤ L / 2 := by linarith
  have hf2_0 : 0 ≤ secondSol a f m k0 :=
    (secondSol_le hL hψ hca ha hf k0 (hmem k0 hk0 (by omega))).1
  -- the selection inequality
  have h0 := hdec k0 (hmem k0 hk0 (by omega))
  have h1 := hdec k1 (hmem k1 (by omega) hk1N)
  rw [← hf2] at hlow hf2_0 hf20
  have hfp0 := hfpos k0 hk0 (by omega)
  have hfp1 := hfpos k1 (by omega) hk1N
  have e1 : |μ| * f2 k1 ≤ |Y k1| + |κ| * f k1 := by
    have : μ * f2 k1 = Y k1 - κ * f k1 := by rw [h1]; ring
    have h2 : 0 ≤ f2 k1 := by linarith
    calc |μ| * f2 k1 = |μ * f2 k1| := by rw [abs_mul, abs_of_nonneg h2]
      _ = |Y k1 - κ * f k1| := by rw [this]
      _ ≤ |Y k1| + |κ * f k1| := abs_sub _ _
      _ = _ := by rw [abs_mul, abs_of_pos hfp1]
  have e0 : |Y k0| ≤ |κ| * f k0 + |μ| * f2 k0 := by
    rw [h0]; refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos hfp0, abs_of_nonneg hf2_0]
  have hsel : |μ| * (f2 k1 - f2 k0) ≤ 2 * |κ| * f k0 := by
    nlinarith [abs_nonneg κ]
  have hμ : |μ| * (L / 2) ≤ 2 * |κ| * f k0 := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg μ)) hsel
    linarith
  have hbound : |μ| ≤ 4 * |κ| * f k0 * (A1 * (3 / 2 * κ2 * airyWt (X (k1 - 1)))) := by
    have hLinv : A1 * (3 / 2 * κ2 * airyWt (X (k1 - 1))) = 1 / L := by
      rw [hL']; field_simp
    rw [hLinv, mul_one_div, le_div_iff₀ hLpos]
    nlinarith
  refine ⟨hbound, ?_⟩
  intro hY hκ
  apply hY
  have : |μ| ≤ 0 := by rw [hκ] at hbound; simpa using hbound
  have hμ0 : μ = 0 := abs_nonpos_iff.1 this
  rw [h0, hκ, hμ0]; ring

/-- **Packaged recessive theorem** (`lem:airy2-recessive` + `A:1160`; the interface for the window lemma).
With the hypotheses of `recessive_airy`, the exact recessive solution `f` and its reduction-of-order partner
`f₂ = secondSol a f m` (Casoratian `≡ 1`) have: `f` as in `recessive_airy`; `0 ≤ f₂ ≤ C₂ δ⁻¹ / airyWt(X)`; and every solution
`Y` of the rows with `|Y_N|, |Y_{N+1}| ≤ Y_max` is `κ f + μ f₂` on `Icc m (N+1)` with
`|μ| ≤ 3 κ₂ a_{N+1} Y_max e^{-ξ(X_N)}`. -/
theorem recessive_airy_selection (c1 B ca κ1 κ2 C0 : ℝ) (hca : 0 < ca) (hC0 : 0 ≤ C0) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (X ψ a c : ℤ → ℝ) (m N : ℤ) (δ : ℝ), m ≤ N → δ ≤ δ0 →
        AiryLattice X m N c1 B δ → AiryComparison ψ X m N κ1 κ2 →
        (∀ k ∈ Icc (m + 1) (N + 1), ca ≤ a k) →
        (∀ i ∈ Icc (m + 1) N, |jac a c ψ i| ≤ C0 * δ ^ 6 * ψ i) →
        ∃ f : ℤ → ℝ, (∀ k ∈ Icc (m + 1) N, jac a c f k = 0) ∧ f N = ψ N ∧ f (N + 1) = ψ (N + 1) ∧
          (∀ k ∈ Icc m (N + 1), |f k - ψ k| ≤ C * δ ^ 3 * ψ k) ∧
          (∀ k ∈ Icc m (N + 1), ψ k / 2 ≤ f k ∧ f k ≤ 3 / 2 * ψ k) ∧
          (∀ k ∈ Icc m N, |(f k - ψ k) - (f (k + 1) - ψ (k + 1))| ≤
            C * δ ^ 5 * ψ k + C * δ ^ 3 * |ψ k - ψ (k + 1)|) ∧
          (∀ k ∈ Icc (m + 1) N, jac a c (secondSol a f m) k = 0) ∧
          (∀ k ∈ Icc m N, cas a f (secondSol a f m) k = 1) ∧
          (∀ k ∈ Icc m (N + 1), 0 ≤ secondSol a f m k ∧
            secondSol a f m k ≤ secondConst c1 ca κ1 κ2 / δ / airyWt (X k)) ∧
          (∀ (Y : ℤ → ℝ) (Ymax : ℝ), (∀ k ∈ Icc (m + 1) N, jac a c Y k = 0) →
            |Y N| ≤ Ymax → |Y (N + 1)| ≤ Ymax →
            ∃ κ μ : ℝ, (∀ k ∈ Icc m (N + 1), Y k = κ * f k + μ * secondSol a f m k) ∧
              |μ| ≤ 3 * κ2 * a (N + 1) * Ymax * Real.exp (-airyXi (X N))) := by
  obtain ⟨δ0, hδ0, C, hC, H⟩ := recessive_airy c1 B ca κ1 κ2 C0 hca hC0
  refine ⟨δ0, hδ0, C, hC, ?_⟩
  intro X ψ a c m N δ hmN hδ hL hψ ha hdef
  obtain ⟨f, hrow, hfN, hfN1, h1, h2, h3⟩ := H X ψ a c m N δ hmN hδ hL hψ ha hdef
  have hapos : ∀ k ∈ Icc (m + 1) (N + 1), 0 < a k := fun k hk => lt_of_lt_of_le hca (ha k hk)
  have hfpos : ∀ k ∈ Icc m (N + 1), 0 < f k := fun k hk =>
    lt_of_lt_of_le (by have := hψ.pos hk; positivity) (h2 k hk).1
  have hmemN : N ∈ Icc m (N + 1) := by simp only [mem_Icc]; omega
  have hmemN1 : N + 1 ∈ Icc m (N + 1) := by simp only [mem_Icc]; omega
  refine ⟨f, hrow, hfN, hfN1, h1, h2, h3, ?_⟩
  obtain ⟨hf2row, hcas, -⟩ := physical_decomposition a c f (fun _ => 0) m N hmN hapos hfpos hrow
    (fun k _ => by simp [jac])
  refine ⟨hf2row, hcas, secondSol_le hL hψ hca ha h2, ?_⟩
  intro Y Ymax hY hYN hYN1
  obtain ⟨-, -, κ, μ, hdec, hμ⟩ := physical_decomposition a c f Y m N hmN hapos hfpos hrow hY
  refine ⟨κ, μ, hdec, ?_⟩
  have hgap := hL.gap N (by simp only [mem_Icc]; omega)
  have hXN : X N ≤ X (N + 1) := by have := mul_pos hL.c1_pos hL.δ_pos; linarith
  exact abs_mu_le_airy a f Y ψ X N μ κ2 Ymax hμ (hapos (N + 1) (by simp only [mem_Icc]; omega)).le
    (h2 N hmemN).2 (h2 (N + 1) hmemN1).2
    (hfpos N hmemN).le (hfpos (N + 1) hmemN1).le (hψ.upper N hmemN) (hψ.upper (N + 1) hmemN1) hXN hYN hYN1
    (lt_of_lt_of_le hψ.κ1_pos hψ.κ1_le).le

/-- info: 'FormalResearch.Special.physical_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.physical_decomposition

/-- info: 'FormalResearch.Special.abs_mu_le_airy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.abs_mu_le_airy

/-- info: 'FormalResearch.Special.secondSol_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.secondSol_le

/-- info: 'FormalResearch.Special.recessive_selection_airy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.recessive_selection_airy

/-- info: 'FormalResearch.Special.recessive_airy_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.recessive_airy_selection

/-- info: 'FormalResearch.Special.secondSol_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.secondSol_ge

/-- info: 'FormalResearch.Special.abs_mu_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.abs_mu_le

end FormalResearch.Special
