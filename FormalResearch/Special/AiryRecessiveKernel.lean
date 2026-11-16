module

public import FormalResearch.Special.AiryRecessiveSums
public import FormalResearch.Special.DiscreteJacobiCalculusVolterra

/-!
# The Volterra kernel of the recessive Airy solution: row sums from the parametrix defect

The Airy-specific part of `lem:airy2-recessive`(i) (P3 appendices `A:1105-1124`; the same estimate in W1 `app:airy`,
`est:266-282`), formalised without `Bi` and without Olver's `M/E`.

Setting (all abstract, the parametrix `ψ = g·Ai(h^{-2/3}ζ)` of the papers enters only through the hypotheses):
* a lattice window `X : ℤ → ℝ` on the sites `Icc m (N+1)` with `X ≥ -1`, spacings `≥ c₁ δ`, `X ≤ B δ⁻²`, `δ = h^{1/3}`
  (`AiryLattice`, `AiryRecessiveSums`);
* a Jacobi operator `jac a c` with `a ≥ c_a > 0` on `Icc (m+1) (N+1)`;
* a comparison sequence `ψ` with the **two-sided envelope bound** `κ₁ airyWt(X_k) ≤ ψ_k ≤ κ₂ airyWt(X_k)`
  (`AiryComparison`; the papers' `ψ = g Ai` with `g ≍ 1` and `Ai ≍ (2+X)^{-1/4}e^{-ξ}` on `[-1,∞)`:
  `airyWt/20 ≤ Ai ≤ 6 airyWt`, `AiryWt`);
* the **relative parametrix defect** `|jac a c ψ_i| ≤ C₀ δ⁶ ψ_i` (= `C₀ h² ψ_i`; hypothesis `hdef`, to be supplied by
  the parametrix module, `A:1105`).

Results (all **proved**, explicit constants):
* `volterraK_row_sum_le` : `Σ_{i ∈ (k,N]} |K k i| ≤ Q δ³` (`δ³ = h`), `Q = (9/4)(C₀/c_a)(κ₂/κ₁)² C_G`
  (paper: `‖K‖_∞ ≤ C h`; the steps `|K_{ki}| ≤ C h² Σ_j e^{-2(ξ_i-ξ_{j+1})}` and the sum over `i` and `j`
  are `AiryRecessiveSums.expTail_le`, `expTail_sum_le`);
* `flux_bound_le` : `Σ_{i ∈ (k,N]} ψ_i |jac ψ_i| / (a_{k+1} ψ_k ψ_{k+1}) ≤ Φ δ⁵` with
  `Φ = (9/4)(C₀/c_a)(κ₂/κ₁)² e⁴ (1 + 1/(2c₁))` (the difference `σ_{k+1}-σ_k` of the relative error, used for the
  Lipschitz-level estimate of `AiryRecessive`).

mpmath check (30 digits, scripts and logs `m5_numerics/num1.py`, `num1.log` in the session scratch area): model chain `a = 1`,
`c = 2cosh√t`, `ψ_k = g Ai(X_k)` with `g = (t/sinh²√t)^{1/4}`, `X_k = kδ`, `δ = N^{-1/3}`, Dirichlet end at
`X = 14, 25, 50, 100, 200` (windows up to `0.5 N^{2/3}`), `N = 10³ … 8·10³`: the relative defect is `C₀ = 0.00417 ≈ 1/240`
(`|jac ψ| ≤ C₀ h² ψ`), and `max_k Σ_i |K k i| / h ∈ [3·10⁻⁴, 2.7·10⁻³]`; `Q` above is therefore far from sharp, and `‖K‖ = O(h)`
holds uniformly in the window length.

**Not formalised:** the hypothesis `hdef` itself (parametrix defect `O(h²)`: the module M4), and `ψ ≍ airyWt`
for the actual `ψ = g Ai` (needs `g ≍ 1`, supplied with the parametrix).  The parametrix defect is
`airyParametrix_defect` (`AiryParametrixDefect`), in window form `K h²(1+|X|)³ airyWt` under an assumed amplitude relation:
it gives `hdef` for bounded `|X|` only; the oscillatory side `X < -1` is `discrete_airy_window` (`AiryWindowMain`).
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- Two-sided comparison `κ₁ airyWt(X_k) ≤ ψ_k ≤ κ₂ airyWt(X_k)` on the window `Icc m (N+1)`. -/
structure AiryComparison (ψ X : ℤ → ℝ) (m N : ℤ) (κ1 κ2 : ℝ) : Prop where
  κ1_pos : 0 < κ1
  κ1_le : κ1 ≤ κ2
  lower : ∀ k ∈ Icc m (N + 1), κ1 * airyWt (X k) ≤ ψ k
  upper : ∀ k ∈ Icc m (N + 1), ψ k ≤ κ2 * airyWt (X k)

lemma AiryComparison.pos {ψ X : ℤ → ℝ} {m N : ℤ} {κ1 κ2 : ℝ} (h : AiryComparison ψ X m N κ1 κ2) {k : ℤ}
    (hk : k ∈ Icc m (N + 1)) : 0 < ψ k :=
  lt_of_lt_of_le (mul_pos h.κ1_pos (airyWt_pos _)) (h.lower k hk)

/-- **Kernel term bound.**  For `m ≤ j`, `j + 1 ≤ i ≤ N`:
`ψ_i ψ_i / (a_{j+1} ψ_j ψ_{j+1}) ≤ (9/4)(κ₂/κ₁)²/c_a · e^{-2(ξ_i - ξ_{j+1})}`. -/
theorem kernel_term_le {X ψ a : ℤ → ℝ} {m N : ℤ} {c1 B δ κ1 κ2 ca : ℝ} (hL : AiryLattice X m N c1 B δ)
    (hψ : AiryComparison ψ X m N κ1 κ2) (hca : 0 < ca) (ha : ∀ k ∈ Icc (m + 1) (N + 1), ca ≤ a k)
    {i j : ℤ} (hj : m ≤ j) (hji : j + 1 ≤ i) (hiN : i ≤ N) :
    ψ i * ψ i / (a (j + 1) * ψ j * ψ (j + 1)) ≤
      9 / 4 * (κ2 / κ1) ^ 2 / ca * Real.exp (-2 * (airyXi (X i) - airyXi (X (j + 1)))) := by
  have hmem : ∀ k, m ≤ k → k ≤ N + 1 → k ∈ Icc m (N + 1) := fun k h1 h2 => by simp only [mem_Icc]; exact ⟨h1, h2⟩
  have hj0 := hψ.pos (hmem j hj (by omega))
  have hj1 := hψ.pos (hmem (j + 1) (by omega) (by omega))
  have hi0 := hψ.pos (hmem i (by omega) (by omega))
  have hac : ca ≤ a (j + 1) := ha (j + 1) (by simp only [mem_Icc]; omega)
  have hapos : 0 < a (j + 1) := lt_of_lt_of_le hca hac
  have hx := hL.lo j (hmem j hj (by omega))
  have hxy := hL.gap j (by simp only [mem_Icc]; omega)
  have hxy' : X j ≤ X (j + 1) := by have := mul_pos hL.c1_pos hL.δ_pos; linarith
  have hyz : X (j + 1) ≤ X i := hL.mono (by omega) hji (by omega)
  have hW := airyWt_sq_le_exp_mul hx hxy' hyz
  set E := Real.exp (-2 * (airyXi (X i) - airyXi (X (j + 1)))) with hE
  have hE0 := Real.exp_pos (-2 * (airyXi (X i) - airyXi (X (j + 1))))
  rw [← hE] at hE0
  have wj := airyWt_pos (X j)
  have wj1 := airyWt_pos (X (j + 1))
  have wi := airyWt_pos (X i)
  have l_j := hψ.lower j (hmem j hj (by omega))
  have l_j1 := hψ.lower (j + 1) (hmem (j + 1) (by omega) (by omega))
  have u_i := hψ.upper i (hmem i (by omega) (by omega))
  have hκ := hψ.κ1_pos
  rw [div_le_iff₀ (by positivity)]
  have hpsi_i : ψ i * ψ i ≤ κ2 ^ 2 * airyWt (X i) ^ 2 := by
    have := mul_le_mul u_i u_i hi0.le (by have : 0 < κ2 := lt_of_lt_of_le hκ hψ.κ1_le; positivity)
    nlinarith
  have hprod : κ1 ^ 2 * (airyWt (X j) * airyWt (X (j + 1))) ≤ ψ j * ψ (j + 1) := by
    have := mul_le_mul l_j l_j1 (by positivity) hj0.le
    nlinarith
  calc ψ i * ψ i ≤ κ2 ^ 2 * airyWt (X i) ^ 2 := hpsi_i
    _ ≤ κ2 ^ 2 * (9 / 4 * E * (airyWt (X j) * airyWt (X (j + 1)))) := by gcongr
    _ = 9 / 4 * (κ2 / κ1) ^ 2 / ca * E * (ca * (κ1 ^ 2 * (airyWt (X j) * airyWt (X (j + 1))))) := by
        field_simp
    _ ≤ 9 / 4 * (κ2 / κ1) ^ 2 / ca * E * (a (j + 1) * (ψ j * ψ (j + 1))) := by
        have h1 : ca * (κ1 ^ 2 * (airyWt (X j) * airyWt (X (j + 1)))) ≤
            a (j + 1) * (ψ j * ψ (j + 1)) := by
          calc ca * (κ1 ^ 2 * (airyWt (X j) * airyWt (X (j + 1)))) ≤ a (j + 1) * (κ1 ^ 2 *
                (airyWt (X j) * airyWt (X (j + 1)))) := by gcongr
            _ ≤ a (j + 1) * (ψ j * ψ (j + 1)) := by gcongr
        have hpos : 0 ≤ 9 / 4 * (κ2 / κ1) ^ 2 / ca * E := by positivity
        exact mul_le_mul_of_nonneg_left h1 hpos
    _ = 9 / 4 * (κ2 / κ1) ^ 2 / ca * E * (a (j + 1) * ψ j * ψ (j + 1)) := by ring

/-- Interchange of the two kernel sums. -/
theorem double_swap (F : ℤ → ℤ → ℝ) (k N : ℤ) :
    ∑ i ∈ Ioc k N, ∑ j ∈ Ico k i, F i (j + 1) = ∑ p ∈ Ioc k N, ∑ i ∈ Icc p N, F i p := by
  have inner : ∀ i, ∑ j ∈ Ico k i, F i (j + 1) = ∑ p ∈ Ioc k i, F i p := by
    intro i
    refine Finset.sum_nbij' (fun j => j + 1) (fun p => p - 1) ?_ ?_ ?_ ?_ ?_
    · intro j hj; simp only [mem_Ico, mem_Ioc] at hj ⊢; omega
    · intro p hp; simp only [mem_Ico, mem_Ioc] at hp ⊢; omega
    · intro j _; simp
    · intro p _; simp
    · intro j _; rfl
  simp_rw [inner]
  refine Finset.sum_comm' ?_
  intro i p
  simp only [mem_Ioc, mem_Icc]
  omega

/-- The constant `Q` of `volterraK_row_sum_le`. -/
noncomputable def kernelConst (c1 B ca κ1 κ2 C0 : ℝ) : ℝ :=
  C0 * (9 / 4 * (κ2 / κ1) ^ 2 / ca) * expTailConst c1 B

lemma expTailConst_nonneg {c1 B : ℝ} (hc : 0 < c1) (hB : 0 ≤ B) : 0 ≤ expTailConst c1 B := by
  unfold expTailConst; positivity

/-- **Row sums of the Volterra kernel** (`A:1119-1124`, `‖K‖_∞ ≤ C h`): under the relative defect
`|jac a c ψ_i| ≤ C₀ δ⁶ ψ_i` and the two-sided envelope comparison, `Σ_{i ∈ (k,N]} |K k i| ≤ Q δ³`. -/
theorem volterraK_row_sum_le {X ψ a c : ℤ → ℝ} {m N : ℤ} {c1 B δ κ1 κ2 ca C0 : ℝ}
    (hL : AiryLattice X m N c1 B δ) (hψ : AiryComparison ψ X m N κ1 κ2) (hca : 0 < ca)
    (ha : ∀ k ∈ Icc (m + 1) (N + 1), ca ≤ a k) (hC0 : 0 ≤ C0)
    (hdef : ∀ i ∈ Icc (m + 1) N, |jac a c ψ i| ≤ C0 * δ ^ 6 * ψ i) :
    ∀ k ∈ Icc m N, ∑ i ∈ Ioc k N, |volterraK a c ψ k i| ≤ kernelConst c1 B ca κ1 κ2 C0 * δ ^ 3 := by
  intro k hk
  rw [mem_Icc] at hk
  have hδ := hL.δ_pos
  set Ck := 9 / 4 * (κ2 / κ1) ^ 2 / ca with hCk
  have hCk0 : 0 ≤ Ck := by
    have := hψ.κ1_pos; positivity
  have hmem : ∀ k, m ≤ k → k ≤ N + 1 → k ∈ Icc m (N + 1) := fun k h1 h2 => by
    simp only [mem_Icc]; exact ⟨h1, h2⟩
  -- pointwise bound on a kernel entry
  have hK : ∀ i ∈ Ioc k N, |volterraK a c ψ k i| ≤
      C0 * δ ^ 6 * ∑ j ∈ Ico k i, Ck * Real.exp (-2 * (airyXi (X i) - airyXi (X (j + 1)))) := by
    intro i hi
    rw [mem_Ioc] at hi
    have hψi := hψ.pos (hmem i (by omega) (by omega))
    have hd := hdef i (by simp only [mem_Icc]; omega)
    have hpos : ∀ j ∈ Ico k i, 0 ≤ ψ i / (a (j + 1) * ψ j * ψ (j + 1)) := by
      intro j hj
      rw [mem_Ico] at hj
      have h1 := hψ.pos (hmem j (by omega) (by omega))
      have h2 := hψ.pos (hmem (j + 1) (by omega) (by omega))
      have h3 : 0 < a (j + 1) :=
        lt_of_lt_of_le hca (ha (j + 1) (by simp only [mem_Icc]; omega))
      positivity
    unfold volterraK
    rw [abs_mul, abs_of_nonneg (sum_nonneg hpos)]
    calc |jac a c ψ i| * ∑ j ∈ Ico k i, ψ i / (a (j + 1) * ψ j * ψ (j + 1))
        ≤ (C0 * δ ^ 6 * ψ i) * ∑ j ∈ Ico k i, ψ i / (a (j + 1) * ψ j * ψ (j + 1)) :=
          mul_le_mul_of_nonneg_right hd (sum_nonneg hpos)
      _ = C0 * δ ^ 6 * ∑ j ∈ Ico k i, ψ i * ψ i / (a (j + 1) * ψ j * ψ (j + 1)) := by
          have e : ψ i * ∑ j ∈ Ico k i, ψ i / (a (j + 1) * ψ j * ψ (j + 1)) =
              ∑ j ∈ Ico k i, ψ i * ψ i / (a (j + 1) * ψ j * ψ (j + 1)) := by
            rw [mul_sum]
            refine sum_congr rfl fun j _ => ?_
            ring
          rw [mul_assoc, e]
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine sum_le_sum fun j hj => ?_
          rw [mem_Ico] at hj
          exact kernel_term_le hL hψ hca ha (by omega) (by omega) hi.2
  refine (sum_le_sum hK).trans ?_
  rw [← mul_sum]
  have hsw := double_swap (fun i p => Ck * Real.exp (-2 * (airyXi (X i) - airyXi (X p)))) k N
  have hsw' : ∑ i ∈ Ioc k N, ∑ j ∈ Ico k i, Ck * Real.exp (-2 * (airyXi (X i) - airyXi (X (j + 1)))) =
      Ck * ∑ p ∈ Ioc k N, ∑ i ∈ Icc p N, Real.exp (-2 * (airyXi (X i) - airyXi (X p))) := by
    rw [hsw, mul_sum]
    refine sum_congr rfl fun p _ => ?_
    rw [mul_sum]
  rw [hsw']
  have hsub : ∑ p ∈ Ioc k N, ∑ i ∈ Icc p N, Real.exp (-2 * (airyXi (X i) - airyXi (X p))) ≤
      ∑ p ∈ Icc (m + 1) N, ∑ i ∈ Icc p N, Real.exp (-2 * (airyXi (X i) - airyXi (X p))) := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp; simp only [mem_Ioc, mem_Icc] at hp ⊢; omega
    · intro p _ _
      exact sum_nonneg fun i _ => (Real.exp_pos _).le
  have hG := expTail_sum_le hL
  have hfin : C0 * δ ^ 6 * (Ck * ∑ p ∈ Ioc k N, ∑ i ∈ Icc p N,
      Real.exp (-2 * (airyXi (X i) - airyXi (X p)))) ≤ C0 * δ ^ 6 * (Ck * (expTailConst c1 B / δ ^ 3)) := by
    gcongr
    exact hsub.trans hG
  refine hfin.trans (le_of_eq ?_)
  unfold kernelConst
  rw [hCk]
  field_simp

/-- The constant `Φ` of `flux_bound_le`. -/
noncomputable def fluxConst (c1 ca κ1 κ2 C0 : ℝ) : ℝ :=
  C0 * (9 / 4 * (κ2 / κ1) ^ 2 / ca) * (Real.exp 4 * (1 + 1 / (2 * c1)))

/-- **Flux bound** (the difference `σ_{k+1} − σ_k = D_k / (a_{k+1} ψ_k ψ_{k+1})` of the relative error):
`Σ_{i ∈ (k,N]} ψ_i |jac ψ_i| / (a_{k+1} ψ_k ψ_{k+1}) ≤ Φ δ⁵` for `k ∈ [m,N]`. -/
theorem flux_bound_le {X ψ a c : ℤ → ℝ} {m N : ℤ} {c1 B δ κ1 κ2 ca C0 : ℝ}
    (hL : AiryLattice X m N c1 B δ) (hψ : AiryComparison ψ X m N κ1 κ2) (hca : 0 < ca)
    (ha : ∀ k ∈ Icc (m + 1) (N + 1), ca ≤ a k) (hC0 : 0 ≤ C0)
    (hdef : ∀ i ∈ Icc (m + 1) N, |jac a c ψ i| ≤ C0 * δ ^ 6 * ψ i) :
    ∀ k ∈ Icc m N, ∑ i ∈ Ioc k N, ψ i * |jac a c ψ i| / (a (k + 1) * ψ k * ψ (k + 1)) ≤
      fluxConst c1 ca κ1 κ2 C0 * δ ^ 5 := by
  intro k hk
  rw [mem_Icc] at hk
  have hδ := hL.δ_pos
  have hδ1 := hL.δ_le_one
  have hc := hL.c1_pos
  set Ck := 9 / 4 * (κ2 / κ1) ^ 2 / ca with hCk
  have hCk0 : 0 ≤ Ck := by
    have := hψ.κ1_pos; positivity
  have hmem : ∀ k, m ≤ k → k ≤ N + 1 → k ∈ Icc m (N + 1) := fun k h1 h2 => by
    simp only [mem_Icc]; exact ⟨h1, h2⟩
  have hT : ∀ i ∈ Ioc k N, ψ i * |jac a c ψ i| / (a (k + 1) * ψ k * ψ (k + 1)) ≤
      C0 * δ ^ 6 * Ck * Real.exp (-2 * (airyXi (X i) - airyXi (X (k + 1)))) := by
    intro i hi
    rw [mem_Ioc] at hi
    have hψi := hψ.pos (hmem i (by omega) (by omega))
    have hψk := hψ.pos (hmem k hk.1 (by omega))
    have hψk1 := hψ.pos (hmem (k + 1) (by omega) (by omega))
    have hapos : 0 < a (k + 1) :=
      lt_of_lt_of_le hca (ha (k + 1) (by simp only [mem_Icc]; omega))
    have hd := hdef i (by simp only [mem_Icc]; omega)
    have hkt := kernel_term_le hL hψ hca ha hk.1 (by omega : k + 1 ≤ i) hi.2
    calc ψ i * |jac a c ψ i| / (a (k + 1) * ψ k * ψ (k + 1))
        ≤ ψ i * (C0 * δ ^ 6 * ψ i) / (a (k + 1) * ψ k * ψ (k + 1)) := by
          gcongr
      _ = C0 * δ ^ 6 * (ψ i * ψ i / (a (k + 1) * ψ k * ψ (k + 1))) := by ring
      _ ≤ C0 * δ ^ 6 * (Ck * Real.exp (-2 * (airyXi (X i) - airyXi (X (k + 1))))) := by
          gcongr
      _ = _ := by ring
  refine (sum_le_sum hT).trans ?_
  rw [← mul_sum]
  have hIoc : Ioc k N = Icc (k + 1) N := by ext i; simp only [mem_Ioc, mem_Icc]; omega
  rw [hIoc]
  have hG := expTail_le hL (p := k + 1) (by omega)
  have hs1 : 1 ≤ √(max (X (k + 1)) 1) := Real.one_le_sqrt.2 (le_max_right _ _)
  have h2 : Real.exp 4 * (1 + 1 / (2 * c1 * δ * √(max (X (k + 1)) 1))) ≤
      Real.exp 4 * (1 + 1 / (2 * c1)) / δ := by
    have h3 : 1 / (2 * c1 * δ * √(max (X (k + 1)) 1)) ≤ 1 / (2 * c1 * δ) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [mul_pos hc hδ]
    have h4 : (1 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
    have h5 : Real.exp 4 * (1 + 1 / (2 * c1 * δ)) = Real.exp 4 * (1 + 1 / (2 * c1) / δ) := by
      congr 2; field_simp
    have h6 : Real.exp 4 * (1 + 1 / (2 * c1) / δ) ≤ Real.exp 4 * (1 + 1 / (2 * c1)) / δ := by
      have : 1 + 1 / (2 * c1) / δ ≤ (1 + 1 / (2 * c1)) / δ := by
        rw [add_div]; have : 0 ≤ 1 / (2 * c1) / δ := by positivity
        linarith
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left this (Real.exp_pos 4).le
    have := Real.exp_pos 4
    calc Real.exp 4 * (1 + 1 / (2 * c1 * δ * √(max (X (k + 1)) 1)))
        ≤ Real.exp 4 * (1 + 1 / (2 * c1 * δ)) := by gcongr
      _ ≤ _ := h5 ▸ h6
  have hC : 0 ≤ C0 * δ ^ 6 * Ck := by positivity
  calc C0 * δ ^ 6 * Ck * ∑ i ∈ Icc (k + 1) N, Real.exp (-2 * (airyXi (X i) - airyXi (X (k + 1))))
      ≤ C0 * δ ^ 6 * Ck * (Real.exp 4 * (1 + 1 / (2 * c1)) / δ) :=
        mul_le_mul_of_nonneg_left (hG.trans h2) hC
    _ = _ := by
        unfold fluxConst
        rw [hCk]
        field_simp

/-- info: 'FormalResearch.Special.kernel_term_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kernel_term_le

/-- info: 'FormalResearch.Special.volterraK_row_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.volterraK_row_sum_le

/-- info: 'FormalResearch.Special.flux_bound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.flux_bound_le

end FormalResearch.Special
