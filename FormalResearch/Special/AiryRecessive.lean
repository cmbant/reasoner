module

public import FormalResearch.Special.AiryRecessiveKernel
public import FormalResearch.Special.DiscreteJacobiExtras

/-!
# The recessive Airy solution of a Jacobi chain (P3 `lem:airy2-recessive`(i), abstract form)

Source: Weyl/P3 appendices `lem:airy2-recessive`(i) (`A:1105-1124`) and the same step in W1 `app:airy` (`est:255-282`).
**No `Bi`, no Olver `M/E`**: the envelope is the explicit weight `airyWt` (`AiryWt`); the second solution, selection and the
`μ` bound (`A:1155-1160`, W1 `lem:recessive`) are in `AiryRecessiveSelection`.

Setting: `AiryLattice X m N c₁ B δ` (sites `Icc m (N+1)`, `δ = h^{1/3}`), `AiryComparison ψ X m N κ₁ κ₂`
(`κ₁ airyWt ≤ ψ ≤ κ₂ airyWt`: the papers' `ψ = g Ai(X)` with `g ≍ 1`), `a ≥ c_a > 0` on `Icc (m+1) (N+1)` and the
**hypothesis `hdef`** `|jac a c ψ_i| ≤ C₀ δ⁶ ψ_i` on the rows `Icc (m+1) N` (the `O(h²)` relative parametrix defect of
`A:1105`, supplied by the parametrix module; **not proved here**).

Main results (all **proved**; constants explicit, non-optimal):

* `recessive_abstract` (Airy-free): if the Volterra row sums are `≤ q ≤ 1/4` and the flux sums
  `Σ_{i>k} ψ_i|jac ψ_i|/(a_{k+1}ψ_kψ_{k+1}) ≤ Fl`, then there is an exact solution `f` of `jac a c f = 0` on the rows
  `Icc (m+1) N` with `f = ψ` at the last two sites, `|f - ψ| ≤ 2q ψ`, `ψ/2 ≤ f ≤ 3ψ/2` and the **Lipschitz-level estimate**
  `|(f-ψ)_k - (f-ψ)_{k+1}| ≤ 2 Fl ψ_k + 2q |ψ_k - ψ_{k+1}|` (the input the Grönwall window lemma
  `jacobi_difference_bound` needs at the top two sites).
* `recessive_airy` (**`lem:airy2-recessive`(i)**): for fixed `(c₁, B, c_a, κ₁, κ₂, C₀)` there are `δ₀, C` such that for every
  `δ ≤ δ₀` the exact solution `f` satisfies `|f_k - ψ_k| ≤ C δ³ ψ_k` (`δ³ = h`) on all of `Icc m (N+1)` and
  `|(f-ψ)_k - (f-ψ)_{k+1}| ≤ C δ⁵ ψ_k + C δ³ |ψ_k - ψ_{k+1}|`.  The second term is `≤ C' h δ ψ_k` as soon as
  `|ψ_k - ψ_{k+1}| ≤ Λ δ ψ_k` (true at bounded `X` for `ψ = g Ai`; false for large `X`, where `ψ` varies by the factor
  `e^{-δ√X}` per step); the first term is of the better order `h δ²`.
* The second solution, `|μ|` bound, recessive selection and the packaged theorem are in `AiryRecessiveSelection`.

Numerics (mpmath 30 digits, model chain `a = 1`, `c = 2cosh√t`, `ψ = g Ai`): see `AiryRecessiveKernel`;
on `X ∈ [-1,6]` the recessive solution differs from `ψ` by `0.0154 N^{-4/3}` relative, and
`|(f-ψ)_k-(f-ψ)_{k+1}|/(hδψ_k) ≤ 0.003` at `X ≤ 1` (`N = 10³ … 10⁵`).

**Not formalised:** `hdef` itself, `ψ ≍ airyWt` for `g Ai`, and the oscillatory side `X < -1` (window lemma: `AiryWindow*`).
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- The reduction-of-order flux equals the weighted defect sum:
`D_k = Σ_{i ∈ (k,N]} ψ_i jac(ψ)_i (1 + σ_i)` for a solution `y = ψ(1+σ)` with `σ_N = σ_{N+1} = 0`. -/
theorem flux_formula (a c ψ σ y : ℤ → ℝ) (m N : ℤ) (hrow : ∀ k ∈ Icc (m + 1) N, jac a c y k = 0)
    (hy : ∀ k ∈ Icc m (N + 1), y k = ψ k * (1 + σ k)) (hσN : σ N = 0) (hσN1 : σ (N + 1) = 0) :
    ∀ k, m ≤ k → k ≤ N →
      redD a ψ σ k = ∑ i ∈ Ioc k N, ψ i * jac a c ψ i * (1 + σ i) := by
  apply int_down_induction (P := fun k => redD a ψ σ k = ∑ i ∈ Ioc k N, ψ i * jac a c ψ i * (1 + σ i))
  · simp [redD, hσN, hσN1]
  · intro k hmk hkN hk
    have hid := reduction_identity a c ψ σ y k
      (hy (k - 1) (by simp only [mem_Icc]; omega)) (hy k (by simp only [mem_Icc]; omega))
      (hy (k + 1) (by simp only [mem_Icc]; omega))
    rw [hrow k (by simp only [mem_Icc]; omega)] at hid
    have hI : Ioc (k - 1) N = insert k (Ioc k N) := by
      ext i; simp only [mem_Ioc, mem_insert]; omega
    rw [hI, Finset.sum_insert (by simp), ← hk]
    simp only [mul_zero] at hid
    linarith

/-- **Abstract recessive theorem** (`lem:airy2-recessive`(i), kernel bound ⇒ conclusion; Airy-free).
Let `m ≤ N`, `ψ > 0` on `Icc m (N+1)`, `a > 0` on `Icc (m+1) (N+1)`, the Volterra row sums `≤ q ≤ 1/4` and the flux sums
`≤ Fl`.  Then there is an exact solution `f` of the rows `Icc (m+1) N` with `f = ψ` at `N, N+1` such that
`|f - ψ| ≤ 2q ψ`, `ψ/2 ≤ f ≤ 3ψ/2`, and `|(f-ψ)_k - (f-ψ)_{k+1}| ≤ 2 Fl ψ_k + 2 q |ψ_k - ψ_{k+1}|`. -/
theorem recessive_abstract (a c ψ : ℤ → ℝ) (m N : ℤ) (hmN : m ≤ N) (q Fl : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 4)
    (hψ : ∀ k ∈ Icc m (N + 1), 0 < ψ k) (ha : ∀ k ∈ Icc (m + 1) (N + 1), 0 < a k)
    (hK : ∀ k ∈ Icc m N, ∑ i ∈ Ioc k N, |volterraK a c ψ k i| ≤ q)
    (hFl : ∀ k ∈ Icc m N, ∑ i ∈ Ioc k N, ψ i * |jac a c ψ i| / (a (k + 1) * ψ k * ψ (k + 1)) ≤ Fl) :
    ∃ f : ℤ → ℝ, (∀ k ∈ Icc (m + 1) N, jac a c f k = 0) ∧ f N = ψ N ∧ f (N + 1) = ψ (N + 1) ∧
      (∀ k ∈ Icc m (N + 1), |f k - ψ k| ≤ 2 * q * ψ k) ∧
      (∀ k ∈ Icc m (N + 1), ψ k / 2 ≤ f k ∧ f k ≤ 3 / 2 * ψ k) ∧
      (∀ k ∈ Icc m N, |(f k - ψ k) - (f (k + 1) - ψ (k + 1))| ≤
        2 * Fl * ψ k + 2 * q * |ψ k - ψ (k + 1)|) := by
  have hne : ∀ k ∈ Icc (m + 1) N, a k ≠ 0 := fun k hk =>
    (ha k (by rw [mem_Icc] at hk ⊢; omega)).ne'
  obtain ⟨y, hrow, hyN, hyN1⟩ := exists_final_solution_hom a c (m + 1) N (ψ N) (ψ (N + 1)) hne
  set σ : ℤ → ℝ := fun k => y k / ψ k - 1 with hσdef
  have hψne : ∀ k ∈ Icc m (N + 1), ψ k ≠ 0 := fun k hk => (hψ k hk).ne'
  have hy : ∀ k ∈ Icc m (N + 1), y k = ψ k * (1 + σ k) := by
    intro k hk
    have := hψne k hk
    simp only [hσdef]; field_simp; ring
  have hσN : σ N = 0 := by
    have := hψne N (by simp only [mem_Icc]; omega)
    simp only [hσdef, hyN]; field_simp; ring
  have hσN1 : σ (N + 1) = 0 := by
    have := hψne (N + 1) (by simp only [mem_Icc]; omega)
    simp only [hσdef, hyN1]; field_simp; ring
  have hne' : ∀ k ∈ Icc (m + 1) (N + 1), a k ≠ 0 := fun k hk => (ha k hk).ne'
  have hbd := reduction_of_order_bound a c ψ σ y m N q hq0 (by linarith) hψne hne' hrow hy hσN hσN1 hK
  have hq2 : q / (1 - q) ≤ 2 * q := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hσ : ∀ k ∈ Icc m (N + 1), |σ k| ≤ 2 * q := fun k hk => (hbd k hk).1.trans hq2
  have hFl0 : 0 ≤ Fl := by
    have := hFl N (by simp only [mem_Icc]; omega)
    rw [Ioc_self] at this
    simpa using this
  refine ⟨y, hrow, hyN, hyN1, ?_, ?_, ?_⟩
  · intro k hk
    have := (hbd k hk).2
    rw [abs_of_pos (hψ k hk)] at this
    exact this.trans (mul_le_mul_of_nonneg_right hq2 (hψ k hk).le)
  · intro k hk
    have h1 := hσ k hk
    have h2 := (abs_le.1 h1)
    have hp := hψ k hk
    rw [hy k hk]
    constructor <;> nlinarith [h2.1, h2.2]
  · intro k hk
    rw [mem_Icc] at hk
    have hk0 : k ∈ Icc m (N + 1) := by simp only [mem_Icc]; omega
    have hk1 : k + 1 ∈ Icc m (N + 1) := by simp only [mem_Icc]; omega
    have hψk := hψ k hk0
    have hψk1 := hψ (k + 1) hk1
    have hak : 0 < a (k + 1) := ha (k + 1) (by simp only [mem_Icc]; omega)
    have hden : 0 < a (k + 1) * ψ k * ψ (k + 1) := by positivity
    -- the flux identity
    have hflux := flux_formula a c ψ σ y m N hrow hy hσN hσN1 k hk.1 hk.2
    have e : σ (k + 1) - σ k =
        (∑ i ∈ Ioc k N, ψ i * jac a c ψ i * (1 + σ i)) / (a (k + 1) * ψ k * ψ (k + 1)) := by
      rw [← hflux]; unfold redD; field_simp
    have hσd : |σ (k + 1) - σ k| ≤ 3 / 2 * Fl := by
      rw [e, abs_div, abs_of_pos hden, div_le_iff₀ hden]
      have h1 : |∑ i ∈ Ioc k N, ψ i * jac a c ψ i * (1 + σ i)| ≤
          ∑ i ∈ Ioc k N, 3 / 2 * (ψ i * |jac a c ψ i|) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
        rw [mem_Ioc] at hi
        have hi' : i ∈ Icc m (N + 1) := by simp only [mem_Icc]; omega
        have := hσ i hi'
        have hpsi := hψ i hi'
        rw [abs_mul, abs_mul, abs_of_pos hpsi]
        have h3 : |1 + σ i| ≤ 3 / 2 := by
          rw [abs_le] at this ⊢; constructor <;> linarith [this.1, this.2]
        nlinarith [abs_nonneg (jac a c ψ i), mul_nonneg hpsi.le (abs_nonneg (jac a c ψ i)),
          mul_le_mul_of_nonneg_left h3 (mul_nonneg hpsi.le (abs_nonneg (jac a c ψ i)))]
      refine h1.trans ?_
      rw [← mul_sum]
      have h2 := hFl k (by simp only [mem_Icc]; omega)
      rw [← sum_div, div_le_iff₀ hden] at h2
      nlinarith
    have hek : (y k - ψ k) - (y (k + 1) - ψ (k + 1)) =
        ψ k * (σ k - σ (k + 1)) + (ψ k - ψ (k + 1)) * σ (k + 1) := by
      rw [hy k hk0, hy (k + 1) hk1]; ring
    rw [hek]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_sub_comm (σ k)]
    have h5 := hσ (k + 1) hk1
    have h6 := mul_le_mul_of_nonneg_left hσd hψk.le
    have h7 := mul_le_mul_of_nonneg_left h5 (abs_nonneg (ψ k - ψ (k + 1)))
    rw [abs_of_pos hψk]
    nlinarith

/-- **`lem:airy2-recessive`(i)** (`A:1105`), without `Bi`.  For fixed lattice and comparison constants
`(c₁, B, c_a, κ₁, κ₂, C₀)` there are `δ₀, C > 0` such that for every window with `δ ≤ δ₀`, every `a ≥ c_a`, and every `ψ`
with `κ₁ airyWt ≤ ψ ≤ κ₂ airyWt` and relative defect `|jac a c ψ_i| ≤ C₀ δ⁶ ψ_i` (rows `Icc (m+1) N`), the exact solution `f`
of `jac a c f = 0` with `f = ψ` at `N, N+1` satisfies, with `δ³ = h`,
* `|f_k - ψ_k| ≤ C δ³ ψ_k` and `ψ_k/2 ≤ f_k ≤ 3ψ_k/2` for `k ∈ [m, N+1]`;
* **Lipschitz level**: `|(f-ψ)_k - (f-ψ)_{k+1}| ≤ C δ⁵ ψ_k + C δ³ |ψ_k - ψ_{k+1}|` for `k ∈ [m, N]`. -/
theorem recessive_airy (c1 B ca κ1 κ2 C0 : ℝ) (hca : 0 < ca) (hC0 : 0 ≤ C0) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (X ψ a c : ℤ → ℝ) (m N : ℤ) (δ : ℝ), m ≤ N → δ ≤ δ0 →
        AiryLattice X m N c1 B δ → AiryComparison ψ X m N κ1 κ2 →
        (∀ k ∈ Icc (m + 1) (N + 1), ca ≤ a k) →
        (∀ i ∈ Icc (m + 1) N, |jac a c ψ i| ≤ C0 * δ ^ 6 * ψ i) →
        ∃ f : ℤ → ℝ, (∀ k ∈ Icc (m + 1) N, jac a c f k = 0) ∧ f N = ψ N ∧ f (N + 1) = ψ (N + 1) ∧
          (∀ k ∈ Icc m (N + 1), |f k - ψ k| ≤ C * δ ^ 3 * ψ k) ∧
          (∀ k ∈ Icc m (N + 1), ψ k / 2 ≤ f k ∧ f k ≤ 3 / 2 * ψ k) ∧
          (∀ k ∈ Icc m N, |(f k - ψ k) - (f (k + 1) - ψ (k + 1))| ≤
            C * δ ^ 5 * ψ k + C * δ ^ 3 * |ψ k - ψ (k + 1)|) := by
  by_cases hdeg : 0 < c1 ∧ 0 ≤ B ∧ 0 < κ1 ∧ κ1 ≤ κ2
  swap
  · -- degenerate parameters: the hypotheses `AiryLattice`/`AiryComparison` are contradictory
    refine ⟨1, one_pos, 1, one_pos, ?_⟩
    intro X ψ a c m N δ _ _ hL hψ
    exact absurd ⟨hL.c1_pos, hL.B_nonneg, hψ.κ1_pos, hψ.κ1_le⟩ hdeg
  obtain ⟨hc1, hB, hκ1, hκ12⟩ := hdeg
  set Q := kernelConst c1 B ca κ1 κ2 C0 with hQ
  set Φ := fluxConst c1 ca κ1 κ2 C0 with hΦ
  have hQ0 : 0 ≤ Q := by
    have := expTailConst_nonneg hc1 hB
    have hκ2 : 0 < κ2 := lt_of_lt_of_le hκ1 hκ12
    rw [hQ]; unfold kernelConst; positivity
  have hΦ0 : 0 ≤ Φ := by
    have hκ2 : 0 < κ2 := lt_of_lt_of_le hκ1 hκ12
    rw [hΦ]; unfold fluxConst; positivity
  refine ⟨min 1 (1 / (4 * (Q + 1))), lt_min one_pos (by positivity), 2 * (Q + Φ) + 1, by positivity, ?_⟩
  intro X ψ a c m N δ hmN hδ hL hψ ha hdef
  have hδ0 := hL.δ_pos
  have hδ1 := hL.δ_le_one
  have hq : Q * δ ^ 3 ≤ 1 / 4 := by
    have h1 : δ ≤ 1 / (4 * (Q + 1)) := hδ.trans (min_le_right _ _)
    have h2 : δ ^ 3 ≤ δ := by nlinarith [pow_le_one₀ hδ0.le hδ1 (n := 2)]
    calc Q * δ ^ 3 ≤ Q * δ := by gcongr
      _ ≤ Q * (1 / (4 * (Q + 1))) := by gcongr
      _ ≤ 1 / 4 := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  have hK := volterraK_row_sum_le hL hψ hca ha hC0 hdef
  have hF := flux_bound_le hL hψ hca ha hC0 hdef
  obtain ⟨f, hrow, hfN, hfN1, hf1, hf2, hf3⟩ := recessive_abstract a c ψ m N hmN (Q * δ ^ 3) (Φ * δ ^ 5)
    (by positivity) hq (fun k hk => hψ.pos hk)
    (fun k hk => lt_of_lt_of_le hca (ha k hk)) hK hF
  refine ⟨f, hrow, hfN, hfN1, ?_, hf2, ?_⟩
  · intro k hk
    refine (hf1 k hk).trans ?_
    have := (hψ.pos hk).le
    have h3 : 0 ≤ δ ^ 3 := by positivity
    nlinarith [mul_nonneg h3 this, mul_nonneg hΦ0 h3]
  · intro k hk
    refine (hf3 k hk).trans ?_
    have hk0 : k ∈ Icc m (N + 1) := by rw [mem_Icc] at hk ⊢; omega
    have := (hψ.pos hk0).le
    have h5 : 0 ≤ δ ^ 5 := by positivity
    have h3 : 0 ≤ δ ^ 3 := by positivity
    have h6 := abs_nonneg (ψ k - ψ (k + 1))
    nlinarith [mul_nonneg h5 this, mul_nonneg h3 h6, mul_nonneg hQ0 (mul_nonneg h3 h6),
      mul_nonneg hΦ0 (mul_nonneg h5 this)]

/-- info: 'FormalResearch.Special.recessive_airy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.recessive_airy

/-- info: 'FormalResearch.Special.recessive_abstract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.recessive_abstract

/-- info: 'FormalResearch.Special.flux_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.flux_formula

end FormalResearch.Special
