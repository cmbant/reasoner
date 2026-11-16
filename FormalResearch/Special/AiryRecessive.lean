module

public import FormalResearch.Special.AiryRecessiveKernel
public import FormalResearch.Special.DiscreteJacobiCalculusComparison
public import FormalResearch.Special.DiscreteJacobiExtras

/-!
# The recessive Airy solution of a Jacobi chain (P3 `lem:airy2-recessive`, W1 `lem:recessive`, abstract form)

Source: Weyl/P3 appendices `lem:airy2-recessive`(i)(ii) and `prop:airy2-exact` (`A:1105-1135`), the recessive selection of
the proof of `thm:general-rank-airy`(ii) (`A:1155-1160`), and W1 `app:airy`, `lem:recessive` (`est:285-345`).
**No `Bi`, no Olver `M/E`**: the second solution is the exact reduction-of-order solution `f₂ = f Σ 1/(a f f)`
with Casoratian `≡ 1` (`DiscreteJacobiCalculus.secondSol`), and the envelope is the explicit weight `airyWt`.

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
* `physical_decomposition` / `abs_mu_le` (**`A:1160`, recessive selection**): for any solution `Y` of the rows,
  `Y = κ f + μ f₂` on `Icc m (N+1)` with the exact `μ = a_{N+1}(f_N Y_{N+1} - f_{N+1} Y_N)` and
  `|μ| ≤ 3 κ₂ a_{N+1} (max|Y_N|,|Y_{N+1}|) e^{-ξ(X_N)}`.  (The papers' `μ_h` multiplies the Bi-type `f₂^{paper}` with Casoratian
  `≍ h^{1/3}`, whence `N^{m+1/3}` in `A:1160`; here `W = 1`, and `f₂ ≈ h^{-1/3} f₂^{paper}`.)

Numerics (mpmath 30 digits, model chain `a = 1`, `c = 2cosh√t`, `ψ = g Ai`): see `AiryRecessiveKernel`;
on `X ∈ [-1,6]` the recessive solution differs from `ψ` by `0.0154 N^{-4/3}` relative, and
`|(f-ψ)_k-(f-ψ)_{k+1}|/(hδψ_k) ≤ 0.003` at `X ≤ 1` (`N = 10³ … 10⁵`).

**Not formalised:** `hdef` itself, `ψ ≍ airyWt` for `g Ai`, `|f₂| ≤ C δ^{-1} e^{ξ}` on the window (the backward
exponential sums), the Bi-comparison `f₂ ≈ Bi` and the Casoratian `|W| ≥ c h^{1/3}` of `A:1105`(ii) (replaced by `W = 1`),
the oscillatory side `X < -1` (window lemma, M6).
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

/-- info: 'FormalResearch.Special.recessive_airy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.recessive_airy

/-- info: 'FormalResearch.Special.physical_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.physical_decomposition

/-- info: 'FormalResearch.Special.abs_mu_le_airy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.abs_mu_le_airy

/-- info: 'FormalResearch.Special.secondSol_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.secondSol_le

/-- info: 'FormalResearch.Special.recessive_airy_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.recessive_airy_selection

/-- info: 'FormalResearch.Special.recessive_abstract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.recessive_abstract

end FormalResearch.Special
