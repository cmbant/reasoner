module

public import FormalResearch.Special.AiryRecessiveSelection
public import FormalResearch.Special.DiscreteJacobiExtrasGronwall

/-!
# The bounded oscillatory window: Grönwall march of the recessive Airy solution (part 1: window lemmas)

Plan M6 of the discrete-to-Airy programme (`P3` appendices `A:1155-1183`, W1 `est:285-345`, `EC:95-113`): the exact
recessive solution `f` of `AiryRecessive` (on the forbidden/turn side `X ≥ -1`) is continued **downward** through the
oscillatory window `X ∈ [-A₀, -1]` by the exact recurrence, and compared with the parametrix `ψ` there by the scaled
two-vector discrete Grönwall bound of `DiscreteJacobiExtrasGronwall` (no positivity of `ψ` and no `Bi` on the window).
This file contains the Airy-light building blocks; the two output theorems (`discrete_airy_window`, the version for
the physical solution) are in `AiryWindowMain`.

Notation (as in `AiryRecessive`): sites `J ≤ m ≤ N`, the top window `Icc m (N+1)` is an `AiryLattice` (`X ≥ -1`), the
oscillatory window is `Icc J m` (`X_J ≥ -A₀`, spacings `≥ c₁ δ`, `X_m ≤ Z`, so `m - J ≤ (A₀+Z)/(c₁ δ)`), `δ = h^{1/3}`.

Statements (all **proved**):

* `window_count`: `(m - J) · c₁ δ ≤ X_m - X_J` (number of lattice steps of the window);
* `extend_below`: an exact solution on the rows `Icc (m+1) N` is continued, as an exact solution, to the rows
  `Icc (J+1) N` (when `a ≠ 0`), without changing its values on `Icc m (N+1)`;
* `window_hom_bound`: **homogeneous Grönwall march**: an exact solution `G` of the rows `Ioc J m` has
  `|G k| ≤ (|G m| + |G m - G (m+1)|/δ) · exp (L S / c₁)` on `Icc J m` (`L = 1 + 2 (Sg+Qq)/c_a`, `S ≥ X_m - X_J`);
* `window_from_top`: the **inhomogeneous march**: from the sites `m, m+1`, where `f - ψ` is `O(δ³ W)` in the scaled
  sense (the output of `recessive_airy`), to `Icc J m`, with the parametrix defect `|jac ψ| ≤ C₀ δ⁶ W` on the rows
  `Ioc J m`: `|f_k - ψ_k| ≤ windowConst · δ³ W` (`windowConst = (C₅ (2+Λ) + 2 S C₀/(c₁ c_a)) exp (L S/c₁)`).

**Algebra of the exponents** (the point of the plan).  With `ρ = C₀ δ⁶ W` and `n = m - J ≤ S/(c₁ δ)` steps, the
inhomogeneous term of the Grönwall bound is `2 n ρ/(δ c_a) ≤ 2 S C₀ δ⁴ W/(c₁ c_a)` (`δ⁴ = h^{4/3}`), which is
dominated by the initial term `|d_m| + |d_m - d_{m+1}|/δ = O(δ³ W) = O(h W)` coming from `recessive_airy`
(`|d_m| ≤ C₅ δ³ ψ_m`; Lipschitz level `|d_m - d_{m+1}|/δ ≤ C₅ (δ⁴ + Λ δ³) W` if `|ψ_m - ψ_{m+1}| ≤ Λ δ W`).  The
amplification factor is `exp (L δ n) ≤ exp (L S/c₁)`, `L = 1 + 2 (Sg + Qq)/c_a`.  On the Airy window `Sg ≈ A₀`
(`c - a_k - a_{k+1} = O(h^{2/3} |X|)`), so the factor is `e^{O(A₀ (A₀+Z))}`: harmless for a statement quantified over
`A₀`, but far from the truth (numerics below).

**Numerics** (mpmath 40 digits, scripts and log `num_m6.py`, `num_m6b.py`, `num_m6.log` in `/home/user/scratch/m6_numerics/`, not committed; model chain `a = 1`,
`c = 2cosh√t`, `ψ = g(t) Ai(X)`, `t = δ² X`, `g = (t/sinh²√t)^{1/4}`, `X_k = kδ`, exact solution from the Dirichlet
end `X = 14` with `f = ψ` at the last two sites, `N = 10³ … 10⁶`): the hypotheses of the Grönwall step hold with
`Qq = 0` and `Sg = sup_window |2cosh√t - 2|/δ² ≤ A₀` (`1.9967, 4.979, 9.917` for `A₀ = 2, 5, 10` at `N = 10³`); the
relative defect is `|jac ψ| ≤ 0.00418 δ⁶ sup|ψ|` (the `1/240` of the paper); the actual error on `X ∈ [-A₀,-1]` is
`max |f - ψ| ≤ 0.0163 · N^{-4/3} · sup|ψ|` (normalised by `sup|ψ| = 0.536`; absolute `0.0087 N^{-4/3}`) (`err/h = 1.6·10⁻³, 7.5·10⁻⁴, 3.5·10⁻⁴, 1.6·10⁻⁴` for `N = 10³ … 10⁶`), **the same
for `A₀ = 2, 5, 10`** (no growth in `A₀`); profile `|f-ψ|/h^{4/3} = 0.0083, 0.0061, 0.0044, 0.0003, 0.0048` at
`X = -1,-2,-4,-7,-10`.  The Grönwall bound is about `10⁷⁹ · h` at `A₀ = 10` with the *measured* initial data (exponent `L δ n ≈ 190`);
the constant `windowConst` of `AiryWindowMain` is itself about `10⁵` larger: proved, but pessimistic by `e^{190}` and by
the order `h^{1/3}`.  Because `δ₀` of `recessive_airy` (inherited from M5) is about `10⁻²` to `3·10⁻³` on the model chain,
the theorem is asymptotic (`N ≳ 10⁶`), not a statement about small `N`.

**Not formalised** here: the parametrix defect `hdef` on the window (supplied by `AiryParametrixUniform*` and the wiring
layer `DiscreteAiryLimit*`; see `AiryWindowMain`), the Hahn/Racah coefficient hypotheses (supplied by `dal_window_hyp`
and `hr_perturb`, `DiscreteAiryLimit*`), a sharper Grönwall norm (adapted to the Prüfer amplitude `|X|^{-1/4}`, which would replace `e^{O(A₀²)}` by a power;
the abstract chain lemma `window_from_top_sharp`, `AiryWindowSharp`, has the sharper constant `exp(3V/2)` but is not yet
applied to `discrete_airy_window`); the oscillatory side beyond a bounded window is `DiscreteAiryOsc*` (amplitude-weighted march).
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **Lattice count.**  If the gaps are `≥ c₁ δ` on `Ico J m` then `(m - J) · (c₁ δ) ≤ X_m - X_J`. -/
lemma window_count {X : ℤ → ℝ} {J m : ℤ} {c1 δ : ℝ} (hJm : J ≤ m)
    (hgap : ∀ k ∈ Ico J m, c1 * δ ≤ X (k + 1) - X k) :
    ((m - J : ℤ) : ℝ) * (c1 * δ) ≤ X m - X J := by
  have key : ∀ n : ℕ, J + n ≤ m → (n : ℝ) * (c1 * δ) ≤ X (J + n) - X J := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have h1 := ih (by omega)
      have h2 := hgap (J + n) (by simp only [mem_Ico]; omega)
      have e : J + ((n + 1 : ℕ) : ℤ) = J + n + 1 := by push_cast; ring
      rw [e]; push_cast; linarith
  have := key (m - J).toNat (by omega)
  have e : J + ((m - J).toNat : ℤ) = m := by omega
  rw [e] at this
  have e2 : (((m - J).toNat : ℕ) : ℝ) = ((m - J : ℤ) : ℝ) := by
    have : (((m - J).toNat : ℕ) : ℤ) = m - J := by omega
    exact_mod_cast this
  rwa [e2] at this

/-- **Continuation below the top window.**  If `f` solves the rows `Icc (m+1) N` and `a ≠ 0` on `Icc (J+1) (N+1)`,
there is `F` with the rows `Icc (J+1) N` exact and `F = f` on `Icc m (N+1)` (the same exact solution, continued
downward by the recurrence `a_k F_{k-1} = c_k F_k - a_{k+1} F_{k+1}`). -/
theorem extend_below (a c f : ℤ → ℝ) (J m N : ℤ) (hJm : J ≤ m) (hmN : m ≤ N)
    (ha : ∀ k ∈ Icc (J + 1) (N + 1), a k ≠ 0) (hrow : ∀ k ∈ Icc (m + 1) N, jac a c f k = 0) :
    ∃ F : ℤ → ℝ, (∀ k ∈ Icc (J + 1) N, jac a c F k = 0) ∧ ∀ k ∈ Icc m (N + 1), F k = f k := by
  obtain ⟨F, hF, hFN, hFN1⟩ := exists_final_solution_hom a c (J + 1) N (f N) (f (N + 1))
    (fun k hk => ha k (by rw [mem_Icc] at hk ⊢; omega))
  refine ⟨F, hF, ?_⟩
  rcases lt_or_eq_of_le hmN with hlt | heq
  · have := eq_of_final_values a c F f (fun _ => 0) (m + 1) N (by omega)
      (fun k hk => by rw [hF k (by rw [mem_Icc] at hk ⊢; omega)])
      (fun k hk => hrow k hk) (fun k hk => ha k (by rw [mem_Icc] at hk ⊢; omega)) hFN hFN1
    intro k hk
    exact this k (by rw [mem_Icc] at hk ⊢; omega)
  · subst heq
    intro k hk
    rw [mem_Icc] at hk
    rcases (by omega : k = m ∨ k = m + 1) with h | h
    · rw [h]; exact hFN
    · rw [h]; exact hFN1

/-- The amplification constant `L S / c₁` with `L = 1 + 2 (Sg + Qq)/c_a`. -/
noncomputable def windowExp (c1 ca Sg Qq S : ℝ) : ℝ := Real.exp ((1 + 2 * (Sg + Qq) / ca) * S / c1)

lemma windowExp_pos (c1 ca Sg Qq S : ℝ) : 0 < windowExp c1 ca Sg Qq S := Real.exp_pos _

lemma windowExp_ge_one {c1 ca Sg Qq S : ℝ} (hc1 : 0 < c1) (hca : 0 < ca) (hSg : 0 ≤ Sg) (hQq : 0 ≤ Qq)
    (hS : 0 ≤ S) : 1 ≤ windowExp c1 ca Sg Qq S := by
  unfold windowExp
  apply Real.one_le_exp
  positivity

/-- The Grönwall exponent is controlled by the window length: `exp (L δ n) ≤ windowExp` if `n δ ≤ S/c₁`. -/
lemma exp_le_windowExp {c1 ca Sg Qq S δ n : ℝ} (hca : 0 < ca) (hSg : 0 ≤ Sg) (hQq : 0 ≤ Qq)
    (hn : n * δ ≤ S / c1) :
    Real.exp ((1 + 2 * (Sg + Qq) / ca) * δ * n) ≤ windowExp c1 ca Sg Qq S := by
  unfold windowExp
  apply Real.exp_le_exp.mpr
  have hL : 0 ≤ 1 + 2 * (Sg + Qq) / ca := by positivity
  have e : (1 + 2 * (Sg + Qq) / ca) * S / c1 = (1 + 2 * (Sg + Qq) / ca) * (S / c1) := by ring
  rw [e]
  have : (1 + 2 * (Sg + Qq) / ca) * δ * n = (1 + 2 * (Sg + Qq) / ca) * (n * δ) := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_left hn hL

/-- **Homogeneous Grönwall march through the window.**  `G` solves the rows `Ioc J m`; `a ≥ c_a` on
`Icc (J+1) (m+1)`, `|c - a_k - a_{k+1}| ≤ Sg δ²`, `|a_{k+1} - a_k| ≤ Qq δ²` on `Ioc J m`; `(m - J) δ ≤ S/c₁`.
Then `|G k| ≤ (|G m| + |G m - G (m+1)|/δ) · windowExp` for `k ∈ Icc J m`. -/
theorem window_hom_bound {a c G : ℤ → ℝ} {J m : ℤ} {δ c1 ca Sg Qq S : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hca : 0 < ca) (hSg : 0 ≤ Sg) (hQq : 0 ≤ Qq) (hnδ : ((m - J : ℤ) : ℝ) * δ ≤ S / c1)
    (hrow : ∀ k ∈ Ioc J m, jac a c G k = 0) (ha : ∀ k ∈ Icc (J + 1) (m + 1), ca ≤ a k)
    (hc : ∀ k ∈ Ioc J m, |c k - a k - a (k + 1)| ≤ Sg * δ ^ 2)
    (ha' : ∀ k ∈ Ioc J m, |a (k + 1) - a k| ≤ Qq * δ ^ 2) :
    ∀ k ∈ Icc J m, |G k| ≤ (|G m| + |G m - G (m + 1)| / δ) * windowExp c1 ca Sg Qq S := by
  intro k hk
  have key := jacobi_difference_bound_down a c G (fun _ => 0) δ ca Sg Qq 0 hδ hδ1 hca hSg hQq le_rfl J m
    hrow ha hc ha' (fun k _ => by simp) k hk
  have hnn : 0 ≤ |G m| + |G m - G (m + 1)| / δ := by positivity
  have h1 : |G k| ≤ |G k| + |G k - G (k + 1)| / δ := by
    have : 0 ≤ |G k - G (k + 1)| / δ := by positivity
    linarith
  refine h1.trans (key.trans ?_)
  have e : 2 * ((m - J : ℤ) : ℝ) * 0 / (δ * ca) = 0 := by ring
  rw [e, add_zero]
  exact mul_le_mul_of_nonneg_left (exp_le_windowExp hca hSg hQq hnδ) hnn

/-- The constant of the window bound. -/
noncomputable def windowConst (c1 ca C0 C5 Λ Sg Qq S : ℝ) : ℝ :=
  (C5 * (2 + Λ) + 2 * S * C0 / (c1 * ca)) * windowExp c1 ca Sg Qq S

/-- **Inhomogeneous Grönwall march through the window** (the core of M6).  Let `f` be exact on the rows `Icc (m+1) N`
with `f = ψ` at `N, N+1`, and suppose at the two sites `m, m+1` (the output of `recessive_airy`)
`|f_m - ψ_m| ≤ C₅ δ³ ψ_m`, `|(f-ψ)_m - (f-ψ)_{m+1}| ≤ C₅ δ⁵ ψ_m + C₅ δ³ |ψ_m - ψ_{m+1}|`,
and `0 ≤ ψ_m ≤ W`, `|ψ_m - ψ_{m+1}| ≤ Λ δ W`.  Let the parametrix have the defect `|jac a c ψ_i| ≤ C₀ δ⁶ W` on the rows
`Ioc J m` and the coefficients the near-hyperbolic structure on `Ioc J m`, with `(m - J) δ ≤ S/c₁`.
Then the continuation `F` of `f` (`extend_below`) satisfies `|F_k - ψ_k| ≤ windowConst · δ³ W` for `k ∈ Icc J m`. -/
theorem window_from_top {a c ψ f : ℤ → ℝ} {J m N : ℤ} {δ W c1 ca C0 C5 Λ Sg Qq S : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc1 : 0 < c1) (hca : 0 < ca) (hC0 : 0 ≤ C0) (hC5 : 0 ≤ C5) (hΛ : 0 ≤ Λ)
    (hSg : 0 ≤ Sg) (hQq : 0 ≤ Qq) (hS : 0 ≤ S) (hJm : J ≤ m) (hmN : m ≤ N)
    (hnδ : ((m - J : ℤ) : ℝ) * δ ≤ S / c1)
    (ha : ∀ k ∈ Icc (J + 1) (N + 1), ca ≤ a k)
    (hc : ∀ k ∈ Ioc J m, |c k - a k - a (k + 1)| ≤ Sg * δ ^ 2)
    (ha' : ∀ k ∈ Ioc J m, |a (k + 1) - a k| ≤ Qq * δ ^ 2)
    (hdef : ∀ i ∈ Ioc J m, |jac a c ψ i| ≤ C0 * δ ^ 6 * W)
    (hrow : ∀ k ∈ Icc (m + 1) N, jac a c f k = 0)
    (h1 : |f m - ψ m| ≤ C5 * δ ^ 3 * ψ m)
    (h2 : |(f m - ψ m) - (f (m + 1) - ψ (m + 1))| ≤ C5 * δ ^ 5 * ψ m + C5 * δ ^ 3 * |ψ m - ψ (m + 1)|)
    (hψ0 : 0 ≤ ψ m) (hψW : ψ m ≤ W) (hLip : |ψ m - ψ (m + 1)| ≤ Λ * δ * W) :
    ∃ F : ℤ → ℝ, (∀ k ∈ Icc (J + 1) N, jac a c F k = 0) ∧ (∀ k ∈ Icc m (N + 1), F k = f k) ∧
      ∀ k ∈ Icc J m, |F k - ψ k| ≤ windowConst c1 ca C0 C5 Λ Sg Qq S * δ ^ 3 * W := by
  have hane : ∀ k ∈ Icc (J + 1) (N + 1), a k ≠ 0 := fun k hk => (lt_of_lt_of_le hca (ha k hk)).ne'
  obtain ⟨F, hF, hFf⟩ := extend_below a c f J m N hJm hmN hane hrow
  refine ⟨F, hF, hFf, ?_⟩
  have hW : 0 ≤ W := le_trans hψ0 hψW
  have hρ : 0 ≤ C0 * δ ^ 6 * W := by positivity
  have key := jacobi_solutions_bound_down a c F ψ (fun _ => 0) (jac a c ψ) δ ca Sg Qq (C0 * δ ^ 6 * W) hδ hδ1
    hca hSg hQq hρ J m
    (fun k hk => by
      rw [mem_Ioc] at hk
      exact hF k (by rw [mem_Icc]; omega))
    (fun k _ => rfl)
    (fun k hk => ha k (by rw [mem_Icc] at hk ⊢; omega)) hc ha'
    (fun k hk => by simpa using hdef k hk)
  intro k hk
  refine (key k hk).trans ?_
  -- bounds on the initial data
  have hFm : F m = f m := hFf m (by rw [mem_Icc]; omega)
  have hFm1 : F (m + 1) = f (m + 1) := hFf (m + 1) (by rw [mem_Icc]; omega)
  rw [hFm, hFm1]
  have hδ3 : 0 ≤ δ ^ 3 := by positivity
  have hδ4 : δ ^ 4 ≤ δ ^ 3 := by nlinarith [pow_pos hδ 3]
  have hδ5 : δ ^ 5 ≤ δ ^ 4 := by nlinarith [pow_pos hδ 4]
  -- term 1
  have t1 : |f m - ψ m| ≤ C5 * δ ^ 3 * W := by
    refine h1.trans ?_
    nlinarith [mul_nonneg hC5 hδ3]
  -- term 2
  have t2 : |(f m - ψ m) - (f (m + 1) - ψ (m + 1))| / δ ≤ C5 * (1 + Λ) * δ ^ 3 * W := by
    rw [div_le_iff₀ hδ]
    refine h2.trans ?_
    have a1 : C5 * δ ^ 5 * ψ m ≤ C5 * δ ^ 5 * W := by gcongr
    have a2 : C5 * δ ^ 3 * |ψ m - ψ (m + 1)| ≤ C5 * δ ^ 3 * (Λ * δ * W) := by gcongr
    have a3 : C5 * δ ^ 5 * W ≤ C5 * δ ^ 4 * W * δ := by nlinarith [mul_nonneg hC5 hW]
    have a4 : C5 * δ ^ 4 * W * δ ≤ C5 * δ ^ 3 * W * δ := by
      have := mul_nonneg hC5 hW
      nlinarith [mul_nonneg this (sub_nonneg.2 hδ4), hδ]
    have a5 : C5 * δ ^ 3 * (Λ * δ * W) = C5 * Λ * δ ^ 3 * W * δ := by ring
    nlinarith
  -- term 3
  have t3 : 2 * ((m - J : ℤ) : ℝ) * (C0 * δ ^ 6 * W) / (δ * ca) ≤ 2 * S * C0 / (c1 * ca) * δ ^ 3 * W := by
    have hn : ((m - J : ℤ) : ℝ) ≤ S / (c1 * δ) := by
      rw [le_div_iff₀ (by positivity)]
      calc ((m - J : ℤ) : ℝ) * (c1 * δ) = (((m - J : ℤ) : ℝ) * δ) * c1 := by ring
        _ ≤ S / c1 * c1 := by gcongr
        _ = S := by field_simp
    have hn0 : 0 ≤ ((m - J : ℤ) : ℝ) := by
      have : (0 : ℤ) ≤ m - J := by omega
      exact_mod_cast this
    have e : 2 * ((m - J : ℤ) : ℝ) * (C0 * δ ^ 6 * W) / (δ * ca) =
        ((m - J : ℤ) : ℝ) * (2 * C0 * δ ^ 5 * W / ca) := by field_simp
    rw [e]
    calc ((m - J : ℤ) : ℝ) * (2 * C0 * δ ^ 5 * W / ca) ≤ S / (c1 * δ) * (2 * C0 * δ ^ 5 * W / ca) := by
          gcongr
      _ = 2 * S * C0 / (c1 * ca) * δ ^ 4 * W := by field_simp
      _ ≤ 2 * S * C0 / (c1 * ca) * δ ^ 3 * W := by
          have : 0 ≤ 2 * S * C0 / (c1 * ca) * W := by positivity
          nlinarith
  have hE := windowExp_pos c1 ca Sg Qq S
  have hsum : |f m - ψ m| + |(f m - ψ m) - (f (m + 1) - ψ (m + 1))| / δ +
      2 * ((m - J : ℤ) : ℝ) * (C0 * δ ^ 6 * W) / (δ * ca) ≤
      (C5 * (2 + Λ) + 2 * S * C0 / (c1 * ca)) * δ ^ 3 * W := by nlinarith
  have hexp := exp_le_windowExp (c1 := c1) hca hSg hQq hnδ
  unfold windowConst
  calc _ ≤ ((C5 * (2 + Λ) + 2 * S * C0 / (c1 * ca)) * δ ^ 3 * W) * windowExp c1 ca Sg Qq S := by
        refine mul_le_mul hsum hexp (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

/-- info: 'FormalResearch.Special.extend_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.extend_below

/-- info: 'FormalResearch.Special.window_hom_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.window_hom_bound

/-- info: 'FormalResearch.Special.window_from_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.window_from_top

end FormalResearch.Special
