module

public import FormalResearch.SignUncertainty.CeCanonicalSide

/-!
# Hermite–Biehler node-square spaces (`lem:airy-node-square`, `ce_airy_lp_proofs.tex`)

Source: `CFT/sign_uncertainty/paper/ce_airy_lp_proofs.tex`, `lem:airy-node-square` (lines 473–533),
and `ce_canonical_iff.tex` (`eq:hb-node-bound`, `eq:hb-node-square-general`).

For strict Hermite–Biehler data `D : ShellHBData` of level `m = D.S.card ≥ 2` with zero enumeration
`t` (`ht : IsHbZeroEnum D.P D.Q t`, `hbNode t n = t_n`), `e = ⌊m/2⌋`, any finite set of real sites
`S : Finset ℝ`, and any finite index set `T : Finset ℕ` (`∀ n ∈ T, 1 ≤ n`, `e + 1 ≤ T.card`):

* `hbNodePolySpace D t S T : Submodule ℝ ℝ[X]`: polynomials `p` of degree `≤ T.card - e - 1`
  vanishing at every `s ∈ S` except nodes of `N = P Ai + Q Ai'` outside `T`.
* `hbNodePolyQuotient D t T p`, `hbNodeTau D t S T` (`τ_T(S)`): the node-space Rayleigh quotient
  and its supremum over nonzero `p ∈ hbNodePolySpace D t S T`.
* `hbNodePolySpace_nonempty_of_card`: whenever `e + 1 + S.card ≤ T.card` (in particular for
  `T_M = {1, …, M}` with `M ≥ e + 1 + S.card`), `hbNodePolySpace D t S T` contains a nonzero
  polynomial.
* `exists_hbNodeTrial`: for every nonzero `p ∈ hbNodePolySpace D t S T`, the entire quotient
  `q_p = N p / ∏_{n ∈ T} (u - t_n)` lies in the full Airy square class `IsAirySquareClass` for `S`
  with Rayleigh quotient `hbNodePolyQuotient D t T p`, and `(u - τ) q_p²` (`τ = hbNodePolyQuotient`)
  is a zero-mass weak witness with strictly positive Laplace transform on `(0, ∞)`.
* `isGreatest_hbNodeTau`, `hbNodeTau_mono`, `hbNodeTau_lt_airyLambdaOf`, `lem_airy_node_square`:
  whenever `hbNodePolySpace D t S T` is nontrivial, `τ_T(S)` is attained, nondecreasing under
  enlargement of `T`, and strictly below `λ(S) = airyLambdaOf S` (proved algebraically from the
  Lagrange-multiplier representation `(eq:airy-square-rep)` and infinitely many poles of `Ai'/Ai`).
* `airy_node_square`: for `S = shellSites D = {t_1, …, t_{m-1}}` and
  `T_0 = {m, …, m + e}`, the constant polynomial `1` gives `λ > τ_N > t_{m+e}` (discharging the
  former `airy_node_square` field of `CeCanonicalInputs`).

**Not formalised here:** the asymptotic truncation rate `0 < λ(S) - τ_{T_M}(S) ≤ C M^{-α_m}`
(`eq:hb-node-truncation`, `ce_airy_lp_proofs.tex` lines 484–490, 534–605), which rests on the
polynomial-HB node/derivative asymptotics `|t_n| ≍ n^{2/3}` and `|N'(t_n)| ≍ |t_n|^{m/2 - 1/4}` of
`gt:1.0p` (3) (not yet in `FormalResearch/Special/`) and is not used by `thm:ce-canonical-iff`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-! ### Node enumeration helpers and positive node weights -/

lemma hbNode_injOn {P Q : ℝ[X]} {t : ℕ → ℝ} (ht : IsHbZeroEnum P Q t) :
    Set.InjOn (hbNode t) {n : ℕ | 1 ≤ n} := by
  intro a ha b hb hab
  unfold hbNode at hab
  have h := ht.1.injective hab
  have ha' : 1 ≤ a := ha
  have hb' : 1 ≤ b := hb
  omega

lemma hbNode_zero_Nf {P Q : ℝ[X]} {t : ℕ → ℝ} (ht : IsHbZeroEnum P Q t) {n : ℕ} :
    at47_Nf P Q (hbNode t n) = 0 :=
  (ht.2 _).2 ⟨n - 1, rfl⟩

lemma hbNode_zero_airyPQN (D : ShellHBData) {t : ℕ → ℝ} (ht : IsHbZeroEnum D.P D.Q t) {n : ℕ} :
    airyPQN D.P D.Q (hbNode t n : ℂ) = 0 :=
  (nodeZero_iff D _).2 (hbNode_zero_Nf ht)

/-- For any finite set `T ⊆ ℕ_{≥ 1}`, the node weights `ω_{n, T}` (`n ∈ T`) are strictly positive. -/
theorem hbNodeWeight_pos_of_mem (D : ShellHBData) {t : ℕ → ℝ} (ht : IsHbZeroEnum D.P D.Q t)
    (hm : 2 ≤ D.S.card) {T : Finset ℕ} (hT1 : ∀ k ∈ T, 1 ≤ k) {n : ℕ} (hn : n ∈ T) :
    0 < hbNodeWeight D.P D.Q t T n := by
  have hQ := D.Q_ne_zero_of_two_le hm
  unfold hbNodeWeight
  have hz : airyPQN D.P D.Q (hbNode t n : ℂ) = 0 := hbNode_zero_airyPQN D ht
  have hD := (airyPQ_zero_weight_pos D.hHB hQ hz).1
  refine div_pos hD (Finset.prod_pos fun k hk => ?_)
  obtain ⟨hkne, hkT⟩ := Finset.mem_erase.1 hk
  have hne : hbNode t n ≠ hbNode t k := fun heq =>
    hkne.symm (hbNode_injOn ht (hT1 n hn) (hT1 k hkT) heq)
  positivity [sub_ne_zero.mpr hne]

/-- Real-axis Hermite–Biehler non-vanishing: `P` and `Q` have no common real zero. -/
lemma hb_real_not_both_zero {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (x : ℝ) :
    P.eval x ≠ 0 ∨ Q.eval x ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨hP, hQ⟩ := h
  have hF0 : airyPQc Q (x : ℂ) + I * airyPQc P (x : ℂ) = 0 := by
    rw [airyPQc_ofReal, airyPQc_ofReal, hP, hQ]
    simp
  have him := hHB (x : ℂ) hF0
  simp at him

private lemma re_sq_of_im_zero {w : ℂ} (hw : w.im = 0) : (w ^ 2).re = w.re ^ 2 := by
  rw [sq, Complex.mul_re, hw, mul_zero, sub_zero, sq]

private lemma im_sq_of_im_zero {w : ℂ} (hw : w.im = 0) : (w ^ 2).im = 0 := by
  rw [sq, Complex.mul_im, hw, mul_zero, zero_mul, add_zero]

/-! ### Polynomial node-square space and finite-dimensional attainment -/

/-- The polynomial space of `eq:hb-node-square-general`: polynomials `p ∈ ℝ[X]` of degree
`≤ T.card - ⌊m/2⌋ - 1` vanishing at every prescribed site `s ∈ S` except nodes of `N` outside `T`. -/
noncomputable def hbNodePolySpace (D : ShellHBData) (t : ℕ → ℝ) (S : Finset ℝ) (T : Finset ℕ) :
    Submodule ℝ ℝ[X] where
  carrier := {p : ℝ[X] | p.natDegree ≤ T.card - D.S.card / 2 - 1 ∧
    ∀ s ∈ S, (at47_Nf D.P D.Q s ≠ 0 ∨ s ∈ T.image (hbNode t)) → p.eval s = 0}
  add_mem' := by
    rintro p q ⟨hp1, hp2⟩ ⟨hq1, hq2⟩
    refine ⟨(Polynomial.natDegree_add_le p q).trans (max_le hp1 hq1), fun s hs hcond => ?_⟩
    rw [Polynomial.eval_add, hp2 s hs hcond, hq2 s hs hcond, add_zero]
  zero_mem' := ⟨by simp, fun _ _ _ => Polynomial.eval_zero⟩
  smul_mem' := by
    rintro c p ⟨hp1, hp2⟩
    refine ⟨(Polynomial.natDegree_smul_le c p).trans hp1, fun s hs hcond => ?_⟩
    rw [Polynomial.eval_smul, hp2 s hs hcond, smul_zero]

/-- Weighted node-square denominator `∑_{n ∈ T} ω_{n, T} p(t_n)²`. -/
noncomputable def hbNodePolyDenom (D : ShellHBData) (t : ℕ → ℝ) (T : Finset ℕ) (p : ℝ[X]) : ℝ :=
  ∑ n ∈ T, hbNodeWeight D.P D.Q t T n * (p.eval (hbNode t n)) ^ 2

/-- Weighted node-square numerator `∑_{n ∈ T} ω_{n, T} t_n p(t_n)²`. -/
noncomputable def hbNodePolyNum (D : ShellHBData) (t : ℕ → ℝ) (T : Finset ℕ) (p : ℝ[X]) : ℝ :=
  ∑ n ∈ T, hbNodeWeight D.P D.Q t T n * hbNode t n * (p.eval (hbNode t n)) ^ 2

/-- Node-space Rayleigh quotient `(∑_{n ∈ T} ω_{n, T} t_n p(t_n)²) / (∑_{n ∈ T} ω_{n, T} p(t_n)²)`. -/
noncomputable def hbNodePolyQuotient (D : ShellHBData) (t : ℕ → ℝ) (T : Finset ℕ) (p : ℝ[X]) : ℝ :=
  hbNodePolyNum D t T p / hbNodePolyDenom D t T p

/-- Maximum node-space threshold `τ_T(S)` (`eq:hb-node-square-general`). -/
noncomputable def hbNodeTau (D : ShellHBData) (t : ℕ → ℝ) (S : Finset ℝ) (T : Finset ℕ) : ℝ :=
  sSup (hbNodePolyQuotient D t T '' {p : ℝ[X] | p ∈ hbNodePolySpace D t S T ∧ p ≠ 0})

lemma hbNodePolyQuotient_one (D : ShellHBData) (t : ℕ → ℝ) (T : Finset ℕ) :
    hbNodePolyQuotient D t T 1 = hbNodeSquareBound D.P D.Q t T := by
  unfold hbNodePolyQuotient hbNodePolyNum hbNodePolyDenom hbNodeSquareBound
  simp

lemma hbNodePolyQuotient_smul (D : ShellHBData) (t : ℕ → ℝ) (T : Finset ℕ)
    {c : ℝ} (hc : c ≠ 0) (p : ℝ[X]) :
    hbNodePolyQuotient D t T (c • p) = hbNodePolyQuotient D t T p := by
  unfold hbNodePolyQuotient hbNodePolyNum hbNodePolyDenom
  have h1 : (∑ n ∈ T, hbNodeWeight D.P D.Q t T n * hbNode t n * ((c • p).eval (hbNode t n)) ^ 2) =
      c ^ 2 * ∑ n ∈ T, hbNodeWeight D.P D.Q t T n * hbNode t n * (p.eval (hbNode t n)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Polynomial.eval_smul, smul_eq_mul]
    ring
  have h2 : (∑ n ∈ T, hbNodeWeight D.P D.Q t T n * ((c • p).eval (hbNode t n)) ^ 2) =
      c ^ 2 * ∑ n ∈ T, hbNodeWeight D.P D.Q t T n * (p.eval (hbNode t n)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Polynomial.eval_smul, smul_eq_mul]
    ring
  rw [h1, h2, mul_div_mul_left _ _ (pow_ne_zero 2 hc)]

/-- A nonzero polynomial of degree `< |T|` cannot vanish at all `|T|` distinct nodes `{t_n : n ∈ T}`,
so `hbNodePolyDenom D t T p > 0`. -/
lemma hbNodePolyDenom_pos (D : ShellHBData) {t : ℕ → ℝ} (ht : IsHbZeroEnum D.P D.Q t)
    (hm : 2 ≤ D.S.card) {S : Finset ℝ} {T : Finset ℕ} (hT1 : ∀ n ∈ T, 1 ≤ n)
    (hTcard : D.S.card / 2 + 1 ≤ T.card) {p : ℝ[X]} (hp : p ∈ hbNodePolySpace D t S T)
    (hp0 : p ≠ 0) :
    0 < hbNodePolyDenom D t T p := by
  have hex : ∃ n ∈ T, p.eval (hbNode t n) ≠ 0 := by
    by_contra hall
    push Not at hall
    have hsub : T.image (hbNode t) ⊆ p.roots.toFinset := by
      intro x hx
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hx
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot]
      exact hall n hn
    have hcard_img : (T.image (hbNode t)).card = T.card :=
      Finset.card_image_of_injOn fun a ha b hb hab =>
        hbNode_injOn ht (hT1 a ha) (hT1 b hb) hab
    have hle1 : T.card ≤ p.roots.toFinset.card := hcard_img ▸ Finset.card_le_card hsub
    have hle2 : p.roots.toFinset.card ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    have hle3 : Multiset.card p.roots ≤ p.natDegree := Polynomial.card_roots' p
    have hdeg : p.natDegree ≤ T.card - D.S.card / 2 - 1 := hp.1
    omega
  obtain ⟨n₀, hn₀, hpn₀⟩ := hex
  unfold hbNodePolyDenom
  refine Finset.sum_pos' (fun n hn => ?_) ⟨n₀, hn₀, ?_⟩
  · exact mul_nonneg (hbNodeWeight_pos_of_mem D ht hm hT1 hn).le (sq_nonneg _)
  · exact mul_pos (hbNodeWeight_pos_of_mem D ht hm hT1 hn₀) (sq_pos_of_ne_zero hpn₀)

/-- Whenever `T.card ≥ ⌊m/2⌋ + 1 + S.card`, `hbNodePolySpace D t S T` contains a nonzero polynomial
(explicitly `∏ (X - C s)` over the active site conditions). -/
theorem hbNodePolySpace_nonempty_of_card (D : ShellHBData) (t : ℕ → ℝ) (S : Finset ℝ) (T : Finset ℕ)
    (hcard : D.S.card / 2 + 1 + S.card ≤ T.card) :
    ∃ p ∈ hbNodePolySpace D t S T, p ≠ 0 := by
  classical
  let S' : Finset ℝ := S.filter fun s => at47_Nf D.P D.Q s ≠ 0 ∨ s ∈ T.image (hbNode t)
  let p : ℝ[X] := ∏ s ∈ S', (Polynomial.X - Polynomial.C s)
  have hmonic : p.Monic := Polynomial.monic_prod_of_monic _ _ fun s _ => Polynomial.monic_X_sub_C s
  refine ⟨p, ⟨?_, ?_⟩, hmonic.ne_zero⟩
  · have hdeg : p.natDegree = S'.card := by
      rw [Polynomial.natDegree_prod_of_monic _ _ fun s _ => Polynomial.monic_X_sub_C s]
      simp
    have hle : S'.card ≤ S.card := Finset.card_filter_le _ _
    omega
  · intro s hs hcond
    have hs' : s ∈ S' := Finset.mem_filter.2 ⟨hs, hcond⟩
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero hs' (by simp)

/-- Coefficient map `(Fin (d + 1) → ℝ) → ℝ[X]` for polynomials of `natDegree ≤ d`. -/
private noncomputable def hbPolyOfCoeff (d : ℕ) (c : Fin (d + 1) → ℝ) : ℝ[X] :=
  ∑ i : Fin (d + 1), Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)

private lemma hbPolyOfCoeff_natDegree_le (d : ℕ) (c : Fin (d + 1) → ℝ) :
    (hbPolyOfCoeff d c).natDegree ≤ d := by
  unfold hbPolyOfCoeff
  refine Finset.induction_on Finset.univ (by simp) fun i s _ ih => ?_
  rw [Finset.sum_insert ‹i ∉ s›]
  exact (Polynomial.natDegree_add_le _ _).trans
    (max_le ((Polynomial.natDegree_C_mul_X_pow_le (c i) (i : ℕ)).trans (Nat.lt_succ_iff.mp i.2)) ih)

private lemma hbPolyOfCoeff_coeff (d : ℕ) (c : Fin (d + 1) → ℝ) (i : Fin (d + 1)) :
    (hbPolyOfCoeff d c).coeff (i : ℕ) = c i := by
  unfold hbPolyOfCoeff
  have hsum : (∑ j : Fin (d + 1), Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)).coeff (i : ℕ) =
      ∑ j : Fin (d + 1), (Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)).coeff (i : ℕ) :=
    map_sum (Polynomial.lcoeff ℝ (i : ℕ)) _ Finset.univ
  rw [hsum]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hji (Fin.ext h.symm)
    simp [hne]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma hbPolyOfCoeff_eq_self {d : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ d) :
    hbPolyOfCoeff d (fun i => p.coeff (i : ℕ)) = p := by
  unfold hbPolyOfCoeff
  rw [Fin.sum_univ_eq_sum_range (fun k => Polynomial.C (p.coeff k) * Polynomial.X ^ k) (d + 1)]
  simp_rw [Polynomial.C_mul_X_pow_eq_monomial]
  exact (Polynomial.as_sum_range' p (d + 1) (Nat.lt_succ_of_le hp)).symm

private lemma hbPolyOfCoeff_smul (d : ℕ) (a : ℝ) (c : Fin (d + 1) → ℝ) :
    hbPolyOfCoeff d (a • c) = a • hbPolyOfCoeff d c := by
  unfold hbPolyOfCoeff
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, Polynomial.C_mul, Algebra.smul_def, Polynomial.algebraMap_eq,
    mul_assoc]

private lemma continuous_eval_hbPolyOfCoeff (d : ℕ) (x : ℝ) :
    Continuous (fun c : Fin (d + 1) → ℝ => (hbPolyOfCoeff d c).eval x) := by
  have heq : (fun c : Fin (d + 1) → ℝ => (hbPolyOfCoeff d c).eval x) =
      fun c => ∑ i : Fin (d + 1), c i * x ^ (i : ℕ) := by
    ext c
    unfold hbPolyOfCoeff
    rw [← Polynomial.coe_evalRingHom, map_sum]
    simp
  rw [heq]
  fun_prop

/-- Finite-dimensional attainment of `τ_T(S) = hbNodeTau D t S T` whenever `hbNodePolySpace` is
nonzero. -/
theorem isGreatest_hbNodeTau (D : ShellHBData) {t : ℕ → ℝ} (ht : IsHbZeroEnum D.P D.Q t)
    (hm : 2 ≤ D.S.card) {S : Finset ℝ} {T : Finset ℕ} (hT1 : ∀ n ∈ T, 1 ≤ n)
    (hTcard : D.S.card / 2 + 1 ≤ T.card)
    (hne : ∃ p ∈ hbNodePolySpace D t S T, p ≠ 0) :
    IsGreatest (hbNodePolyQuotient D t T '' {p : ℝ[X] | p ∈ hbNodePolySpace D t S T ∧ p ≠ 0})
      (hbNodeTau D t S T) := by
  classical
  let d : ℕ := T.card - D.S.card / 2 - 1
  let S' : Finset ℝ := S.filter fun s => at47_Nf D.P D.Q s ≠ 0 ∨ s ∈ T.image (hbNode t)
  let K_set : Set (Fin (d + 1) → ℝ) :=
    Metric.sphere 0 1 ∩ {c | ∀ s ∈ S', (hbPolyOfCoeff d c).eval s = 0}
  have hmem_space : ∀ c : Fin (d + 1) → ℝ,
      (∀ s ∈ S', (hbPolyOfCoeff d c).eval s = 0) ↔ hbPolyOfCoeff d c ∈ hbNodePolySpace D t S T := by
    intro c
    constructor
    · intro hc
      exact ⟨hbPolyOfCoeff_natDegree_le d c, fun s hs hcond => hc s (Finset.mem_filter.2 ⟨hs, hcond⟩)⟩
    · intro hc s hs'
      exact hc.2 s (Finset.mem_filter.1 hs').1 (Finset.mem_filter.1 hs').2
  have hclosed_vanish : IsClosed {c : Fin (d + 1) → ℝ | ∀ s ∈ S', (hbPolyOfCoeff d c).eval s = 0} := by
    have heq : {c : Fin (d + 1) → ℝ | ∀ s ∈ S', (hbPolyOfCoeff d c).eval s = 0} =
        ⋂ s ∈ S', {c | (hbPolyOfCoeff d c).eval s = 0} := by
      ext c; simp
    rw [heq]
    exact isClosed_biInter fun s _ => isClosed_eq (continuous_eval_hbPolyOfCoeff d s) continuous_const
  have hK_compact : IsCompact K_set :=
    (isCompact_sphere (0 : Fin (d + 1) → ℝ) 1).inter_right hclosed_vanish
  have hK_nz : ∀ c ∈ K_set, hbPolyOfCoeff d c ≠ 0 := by
    intro c hc h0
    have hc_norm : ‖c‖ = 1 := by simpa using hc.1
    have hc0 : c = 0 := by
      ext i
      rw [← hbPolyOfCoeff_coeff d c i, h0, Polynomial.coeff_zero, Pi.zero_apply]
    simp [hc0] at hc_norm
  -- Every nonzero `p ∈ hbNodePolySpace` normalizes into `K_set` with the same quotient.
  have hnorm_in_K : ∀ p : ℝ[X], p ∈ hbNodePolySpace D t S T → p ≠ 0 →
      ∃ c ∈ K_set, hbNodePolyQuotient D t T (hbPolyOfCoeff d c) = hbNodePolyQuotient D t T p := by
    intro p hp hp0
    let c₀ : Fin (d + 1) → ℝ := fun i => p.coeff (i : ℕ)
    have hc₀_eq : hbPolyOfCoeff d c₀ = p := hbPolyOfCoeff_eq_self hp.1
    have hc₀_ne : c₀ ≠ 0 := by
      intro h0
      apply hp0
      rw [← hc₀_eq, h0]
      unfold hbPolyOfCoeff
      simp
    have hnorm_pos : 0 < ‖c₀‖ := norm_pos_iff.mpr hc₀_ne
    let c : Fin (d + 1) → ℝ := ‖c₀‖⁻¹ • c₀
    have hc_poly : hbPolyOfCoeff d c = ‖c₀‖⁻¹ • p := by
      rw [hbPolyOfCoeff_smul, hc₀_eq]
    refine ⟨c, ⟨?_, ?_⟩, ?_⟩
    · simp only [mem_sphere_zero_iff_norm, c, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hnorm_pos), inv_mul_cancel₀ hnorm_pos.ne']
    · show ∀ s ∈ S', (hbPolyOfCoeff d c).eval s = 0
      rw [hmem_space, hc_poly]
      exact Submodule.smul_mem _ _ hp
    · rw [hc_poly, hbNodePolyQuotient_smul D t T (inv_ne_zero hnorm_pos.ne') p]
  obtain ⟨p₀, hp₀, hp₀0⟩ := hne
  obtain ⟨c₀, hc₀K, -⟩ := hnorm_in_K p₀ hp₀ hp₀0
  have hcont_num : Continuous (fun c : Fin (d + 1) → ℝ => hbNodePolyNum D t T (hbPolyOfCoeff d c)) := by
    unfold hbNodePolyNum
    have h := fun n : ℕ => continuous_eval_hbPolyOfCoeff d (hbNode t n)
    fun_prop
  have hcont_den : Continuous (fun c : Fin (d + 1) → ℝ => hbNodePolyDenom D t T (hbPolyOfCoeff d c)) := by
    unfold hbNodePolyDenom
    have h := fun n : ℕ => continuous_eval_hbPolyOfCoeff d (hbNode t n)
    fun_prop
  have hcont_quot : ContinuousOn (fun c : Fin (d + 1) → ℝ =>
      hbNodePolyQuotient D t T (hbPolyOfCoeff d c)) K_set := by
    refine hcont_num.continuousOn.div hcont_den.continuousOn fun c hc => ?_
    exact (hbNodePolyDenom_pos D ht hm hT1 hTcard ((hmem_space c).mp hc.2) (hK_nz c hc)).ne'
  obtain ⟨c_max, hc_maxK, hc_max⟩ := hK_compact.exists_isMaxOn ⟨c₀, hc₀K⟩ hcont_quot
  have himg_eq : (hbNodePolyQuotient D t T '' {p : ℝ[X] | p ∈ hbNodePolySpace D t S T ∧ p ≠ 0}) =
      (fun c => hbNodePolyQuotient D t T (hbPolyOfCoeff d c)) '' K_set := by
    ext r
    constructor
    · rintro ⟨p, ⟨hp, hp0⟩, rfl⟩
      obtain ⟨c, hcK, hceq⟩ := hnorm_in_K p hp hp0
      exact ⟨c, hcK, hceq⟩
    · rintro ⟨c, hcK, rfl⟩
      exact ⟨hbPolyOfCoeff d c, ⟨(hmem_space c).mp hcK.2, hK_nz c hcK⟩, rfl⟩
  have hgreat : IsGreatest (hbNodePolyQuotient D t T ''
      {p : ℝ[X] | p ∈ hbNodePolySpace D t S T ∧ p ≠ 0})
      (hbNodePolyQuotient D t T (hbPolyOfCoeff d c_max)) := by
    rw [himg_eq]
    exact ⟨⟨c_max, hc_maxK, rfl⟩, by rintro _ ⟨c, hcK, rfl⟩; exact hc_max hcK⟩
  have hsup : hbNodeTau D t S T = hbNodePolyQuotient D t T (hbPolyOfCoeff d c_max) :=
    hgreat.csSup_eq
  rwa [hsup]

/-! ### Entire node-square trial `q_p = N p / ∏_{n ∈ T} (u - t_n)` and HB quadrature -/

/-- Iterative division of an entire function vanishing on a finite real set `A` by `at47_pr A`. -/
private lemma exists_entire_div_finset (A : Finset ℝ) :
    ∀ {φ : ℂ → ℂ}, Differentiable ℂ φ → (∀ a ∈ A, φ (a : ℂ) = 0) →
    ∃ q : ℂ → ℂ, Differentiable ℂ q ∧ ∀ z : ℂ, q z * at47_pr A z = φ z := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    intro φ hφ _
    exact ⟨φ, hφ, fun z => by simp [at47_pr]⟩
  | insert a A ha ih =>
    intro φ hφ hz
    let q₁ : ℂ → ℂ := dslope φ (a : ℂ)
    have hq₁d : Differentiable ℂ q₁ := EntireDiv.differentiable_dslope_entire hφ (a : ℂ)
    have hq₁eq : ∀ z : ℂ, q₁ z * (z - (a : ℂ)) = φ z := by
      intro z
      have h := sub_smul_dslope φ (a : ℂ) z
      rw [hz a (Finset.mem_insert_self _ _), sub_zero, smul_eq_mul] at h
      dsimp [q₁]; linear_combination h
    have hq₁z : ∀ b ∈ A, q₁ (b : ℂ) = 0 := by
      intro b hb
      have h := hq₁eq (b : ℂ)
      rw [hz b (Finset.mem_insert_of_mem hb)] at h
      have hne : (b : ℂ) - (a : ℂ) ≠ 0 := by
        intro h0
        exact ha ((Complex.ofReal_injective (sub_eq_zero.mp h0)) ▸ hb)
      exact (mul_eq_zero.mp h).resolve_right hne
    obtain ⟨q, hqd, hqeq⟩ := ih hq₁d hq₁z
    refine ⟨q, hqd, fun z => ?_⟩
    unfold at47_pr at hqeq ⊢
    rw [Finset.prod_insert ha]
    calc q z * ((z - (a : ℂ)) * ∏ t ∈ A, (z - (t : ℂ)))
        = (q z * ∏ t ∈ A, (z - (t : ℂ))) * (z - (a : ℂ)) := by ring
      _ = q₁ z * (z - (a : ℂ)) := by rw [hqeq z]
      _ = φ z := hq₁eq z

/-- Derivative of `at47_pr A` at `a ∈ A` equals `∏_{b ∈ A.erase a} (a - b)`. -/
private lemma deriv_at47_pr_of_mem {A : Finset ℝ} {a : ℝ} (ha : a ∈ A) :
    deriv (at47_pr A) (a : ℂ) = ∏ b ∈ A.erase a, ((a : ℂ) - (b : ℂ)) := by
  classical
  have hfac : at47_pr A = (fun z : ℂ => z - (a : ℂ)) * at47_pr (A.erase a) := by
    ext z
    unfold at47_pr
    exact (Finset.mul_prod_erase A (fun b => z - (b : ℂ)) ha).symm
  have hd1 : HasDerivAt (fun z : ℂ => z - (a : ℂ)) 1 (a : ℂ) := (hasDerivAt_id _).sub_const _
  have hd2 : HasDerivAt (at47_pr (A.erase a)) (deriv (at47_pr (A.erase a)) (a : ℂ)) (a : ℂ) :=
    (at47_pr_differentiable (A.erase a) (a : ℂ)).hasDerivAt
  have hmul := (hd1.mul hd2).deriv
  rw [← hfac] at hmul
  rw [hmul, sub_self, zero_mul, one_mul, add_zero]
  rfl

/-- Two entire functions agreeing outside a finite real set coincide everywhere on `ℂ`. -/
private lemma entire_eq_of_eq_off_finset {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (A : Finset ℝ)
    (h : ∀ x : ℝ, x ∉ A → f (x : ℂ) = g (x : ℂ)) : ∀ z : ℂ, f z = g z := by
  let M : ℝ := (∑ a ∈ A, |a|) + 1
  have h_ivl : ∀ x : ℝ, M < x → x < M + 1 → f (x : ℂ) - g (x : ℂ) = 0 := by
    intro x hx1 _
    have hxA : x ∉ A := by
      intro hxA
      have hle : |x| ≤ ∑ a ∈ A, |a| :=
        Finset.single_le_sum (f := fun a => |a|) (fun _ _ => abs_nonneg _) hxA
      have hx_le : x ≤ |x| := le_abs_self x
      dsimp [M] at hx1
      linarith
    exact sub_eq_zero.mpr (h x hxA)
  have h0 := airy_entire_eq_zero_of_real_interval (hf.sub hg) (by linarith : M < M + 1) h_ivl
  exact fun z => sub_eq_zero.mp (h0 z)

/-- **Trial construction for `lem:airy-node-square`:** for any nonzero `p ∈ hbNodePolySpace D t S T`,
there is an entire `q_p` satisfying `q_p(z) ∏_{n ∈ T} (z - t_n) = N(z) p(z)` such that
`q_p ∈ IsAirySquareClass (airySites S)`, `∫ q_p² = hbNodePolyDenom`, `∫ u q_p² = hbNodePolyNum`,
`airySquareClassQuotient q_p = hbNodePolyQuotient`, and `(z - τ) q_p²` (`τ = hbNodePolyQuotient`) is
a zero-mass weak witness at `τ` with strictly positive Laplace transform on `(0, ∞)`. -/
theorem exists_hbNodeTrial (D : ShellHBData) {t : ℕ → ℝ} (ht : IsHbZeroEnum D.P D.Q t)
    (hm : 2 ≤ D.S.card) {S : Finset ℝ} {T : Finset ℕ} (hT1 : ∀ n ∈ T, 1 ≤ n)
    (hTcard : D.S.card / 2 + 1 ≤ T.card) {p : ℝ[X]}
    (hp : p ∈ hbNodePolySpace D t S T) (hp0 : p ≠ 0) :
    ∃ q : ℂ → ℂ,
      Differentiable ℂ q ∧
      (∀ z : ℂ, q z * at47_pr (T.image (hbNode t)) z = airyPQN D.P D.Q z * airyPQc p z) ∧
      IsAirySquareClass (airySites S) q ∧
      (∫ u : ℝ, (q (u : ℂ)).re ^ 2) = hbNodePolyDenom D t T p ∧
      (∫ u : ℝ, u * (q (u : ℂ)).re ^ 2) = hbNodePolyNum D t T p ∧
      airySquareClassQuotient q = hbNodePolyQuotient D t T p ∧
      IsAiryWeakWitness (S : Set ℝ) (hbNodePolyQuotient D t T p)
        (fun z => (z - (hbNodePolyQuotient D t T p : ℂ)) * q z ^ 2) ∧
      (∫ u : ℝ, (((u : ℂ) - (hbNodePolyQuotient D t T p : ℂ)) * q (u : ℂ) ^ 2).re) = 0 ∧
      (∀ y : ℝ, 0 < y →
        0 < laplaceL (fun u => (((u : ℂ) - (hbNodePolyQuotient D t T p : ℂ)) * q (u : ℂ) ^ 2).re) y) := by
  classical
  have hQ : D.Q ≠ 0 := D.Q_ne_zero_of_two_le hm
  have hm_eq : D.S.card = at47_e D.P D.Q + 2 := by
    rcases D.m_eq with ⟨hQ0, _⟩ | ⟨_, hcard⟩
    · exact absurd hQ0 hQ
    · exact hcard.trans (at47_m_eq D.P D.Q)
  let A_T : Finset ℝ := T.image (hbNode t)
  have hAT_card : A_T.card = T.card :=
    Finset.card_image_of_injOn fun a ha b hb hab =>
      hbNode_injOn ht (hT1 a ha) (hT1 b hb) hab
  have hAT_zero : ∀ a ∈ A_T, airyPQN D.P D.Q (a : ℂ) = 0 := by
    intro a ha
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.1 ha
    exact hbNode_zero_airyPQN D ht
  have hNd : Differentiable ℂ (airyPQN D.P D.Q) := differentiable_airyPQN D.P D.Q
  have hpd : Differentiable ℂ (airyPQc p) := fun z => (hasDerivAt_airyPQc p z).differentiableAt
  obtain ⟨q, hqd, hqeq⟩ := exists_entire_div_finset A_T (φ := fun z => airyPQN D.P D.Q z * airyPQc p z)
    (hNd.mul hpd) (fun a ha => by rw [hAT_zero a ha, zero_mul])
  -- Value of `q` at nodes `hbNode t n`: `0` outside `T`, derivative ratio inside `T`.
  have hq_node_out : ∀ x : ℝ, airyPQN D.P D.Q (x : ℂ) = 0 → x ∉ A_T → q (x : ℂ) = 0 := by
    intro x hx0 hxAT
    have h := hqeq (x : ℂ)
    rw [hx0, zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_right (at47_pr_ne_zero hxAT)
  have hq_node_in : ∀ n ∈ T,
      q (hbNode t n : ℂ) * (∏ k ∈ T.erase n, ((hbNode t n : ℂ) - (hbNode t k : ℂ))) =
        airyPQN' D.P D.Q (hbNode t n : ℂ) * ((Polynomial.eval (hbNode t n) p : ℝ) : ℂ) := by
    intro n hn
    have ha_mem : hbNode t n ∈ A_T := Finset.mem_image_of_mem _ hn
    have hlhs : deriv (fun z => q z * at47_pr A_T z) (hbNode t n : ℂ) =
        q (hbNode t n : ℂ) * deriv (at47_pr A_T) (hbNode t n : ℂ) := by
      have h1 := ((hqd (hbNode t n : ℂ)).hasDerivAt.mul
        (at47_pr_differentiable A_T (hbNode t n : ℂ)).hasDerivAt).deriv
      change deriv (fun z => q z * at47_pr A_T z) (hbNode t n : ℂ) = _ at h1
      rw [h1, at47_pr_eq_zero ha_mem, mul_zero, zero_add]
    have hrhs : deriv (fun z => airyPQN D.P D.Q z * airyPQc p z) (hbNode t n : ℂ) =
        airyPQN' D.P D.Q (hbNode t n : ℂ) * airyPQc p (hbNode t n : ℂ) := by
      have h1 := ((hasDerivAt_airyPQN D.P D.Q (hbNode t n : ℂ)).mul
        (hasDerivAt_airyPQc p (hbNode t n : ℂ))).deriv
      change deriv (fun z => airyPQN D.P D.Q z * airyPQc p z) (hbNode t n : ℂ) = _ at h1
      rw [h1, hbNode_zero_airyPQN D ht, zero_mul, add_zero]
    have hfeq : (fun z => q z * at47_pr A_T z) = fun z => airyPQN D.P D.Q z * airyPQc p z := funext hqeq
    rw [hfeq, hrhs, airyPQc_ofReal] at hlhs
    rw [hlhs, deriv_at47_pr_of_mem ha_mem]
    congr 1
    have himg_erase : A_T.erase (hbNode t n) = (T.erase n).image (hbNode t) := by
      ext x
      simp only [A_T, Finset.mem_erase, Finset.mem_image]
      constructor
      · rintro ⟨hxne, k, hkT, rfl⟩
        exact ⟨k, ⟨ fun hkn => hxne (hkn ▸ rfl), hkT⟩, rfl⟩
      · rintro ⟨k, ⟨hkn, hkT⟩, rfl⟩
        exact ⟨fun heq => hkn (hbNode_injOn ht (hT1 k hkT) (hT1 n hn) heq), k, hkT, rfl⟩
    rw [himg_erase, Finset.prod_image]
    intro a ha b hb hab
    exact hbNode_injOn ht (hT1 a (Finset.mem_of_mem_erase ha)) (hT1 b (Finset.mem_of_mem_erase hb)) hab
  -- Real-valuedness of `q` on `ℝ`.
  have hq_real_formula : ∀ x : ℝ, x ∉ A_T →
      q (x : ℂ) = ((at47_Nf D.P D.Q x * p.eval x / ∏ a ∈ A_T, (x - a) : ℝ) : ℂ) := by
    intro x hx
    have h := hqeq (x : ℂ)
    have hpr := at47_pr_ne_zero hx
    rw [at47_pr_ofReal] at h hpr
    have hpr_re : (∏ a ∈ A_T, (x - a)) ≠ 0 := fun h0 => hpr (by simp [h0])
    rw [airyPQN_ofReal, airyPQc_ofReal] at h
    unfold at47_Nf
    rw [Complex.ofReal_div, eq_div_iff (Complex.ofReal_ne_zero.mpr hpr_re), Complex.ofReal_mul]
    exact h
  have hq_real : ∀ x : ℝ, (q (x : ℂ)).im = 0 := by
    intro x
    by_cases hx : x ∈ A_T
    · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hx
      have hprod_ne : (∏ k ∈ T.erase n, (hbNode t n - hbNode t k)) ≠ 0 := by
        refine Finset.prod_ne_zero_iff.2 fun k hk => sub_ne_zero.2 fun heq => ?_
        obtain ⟨hkn, hkT⟩ := Finset.mem_erase.1 hk
        exact hkn (hbNode_injOn ht (hT1 n hn) (hT1 k hkT) heq).symm
      -- Continuity from `x ∉ A_T` gives `(q x).im = 0` everywhere on `ℝ`!
      have hcont_im : Continuous (fun y : ℝ => (q (y : ℂ)).im) :=
        Complex.continuous_im.comp (hqd.continuous.comp Complex.continuous_ofReal)
      have hdense : Dense ({y : ℝ | y ∉ A_T}) :=
        (A_T.finite_toSet.countable).dense_compl ℝ
      have hext := Continuous.ext_on hdense hcont_im continuous_const
        (g := fun _ => (0 : ℝ)) fun y hy => by rw [hq_real_formula y hy, Complex.ofReal_im]
      exact congrFun hext (hbNode t n)
    · rw [hq_real_formula x hx, Complex.ofReal_im]
  -- Vanishing on `S`.
  have hq_sites : ∀ s ∈ S, q (s : ℂ) = 0 := by
    intro s hs
    by_cases hN0 : at47_Nf D.P D.Q s = 0
    · by_cases hsAT : s ∈ A_T
      · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hsAT
        have hp_eval : p.eval (hbNode t n) = 0 := hp.2 _ hs (Or.inr hsAT)
        have hrel := hq_node_in n hn
        rw [hp_eval, Complex.ofReal_zero, mul_zero] at hrel
        have hpr_ne : (∏ k ∈ T.erase n, ((hbNode t n : ℂ) - (hbNode t k : ℂ))) ≠ 0 := by
          refine Finset.prod_ne_zero_iff.2 fun k hk => sub_ne_zero.2 fun heq => ?_
          obtain ⟨hkn, hkT⟩ := Finset.mem_erase.1 hk
          exact hkn (hbNode_injOn ht (hT1 n hn) (hT1 k hkT) (Complex.ofReal_injective heq)).symm
        exact (mul_eq_zero.mp hrel).resolve_right hpr_ne
      · exact hq_node_out s ((nodeZero_iff D s).2 hN0) hsAT
    · have hp_eval : p.eval s = 0 := hp.2 s hs (Or.inl hN0)
      have hsAT : s ∉ A_T := by
        intro hsAT
        obtain ⟨n, _, rfl⟩ := Finset.mem_image.1 hsAT
        exact hN0 (hbNode_zero_Nf ht)
      rw [hq_real_formula s hsAT, hp_eval, mul_zero, zero_div, Complex.ofReal_zero]
  -- Global `airyEnv` growth bound for `q²` via two applications of `at47_div_finset A_T`.
  obtain ⟨CN, νN, hCN, hbN⟩ := at47_N_class D.P D.Q
  let Bp : ℝ := ∑ k ∈ Finset.range (p.natDegree + 1), |p.coeff k|
  have hBp0 : 0 ≤ Bp := Finset.sum_nonneg fun _ _ => abs_nonneg _
  let φ₂ : ℂ → ℂ := fun z => airyPQN D.P D.Q z ^ 2 * airyPQc p z ^ 2
  have hφ₂_eq : ∀ z : ℂ, φ₂ z = (q z ^ 2 * at47_pr A_T z) * at47_pr A_T z := by
    intro z
    dsimp [φ₂]
    have h : (q z * at47_pr A_T z) ^ 2 = (airyPQN D.P D.Q z * airyPQc p z) ^ 2 :=
      congrArg (fun w => w ^ 2) (hqeq z)
    linear_combination -h
  have hφ₂_bound : ∀ z : ℂ, ‖φ₂ z‖ ≤ (CN * Bp ^ 2) * (1 + ‖z‖) ^ (νN + 2 * (p.natDegree : ℝ)) * airyEnv z := by
    intro z
    dsimp [φ₂]
    rw [norm_mul, norm_pow (airyPQc p z)]
    have h1 := hbN z
    have h2 : ‖airyPQc p z‖ ^ 2 ≤ Bp ^ 2 * ((1 + ‖z‖) ^ p.natDegree) ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (at47_cpoly_norm_le p z) 2
    have hx0 : 0 < 1 + ‖z‖ := by linarith [norm_nonneg z]
    have hexp : (1 + ‖z‖) ^ νN * ((1 + ‖z‖) ^ p.natDegree) ^ 2 =
        (1 + ‖z‖) ^ (νN + 2 * (p.natDegree : ℝ)) := by
      rw [← pow_mul, mul_comm p.natDegree 2, Real.rpow_add hx0,
        show (2 * (p.natDegree : ℝ)) = ((2 * p.natDegree : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    calc ‖airyPQN D.P D.Q z ^ 2‖ * ‖airyPQc p z‖ ^ 2
        ≤ (CN * (1 + ‖z‖) ^ νN * airyEnv z) * (Bp ^ 2 * ((1 + ‖z‖) ^ p.natDegree) ^ 2) :=
          mul_le_mul h1 h2 (sq_nonneg _) (mul_nonneg (mul_nonneg hCN (Real.rpow_nonneg hx0.le _)) (airyEnv_pos z).le)
      _ = (CN * Bp ^ 2) * ((1 + ‖z‖) ^ νN * ((1 + ‖z‖) ^ p.natDegree) ^ 2) * airyEnv z := by ring
      _ = (CN * Bp ^ 2) * (1 + ‖z‖) ^ (νN + 2 * (p.natDegree : ℝ)) * airyEnv z := by rw [hexp]
  have hφ₂_d : Differentiable ℂ φ₂ := (hNd.pow 2).mul (hpd.pow 2)
  obtain ⟨ψ₁, hψ₁d, hψ₁eq, C₁, hC₁, hb₁⟩ := at47_div_finset A_T hφ₂_d
    (fun a ha => by dsimp [φ₂]; rw [hAT_zero a ha]; simp)
    (mul_nonneg hCN (sq_nonneg Bp)) hφ₂_bound
  have hψ₁_ident : ∀ z : ℂ, ψ₁ z = q z ^ 2 * at47_pr A_T z := by
    refine entire_eq_of_eq_off_finset hψ₁d ((hqd.pow 2).mul (at47_pr_differentiable A_T)) A_T fun x hx => ?_
    have hpr := at47_pr_ne_zero hx
    have h := (hψ₁eq (x : ℂ)).symm.trans (hφ₂_eq (x : ℂ))
    unfold at47_pr at h
    exact mul_right_cancel₀ hpr h
  obtain ⟨ψ₂, hψ₂d, hψ₂eq, C₂, hC₂, hb₂⟩ := at47_div_finset A_T hψ₁d
    (fun a ha => by rw [hψ₁_ident, at47_pr_eq_zero ha, mul_zero]) hC₁ hb₁
  have hψ₂_ident : ∀ z : ℂ, ψ₂ z = q z ^ 2 := by
    refine entire_eq_of_eq_off_finset hψ₂d (hqd.pow 2) A_T fun x hx => ?_
    have hpr := at47_pr_ne_zero hx
    have h := (hψ₂eq (x : ℂ)).symm.trans (hψ₁_ident (x : ℂ))
    unfold at47_pr at h
    exact mul_right_cancel₀ hpr h
  let ν₂ : ℝ := νN + 2 * (p.natDegree : ℝ)
  have hq2_env : ∀ z : ℂ, ‖q z ^ 2‖ ≤ C₂ * (1 + ‖z‖) ^ ν₂ * airyEnv z := by
    intro z; rw [← hψ₂_ident z]; exact hb₂ z
  have hzq2_env : ∀ z : ℂ, ‖z * q z ^ 2‖ ≤ C₂ * (1 + ‖z‖) ^ (ν₂ + 1) * airyEnv z := by
    intro z
    have hx0 : 0 < 1 + ‖z‖ := by linarith [norm_nonneg z]
    rw [norm_mul, Real.rpow_add hx0, Real.rpow_one]
    calc ‖z‖ * ‖q z ^ 2‖
        ≤ (1 + ‖z‖) * (C₂ * (1 + ‖z‖) ^ ν₂ * airyEnv z) :=
          mul_le_mul (by linarith) (hq2_env z) (norm_nonneg _) hx0.le
      _ = C₂ * ((1 + ‖z‖) ^ ν₂ * (1 + ‖z‖)) * airyEnv z := by ring
  -- Negative-axis decay `|x|^{-3/2}` for both `q(x)²` and `x * q(x)²`.
  obtain ⟨KN, S1, hKN, hS1, hN_neg⟩ := at47_Nf_neg_sq D.P D.Q hQ
  let R_T : ℝ := ∑ a ∈ A_T, |a|
  have hRT0 : 0 ≤ R_T := Finset.sum_nonneg fun _ _ => abs_nonneg _
  let A_neg : ℝ := max S1 (2 * R_T + 1)
  have hA_neg1 : 1 ≤ A_neg := hS1.trans (le_max_left _ _)
  have hzq2_neg : ∀ x : ℝ, x ≤ -A_neg →
      ‖(x : ℂ) * q (x : ℂ) ^ 2‖ ≤ (KN * Bp ^ 2 * 2 ^ (2 * p.natDegree + 2 * T.card)) * (-x) ^ (-(3 / 2) : ℝ) := by
    intro x hx
    set s : ℝ := -x with hs_def
    have hsA : A_neg ≤ s := by linarith
    have hsS1 : S1 ≤ s := (le_max_left _ _).trans hsA
    have hsR : 2 * R_T + 1 ≤ s := (le_max_right _ _).trans hsA
    have hs1 : 1 ≤ s := hA_neg1.trans hsA
    have hs0 : 0 < s := by linarith
    have hxs : x = -s := by linarith
    have hxAT : x ∉ A_T := by
      intro hxAT
      have hle : |x| ≤ R_T := Finset.single_le_sum (f := fun a => |a|) (fun _ _ => abs_nonneg _) hxAT
      rw [hxs, abs_neg, abs_of_pos hs0] at hle
      linarith
    have hpr_low : (s / 2) ^ (2 * T.card) ≤ (∏ a ∈ A_T, (x - a)) ^ 2 := by
      have h1 : (s / 2) ^ A_T.card ≤ |∏ a ∈ A_T, (x - a)| := by
        rw [Finset.abs_prod]
        calc (s / 2) ^ A_T.card = ∏ _a ∈ A_T, (s / 2) := by rw [Finset.prod_const]
          _ ≤ ∏ a ∈ A_T, |x - a| := by
            gcongr with a ha
            have haR : |a| ≤ R_T := Finset.single_le_sum (f := fun b => |b|) (fun _ _ => abs_nonneg _) ha
            have hxabs : |x| = s := by rw [hxs, abs_neg, abs_of_pos hs0]
            have htri := abs_sub_abs_le_abs_sub x a
            linarith
      have h2 := pow_le_pow_left₀ (by positivity) h1 2
      rwa [sq_abs, ← pow_mul, mul_comm _ 2, hAT_card] at h2
    have hp_up : (p.eval x) ^ 2 ≤ Bp ^ 2 * (2 * s) ^ (2 * p.natDegree) := by
      have hcpoly := at47_cpoly_norm_le p (x : ℂ)
      rw [airyPQc_ofReal, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
        Real.norm_eq_abs, hxs, abs_neg, abs_of_pos hs0, ← hxs] at hcpoly
      have h1s : 1 + s ≤ 2 * s := by linarith
      have hp1 : |p.eval x| ≤ Bp * (2 * s) ^ p.natDegree :=
        hcpoly.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1s _) hBp0)
      have hp2 := pow_le_pow_left₀ (abs_nonneg _) hp1 2
      rwa [sq_abs, mul_pow, ← pow_mul, mul_comm p.natDegree 2] at hp2
    have hNs := hN_neg s hsS1
    rw [← hxs] at hNs
    rw [hq_real_formula x hxAT, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, hxs, abs_neg, abs_of_pos hs0, ← hxs, sq_abs, div_pow,
      mul_pow, at47_rpow_neg_three_halves hs0]
    have hden_pos : 0 < (s / 2) ^ (2 * T.card) := by positivity
    have hnum_le : s * (at47_Nf D.P D.Q x ^ 2 * p.eval x ^ 2) ≤
        KN * Bp ^ 2 * 2 ^ (2 * p.natDegree) * (s ^ (1 + at47_e D.P D.Q + 2 * p.natDegree) * √s) := by
      calc s * (at47_Nf D.P D.Q x ^ 2 * p.eval x ^ 2)
          ≤ s * ((KN * (s ^ at47_e D.P D.Q * √s)) * (Bp ^ 2 * (2 * s) ^ (2 * p.natDegree))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hNs hp_up (sq_nonneg _) (by positivity)) hs0.le
        _ = KN * Bp ^ 2 * 2 ^ (2 * p.natDegree) *
              ((s * s ^ at47_e D.P D.Q * s ^ (2 * p.natDegree)) * √s) := by
            rw [mul_pow]; ring
        _ = KN * Bp ^ 2 * 2 ^ (2 * p.natDegree) * (s ^ (1 + at47_e D.P D.Q + 2 * p.natDegree) * √s) := by
            congr 2; rw [pow_add, pow_add, pow_one]
    have hexp_le : 1 + at47_e D.P D.Q + 2 * p.natDegree + 2 ≤ 2 * T.card := by
      have hdeg : p.natDegree ≤ T.card - D.S.card / 2 - 1 := hp.1
      omega
    have hpow_le : s ^ (1 + at47_e D.P D.Q + 2 * p.natDegree) * s ^ 2 ≤ s ^ (2 * T.card) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hs1 hexp_le
    calc s * (at47_Nf D.P D.Q x ^ 2 * p.eval x ^ 2 / (∏ a ∈ A_T, (x - a)) ^ 2)
        = (s * (at47_Nf D.P D.Q x ^ 2 * p.eval x ^ 2)) / (∏ a ∈ A_T, (x - a)) ^ 2 :=
          (mul_div_assoc _ _ _).symm
      _ ≤ (KN * Bp ^ 2 * 2 ^ (2 * p.natDegree) * (s ^ (1 + at47_e D.P D.Q + 2 * p.natDegree) * √s)) /
            (s / 2) ^ (2 * T.card) :=
          div_le_div₀ (by positivity) hnum_le hden_pos hpr_low
      _ = (KN * Bp ^ 2 * 2 ^ (2 * p.natDegree + 2 * T.card)) *
            ((s ^ (1 + at47_e D.P D.Q + 2 * p.natDegree) * √s) / s ^ (2 * T.card)) := by
          rw [div_pow, pow_add]; field_simp; ring
      _ ≤ (KN * Bp ^ 2 * 2 ^ (2 * p.natDegree + 2 * T.card)) * (1 / (s * √s)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hsqrt_pos : 0 < √s := Real.sqrt_pos.mpr hs0
          have hrr : √s * √s = s := Real.mul_self_sqrt hs0.le
          rw [div_le_div_iff₀ (pow_pos hs0 _) (mul_pos hs0 hsqrt_pos)]
          calc s ^ (1 + at47_e D.P D.Q + 2 * p.natDegree) * √s * (s * √s)
              = (s ^ (1 + at47_e D.P D.Q + 2 * p.natDegree) * s ^ 2) := by
                have : √s * (s * √s) = s ^ 2 := by nlinarith [hrr]
                rw [mul_assoc, this]
            _ ≤ 1 * s ^ (2 * T.card) := by linarith
  have hq2_neg : ∀ x : ℝ, x ≤ -A_neg →
      ‖q (x : ℂ) ^ 2‖ ≤ (KN * Bp ^ 2 * 2 ^ (2 * p.natDegree + 2 * T.card)) * (-x) ^ (-(3 / 2) : ℝ) := by
    intro x hx
    have hs1 : 1 ≤ -x := hA_neg1.trans (by linarith)
    calc ‖q (x : ℂ) ^ 2‖
        ≤ (-x) * ‖q (x : ℂ) ^ 2‖ := le_mul_of_one_le_left (norm_nonneg _) hs1
      _ = ‖(x : ℂ) * q (x : ℂ) ^ 2‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      _ ≤ _ := hzq2_neg x hx
  -- `InAiryClass` for `q²` and `z * q²`.
  obtain ⟨Kp1, Ap1, hAp1, hpos1⟩ := at47_F_pos_decay hC₂ hq2_env
  have hq2_int : Integrable (fun x : ℝ => q (x : ℂ) ^ 2) :=
    at47_integrable_of_decay (fun z => (hqd z).pow 2) (A := max A_neg Ap1)
      (hA_neg1.trans (le_max_left _ _))
      (fun x hx => hq2_neg x (by linarith [le_max_left A_neg Ap1]))
      (fun x hx => hpos1 x ((le_max_right _ _).trans hx))
  have hq2_class : InAiryClass (fun z => q z ^ 2) :=
    ⟨fun z => (hqd z).pow 2, hq2_int, ⟨C₂, ν₂, hC₂, hq2_env⟩,
      fun x => im_sq_of_im_zero (hq_real x)⟩
  obtain ⟨Kp2, Ap2, hAp2, hpos2⟩ := at47_F_pos_decay hC₂ hzq2_env
  have hzq2_int : Integrable (fun x : ℝ => (x : ℂ) * q (x : ℂ) ^ 2) :=
    at47_integrable_of_decay (fun z => differentiableAt_id.mul ((hqd z).pow 2)) (A := max A_neg Ap2)
      (hA_neg1.trans (le_max_left _ _))
      (fun x hx => hzq2_neg x (by linarith [le_max_left A_neg Ap2]))
      (fun x hx => hpos2 x ((le_max_right _ _).trans hx))
  have hzq2_class : InAiryClass (fun z => z * q z ^ 2) :=
    ⟨fun z => differentiableAt_id.mul ((hqd z).pow 2), hzq2_int, ⟨C₂, ν₂ + 1, hC₂, hzq2_env⟩,
      fun x => by
        dsimp only
        rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
          im_sq_of_im_zero (hq_real x), mul_zero]⟩
  -- HB quadrature evaluates `∫ q²` and `∫ u q²` in terms of `hbNodeWeight`.
  let embT : {n // n ∈ T} → {z : ℂ // airyPQN D.P D.Q z = 0} :=
    fun ⟨n, _⟩ => ⟨(hbNode t n : ℂ), hbNode_zero_airyPQN D ht⟩
  have hemb_inj : Function.Injective embT := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have h1 : (hbNode t a : ℂ) = (hbNode t b : ℂ) := congrArg Subtype.val hab
    exact Subtype.ext (hbNode_injOn ht (hT1 a ha) (hT1 b hb) (Complex.ofReal_injective h1))
  let F_T : Finset {z : ℂ // airyPQN D.P D.Q z = 0} := T.attach.image embT
  have hq_zero_off_FT : ∀ z : {z : ℂ // airyPQN D.P D.Q z = 0}, z ∉ F_T → q z.1 = 0 := by
    intro z hzFT
    have hzr : z.1 = ((z.1.re : ℝ) : ℂ) := airyPQ_zero_eq_ofReal D.hHB z.2
    have hx0 : airyPQN D.P D.Q (z.1.re : ℂ) = 0 := hzr ▸ z.2
    have hxAT : z.1.re ∉ A_T := by
      intro hxAT
      obtain ⟨n, hn, hxn⟩ := Finset.mem_image.1 hxAT
      apply hzFT
      refine Finset.mem_image.2 ⟨⟨n, hn⟩, Finset.mem_attach _ _, ?_⟩
      apply Subtype.ext
      dsimp [embT]
      rw [hxn, ← hzr]
    rw [hzr]
    exact hq_node_out z.1.re hx0 hxAT
  have hterm_val : ∀ n ∈ T,
      q (hbNode t n : ℂ) ^ 2 *
        (airyPQD D.P D.Q (hbNode t n : ℂ) / airyPQN' D.P D.Q (hbNode t n : ℂ) ^ 2) =
        ((hbNodeWeight D.P D.Q t T n * (p.eval (hbNode t n)) ^ 2 : ℝ) : ℂ) := by
    intro n hn
    have hz : airyPQN D.P D.Q (hbNode t n : ℂ) = 0 := hbNode_zero_airyPQN D ht
    have hN'_ne : airyPQN' D.P D.Q (hbNode t n : ℂ) ≠ 0 := (airyPQ_zero_weight_pos D.hHB hQ hz).2
    have hpr_ne_r : (∏ k ∈ T.erase n, (hbNode t n - hbNode t k)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun k hk => sub_ne_zero.2 fun heq => ?_
      obtain ⟨hkn, hkT⟩ := Finset.mem_erase.1 hk
      exact hkn (hbNode_injOn ht (hT1 n hn) (hT1 k hkT) heq).symm
    have hpr_ne : (∏ k ∈ T.erase n, ((hbNode t n : ℂ) - (hbNode t k : ℂ))) ≠ 0 := by
      simpa using Complex.ofReal_ne_zero.mpr hpr_ne_r
    have hrel_sq : (q (hbNode t n : ℂ) * ∏ k ∈ T.erase n, ((hbNode t n : ℂ) - (hbNode t k : ℂ))) ^ 2 =
        (airyPQN' D.P D.Q (hbNode t n : ℂ) * ((Polynomial.eval (hbNode t n) p : ℝ) : ℂ)) ^ 2 :=
      congrArg (fun w => w ^ 2) (hq_node_in n hn)
    rw [mul_pow, mul_pow] at hrel_sq
    have hq_sq : q (hbNode t n : ℂ) ^ 2 =
        airyPQN' D.P D.Q (hbNode t n : ℂ) ^ 2 * ((Polynomial.eval (hbNode t n) p : ℝ) : ℂ) ^ 2 /
          (∏ k ∈ T.erase n, ((hbNode t n : ℂ) - (hbNode t k : ℂ))) ^ 2 := by
      rw [eq_div_iff (pow_ne_zero 2 hpr_ne)]
      exact hrel_sq
    rw [hq_sq, airyPQD_ofReal]
    unfold hbNodeWeight
    have hprod_sq : (∏ k ∈ T.erase n, ((hbNode t n : ℂ) - (hbNode t k : ℂ))) ^ 2 =
        ((∏ k ∈ T.erase n, (hbNode t n - hbNode t k) ^ 2 : ℝ) : ℂ) := by
      rw [← Finset.prod_pow]
      push_cast
      rfl
    rw [hprod_sq]
    have hden_c : ((∏ k ∈ T.erase n, (hbNode t n - hbNode t k) ^ 2 : ℝ) : ℂ) ≠ 0 := by
      rw [← hprod_sq]
      exact pow_ne_zero 2 hpr_ne
    push_cast
    field_simp
  have hint_q2_c : (∫ x : ℝ, q (x : ℂ) ^ 2) = ((hbNodePolyDenom D t T p : ℝ) : ℂ) := by
    have hsum1 := airyPQ_hasSum_unc D.hHB hQ (f := fun z => q z ^ 2)
      (fun z => (hqd z).pow 2) hq2_int hC₂ hq2_env
    have hsum2 : HasSum (fun z : {z : ℂ // airyPQN D.P D.Q z = 0} =>
        q z.1 ^ 2 * (airyPQD D.P D.Q z.1 / airyPQN' D.P D.Q z.1 ^ 2))
        (∑ z ∈ F_T, q z.1 ^ 2 * (airyPQD D.P D.Q z.1 / airyPQN' D.P D.Q z.1 ^ 2)) :=
      hasSum_sum_of_ne_finset_zero fun z hz => by rw [hq_zero_off_FT z hz, zero_pow two_ne_zero, zero_mul]
    rw [hsum1.unique hsum2]
    dsimp [F_T]
    rw [Finset.sum_image (fun a _ b _ hab => hemb_inj hab)]
    unfold hbNodePolyDenom
    rw [Complex.ofReal_sum, ← Finset.sum_attach T]
    refine Finset.sum_congr rfl fun ⟨n, hn⟩ _ => ?_
    dsimp [embT]
    exact hterm_val n hn
  have hint_zq2_c : (∫ x : ℝ, (x : ℂ) * q (x : ℂ) ^ 2) = ((hbNodePolyNum D t T p : ℝ) : ℂ) := by
    have hsum1 := airyPQ_hasSum_unc D.hHB hQ (f := fun z => z * q z ^ 2)
      (fun z => differentiableAt_id.mul ((hqd z).pow 2)) hzq2_int hC₂ hzq2_env
    have hsum2 : HasSum (fun z : {z : ℂ // airyPQN D.P D.Q z = 0} =>
        (z.1 * q z.1 ^ 2) * (airyPQD D.P D.Q z.1 / airyPQN' D.P D.Q z.1 ^ 2))
        (∑ z ∈ F_T, (z.1 * q z.1 ^ 2) * (airyPQD D.P D.Q z.1 / airyPQN' D.P D.Q z.1 ^ 2)) :=
      hasSum_sum_of_ne_finset_zero fun z hz => by
        rw [hq_zero_off_FT z hz, zero_pow two_ne_zero, mul_zero, zero_mul]
    rw [hsum1.unique hsum2]
    dsimp [F_T]
    rw [Finset.sum_image (fun a _ b _ hab => hemb_inj hab)]
    unfold hbNodePolyNum
    rw [Complex.ofReal_sum, ← Finset.sum_attach T]
    refine Finset.sum_congr rfl fun ⟨n, hn⟩ _ => ?_
    dsimp [embT]
    have h := congrArg (fun w => (hbNode t n : ℂ) * w) (hterm_val n hn)
    calc ((hbNode t n : ℂ) * q (hbNode t n : ℂ) ^ 2) *
          (airyPQD D.P D.Q (hbNode t n : ℂ) / airyPQN' D.P D.Q (hbNode t n : ℂ) ^ 2)
        = (hbNode t n : ℂ) * (q (hbNode t n : ℂ) ^ 2 *
            (airyPQD D.P D.Q (hbNode t n : ℂ) / airyPQN' D.P D.Q (hbNode t n : ℂ) ^ 2)) := by ring
      _ = (hbNode t n : ℂ) * ((hbNodeWeight D.P D.Q t T n * (p.eval (hbNode t n)) ^ 2 : ℝ) : ℂ) := h
      _ = ((hbNodeWeight D.P D.Q t T n * hbNode t n * (p.eval (hbNode t n)) ^ 2 : ℝ) : ℂ) := by
          push_cast; ring
  have hint_q2 : (∫ u : ℝ, (q (u : ℂ)).re ^ 2) = hbNodePolyDenom D t T p := by
    have h1 := congrArg Complex.re hint_q2_c
    have h2 : (∫ x : ℝ, q (x : ℂ) ^ 2).re = ∫ x : ℝ, (q (x : ℂ) ^ 2).re := by
      simpa [RCLike.re_to_complex] using (integral_re hq2_int).symm
    rw [h2, Complex.ofReal_re] at h1
    rw [← h1]
    exact integral_congr_ae (Eventually.of_forall fun u => (re_sq_of_im_zero (hq_real u)).symm)
  have hint_zq2 : (∫ u : ℝ, u * (q (u : ℂ)).re ^ 2) = hbNodePolyNum D t T p := by
    have h1 := congrArg Complex.re hint_zq2_c
    have h2 : (∫ x : ℝ, (x : ℂ) * q (x : ℂ) ^ 2).re = ∫ x : ℝ, ((x : ℂ) * q (x : ℂ) ^ 2).re := by
      simpa [RCLike.re_to_complex] using (integral_re hzq2_int).symm
    rw [h2, Complex.ofReal_re] at h1
    rw [← h1]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      re_sq_of_im_zero (hq_real u)]
  have hden_pos : 0 < hbNodePolyDenom D t T p := hbNodePolyDenom_pos D ht hm hT1 hTcard hp hp0
  have hq_nz : ∃ z : ℂ, q z ≠ 0 := by
    by_contra hall0
    push Not at hall0
    simp [hall0] at hint_q2
    linarith
  have hsq_class : IsAirySquareClass (airySites S) q := by
    refine ⟨hqd, hq_real, hq_nz, hq2_class, hzq2_class, fun j => ?_⟩
    have hj : airySites S j ∈ S := by
      have hmem : airySites S j ∈ Set.range (airySites S) := ⟨j, rfl⟩
      rwa [range_airySites] at hmem
    exact hq_sites _ hj
  have hquot_eq : airySquareClassQuotient q = hbNodePolyQuotient D t T p := by
    unfold airySquareClassQuotient hbNodePolyQuotient
    rw [hint_zq2, hint_q2]
  -- Witness properties of `H_p(z) = (z - τ) q(z)²`.
  let τ : ℝ := hbNodePolyQuotient D t T p
  let H_p : ℂ → ℂ := fun z => (z - (τ : ℂ)) * q z ^ 2
  have hHp_eq : H_p = fun z => z * q z ^ 2 - (τ : ℂ) * q z ^ 2 := by ext z; dsimp [H_p]; ring
  have hHp_class : InAiryClass H_p := by
    rw [hHp_eq]
    exact hzq2_class.sub (hq2_class.smul τ)
  have hHp_re : ∀ u : ℝ, (H_p (u : ℂ)).re = (u - τ) * (q (u : ℂ)).re ^ 2 := by
    intro u
    dsimp [H_p]
    rw [← Complex.ofReal_sub, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, re_sq_of_im_zero (hq_real u)]
  have hHp_int0 : (∫ u : ℝ, (H_p (u : ℂ)).re) = 0 := by
    have h1 : Integrable (fun u : ℝ => u * (q (u : ℂ)).re ^ 2) :=
      hzq2_class.2.1.re.congr (Eventually.of_forall fun u => by
        dsimp only
        rw [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          sub_zero, re_sq_of_im_zero (hq_real u)])
    have h2 : Integrable (fun u : ℝ => (q (u : ℂ)).re ^ 2) :=
      hq2_class.2.1.re.congr (Eventually.of_forall fun u => by
        dsimp only
        rw [RCLike.re_to_complex, re_sq_of_im_zero (hq_real u)])
    have hsub : (∫ u : ℝ, (H_p (u : ℂ)).re) =
        (∫ u : ℝ, u * (q (u : ℂ)).re ^ 2) - τ * (∫ u : ℝ, (q (u : ℂ)).re ^ 2) := by
      simp_rw [hHp_re, sub_mul]
      rw [integral_sub h1 (h2.const_mul τ), integral_const_mul]
    rw [hsub, hint_zq2, hint_q2]
    dsimp [τ, hbNodePolyQuotient]
    rw [div_mul_cancel₀ _ hden_pos.ne', sub_self]
  have hHp_lap_pos : ∀ y : ℝ, 0 < y → 0 < laplaceL (fun u => (H_p (u : ℂ)).re) y := by
    intro y hy
    unfold laplaceL
    have hint_exp : Integrable (fun u : ℝ => (H_p (u : ℂ)).re * Real.exp (y * u)) :=
      hHp_class.to_polyLeftAiryRightBound.integrable_exp hy
    have hint_base : Integrable (fun u : ℝ => (H_p (u : ℂ)).re) := hHp_class.2.1.re
    let g : ℝ → ℝ := fun u => (u - τ) * (Real.exp (y * u) - Real.exp (y * τ)) * (q (u : ℂ)).re ^ 2
    have hg_eq : g = fun u : ℝ => (H_p (u : ℂ)).re * Real.exp (y * u) -
        Real.exp (y * τ) * (H_p (u : ℂ)).re := by
      ext u; dsimp [g]; rw [hHp_re u]; ring
    have hg_int : Integrable g := by rw [hg_eq]; exact hint_exp.sub (hint_base.const_mul _)
    have hg_integral_eq : (∫ u : ℝ, g u) = ∫ u : ℝ, (H_p (u : ℂ)).re * Real.exp (y * u) := by
      rw [hg_eq, integral_sub hint_exp (hint_base.const_mul _), integral_const_mul,
        hHp_int0, mul_zero, sub_zero]
    rw [← hg_integral_eq]
    have hg_nn : ∀ u : ℝ, 0 ≤ g u := by
      intro u
      dsimp [g]
      refine mul_nonneg ?_ (sq_nonneg _)
      rcases le_or_gt u τ with hle | hgt
      · exact mul_nonneg_of_nonpos_of_nonpos (by linarith)
          (sub_nonpos.mpr (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hle hy.le)))
      · exact mul_nonneg (by linarith)
          (sub_nonneg.mpr (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hgt.le hy.le)))
    by_contra hnot
    have hg_int0 : (∫ u : ℝ, g u) = 0 := le_antisymm (not_lt.mp hnot) (integral_nonneg hg_nn)
    have hae := (integral_eq_zero_iff_of_nonneg hg_nn hg_int).mp hg_int0
    have hg_cont : Continuous g := by
      dsimp [g]
      exact ((continuous_id.sub continuous_const).mul
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub continuous_const)).mul
        ((Complex.continuous_re.comp (hqd.continuous.comp Complex.continuous_ofReal)).pow 2)
    have hg_zero : ∀ u : ℝ, g u = 0 := fun u =>
      congrFun ((Continuous.ae_eq_iff_eq volume hg_cont continuous_const).mp hae) u
    have hq_ivl : ∀ x : ℝ, τ + 1 < x → x < τ + 2 → q (x : ℂ) = 0 := by
      intro x hx1 _
      have hx_gt : τ < x := by linarith
      have hg0 := hg_zero x
      dsimp [g] at hg0
      have hf1 : x - τ ≠ 0 := (sub_pos.mpr hx_gt).ne'
      have hf2 : Real.exp (y * x) - Real.exp (y * τ) ≠ 0 :=
        (sub_pos.mpr (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hx_gt hy))).ne'
      have hsq0 : (q (x : ℂ)).re ^ 2 = 0 := (mul_eq_zero.mp hg0).resolve_left (mul_ne_zero hf1 hf2)
      exact Complex.ext (sq_eq_zero_iff.mp hsq0) (hq_real x)
    have hq_all0 := airy_entire_eq_zero_of_real_interval hqd (by linarith : τ + 1 < τ + 2) hq_ivl
    obtain ⟨z₀, hz₀⟩ := hq_nz
    exact hz₀ (hq_all0 z₀)
  have hHp_nz : ∃ z : ℂ, H_p z ≠ 0 := by
    by_contra hall0
    push Not at hall0
    have hpos1 := hHp_lap_pos 1 one_pos
    unfold laplaceL at hpos1
    simp [hall0] at hpos1
  have hHp_wit : IsAiryWeakWitness (S : Set ℝ) τ H_p := by
    refine ⟨hHp_class, hHp_nz, ?_, ?_, ?_⟩
    · intro s hs
      dsimp [H_p]
      rw [hq_sites s hs, zero_pow two_ne_zero, mul_zero, Complex.zero_re]
    · intro u hu
      rw [hHp_re u]
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu) (sq_nonneg _)
    · intro y hy
      unfold airyLaplace
      refine mul_nonneg (Real.exp_pos _).le ?_
      rcases hy.eq_or_lt with rfl | hypos
      · simp [hHp_int0]
      · exact (hHp_lap_pos y hypos).le
  exact ⟨q, hqd, hqeq, hsq_class, hint_q2, hint_zq2, hquot_eq, hHp_wit, hHp_int0, hHp_lap_pos⟩

/-! ### Enlargement monotonicity and algebraic strictness `τ_T(S) < λ(S)` -/

/-- Enlarging `T` preserves every trial `q_p` on multiplying `p` by `∏_{n ∈ T₂ \ T₁} (X - C t_n)`,
so `hbNodePolySpace` stays nontrivial and `hbNodeTau` is nondecreasing. -/
theorem hbNodeTau_mono (D : ShellHBData) {t : ℕ → ℝ} (ht : IsHbZeroEnum D.P D.Q t)
    (hm : 2 ≤ D.S.card) {S : Finset ℝ} {T₁ T₂ : Finset ℕ} (hsub : T₁ ⊆ T₂)
    (hT₂1 : ∀ n ∈ T₂, 1 ≤ n) (hT₁card : D.S.card / 2 + 1 ≤ T₁.card)
    (hne₁ : ∃ p ∈ hbNodePolySpace D t S T₁, p ≠ 0) :
    (∃ p ∈ hbNodePolySpace D t S T₂, p ≠ 0) ∧
    hbNodeTau D t S T₁ ≤ hbNodeTau D t S T₂ := by
  classical
  have hT₁1 : ∀ n ∈ T₁, 1 ≤ n := fun n hn => hT₂1 n (hsub hn)
  have hT₂card : D.S.card / 2 + 1 ≤ T₂.card := hT₁card.trans (Finset.card_le_card hsub)
  let R_diff : Polynomial ℝ := ∏ n ∈ T₂ \ T₁, (Polynomial.X - Polynomial.C (hbNode t n))
  have hR_monic : R_diff.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun n _ => Polynomial.monic_X_sub_C _
  have hR_deg : R_diff.natDegree = (T₂ \ T₁).card := by
    rw [Polynomial.natDegree_prod_of_monic _ _ fun n _ => Polynomial.monic_X_sub_C _]
    simp
  have hcard_sdiff : T₁.card + (T₂ \ T₁).card = T₂.card := by
    have h := Finset.card_union_of_disjoint (Finset.disjoint_sdiff (s := T₁) (t := T₂))
    rw [Finset.union_sdiff_of_subset hsub] at h
    omega
  have lift_poly : ∀ p₁ ∈ hbNodePolySpace D t S T₁, p₁ ≠ 0 →
      p₁ * R_diff ∈ hbNodePolySpace D t S T₂ ∧ p₁ * R_diff ≠ 0 ∧
      hbNodePolyQuotient D t T₂ (p₁ * R_diff) = hbNodePolyQuotient D t T₁ p₁ := by
    intro p₁ hp₁ hp₁0
    have hmul_ne : p₁ * R_diff ≠ 0 := mul_ne_zero hp₁0 hR_monic.ne_zero
    have hmul_mem : p₁ * R_diff ∈ hbNodePolySpace D t S T₂ := by
      refine ⟨?_, fun s hs hcond => ?_⟩
      · rw [Polynomial.natDegree_mul hp₁0 hR_monic.ne_zero, hR_deg]
        have hd₁ : p₁.natDegree ≤ T₁.card - D.S.card / 2 - 1 := hp₁.1
        omega
      · rw [Polynomial.eval_mul]
        rcases hcond with hN0 | hsT₂
        · rw [hp₁.2 s hs (Or.inl hN0), zero_mul]
        · by_cases hsT₁ : s ∈ T₁.image (hbNode t)
          · rw [hp₁.2 s hs (Or.inr hsT₁), zero_mul]
          · obtain ⟨n, hn₂, rfl⟩ := Finset.mem_image.1 hsT₂
            have hn_not₁ : n ∉ T₁ := fun hn₁ => hsT₁ (Finset.mem_image_of_mem _ hn₁)
            have hn_sdiff : n ∈ T₂ \ T₁ := Finset.mem_sdiff.2 ⟨hn₂, hn_not₁⟩
            have hR0 : R_diff.eval (hbNode t n) = 0 := by
              dsimp [R_diff]
              rw [Polynomial.eval_prod]
              exact Finset.prod_eq_zero hn_sdiff (by simp)
            rw [hR0, mul_zero]
    obtain ⟨q₁, hq₁d, hq₁eq, -, -, -, hquot₁, -, -, -⟩ :=
      exists_hbNodeTrial D ht hm hT₁1 hT₁card hp₁ hp₁0
    obtain ⟨q₂, hq₂d, hq₂eq, -, -, -, hquot₂, -, -, -⟩ :=
      exists_hbNodeTrial D ht hm hT₂1 hT₂card hmul_mem hmul_ne
    have hq_same : q₂ = q₁ := by
      ext z
      refine entire_eq_of_eq_off_finset hq₂d hq₁d (T₂.image (hbNode t)) (fun x hx => ?_) z
      have hpr₂_ne : at47_pr (T₂.image (hbNode t)) (x : ℂ) ≠ 0 := at47_pr_ne_zero hx
      have himg_union : T₂.image (hbNode t) = T₁.image (hbNode t) ∪ (T₂ \ T₁).image (hbNode t) := by
        rw [← Finset.image_union, Finset.union_sdiff_of_subset hsub]
      have hdisj : Disjoint (T₁.image (hbNode t)) ((T₂ \ T₁).image (hbNode t)) := by
        rw [Finset.disjoint_left]
        intro y hy₁ hy₂
        obtain ⟨a, ha₁, rfl⟩ := Finset.mem_image.1 hy₁
        obtain ⟨b, hb_sd, hab⟩ := Finset.mem_image.1 hy₂
        obtain ⟨hb₂, hb_not₁⟩ := Finset.mem_sdiff.1 hb_sd
        exact hb_not₁ (hbNode_injOn ht (hT₂1 b hb₂) (hT₁1 a ha₁) hab ▸ ha₁)
      have hpr_split : at47_pr (T₂.image (hbNode t)) (x : ℂ) =
          at47_pr (T₁.image (hbNode t)) (x : ℂ) * airyPQc R_diff (x : ℂ) := by
        unfold at47_pr
        rw [himg_union, Finset.prod_union hdisj, airyPQc_ofReal]
        congr 1
        rw [Finset.prod_image (fun a ha b hb hab =>
          hbNode_injOn ht (hT₂1 a (Finset.mem_sdiff.1 ha).1) (hT₂1 b (Finset.mem_sdiff.1 hb).1) hab)]
        dsimp [R_diff]
        rw [Polynomial.eval_prod, Complex.ofReal_prod]
        refine Finset.prod_congr rfl fun n _ => by simp
      have heq_mul : q₂ (x : ℂ) * at47_pr (T₂.image (hbNode t)) (x : ℂ) =
          q₁ (x : ℂ) * at47_pr (T₂.image (hbNode t)) (x : ℂ) := by
        rw [hq₂eq, airyPQc_ofReal, Polynomial.eval_mul, Complex.ofReal_mul, ← airyPQc_ofReal,
          ← airyPQc_ofReal, ← mul_assoc, ← hq₁eq, mul_assoc, ← hpr_split]
      exact mul_right_cancel₀ hpr₂_ne heq_mul
    exact ⟨hmul_mem, hmul_ne, hquot₂.symm.trans (hq_same ▸ hquot₁)⟩
  obtain ⟨⟨p₁, ⟨hp₁, hp₁0⟩, hp₁max⟩, _⟩ := isGreatest_hbNodeTau D ht hm hT₁1 hT₁card hne₁
  obtain ⟨hm₂, hne₂, hqeq⟩ := lift_poly p₁ hp₁ hp₁0
  obtain ⟨_, hmax₂⟩ := isGreatest_hbNodeTau D ht hm hT₂1 hT₂card ⟨p₁ * R_diff, hm₂, hne₂⟩
  refine ⟨⟨p₁ * R_diff, hm₂, hne₂⟩, ?_⟩
  rw [← hp₁max, ← hqeq]
  exact hmax₂ ⟨p₁ * R_diff, ⟨hm₂, hne₂⟩, rfl⟩

/-- Every member of `IsAirySquareClass s` equals `(α : ℂ) * airyCardinalSeries c` for a unit
feasible `c` with `α > 0` and `airySquareClassQuotient q = airySquareRayleigh c`
(Dirichlet quadrature argument from `isGreatest_airySquareClass`). -/
private lemma exists_unitFeasible_of_isAirySquareClass {k : ℕ} {s : Fin k → ℝ} {q : ℂ → ℂ}
    (hq : IsAirySquareClass s q) :
    ∃ (c : lp (fun _ : ℕ => ℝ) 2) (α : ℝ),
      0 < α ∧ AirySquareUnitFeasible s c ∧
      (∀ z : ℂ, q z = (α : ℂ) * airyCardinalSeries c z) ∧
      airySquareClassQuotient q = airySquareRayleigh c := by
  obtain ⟨hq_diff, hq_real, hq_nz, hq2, hzq2, hq_sites⟩ := hq
  have hre_sq : ∀ u : ℝ, (q (u : ℂ) ^ 2).re = (q (u : ℂ)).re ^ 2 := fun u =>
    re_sq_of_im_zero (hq_real u)
  have hq2_int : Integrable (fun u : ℝ => (q (u : ℂ)).re ^ 2) :=
    hq2.2.1.re.congr (Eventually.of_forall fun u => by
      dsimp only; rw [RCLike.re_to_complex, hre_sq u])
  have hq2_pos : 0 < ∫ u : ℝ, (q (u : ℂ)).re ^ 2 := by
    by_contra hnot
    have hint0 : (∫ u : ℝ, (q (u : ℂ)).re ^ 2) = 0 :=
      le_antisymm (not_lt.mp hnot) (integral_nonneg fun _ => sq_nonneg _)
    have hae := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hq2_int).mp hint0
    have hcont : Continuous (fun u : ℝ => (q (u : ℂ)).re ^ 2) :=
      (Complex.continuous_re.comp (hq_diff.continuous.comp Complex.continuous_ofReal)).pow 2
    have hre0 : ∀ u : ℝ, (q (u : ℂ)).re = 0 := fun u =>
      sq_eq_zero_iff.mp (congrFun ((Continuous.ae_eq_iff_eq volume hcont continuous_const).mp hae) u)
    have hall0 := airy_entire_eq_zero_of_real_interval hq_diff (by norm_num : (0 : ℝ) < 1)
      fun x _ _ => Complex.ext (hre0 x) (hq_real x)
    obtain ⟨z₀, hz₀⟩ := hq_nz
    exact hz₀ (hall0 z₀)
  let d_raw : ℕ → ℝ := fun n => (q (airyZ n : ℂ)).re / airyAi' (airyZ n)
  have hd_hasSum : HasSum (fun n : ℕ => (d_raw n) ^ 2) (∫ u : ℝ, (q (u : ℂ)).re ^ 2) := by
    have hquad := inAiryClass_quadrature_re hq2
    rw [integral_congr_ae (Eventually.of_forall hre_sq)] at hquad
    refine hquad.congr_fun fun n => ?_
    dsimp [d_raw]
    rw [hre_sq (airyZ n), div_pow]
  have hd_mem : Memℓp d_raw 2 := by
    refine memℓp_gen ?_
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using hd_hasSum.summable
  let d : lp (fun _ : ℕ => ℝ) 2 := ⟨d_raw, hd_mem⟩
  have hqd_mul : InAiryClass (fun z => q z * airyCardinalSeries d z) :=
    InAiryClass.mul_of_sq hq_diff (differentiable_airyCardinalSeries d)
      hq_real (airyCardinalSeries_ofReal_im d) hq2 (airyCardinalSeries_sq_inAiryClass d)
  have hdiff_sq_class : InAiryClass (fun z => (q z - airyCardinalSeries d z) ^ 2) := by
    have heq2 : (fun z => (q z - airyCardinalSeries d z) ^ 2) =
        fun z => (q z ^ 2 - ((2 : ℝ) : ℂ) * (q z * airyCardinalSeries d z)) +
          airyCardinalSeries d z ^ 2 := by ext z; push_cast; ring
    rw [heq2]
    exact (hq2.sub (hqd_mul.smul 2)).add (airyCardinalSeries_sq_inAiryClass d)
  have hdiff_int0 : (∫ u : ℝ, ((q (u : ℂ) - airyCardinalSeries d (u : ℂ)) ^ 2).re) = 0 := by
    have hquad := inAiryClass_quadrature_re hdiff_sq_class
    have h0 : (fun n : ℕ => ((q (airyZ n : ℂ) - airyCardinalSeries d (airyZ n : ℂ)) ^ 2).re /
        airyAi' (airyZ n) ^ 2) = fun _ => 0 := by
      ext n
      rw [airyCardinalSeries_airyZ]
      have hd_n : (d : ℕ → ℝ) n = d_raw n := rfl
      rw [hd_n]
      dsimp [d_raw]
      have hmul_c : (((q (airyZ n : ℂ)).re / airyAi' (airyZ n)) * airyAi' (airyZ n) : ℝ) =
          (q (airyZ n : ℂ)).re := div_mul_cancel₀ _ (airyAi'_airyZ_ne_zero n)
      have hq_n : (((q (airyZ n : ℂ)).re : ℝ) : ℂ) = q (airyZ n : ℂ) :=
        Complex.ext (by simp) (by simp [hq_real (airyZ n)])
      rw [hmul_c, hq_n, sub_self, sq, zero_mul, Complex.zero_re, zero_div]
    rw [h0] at hquad
    exact hquad.unique hasSum_zero
  have hq_eq_qd : ∀ z : ℂ, q z = airyCardinalSeries d z := by
    have hre_diff : ∀ u : ℝ, ((q (u : ℂ) - airyCardinalSeries d (u : ℂ)) ^ 2).re =
        ((q (u : ℂ)).re - airyCardinalSeriesR d u) ^ 2 := by
      intro u
      have him0 : (q (u : ℂ) - airyCardinalSeries d (u : ℂ)).im = 0 := by
        simp [hq_real u, airyCardinalSeries_ofReal_im d u]
      rw [re_sq_of_im_zero him0, Complex.sub_re, airyCardinalSeriesR]
    simp_rw [hre_diff] at hdiff_int0
    have hint_diff : Integrable (fun u : ℝ => ((q (u : ℂ)).re - airyCardinalSeriesR d u) ^ 2) :=
      hdiff_sq_class.2.1.re.congr (Eventually.of_forall fun u => by
        dsimp only; rw [RCLike.re_to_complex, hre_diff u])
    have hae := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hint_diff).mp hdiff_int0
    have hcont : Continuous (fun u : ℝ => ((q (u : ℂ)).re - airyCardinalSeriesR d u) ^ 2) :=
      ((Complex.continuous_re.comp (hq_diff.continuous.comp Complex.continuous_ofReal)).sub
        (continuous_airyCardinalSeriesR d)).pow 2
    have hreal_eq : ∀ u : ℝ, q (u : ℂ) = airyCardinalSeries d (u : ℂ) := by
      intro u
      have hsq0 : ((q (u : ℂ)).re - airyCardinalSeriesR d u) ^ 2 = 0 :=
        congrFun ((Continuous.ae_eq_iff_eq volume hcont continuous_const).mp hae) u
      exact Complex.ext (sub_eq_zero.mp (sq_eq_zero_iff.mp hsq0))
        ((hq_real u).trans (airyCardinalSeries_ofReal_im d u).symm)
    have hsub0 := airy_entire_eq_zero_of_real_interval
      (hq_diff.sub (differentiable_airyCardinalSeries d)) (by norm_num : (0 : ℝ) < 1)
      fun x _ _ => sub_eq_zero.mpr (hreal_eq x)
    exact fun z => sub_eq_zero.mp (hsub0 z)
  have hnum_hasSum : HasSum (fun n : ℕ => airyZ n * (d n) ^ 2)
      (∫ u : ℝ, u * (q (u : ℂ)).re ^ 2) := by
    have hquad := inAiryClass_quadrature_re hzq2
    have hrhs : (∫ u : ℝ, ((u : ℂ) * q (u : ℂ) ^ 2).re) = ∫ u : ℝ, u * (q (u : ℂ)).re ^ 2 :=
      integral_congr_ae (Eventually.of_forall fun u => by
        dsimp only
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hre_sq u])
    rw [hrhs] at hquad
    refine hquad.congr_fun fun n => ?_
    dsimp only
    have hd_n : (d : ℕ → ℝ) n = d_raw n := rfl
    rw [hd_n]
    dsimp [d_raw]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      hre_sq (airyZ n), div_pow, mul_div_assoc]
  have hd_abs_sum : Summable (fun n : ℕ => |airyZ n| * (d n) ^ 2) :=
    (summable_airyZ_mul_sq_iff d).mpr hnum_hasSum.summable
  have hd_ker : ∀ j : Fin k, airyCardinalSeriesR d (s j) = 0 := by
    intro j
    unfold airyCardinalSeriesR
    rw [← hq_eq_qd (s j : ℂ), hq_sites j, Complex.zero_re]
  have hd_norm_sq : ‖d‖ ^ 2 = ∫ u : ℝ, (q (u : ℂ)).re ^ 2 := by
    have h1 := lp.hasSum_norm (p := 2) (by norm_num) d
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] at h1
    exact h1.unique hd_hasSum
  have hd_norm_pos : 0 < ‖d‖ := by nlinarith [hd_norm_sq.symm ▸ hq2_pos, norm_nonneg d]
  let c : lp (fun _ : ℕ => ℝ) 2 := (‖d‖⁻¹ : ℝ) • d
  have hc_feas : AirySquareUnitFeasible s c := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hasSum_sq_one_iff_norm_eq_one]
      change ‖(‖d‖⁻¹ : ℝ) • d‖ = 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd_norm_pos),
        inv_mul_cancel₀ hd_norm_pos.ne']
    · refine (hd_abs_sum.mul_left ((‖d‖⁻¹) ^ 2)).congr fun n => ?_
      simp [c, Pi.smul_apply, smul_eq_mul]; ring
    · rw [← airyEvalMap_eq_zero_iff]
      change airyEvalMap s ((‖d‖⁻¹ : ℝ) • d) = 0
      rw [map_smul, (airyEvalMap_eq_zero_iff s d).mpr hd_ker, smul_zero]
  have hq_smul : ∀ z : ℂ, q z = (‖d‖ : ℂ) * airyCardinalSeries c z := by
    intro z
    rw [hq_eq_qd z]
    have h1 := (airyCardinalSeries_hasSum d z).const_smul (‖d‖⁻¹ : ℂ)
    have h2 : airyCardinalSeries c z = (‖d‖⁻¹ : ℂ) * airyCardinalSeries d z := by
      refine (airyCardinalSeries_hasSum c z).unique ?_
      refine h1.congr_fun fun n => ?_
      simp [c, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [h2, ← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hd_norm_pos.ne', Complex.ofReal_one, one_mul]
  have hquot_eq : airySquareClassQuotient q = airySquareRayleigh c := by
    unfold airySquareClassQuotient airySquareRayleigh
    rw [← hnum_hasSum.tsum_eq, ← hd_norm_sq]
    have hcongr : (fun n : ℕ => airyZ n * (c n) ^ 2) =
        fun n : ℕ => (‖d‖⁻¹) ^ 2 * (airyZ n * (d n) ^ 2) := by
      ext n; simp [c, Pi.smul_apply, smul_eq_mul]; ring
    rw [hcongr, tsum_mul_left, inv_pow, inv_mul_eq_div]
  exact ⟨c, ‖d‖, hd_norm_pos, hc_feas, hq_smul, hquot_eq⟩

/-- **Algebraic strictness (`lem:airy-node-square`, `ce_airy_lp_proofs.tex` lines 516–531):**
whenever `hbNodePolySpace D t S T` is nontrivial (`m ≥ 2`), `τ_T(S) < λ(S)`. -/
theorem hbNodeTau_lt_airyLambdaOf (D : ShellHBData) {t : ℕ → ℝ} (ht : IsHbZeroEnum D.P D.Q t)
    (hm : 2 ≤ D.S.card) {S : Finset ℝ} {T : Finset ℕ} (hT1 : ∀ n ∈ T, 1 ≤ n)
    (hTcard : D.S.card / 2 + 1 ≤ T.card)
    (hne : ∃ p ∈ hbNodePolySpace D t S T, p ≠ 0) :
    hbNodeTau D t S T < airyLambdaOf S := by
  classical
  obtain ⟨⟨p, ⟨hp, hp0⟩, hpmax⟩, _⟩ := isGreatest_hbNodeTau D ht hm hT1 hTcard hne
  obtain ⟨q, hqd, hqeq, hsq_class, -, -, hquot_eq, -, -, -⟩ :=
    exists_hbNodeTrial D ht hm hT1 hTcard hp hp0
  have hs_inj := airySites_injective S
  have hle : hbNodeTau D t S T ≤ airyLambdaOf S := by
    rw [← hpmax, ← hquot_eq]
    exact (isGreatest_airySquareClass hs_inj).2 ⟨q, hsq_class, rfl⟩
  refine lt_of_le_of_ne hle fun heq_lam => ?_
  obtain ⟨c, α, hα_pos, hc_feas, hq_smul, hq_ray⟩ := exists_unitFeasible_of_isAirySquareClass hsq_class
  have hc_max : airySquareRayleigh c = airyLambda (airySites S) := by
    rw [← hq_ray, hquot_eq, hpmax, heq_lam]
    rfl
  obtain ⟨μ, -, -, -, -, -, hrep⟩ := airySquare_maximizer_representation hs_inj hc_feas hc_max
  let lam : ℝ := airyLambdaOf S
  let C₀ : ℝ := ∑' n : ℕ, c n
  -- Polynomials `polyT(X) = ∏_{a ∈ A_T} (X - a)` and `polyS(X) = ∏_{s ∈ S} (X - s)`.
  let A_T : Finset ℝ := T.image (hbNode t)
  let polyT : ℝ[X] := ∏ a ∈ A_T, (Polynomial.X - Polynomial.C a)
  let polyS : ℝ[X] := ∏ s ∈ S, (Polynomial.X - Polynomial.C s)
  let polySj : Fin S.card → ℝ[X] := fun j =>
    ∏ s ∈ S.erase (airySites S j), (Polynomial.X - Polynomial.C s)
  have hpolyS_split : ∀ j : Fin S.card,
      polyS = (Polynomial.X - Polynomial.C (airySites S j)) * polySj j := by
    intro j
    have hjS : airySites S j ∈ S := by
      have hmem : airySites S j ∈ Set.range (airySites S) := ⟨j, rfl⟩
      rwa [range_airySites] at hmem
    dsimp [polyS, polySj]
    exact (Finset.mul_prod_erase S (fun s => Polynomial.X - Polynomial.C s) hjS).symm
  -- Check exact sign of `(x - s_j) * airyKerC x s_j` for `x ∉ S`.
  -- `airyKerC x s_j = (Ai(x) Ai'(s_j) - Ai'(x) Ai(s_j)) / (x - s_j)`.
  have hker_real : ∀ (j : Fin S.card) (x : ℝ), x ∉ S →
      ((x - airySites S j : ℝ) : ℂ) * airyKerC (x : ℂ) (airySites S j : ℂ) =
        ((airyAi x * airyAi' (airySites S j) - airyAi' x * airyAi (airySites S j) : ℝ) : ℂ) := by
    intro j x hxS
    have hjS : airySites S j ∈ S := by
      have hmem : airySites S j ∈ Set.range (airySites S) := ⟨j, rfl⟩
      rwa [range_airySites] at hmem
    have hne : (x : ℂ) ≠ (airySites S j : ℂ) := fun h => hxS (Complex.ofReal_injective h ▸ hjS)
    rw [airyKerC_of_ne hne, airyKernelXY, airyAiC_ofReal, airyAiC_ofReal,
      deriv_airyAiC_ofReal, deriv_airyAiC_ofReal]
    have hsub_ne : (x : ℂ) - (airySites S j : ℂ) ≠ 0 := sub_ne_zero.mpr hne
    have hcast : ((x - airySites S j : ℝ) : ℂ) = (x : ℂ) - (airySites S j : ℂ) := by push_cast; rfl
    rw [hcast, mul_div_cancel₀ _ hsub_ne]
    push_cast; ring
  -- Construct `A_poly, B_poly ∈ ℝ[X]` with `A_poly(x) Ai(x) + B_poly(x) Ai'(x) = 0` for all `x ∉ S`.
  let A_poly : ℝ[X] :=
    (Polynomial.X - Polynomial.C lam) * polyS * p * D.P -
      polyT * (Polynomial.C (α * C₀) * polyS +
        ∑ j : Fin S.card, Polynomial.C (α * μ j * airyAi' (airySites S j)) * polySj j)
  let B_poly : ℝ[X] :=
    (Polynomial.X - Polynomial.C lam) * polyS * p * D.Q +
      polyT * (∑ j : Fin S.card, Polynomial.C (α * μ j * airyAi (airySites S j)) * polySj j)
  have hAB_eq : ∀ x : ℝ, x ∉ S → A_poly.eval x * airyAi x + B_poly.eval x * airyAi' x = 0 := by
    intro x hxS
    -- Multiply `(x - lam) * q(x) = α * ((x - lam) * q_c(x))` by `polyT(x) * polyS(x)` in `ℂ`.
    have hlhs : (((x - lam) * polyS.eval x * polyT.eval x : ℝ) : ℂ) * q (x : ℂ) =
        (((x - lam) * polyS.eval x * p.eval x *
          (D.P.eval x * airyAi x + D.Q.eval x * airyAi' x) : ℝ) : ℂ) := by
      have hpolyT_eq : ((polyT.eval x : ℝ) : ℂ) = at47_pr A_T (x : ℂ) := by
        dsimp [polyT]
        rw [Polynomial.eval_prod, at47_pr_ofReal]
        exact congrArg Complex.ofReal (Finset.prod_congr rfl fun a _ => by simp)
      have h := hqeq (x : ℂ)
      rw [airyPQN_ofReal, airyPQc_ofReal] at h
      calc (((x - lam) * polyS.eval x * polyT.eval x : ℝ) : ℂ) * q (x : ℂ)
          = (((x - lam) * polyS.eval x : ℝ) : ℂ) * (q (x : ℂ) * at47_pr A_T (x : ℂ)) := by
            rw [← hpolyT_eq]; push_cast; ring
        _ = (((x - lam) * polyS.eval x : ℝ) : ℂ) *
              (((D.P.eval x * airyAi x + D.Q.eval x * airyAi' x : ℝ) : ℂ) *
                ((Polynomial.eval x p : ℝ) : ℂ)) := by
            rw [h]
        _ = _ := by push_cast; ring
    have hrhs : (((x - lam) * polyS.eval x * polyT.eval x : ℝ) : ℂ) * q (x : ℂ) =
        ((polyT.eval x * (α * C₀ * polyS.eval x * airyAi x +
          ∑ j : Fin S.card, α * μ j * (polySj j).eval x *
            (airyAi x * airyAi' (airySites S j) - airyAi' x * airyAi (airySites S j))) : ℝ) : ℂ) := by
      rw [hq_smul (x : ℂ)]
      have hrep_x := hrep (x : ℂ)
      change ((x : ℂ) - (lam : ℂ)) * airyCardinalSeries c (x : ℂ) =
        (C₀ : ℂ) * airyAiC (x : ℂ) +
          ∑ j : Fin S.card, (μ j : ℂ) * airyKerC (x : ℂ) (airySites S j : ℂ) at hrep_x
      have hstep : (((x - lam) * polyS.eval x * polyT.eval x : ℝ) : ℂ) *
          ((α : ℂ) * airyCardinalSeries c (x : ℂ)) =
          ((polyT.eval x : ℝ) : ℂ) * (α : ℂ) * (((polyS.eval x : ℝ) : ℂ) *
            (((x : ℂ) - (lam : ℂ)) * airyCardinalSeries c (x : ℂ))) := by
        push_cast; ring
      rw [hstep, hrep_x, mul_add, Finset.mul_sum, airyAiC_ofReal]
      have hsum_eq : (∑ j : Fin S.card, ((polyS.eval x : ℝ) : ℂ) *
          ((μ j : ℂ) * airyKerC (x : ℂ) (airySites S j : ℂ))) =
          ∑ j : Fin S.card, (((μ j * (polySj j).eval x *
            (airyAi x * airyAi' (airySites S j) - airyAi' x * airyAi (airySites S j)) : ℝ) : ℂ)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have hpolySj : ((polyS.eval x : ℝ) : ℂ) =
            ((x - airySites S j : ℝ) : ℂ) * (((polySj j).eval x : ℝ) : ℂ) := by
          conv_lhs => rw [hpolyS_split j]
          rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
            Complex.ofReal_mul]
        rw [hpolySj]
        calc (((x - airySites S j : ℝ) : ℂ) * (((polySj j).eval x : ℝ) : ℂ)) *
              ((μ j : ℂ) * airyKerC (x : ℂ) (airySites S j : ℂ))
            = (μ j : ℂ) * (((polySj j).eval x : ℝ) : ℂ) *
                (((x - airySites S j : ℝ) : ℂ) * airyKerC (x : ℂ) (airySites S j : ℂ)) := by ring
          _ = (μ j : ℂ) * (((polySj j).eval x : ℝ) : ℂ) *
                ((airyAi x * airyAi' (airySites S j) - airyAi' x * airyAi (airySites S j) : ℝ) : ℂ) := by
              rw [hker_real j x hxS]
          _ = _ := by push_cast; ring
      rw [hsum_eq, ← Complex.ofReal_sum]
      have hα_sum : α * ∑ j : Fin S.card, μ j * (polySj j).eval x *
          (airyAi x * airyAi' (airySites S j) - airyAi' x * airyAi (airySites S j)) =
          ∑ j : Fin S.card, α * μ j * (polySj j).eval x *
            (airyAi x * airyAi' (airySites S j) - airyAi' x * airyAi (airySites S j)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [← hα_sum]
      push_cast
      ring
    have heq_re := congrArg Complex.re (hlhs.symm.trans hrhs)
    simp only [Complex.ofReal_re] at heq_re
    have eval_sum_Sj1 : (∑ j : Fin S.card, Polynomial.C (α * μ j * airyAi' (airySites S j)) * polySj j).eval x =
        ∑ j : Fin S.card, α * μ j * airyAi' (airySites S j) * (polySj j).eval x := by
      rw [← Polynomial.coe_evalRingHom, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C]
    have eval_sum_Sj2 : (∑ j : Fin S.card, Polynomial.C (α * μ j * airyAi (airySites S j)) * polySj j).eval x =
        ∑ j : Fin S.card, α * μ j * airyAi (airySites S j) * (polySj j).eval x := by
      rw [← Polynomial.coe_evalRingHom, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C]
    dsimp [A_poly, B_poly]
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, eval_sum_Sj1, eval_sum_Sj2]
    have hlin : ((x - lam) * polyS.eval x * p.eval x * D.P.eval x -
        polyT.eval x * (α * C₀ * polyS.eval x +
          ∑ j : Fin S.card, α * μ j * airyAi' (airySites S j) * (polySj j).eval x)) * airyAi x +
        ((x - lam) * polyS.eval x * p.eval x * D.Q.eval x +
          polyT.eval x * ∑ j : Fin S.card, α * μ j * airyAi (airySites S j) * (polySj j).eval x) *
            airyAi' x =
        (x - lam) * polyS.eval x * p.eval x * (D.P.eval x * airyAi x + D.Q.eval x * airyAi' x) -
        polyT.eval x * (α * C₀ * polyS.eval x * airyAi x +
          ∑ j : Fin S.card, α * μ j * (polySj j).eval x *
            (airyAi x * airyAi' (airySites S j) - airyAi' x * airyAi (airySites S j))) := by
      have hsum_split : (∑ j : Fin S.card, α * μ j * (polySj j).eval x *
          (airyAi x * airyAi' (airySites S j) - airyAi' x * airyAi (airySites S j))) =
          (∑ j : Fin S.card, α * μ j * airyAi' (airySites S j) * (polySj j).eval x) * airyAi x -
            (∑ j : Fin S.card, α * μ j * airyAi (airySites S j) * (polySj j).eval x) * airyAi' x := by
        rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hsum_split]
      ring
    rw [hlin, sub_eq_zero]
    exact heq_re
  -- Deduce `B_poly = 0` by evaluating at infinitely many Airy zeros `airyZ k ∉ S`.
  have hB_zero : B_poly = 0 := by
    by_contra hB_ne
    let N_roots : ℕ := B_poly.natDegree + S.card + 1
    have hsub_roots : ((Finset.range N_roots).image airyZ \ S) ⊆ B_poly.roots.toFinset := by
      intro x hx
      obtain ⟨hx_img, hxS⟩ := Finset.mem_sdiff.1 hx
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hx_img
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hB_ne, Polynomial.IsRoot]
      have h0 := hAB_eq (airyZ k) hxS
      rw [airyAi_airyZ, mul_zero, zero_add] at h0
      exact (mul_eq_zero.mp h0).resolve_right (airyAi'_airyZ_ne_zero k)
    have hc1 : ((Finset.range N_roots).image airyZ).card = N_roots :=
      (Finset.card_image_of_injective _ airyZ_injective).trans (Finset.card_range _)
    have hc2 := Finset.card_sdiff_add_card_inter ((Finset.range N_roots).image airyZ) S
    have hc3 : (((Finset.range N_roots).image airyZ) ∩ S).card ≤ S.card :=
      Finset.card_le_card Finset.inter_subset_right
    have hc4 : ((Finset.range N_roots).image airyZ \ S).card ≤ B_poly.natDegree :=
      (Finset.card_le_card hsub_roots).trans
        ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' B_poly))
    omega
  -- Deduce `A_poly = 0` from `A_poly(x) * airyAi x = 0` on `(M_S, ∞)` where `airyAi x > 0`.
  have hA_zero : A_poly = 0 := by
    by_contra hA_ne
    let M_S : ℝ := (∑ s ∈ S, |s|) + 1
    let pts : Finset ℝ := (Finset.range (A_poly.natDegree + 1)).image (fun k : ℕ => M_S + (k : ℝ))
    have hpts_card : pts.card = A_poly.natDegree + 1 := by
      refine (Finset.card_image_of_injective _ fun a b hab => ?_).trans (Finset.card_range _)
      exact Nat.cast_injective (add_left_cancel hab)
    have hsub_roots : pts ⊆ A_poly.roots.toFinset := by
      intro x hx
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hx
      have hx_pos : 0 < M_S + (k : ℝ) := by
        have hnn : 0 ≤ ∑ s ∈ S, |s| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        positivity
      have hxS : M_S + (k : ℝ) ∉ S := by
        intro hxS
        have hle : |M_S + (k : ℝ)| ≤ ∑ s ∈ S, |s| :=
          Finset.single_le_sum (f := fun s => |s|) (fun _ _ => abs_nonneg _) hxS
        rw [abs_of_pos hx_pos] at hle
        dsimp [M_S] at hle
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      have h0 := hAB_eq (M_S + (k : ℝ)) hxS
      rw [hB_zero, Polynomial.eval_zero, zero_mul, add_zero] at h0
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hA_ne, Polynomial.IsRoot]
      exact (mul_eq_zero.mp h0).resolve_right (airyAi_pos hx_pos.le).ne'
    have hc4 : pts.card ≤ A_poly.natDegree :=
      (Finset.card_le_card hsub_roots).trans
        ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' A_poly))
    omega
  -- Evaluate `A_poly = 0` and `B_poly = 0` at every `t_n` (`n ∈ T`).
  have hroot_T : ∀ n ∈ T, ((Polynomial.X - Polynomial.C lam) * p).eval (hbNode t n) = 0 := by
    intro n hn
    have ha_mem : hbNode t n ∈ A_T := Finset.mem_image_of_mem _ hn
    have hpolyT0 : polyT.eval (hbNode t n) = 0 := by
      dsimp [polyT]; rw [Polynomial.eval_prod]; exact Finset.prod_eq_zero ha_mem (by simp)
    have hA0 : ((hbNode t n - lam) * polyS.eval (hbNode t n) * p.eval (hbNode t n)) *
        D.P.eval (hbNode t n) = 0 := by
      have h := congrArg (Polynomial.eval (hbNode t n)) hA_zero
      dsimp [A_poly] at h
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_zero, hpolyT0, zero_mul, sub_zero] at h
      exact h
    have hB0 : ((hbNode t n - lam) * polyS.eval (hbNode t n) * p.eval (hbNode t n)) *
        D.Q.eval (hbNode t n) = 0 := by
      have h := congrArg (Polynomial.eval (hbNode t n)) hB_zero
      dsimp [B_poly] at h
      simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_zero, hpolyT0, zero_mul, add_zero] at h
      exact h
    have hprod0 : (hbNode t n - lam) * polyS.eval (hbNode t n) * p.eval (hbNode t n) = 0 := by
      rcases hb_real_not_both_zero D.hHB (hbNode t n) with hPne | hQne
      · exact (mul_eq_zero.mp hA0).resolve_right hPne
      · exact (mul_eq_zero.mp hB0).resolve_right hQne
    rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    by_cases hsS : hbNode t n ∈ S
    · rw [hp.2 _ hsS (Or.inr ha_mem), mul_zero]
    · have hpolyS_ne : polyS.eval (hbNode t n) ≠ 0 := by
        dsimp [polyS]; rw [Polynomial.eval_prod]
        refine Finset.prod_ne_zero_iff.2 fun s hs => ?_
        rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        refine sub_ne_zero.2 fun heq => ?_
        have hns : hbNode t n = s := heq
        exact hsS (hns ▸ hs)
      rcases mul_eq_zero.mp hprod0 with h1 | hp_z
      · rw [(mul_eq_zero.mp h1).resolve_right hpolyS_ne, zero_mul]
      · rw [hp_z, mul_zero]
  -- Count roots of `(X - C lam) * p` vs its degree `≤ T.card - e < T.card`.
  let Q_poly : ℝ[X] := (Polynomial.X - Polynomial.C lam) * p
  have hQ_ne : Q_poly ≠ 0 := mul_ne_zero (Polynomial.X_sub_C_ne_zero lam) hp0
  have hsub_AT : A_T ⊆ Q_poly.roots.toFinset := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hQ_ne, Polynomial.IsRoot]
    exact hroot_T n hn
  have hAT_card : A_T.card = T.card :=
    Finset.card_image_of_injOn fun a ha b hb hab => hbNode_injOn ht (hT1 a ha) (hT1 b hb) hab
  have hcard_le : T.card ≤ Q_poly.natDegree := by
    rw [← hAT_card]
    exact (Finset.card_le_card hsub_AT).trans
      ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' Q_poly))
  have hQ_deg : Q_poly.natDegree = 1 + p.natDegree := by
    dsimp [Q_poly]
    rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero lam) hp0, Polynomial.natDegree_X_sub_C]
  have hp_deg : p.natDegree ≤ T.card - D.S.card / 2 - 1 := hp.1
  omega

/-! ### Bundled `lem:airy-node-square` and `T_0 = {m, …, m + e}` specialization -/

/-- **`lem:airy-node-square` (finite-`T` package, `ce_airy_lp_proofs.tex` lines 473–497).**
For strict Hermite–Biehler data `D` with `m = D.S.card ≥ 2`, zero enumeration `t`, any finite real
site set `S`, and any finite `T ⊆ ℕ_{≥ 1}` with `|T| ≥ ⌊m/2⌋ + 1` and `hbNodePolySpace D t S T`
nontrivial:
1. `τ_T(S) = hbNodeTau D t S T` is attained (`IsGreatest`);
2. `τ_T(S) < λ(S) = airyLambdaOf S`;
3. `τ_T(S)` is nondecreasing under enlargement `T ⊆ T'`;
4. for every optimizer `p`, the entire function `q_p = N p / ∏_{n ∈ T} (u - t_n)` lies in
   `IsAirySquareClass (airySites S)` with Rayleigh quotient `τ_T(S)`, and `(u - τ_T(S)) q_p²` is a
   zero-mass weak witness at `τ_T(S)` with strictly positive Laplace transform on `(0, ∞)`. -/
theorem lem_airy_node_square (D : ShellHBData) {t : ℕ → ℝ} (ht : IsHbZeroEnum D.P D.Q t)
    (hm : 2 ≤ D.S.card) (S : Finset ℝ) {T : Finset ℕ} (hT1 : ∀ n ∈ T, 1 ≤ n)
    (hTcard : D.S.card / 2 + 1 ≤ T.card)
    (hne : ∃ p ∈ hbNodePolySpace D t S T, p ≠ 0) :
    IsGreatest (hbNodePolyQuotient D t T '' {p : ℝ[X] | p ∈ hbNodePolySpace D t S T ∧ p ≠ 0})
      (hbNodeTau D t S T) ∧
    hbNodeTau D t S T < airyLambdaOf S ∧
    (∀ T' : Finset ℕ, T ⊆ T' → (∀ n ∈ T', 1 ≤ n) →
      (∃ p ∈ hbNodePolySpace D t S T', p ≠ 0) ∧ hbNodeTau D t S T ≤ hbNodeTau D t S T') ∧
    (∀ p ∈ hbNodePolySpace D t S T, p ≠ 0 → hbNodePolyQuotient D t T p = hbNodeTau D t S T →
      ∃ q : ℂ → ℂ,
        Differentiable ℂ q ∧
        (∀ z : ℂ, q z * at47_pr (T.image (hbNode t)) z = airyPQN D.P D.Q z * airyPQc p z) ∧
        IsAirySquareClass (airySites S) q ∧
        airySquareClassQuotient q = hbNodeTau D t S T ∧
        IsAiryWeakWitness (S : Set ℝ) (hbNodeTau D t S T)
          (fun z => (z - (hbNodeTau D t S T : ℂ)) * q z ^ 2) ∧
        (∫ u : ℝ, (((u : ℂ) - (hbNodeTau D t S T : ℂ)) * q (u : ℂ) ^ 2).re) = 0 ∧
        (∀ y : ℝ, 0 < y →
          0 < laplaceL (fun u => (((u : ℂ) - (hbNodeTau D t S T : ℂ)) * q (u : ℂ) ^ 2).re) y)) := by
  refine ⟨isGreatest_hbNodeTau D ht hm hT1 hTcard hne,
    hbNodeTau_lt_airyLambdaOf D ht hm hT1 hTcard hne,
    fun T' hsub hT'1 => hbNodeTau_mono D ht hm hsub hT'1 hTcard hne,
    fun p hp hp0 hpmax => ?_⟩
  obtain ⟨q, hqd, hqeq, hsq, -, -, hquot, hwit, hint0, hlap⟩ :=
    exists_hbNodeTrial D ht hm hT1 hTcard hp hp0
  rw [hpmax] at hquot hwit hint0 hlap
  exact ⟨q, hqd, hqeq, hsq, hquot, hwit, hint0, hlap⟩

/-- **`lem:airy-node-square` (`T_0 = {m, …, m + e}` constant-polynomial bound,
`ce_airy_lp_proofs.tex` line 495 / `ce_canonical_iff.tex` `eq:hb-node-bound`).**
For `m = D.S.card ≥ 2` and the zero enumeration `t` (`ht : IsHbZeroEnum D.P D.Q t`),
`t_{m+e} < τ_N < λ(t_1, …, t_{m-1})`. This proves the former `airy_node_square` field of
`CeCanonicalInputs` (with the implicit enumeration hypothesis `ht : IsHbZeroEnum D.P D.Q t`
made explicit). -/
theorem airy_node_square (D : ShellHBData) {t : ℕ → ℝ} (ht : IsHbZeroEnum D.P D.Q t)
    (hm : 2 ≤ D.S.card) :
    hbTauN D t < airyLambdaOf (shellSites D) ∧
    hbNode t (D.S.card + D.S.card / 2) < hbTauN D t := by
  let T₀ : Finset ℕ := Finset.Icc D.S.card (D.S.card + D.S.card / 2)
  have hT₀1 : ∀ n ∈ T₀, 1 ≤ n := fun n hn => by
    have := (Finset.mem_Icc.1 hn).1; omega
  have hT₀_card : T₀.card = D.S.card / 2 + 1 := by
    dsimp [T₀]; rw [Nat.card_Icc]; omega
  have h1_mem : (1 : ℝ[X]) ∈ hbNodePolySpace D t (shellSites D) T₀ := by
    refine ⟨by simp, fun s hs hcond => ?_⟩
    exfalso
    obtain ⟨hs_ne_tm, hsS⟩ := Finset.mem_erase.1 hs
    have hs_Nf0 : at47_Nf D.P D.Q s = 0 := (nodeZero_iff D s).1 (D.S_zero hsS)
    rcases hcond with hN_ne | hs_img
    · exact hN_ne hs_Nf0
    · obtain ⟨n, hnT₀, rfl⟩ := Finset.mem_image.1 hs_img
      have hn_ge : D.S.card ≤ n := (Finset.mem_Icc.1 hnT₀).1
      have htm_lt : D.tm < hbNode t n := lt_of_le_of_ne (D.tm_min _ hsS) hs_ne_tm.symm
      rw [D.tm_eq_hbNode ht] at htm_lt
      have hle : hbNode t n ≤ hbNode t D.S.card := by
        unfold hbNode
        exact ht.1.antitone (by omega)
      linarith
  have hne : ∃ p ∈ hbNodePolySpace D t (shellSites D) T₀, p ≠ 0 :=
    ⟨1, h1_mem, one_ne_zero⟩
  have hτ_le : hbTauN D t ≤ hbNodeTau D t (shellSites D) T₀ := by
    have hq1 : hbTauN D t = hbNodePolyQuotient D t T₀ 1 := by
      unfold hbTauN
      exact (hbNodePolyQuotient_one D t T₀).symm
    rw [hq1]
    exact (isGreatest_hbNodeTau D ht hm hT₀1 hT₀_card.ge hne).2 ⟨1, ⟨h1_mem, one_ne_zero⟩, rfl⟩
  have hτ_lt_lam : hbTauN D t < airyLambdaOf (shellSites D) :=
    hτ_le.trans_lt (hbNodeTau_lt_airyLambdaOf D ht hm hT₀1 hT₀_card.ge hne)
  -- Lower bound `t_{m+e} < τ_N`: positive-weight average over `{m, …, m+e}` with `t_m > t_{m+e}`.
  have ht_lt_τ : hbNode t (D.S.card + D.S.card / 2) < hbTauN D t := by
    unfold hbTauN hbNodeSquareBound
    have hw : ∀ n ∈ T₀, 0 < hbNodeWeight D.P D.Q t T₀ n := fun n hn => hbNodeWeight_pos D ht hm hn
    have hmT : D.S.card ∈ T₀ := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
    have hsum : 0 < ∑ n ∈ T₀, hbNodeWeight D.P D.Q t T₀ n := Finset.sum_pos hw ⟨_, hmT⟩
    rw [lt_div_iff₀ hsum, Finset.mul_sum]
    refine Finset.sum_lt_sum (fun n hn => ?_) ⟨D.S.card, hmT, ?_⟩
    · have hn_le : n ≤ D.S.card + D.S.card / 2 := (Finset.mem_Icc.1 hn).2
      have h : hbNode t (D.S.card + D.S.card / 2) ≤ hbNode t n := by
        unfold hbNode
        exact ht.1.antitone (by omega)
      nlinarith [hw n hn]
    · have h : hbNode t (D.S.card + D.S.card / 2) < hbNode t D.S.card := by
        unfold hbNode
        exact ht.1 (by omega)
      nlinarith [hw _ hmT]
  exact ⟨hτ_lt_lam, ht_lt_τ⟩

/-- info: 'FormalResearch.SignUncertainty.lem_airy_node_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.lem_airy_node_square

/-- info: 'FormalResearch.SignUncertainty.airy_node_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.airy_node_square

end FormalResearch.SignUncertainty
