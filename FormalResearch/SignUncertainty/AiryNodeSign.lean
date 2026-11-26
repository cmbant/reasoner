module

public import FormalResearch.SignUncertainty.CeTerminalDeflation

/-!
# Node-sign and cumulative node-sum criteria (`thm:airy-node-sign`, `ce_airy_lp_proofs.tex`)

Source: `CFT/sign_uncertainty/paper/ce_airy_lp_proofs.tex` (`thm:airy-node-sign`, lines 607–643)
and `ce_canonical_iff.tex` (`thm:ce-canonical-iff` (2), lines 40–48).

Main results:

* **`airy_node_sum`** (`thm:airy-node-sign`, cumulative node-sum criterion): for any
  `D : ShellHBData` with zero enumeration `ht : IsHbZeroEnum D.P D.Q t`, `b = u_LP < t_m`, and weak
  optimizer `H`, if there exists `c ∈ [b, t_m)` with `H(c) = 0`, `H(t_n) ≤ 0` for `t_n < c`,
  `H'(c) ≥ 0` if `c` is a node, and nonnegative cumulative node sums `A(x) = ∑_{c < t_n ≤ x} η_n ≥ 0`
  (`η_n = D(t_n) H(t_n) / N'(t_n)²`) for all `x > c`, then `u_sh = b`. (Proved via
  `deflation_inAiryClass`, `hb_real_quadrature`, finite Abel partial summation on `{n | t_n > c}`,
  and `airy_active_height` parts (3) and (4); for `c > b` no optimizer can satisfy the hypotheses,
  recorded separately as `not_exists_airy_node_sum_gt`.)
* `airy_node_single_block`: single-block sign-pattern specialization (`t_n < c ⇒ H ≤ 0`,
  `c < t_n ≤ d ⇒ H ≥ 0`, `d < t_n ⇒ H ≤ 0`).
* **`airy_node_sign`** (`thm:airy-node-sign`):
  (1) if `b = u_LP < t_m` and an optimizer `H` has no triple of nodes `t₁ < t₂ < t₃` in `(b, t_m]`
      with `H(t₁) > 0`, `H(t₂) < 0`, `H(t₃) > 0`, then `u_sh = b`;
  (2) in particular `u_sh = b` whenever `t_{m+2} ≤ b = u_LP < t_m` (optimizer existence from
      `one_profile_envelope_aux` and `one_profile_maximizer_exists`).

These theorems discharge the former `node_sum` and `node_sign` fields of `CeCanonicalInputs`
(making the implicit zero-enumeration hypothesis `ht : IsHbZeroEnum D.P D.Q t` explicit where `t`
appears).
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-! ### Series bounds off a finite set and finite Abel summation by parts -/

private lemma sum_le_of_hasSum_nonneg_off {f : ℕ → ℝ} {I : ℝ} (hf : HasSum f I)
    (F : Finset ℕ) (h_off : ∀ n : ℕ, n ∉ F → 0 ≤ f n) :
    ∑ n ∈ F, f n ≤ I :=
  sum_le_hasSum F h_off hf

private lemma le_sum_of_hasSum_nonpos_off {f : ℕ → ℝ} {I : ℝ} (hf : HasSum f I)
    (F : Finset ℕ) (h_off : ∀ n : ℕ, n ∉ F → f n ≤ 0) :
    I ≤ ∑ n ∈ F, f n := by
  have h := sum_le_of_hasSum_nonneg_off hf.neg F fun n hn => neg_nonneg.mpr (h_off n hn)
  rw [Finset.sum_neg_distrib] at h
  linarith

/-- Finite Abel summation by parts:
`∑_{j=0}^m a_j d_j = ∑_{j=0}^{m-1} (∑_{i=0}^j a_i) (d_j - d_{j+1}) + (∑_{i=0}^m a_i) d_m`. -/
private lemma sum_range_abel (a d : ℕ → ℝ) (m : ℕ) :
    (∑ j ∈ Finset.range (m + 1), a j * d j) =
      (∑ j ∈ Finset.range m, (∑ i ∈ Finset.range (j + 1), a i) * (d j - d (j + 1))) +
        (∑ i ∈ Finset.range (m + 1), a i) * d m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ (fun j => a j * d j) (m + 1), ih,
      Finset.sum_range_succ (fun j => (∑ i ∈ Finset.range (j + 1), a i) * (d j - d (j + 1))) m,
      Finset.sum_range_succ a (m + 1)]
    ring

private lemma sum_range_mul_nonneg_of_partial_nonneg {a d : ℕ → ℝ} {K : ℕ}
    (hS : ∀ j < K, 0 ≤ ∑ i ∈ Finset.range (j + 1), a i)
    (hd_anti : ∀ j, j + 1 < K → d (j + 1) ≤ d j)
    (hd_nn : ∀ j < K, 0 ≤ d j) :
    0 ≤ ∑ j ∈ Finset.range K, a j * d j := by
  cases K with
  | zero => simp
  | succ m =>
    rw [sum_range_abel a d m]
    refine add_nonneg (Finset.sum_nonneg fun j hj => ?_)
      (mul_nonneg (hS m (Nat.lt_succ_self m)) (hd_nn m (Nat.lt_succ_self m)))
    have hj_lt : j < m := Finset.mem_range.mp hj
    exact mul_nonneg (hS j (Nat.lt_succ_of_lt hj_lt))
      (sub_nonneg.mpr (hd_anti j (Nat.succ_lt_succ hj_lt)))

/-- For a zero enumeration `t` of `D`, the nodes strictly above any threshold `c : ℝ` form an
initial segment `Finset.range K`. -/
private lemma exists_range_eq_nodes_gt (D : ShellHBData) {t : ℕ → ℝ}
    (ht : IsHbZeroEnum D.P D.Q t) (c : ℝ) :
    ∃ K : ℕ, ∀ n : ℕ, c < t n ↔ n < K := by
  classical
  have hex_le : ∃ m : ℕ, t m ≤ c := by
    by_contra hall
    push Not at hall
    have hfin := hb_zeroSet_finite_above D.hHB c
    have hinf : (Set.range t).Infinite :=
      Set.infinite_range_of_injective ht.1.injective
    refine hinf (hfin.subset ?_)
    rintro x ⟨n, rfl⟩
    exact ⟨(ht.2 (t n)).2 ⟨n, rfl⟩, (hall n).le⟩
  let K : ℕ := Nat.find hex_le
  have hK_le : t K ≤ c := Nat.find_spec hex_le
  refine ⟨K, fun n => ⟨fun hgt => ?_, fun hlt => ?_⟩⟩
  · by_contra hn
    have hle : t n ≤ t K := ht.1.antitone (by omega)
    linarith
  · have hnot := Nat.find_min hex_le hlt
    linarith

/-! ### Cumulative node-sum criterion (`thm:airy-node-sign`, general form) -/

/-- Core quotient-integral lower bound of `thm:airy-node-sign`: under the cumulative node-sum
hypotheses at `c`, `0 ≤ ∫_ℝ (H u).re / (u - c)`. -/
private lemma quotient_integral_nonneg_of_node_sum (D : ShellHBData) {t : ℕ → ℝ}
    (ht : IsHbZeroEnum D.P D.Q t) {H : ℂ → ℂ} (hH : InAiryClass H) {c : ℝ}
    (hHc0 : (H (c : ℂ)).re = 0)
    (hbelow : ∀ n : ℕ, t n < c → (H (t n : ℂ)).re ≤ 0)
    (hatc : (∃ n : ℕ, t n = c) → 0 ≤ (deriv H (c : ℂ)).re)
    (hcum : ∀ x : ℝ, c < x → ∀ F : Finset ℕ, (∀ n : ℕ, n ∈ F ↔ (c < t n ∧ t n ≤ x)) →
      0 ≤ ∑ n ∈ F, airyPQDr D.P D.Q (t n) * (H (t n : ℂ)).re /
        ((airyPQN' D.P D.Q (t n : ℂ)).re) ^ 2) :
    0 ≤ ∫ u : ℝ, (H (u : ℂ)).re / (u - c) := by
  obtain ⟨hQc_cl, -, hQc_int_eq⟩ := deflation_inAiryClass hH hHc0
  let Q_c : ℂ → ℂ := dslope H (c : ℂ)
  change InAiryClass Q_c at hQc_cl
  rw [hQc_int_eq]
  have hHc_c : H (c : ℂ) = 0 := Complex.ext hHc0 (hH.2.2.2 c)
  have hQc_of_ne : ∀ u : ℝ, u ≠ c → (Q_c (u : ℂ)).re = (H (u : ℂ)).re / (u - c) := by
    intro u hu
    have hne : (u : ℂ) ≠ (c : ℂ) := fun h => hu (Complex.ofReal_injective h)
    dsimp [Q_c]
    rw [dslope_of_ne _ hne, slope_def_field, hHc_c, sub_zero]
    have hHu : H (u : ℂ) = (((H (u : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl (hH.2.2.2 u)
    conv_lhs => rw [hHu]
    rw [← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re]
  let w : ℕ → ℝ := fun n =>
    airyPQDr D.P D.Q (t n) / ((airyPQN' D.P D.Q (t n : ℂ)).re) ^ 2
  have hw_pos : ∀ n : ℕ, 0 < w n := by
    intro n
    have hz : airyPQN D.P D.Q (t n : ℂ) = 0 := (nodeZero_iff D (t n)).2 ((ht.2 (t n)).2 ⟨n, rfl⟩)
    obtain ⟨hD, hN'⟩ := hb_zero_weight_pos_all D hz
    exact div_pos hD (sq_pos_of_ne_zero hN')
  let η : ℕ → ℝ := fun n =>
    airyPQDr D.P D.Q (t n) * (H (t n : ℂ)).re / ((airyPQN' D.P D.Q (t n : ℂ)).re) ^ 2
  let qterm : ℕ → ℝ := fun n =>
    airyPQDr D.P D.Q (t n) * (Q_c (t n : ℂ)).re / ((airyPQN' D.P D.Q (t n : ℂ)).re) ^ 2
  have hquad := hb_real_quadrature D ht hQc_cl
  change HasSum qterm (∫ u : ℝ, (Q_c (u : ℂ)).re) at hquad
  obtain ⟨K, hK_iff⟩ := exists_range_eq_nodes_gt D ht c
  -- Terms outside `Finset.range K` (`t n ≤ c`) are all nonnegative.
  have hoff_nn : ∀ n : ℕ, n ∉ Finset.range K → 0 ≤ qterm n := by
    intro n hn_not
    have hle_c : t n ≤ c := not_lt.mp fun hgt => hn_not (Finset.mem_range.mpr ((hK_iff n).mp hgt))
    have hterm_eq : qterm n = w n * (Q_c (t n : ℂ)).re := by dsimp [qterm, w]; ring
    rw [hterm_eq]
    rcases hle_c.lt_or_eq with hlt | heq
    · rw [hQc_of_ne (t n) hlt.ne]
      exact mul_nonneg (hw_pos n).le
        (div_nonneg_of_nonpos (hbelow n hlt) (sub_neg.mpr hlt).le)
    · have hderiv_nn : 0 ≤ (deriv H (c : ℂ)).re := hatc ⟨n, heq⟩
      have hQc_c : (Q_c (t n : ℂ)).re = (deriv H (c : ℂ)).re := by
        rw [heq]; dsimp [Q_c]; rw [dslope_same]
      rw [hQc_c]
      exact mul_nonneg (hw_pos n).le hderiv_nn
  -- Finite sum over `Finset.range K` (`c < t n`) is nonnegative by Abel summation by parts.
  have hsum_K_nn : 0 ≤ ∑ n ∈ Finset.range K, qterm n := by
    have hq_above : ∀ n ∈ Finset.range K, qterm n = η n * (1 / (t n - c)) := by
      intro n hn
      have hgt : c < t n := (hK_iff n).mpr (Finset.mem_range.mp hn)
      dsimp [qterm, η]
      rw [hQc_of_ne (t n) hgt.ne']
      ring
    rw [Finset.sum_congr rfl hq_above]
    cases K with
    | zero => simp
    | succ m =>
      rw [← Finset.sum_range_reflect (fun n => η n * (1 / (t n - c))) (m + 1)]
      simp only [Nat.add_sub_cancel]
      refine sum_range_mul_nonneg_of_partial_nonneg ?_ ?_ ?_
      · intro j hj
        have hjm : j ≤ m := Nat.lt_succ_iff.mp hj
        let x : ℝ := t (m - j)
        have hcx : c < x := (hK_iff (m - j)).mpr (by omega)
        let F_j : Finset ℕ := Finset.Ico (m - j) (m + 1)
        have hFj_iff : ∀ n : ℕ, n ∈ F_j ↔ (c < t n ∧ t n ≤ x) := by
          intro n
          rw [Finset.mem_Ico, hK_iff n]
          refine ⟨fun ⟨h1, h2⟩ => ⟨h2, ht.1.antitone h1⟩, fun ⟨h2, hle⟩ => ⟨?_, h2⟩⟩
          by_contra hlt_idx
          have hgt_t : x < t n := ht.1 (by omega : n < m - j)
          linarith
        have hcum_j := hcum x hcx F_j hFj_iff
        -- Identify `∑ i ∈ range (j + 1), η (m - i)` with `∑ n ∈ F_j, η n`.
        have himg : (Finset.range (j + 1)).image (fun i => m - i) = F_j := by
          ext n
          simp only [Finset.mem_image, Finset.mem_range, F_j, Finset.mem_Ico]
          refine ⟨?_, fun ⟨h1, h2⟩ => ⟨m - n, by omega, by omega⟩⟩
          rintro ⟨i, hi, rfl⟩
          exact ⟨by omega, by omega⟩
        have hinj : Set.InjOn (fun i => m - i) (Finset.range (j + 1) : Set ℕ) := by
          intro i₁ hi₁ i₂ hi₂ heq
          simp only [Finset.mem_coe, Finset.mem_range] at hi₁ hi₂
          dsimp at heq
          omega
        rw [← himg, Finset.sum_image hinj] at hcum_j
        exact hcum_j
      · intro j hj
        have hjm : j < m := Nat.succ_lt_succ_iff.mp hj
        have h1 : c < t (m - j) := (hK_iff (m - j)).mpr (by omega)
        have h2 : t (m - j) < t (m - (j + 1)) := ht.1 (by omega : m - (j + 1) < m - j)
        exact one_div_le_one_div_of_le (sub_pos.mpr h1) (by linarith)
      · intro j hj
        have h1 : c < t (m - j) := (hK_iff (m - j)).mpr (by omega)
        exact one_div_nonneg.mpr (sub_pos.mpr h1).le
  exact hsum_K_nn.trans (sum_le_of_hasSum_nonneg_off hquad (Finset.range K) hoff_nn)

/-- Remark in `thm:airy-node-sign` (`ce_airy_lp_proofs.tex` line 615): for `c > b`, no optimizer at
`b = u_LP < t_m` can satisfy the cumulative node-sum hypotheses (they contradict
`lem:airy-active-height` (4)). -/
theorem not_exists_airy_node_sum_gt (D : ShellHBData) {t : ℕ → ℝ} (ht : IsHbZeroEnum D.P D.Q t)
    {b : ℝ} (hb : uLP D = (b : EReal)) (hbt : b < D.tm)
    {H : ℂ → ℂ} (hH : OneProfileFeasibleWitness D b H)
    {c : ℝ} (hbc : b < c) (hctm : c < D.tm) (hHc0 : (H (c : ℂ)).re = 0)
    (hbelow : ∀ n : ℕ, t n < c → (H (t n : ℂ)).re ≤ 0)
    (hatc : (∃ n : ℕ, t n = c) → 0 ≤ (deriv H (c : ℂ)).re)
    (hcum : ∀ x : ℝ, c < x → ∀ F : Finset ℕ, (∀ n : ℕ, n ∈ F ↔ (c < t n ∧ t n ≤ x)) →
      0 ≤ ∑ n ∈ F, airyPQDr D.P D.Q (t n) * (H (t n : ℂ)).re /
        ((airyPQN' D.P D.Q (t n : ℂ)).re) ^ 2) :
    False := by
  have hnn := quotient_integral_nonneg_of_node_sum D ht hH.1 hHc0 hbelow hatc hcum
  have hlt_tm : uLP D < (D.tm : EReal) := hb ▸ EReal.coe_lt_coe_iff.mpr hbt
  have hc_not_site : c ∉ shellSites D := by
    intro hc_mem
    have htm_le := D.tm_min c (Finset.mem_erase.mp hc_mem).2
    linarith
  have hneg := (airy_active_height D).deflation hlt_tm b hb H hH c hbc hHc0 (Or.inl hc_not_site)
  linarith

/-- **`thm:airy-node-sign`, cumulative node-sum criterion (`ce_airy_lp_proofs.tex`, lines 611–626):**
proves the former `node_sum` field of `CeCanonicalInputs` (with the zero-enumeration hypothesis
`ht : IsHbZeroEnum D.P D.Q t`). -/
theorem airy_node_sum (D : ShellHBData) {t : ℕ → ℝ} (ht : IsHbZeroEnum D.P D.Q t) :
    ∀ b : ℝ, uLP D = (b : EReal) → b < D.tm → ∀ H : ℂ → ℂ, OneProfileFeasibleWitness D b H →
      (∃ c : ℝ, b ≤ c ∧ c < D.tm ∧ (H (c : ℂ)).re = 0 ∧
        (∀ n : ℕ, t n < c → (H (t n : ℂ)).re ≤ 0) ∧
        ((∃ n : ℕ, t n = c) → 0 ≤ (deriv H (c : ℂ)).re) ∧
        (∀ x : ℝ, c < x → ∀ F : Finset ℕ, (∀ n : ℕ, n ∈ F ↔ (c < t n ∧ t n ≤ x)) →
          0 ≤ ∑ n ∈ F, airyPQDr D.P D.Q (t n) * (H (t n : ℂ)).re /
            ((airyPQN' D.P D.Q (t n : ℂ)).re) ^ 2)) →
      uSh D = (b : EReal) := by
  rintro b hb hbt H hH ⟨c, hbc, hctm, hHc0, hbelow, hatc, hcum⟩
  rcases hbc.eq_or_lt with rfl | hbc_lt
  · have hnn := quotient_integral_nonneg_of_node_sum D ht hH.1 hHc0 hbelow hatc hcum
    exact (airy_active_height D).quotient_mass b hb H hH hnn
  · exact (not_exists_airy_node_sum_gt D ht hb hbt hH hbc_lt hctm hHc0 hbelow hatc hcum).elim

/-! ### Single-block reduction and three-alternation criterion (`thm:airy-node-sign`) -/

/-- Single-block case (`ce_airy_lp_proofs.tex`, lines 627–628): if `H(t_n) ≤ 0` for `t_n < c`,
`H(t_n) ≥ 0` for `c < t_n ≤ d`, and `H(t_n) ≤ 0` for `t_n > d`, then the cumulative node-sum
criterion applies. -/
lemma airy_node_single_block (D : ShellHBData) {t : ℕ → ℝ} (ht : IsHbZeroEnum D.P D.Q t)
    {b : ℝ} (hb : uLP D = (b : EReal)) (hbt : b < D.tm)
    {H : ℂ → ℂ} (hH : OneProfileFeasibleWitness D b H)
    {c d : ℝ} (hbc : b ≤ c) (hctm : c < D.tm)
    (hHc0 : (H (c : ℂ)).re = 0)
    (hatc : (∃ n : ℕ, t n = c) → 0 ≤ (deriv H (c : ℂ)).re)
    (hlow : ∀ n : ℕ, t n < c → (H (t n : ℂ)).re ≤ 0)
    (hmid : ∀ n : ℕ, c < t n → t n ≤ d → 0 ≤ (H (t n : ℂ)).re)
    (hhigh : ∀ n : ℕ, d < t n → (H (t n : ℂ)).re ≤ 0) :
    uSh D = (b : EReal) := by
  refine airy_node_sum D ht b hb hbt H hH ⟨c, hbc, hctm, hHc0, hlow, hatc, fun x hcx F hF => ?_⟩
  let η : ℕ → ℝ := fun n =>
    airyPQDr D.P D.Q (t n) * (H (t n : ℂ)).re / ((airyPQN' D.P D.Q (t n : ℂ)).re) ^ 2
  have hw_pos : ∀ n : ℕ,
      0 < airyPQDr D.P D.Q (t n) / ((airyPQN' D.P D.Q (t n : ℂ)).re) ^ 2 := by
    intro n
    have hz : airyPQN D.P D.Q (t n : ℂ) = 0 := (nodeZero_iff D (t n)).2 ((ht.2 (t n)).2 ⟨n, rfl⟩)
    obtain ⟨hD, hN'⟩ := hb_zero_weight_pos_all D hz
    exact div_pos hD (sq_pos_of_ne_zero hN')
  have hη_eq : ∀ n : ℕ,
      η n = (airyPQDr D.P D.Q (t n) / ((airyPQN' D.P D.Q (t n : ℂ)).re) ^ 2) * (H (t n : ℂ)).re := by
    intro n; dsimp [η]; ring
  rcases le_or_gt x d with hxd | hdx
  · refine Finset.sum_nonneg fun n hn => ?_
    obtain ⟨hgt, hle⟩ := (hF n).mp hn
    change 0 ≤ η n
    rw [hη_eq n]
    exact mul_nonneg (hw_pos n).le (hmid n hgt (hle.trans hxd))
  · -- For `x > d`, every term outside `F` is `≤ 0`, so `∑_{n ∈ F} η_n ≥ ∫_ℝ H ≥ 0`.
    have hquad := hb_real_quadrature D ht hH.1
    change HasSum η (∫ u : ℝ, (H (u : ℂ)).re) at hquad
    have hH_int_nn : 0 ≤ ∫ u : ℝ, (H (u : ℂ)).re := by
      simpa using hH.2.2.2.2 0 le_rfl
    have hoff_np : ∀ n : ℕ, n ∉ F → η n ≤ 0 := by
      intro n hn_not
      rw [hη_eq n]
      refine mul_nonpos_of_nonneg_of_nonpos (hw_pos n).le ?_
      rcases lt_trichotomy (t n) c with hlt | heq | hgt
      · exact hlow n hlt
      · rw [heq, hHc0]
      · have hgt_x : x < t n := by
          by_contra hle_x
          exact hn_not ((hF n).mpr ⟨hgt, not_lt.mp hle_x⟩)
        exact hhigh n (hdx.trans hgt_x)
    exact hH_int_nn.trans (le_sum_of_hasSum_nonpos_off hquad F hoff_np)

/-- If `H` is entire, `(H c).re = 0`, and `(H u).re ≤ 0` on `[a, c]` (`a < c`), then
`0 ≤ (deriv H c).re`. -/
private lemma deriv_re_nonneg_of_nonpos_left {H : ℂ → ℂ} (hHd : Differentiable ℂ H)
    {a c : ℝ} (hac : a < c) (hHc0 : (H (c : ℂ)).re = 0)
    (hnp : ∀ u ∈ Icc a c, (H (u : ℂ)).re ≤ 0) :
    0 ≤ (deriv H (c : ℂ)).re := by
  have hd_real : HasDerivAt (fun x : ℝ => (H (x : ℂ)).re) (deriv H (c : ℂ)).re c := by
    have hdC : HasDerivAt (fun x : ℝ => H (x : ℂ)) (deriv H (c : ℂ)) c := by
      simpa using (hHd (c : ℂ)).hasDerivAt.comp_ofReal
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt c hdC).congr_of_eventuallyEq
      (Eventually.of_forall fun _ => rfl)
  by_contra hlt
  push Not at hlt
  have hslope := hd_real.tendsto_slope_zero_left
  have hev := hslope.eventually (Iio_mem_nhds hlt)
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.eventually_nhds_iff.mp hev
  let h : ℝ := -min (δ / 2) ((c - a) / 2)
  have hh_neg : h < 0 := neg_neg_of_pos (lt_min (half_pos hδ_pos) (half_pos (sub_pos.mpr hac)))
  have hh_dist : dist h 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_neg hh_neg]
    dsimp [h]; rw [neg_neg]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ_pos)
  have hneg_q : h⁻¹ • ((H ((c + h : ℝ) : ℂ)).re - (H (c : ℂ)).re) < 0 :=
    hδ hh_dist hh_neg
  rw [hHc0, sub_zero, smul_eq_mul] at hneg_q
  have hmem : c + h ∈ Icc a c := by
    have hle_ca : -h ≤ (c - a) / 2 := by dsimp [h]; rw [neg_neg]; exact min_le_right _ _
    exact ⟨by linarith, by linarith⟩
  have hnn : 0 ≤ h⁻¹ * (H ((c + h : ℝ) : ℂ)).re :=
    mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.mpr hh_neg.le) (hnp (c + h) hmem)
  linarith

/-- Attainment of `OneProfileFeasible D b` whenever `uLP D = (b : EReal)`. -/
private lemma exists_optimizer_of_uLP_eq (D : ShellHBData) {b : ℝ} (hb : uLP D = (b : EReal)) :
    ∃ H : ℂ → ℂ, OneProfileFeasibleWitness D b H := by
  have hex : ∃ u : ℝ, OneProfileFeasible D u := by
    by_contra hno
    push Not at hno
    have hbot : uLP D = ⊥ := by simp [uLP, hno]
    rw [hbot] at hb
    exact EReal.bot_ne_coe b hb
  obtain ⟨u₀, hu₀⟩ := hex
  obtain ⟨C, ν, hC, hbound⟩ := one_profile_envelope_aux D u₀ hu₀
  obtain ⟨u_s, hu_s⟩ := one_profile_maximizer_exists D
    { u₀ := u₀, u₀_feasible := hu₀, C₀ := C, ν₀ := ν, hC₀ := hC,
      uniform_env := fun {u H} hu hH hn z => hbound u hu H hH hn z }
  have hub : uLP D = (u_s : EReal) :=
    le_antisymm (iSup₂_le fun u hu => EReal.coe_le_coe_iff.2 (hu_s.2 hu))
      (le_iSup₂ (f := fun (u : ℝ) (_ : OneProfileFeasible D u) => (u : EReal)) u_s hu_s.1)
  have heq : u_s = b := EReal.coe_injective (hub.symm.trans hb)
  exact heq ▸ hu_s.1

/-- **`thm:airy-node-sign` (`ce_airy_lp_proofs.tex`, lines 607–643):**
(1) three-alternation node-sign criterion for any weak optimizer `H` at `b = u_LP < t_m`, and
(2) `u_sh = b` whenever `t_{m+2} ≤ b = u_LP < t_m` (`ht : IsHbZeroEnum D.P D.Q t`).
Proves the former `node_sign` field of `CeCanonicalInputs`. -/
theorem airy_node_sign (D : ShellHBData) {t : ℕ → ℝ} (ht : IsHbZeroEnum D.P D.Q t) :
    (∀ b : ℝ, uLP D = (b : EReal) → b < D.tm → ∀ H : ℂ → ℂ, OneProfileFeasibleWitness D b H →
      (¬ ∃ t₁ t₂ t₃ : ℝ, t₁ < t₂ ∧ t₂ < t₃ ∧ b < t₁ ∧ t₃ ≤ D.tm ∧ at47_Nf D.P D.Q t₁ = 0 ∧
        at47_Nf D.P D.Q t₂ = 0 ∧ at47_Nf D.P D.Q t₃ = 0 ∧ 0 < (H (t₁ : ℂ)).re ∧
        (H (t₂ : ℂ)).re < 0 ∧ 0 < (H (t₃ : ℂ)).re) → uSh D = (b : EReal)) ∧
    (∀ b : ℝ, uLP D = (b : EReal) → hbNode t (D.S.card + 2) ≤ b → b < D.tm → uSh D = (b : EReal)) := by
  classical
  have hpart1 : ∀ b : ℝ, uLP D = (b : EReal) → b < D.tm → ∀ H : ℂ → ℂ,
      OneProfileFeasibleWitness D b H →
      (¬ ∃ t₁ t₂ t₃ : ℝ, t₁ < t₂ ∧ t₂ < t₃ ∧ b < t₁ ∧ t₃ ≤ D.tm ∧ at47_Nf D.P D.Q t₁ = 0 ∧
        at47_Nf D.P D.Q t₂ = 0 ∧ at47_Nf D.P D.Q t₃ = 0 ∧ 0 < (H (t₁ : ℂ)).re ∧
        (H (t₂ : ℂ)).re < 0 ∧ 0 < (H (t₃ : ℂ)).re) → uSh D = (b : EReal) := by
    intro b hb hbt H hH hno
    let h : ℝ → ℝ := fun u => (H (u : ℂ)).re
    have hcont : Continuous h :=
      Complex.continuous_re.comp (hH.1.1.continuous.comp Complex.continuous_ofReal)
    -- `h b = 0` (by maximality of `b = u_LP`) and `0 ≤ (deriv H b).re`.
    have hHb0 : h b = 0 := by
      have hle0 : h b ≤ 0 := hH.2.2.2.1 b le_rfl
      refine le_antisymm hle0 ?_
      by_contra hneg
      push Not at hneg
      obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp (hcont.continuousAt (x := b))
        (-h b / 2) (by linarith)
      let b' : ℝ := b + δ / 2
      have hb_lt_b' : b < b' := by dsimp [b']; linarith
      have hH_b' : OneProfileFeasibleWitness D b' H := by
        refine ⟨hH.1, hH.2.1, hH.2.2.1, fun u hu => ?_, hH.2.2.2.2⟩
        rcases le_or_gt u b with hub | hub
        · exact hH.2.2.2.1 u hub
        · have hdist : dist u b < δ := by
            rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hub)]
            dsimp [b'] at hu; linarith
          have hd := hδ hdist
          rw [Real.dist_eq] at hd
          have hd' := abs_lt.mp hd
          linarith
      have hle_ulp : (b' : EReal) ≤ uLP D :=
        le_iSup₂ (f := fun (u : ℝ) (_ : OneProfileFeasible D u) => (u : EReal)) b' ⟨H, hH_b'⟩
      rw [hb] at hle_ulp
      exact absurd (EReal.coe_le_coe_iff.mp hle_ulp) (not_le.mpr hb_lt_b')
    have hderiv_b : 0 ≤ (deriv H (b : ℂ)).re :=
      deriv_re_nonneg_of_nonpos_left hH.1.1 (by linarith : b - 1 < b) hHb0
        fun u hu => hH.2.2.2.1 u hu.2
    -- Nodes above `D.tm` are prescribed sites, hence `h (t n) ≤ 0`.
    have h_above_tm : ∀ n : ℕ, D.tm < t n → h (t n) ≤ 0 := by
      intro n hgt
      have hmem_S : t n ∈ D.S := by
        by_contra hnotS
        have hN0 : airyPQN D.P D.Q (t n : ℂ) = 0 :=
          (nodeZero_iff D (t n)).2 ((ht.2 (t n)).2 ⟨n, rfl⟩)
        exact absurd (D.S_top (t n) hN0 hnotS D.tm D.tm_mem) (not_lt.mpr hgt.le)
      exact hH.2.2.1 (t n) hmem_S hgt.ne'
    -- Finite set of nodes in `(b, D.tm]` where `h > 0`.
    obtain ⟨K_b, hKb_iff⟩ := exists_range_eq_nodes_gt D ht b
    let P_pos : Finset ℕ := (Finset.range K_b).filter (fun n => t n ≤ D.tm ∧ 0 < h (t n))
    by_cases hP_ne : P_pos.Nonempty
    · let P_vals : Finset ℝ := P_pos.image t
      have hPv_ne : P_vals.Nonempty := hP_ne.image t
      let t_lo : ℝ := P_vals.min' hPv_ne
      let t_hi : ℝ := P_vals.max' hPv_ne
      obtain ⟨n_lo, hn_lo, ht_lo_eq⟩ := Finset.mem_image.mp (Finset.min'_mem P_vals hPv_ne)
      obtain ⟨n_hi, hn_hi, ht_hi_eq⟩ := Finset.mem_image.mp (Finset.max'_mem P_vals hPv_ne)
      have ht_lo_eq' : t n_lo = t_lo := ht_lo_eq
      have ht_hi_eq' : t n_hi = t_hi := ht_hi_eq
      have hb_lo : b < t_lo := by
        rw [← ht_lo_eq']
        exact (hKb_iff n_lo).mpr (Finset.mem_range.mp (Finset.mem_filter.mp hn_lo).1)
      have hlo_pos : 0 < h t_lo := by rw [← ht_lo_eq']; exact (Finset.mem_filter.mp hn_lo).2.2
      have hhi_tm : t_hi ≤ D.tm := by rw [← ht_hi_eq']; exact (Finset.mem_filter.mp hn_hi).2.1
      have hhi_pos : 0 < h t_hi := by rw [← ht_hi_eq']; exact (Finset.mem_filter.mp hn_hi).2.2
      have hlo_Nf : at47_Nf D.P D.Q t_lo = 0 := by rw [← ht_lo_eq']; exact (ht.2 (t n_lo)).2 ⟨n_lo, rfl⟩
      have hhi_Nf : at47_Nf D.P D.Q t_hi = 0 := by rw [← ht_hi_eq']; exact (ht.2 (t n_hi)).2 ⟨n_hi, rfl⟩
      -- Above `t_hi`: `h (t n) ≤ 0`.
      have h_above_hi : ∀ n : ℕ, t_hi < t n → h (t n) ≤ 0 := by
        intro n hgt
        rcases le_or_gt (t n) D.tm with hle_tm | hgt_tm
        · by_contra hpos
          push Not at hpos
          have hb_n : b < t n := hb_lo.trans ((Finset.min'_le P_vals t_hi (Finset.max'_mem _ _)).trans_lt hgt)
          have hn_P : n ∈ P_pos := Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr ((hKb_iff n).mp hb_n), hle_tm, hpos⟩
          have hle_hi : t n ≤ t_hi := Finset.le_max' P_vals (t n) (Finset.mem_image_of_mem t hn_P)
          linarith
        · exact h_above_tm n hgt_tm
      -- On `[t_lo, t_hi]`: `0 ≤ h (t n)` by the no-alternating-triple hypothesis `hno`.
      have h_on_lohi : ∀ n : ℕ, t_lo ≤ t n → t n ≤ t_hi → 0 ≤ h (t n) := by
        intro n hge_lo hle_hi
        by_contra hneg
        push Not at hneg
        have hne_lo : t_lo ≠ t n := fun heq => by linarith [heq ▸ hlo_pos]
        have hne_hi : t n ≠ t_hi := fun heq => by linarith [heq ▸ hhi_pos]
        exact hno ⟨t_lo, t n, t_hi, lt_of_le_of_ne hge_lo hne_lo, lt_of_le_of_ne hle_hi hne_hi,
          hb_lo, hhi_tm, hlo_Nf, (ht.2 (t n)).2 ⟨n, rfl⟩, hhi_Nf, hlo_pos, hneg, hhi_pos⟩
      -- Negative nodes in `(b, t_lo)`.
      let N_neg : Finset ℕ := (Finset.range K_b).filter (fun n => t n < t_lo ∧ h (t n) < 0)
      by_cases hN_ne : N_neg.Nonempty
      · let N_vals : Finset ℝ := N_neg.image t
        have hNv_ne : N_vals.Nonempty := hN_ne.image t
        let t_neg : ℝ := N_vals.max' hNv_ne
        obtain ⟨n_neg, hn_neg, ht_neg_eq⟩ := Finset.mem_image.mp (Finset.max'_mem N_vals hNv_ne)
        have ht_neg_eq' : t n_neg = t_neg := ht_neg_eq
        have hb_neg : b < t_neg := by
          rw [← ht_neg_eq']
          exact (hKb_iff n_neg).mpr (Finset.mem_range.mp (Finset.mem_filter.mp hn_neg).1)
        have hneg_lo : t_neg < t_lo := by rw [← ht_neg_eq']; exact (Finset.mem_filter.mp hn_neg).2.1
        have hneg_val : h t_neg < 0 := by rw [← ht_neg_eq']; exact (Finset.mem_filter.mp hn_neg).2.2
        -- First zero `c = sInf {u ∈ [t_neg, t_lo] | 0 ≤ h u}`.
        let E : Set ℝ := {u ∈ Icc t_neg t_lo | 0 ≤ h u}
        have hE_closed : IsClosed E :=
          isClosed_Icc.inter (isClosed_le continuous_const hcont)
        have hE_ne : E.Nonempty :=
          ⟨t_lo, ⟨hneg_lo.le, le_rfl⟩, hlo_pos.le⟩
        have hE_bdd : BddBelow E := ⟨t_neg, fun _ hu => hu.1.1⟩
        let c : ℝ := sInf E
        have hc_mem : c ∈ E := hE_closed.csInf_mem hE_ne hE_bdd
        have hc_ge_neg : t_neg ≤ c := hc_mem.1.1
        have hc_le_lo : c ≤ t_lo := hc_mem.1.2
        have hc_nn : 0 ≤ h c := hc_mem.2
        have hneg_lt_c : t_neg < c :=
          lt_of_le_of_ne hc_ge_neg fun heq => by linarith [heq ▸ hneg_val]
        have h_neg_Ico : ∀ u ∈ Ico t_neg c, h u < 0 := by
          intro u hu
          by_contra hge
          push Not at hge
          have hu_mem : u ∈ E := ⟨⟨hu.1, hu.2.le.trans hc_le_lo⟩, hge⟩
          exact absurd (csInf_le hE_bdd hu_mem) (not_le.mpr hu.2)
        have hHc0 : h c = 0 := by
          refine le_antisymm ?_ hc_nn
          by_contra hpos_c
          push Not at hpos_c
          obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp (hcont.continuousAt (x := c))
            (h c / 2) (half_pos hpos_c)
          let u₀ : ℝ := max t_neg (c - δ / 2)
          have hu₀_Ico : u₀ ∈ Ico t_neg c :=
            ⟨le_max_left _ _, max_lt hneg_lt_c (by linarith)⟩
          have hdist : dist u₀ c < δ := by
            rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hu₀_Ico.2)]
            have : c - δ / 2 ≤ u₀ := le_max_right _ _
            linarith
          have hd := hδ hdist
          rw [Real.dist_eq] at hd
          have hd' := abs_lt.mp hd
          linarith [h_neg_Ico u₀ hu₀_Ico]
        have hc_lt_lo : c < t_lo :=
          lt_of_le_of_ne hc_le_lo fun heq => by linarith [heq ▸ hHc0]
        have hlo_tm : t_lo ≤ D.tm :=
          (Finset.min'_le P_vals t_hi (Finset.max'_mem _ _)).trans hhi_tm
        have hderiv_c : 0 ≤ (deriv H (c : ℂ)).re :=
          deriv_re_nonneg_of_nonpos_left hH.1.1 hneg_lt_c hHc0 fun u hu => by
            rcases hu.2.lt_or_eq with hlt | rfl
            · exact (h_neg_Ico u ⟨hu.1, hlt⟩).le
            · exact hHc0.le
        refine airy_node_single_block D ht hb hbt hH (hb_neg.le.trans hneg_lt_c.le)
          (hc_lt_lo.trans_le hlo_tm) hHc0 (fun _ => hderiv_c) ?_ ?_ h_above_hi
        · -- `t n < c ⇒ h (t n) ≤ 0`.
          intro n hlt_c
          rcases le_or_gt (t n) b with hle_b | hgt_b
          · exact hH.2.2.2.1 (t n) hle_b
          · rcases lt_or_ge (t n) t_neg with hlt_neg | hge_neg
            · by_contra hpos_n
              push Not at hpos_n
              have hn_P : n ∈ P_pos := Finset.mem_filter.mpr
                ⟨Finset.mem_range.mpr ((hKb_iff n).mp hgt_b),
                  (hlt_neg.trans hneg_lo).le.trans hlo_tm, hpos_n⟩
              have hge_lo := Finset.min'_le P_vals (t n) (Finset.mem_image_of_mem t hn_P)
              linarith
            · exact (h_neg_Ico (t n) ⟨hge_neg, hlt_c⟩).le
        · -- `c < t n ≤ t_hi ⇒ 0 ≤ h (t n)`.
          intro n hgt_c hle_hi
          rcases lt_or_ge (t n) t_lo with hlt_lo | hge_lo
          · by_contra hneg_n
              -- If `h (t n) < 0` with `b < t_neg < c < t n < t_lo`, then `t n ∈ N_vals` exceeds `t_neg`!
            push Not at hneg_n
            have hb_n : b < t n := hb_neg.trans (hneg_lt_c.trans hgt_c)
            have hn_N : n ∈ N_neg := Finset.mem_filter.mpr
              ⟨Finset.mem_range.mpr ((hKb_iff n).mp hb_n), hlt_lo, hneg_n⟩
            have hle_neg := Finset.le_max' N_vals (t n) (Finset.mem_image_of_mem t hn_N)
            linarith
          · exact h_on_lohi n hge_lo hle_hi
      · -- `N_neg = ∅`: take `(c, d) = (b, t_hi)`.
        refine airy_node_single_block D ht hb hbt hH le_rfl hbt hHb0 (fun _ => hderiv_b)
          (fun n hlt => hH.2.2.2.1 (t n) hlt.le) ?_ h_above_hi
        intro n hgt_b hle_hi
        rcases lt_or_ge (t n) t_lo with hlt_lo | hge_lo
        · by_contra hneg_n
          push Not at hneg_n
          have hn_N : n ∈ N_neg := Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr ((hKb_iff n).mp hgt_b), hlt_lo, hneg_n⟩
          exact hN_ne ⟨n, hn_N⟩
        · exact h_on_lohi n hge_lo hle_hi
    · -- `P_pos = ∅`: take `(c, d) = (b, b)`.
      refine airy_node_single_block D ht hb hbt hH le_rfl hbt hHb0 (fun _ => hderiv_b)
        (fun n hlt => hH.2.2.2.1 (t n) hlt.le)
        (fun _ h1 h2 => absurd (h1.trans_le h2) (lt_irrefl b)) ?_
      intro n hgt_b
      rcases le_or_gt (t n) D.tm with hle_tm | hgt_tm
      · by_contra hpos_n
        push Not at hpos_n
        have hn_P : n ∈ P_pos := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr ((hKb_iff n).mp hgt_b), hle_tm, hpos_n⟩
        exact hP_ne ⟨n, hn_P⟩
      · exact h_above_tm n hgt_tm
  refine ⟨hpart1, fun b hb htm2 hbt => ?_⟩
  obtain ⟨H, hH⟩ := exists_optimizer_of_uLP_eq D hb
  refine hpart1 b hb hbt H hH ?_
  rintro ⟨t₁, t₂, t₃, ht12, ht23, hbt1, ht3tm, hNf1, hNf2, hNf3, -⟩
  obtain ⟨k₁, rfl⟩ := (ht.2 t₁).1 hNf1
  obtain ⟨k₂, rfl⟩ := (ht.2 t₂).1 hNf2
  obtain ⟨k₃, rfl⟩ := (ht.2 t₃).1 hNf3
  have hk32 : k₃ < k₂ := by
    by_contra hle; exact absurd (ht.1.antitone (not_lt.mp hle)) (not_le.mpr ht23)
  have hk21 : k₂ < k₁ := by
    by_contra hle; exact absurd (ht.1.antitone (not_lt.mp hle)) (not_le.mpr ht12)
  have hcard_pos : 1 ≤ D.S.card := Finset.card_pos.mpr D.S_nonempty
  have htm_eq : D.tm = t (D.S.card - 1) := by
    rw [D.tm_eq_hbNode ht]; rfl
  have hk3_ge : D.S.card - 1 ≤ k₃ := by
    by_contra hlt
    have hgt : t (D.S.card - 1) < t k₃ := ht.1 (not_le.mp hlt)
    linarith [htm_eq, ht3tm]
  have hk1_lt : k₁ < D.S.card + 1 := by
    by_contra hge
    have hle : t k₁ ≤ t (D.S.card + 1) := ht.1.antitone (not_lt.mp hge)
    have hnode_eq : hbNode t (D.S.card + 2) = t (D.S.card + 1) := rfl
    linarith [hnode_eq, htm2, hbt1]
  omega

/-- info: 'FormalResearch.SignUncertainty.airy_node_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.airy_node_sum

/-- info: 'FormalResearch.SignUncertainty.airy_node_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.airy_node_sign

end FormalResearch.SignUncertainty
