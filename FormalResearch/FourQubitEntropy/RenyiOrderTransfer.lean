import FormalResearch.FourQubitEntropy.RenyiSingleCrossingFamily

/-!
# Order transfer for the Rényi entropies above one

Paper: `cor:fqe-renyi-order-transfer` (renyi_single_crossing.tex), from the single-crossing
inequality (SX) of `lem:fqe-renyi-single-crossing`.

The single-crossing statement is taken here as an explicit hypothesis `SingleCrossingStatement`
(for every `q > 1` and every four-point probability vector `l`: `v_q(l) - v_q(σ) ≤ κ_q (u_q(l) - u_q(σ))`,
with equality only for permutations of `σ`); it is proved in `RenyiSingleCrossing.lean`, which
instantiates the theorems of this file without hypothesis. This file proves, from it:

* `G_l(q) = (q-1)(H_q(l) - H_q(σ)) / (q tanh((q-1) ln 3 / 2))` is nondecreasing on `(1, ∞)`, strictly
  unless `l` is a permutation of `σ` (`renyiG_monotoneOn`, `renyiG_strictMonoOn`);
* for three four-point spectra and `1 < q < q₁`: `E_{q₁} ≤ h_{q₁} → E_q ≤ h_q` with equality only if all
  three are permutations of `σ`, and `E_{q₁} < h_{q₁} → E_q < h_q` (`renyi_order_transfer`).

`H_q(l) = log₂(Σ lᵢ^q)/(1-q)` (`renyiSpec` of `RenyiSpec.lean`), `E_q` the mean of three `H_q`, `h_q = H_q(σ)`.
-/

namespace FormalResearch.FourQubitEntropy

open Real

/-- The single-crossing lemma `lem:fqe-renyi-single-crossing` (SX), as a statement. -/
def SingleCrossingStatement : Prop :=
  ∀ q : ℝ, 1 < q → ∀ l : Fin 4 → ℝ, IsProb4 l →
    sxV q l - sxV q hsSpec ≤ sxKappa q * (sxU q l - sxU q hsSpec) ∧
    (sxV q l - sxV q hsSpec = sxKappa q * (sxU q l - sxU q hsSpec) → IsHsPerm l)

/-- `G_l(q) = (q-1)(H_q(l) - H_q(σ)) / (q tanh((q-1) ln 3/2))`. -/
noncomputable def renyiG (l : Fin 4 → ℝ) (q : ℝ) : ℝ :=
  (q - 1) * (renyiSpec q l - renyiSpec q hsSpec) / (q * Real.tanh ((q - 1) * Real.log 3 / 2))

/-- `m(q) = e^{K(q)} = q tanh((q-1) ln 3/2)`. -/
noncomputable def renyiM (q : ℝ) : ℝ := q * Real.tanh ((q - 1) * Real.log 3 / 2)

/-! ### Derivatives in the order -/

theorem sxZ_pos {l : Fin 4 → ℝ} (hl : IsProb4 l) (q : ℝ) : 0 < sxZ q l := by
  obtain ⟨h0, h1⟩ := hl
  have : ∃ i, 0 < l i := by
    by_contra h
    push Not at h
    have : ∑ i, l i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm (h i) (h0 i)
    linarith
  obtain ⟨i, hi⟩ := this
  unfold sxZ
  calc 0 < l i ^ q := Real.rpow_pos_of_pos hi q
    _ ≤ ∑ j, l j ^ q :=
      Finset.single_le_sum (f := fun j => l j ^ q) (fun j _ => Real.rpow_nonneg (h0 j) q)
        (Finset.mem_univ i)

theorem hasDerivAt_rpow_order {x : ℝ} (hx : 0 ≤ x) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun r : ℝ => x ^ r) (x ^ q * Real.log x) q := by
  rcases hx.eq_or_lt with h | h
  · subst h
    have : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 q := hasDerivAt_const q 0
    have h2 := this.congr_of_eventuallyEq (f₁ := fun r : ℝ => (0 : ℝ) ^ r) ?_
    · simpa using h2
    · filter_upwards [lt_mem_nhds hq] with r hr
      exact Real.zero_rpow hr.ne'
  · exact (Real.hasStrictDerivAt_const_rpow h q).hasDerivAt

theorem sxZ_hasDerivAt {l : Fin 4 → ℝ} (hl : IsProb4 l) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun r => sxZ r l) (∑ i, l i ^ q * Real.log (l i)) q := by
  unfold sxZ
  have := HasDerivAt.fun_sum (u := Finset.univ) (A := fun i r => l i ^ r)
    (A' := fun i => l i ^ q * Real.log (l i)) (x := q)
    (fun i _ => hasDerivAt_rpow_order (hl.1 i) hq)
  simpa using this

theorem sxU_hasDerivAt {l : Fin 4 → ℝ} (hl : IsProb4 l) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun r => sxU r l) (sxV q l) q := by
  have h := (sxZ_hasDerivAt hl hq).log (sxZ_pos hl q).ne'
  exact h

theorem renyiM_eq (q : ℝ) :
    renyiM q = q * (Real.sinh ((q - 1) * Real.log 3 / 2) / Real.cosh ((q - 1) * Real.log 3 / 2)) := by
  unfold renyiM; rw [Real.tanh_eq_sinh_div_cosh]

theorem renyiM_pos {q : ℝ} (hq : 1 < q) : 0 < renyiM q := by
  rw [renyiM_eq]
  have hy : 0 < (q - 1) * Real.log 3 / 2 := by
    have := sx_log3_pos
    have : 0 < (q - 1) * Real.log 3 := mul_pos (by linarith) this
    linarith
  have := Real.sinh_pos_iff.mpr hy
  have := Real.cosh_pos ((q - 1) * Real.log 3 / 2)
  positivity

/-- `m'(q) = κ_q m(q)`, i.e. `K' = κ` for `K = ln m`. -/
theorem renyiM_hasDerivAt {q : ℝ} (hq : 1 < q) : HasDerivAt renyiM (sxKappa q * renyiM q) q := by
  set L := Real.log 3 with hL
  have hL0 : 0 < L := sx_log3_pos
  set y := (q - 1) * L / 2 with hy
  have hy0 : 0 < y := by
    have : 0 < (q - 1) * L := mul_pos (by linarith) hL0
    rw [hy]; linarith
  have hyd : HasDerivAt (fun r : ℝ => (r - 1) * L / 2) (L / 2) q := by
    have := (((hasDerivAt_id q).sub_const 1).mul_const L).div_const 2
    convert this using 1
    simp
    ring
  have hS := hyd.sinh
  have hC := hyd.cosh
  have hch : 0 < Real.cosh y := Real.cosh_pos y
  have hT := hS.div hC hch.ne'
  have hm := (hasDerivAt_id q).mul hT
  have hfun : renyiM = fun r => id r * ((fun x => Real.sinh ((x - 1) * L / 2)) /
      fun x => Real.cosh ((x - 1) * L / 2)) r := by
    funext r
    rw [renyiM_eq]; rfl
  convert hm using 1
  have hsh : 0 < Real.sinh y := Real.sinh_pos_iff.mpr hy0
  have h2y : Real.sinh ((q - 1) * L) = 2 * Real.sinh y * Real.cosh y := by
    rw [← Real.sinh_two_mul]; congr 1; rw [hy]; ring
  have hcs : Real.cosh y ^ 2 - Real.sinh y ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq y
  unfold sxKappa
  rw [renyiM_eq, h2y]
  simp only [id, Pi.div_apply]
  simp only [← hy, ← hL]
  have hq0 : q ≠ 0 := by linarith
  field_simp
  linear_combination (-(q * L)) * hcs

/-! ### `N_l = (u_q(l) - u_q(σ)) / m(q)` is nonincreasing -/

theorem hsSpec_isProb : IsProb4 hsSpec := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> simp [hsSpec]
  · simp [hsSpec, Fin.sum_univ_four]; norm_num

/-- `N_l(q) = (u_q(l) - u_q(σ))/m(q)`. -/
noncomputable def renyiN (l : Fin 4 → ℝ) (q : ℝ) : ℝ := (sxU q l - sxU q hsSpec) / renyiM q

theorem renyiN_hasDerivAt {l : Fin 4 → ℝ} (hl : IsProb4 l) {q : ℝ} (hq : 1 < q) :
    HasDerivAt (renyiN l)
      ((sxV q l - sxV q hsSpec - sxKappa q * (sxU q l - sxU q hsSpec)) / renyiM q) q := by
  have hq0 : 0 < q := by linarith
  have h1 := (sxU_hasDerivAt hl hq0).sub (sxU_hasDerivAt hsSpec_isProb hq0)
  have h2 := h1.div (renyiM_hasDerivAt hq) (renyiM_pos hq).ne'
  unfold renyiN
  refine h2.congr_deriv ?_
  have := (renyiM_pos hq).ne'
  simp only [Pi.sub_apply]
  field_simp

theorem renyiN_continuousOn {l : Fin 4 → ℝ} (hl : IsProb4 l) :
    ContinuousOn (renyiN l) (Set.Ioi 1) :=
  fun _ hq => (renyiN_hasDerivAt hl (Set.mem_Ioi.mp hq)).continuousAt.continuousWithinAt

theorem renyiN_deriv {l : Fin 4 → ℝ} (hl : IsProb4 l) {q : ℝ} (hq : 1 < q) :
    deriv (renyiN l) q
      = (sxV q l - sxV q hsSpec - sxKappa q * (sxU q l - sxU q hsSpec)) / renyiM q :=
  (renyiN_hasDerivAt hl hq).deriv

theorem renyiN_antitoneOn (hSX : SingleCrossingStatement) {l : Fin 4 → ℝ} (hl : IsProb4 l) :
    AntitoneOn (renyiN l) (Set.Ioi 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 1) (renyiN_continuousOn hl)
  · intro q hq
    rw [interior_Ioi] at hq
    exact (renyiN_hasDerivAt hl hq).differentiableAt.differentiableWithinAt
  · intro q hq
    rw [interior_Ioi] at hq
    rw [renyiN_deriv hl hq]
    have := (hSX q hq l hl).1
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (renyiM_pos hq).le

theorem renyiN_strictAntiOn (hSX : SingleCrossingStatement) {l : Fin 4 → ℝ} (hl : IsProb4 l)
    (hn : ¬ IsHsPerm l) : StrictAntiOn (renyiN l) (Set.Ioi 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 1) (renyiN_continuousOn hl)
  intro q hq
  rw [interior_Ioi] at hq
  rw [renyiN_deriv hl hq]
  obtain ⟨hle, heq⟩ := hSX q hq l hl
  have hlt : sxV q l - sxV q hsSpec < sxKappa q * (sxU q l - sxU q hsSpec) :=
    lt_of_le_of_ne hle (fun h => hn (heq h))
  exact div_neg_of_neg_of_pos (by linarith) (renyiM_pos hq)

/-! ### The Rényi entropies -/

theorem renyiSpec_sub {l : Fin 4 → ℝ} {q : ℝ} (hq : 1 < q) :
    renyiSpec q hsSpec - renyiSpec q l = (sxU q l - sxU q hsSpec) / ((q - 1) * Real.log 2) := by
  have h1 : q - 1 ≠ 0 := by linarith
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold renyiSpec sxU sxZ Real.logb
  have h3 : 1 - q = -(q - 1) := by ring
  rw [h3]
  field_simp
  ring

/-- `G_l = -N_l / ln 2`. -/
theorem renyiG_eq {l : Fin 4 → ℝ} {q : ℝ} (hq : 1 < q) :
    renyiG l q = - renyiN l q / Real.log 2 := by
  have h1 : q - 1 ≠ 0 := by linarith
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have h3 := (renyiM_pos hq).ne'
  have h4 := renyiSpec_sub (l := l) hq
  unfold renyiG renyiN
  rw [show renyiSpec q l - renyiSpec q hsSpec = -(renyiSpec q hsSpec - renyiSpec q l) by ring, h4]
  change _ / renyiM q = _
  field_simp

/-- **`cor:fqe-renyi-order-transfer`, monotonicity of `G_l`** (from the hypothesis SX):
`G_l` is nondecreasing on `(1, ∞)`. -/
theorem renyiG_monotoneOn (hSX : SingleCrossingStatement) {l : Fin 4 → ℝ} (hl : IsProb4 l) :
    MonotoneOn (renyiG l) (Set.Ioi 1) := by
  intro x hx y hy hxy
  rw [renyiG_eq hx, renyiG_eq hy]
  have := renyiN_antitoneOn hSX hl hx hy hxy
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_le_div_iff_of_pos_right h2]
  linarith

/-- `G_l` is strictly increasing unless `l` is a permutation of `σ`. -/
theorem renyiG_strictMonoOn (hSX : SingleCrossingStatement) {l : Fin 4 → ℝ} (hl : IsProb4 l)
    (hn : ¬ IsHsPerm l) : StrictMonoOn (renyiG l) (Set.Ioi 1) := by
  intro x hx y hy hxy
  rw [renyiG_eq hx, renyiG_eq hy]
  have := renyiN_strictAntiOn hSX hl hn hx hy hxy
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_lt_div_iff_of_pos_right h2]
  linarith

/-- The mean of three Rényi entropies. -/
noncomputable def renyiE (q : ℝ) (l₁ l₂ l₃ : Fin 4 → ℝ) : ℝ :=
  (renyiSpec q l₁ + renyiSpec q l₂ + renyiSpec q l₃) / 3

/-- **`cor:fqe-renyi-order-transfer`, the triple transfer** (from the hypothesis SX). For three
four-point spectra and `1 < q < q₁`, with `E = renyiE`, `h_q = H_q(σ)`:
`E_{q₁} ≤ h_{q₁} → E_q ≤ h_q`; `E_{q₁} < h_{q₁} → E_q < h_q`; and if `E_{q₁} ≤ h_{q₁}` and `E_q = h_q`,
all three spectra are permutations of `σ`. -/
theorem renyi_order_transfer (hSX : SingleCrossingStatement) {l₁ l₂ l₃ : Fin 4 → ℝ}
    (h₁ : IsProb4 l₁) (h₂ : IsProb4 l₂) (h₃ : IsProb4 l₃) {q q₁ : ℝ} (hq : 1 < q) (hqq : q < q₁) :
    (renyiE q₁ l₁ l₂ l₃ ≤ renyiSpec q₁ hsSpec → renyiE q l₁ l₂ l₃ ≤ renyiSpec q hsSpec) ∧
    (renyiE q₁ l₁ l₂ l₃ < renyiSpec q₁ hsSpec → renyiE q l₁ l₂ l₃ < renyiSpec q hsSpec) ∧
    (renyiE q₁ l₁ l₂ l₃ ≤ renyiSpec q₁ hsSpec → renyiE q l₁ l₂ l₃ = renyiSpec q hsSpec →
      IsHsPerm l₁ ∧ IsHsPerm l₂ ∧ IsHsPerm l₃) := by
  have hq1 : 1 < q₁ := lt_trans hq hqq
  set S : ℝ → ℝ := fun r => renyiN l₁ r + renyiN l₂ r + renyiN l₃ r with hS
  -- `h - E = (m / (3 (r - 1) ln 2)) S`
  have key : ∀ r, 1 < r → renyiSpec r hsSpec - renyiE r l₁ l₂ l₃
      = renyiM r / (3 * ((r - 1) * Real.log 2)) * S r := by
    intro r hr
    have h1 : r - 1 ≠ 0 := by linarith
    have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    have e1 := renyiSpec_sub (l := l₁) hr
    have e2 := renyiSpec_sub (l := l₂) hr
    have e3 := renyiSpec_sub (l := l₃) hr
    have hm := (renyiM_pos hr).ne'
    have : renyiSpec r hsSpec - renyiE r l₁ l₂ l₃
        = ((renyiSpec r hsSpec - renyiSpec r l₁) + (renyiSpec r hsSpec - renyiSpec r l₂)
            + (renyiSpec r hsSpec - renyiSpec r l₃)) / 3 := by unfold renyiE; ring
    rw [this, e1, e2, e3]
    simp only [hS, renyiN]
    field_simp
  have hc : ∀ r, 1 < r → 0 < renyiM r / (3 * ((r - 1) * Real.log 2)) := by
    intro r hr
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have : 0 < r - 1 := by linarith
    have := renyiM_pos hr
    positivity
  have a1 := renyiN_antitoneOn hSX h₁ (Set.mem_Ioi.mpr hq) (Set.mem_Ioi.mpr hq1) hqq.le
  have a2 := renyiN_antitoneOn hSX h₂ (Set.mem_Ioi.mpr hq) (Set.mem_Ioi.mpr hq1) hqq.le
  have a3 := renyiN_antitoneOn hSX h₃ (Set.mem_Ioi.mpr hq) (Set.mem_Ioi.mpr hq1) hqq.le
  have hSle : S q₁ ≤ S q := by simp only [hS]; linarith
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have k1 := key q₁ hq1
    have k0 := key q hq
    have : 0 ≤ S q₁ := by
      have h0 : 0 ≤ renyiSpec q₁ hsSpec - renyiE q₁ l₁ l₂ l₃ := by linarith
      rw [k1] at h0
      exact nonneg_of_mul_nonneg_right h0 (hc q₁ hq1)
    have : 0 ≤ renyiSpec q hsSpec - renyiE q l₁ l₂ l₃ := by
      rw [k0]; exact mul_nonneg (hc q hq).le (by linarith)
    linarith
  · intro h
    have k1 := key q₁ hq1
    have k0 := key q hq
    have : 0 < S q₁ := by
      have h0 : 0 < renyiSpec q₁ hsSpec - renyiE q₁ l₁ l₂ l₃ := by linarith
      rw [k1] at h0
      exact pos_of_mul_pos_right h0 (hc q₁ hq1).le
    have : 0 < renyiSpec q hsSpec - renyiE q l₁ l₂ l₃ := by
      rw [k0]; exact mul_pos (hc q hq) (by linarith)
    linarith
  · intro h heq
    have k1 := key q₁ hq1
    have k0 := key q hq
    have hS1 : 0 ≤ S q₁ := by
      have h0 : 0 ≤ renyiSpec q₁ hsSpec - renyiE q₁ l₁ l₂ l₃ := by linarith
      rw [k1] at h0
      exact nonneg_of_mul_nonneg_right h0 (hc q₁ hq1)
    have hS0 : S q = 0 := by
      have h0 : renyiSpec q hsSpec - renyiE q l₁ l₂ l₃ = 0 := by linarith
      rw [k0] at h0
      exact (mul_eq_zero.mp h0).resolve_left (hc q hq).ne'
    have s1 := fun hn => renyiN_strictAntiOn hSX h₁ hn (Set.mem_Ioi.mpr hq) (Set.mem_Ioi.mpr hq1) hqq
    have s2 := fun hn => renyiN_strictAntiOn hSX h₂ hn (Set.mem_Ioi.mpr hq) (Set.mem_Ioi.mpr hq1) hqq
    have s3 := fun hn => renyiN_strictAntiOn hSX h₃ hn (Set.mem_Ioi.mpr hq) (Set.mem_Ioi.mpr hq1) hqq
    refine ⟨?_, ?_, ?_⟩ <;> by_contra hn
    · have := s1 hn; simp only [hS] at hS0 hS1; linarith
    · have := s2 hn; simp only [hS] at hS0 hS1; linarith
    · have := s3 hn; simp only [hS] at hS0 hS1; linarith

end FormalResearch.FourQubitEntropy
