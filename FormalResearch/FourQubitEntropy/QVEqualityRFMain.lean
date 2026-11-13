module

public import FormalResearch.FourQubitEntropy.QVEqualityRFSpec
public import FormalResearch.FourQubitEntropy.QVEqualityState
public import FormalResearch.FourQubitEntropy.QVEqualityBell

/-!
# `prop:fqe-critical-variance` (RF): the equality case and its attainment

Paper E, `renyi_compatibility.tex`: for a pure four-qubit state with `P = 1` and `s = (24 V_P)^{1/4}`,

* `critical_rf` (`QVEqualityState.lean`): `F ≥ (3/2)s² - s³`;
* `critical_rf_equality_iff`: for `0 < s < 1`, equality holds iff the cut spectra are `(RF-eq)` (`IsRfTriple`),
  up to ordering of cuts and eigenvalues; `critical_rf_equality_zero`, `critical_rf_equality_one`: the endpoints
  are the HS and the cluster spectra;
* `critical_rf_attained`: for every `s ∈ [0,1]` these spectra are attained by a unit state with `P = 1`;
* `critical_T_add_U_le`: the weaker bound `T + Σ_j p_j² ≤ 3/4` (`F ≥ 12 V_P`), with equality only at HS or
  cluster spectra.
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.QVEquality

open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.RenyiFull

/-- `a = (1+2s)/3`, `b = (1-s)/3` for `s ∈ [0,1]`: `a, b ≥ 0`, `ab ≥ 0`. -/
theorem rf_vals {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    RenyiFull.Pm (rfSpec1 s) (rfSpec2 s) (rfSpec2 s) = 1 ∧
    RenyiFull.Fm (rfSpec1 s) (rfSpec2 s) (rfSpec2 s) = 3 / 2 * s ^ 2 - s ^ 3 ∧
    24 * RenyiFull.Vm (rfSpec1 s) (rfSpec2 s) (rfSpec2 s) = s ^ 4 := by
  set t := Real.sqrt ((1 + 2 * s) / 3 * ((1 - s) / 3)) with ht
  have ht2 : t ^ 2 = (1 + 2 * s) / 3 * ((1 - s) / 3) :=
    Real.sq_sqrt (mul_nonneg (by linarith) (by linarith))
  have hP : RenyiFull.Pm (rfSpec1 s) (rfSpec2 s) (rfSpec2 s) = 1 := by
    unfold RenyiFull.Pm RenyiFull.pur rfSpec1 rfSpec2 rfSpec1' rfSpec2'
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [← ht]
    linear_combination 1 * ht2
  refine ⟨hP, ?_, ?_⟩
  · unfold RenyiFull.Fm RenyiFull.Tm RenyiFull.cub RenyiFull.Pm RenyiFull.pur
    unfold rfSpec1 rfSpec2 rfSpec1' rfSpec2'
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [← ht]
    linear_combination (3 * s + 5) * ht2
  · unfold RenyiFull.Vm RenyiFull.Pm RenyiFull.pur
    unfold rfSpec1 rfSpec2 rfSpec1' rfSpec2'
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [← ht]
    linear_combination (-4 * (7 * s ^ 2 + s - 9 * t ^ 2 + 1) / 9) * ht2

theorem Pm_swap12 (a b c : Fin 4 → ℝ) : RenyiFull.Pm a b c = RenyiFull.Pm b a c := by
  unfold RenyiFull.Pm; ring
theorem Pm_swap13 (a b c : Fin 4 → ℝ) : RenyiFull.Pm a b c = RenyiFull.Pm c b a := by
  unfold RenyiFull.Pm; ring
theorem Fm_swap12 (a b c : Fin 4 → ℝ) : RenyiFull.Fm a b c = RenyiFull.Fm b a c := by
  unfold RenyiFull.Fm RenyiFull.Tm; rw [Pm_swap12]; ring
theorem Fm_swap13 (a b c : Fin 4 → ℝ) : RenyiFull.Fm a b c = RenyiFull.Fm c b a := by
  unfold RenyiFull.Fm RenyiFull.Tm; rw [Pm_swap13]; ring
theorem Vm_swap12 (a b c : Fin 4 → ℝ) : RenyiFull.Vm a b c = RenyiFull.Vm b a c := by
  unfold RenyiFull.Vm RenyiFull.Pm; ring
theorem Vm_swap13 (a b c : Fin 4 → ℝ) : RenyiFull.Vm a b c = RenyiFull.Vm c b a := by
  unfold RenyiFull.Vm RenyiFull.Pm; ring

/-- The `(RF-eq)` spectra have `P = 1`, `F = (3/2)s² - s³`, `24 V = s⁴`. -/
theorem rfTriple_vals {l₂ l₃ l₄ : Fin 4 → ℝ} {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (h : IsRfTriple l₂ l₃ l₄ s) :
    RenyiFull.Pm l₂ l₃ l₄ = 1 ∧ RenyiFull.Fm l₂ l₃ l₄ = 3 / 2 * s ^ 2 - s ^ 3 ∧
      24 * RenyiFull.Vm l₂ l₃ l₄ = s ^ 4 := by
  obtain ⟨hP, hF, hV⟩ := rf_vals hs0 hs1
  rcases h with ⟨h2, h3, h4⟩ | ⟨h2, h3, h4⟩ | ⟨h2, h3, h4⟩
  · exact ⟨by rw [Pm_equiv h2 h3 h4]; exact hP, by rw [Fm_equiv h2 h3 h4]; exact hF,
      by rw [Vm_equiv h2 h3 h4]; exact hV⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [Pm_equiv h2 h3 h4, Pm_swap12]; exact hP
    · rw [Fm_equiv h2 h3 h4, Fm_swap12]; exact hF
    · rw [Vm_equiv h2 h3 h4, Vm_swap12]; exact hV
  · refine ⟨?_, ?_, ?_⟩
    · rw [Pm_equiv h2 h3 h4, Pm_swap13]; exact hP
    · rw [Fm_equiv h2 h3 h4, Fm_swap13]; exact hF
    · rw [Vm_equiv h2 h3 h4, Vm_swap13]; exact hV

/-- **(RF-eq) spectra attain equality in (RF)** (state form): if the cut spectra of a unit state are the
`(RF-eq)` triple for some `s ∈ [0,1]`, then `P = 1`, `24 V_P = s⁴` and `F = (3/2)s² - s³`. -/
theorem rf_spectra_equality {ψ : Psi} (hψ : normSqPsi ψ = 1) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (h : IsRfTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) s) :
    purity ψ = 1 ∧ 24 * VP ψ = s ^ 4 ∧ sexticF ψ = 3 / 2 * s ^ 2 - s ^ 3 := by
  obtain ⟨hP, hF, hV⟩ := rfTriple_vals hs0 hs1 h
  refine ⟨by rw [← Pm_cutSpec]; exact hP, by rw [VP_eq_Vm]; exact hV, by rw [← Fm_cutSpec ψ hψ]; exact hF⟩

theorem IsRfTriple.of_equiv {l₂ l₃ l₄ l₂' l₃' l₄' : Fin 4 → ℝ} {s : ℝ} (h : IsRfTriple l₂' l₃' l₄' s)
    (e2 : SpecEquiv l₂ l₂') (e3 : SpecEquiv l₃ l₃') (e4 : SpecEquiv l₄ l₄') : IsRfTriple l₂ l₃ l₄ s := by
  rcases h with ⟨h2, h3, h4⟩ | ⟨h2, h3, h4⟩ | ⟨h2, h3, h4⟩
  · exact Or.inl ⟨e2.trans' h2, e3.trans' h3, e4.trans' h4⟩
  · exact Or.inr (Or.inl ⟨e2.trans' h2, e3.trans' h3, e4.trans' h4⟩)
  · exact Or.inr (Or.inr ⟨e2.trans' h2, e3.trans' h3, e4.trans' h4⟩)

theorem gfun_eq (s : ℝ) : gfun s = 1 - 3 * s ^ 2 + 2 * s ^ 3 := by unfold gfun; ring

/-- **Equality in (RF), `0 < s < 1`** (`prop:fqe-critical-variance`, forward direction): a unit state with
`P = 1`, `s = (24 V_P)^{1/4} ∈ (0,1)` and `F = (3/2)s² - s³` has the `(RF-eq)` cut spectra. -/
theorem critical_rf_equality (ψ : Psi) (hψ : normSqPsi ψ = 1) (hP : purity ψ = 1) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hs4 : s ^ 4 = 24 * VP ψ) (hF : sexticF ψ = 3 / 2 * s ^ 2 - s ^ 3) :
    IsRfTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) s := by
  obtain ⟨m, n, hm, hn, e2, e3, e4⟩ := critical_cut_data ψ hψ hP
  obtain ⟨ξ, hξ, hξ1, hξ4⟩ := exists_xi m hm
  obtain ⟨ζ, hζ, hζ1, hζ4⟩ := exists_xi n hn
  have hV : 24 * RenyiFull.Vm (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) = (ξ * ζ) ^ 4 := by
    rw [Vm_equiv e2 e3 e4, Vm_core m n hm hn, mul_pow, hξ4, hζ4]
  have hsξζ : s = ξ * ζ := by
    have h1 : s ^ 4 = (ξ * ζ) ^ 4 := by rw [hs4, VP_eq_Vm, hV]
    exact (pow_left_inj₀ hs0.le (mul_nonneg hξ hζ) (by norm_num)).mp h1
  have hF' : RenyiFull.Fm (spc0 m n) (spc1 m n) (spc2 m n) = 3 / 2 * s ^ 2 - s ^ 3 := by
    rw [← Fm_equiv e2 e3 e4, Fm_cutSpec ψ hψ]; exact hF
  rw [Fm_core m n hm hn] at hF'
  have h27 : 27 * kap m n = gfun (ξ * ζ) := by
    rw [← hsξζ, gfun_eq]; linarith
  obtain ⟨hξζ, hκ, hA, hB⟩ := rf_equality_core (sq_nonneg (m 0)) (sq_nonneg (m 1)) (sq_nonneg (m 2)) hm
    (sq_nonneg (n 0)) (sq_nonneg (n 1)) (sq_nonneg (n 2)) hn (kap_sq m n) hξ hξ4 hζ hζ4 h27
    (by rw [← hsξζ]; exact hs0) (by rw [← hsξζ]; exact hs1)
  have hss : ξ ^ 2 = s := by rw [hsξζ, ← hξζ]; ring
  rw [hss] at hA hB
  exact IsRfTriple.of_equiv (spc_rf_triple m n hs0 hs1 hκ hA hB) e2 e3 e4

/-- **`prop:fqe-critical-variance`, equality case, `0 < s < 1`** (iff form). -/
theorem critical_rf_equality_iff (ψ : Psi) (hψ : normSqPsi ψ = 1) (hP : purity ψ = 1) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hs4 : s ^ 4 = 24 * VP ψ) :
    sexticF ψ = 3 / 2 * s ^ 2 - s ^ 3 ↔
      IsRfTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) s :=
  ⟨critical_rf_equality ψ hψ hP hs0 hs1 hs4,
    fun h => (rf_spectra_equality hψ hs0.le hs1.le h).2.2⟩

/-! ### The endpoints `s = 0, 1` and the weaker bound `F ≥ 12 V_P` -/

theorem hs_triple_vals {l₂ l₃ l₄ : Fin 4 → ℝ} (h : IsHsTriple l₂ l₃ l₄) :
    RenyiFull.Pm l₂ l₃ l₄ = 1 ∧ RenyiFull.Fm l₂ l₃ l₄ = 0 ∧ RenyiFull.Vm l₂ l₃ l₄ = 0 := by
  obtain ⟨h2, h3, h4⟩ := h
  obtain ⟨a2, b2⟩ := pur_cub_of_hsPerm h2
  obtain ⟨a3, b3⟩ := pur_cub_of_hsPerm h3
  obtain ⟨a4, b4⟩ := pur_cub_of_hsPerm h4
  have hP : RenyiFull.Pm l₂ l₃ l₄ = 1 := by unfold RenyiFull.Pm; rw [a2, a3, a4]; norm_num
  refine ⟨hP, ?_, ?_⟩
  · unfold RenyiFull.Fm RenyiFull.Tm; rw [hP, b2, b3, b4]; norm_num
  · unfold RenyiFull.Vm; rw [hP, a2, a3, a4]; norm_num

theorem cluster_triple_vals {l₂ l₃ l₄ : Fin 4 → ℝ} (h : IsClusterTriple l₂ l₃ l₄) :
    RenyiFull.Pm l₂ l₃ l₄ = 1 ∧ RenyiFull.Fm l₂ l₃ l₄ = 1 / 2 ∧ 24 * RenyiFull.Vm l₂ l₃ l₄ = 1 := by
  rcases h with ⟨t2, f3, f4⟩ | ⟨f2, t3, f4⟩ | ⟨f2, f3, t4⟩
  · obtain ⟨a, b⟩ := uniformTwo_pur_cub t2
    have hP : RenyiFull.Pm l₂ l₃ l₄ = 1 := by
      unfold RenyiFull.Pm; rw [a, uniformFour_pur f3, uniformFour_pur f4]; norm_num
    refine ⟨hP, ?_, ?_⟩
    · unfold RenyiFull.Fm RenyiFull.Tm; rw [hP, b, uniformFour_cub f3, uniformFour_cub f4]; norm_num
    · unfold RenyiFull.Vm; rw [hP, a, uniformFour_pur f3, uniformFour_pur f4]; norm_num
  · obtain ⟨a, b⟩ := uniformTwo_pur_cub t3
    have hP : RenyiFull.Pm l₂ l₃ l₄ = 1 := by
      unfold RenyiFull.Pm; rw [a, uniformFour_pur f2, uniformFour_pur f4]; norm_num
    refine ⟨hP, ?_, ?_⟩
    · unfold RenyiFull.Fm RenyiFull.Tm; rw [hP, b, uniformFour_cub f2, uniformFour_cub f4]; norm_num
    · unfold RenyiFull.Vm; rw [hP, a, uniformFour_pur f2, uniformFour_pur f4]; norm_num
  · obtain ⟨a, b⟩ := uniformTwo_pur_cub t4
    have hP : RenyiFull.Pm l₂ l₃ l₄ = 1 := by
      unfold RenyiFull.Pm; rw [a, uniformFour_pur f2, uniformFour_pur f3]; norm_num
    refine ⟨hP, ?_, ?_⟩
    · unfold RenyiFull.Fm RenyiFull.Tm; rw [hP, b, uniformFour_cub f2, uniformFour_cub f3]; norm_num
    · unfold RenyiFull.Vm; rw [hP, a, uniformFour_pur f2, uniformFour_pur f3]; norm_num

/-- **(RF) at `s = 0`**: for `P = 1`, `V_P = 0`: `F = 0` iff the spectra are HS. -/
theorem critical_rf_equality_zero (ψ : Psi) (hψ : normSqPsi ψ = 1) (hP : purity ψ = 1) (hV : VP ψ = 0) :
    sexticF ψ = 0 ↔ IsHsTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) := by
  constructor
  · intro hF
    rcases critical_qk_equality ψ hψ hP (by rw [hF, hV]; norm_num) with h | h
    · exact h
    · exfalso
      have := (cluster_triple_vals h).2.2
      rw [← VP_eq_Vm, hV] at this; norm_num at this
  · intro h
    have := (hs_triple_vals h).2.1
    rw [Fm_cutSpec ψ hψ] at this; exact this

/-- **(RF) at `s = 1`**: for `P = 1`, `24 V_P = 1`: `F = 1/2` iff the spectra are cluster spectra. -/
theorem critical_rf_equality_one (ψ : Psi) (hψ : normSqPsi ψ = 1) (hP : purity ψ = 1)
    (hV : 24 * VP ψ = 1) :
    sexticF ψ = 1 / 2 ↔ IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) := by
  constructor
  · intro hF
    rcases critical_qk_equality ψ hψ hP (by rw [hF]; linarith) with h | h
    · exfalso
      have := (hs_triple_vals h).2.2
      rw [← VP_eq_Vm] at this; rw [this] at hV; norm_num at hV
    · exact h
  · intro h
    have := (cluster_triple_vals h).2.1
    rw [Fm_cutSpec ψ hψ] at this; exact this

/-- **The weaker bound** `F ≥ 12 V_P` at `P = 1` (equivalently `T + Σ_j p_j² ≤ 3/4`), with equality exactly at
HS or cluster spectra. -/
theorem critical_F_ge_12V (ψ : Psi) (hψ : normSqPsi ψ = 1) (hP : purity ψ = 1) :
    12 * VP ψ ≤ sexticF ψ ∧
      (sexticF ψ = 12 * VP ψ ↔ IsHsTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) ∨
        IsClusterTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) := by
  obtain ⟨s, hs0, hs1, hs4, hF⟩ := critical_rf ψ hψ hP
  have hkey : 12 * VP ψ + s ^ 2 * (1 - s) * (3 + s) / 2 ≤ sexticF ψ := by
    have : 12 * VP ψ = s ^ 4 / 2 := by linarith
    rw [this]; nlinarith
  have hpos : 0 ≤ s ^ 2 * (1 - s) * (3 + s) / 2 := by
    have : 0 ≤ 1 - s := by linarith
    positivity
  refine ⟨by linarith, ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h0 : s ^ 2 * (1 - s) * (3 + s) = 0 := by linarith
    have : s ^ 2 * (1 - s) = 0 ∨ 3 + s = 0 := mul_eq_zero.mp h0
    have hs01 : s = 0 ∨ s = 1 := by
      rcases this with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · left; exact pow_eq_zero_iff (two_ne_zero) |>.mp h2
        · right; linarith
      · exfalso; linarith
    have hEq : sexticF ψ ^ 2 = 6 * VP ψ := by
      rcases hs01 with rfl | rfl
      · have : VP ψ = 0 := by linarith
        rw [this] at h; rw [h, this]; norm_num
      · have hV : VP ψ = 1 / 24 := by linarith
        rw [h, hV]; norm_num
    exact critical_qk_equality ψ hψ hP hEq
  · rcases h with h | h
    · have := hs_triple_vals h
      have h1 := this.2.1; have h2 := this.2.2
      rw [Fm_cutSpec ψ hψ] at h1; rw [← VP_eq_Vm] at h2; rw [h1, h2]; norm_num
    · have := cluster_triple_vals h
      have h1 := this.2.1; have h2 := this.2.2
      rw [Fm_cutSpec ψ hψ] at h1; rw [← VP_eq_Vm] at h2
      rw [h1]; linarith

/-- `T + Σ_j p_j² ≤ 3/4` for `P = 1` (`prop:fqe-critical-variance`, last sentence). -/
theorem critical_T_add_U_le (ψ : Psi) (hψ : normSqPsi ψ = 1) (hP : purity ψ = 1) :
    cubicMoment ψ + (cutPurity12 ψ ^ 2 + cutPurity13 ψ ^ 2 + cutPurity14 ψ ^ 2) ≤ 3 / 4 := by
  have h := (critical_F_ge_12V ψ hψ hP).1
  have hF : sexticF ψ = 17 * purity ψ - 12 * cubicMoment ψ - 12 := by
    unfold sexticF; rw [hψ]; ring
  have hPe := purity_eq_cutPurities ψ
  unfold VP at h
  rw [hF, hP] at h
  rw [hP] at hPe
  nlinarith

/-! ### Attainment for every `s ∈ [0,1]` -/

/-- The explicit critical vector `c (1, iα, iβ, iβ)`. -/
noncomputable def rfVec (α β c : ℝ) : Fin 2 × Fin 2 → ℂ := fun k =>
  if k = (0, 0) then (c : ℂ)
  else if k = (0, 1) then Complex.I * ((α * c : ℝ) : ℂ)
  else Complex.I * ((β * c : ℝ) : ℂ)

theorem rfVec_normSq (α β c : ℝ) (hc : c ^ 2 = 1 / 2) (k : Fin 4) :
    Complex.normSq (rfVec α β c (eqv k)) = ![1 / 2, α ^ 2 / 2, β ^ 2 / 2, β ^ 2 / 2] k := by
  fin_cases k <;> simp [rfVec, eqv, Complex.normSq_apply]
  · linear_combination hc
  · linear_combination α ^ 2 * hc
  · linear_combination β ^ 2 * hc
  · linear_combination β ^ 2 * hc

theorem rfVec_wp (α β c : ℝ) (hc : c ^ 2 = 1 / 2) (k : Fin 4) :
    Complex.normSq (PaperECritical.wp (rfVec α β c) (eqv k)) =
      ![(1 + α ^ 2) / 8, (1 + α ^ 2) / 8, (1 + (α + 2 * β) ^ 2) / 8, (1 + (2 * β - α) ^ 2) / 8] k := by
  fin_cases k <;> simp [rfVec, eqv, PaperECritical.wp, Complex.normSq_apply]
  · linear_combination (1 + α ^ 2) / 4 * hc
  · linear_combination (1 + α ^ 2) / 4 * hc
  · linear_combination (1 + (α + 2 * β) ^ 2) / 4 * hc
  · linear_combination (1 + (2 * β - α) ^ 2) / 4 * hc

theorem rfVec_wm (α β c : ℝ) (hc : c ^ 2 = 1 / 2) (k : Fin 4) :
    Complex.normSq (PaperECritical.wm (rfVec α β c) (eqv k)) =
      ![(1 + (α + 2 * β) ^ 2) / 8, (1 + (α - 2 * β) ^ 2) / 8, (1 + α ^ 2) / 8, (1 + α ^ 2) / 8] k := by
  fin_cases k <;> simp [rfVec, eqv, PaperECritical.wm, Complex.normSq_apply]
  · linear_combination (1 + (α + 2 * β) ^ 2) / 4 * hc
  · linear_combination (1 + (α - 2 * β) ^ 2) / 4 * hc
  · linear_combination (1 + α ^ 2) / 4 * hc
  · linear_combination (1 + α ^ 2) / 4 * hc

/-- **Attainment of (RF-eq)**: for every `s ∈ [0,1]` there is a unit state with `P = 1` whose cut spectra are the
`(RF-eq)` triple (the critical vector `G(c(1, iα, iβ, iβ))`, `α² = (1+2s)/3`, `β² = (1-s)/3`, `c² = 1/2`). -/
theorem rf_attained {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∃ ψ : Psi, normSqPsi ψ = 1 ∧ purity ψ = 1 ∧
      IsRfTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) s := by
  have ha : 0 ≤ (1 + 2 * s) / 3 := by linarith
  have hb : 0 ≤ (1 - s) / 3 := by linarith
  set a : ℝ := (1 + 2 * s) / 3 with hadef
  set b : ℝ := (1 - s) / 3 with hbdef
  have hab : a + 2 * b = 1 := by rw [hadef, hbdef]; ring
  set α : ℝ := Real.sqrt a with hαdef
  set β : ℝ := Real.sqrt b with hβdef
  set c : ℝ := Real.sqrt (1 / 2) with hcdef
  have hα : α ^ 2 = a := Real.sq_sqrt ha
  have hβ : β ^ 2 = b := Real.sq_sqrt hb
  have hc : c ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hαβ : α * β = Real.sqrt (a * b) := by rw [Real.sqrt_mul ha]
  set v := rfVec α β c with hv
  have hn : ∑ k, Complex.normSq (v k) = 1 := by
    have := Equiv.sum_comp eqv (fun k => Complex.normSq (v k))
    rw [← this]
    simp only [hv, rfVec_normSq α β c hc, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val]
    rw [hα, hβ]; linarith
  have hτ : ∑ k, v k ^ 2 = 0 := by
    have h0 : (1 - α ^ 2 - 2 * β ^ 2 : ℝ) = 0 := by rw [hα, hβ]; linarith
    have h1 : ((c ^ 2 * (1 - α ^ 2 - 2 * β ^ 2) : ℝ) : ℂ) = 0 := by rw [h0]; simp
    simp only [hv, rfVec, Fintype.sum_prod_type, Fin.sum_univ_two]
    simp
    push_cast at h1
    linear_combination h1 + ((c : ℂ) ^ 2 * (α : ℂ) ^ 2 + 2 * (c : ℂ) ^ 2 * (β : ℂ) ^ 2) * Complex.I_sq
  have hP : purity (PaperECritical.Gv v) = 1 := by
    have := PaperECritical.Gv_purity_tau v hn
    rw [hτ] at this; simp at this; linarith
  refine ⟨PaperECritical.Gv v, by rw [PaperECritical.Gv_n]; exact hn, hP, ?_⟩
  have l12 : SpecEquiv (cutSpec₂ (PaperECritical.Gv v)) (rfSpec1 s) := by
    refine specEquiv_cutSpec₂ _ (listing12_of_diag v _ (fun k => ?_))
    rw [rfVec_normSq α β c hc k]
    fin_cases k <;> simp [rfSpec1, rfSpec1', hα, hβ] <;> rfl
  have l13 : SpecEquiv (cutSpec₃ (PaperECritical.Gv v)) (rfSpec2 s) := by
    refine (specEquiv_cutSpec₃ _ (listing13_of_diag v
      ![(1 + α ^ 2) / 8, (1 + α ^ 2) / 8, (1 + (α + 2 * β) ^ 2) / 8, (1 + (2 * β - α) ^ 2) / 8]
      (fun k => (rfVec_wp α β c hc k).symm))).trans' ?_
    refine ⟨⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩, fun i => ?_⟩
    have : rfSpec2 s = rfSpec2' (α * β) b := by unfold rfSpec2; rw [hαβ]
    rw [this]
    fin_cases i <;> simp [rfSpec2'] <;> nlinarith [hα, hβ, hab]
  have l14 : SpecEquiv (cutSpec₄ (PaperECritical.Gv v)) (rfSpec2 s) := by
    refine (specEquiv_cutSpec₄ _ (listing14_of_diag v
      ![(1 + (α + 2 * β) ^ 2) / 8, (1 + (α - 2 * β) ^ 2) / 8, (1 + α ^ 2) / 8, (1 + α ^ 2) / 8]
      (fun k => (rfVec_wm α β c hc k).symm))).trans' ?_
    refine ⟨1, fun i => ?_⟩
    have : rfSpec2 s = rfSpec2' (α * β) b := by unfold rfSpec2; rw [hαβ]
    rw [this]
    fin_cases i <;> simp [rfSpec2'] <;> nlinarith [hα, hβ, hab]
  exact Or.inl ⟨l12, l13, l14⟩

/-- **Sharpness of (RF) for every `s ∈ [0,1]`**: a unit state with `P = 1`, `24 V_P = s⁴`,
`F = (3/2)s² - s³` and the `(RF-eq)` cut spectra. -/
theorem critical_rf_attained {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∃ ψ : Psi, normSqPsi ψ = 1 ∧ purity ψ = 1 ∧ s ^ 4 = 24 * VP ψ ∧
      sexticF ψ = 3 / 2 * s ^ 2 - s ^ 3 ∧ IsRfTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ) s := by
  obtain ⟨ψ, hψ, hP, h⟩ := rf_attained hs0 hs1
  obtain ⟨-, hV, hF⟩ := rf_spectra_equality hψ hs0 hs1 h
  exact ⟨ψ, hψ, hP, hV.symm, hF, h⟩

end FormalResearch.FourQubitEntropy.QVEquality

/-- info: 'FormalResearch.FourQubitEntropy.QVEquality.critical_rf_equality_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.FourQubitEntropy.QVEquality.critical_rf_equality_iff

/-- info: 'FormalResearch.FourQubitEntropy.QVEquality.critical_rf_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.FourQubitEntropy.QVEquality.critical_rf_attained

/-- info: 'FormalResearch.FourQubitEntropy.QVEquality.critical_rf_equality_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.FourQubitEntropy.QVEquality.critical_rf_equality_zero

/-- info: 'FormalResearch.FourQubitEntropy.QVEquality.critical_rf_equality_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.FourQubitEntropy.QVEquality.critical_rf_equality_one

/-- info: 'FormalResearch.FourQubitEntropy.QVEquality.critical_F_ge_12V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.FourQubitEntropy.QVEquality.critical_F_ge_12V

/-- info: 'FormalResearch.FourQubitEntropy.QVEquality.critical_T_add_U_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.FourQubitEntropy.QVEquality.critical_T_add_U_le
