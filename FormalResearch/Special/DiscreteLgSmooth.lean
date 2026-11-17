module

public import FormalResearch.Special.DiscreteLgMatch

/-!
# Smooth chain coefficients give an LG datum

For `A, u ∈ C²` on an open set `U₀ ⊇ [c, d]` with `A > 0`, `|u| < 1` (the oscillatory side), the Liouville-Green datum of `DiscreteLgDefect` exists on `(c, d)`:
`θ = arccos u`, `w = (A sin θ)^{-1/2} = (√(A √(1 - u²)))⁻¹`, `Θ = ∫_c^t θ`; the constants `lo, hi, M` come from compactness of `[c, d]`.
This makes `dlg_bulk` and `dlg_airy_match` applicable to every smooth symmetric Jacobi chain `a_k ≈ A(q_k - h/2)`, `c_k ≈ 2 A(q_k) u(q_k)`.

**Claim class: proved.**  **Not formalised here:** the closed-form Hahn/Racah instance (the closeness `|a_k - A(q_k - h/2)| ≤ E h²` is `hr_perturb`'s job).
-/

@[expose] public section

open Set FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special

/-- `C²` functions on an open set have bounded value, first and second derivative on a compact subset. -/
lemma dlgs_c2_bound {f : ℝ → ℝ} {U0 : Set ℝ} (hU0 : IsOpen U0) (hf : ContDiffOn ℝ 2 f U0) {K : Set ℝ} (hK : IsCompact K)
    (hKU : K ⊆ U0) : ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ K, |f t| ≤ B ∧ |deriv f t| ≤ B ∧ |deriv (deriv f) t| ≤ B := by
  have h1 : ContDiffOn ℝ 1 (deriv f) U0 := hf.deriv_of_isOpen hU0 (by norm_num)
  have c0 : ContinuousOn f K := hf.continuousOn.mono hKU
  have c1 : ContinuousOn (deriv f) K := (hf.continuousOn_deriv_of_isOpen hU0 (by norm_num)).mono hKU
  have c2 : ContinuousOn (deriv (deriv f)) K := (h1.continuousOn_deriv_of_isOpen hU0 le_rfl).mono hKU
  obtain ⟨B0, hB0⟩ := hK.exists_bound_of_continuousOn c0
  obtain ⟨B1, hB1⟩ := hK.exists_bound_of_continuousOn c1
  obtain ⟨B2, hB2⟩ := hK.exists_bound_of_continuousOn c2
  refine ⟨max (max |B0| |B1|) |B2|, by positivity, fun t ht => ⟨?_, ?_, ?_⟩⟩
  · have := hB0 t ht; rw [Real.norm_eq_abs] at this
    exact this.trans ((le_abs_self _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  · have := hB1 t ht; rw [Real.norm_eq_abs] at this
    exact this.trans ((le_abs_self _).trans ((le_max_right _ _).trans (le_max_left _ _)))
  · have := hB2 t ht; rw [Real.norm_eq_abs] at this
    exact this.trans ((le_abs_self _).trans (le_max_right _ _))


/-- The concrete LG data of a smooth oscillatory coefficient pair `(A, u)`. -/
noncomputable def dlgsTheta (u : ℝ → ℝ) (t : ℝ) : ℝ := Real.arccos (u t)

noncomputable def dlgsW (A u : ℝ → ℝ) (t : ℝ) : ℝ := (√(A t * √(1 - u t ^ 2)))⁻¹

noncomputable def dlgsPhase (u : ℝ → ℝ) (c t : ℝ) : ℝ := ∫ s in c..t, dlgsTheta u s

lemma dlgs_theta_diff {u : ℝ → ℝ} {U0 : Set ℝ} (hU0 : IsOpen U0) (hu : ContDiffOn ℝ 2 u U0)
    (hu1 : ∀ t ∈ U0, |u t| < 1) : ContDiffOn ℝ 2 (dlgsTheta u) U0 := by
  intro t ht
  have h1 : u t ≠ -1 := fun h => by have := hu1 t ht; rw [h] at this; simp at this
  have h2 : u t ≠ 1 := fun h => by have := hu1 t ht; rw [h] at this; simp at this
  have := (Real.contDiffAt_arccos (n := 2) h1 h2).comp t (hu.contDiffAt (hU0.mem_nhds ht))
  exact this.contDiffWithinAt

lemma dlgs_w_diff {A u : ℝ → ℝ} {U0 : Set ℝ} (hU0 : IsOpen U0) (hA : ContDiffOn ℝ 2 A U0) (hu : ContDiffOn ℝ 2 u U0)
    (hApos : ∀ t ∈ U0, 0 < A t) (hu1 : ∀ t ∈ U0, |u t| < 1) : ContDiffOn ℝ 2 (dlgsW A u) U0 := by
  intro t ht
  have hu2 : 0 < 1 - u t ^ 2 := by
    have := hu1 t ht
    have : u t ^ 2 < 1 := by nlinarith [abs_nonneg (u t), sq_abs (u t)]
    linarith
  have hAt : ContDiffAt ℝ 2 A t := hA.contDiffAt (hU0.mem_nhds ht)
  have hut : ContDiffAt ℝ 2 u t := hu.contDiffAt (hU0.mem_nhds ht)
  have hs : ContDiffAt ℝ 2 (fun s => √(1 - u s ^ 2)) t :=
    ((contDiffAt_const.sub (hut.pow 2)).sqrt hu2.ne')
  have hAs : ContDiffAt ℝ 2 (fun s => A s * √(1 - u s ^ 2)) t := hAt.mul hs
  have hpos : 0 < A t * √(1 - u t ^ 2) := mul_pos (hApos t ht) (Real.sqrt_pos.2 hu2)
  have hq : ContDiffAt ℝ 2 (fun s => √(A s * √(1 - u s ^ 2))) t := hAs.sqrt hpos.ne'
  exact (hq.inv (Real.sqrt_pos.2 hpos).ne').contDiffWithinAt

lemma dlgs_rel {A u : ℝ → ℝ} {t : ℝ} (hA : 0 < A t) (hu : |u t| < 1) :
    A t * dlgsW A u t ^ 2 * Real.sin (dlgsTheta u t) = 1 := by
  have hu2 : 0 < 1 - u t ^ 2 := by
    have : u t ^ 2 < 1 := by nlinarith [abs_nonneg (u t), sq_abs (u t)]
    linarith
  have hs : 0 < √(1 - u t ^ 2) := Real.sqrt_pos.2 hu2
  have hpos : 0 < A t * √(1 - u t ^ 2) := mul_pos hA hs
  unfold dlgsW dlgsTheta
  rw [Real.sin_arccos, inv_pow, Real.sq_sqrt hpos.le]
  field_simp

/-- **Smooth data give an LG datum** on `(c, d) ⊂ [c, d] ⊆ U₀`. -/
theorem dlg_smooth_data {A u : ℝ → ℝ} {U0 : Set ℝ} (hU0 : IsOpen U0) {c d : ℝ} (hcd : c < d) (hsub : Icc c d ⊆ U0)
    (hA : ContDiffOn ℝ 2 A U0) (hu : ContDiffOn ℝ 2 u U0) (hApos : ∀ t ∈ U0, 0 < A t) (hu1 : ∀ t ∈ U0, |u t| < 1) :
    ∃ lo hi M : ℝ, DlgData A (dlgsTheta u) (dlgsW A u) (dlgsPhase u c) (Ioo c d) lo hi M ∧
      ∀ t ∈ Ioo c d, Real.cos (dlgsTheta u t) = u t := by
  have hθ := dlgs_theta_diff hU0 hu hu1
  have hw := dlgs_w_diff hU0 hA hu hApos hu1
  have hK : IsCompact (Icc c d) := isCompact_Icc
  have hne : (Icc c d).Nonempty := ⟨c, left_mem_Icc.2 hcd.le⟩
  obtain ⟨BA, hBA0, hBA⟩ := dlgs_c2_bound hU0 hA hK hsub
  obtain ⟨Bθ, hBθ0, hBθ⟩ := dlgs_c2_bound hU0 hθ hK hsub
  obtain ⟨Bw, hBw0, hBw⟩ := dlgs_c2_bound hU0 hw hK hsub
  have wpos : ∀ t ∈ U0, 0 < dlgsW A u t := fun t ht => by
    have hu2 : 0 < 1 - u t ^ 2 := by
      have : u t ^ 2 < 1 := by nlinarith [hu1 t ht, abs_nonneg (u t), sq_abs (u t)]
      linarith
    unfold dlgsW
    exact inv_pos.2 (Real.sqrt_pos.2 (mul_pos (hApos t ht) (Real.sqrt_pos.2 hu2)))
  obtain ⟨tA, htA, hmA⟩ := hK.exists_isMinOn hne (hA.continuousOn.mono hsub)
  obtain ⟨tw, htw, hmw⟩ := hK.exists_isMinOn hne (hw.continuousOn.mono hsub)
  have hAmin : ∀ t ∈ Icc c d, A tA ≤ A t := fun t ht => hmA ht
  have hwmin : ∀ t ∈ Icc c d, dlgsW A u tw ≤ dlgsW A u t := fun t ht => hmw ht
  have hlo : 0 < min (A tA) (dlgsW A u tw) := lt_min (hApos _ (hsub htA)) (wpos _ (hsub htw))
  refine ⟨min (A tA) (dlgsW A u tw), max BA Bw, max (max BA Bθ) Bw, ⟨isOpen_Ioo, convex_Ioo c d, hlo, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (hBA0.trans (le_max_left _ _)).trans (le_max_left _ _)
  · exact hA.mono (Ioo_subset_Icc_self.trans hsub)
  · exact hθ.mono (Ioo_subset_Icc_self.trans hsub)
  · exact hw.mono (Ioo_subset_Icc_self.trans hsub)
  · intro t ht
    have hc : ContinuousOn (dlgsTheta u) U0 := hθ.continuousOn
    have hint : IntervalIntegrable (dlgsTheta u) MeasureTheory.volume c t := by
      apply ContinuousOn.intervalIntegrable
      refine hc.mono (fun s hs => hsub ?_)
      rw [uIcc_of_le ht.1.le] at hs
      exact ⟨hs.1, hs.2.trans ht.2.le⟩
    exact intervalIntegral.integral_hasDerivAt_right hint (hc.stronglyMeasurableAtFilter hU0 t (hsub (Ioo_subset_Icc_self ht)))
      (hc.continuousAt (hU0.mem_nhds (hsub (Ioo_subset_Icc_self ht))))
  · intro t ht
    have ht' := Ioo_subset_Icc_self ht
    exact ⟨(min_le_left _ _).trans (hAmin t ht'), ((hBA t ht').1.trans' (le_abs_self _)).trans (le_max_left _ _)⟩
  · intro t ht
    have ht' := Ioo_subset_Icc_self ht
    exact ⟨(min_le_right _ _).trans (hwmin t ht'), ((hBw t ht').1.trans' (le_abs_self _)).trans (le_max_right _ _)⟩
  · intro t ht
    have ht' := Ioo_subset_Icc_self ht
    have a := hBA t ht'
    have b := hBθ t ht'
    have c' := hBw t ht'
    have m1 : BA ≤ max (max BA Bθ) Bw := (le_max_left _ _).trans (le_max_left _ _)
    have m2 : Bθ ≤ max (max BA Bθ) Bw := (le_max_right _ _).trans (le_max_left _ _)
    have m3 : Bw ≤ max (max BA Bθ) Bw := le_max_right _ _
    exact ⟨a.2.1.trans m1, a.2.2.trans m1, b.2.1.trans m2, b.2.2.trans m2, c'.2.1.trans m3, c'.2.2.trans m3⟩
  · intro t ht
    exact dlgs_rel (hApos t (hsub (Ioo_subset_Icc_self ht))) (hu1 t (hsub (Ioo_subset_Icc_self ht)))
  · intro t ht
    have := hu1 t (hsub (Ioo_subset_Icc_self ht))
    unfold dlgsTheta
    exact Real.cos_arccos (abs_lt.1 this).1.le (abs_lt.1 this).2.le

/-- info: 'FormalResearch.Special.dlg_smooth_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dlg_smooth_data


/-- **Bulk Liouville-Green theorem for a smooth chain** (the user-facing form of `dlg_bulk`): only `A, u ∈ C²` with `A > 0`, `|u| < 1` on a neighbourhood
of `[c, d]` are assumed.  There are constants `h₀, C` such that every exact solution of the rows of a chain
`a_k ≈ A(q_k - h/2)`, `c_k ≈ 2 A(q_k) u(q_k)` (error `E h²`) on a lattice window of macroscopic length `≤ L` inside `(c, d)` is
`Y_k = R w(q_k) [cos(Θ(q_k)/h - φ₀) + O(h)]` with the explicit `θ = arccos u` (`dlgsTheta`), `w = dlgsW A u`, `Θ = dlgsPhase u c = ∫_c^· θ`, with `R ≍ |Y_m| + |Y_{m+1}|` for any bond `m` of the window. -/
theorem dlg_bulk_smooth {A u : ℝ → ℝ} {U0 : Set ℝ} (hU0 : IsOpen U0) {c d : ℝ} (hcd : c < d) (hsub : Icc c d ⊆ U0)
    (hA : ContDiffOn ℝ 2 A U0) (hu : ContDiffOn ℝ 2 u U0) (hApos : ∀ t ∈ U0, 0 < A t) (hu1 : ∀ t ∈ U0, |u t| < 1)
    (E L : ℝ) (hE : 0 ≤ E) (hL : 0 ≤ L) :
    ∃ h0 C : ℝ, 0 < h0 ∧ h0 ≤ 1 ∧ 0 < C ∧
      ∀ (q0 h : ℝ) (a c' Y : ℤ → ℝ) (J N m : ℤ), 0 < h → h ≤ h0 → J ≤ m → m ≤ N → ((N - J : ℤ) : ℝ) * h ≤ L →
        (∀ k ∈ Finset.Icc J (N + 1), dlgQ q0 h k ∈ Ioo c d) →
        (∀ k ∈ Finset.Icc (J + 1) (N + 1), |a k - A (dlgQ q0 h k - h / 2)| ≤ E * h ^ 2) →
        (∀ k ∈ Finset.Icc (J + 1) N, |c' k - 2 * A (dlgQ q0 h k) * u (dlgQ q0 h k)| ≤ E * h ^ 2) →
        (∀ k ∈ Finset.Icc (J + 1) N, jac a c' Y k = 0) →
        ∃ R φ0 : ℝ, 0 ≤ R ∧
          (∀ k ∈ Finset.Icc J (N + 1), |Y k - R * dlgsW A u (dlgQ q0 h k) *
              Real.cos (dlgP (dlgsPhase u c) q0 h k - φ0)| ≤ C * h * R * dlgsW A u (dlgQ q0 h k)) ∧
          R ≤ C * (|Y m| + |Y (m + 1)|) ∧ |Y m| + |Y (m + 1)| ≤ C * R := by
  obtain ⟨lo, hi, M, D, hcos⟩ := dlg_smooth_data hU0 hcd hsub hA hu hApos hu1
  have hmid : (c + d) / 2 ∈ Ioo c d := ⟨by linarith, by linarith⟩
  have hhi : 0 ≤ hi := ((D.Ab _ hmid).1.trans' D.lo_pos.le).trans (D.Ab _ hmid).2
  obtain ⟨h0, C, hh0, hh01, hC, H⟩ := dlg_bulk lo hi M E L D.lo_pos hhi D.M_nonneg hE hL
  refine ⟨h0, C, hh0, hh01, hC, ?_⟩
  intro q0 h a c' Y J N m hh hhh0 hJm hmN hlen hU hA' hC' hY
  refine H D q0 h a c' Y J N m hh hhh0 hJm hmN hlen hU hA' (fun k hk => ?_) hY
  have hq : dlgQ q0 h k ∈ Ioo c d := hU k (by rw [Finset.mem_Icc] at hk ⊢; omega)
  rw [hcos _ hq]
  exact hC' k hk

/-- info: 'FormalResearch.Special.dlg_bulk_smooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dlg_bulk_smooth


/-- **Airy matching for a smooth chain** (the user-facing form of `dlg_airy_match`): same assumptions as `dlg_bulk_smooth`; the matching hypotheses `DlgAiryAt` at the two
sites `m, m+1` give the Maslov-offset form on the whole window, with the explicit `θ = arccos u`, `w = dlgsW A u`, `Θ = dlgsPhase u c`. -/
theorem dlg_airy_match_smooth {A u : ℝ → ℝ} {U0 : Set ℝ} (hU0 : IsOpen U0) {c d : ℝ} (hcd : c < d) (hsub : Icc c d ⊆ U0)
    (hA : ContDiffOn ℝ 2 A U0) (hu : ContDiffOn ℝ 2 u U0) (hApos : ∀ t ∈ U0, 0 < A t) (hu1 : ∀ t ∈ U0, |u t| < 1)
    (E L : ℝ) (hE : 0 ≤ E) (hL : 0 ≤ L) :
    ∃ h0 C : ℝ, 0 < h0 ∧ h0 ≤ 1 ∧ 0 < C ∧
      ∀ (q0 h : ℝ) (a c' Y : ℤ → ℝ) (J N m : ℤ) (κ μ Ts Φmin gmin Ca : ℝ), 0 < Φmin → 0 < gmin → 0 ≤ Ca →
        0 < h → h ≤ h0 → J ≤ m → m ≤ N → ((N - J : ℤ) : ℝ) * h ≤ L →
        (∀ k ∈ Finset.Icc J (N + 1), dlgQ q0 h k ∈ Ioo c d) →
        (∀ k ∈ Finset.Icc (J + 1) (N + 1), |a k - A (dlgQ q0 h k - h / 2)| ≤ E * h ^ 2) →
        (∀ k ∈ Finset.Icc (J + 1) N, |c' k - 2 * A (dlgQ q0 h k) * u (dlgQ q0 h k)| ≤ E * h ^ 2) →
        (∀ k ∈ Finset.Icc (J + 1) N, jac a c' Y k = 0) →
        DlgAiryAt κ μ Y (dlgsW A u) (dlgsPhase u c) q0 h Ts Φmin gmin Ca m →
        DlgAiryAt κ μ Y (dlgsW A u) (dlgsPhase u c) q0 h Ts Φmin gmin Ca (m + 1) →
        ∀ k ∈ Finset.Icc J (N + 1),
          |Y k - h ^ (1 / 6 : ℝ) * (1 / √π) * dlgsW A u (dlgQ q0 h k) *
              (κ * Real.cos (dlgP (dlgsPhase u c) q0 h k - Ts / h + π / 4) +
                μ * Real.sin (dlgP (dlgsPhase u c) q0 h k - Ts / h + π / 4))| ≤
            C * (2 + (1 / (12 * Φmin) + Ca / gmin)) * ((|κ| + |μ|) * (h ^ (1 / 6 : ℝ) * h)) *
              dlgsW A u (dlgQ q0 h k) := by
  obtain ⟨lo, hi, M, D, hcos⟩ := dlg_smooth_data hU0 hcd hsub hA hu hApos hu1
  have hmid : (c + d) / 2 ∈ Ioo c d := ⟨by linarith, by linarith⟩
  have hhi : 0 ≤ hi := ((D.Ab _ hmid).1.trans' D.lo_pos.le).trans (D.Ab _ hmid).2
  obtain ⟨h0, C, hh0, hh01, hC, H⟩ := dlg_airy_match lo hi M E L D.lo_pos hhi D.M_nonneg hE hL
  refine ⟨h0, C, hh0, hh01, hC, ?_⟩
  intro q0 h a c' Y J N m κ μ Ts Φmin gmin Ca hΦ hg hCa hh hhh0 hJm hmN hlen hU hA' hC' hY S0 S1
  refine H D q0 h a c' Y J N m κ μ Ts Φmin gmin Ca hΦ hg hCa hh hhh0 hJm hmN hlen hU hA' (fun k hk => ?_) hY S0 S1
  have hq : dlgQ q0 h k ∈ Ioo c d := hU k (by rw [Finset.mem_Icc] at hk ⊢; omega)
  rw [hcos _ hq]
  exact hC' k hk

/-- info: 'FormalResearch.Special.dlg_airy_match_smooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dlg_airy_match_smooth

end FormalResearch.Special
