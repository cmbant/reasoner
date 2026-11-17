module

public import FormalResearch.Special.DiscreteAiryPhysTurn
public import FormalResearch.Special.DiscreteAiryLimitHahn

/-!
# `discrete_airy_full` for the closed-form Hahn / centred Racah chains (whole macroscopic window)

Instance of `discrete_airy_full` (`DiscreteAiryPhysTurn`) for the closed-form coefficients of P3 `A:1319-1322`
`A_k = ½ r_k ẽ((kh)²)` (`hrAk`), `c_k = τ(x - B_k)` (`hrCk`), with the same simple-turn hypotheses as
`discrete_airy_hahn_racah` (`Φ(q_*²) = 0`, `1 - τ x > 0`, `τ² = 1`, `P q_*² < 1`, `Q q_*² < 1`, `q_* > 0`, `P, Q ≥ 0`).
The coefficient closeness `|A_k - A(q_k - h/2)|, |c_k - 2A(q_k)u(q_k)| ≤ E h²` is needed on the **whole** macroscopic window
(`|q_k - q_*| ≤ r ≤ q_*/4`); it is `hr_perturb` (`DiscreteAiryLimitHahn`), stated there for exactly such a window.

* `discrete_airy_hahn_racah_full`: for `δ ≤ δ₀` (`h = δ³`, `q_k = (k+½)h`) indices `1 ≤ J < N`, `J ≤ m ≤ N` with
  `q_J ∈ [q_* - r, q_* - r + h)`, `q_m ∈ [q_*, q_* + h)`, `q_N ≥ q_* + r/4`, `q_{N+1} ≤ q_* + r/2` and `DaiFull` for the closed-form chain;
* `AiryFullAt`, `airy_full_compose`: the version for any sequence `Y` solving every row `k ≥ 1` at a scale `h ≤ δ₀³` with `|Y| ≤ Y_max`:
  `Y_k = κ g Ai(X_k) + μ g Bi(X_k)` up to `C δ³ (|κ| airyWt + |μ| airyBiWt)` on all of `[J, N+1]`, `|μ| ≤ Cmu Y_max e^{-ξ₀/δ³}/δ`.

**Claim class: proved.**  `r` is the (existential) radius of the Langer chart of `dal_turn_data` (`r ≤ q_*/4`), not the full
`q_*/4` of the paper: the whole macroscopic window is `[q_* - r, q_* + r/2]` with this `r`; enlarging it to the largest window on
which `A, u` are smooth needs the global Langer chart (not formalised).  `κ ≠ 0` and the value of `κ` are not asserted for the abstract recurrence (for the actual `3j` chain `κ² δ → 2` is `hahn_chain_kappa_sharp`, `DiscreteAiryKappaSharpFinal`).
-/

@[expose] public section

open Finset FormalResearch.Racah.P3 FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **`discrete_airy_full` for the closed-form Hahn / centred Racah chains.**  See the module docstring. -/
theorem discrete_airy_hahn_racah_full {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs : ℝ) (hqs : 0 < qs)
    (hτ : τ ^ 2 = 1) (hκ : 0 < 1 - τ * x) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2)
    (hturn : Phi P Q τ x (qs ^ 2) = 0) :
    ∃ (r δ0 C Cmu ξ0 : ℝ), 0 < r ∧ r ≤ qs / 4 ∧ 0 < δ0 ∧ δ0 ≤ 1 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∃ J m N : ℤ, 1 ≤ J ∧ J < N ∧ J ≤ m ∧ m ≤ N ∧
        (∀ k ∈ Finset.Icc J (N + 1), |((k : ℝ) + 1 / 2) * δ ^ 3 - qs| ≤ r) ∧
        qs - r ≤ ((J : ℝ) + 1 / 2) * δ ^ 3 ∧ ((J : ℝ) + 1 / 2) * δ ^ 3 < qs - r + δ ^ 3 ∧
        qs ≤ ((m : ℝ) + 1 / 2) * δ ^ 3 ∧ ((m : ℝ) + 1 / 2) * δ ^ 3 < qs + δ ^ 3 ∧
        qs + r / 4 ≤ ((N : ℝ) + 1 / 2) * δ ^ 3 ∧ ((N : ℝ) + 1 + 1 / 2) * δ ^ 3 ≤ qs + r / 2 ∧
        DaiFull (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3)) (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ)
          (fun k => langerAmp (hrU P Q τ x) (hrA1 P Q) qs (dalQ (δ ^ 3 / 2) δ k)) J m N δ C Cmu ξ0 := by
  obtain ⟨r0, hr0, hr0q, hdom⟩ := hr_dom hqs hα hβ
  have hint : 0 < (1 - P * qs ^ 2) * (1 - Q * qs ^ 2) := mul_pos hα hβ
  obtain ⟨r, δ0', C, Cmu, ξ0, hr, hrr0, hδ0', hδ01, hC, hCmu, hξ0, H⟩ :=
    discrete_airy_full (hrU_contDiffAt τ x 3 hint) (hrU_turn hint hturn)
      (hrU_deriv_pos hqs hκ hα hβ hturn) (hrA_contDiffAt 2 hint) (hrA_pos hint) hr0 (hrE P Q a b qs)
      (hrE_nonneg P Q a b qs)
  have hM0 : 0 < hrM a b := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hδip : 0 < min 1 (min (3 * qs / (4 * hrM a b)) (qs / 2)) :=
    lt_min one_pos (lt_min (by positivity) (by positivity))
  refine ⟨r, min δ0' (min 1 (min (3 * qs / (4 * hrM a b)) (qs / 2))), C, Cmu, ξ0, hr,
    hrr0.trans hr0q, lt_min hδ0' hδip, (min_le_left _ _).trans hδ01, hC, hCmu, hξ0, ?_⟩
  intro δ hδ hδδ0
  have hδ1' : δ ≤ δ0' := hδδ0.trans (min_le_left _ _)
  have hδi' := hδδ0.trans (min_le_right _ _)
  have hδ1 : δ ≤ 1 := hδi'.trans (min_le_left _ _)
  have hδM : δ ≤ 3 * qs / (4 * hrM a b) := hδi'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδq : δ ≤ qs / 2 := hδi'.trans ((min_le_right _ _).trans (min_le_right _ _))
  have h3δ : δ ^ 3 ≤ δ := by nlinarith [pow_pos hδ 2]
  obtain ⟨J, m, N, hJN, hJm, hmN, hwin, hqJ, hqJc, hqm1, hqm2, hqN, hqN1, Hc⟩ := H δ (δ ^ 3 / 2) hδ hδ1'
  have hr4 : r ≤ qs / 4 := hrr0.trans hr0q
  obtain ⟨hpa, hpc⟩ := hr_perturb hP hQ a b τ x qs hqs hτ hr4 hrr0 hdom hδ hδ1 hδM hwin
  have e2 : ∀ k : ℤ, dalQ (δ ^ 3 / 2) δ k = ((k : ℝ) + 1 / 2) * δ ^ 3 := fun k => by unfold dalQ; ring
  refine ⟨J, m, N, hr_J_pos hr4 hδ (h3δ.trans hδq) (by omega) hwin, hJN, hJm, hmN, fun k hk => ?_,
    by rw [← e2]; exact hqJ, by rw [← e2]; exact hqJc, by rw [← e2]; exact hqm1, by rw [← e2]; exact hqm2,
    by rw [← e2]; exact hqN, by have := hqN1; rw [show ((N : ℝ) + 1 + 1 / 2) * δ ^ 3 = dalQ (δ ^ 3 / 2) δ (N + 1) by
      unfold dalQ; push_cast; ring]; exact this, Hc _ _ hpa hpc⟩
  have h1 := hwin k hk
  rw [e2] at h1
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2]

/-- info: 'FormalResearch.Special.discrete_airy_hahn_racah_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.discrete_airy_hahn_racah_full

/-- The conclusion of `airy_full_compose` for a sequence `Y` at scale `h = δ³`: window positions (`q_J ≈ q_* - r`), the unified
`DaiFull` of the closed-form recurrence, and `Y = κ g Ai + μ g Bi` up to `C δ³ (|κ| airyWt + |μ| airyBiWt)` on all of `[J, N+1]`. -/
def AiryFullAt (P Q τ x qs a b : ℝ) (Y : ℤ → ℝ) (Ymax r δ0 C Cmu ξ0 h : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ^ 3 = h ∧ ∃ J m N : ℤ, 1 ≤ J ∧ J < N ∧ J ≤ m ∧ m ≤ N ∧
    (∀ k ∈ Finset.Icc J (N + 1), |((k : ℝ) + 1 / 2) * δ ^ 3 - qs| ≤ r) ∧
    qs - r ≤ ((J : ℝ) + 1 / 2) * δ ^ 3 ∧ ((J : ℝ) + 1 / 2) * δ ^ 3 < qs - r + δ ^ 3 ∧
    qs ≤ ((m : ℝ) + 1 / 2) * δ ^ 3 ∧ ((m : ℝ) + 1 / 2) * δ ^ 3 < qs + δ ^ 3 ∧
    qs + r / 4 ≤ ((N : ℝ) + 1 / 2) * δ ^ 3 ∧ ((N : ℝ) + 1 + 1 / 2) * δ ^ 3 ≤ qs + r / 2 ∧
    DaiFull (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3)) (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ)
      (fun k => langerAmp (hrU P Q τ x) (hrA1 P Q) qs (dalQ (δ ^ 3 / 2) δ k)) J m N δ C Cmu ξ0 ∧
    ∃ κ μ : ℝ, |μ| ≤ Cmu * Ymax * Real.exp (-airyXi (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ N)) / δ ∧
      |μ| ≤ Cmu * Ymax * Real.exp (-ξ0 / δ ^ 3) / δ ∧
      ∀ k ∈ Finset.Icc J (N + 1),
        |Y k - (κ * daoPhi (fun k => langerAmp (hrU P Q τ x) (hrA1 P Q) qs (dalQ (δ ^ 3 / 2) δ k))
              (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ) k +
            μ * daoPsi (fun k => langerAmp (hrU P Q τ x) (hrA1 P Q) qs (dalQ (δ ^ 3 / 2) δ k))
              (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ) k)| ≤
          C * δ ^ 3 * (|κ| * airyWt (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ k) +
            |μ| * airyBiWt (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ k))

/-- **Composition lemma (unified form).**  Under the simple-turn hypotheses of `discrete_airy_hahn_racah`, the constants are
independent of `Y` and `h`: any `Y` that solves every row `k ≥ 1` of `jac (hrAk P Q a b h) (hrCk P Q τ x a b h) Y = 0` at a scale
`0 < h ≤ δ₀³` and satisfies `|Y_k| ≤ Y_max` satisfies `AiryFullAt` (`δ = h^{1/3}`). -/
theorem airy_full_compose {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs : ℝ) (hqs : 0 < qs) (hτ : τ ^ 2 = 1)
    (hκ : 0 < 1 - τ * x) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2)
    (hturn : Phi P Q τ x (qs ^ 2) = 0) :
    ∃ (r δ0 C Cmu ξ0 : ℝ), 0 < r ∧ r ≤ qs / 4 ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧
      ∀ (h : ℝ) (Y : ℤ → ℝ) (Ymax : ℝ), 0 < h → h ≤ δ0 ^ 3 →
        (∀ k : ℤ, 1 ≤ k → jac (hrAk P Q a b h) (hrCk P Q τ x a b h) Y k = 0) → (∀ k, |Y k| ≤ Ymax) →
        AiryFullAt P Q τ x qs a b Y Ymax r δ0 C Cmu ξ0 h := by
  obtain ⟨r, δ0, C, Cmu, ξ0, hr, hrq, hδ0, -, hC, hCmu, hξ0, H⟩ :=
    discrete_airy_hahn_racah_full hP hQ a b τ x qs hqs hτ hκ hα hβ hturn
  refine ⟨r, δ0, C, Cmu, ξ0, hr, hrq, hδ0, hC, hCmu, hξ0, ?_⟩
  intro h Y Ymax hh hhδ hrows hbd
  obtain ⟨δ, hδ0', hδ3⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = h := by
    refine ⟨h ^ ((1 : ℝ) / 3), Real.rpow_pos_of_pos hh _, ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]
    norm_num
  have hδle : δ ≤ δ0 := by
    by_contra hcon
    push Not at hcon
    have : δ0 ^ 3 < δ ^ 3 := by gcongr
    linarith
  obtain ⟨J, m, N, hJ, hJN, hJm, hmN, hwin, h1, h2, h3, h4, h5, h6, Hc⟩ := H δ hδ0' hδle
  have hrows' : ∀ k ∈ Finset.Icc (J + 1) N,
      jac (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3)) Y k = 0 := by
    intro k hk
    have hk1 : 1 ≤ k := by rw [Finset.mem_Icc] at hk; omega
    rw [hδ3]
    exact hrows k hk1
  obtain ⟨κ, μ, hμ, hpt⟩ := Hc.pointwise Y Ymax hrows' (hbd _) (hbd _)
  have hYm : 0 ≤ Ymax := (abs_nonneg _).trans (hbd 0)
  refine ⟨δ, hδ0', hδle, hδ3, J, m, N, hJ, hJN, hJm, hmN, hwin, h1, h2, h3, h4, h5, h6, Hc, κ, μ, hμ, ?_, hpt⟩
  refine hμ.trans ?_
  have hxi := Hc.1
  have : Real.exp (-airyXi (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ N)) ≤ Real.exp (-ξ0 / δ ^ 3) := by
    apply Real.exp_le_exp.2
    rw [neg_div]
    exact neg_le_neg hxi
  have hδp := hδ0'
  have : Cmu * Ymax * Real.exp (-airyXi (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ N)) ≤
      Cmu * Ymax * Real.exp (-ξ0 / δ ^ 3) := mul_le_mul_of_nonneg_left this (by positivity)
  exact div_le_div_of_nonneg_right this hδp.le

/-- info: 'FormalResearch.Special.airy_full_compose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_full_compose

end FormalResearch.Special
