module

public import FormalResearch.Special.DiscreteLgHahn
public import FormalResearch.Special.DiscreteAiryPhysHahn

/-!
# Hahn/Racah chains: the Airy chart radius can be capped

`airy_full_compose` (`DiscreteAiryPhysHahn`) returns an existential chart radius `r ≤ q_*/4`.  The Langer identities used in the matching
(`langerZeta_integral`, `langerAmp_of_coeff`, the sign of `ζ`) hold only on a neighbourhood `|q - q_*| < ρ` of the turn, so `r` has to be shrunk below the radius
`ρ` of that neighbourhood.  `dlgh_airy_compose` is `airy_full_compose` with the extra output `r ≤ ρ` for an arbitrary `ρ > 0` (same proof, `discrete_airy_full` with `r₀ = min(r₀, ρ)`).

**Claim class: proved.**
-/

@[expose] public section

open Finset FormalResearch.Racah.P3 FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- `airy_full_compose` with the chart radius capped by an arbitrary `ρ > 0`. -/
theorem dlgh_airy_compose {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs : ℝ) (hqs : 0 < qs) (hτ : τ ^ 2 = 1)
    (hκ : 0 < 1 - τ * x) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2)
    (hturn : Phi P Q τ x (qs ^ 2) = 0) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (r δ0 C Cmu ξ0 : ℝ), 0 < r ∧ r ≤ ρ ∧ r ≤ qs / 4 ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧
      ∀ (h : ℝ) (Y : ℤ → ℝ) (Ymax : ℝ), 0 < h → h ≤ δ0 ^ 3 →
        (∀ k : ℤ, 1 ≤ k → jac (hrAk P Q a b h) (hrCk P Q τ x a b h) Y k = 0) → (∀ k, |Y k| ≤ Ymax) →
        AiryFullAt P Q τ x qs a b Y Ymax r δ0 C Cmu ξ0 h := by
  obtain ⟨r0, hr0, hr0q, hdom⟩ := hr_dom hqs hα hβ
  have hint : 0 < (1 - P * qs ^ 2) * (1 - Q * qs ^ 2) := mul_pos hα hβ
  obtain ⟨r, δ0', C, Cmu, ξ0, hr, hrr0, hδ0', hδ01, hC, hCmu, hξ0, H⟩ :=
    discrete_airy_full (hrU_contDiffAt τ x 3 hint) (hrU_turn hint hturn)
      (hrU_deriv_pos hqs hκ hα hβ hturn) (hrA_contDiffAt 2 hint) (hrA_pos hint) (lt_min hr0 hρ) (hrE P Q a b qs)
      (hrE_nonneg P Q a b qs)
  have hM0 : 0 < hrM a b := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hδip : 0 < min 1 (min (3 * qs / (4 * hrM a b)) (qs / 2)) :=
    lt_min one_pos (lt_min (by positivity) (by positivity))
  have hrr1 : r ≤ r0 := hrr0.trans (min_le_left _ _)
  have hrρ : r ≤ ρ := hrr0.trans (min_le_right _ _)
  refine ⟨r, min δ0' (min 1 (min (3 * qs / (4 * hrM a b)) (qs / 2))), C, Cmu, ξ0, hr, hrρ,
    hrr1.trans hr0q, lt_min hδ0' hδip, hC, hCmu, hξ0, ?_⟩
  intro h Y Ymax hh hhδ hrows hbd
  obtain ⟨δ, hδ, hδ3⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = h := by
    refine ⟨h ^ ((1 : ℝ) / 3), Real.rpow_pos_of_pos hh _, ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]
    norm_num
  have hδle : δ ≤ min δ0' (min 1 (min (3 * qs / (4 * hrM a b)) (qs / 2))) := by
    by_contra hcon
    push Not at hcon
    have : (min δ0' (min 1 (min (3 * qs / (4 * hrM a b)) (qs / 2)))) ^ 3 < δ ^ 3 := by gcongr
    linarith
  have hδ1' : δ ≤ δ0' := hδle.trans (min_le_left _ _)
  have hδi' := hδle.trans (min_le_right _ _)
  have hδ1 : δ ≤ 1 := hδi'.trans (min_le_left _ _)
  have hδM : δ ≤ 3 * qs / (4 * hrM a b) := hδi'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδq : δ ≤ qs / 2 := hδi'.trans ((min_le_right _ _).trans (min_le_right _ _))
  have h3δ : δ ^ 3 ≤ δ := by nlinarith [pow_pos hδ 2]
  obtain ⟨J, m, N, hJN, hJm, hmN, hwin, hqJ, hqJc, hqm1, hqm2, hqN, hqN1, Hc⟩ := H δ (δ ^ 3 / 2) hδ hδ1'
  have hr4 : r ≤ qs / 4 := hrr1.trans hr0q
  obtain ⟨hpa, hpc⟩ := hr_perturb hP hQ a b τ x qs hqs hτ hr4 hrr1 hdom hδ hδ1 hδM hwin
  have e2 : ∀ k : ℤ, dalQ (δ ^ 3 / 2) δ k = ((k : ℝ) + 1 / 2) * δ ^ 3 := fun k => by unfold dalQ; ring
  have Hc' := Hc _ _ hpa hpc
  have hJ1 : 1 ≤ J := hr_J_pos hr4 hδ (h3δ.trans hδq) (by omega) hwin
  have hrows' : ∀ k ∈ Finset.Icc (J + 1) N,
      jac (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3)) Y k = 0 := by
    intro k hk
    have hk1 : 1 ≤ k := by rw [Finset.mem_Icc] at hk; omega
    rw [hδ3]
    exact hrows k hk1
  obtain ⟨κ, μ, hμ, hpt⟩ := Hc'.pointwise Y Ymax hrows' (hbd _) (hbd _)
  have hYm : 0 ≤ Ymax := (abs_nonneg _).trans (hbd 0)
  have hwin' : ∀ k ∈ Finset.Icc J (N + 1), |((k : ℝ) + 1 / 2) * δ ^ 3 - qs| ≤ r := by
    intro k hk
    have h1 := hwin k hk
    rw [e2] at h1
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2]
  refine ⟨δ, hδ, hδle, hδ3, J, m, N, hJ1, hJN, hJm, hmN, hwin', ?_, ?_, ?_, ?_,
    ?_, ?_, Hc', κ, μ, hμ, ?_, hpt⟩
  · rw [← e2]; exact hqJ
  · rw [← e2]; exact hqJc
  · rw [← e2]; exact hqm1
  · rw [← e2]; exact hqm2
  · rw [← e2]; exact hqN
  · have := hqN1; rw [show ((N : ℝ) + 1 + 1 / 2) * δ ^ 3 = dalQ (δ ^ 3 / 2) δ (N + 1) by
      unfold dalQ; push_cast; ring]; exact this
  · refine hμ.trans ?_
    have hxi := Hc'.1
    have : Real.exp (-airyXi (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ N)) ≤ Real.exp (-ξ0 / δ ^ 3) := by
      apply Real.exp_le_exp.2
      rw [neg_div]
      exact neg_le_neg hxi
    have : Cmu * Ymax * Real.exp (-airyXi (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ N)) ≤
        Cmu * Ymax * Real.exp (-ξ0 / δ ^ 3) := mul_le_mul_of_nonneg_left this (by positivity)
    exact div_le_div_of_nonneg_right this hδ.le

/-- info: 'FormalResearch.Special.dlgh_airy_compose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dlgh_airy_compose


lemma dlgh_sqrt_phi (z : ℝ) : √(-langerPhi z) = Real.arccos (1 + z) := by
  by_cases hz : 0 ≤ z
  · rw [langerPhi_of_nonneg hz]
    rw [Real.sqrt_eq_zero_of_nonpos (by nlinarith [sq_nonneg (Real.arcosh (1 + z))]),
      Real.arccos_eq_zero.2 (by linarith)]
  · push Not at hz
    simp only [langerPhi, not_le.2 hz, ite_false]
    rw [neg_neg, Real.sqrt_sq (Real.arccos_nonneg _)]

/-- **Langer chart facts at the Hahn/Racah turn** on a punctured left neighbourhood `(q_* - ρ, q_*)`: with `ζ = langerZeta u q_*`, `g = langerAmp u A q_*`,
`u = hrU`, `A = hrA1`: `ζ < 0`; `(2/3)(-ζ)^{3/2} = ∫_q^{q_*} arccos u` (the Langer phase is the Liouville-Green phase measured from the turn);
`g⁴ = 4|ζ| / |4 A² (1 - u²)|` (the Langer amplitude relation). -/
theorem dlgh_chart {P Q : ℝ} (τ x qs : ℝ) (hqs : 0 < qs) (hκ : 0 < 1 - τ * x) (hα : 0 < 1 - P * qs ^ 2)
    (hβ : 0 < 1 - Q * qs ^ 2) (hturn : Phi P Q τ x (qs ^ 2) = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ q : ℝ, qs - ρ < q → q < qs →
      langerZeta (hrU P Q τ x) qs q < 0 ∧
      2 / 3 * (-langerZeta (hrU P Q τ x) qs q) ^ (3 / 2 : ℝ) = ∫ s in q..qs, Real.arccos (hrU P Q τ x s) ∧
      (langerAmp (hrU P Q τ x) (hrA1 P Q) qs q) ^ 4 =
        4 * |langerZeta (hrU P Q τ x) qs q| / |4 * hrA1 P Q q ^ 2 * (1 - hrU P Q τ x q ^ 2)| := by
  have hint : 0 < (1 - P * qs ^ 2) * (1 - Q * qs ^ 2) := mul_pos hα hβ
  have hu3 : ContDiffAt ℝ ((2 + 1 : ℕ) : WithTop ℕ∞) (hrU P Q τ x) qs := by
    simpa using hrU_contDiffAt (P := P) (Q := Q) τ x 3 hint
  have h1 := hrU_turn hint hturn
  have h2 := hrU_deriv_pos hqs hκ hα hβ hturn
  have hA2 : ContDiffAt ℝ (2 : ℕ) (hrA1 P Q) qs := by simpa using hrA_contDiffAt (P := P) (Q := Q) 2 hint
  have hAp := hrA_pos hint
  have sp := langerZeta_spec (m := 2) (by norm_num) hu3 h1 h2
  have ig := langerZeta_integral (m := 2) (by norm_num) hu3 h1 h2
  have am := (langerAmp_of_coeff (m := 2) (by norm_num) hu3 h1 h2 hA2 hAp).2.2
  have ev := (sp.2.2.1).and (ig.and am)
  obtain ⟨ρ, hρ, hρb⟩ := Metric.eventually_nhds_iff.1 ev
  refine ⟨ρ, hρ, fun q hq1 hq2 => ?_⟩
  have hd : dist q qs < ρ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  obtain ⟨⟨-, -, -, -, hneg⟩, ⟨-, hI⟩, hg⟩ := hρb hd
  refine ⟨hneg.2 hq2, ?_, hg hq2.ne⟩
  rw [hI hq2.le]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  rw [dlgh_sqrt_phi]
  congr 1; ring

/-- info: 'FormalResearch.Special.dlgh_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dlgh_chart

end FormalResearch.Special
