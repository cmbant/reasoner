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
open scoped Real

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
        4 * |langerZeta (hrU P Q τ x) qs q| / |4 * hrA1 P Q q ^ 2 * (1 - hrU P Q τ x q ^ 2)| ∧
      0 < langerAmp (hrU P Q τ x) (hrA1 P Q) qs q := by
  have hint : 0 < (1 - P * qs ^ 2) * (1 - Q * qs ^ 2) := mul_pos hα hβ
  have hu3 : ContDiffAt ℝ ((2 + 1 : ℕ) : WithTop ℕ∞) (hrU P Q τ x) qs := by
    simpa using hrU_contDiffAt (P := P) (Q := Q) τ x 3 hint
  have h1 := hrU_turn hint hturn
  have h2 := hrU_deriv_pos hqs hκ hα hβ hturn
  have hA2 : ContDiffAt ℝ (2 : ℕ) (hrA1 P Q) qs := by simpa using hrA_contDiffAt (P := P) (Q := Q) 2 hint
  have hAp := hrA_pos hint
  have sp := langerZeta_spec (m := 2) (by norm_num) hu3 h1 h2
  have ig := langerZeta_integral (m := 2) (by norm_num) hu3 h1 h2
  have am0 := langerAmp_of_coeff (m := 2) (by norm_num) hu3 h1 h2 hA2 hAp
  have ev := (sp.2.2.1).and (ig.and (am0.2.2.and am0.2.1))
  obtain ⟨ρ, hρ, hρb⟩ := Metric.eventually_nhds_iff.1 ev
  refine ⟨ρ, hρ, fun q hq1 hq2 => ?_⟩
  have hd : dist q qs < ρ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  obtain ⟨⟨-, -, -, -, hneg⟩, ⟨-, hI⟩, hg, hgp⟩ := hρb hd
  refine ⟨hneg.2 hq2, ?_, hg hq2.ne, hgp⟩
  rw [hI hq2.le]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  rw [dlgh_sqrt_phi]
  congr 1; ring

/-- info: 'FormalResearch.Special.dlgh_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dlgh_chart


/-- Real arithmetic of one site: with `Z = -ζ > 0`, `g⁴ = Z W⁴` (`g, W > 0`), `h > 0`, `y = h^{-2/3} Z`:
`g y^{-1/4} = h^{1/6} W` and `(2/3) y^{3/2} = ((2/3) Z^{3/2}) / h`, and `g = Z^{1/4} W`. -/
lemma dlgh_site_arith {g W Z h : ℝ} (hg : 0 < g) (hW : 0 < W) (hZ : 0 < Z) (hh : 0 < h) (h4 : g ^ 4 = Z * W ^ 4) :
    g = Z ^ (1 / 4 : ℝ) * W ∧ 0 < h ^ (-(2 / 3) : ℝ) * Z ∧
      g * (h ^ (-(2 / 3) : ℝ) * Z) ^ (-(1 / 4) : ℝ) = h ^ (1 / 6 : ℝ) * W ∧
      2 / 3 * (h ^ (-(2 / 3) : ℝ) * Z) ^ (3 / 2 : ℝ) = (2 / 3 * Z ^ (3 / 2 : ℝ)) / h := by
  have hZ4 : (Z ^ (1 / 4 : ℝ)) ^ 4 = Z := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hZ.le]; norm_num
  have hZp : 0 < Z ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hZ _
  have hgeq : g = Z ^ (1 / 4 : ℝ) * W := by
    have : g ^ 4 = (Z ^ (1 / 4 : ℝ) * W) ^ 4 := by rw [mul_pow, hZ4]; exact h4
    exact (pow_left_inj₀ hg.le (by positivity) (by norm_num)).1 this
  have hhp : 0 < h ^ (-(2 / 3) : ℝ) := Real.rpow_pos_of_pos hh _
  have e1 : (h ^ (-(2 / 3) : ℝ) * Z) ^ (-(1 / 4) : ℝ) = h ^ (1 / 6 : ℝ) * Z ^ (-(1 / 4) : ℝ) := by
    rw [Real.mul_rpow hhp.le hZ.le, ← Real.rpow_mul hh.le]; norm_num
  have e2 : (h ^ (-(2 / 3) : ℝ) * Z) ^ (3 / 2 : ℝ) = h⁻¹ * Z ^ (3 / 2 : ℝ) := by
    rw [Real.mul_rpow hhp.le hZ.le, ← Real.rpow_mul hh.le, ← Real.rpow_neg_one]; norm_num
  refine ⟨hgeq, mul_pos hhp hZ, ?_, ?_⟩
  · rw [e1, hgeq]
    have : Z ^ (-(1 / 4) : ℝ) = (Z ^ (1 / 4 : ℝ))⁻¹ := Real.rpow_neg hZ.le _
    rw [this]; field_simp
  · rw [e2]; field_simp

lemma dlgh_W4 {A0 u0 : ℝ} (hA : 0 < A0) (hu : |u0| < 1) :
    ((√(A0 * √(1 - u0 ^ 2)))⁻¹) ^ 4 = 1 / (A0 ^ 2 * (1 - u0 ^ 2)) := by
  have hu2 : 0 < 1 - u0 ^ 2 := by
    have : u0 ^ 2 < 1 := by nlinarith [abs_nonneg u0, sq_abs u0]
    linarith
  have hs : 0 < √(1 - u0 ^ 2) := Real.sqrt_pos.2 hu2
  have hp : 0 < A0 * √(1 - u0 ^ 2) := mul_pos hA hs
  have e : ((√(A0 * √(1 - u0 ^ 2)))⁻¹) ^ 4 = ((√(A0 * √(1 - u0 ^ 2))) ^ 2)⁻¹ ^ 2 := by
    rw [← inv_pow, ← pow_mul]
  rw [e, Real.sq_sqrt hp.le, inv_pow, mul_pow, Real.sq_sqrt hu2.le]
  field_simp

lemma dlgh_g4 {A0 u0 Z g : ℝ} (hA : 0 < A0) (hu : |u0| < 1) (hZ : 0 < Z)
    (hg : g ^ 4 = 4 * |-Z| / |4 * A0 ^ 2 * (1 - u0 ^ 2)|) :
    g ^ 4 = Z * ((√(A0 * √(1 - u0 ^ 2)))⁻¹) ^ 4 := by
  have hu2 : 0 < 1 - u0 ^ 2 := by
    have : u0 ^ 2 < 1 := by nlinarith [abs_nonneg u0, sq_abs u0]
    linarith
  rw [hg, dlgh_W4 hA hu, abs_neg, abs_of_pos hZ, abs_of_pos (by positivity)]
  field_simp


/-- **The Airy datum at one lattice site** (`DlgAiryAt`) from the Langer chart facts at that site and the D2A pointwise Airy shape. -/
theorem dlgh_airyat {P Q τ x qs : ℝ} {Y : ℤ → ℝ} {κ μ Ts Φmin lo C δ : ℝ} {k : ℤ} {Θ : ℝ → ℝ}
    (hδ : 0 < δ) (hlo : 0 < lo) (hΦ : 0 < Φmin) (hC : 0 ≤ C)
    (hA : 0 < hrA1 P Q (dalQ (δ ^ 3 / 2) δ k)) (hu : |hrU P Q τ x (dalQ (δ ^ 3 / 2) δ k)| < 1)
    (hneg : langerZeta (hrU P Q τ x) qs (dalQ (δ ^ 3 / 2) δ k) < 0)
    (hphase : 2 / 3 * (-langerZeta (hrU P Q τ x) qs (dalQ (δ ^ 3 / 2) δ k)) ^ (3 / 2 : ℝ) = Ts - Θ (dalQ (δ ^ 3 / 2) δ k))
    (hg4 : (langerAmp (hrU P Q τ x) (hrA1 P Q) qs (dalQ (δ ^ 3 / 2) δ k)) ^ 4 =
      4 * |langerZeta (hrU P Q τ x) qs (dalQ (δ ^ 3 / 2) δ k)| /
        |4 * hrA1 P Q (dalQ (δ ^ 3 / 2) δ k) ^ 2 * (1 - hrU P Q τ x (dalQ (δ ^ 3 / 2) δ k) ^ 2)|)
    (hg0 : 0 < langerAmp (hrU P Q τ x) (hrA1 P Q) qs (dalQ (δ ^ 3 / 2) δ k))
    (hΦle : Φmin ≤ Ts - Θ (dalQ (δ ^ 3 / 2) δ k))
    (hwlo : lo ≤ dlgsW (hrA1 P Q) (hrU P Q τ x) (dalQ (δ ^ 3 / 2) δ k))
    (hAiry : |Y k - (κ * daoPhi (fun k => langerAmp (hrU P Q τ x) (hrA1 P Q) qs (dalQ (δ ^ 3 / 2) δ k))
          (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ) k +
        μ * daoPsi (fun k => langerAmp (hrU P Q τ x) (hrA1 P Q) qs (dalQ (δ ^ 3 / 2) δ k))
          (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ) k)| ≤
      C * δ ^ 3 * (|κ| * airyWt (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ k) +
        |μ| * airyBiWt (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ k))) :
    DlgAiryAt κ μ Y (dlgsW (hrA1 P Q) (hrU P Q τ x)) Θ (δ ^ 3 / 2) (δ ^ 3) Ts Φmin
      ((((3 / 2) * Φmin) ^ (2 / 3 : ℝ)) ^ (1 / 4 : ℝ) * lo) C k := by
  set q : ℝ := dalQ (δ ^ 3 / 2) δ k with hq
  set ζ : ℝ := langerZeta (hrU P Q τ x) qs q with hζ
  set g : ℝ := langerAmp (hrU P Q τ x) (hrA1 P Q) qs q with hgdef
  set W : ℝ := dlgsW (hrA1 P Q) (hrU P Q τ x) q with hWdef
  have hh : 0 < δ ^ 3 := by positivity
  have hZ : 0 < -ζ := neg_pos.2 hneg
  have hW : 0 < W := hlo.trans_le hwlo
  have h4 : g ^ 4 = -ζ * W ^ 4 := by
    have := dlgh_g4 (A0 := hrA1 P Q q) (u0 := hrU P Q τ x q) (Z := -ζ) (g := g) hA hu hZ (by rw [hg4, neg_neg])
    exact this
  obtain ⟨hgeq, hyp, hM2, hM3⟩ := dlgh_site_arith hg0 hW hZ hh h4
  have hDpos : Φmin ≤ 2 / 3 * (-ζ) ^ (3 / 2 : ℝ) := by rw [hphase]; exact hΦle
  have hXk : turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ k = (δ ^ 3) ^ (-(2 / 3) : ℝ) * ζ := rfl
  set y : ℝ := (δ ^ 3) ^ (-(2 / 3) : ℝ) * (-ζ) with hy
  have hXy : turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ k = -y := by
    rw [hXk, hy]; ring
  have hyw : y ^ (-(1 / 4) : ℝ) ≥ 0 := (Real.rpow_pos_of_pos hyp _).le
  have hq' : dlgQ (δ ^ 3 / 2) (δ ^ 3) k = q := rfl
  refine ⟨g, y, hyp, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hq']; exact hM2
  · have : (2 / 3 * (-ζ) ^ (3 / 2 : ℝ)) / δ ^ 3 = Ts / δ ^ 3 - dlgP Θ (δ ^ 3 / 2) (δ ^ 3) k := by
      rw [hphase, sub_div]; rfl
    rw [hM3, this]
  · have : δ ^ 3 * dlgP Θ (δ ^ 3 / 2) (δ ^ 3) k = Θ q := by
      unfold dlgP; rw [mul_div_cancel₀ _ hh.ne']; rfl
    rw [this]; exact hΦle
  · -- g ≥ gmin
    have hZmin : ((3 / 2) * Φmin) ^ (2 / 3 : ℝ) ≤ -ζ := by
      have h1 : (3 / 2) * Φmin ≤ (-ζ) ^ (3 / 2 : ℝ) := by linarith
      have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 2 / 3)
      rwa [← Real.rpow_mul hZ.le, show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num, Real.rpow_one] at h2
    rw [hgeq]
    exact mul_le_mul (Real.rpow_le_rpow (by positivity) hZmin (by norm_num)) hwlo hlo.le (Real.rpow_nonneg hZ.le _)
  · -- Airy shape
    have hAi : airyAi (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ k) = airyAi (-y) := by rw [hXy]
    have hBi : airyBi (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ k) = airyBi (-y) := by rw [hXy]
    have hwt : airyWt (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ k) ≤ y ^ (-(1 / 4) : ℝ) ∧
        airyBiWt (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ k) ≤ y ^ (-(1 / 4) : ℝ) := by
      rw [hXy]
      have hxi : airyXi (-y) = 0 := by
        unfold airyXi
        rw [max_eq_right (by linarith), Real.zero_rpow (by norm_num)]; ring
      have hab : |-y| = y := by rw [abs_neg, abs_of_pos hyp]
      have hrp : (2 + y) ^ (-(1 / 4) : ℝ) ≤ y ^ (-(1 / 4) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hyp (by linarith) (by norm_num)
      unfold airyWt airyBiWt
      rw [hxi, hab]
      simp only [neg_zero, Real.exp_zero, mul_one]
      exact ⟨hrp, hrp⟩
    have hC' : C * δ ^ 3 * (|κ| * airyWt (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ k) +
        |μ| * airyBiWt (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ k)) ≤ C * (δ ^ 3) * ((|κ| + |μ|) * y ^ (-(1 / 4) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left hwt.1 (abs_nonneg κ), mul_le_mul_of_nonneg_left hwt.2 (abs_nonneg μ)]
    have := hAiry
    unfold daoPhi daoPsi at this
    rw [hAi, hBi] at this
    exact this.trans hC'

/-- info: 'FormalResearch.Special.dlgh_airyat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dlgh_airyat


lemma dlgh_fac {P qs q : ℝ} (hP : 0 ≤ P) (hα : 0 < 1 - P * qs ^ 2) (hq : 0 < q) (hqq : q ≤ qs) : 0 < 1 - P * q ^ 2 := by
  have : q ^ 2 ≤ qs ^ 2 := pow_le_pow_left₀ hq.le hqq 2
  nlinarith [mul_le_mul_of_nonneg_left this hP]

lemma dlgh_w_ge_one {P Q q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (h1 : 0 < 1 - P * q ^ 2) (h2 : 0 < 1 - Q * q ^ 2)
    (τ x : ℝ) (hu : |hrU P Q τ x q| < 1) : 1 ≤ dlgsW (hrA1 P Q) (hrU P Q τ x) q := by
  have hu2 : 0 < 1 - hrU P Q τ x q ^ 2 := by
    have : hrU P Q τ x q ^ 2 < 1 := by nlinarith [abs_nonneg (hrU P Q τ x q), sq_abs (hrU P Q τ x q)]
    linarith
  have hs : 0 < √(1 - hrU P Q τ x q ^ 2) := Real.sqrt_pos.2 hu2
  have hs1 : √(1 - hrU P Q τ x q ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]; nlinarith [sq_nonneg (hrU P Q τ x q)]
  have hint : 0 < (1 - P * q ^ 2) * (1 - Q * q ^ 2) := mul_pos h1 h2
  have hA : 0 < hrA1 P Q q := hrA_pos hint
  have hA1 : hrA1 P Q q ≤ 1 := by
    unfold hrA1 Racah.P3.etilde
    have : (1 - P * q ^ 2) * (1 - Q * q ^ 2) ≤ 1 := by
      have a1 : 1 - P * q ^ 2 ≤ 1 := by nlinarith [mul_nonneg hP (sq_nonneg q)]
      have a2 : 1 - Q * q ^ 2 ≤ 1 := by nlinarith [mul_nonneg hQ (sq_nonneg q)]
      calc (1 - P * q ^ 2) * (1 - Q * q ^ 2) ≤ 1 * 1 := mul_le_mul a1 a2 h2.le zero_le_one
        _ = 1 := one_mul 1
    have := Real.sqrt_le_one.2 this
    linarith
  have hp : 0 < hrA1 P Q q * √(1 - hrU P Q τ x q ^ 2) := mul_pos hA hs
  have hp1 : hrA1 P Q q * √(1 - hrU P Q τ x q ^ 2) ≤ 1 := by
    calc _ ≤ 1 * 1 := mul_le_mul hA1 hs1 hs.le zero_le_one
      _ = 1 := one_mul 1
  unfold dlgsW
  rw [one_le_inv₀ (Real.sqrt_pos.2 hp), Real.sqrt_le_one]
  exact hp1

lemma dlgh_cont {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (τ x qs c1 : ℝ) (hc1 : 0 < c1) (hα : 0 < 1 - P * qs ^ 2)
    (hβ : 0 < 1 - Q * qs ^ 2) :
    ContinuousOn (fun s => Real.arccos (hrU P Q τ x s)) (Set.Icc c1 qs) := by
  refine Real.continuous_arccos.comp_continuousOn (fun s hs => ?_)
  have hs0 : 0 < s := hc1.trans_le hs.1
  have := hrU_contDiffAt (P := P) (Q := Q) τ x 1
    (mul_pos (dlgh_fac hP hα hs0 hs.2) (dlgh_fac hQ hβ hs0 hs.2))
  exact this.continuousAt.continuousWithinAt

lemma dlgh_split {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (τ x qs c1 q : ℝ) (hc1 : 0 < c1) (hα : 0 < 1 - P * qs ^ 2)
    (hβ : 0 < 1 - Q * qs ^ 2) (hq1 : c1 ≤ q) (hq2 : q ≤ qs) :
    (∫ s in c1..qs, Real.arccos (hrU P Q τ x s)) - dlgsPhase (hrU P Q τ x) c1 q =
      ∫ s in q..qs, Real.arccos (hrU P Q τ x s) := by
  have hc := dlgh_cont hP hQ τ x qs c1 hc1 hα hβ
  have i1 : IntervalIntegrable (fun s => Real.arccos (hrU P Q τ x s)) MeasureTheory.volume c1 q :=
    (hc.mono (Set.Icc_subset_Icc_right hq2)).intervalIntegrable_of_Icc hq1
  have i2 : IntervalIntegrable (fun s => Real.arccos (hrU P Q τ x s)) MeasureTheory.volume q qs :=
    (hc.mono (Set.Icc_subset_Icc_left hq1)).intervalIntegrable_of_Icc hq2
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
  unfold dlgsPhase dlgsTheta
  ring

lemma dlgh_tail_ge {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (τ x qs c1 q e : ℝ) (hc1 : 0 < c1) (hα : 0 < 1 - P * qs ^ 2)
    (hβ : 0 < 1 - Q * qs ^ 2) (hq1 : c1 ≤ q) (hqe : q ≤ e) (he : e ≤ qs) :
    (∫ s in e..qs, Real.arccos (hrU P Q τ x s)) ≤ ∫ s in q..qs, Real.arccos (hrU P Q τ x s) := by
  have hc := dlgh_cont hP hQ τ x qs c1 hc1 hα hβ
  have i1 : IntervalIntegrable (fun s => Real.arccos (hrU P Q τ x s)) MeasureTheory.volume q e :=
    (hc.mono (Set.Icc_subset_Icc hq1 he)).intervalIntegrable_of_Icc hqe
  have i2 : IntervalIntegrable (fun s => Real.arccos (hrU P Q τ x s)) MeasureTheory.volume e qs :=
    (hc.mono (Set.Icc_subset_Icc (hq1.trans hqe) le_rfl)).intervalIntegrable_of_Icc he
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
  have : 0 ≤ ∫ s in q..e, Real.arccos (hrU P Q τ x s) :=
    intervalIntegral.integral_nonneg hqe (fun s _ => Real.arccos_nonneg _)
  linarith

lemma dlgh_lattice {δ c d : ℝ} (hδ : 0 < δ) (k : ℤ) :
    (c ≤ dlgQ (δ ^ 3 / 2) (δ ^ 3) k ∧ dlgQ (δ ^ 3 / 2) (δ ^ 3) k ≤ d) ↔
      (⌈(c - δ ^ 3 / 2) / δ ^ 3⌉ ≤ k ∧ k ≤ ⌊(d - δ ^ 3 / 2) / δ ^ 3⌋) := by
  have hh : 0 < δ ^ 3 := by positivity
  rw [Int.ceil_le, Int.le_floor, div_le_iff₀ hh, le_div_iff₀ hh]
  unfold dlgQ
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith


lemma dlgh_qJ {qs r δ : ℝ} {J : ℤ} (hδ : 0 < δ) (h1 : qs - r ≤ ((J : ℝ) + 1 / 2) * δ ^ 3)
    (h2 : ((J : ℝ) + 1 / 2) * δ ^ 3 < qs - r + δ ^ 3) (h3 : δ ^ 3 ≤ r / 4) :
    ∀ k : ℤ, J ≤ k → k ≤ J + 1 → qs - r ≤ dalQ (δ ^ 3 / 2) δ k ∧ dalQ (δ ^ 3 / 2) δ k ≤ qs - r / 2 := by
  intro k hk1 hk2
  have e2 : dalQ (δ ^ 3 / 2) δ k = ((k : ℝ) + 1 / 2) * δ ^ 3 := by unfold dalQ; ring
  rw [e2]
  have h3p : 0 < δ ^ 3 := by positivity
  rcases (by omega : k = J ∨ k = J + 1) with rfl | rfl
  · constructor <;> linarith
  · push_cast
    have : (((J : ℝ) + 1) + 1 / 2) * δ ^ 3 = ((J : ℝ) + 1 / 2) * δ ^ 3 + δ ^ 3 := by ring
    rw [this]
    constructor <;> linarith

/-- The Airy datum `DlgAiryAt` at the two sites `J, J + 1` of the Airy window (assembly of `dlgh_chart`, the phase split and `dlgh_airyat`). -/
lemma dlgh_site_all {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (τ x qs : ℝ) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2)
    {c0 c r ρ δ : ℝ} {J N : ℤ} {κ μ : ℝ} {Y : ℤ → ℝ} {CA : ℝ}
    (hch : ∀ q : ℝ, qs - ρ < q → q < qs →
      langerZeta (hrU P Q τ x) qs q < 0 ∧
      2 / 3 * (-langerZeta (hrU P Q τ x) qs q) ^ (3 / 2 : ℝ) = ∫ s in q..qs, Real.arccos (hrU P Q τ x s) ∧
      (langerAmp (hrU P Q τ x) (hrA1 P Q) qs q) ^ 4 =
        4 * |langerZeta (hrU P Q τ x) qs q| / |4 * hrA1 P Q q ^ 2 * (1 - hrU P Q τ x q ^ 2)| ∧
      0 < langerAmp (hrU P Q τ x) (hrA1 P Q) qs q)
    (hosc : ∀ q ∈ Set.Ico c0 qs, |hrU P Q τ x q| < 1) (hrρ1 : r ≤ ρ / 2) (hc0c : c0 < c) (hcr : c < qs - r)
    (hδ : 0 < δ)
    (hqJ : ∀ k : ℤ, J ≤ k → k ≤ J + 1 → qs - r ≤ dalQ (δ ^ 3 / 2) δ k ∧ dalQ (δ ^ 3 / 2) δ k ≤ qs - r / 2)
    (hΦpos : 0 < ∫ s in (qs - r / 2)..qs, Real.arccos (hrU P Q τ x s)) (hCA : 0 < CA)
    (hpt : ∀ k ∈ Finset.Icc J (N + 1),
      |Y k - (κ * daoPhi (fun k => langerAmp (hrU P Q τ x) (hrA1 P Q) qs (dalQ (δ ^ 3 / 2) δ k))
            (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ) k +
          μ * daoPsi (fun k => langerAmp (hrU P Q τ x) (hrA1 P Q) qs (dalQ (δ ^ 3 / 2) δ k))
            (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ) k)| ≤
        CA * δ ^ 3 * (|κ| * airyWt (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ k) +
          |μ| * airyBiWt (turnX (hrU P Q τ x) qs (δ ^ 3 / 2) δ k))) (hJN : J < N) (hr : 0 < r) (hc0 : 0 < c0) :
    ∀ k : ℤ, J ≤ k → k ≤ J + 1 →
      DlgAiryAt κ μ Y (dlgsW (hrA1 P Q) (hrU P Q τ x)) (dlgsPhase (hrU P Q τ x) ((c0 + c) / 2)) (δ ^ 3 / 2) (δ ^ 3)
        (∫ s in (c0 + c) / 2..qs, Real.arccos (hrU P Q τ x s))
        (∫ s in (qs - r / 2)..qs, Real.arccos (hrU P Q τ x s))
        ((((3 / 2) * (∫ s in (qs - r / 2)..qs, Real.arccos (hrU P Q τ x s))) ^ (2 / 3 : ℝ)) ^ (1 / 4 : ℝ) * 1) CA k := by
  intro k hk1 hk2
  have hc : 0 < c := hc0.trans hc0c
  have hc1pos : 0 < (c0 + c) / 2 := by linarith
  have hfacP : ∀ q : ℝ, 0 < q → q ≤ qs → 0 < 1 - P * q ^ 2 := fun q h1 h2 => dlgh_fac hP hα h1 h2
  have hfacQ : ∀ q : ℝ, 0 < q → q ≤ qs → 0 < 1 - Q * q ^ 2 := fun q h1 h2 => dlgh_fac hQ hβ h1 h2
  obtain ⟨hq1, hq2⟩ := hqJ k hk1 hk2
  have hqc : c < dalQ (δ ^ 3 / 2) δ k := by linarith
  have hq0 : 0 < dalQ (δ ^ 3 / 2) δ k := hc.trans hqc
  have hqs' : dalQ (δ ^ 3 / 2) δ k < qs := by linarith
  have hcq1 : (c0 + c) / 2 ≤ dalQ (δ ^ 3 / 2) δ k := by linarith
  obtain ⟨hneg, hI, hg4, hg0⟩ := hch (dalQ (δ ^ 3 / 2) δ k) (by linarith) hqs'
  have hsplit := dlgh_split hP hQ τ x qs ((c0 + c) / 2) (dalQ (δ ^ 3 / 2) δ k) hc1pos hα hβ hcq1 hqs'.le
  have hΦle := dlgh_tail_ge hP hQ τ x qs ((c0 + c) / 2) (dalQ (δ ^ 3 / 2) δ k) (qs - r / 2) hc1pos hα hβ hcq1 hq2
    (by linarith)
  have hu1 : |hrU P Q τ x (dalQ (δ ^ 3 / 2) δ k)| < 1 := hosc _ ⟨by linarith, hqs'⟩
  exact dlgh_airyat (P := P) (Q := Q) (τ := τ) (x := x) (qs := qs) (Y := Y) (κ := κ) (μ := μ) hδ one_pos hΦpos hCA.le
    (hrA_pos (mul_pos (hfacP _ hq0 hqs'.le) (hfacQ _ hq0 hqs'.le))) hu1 hneg (hI.trans hsplit.symm) hg4 hg0
    (by rw [hsplit]; exact hΦle)
    (dlgh_w_ge_one hP hQ (hfacP _ hq0 hqs'.le) (hfacQ _ hq0 hqs'.le) τ x hu1)
    (hpt k (by rw [Finset.mem_Icc]; omega))

/-- **End-to-end bulk/Airy matching for the Hahn / centred Racah chains.**  Inputs: the simple-turn hypotheses of `airy_full_compose`
(`P, Q ≥ 0`, `τ² = 1`, `Φ(q_*²) = 0`, `1 - τ x > 0`, `P q_*² < 1`, `Q q_*² < 1`, `q_* > 0`) and the oscillatory regularity `|u| < 1` on `[c₀, q_*)`.
There are `r, C_μ, ξ₀ > 0` (the Airy chart radius; `r ≤ q_*/4`) such that for every left end `c ∈ (c₀, q_* - r)` there are `δ₀, C > 0` with the following property.
Every `Y` solving all rows `k ≥ 1` of the closed-form Jacobi chain at scale `h = δ³`, `δ ≤ δ₀`, with `|Y_k| ≤ Y_max`, has Airy coefficients `κ, μ`
(`|μ| ≤ C_μ Y_max e^{-ξ₀/δ³}/δ`) such that at every lattice site `q_k ∈ [c, q_* - r/2]`
`Y_k = h^{1/6} π^{-1/2} w(q_k) (κ cos χ_k + μ sin χ_k) + O(h^{1/6} h (|κ|+|μ|) w(q_k))`, `χ_k = Θ(q_k)/h - Θ*/h + π/4`,
with `Θ = ∫_{c₁}^· arccos u`, `Θ* = ∫_{c₁}^{q_*} arccos u`, `w = (A √(1-u²))^{-1/2}`.  For `μ = 0` (and `μ` is exponentially small): amplitude `h^{1/6}|κ|/√π`, phase
offset exactly `π/4` (the Maslov index of a simple turn), sign of `κ` the sign of the cosine factor. -/
theorem dlg_hahn_airy {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs : ℝ) (hqs : 0 < qs) (hτ : τ ^ 2 = 1)
    (hκ : 0 < 1 - τ * x) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2) (hturn : Phi P Q τ x (qs ^ 2) = 0)
    {c0 : ℝ} (hc0 : 0 < c0) (hc0q : c0 < qs) (hosc : ∀ q ∈ Set.Ico c0 qs, |hrU P Q τ x q| < 1) :
    ∃ (r Cmu ξ0 : ℝ), 0 < r ∧ r ≤ qs / 4 ∧ 0 < Cmu ∧ 0 < ξ0 ∧
      ∀ c : ℝ, c0 < c → c < qs - r → ∃ δ0 C : ℝ, 0 < δ0 ∧ 0 < C ∧
        ∀ (δ : ℝ) (Y : ℤ → ℝ) (Ymax : ℝ), 0 < δ → δ ≤ δ0 →
          (∀ k : ℤ, 1 ≤ k → jac (hrAk P Q a b (δ ^ 3)) (hrCk P Q τ x a b (δ ^ 3)) Y k = 0) → (∀ k, |Y k| ≤ Ymax) →
          ∃ κ μ : ℝ, |μ| ≤ Cmu * Ymax * Real.exp (-ξ0 / δ ^ 3) / δ ∧
            ∀ k : ℤ, c ≤ dlgQ (δ ^ 3 / 2) (δ ^ 3) k → dlgQ (δ ^ 3 / 2) (δ ^ 3) k ≤ qs - r / 2 →
              |Y k - (δ ^ 3) ^ (1 / 6 : ℝ) * (1 / √π) * dlgsW (hrA1 P Q) (hrU P Q τ x) (dlgQ (δ ^ 3 / 2) (δ ^ 3) k) *
                  (κ * Real.cos (dlgP (dlgsPhase (hrU P Q τ x) ((c0 + c) / 2)) (δ ^ 3 / 2) (δ ^ 3) k -
                      (∫ s in (c0 + c) / 2..qs, Real.arccos (hrU P Q τ x s)) / δ ^ 3 + π / 4) +
                    μ * Real.sin (dlgP (dlgsPhase (hrU P Q τ x) ((c0 + c) / 2)) (δ ^ 3 / 2) (δ ^ 3) k -
                      (∫ s in (c0 + c) / 2..qs, Real.arccos (hrU P Q τ x s)) / δ ^ 3 + π / 4))| ≤
                C * ((|κ| + |μ|) * ((δ ^ 3) ^ (1 / 6 : ℝ) * δ ^ 3)) *
                  dlgsW (hrA1 P Q) (hrU P Q τ x) (dlgQ (δ ^ 3 / 2) (δ ^ 3) k) := by
  obtain ⟨ρ, hρ, hch⟩ := dlgh_chart (P := P) (Q := Q) τ x qs hqs hκ hα hβ hturn
  obtain ⟨r, δA, CA, Cmu, ξ0, hr, hrρ, hrq4, hδA, hCA, hCmu, hξ0, HA⟩ :=
    dlgh_airy_compose hP hQ a b τ x qs hqs hτ hκ hα hβ hturn (ρ := min (ρ / 2) (qs - c0))
      (lt_min (by positivity) (by linarith))
  have hrρ1 : r ≤ ρ / 2 := hrρ.trans (min_le_left _ _)
  have hrρ2 : r ≤ qs - c0 := hrρ.trans (min_le_right _ _)
  refine ⟨r, Cmu, ξ0, hr, hrq4, hCmu, hξ0, ?_⟩
  intro c hc0c hcr
  have hc : 0 < c := hc0.trans hc0c
  have hc1pos : 0 < (c0 + c) / 2 := by linarith
  have hcd : c < qs - r / 2 := by linarith
  have hdd0 : qs - r / 2 < qs - r / 4 := by linarith
  have hfacP : ∀ q : ℝ, 0 < q → q ≤ qs → 0 < 1 - P * q ^ 2 := fun q h1 h2 => dlgh_fac hP hα h1 h2
  have hfacQ : ∀ q : ℝ, 0 < q → q ≤ qs → 0 < 1 - Q * q ^ 2 := fun q h1 h2 => dlgh_fac hQ hβ h1 h2
  have hreg : ∀ q ∈ Set.Icc c0 (qs - r / 4), 0 < 1 - P * q ^ 2 ∧ 0 < 1 - Q * q ^ 2 ∧ |hrU P Q τ x q| < 1 :=
    fun q hq => ⟨hfacP q (by linarith [hq.1]) (by linarith [hq.2]), hfacQ q (by linarith [hq.1]) (by linarith [hq.2]),
      hosc q ⟨hq.1, by linarith [hq.2]⟩⟩
  obtain ⟨δ1, Cb, hδ1, hCb, HM⟩ := dlg_airy_match_hahn hP hQ a b τ x hτ hc0 hc0c hcd hdd0 hreg
  have hch_d := hch (qs - r / 2) (by linarith) (by linarith)
  have hΦpos : 0 < ∫ s in (qs - r / 2)..qs, Real.arccos (hrU P Q τ x s) := by
    rw [← hch_d.2.1]; exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (neg_pos.2 hch_d.1) _)
  set Φ : ℝ := ∫ s in (qs - r / 2)..qs, Real.arccos (hrU P Q τ x s) with hΦ
  have hgmin : 0 < (((3 / 2) * Φ) ^ (2 / 3 : ℝ)) ^ (1 / 4 : ℝ) * 1 :=
    mul_pos (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by positivity) _) _) one_pos
  set gmin : ℝ := (((3 / 2) * Φ) ^ (2 / 3 : ℝ)) ^ (1 / 4 : ℝ) * 1 with hgmin_def
  have hKc : 0 ≤ 1 / (12 * Φ) + CA / gmin := by positivity
  refine ⟨min (min δA δ1) (min 1 (r / 4)), Cb * (2 + (1 / (12 * Φ) + CA / gmin)),
    lt_min (lt_min hδA hδ1) (lt_min one_pos (by positivity)), by positivity, ?_⟩
  intro δ Y Ymax hδ hδ0 hrows hbd
  have hδA' : δ ≤ δA := hδ0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδ1' : δ ≤ δ1 := hδ0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδone : δ ≤ 1 := hδ0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδr : δ ≤ r / 4 := hδ0.trans ((min_le_right _ _).trans (min_le_right _ _))
  have h3δ : δ ^ 3 ≤ δ := by
    have h1 : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδone
    calc δ ^ 3 = δ * δ ^ 2 := by ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left h1 hδ.le
      _ = δ := mul_one _
  have hδ3r : δ ^ 3 ≤ r / 4 := h3δ.trans hδr
  have hhA := HA (δ ^ 3) Y Ymax (by positivity) (pow_le_pow_left₀ hδ.le hδA' 3) hrows hbd
  obtain ⟨δ', hδ', hδ'A, hδ'3, J, m, N, hJ1, hJN, hJm, hmN, hwin, h1, h2, h3, h4, h5, h6, Hc, κ, μ, hμ1, hμ2, hpt⟩ := hhA
  have hδeq : δ = δ' := (pow_left_inj₀ hδ.le hδ'.le (by norm_num)).1 hδ'3.symm
  subst hδeq
  have e2 : ∀ k : ℤ, dalQ (δ ^ 3 / 2) δ k = ((k : ℝ) + 1 / 2) * δ ^ 3 := fun k => by unfold dalQ; ring
  have hqJ := dlgh_qJ (qs := qs) (r := r) (δ := δ) (J := J) hδ h1 h2 hδ3r
  have site := dlgh_site_all (P := P) (Q := Q) hP hQ τ x qs hα hβ (c0 := c0) (c := c) (r := r) (ρ := ρ) (δ := δ) (J := J)
    (N := N) (κ := κ) (μ := μ) (Y := Y) (CA := CA) hch hosc hrρ1 hc0c hcr hδ hqJ hΦpos hCA hpt hJN hr hc0
  -- the bulk window of all lattice sites in `[c, qs - r/2]`
  have hlat := dlgh_lattice (c := c) (d := qs - r / 2) hδ
  have hqJ' : ∀ k : ℤ, J ≤ k → k ≤ J + 1 → c ≤ dlgQ (δ ^ 3 / 2) (δ ^ 3) k ∧ dlgQ (δ ^ 3 / 2) (δ ^ 3) k ≤ qs - r / 2 :=
    fun k hk1 hk2 => ⟨by have h := hqJ k hk1 hk2; show c ≤ dalQ (δ ^ 3 / 2) δ k; linarith [h.1], (hqJ k hk1 hk2).2⟩
  have hJw := (hlat J).1 (hqJ' J le_rfl (by omega))
  have hJw1 := (hlat (J + 1)).1 (hqJ' (J + 1) (by omega) le_rfl)
  have hJ0 : 0 ≤ ⌈(c - δ ^ 3 / 2) / δ ^ 3⌉ := by
    by_contra hneg
    push Not at hneg
    have hmem := (hlat ⌈(c - δ ^ 3 / 2) / δ ^ 3⌉).2 ⟨le_rfl, by omega⟩
    have h1' : ((⌈(c - δ ^ 3 / 2) / δ ^ 3⌉ : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (by omega : ⌈(c - δ ^ 3 / 2) / δ ^ 3⌉ ≤ -1)
    have := hmem.1
    unfold dlgQ at this
    have h3p : 0 < δ ^ 3 := by positivity
    nlinarith
  refine ⟨κ, μ, hμ2, fun k hk1 hk2 => ?_⟩
  have hmem := (hlat k).1 ⟨hk1, hk2⟩
  have hres := HM δ Y ⌈(c - δ ^ 3 / 2) / δ ^ 3⌉ (⌊(qs - r / 2 - δ ^ 3 / 2) / δ ^ 3⌋ - 1) J κ μ
    (∫ s in (c0 + c) / 2..qs, Real.arccos (hrU P Q τ x s)) Φ gmin CA hΦpos hgmin hCA.le hδ
    (hδ0.trans ((min_le_left _ _).trans (min_le_right _ _))) hJw.1 (by omega)
    (fun j hj => by
      rw [Finset.mem_Icc] at hj
      exact (hlat j).2 ⟨hj.1, by omega⟩)
    (fun j hj => hrows j (by rw [Finset.mem_Icc] at hj; omega))
    (site J le_rfl (by omega)) (site (J + 1) (by omega) le_rfl)
  have := hres k (by rw [Finset.mem_Icc]; omega)
  exact this

/-- info: 'FormalResearch.Special.dlg_hahn_airy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dlg_hahn_airy

end FormalResearch.Special
