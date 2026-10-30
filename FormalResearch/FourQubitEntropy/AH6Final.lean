import FormalResearch.FourQubitEntropy.AH6Coef
import FormalResearch.FourQubitEntropy.SevenQubitMaximumStar

/-!
# `lem:seven-joint-scalar-majorant` (AH-6): the headline theorems

Home and proof: `ResearchNotes/QI/seven_qubit_entanglement/joint_entropy_analytic_proof.tex`
(`sec:seven-joint-analytic-proof`), lemma `lem:seven-joint-scalar-majorant` of `seven_qubit_entropy_joint.tex`.

* `joint_scalar_majorant`: for the explicit coefficients `jointCoef x` (the paper's `h_{kl}` in nats) and `x` in the
  bracket of the root of `2³²(1-2x)¹⁵ = 3⁸(1+8x)⁸(1+28x)⁷`, `ScalarMajorant (polyH degFive (jointCoef x)) cap`
  for **every** `cap` (the paper's statement on all of `[0,∞)²`).
* `bracket_of_root`: any real root of that equation lies in the bracket `[XLO/10⁴⁵, (XLO+1)/10⁴⁵]`.
* `joint_majorant_bound_star`: the hypothesis `JointMajorantBound` for the explicit functional at `x_*`, unconditionally.
* `seven_entropy_max_reduction_joint`: the final reduction of `thm:seven-entropy-global-maximum` with `E_* = E₃(x_*)`
  and the explicit `𝒫₅`: the only remaining hypotheses are `SevenPurityBound` and the localized bound `LocalizedBound`
  (E7-1).
-/

namespace FormalResearch.FourQubitEntropy.AH6

open FormalResearch.FourQubitEntropy.SevenQubitConseq
open FormalResearch.FourQubitEntropy.SevenQubitConseq.JointMajorant
open FormalResearch.FourQubitEntropy.SevenQubitConseq.MaximumReduction

/-- **AH-6 for `polyH`.** -/
theorem joint_scalar_majorant {x : ℝ} (hb : InBracket x) (cap : ℝ) :
    ScalarMajorant (polyH degFive (jointCoef x)) cap := by
  intro l m hl _ hm _
  rw [polyH_jointCoef]
  exact joint_majorant hb hl hm

/-- Any real root of the stationarity equation lies in the bracket. -/
theorem bracket_of_root {c : ℝ}
    (heq : 2 ^ 32 * (1 - 2 * c) ^ 15 = 3 ^ 8 * (1 + 8 * c) ^ 8 * (1 + 28 * c) ^ 7) : InBracket c := by
  have hlo : 3 ^ 8 * (1 + 8 * ((XLO : ℝ) / 10 ^ 45)) ^ 8 * (1 + 28 * ((XLO : ℝ) / 10 ^ 45)) ^ 7 <
      2 ^ 32 * (1 - 2 * ((XLO : ℝ) / 10 ^ 45)) ^ 15 := by norm_num [XLO]
  have hhi : 2 ^ 32 * (1 - 2 * (((XLO : ℝ) + 1) / 10 ^ 45)) ^ 15 <
      3 ^ 8 * (1 + 8 * (((XLO : ℝ) + 1) / 10 ^ 45)) ^ 8 * (1 + 28 * (((XLO : ℝ) + 1) / 10 ^ 45)) ^ 7 := by
    norm_num [XLO]
  have hlo0 : (0 : ℝ) < (XLO : ℝ) / 10 ^ 45 := by norm_num [XLO]
  have hhi1 : ((XLO : ℝ) + 1) / 10 ^ 45 < 1 / 2 := by norm_num [XLO]
  have hhi0 : (0 : ℝ) < ((XLO : ℝ) + 1) / 10 ^ 45 := by norm_num [XLO]
  have hlohi : (XLO : ℝ) / 10 ^ 45 ≤ ((XLO : ℝ) + 1) / 10 ^ 45 := by
    apply div_le_div_of_nonneg_right (by linarith) (by positivity)
  constructor
  · by_contra hcon
    push Not at hcon
    set lo : ℝ := (XLO : ℝ) / 10 ^ 45 with hlodef
    -- `c < lo`
    rcases lt_or_ge c (-1 / 28) with hc | hc
    · have h1 : 0 < 2 ^ 32 * (1 - 2 * c) ^ 15 := by
        have : 0 < 1 - 2 * c := by linarith
        positivity
      have h2 : 3 ^ 8 * (1 + 8 * c) ^ 8 * (1 + 28 * c) ^ 7 ≤ 0 := by
        have : (1 + 28 * c) ^ 7 ≤ 0 := Odd.pow_nonpos (by decide) (by linarith)
        have h8 : 0 ≤ 3 ^ 8 * (1 + 8 * c) ^ 8 := by positivity
        exact mul_nonpos_of_nonneg_of_nonpos h8 this
      linarith
    · have hc8 : 0 ≤ 1 + 8 * c := by linarith
      have hc28 : 0 ≤ 1 + 28 * c := by linarith
      have hcl : 1 - 2 * lo ≤ 1 - 2 * c := by linarith
      have hL : 2 ^ 32 * (1 - 2 * lo) ^ 15 ≤ 2 ^ 32 * (1 - 2 * c) ^ 15 := by
        have : (1 - 2 * lo) ^ 15 ≤ (1 - 2 * c) ^ 15 :=
          pow_le_pow_left₀ (by linarith) hcl 15
        linarith
      have hR : 3 ^ 8 * (1 + 8 * c) ^ 8 * (1 + 28 * c) ^ 7 ≤
          3 ^ 8 * (1 + 8 * lo) ^ 8 * (1 + 28 * lo) ^ 7 := by
        have a1 : (1 + 8 * c) ^ 8 ≤ (1 + 8 * lo) ^ 8 := pow_le_pow_left₀ hc8 (by linarith) 8
        have a2 : (1 + 28 * c) ^ 7 ≤ (1 + 28 * lo) ^ 7 := pow_le_pow_left₀ hc28 (by linarith) 7
        have b1 : 0 ≤ (1 + 8 * c) ^ 8 := by positivity
        have b2 : 0 ≤ (1 + 28 * lo) ^ 7 := by
          have : 0 ≤ 1 + 28 * lo := by linarith
          positivity
        calc 3 ^ 8 * (1 + 8 * c) ^ 8 * (1 + 28 * c) ^ 7
            ≤ 3 ^ 8 * (1 + 8 * lo) ^ 8 * (1 + 28 * c) ^ 7 := by gcongr
          _ ≤ 3 ^ 8 * (1 + 8 * lo) ^ 8 * (1 + 28 * lo) ^ 7 := by gcongr
      linarith
  · by_contra hcon
    push Not at hcon
    set hi : ℝ := ((XLO : ℝ) + 1) / 10 ^ 45 with hhidef
    rcases lt_or_ge c (1 / 2) with hc | hc
    · have hc8 : 0 ≤ 1 + 8 * hi := by linarith
      have hc28 : 0 ≤ 1 + 28 * hi := by linarith
      have hL : 2 ^ 32 * (1 - 2 * c) ^ 15 ≤ 2 ^ 32 * (1 - 2 * hi) ^ 15 := by
        have : (1 - 2 * c) ^ 15 ≤ (1 - 2 * hi) ^ 15 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 15
        linarith
      have hR : 3 ^ 8 * (1 + 8 * hi) ^ 8 * (1 + 28 * hi) ^ 7 ≤
          3 ^ 8 * (1 + 8 * c) ^ 8 * (1 + 28 * c) ^ 7 := by
        have a1 : (1 + 8 * hi) ^ 8 ≤ (1 + 8 * c) ^ 8 := pow_le_pow_left₀ hc8 (by linarith) 8
        have a2 : (1 + 28 * hi) ^ 7 ≤ (1 + 28 * c) ^ 7 := pow_le_pow_left₀ hc28 (by linarith) 7
        have b1 : 0 ≤ (1 + 8 * hi) ^ 8 := by positivity
        have b2 : 0 ≤ (1 + 28 * c) ^ 7 := by
          have : 0 ≤ 1 + 28 * c := by linarith
          positivity
        calc 3 ^ 8 * (1 + 8 * hi) ^ 8 * (1 + 28 * hi) ^ 7
            ≤ 3 ^ 8 * (1 + 8 * c) ^ 8 * (1 + 28 * hi) ^ 7 := by gcongr
          _ ≤ 3 ^ 8 * (1 + 8 * c) ^ 8 * (1 + 28 * c) ^ 7 := by gcongr
      linarith
    · have h1 : 2 ^ 32 * (1 - 2 * c) ^ 15 ≤ 0 := by
        have : (1 - 2 * c) ^ 15 ≤ 0 := Odd.pow_nonpos (by decide) (by linarith)
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) this
      have h2 : 0 < 3 ^ 8 * (1 + 8 * c) ^ 8 * (1 + 28 * c) ^ 7 := by
        have : 0 < 1 + 28 * c := by linarith
        have : 0 < 1 + 8 * c := by linarith
        positivity
      linarith


/-- **`thm:seven-entropy-global-maximum`, final reduction with the explicit `𝒫₅` (AH-6 discharged).**
`x_*` is the maximiser of the family entropy `E3` (the root of the stationarity equation); `jointCoef x_*` are the
coefficients `h_{kl}` of the paper's `H`, `ScalarMajorant (polyH degFive (jointCoef x_*)) cap` holds for every `cap`
(`joint_scalar_majorant`), and the entropy bound `E₃(ψ) ≤ E₃(x_*)` for every unit vector follows from
`SevenPurityBound` and the localized bound `LocalizedBound (jointP5 degFive (jointCoef x_*)) (E₃ x_*)` (E7-1) alone. -/
theorem seven_entropy_max_reduction_joint (hPB : SevenPurityBound) :
    ∃ c : ℝ, (∀ y ∈ Set.Icc (0 : ℝ) (1 / 2), y ≠ c → SevenQubitIco.E3 y < SevenQubitIco.E3 c) ∧
      2 ^ 32 * (1 - 2 * c) ^ 15 = 3 ^ 8 * (1 + 8 * c) ^ 8 * (1 + 28 * c) ^ 7 ∧
      (∀ cap : ℝ, ScalarMajorant (polyH degFive (jointCoef c)) cap) ∧
      (LocalizedBound (jointP5 degFive (jointCoef c)) (SevenQubitIco.E3 c) →
        ∀ ψ : SevenQubitIco.BitString → ℂ, UnitVec ψ → meanEntropy3 ψ ≤ SevenQubitIco.E3 c) := by
  obtain ⟨c, hmax, heq, h1, -⟩ := SevenQubitIco.StarValue.star_value
  have hb : InBracket c := bracket_of_root heq
  have hwit : (59307 / 20000 : ℝ) * Real.log 2 < SevenQubitIco.E3 c := by
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h3 : (59307 / 20000 : ℝ) < SevenQubitIco.E3 c / Real.log 2 := lt_trans (by norm_num) h1
    have := (lt_div_iff₀ h2).mp h3
    linarith
  refine ⟨c, hmax, heq, fun cap => joint_scalar_majorant hb cap, ?_⟩
  intro hL ψ hψ
  exact seven_entropy_max_reduction_of_scalarMajorant hPB hwit degFive (jointCoef c)
    (joint_scalar_majorant hb _) hL ψ hψ

end FormalResearch.FourQubitEntropy.AH6
