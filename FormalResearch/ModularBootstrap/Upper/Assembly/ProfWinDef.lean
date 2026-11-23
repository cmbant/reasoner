module

public import FormalResearch.ModularBootstrap.Upper.Rigidity.Design
public import FormalResearch.ModularBootstrap.Upper.Ramped.ProfileV
public import FormalResearch.ModularBootstrap.Upper.Window.AiryProdPositive

/-!
# The abstract window of an admissible profile (`profWin`)

Source: `CFT/modular_bootstrap/paper/spectral_rigidity.tex` (`sr:P`, §2: the window `W_𝔇` and the sign law),
`upper_transfer.tex` (`ut:V`, `ut:R`), `CFT/notes/n2_ramped_comb.tex` (`rem:profile`).

`profWin uSite epsU hH hε d` is the abstract `Window` (`Upper.Rigidity.Window`) of an arbitrary profile
`(u_k, ε_k)` (tail hypothesis `AiryProdTailHypothesis 1`, all `ε_k ≠ 0`, `k ≥ 2`) with first site
`u_1 = a_1 - d`: `W = Re profW`, `Window.uF = a_1 - d`.  Its fields are the profile Lemma V
(`profV_hasSum`) and the sign structure of the Airy product (`airyWindowProd_re_pos`).  The design windows
`designWin` of `Assembly.DesignWindow` are the special case `(designSiteU N, designWidthU N η)`.

* `continuous_profWre`, `integrable_profWre`, `profWre_hasSum` (no sign hypothesis), `profWre_nonneg_of_le`
  (needs `ε_k ≠ 0`): the fields of `profWin`.
* `profWin_pi_zero`, `profWin_pi_succ`, `profWin_V_eq`: `Π_1 = -d R_1`, `Π_n = profPi d n`,
  `V = -d R_1 + ∑_{n ≥ 2} Π_n(d)`.
* The sign law `profWin_pi_pos`, `profWin_pi_neg`, `profWin_pi_eq_zero`, `profWin_pi_nonneg_of_le`:
  `Π_n > 0, < 0, = 0` according as `a_n <, >, = u_f` (`W = -(u - u_f) S` with `S > 0`).

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Assembly

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Rigidity
  FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Ramped

section ProfWre

variable (uSite epsU : ℕ → ℝ) (hH : AiryProdTailHypothesis 1 uSite epsU) (d : ℝ)

include hH

lemma continuous_profWre : Continuous fun u : ℝ => (profW uSite epsU d (u : ℂ)).re :=
  Complex.continuous_re.comp
    ((profW_differentiable uSite epsU hH d).continuous.comp Complex.continuous_ofReal)

lemma integrable_profWre : Integrable fun u : ℝ => (profW uSite epsU d (u : ℂ)).re :=
  (profW_integrable uSite epsU hH d).re

/-- The Airy quadrature `∫ W = ∑ W(a_n)/Ai'(a_n)²` for the real part of a profile product. -/
lemma profWre_hasSum :
    HasSum (fun i : ℕ => (profW uSite epsU d (airyNode i : ℂ)).re * airyNodeWeight i)
      (∫ u : ℝ, (profW uSite epsU d (u : ℂ)).re) := by
  obtain ⟨h, -⟩ := profV_hasSum uSite epsU hH d
  have h1 := Complex.reCLM.hasSum h
  have h3 : ∫ x : ℝ, (profW uSite epsU d (x : ℂ)).re =
      (∫ x : ℝ, profW uSite epsU d (x : ℂ)).re := by
    simpa using integral_re (profW_integrable uSite epsU hH d)
  have h2 : Complex.reCLM (∫ x : ℝ, profW uSite epsU d (x : ℂ)) =
      ∫ x : ℝ, (profW uSite epsU d (x : ℂ)).re := by
    simp only [Complex.reCLM_apply]
    exact h3.symm
  rw [h2] at h1
  convert h1 using 2 with i
  have hd : deriv airyAiC (airyZero (i + 1) : ℂ) = (airyAi' (airyZero (i + 1)) : ℂ) :=
    deriv_airyAiC_ofReal _
  have hnode : airyNode i = airyZero (i + 1) := rfl
  simp only [Complex.reCLM_apply, airyNodeWeight, hnode]
  rw [hd, ← Complex.ofReal_pow, Complex.div_ofReal_re]
  ring

/-- `Re W ≥ 0` on `u ≤ u_f = a_1 - d` (all `ε_k ≠ 0`). -/
lemma profWre_nonneg_of_le (hε : ∀ k : ℕ, 1 < k → epsU k ≠ 0) {u : ℝ} (hu : u ≤ airyZero 1 - d) :
    0 ≤ (profW uSite epsU d (u : ℂ)).re := by
  rcases hu.lt_or_eq with h | h
  · exact (airyWindowProd_re_pos (f := 1) (airyZero 1 - d) hH hε h).le
  · rw [h]
    exact ((airyWindowProd_re_eq_zero_iff (f := 1) (airyZero 1 - d) hH hε _).2 rfl).ge

end ProfWre

/-! ### The window of an admissible profile -/

/-- **The abstract window of an admissible profile** `(u_k, ε_k)` with first site `u_1 = a_1 - d`:
`W = Re profW`. -/
noncomputable def profWin (uSite epsU : ℕ → ℝ) (hH : AiryProdTailHypothesis 1 uSite epsU)
    (hε : ∀ k : ℕ, 1 < k → epsU k ≠ 0) (d : ℝ) : Window where
  W := fun u => (profW uSite epsU d (u : ℂ)).re
  uF := airyZero 1 - d
  continuous := continuous_profWre uSite epsU hH d
  integrable := integrable_profWre uSite epsU hH d
  nonneg_left := fun _ hu => profWre_nonneg_of_le uSite epsU hH d hε hu
  hasSum := profWre_hasSum uSite epsU hH d

section ProfWin

variable (uSite epsU : ℕ → ℝ) (hH : AiryProdTailHypothesis 1 uSite epsU)
  (hε : ∀ k : ℕ, 1 < k → epsU k ≠ 0) (d : ℝ)

lemma profWin_W (u : ℝ) : (profWin uSite epsU hH hε d).W u = (profW uSite epsU d (u : ℂ)).re := rfl

lemma profWin_uF : (profWin uSite epsU hH hε d).uF = airyZero 1 - d := rfl

lemma profWin_pi_eq (i : ℕ) :
    (profWin uSite epsU hH hε d).pi i =
      (profW uSite epsU d (airyZero (i + 1) : ℂ) /
        (deriv airyAiC (airyZero (i + 1) : ℂ)) ^ 2).re := by
  have hd : deriv airyAiC (airyZero (i + 1) : ℂ) = (airyAi' (airyZero (i + 1)) : ℂ) :=
    deriv_airyAiC_ofReal _
  have hnode : airyNode i = airyZero (i + 1) := rfl
  unfold Window.pi
  simp only [profWin_W, airyNodeWeight, hnode]
  rw [hd, ← Complex.ofReal_pow, Complex.div_ofReal_re]
  ring

/-- `Π_1 = W(a_1)/Ai'(a_1)² = -d R_1`. -/
lemma profWin_pi_zero : (profWin uSite epsU hH hε d).pi 0 = -d * profR1 uSite epsU := by
  rw [profWin_pi_eq]
  have := profV_eval_one uSite epsU hH d
  simp only [zero_add] at this ⊢
  rw [this, Complex.ofReal_re]

/-- `Π_{i+2} = profPi d (i + 2)` (`W(a_n)/Ai'(a_n)² = Π_n(d)`). -/
lemma profWin_pi_succ (i : ℕ) :
    (profWin uSite epsU hH hε d).pi (i + 1) = profPi uSite epsU d (i + 2) := by
  rw [profWin_pi_eq]
  have := profV_eval_succ uSite epsU hH d (n := i + 2) (by omega)
  simp only [show i + 1 + 1 = i + 2 from rfl] at this ⊢
  rw [this, Complex.ofReal_re]

/-- `V = ∫ W = -d R_1 + ∑_{n ≥ 2} Π_n(d)`. -/
lemma profWin_V_eq :
    (profWin uSite epsU hH hε d).V =
      -d * profR1 uSite epsU + ∑' i : ℕ, profPi uSite epsU d (i + 2) := by
  have hs := (profWin uSite epsU hH hε d).summable_pi
  rw [← (profWin uSite epsU hH hε d).tsum_pi, hs.tsum_eq_zero_add, profWin_pi_zero]
  congr 1
  exact tsum_congr fun i => profWin_pi_succ uSite epsU hH hε d i

/-- **Sign law** (`sr:P`, §2): `Π_i > 0` when the zero `a_{i+1}` lies below the first site `u_f`. -/
lemma profWin_pi_pos {i : ℕ} (h : airyNode i < airyZero 1 - d) :
    0 < (profWin uSite epsU hH hε d).pi i :=
  mul_pos (airyWindowProd_re_pos (f := 1) (airyZero 1 - d) hH hε h) (airyNodeWeight_pos i)

/-- `Π_i < 0` when the zero `a_{i+1}` lies above the first site `u_f`. -/
lemma profWin_pi_neg {i : ℕ} (h : airyZero 1 - d < airyNode i) :
    (profWin uSite epsU hH hε d).pi i < 0 :=
  mul_neg_of_neg_of_pos (airyWindowProd_re_neg (f := 1) (airyZero 1 - d) hH hε h)
    (airyNodeWeight_pos i)

/-- `Π_i = 0` at the first site. -/
lemma profWin_pi_eq_zero {i : ℕ} (h : airyNode i = airyZero 1 - d) :
    (profWin uSite epsU hH hε d).pi i = 0 := by
  have := (airyWindowProd_re_eq_zero_iff (f := 1) (airyZero 1 - d) hH hε (airyNode i)).2 h
  unfold Window.pi
  rw [profWin_W]
  change (airyWindowProd 1 (airyZero 1 - d) uSite epsU (airyNode i : ℂ)).re * _ = 0
  rw [this, zero_mul]

lemma profWin_pi_nonneg_of_le {i : ℕ} (h : airyNode i ≤ airyZero 1 - d) :
    0 ≤ (profWin uSite epsU hH hε d).pi i :=
  (profWin uSite epsU hH hε d).pi_nonneg_of_le h

end ProfWin

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.profWre_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms profWre_hasSum

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.profWin_V_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms profWin_V_eq

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.profWin_pi_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms profWin_pi_neg

end FormalResearch.ModularBootstrap.Upper.Assembly
