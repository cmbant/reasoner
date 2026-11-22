module

public import FormalResearch.SignUncertainty.ShellLaplaceBase
public import FormalResearch.Complex.Hurwitz
public import Mathlib.Analysis.Complex.AbsMax

/-!
# Analytic Odd-Level Airy–Laplace Gaps (`ce_shells.tex` Corollary H.14a / `thm:ce-odd-family`)

Source: `CFT/sign_uncertainty/paper/ce_shells.tex` (lines 251–295, commit `9b51a651f`).

For every `ℓ : ℕ` with `1 ≤ ℓ` (odd `m = 2 * ℓ + 1 ≥ 3`) and parameters `b > 0`, `η > 0`:
* `oddShellB ℓ b := (X - C b) * ∏ k ∈ Finset.Icc 2 ℓ, (X - C (airyZero k))`;
* `oddShellQ ℓ b η`, `oddShellP ℓ b η` satisfy `Q_η + i P_η = i B(X + i η)`, giving
  `AiryPQHB`, `natDegree P = ℓ`, `Q ≠ 0`, `natDegree Q = ℓ - 1`, `at47_m P Q = 2 * ℓ + 1`,
  and `oddShellHBData : ShellHBData` via `ShellHBData.ofQNeZero`;
* As `η → 0⁺`, `airyPQN P_η Q_η → B Ai` locally uniformly on `ℂ`, the top `m` zeros `S_η`
  converge with multiplicity to `b, a₁, a_{ℓ+1}` (simple) and `a₂, …, a_ℓ` (double), and
  `airyLaplace (fun u => (D_η.G (u : ℂ)).re) y → airyLaplace (fun u => (b - u) * oddShellH ℓ u) y`
  via maximum modulus on `closedBall 0 (2 * R_B + 1)` and uniform left/right tail envelopes;
* Choosing `y > 0` large so `0 < ∫ u, oddShellH ℓ u * exp (y * u)` and then `b > 0` large yields
  `odd_shell_family_laplace_gap` and `ce_odd_family_laplace_gap` (`∃ y > 0, ℒ_y(-G_N) < 0`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set Polynomial
open scoped Real ENNReal

namespace FormalResearch.SignUncertainty

open FormalResearch.Special
open FormalResearch.ArgPrinciple
open FormalResearch.EntireDiv

/-! ### Section 1: Odd-Shell Polynomials, Degrees, `AiryPQHB`, and `ShellHBData` -/

/-- The real polynomial `B(u) = (u - b) ∏_{k=2}^{ℓ} (u - a_k)`. -/
noncomputable def oddShellB (ℓ : ℕ) (b : ℝ) : ℝ[X] :=
  (Polynomial.X - Polynomial.C b) * ∏ k ∈ Finset.Icc 2 ℓ, (Polynomial.X - Polynomial.C (airyZero k))

lemma oddShellB_monic (ℓ : ℕ) (b : ℝ) : (oddShellB ℓ b).Monic :=
  (Polynomial.monic_X_sub_C b).mul
    (Polynomial.monic_prod_of_monic _ _ fun k _ => Polynomial.monic_X_sub_C (airyZero k))

lemma oddShellB_ne_zero (ℓ : ℕ) (b : ℝ) : oddShellB ℓ b ≠ 0 := (oddShellB_monic ℓ b).ne_zero

lemma oddShellB_natDegree {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (b : ℝ) : (oddShellB ℓ b).natDegree = ℓ := by
  have hprod_monic : (∏ k ∈ Finset.Icc 2 ℓ, (Polynomial.X - Polynomial.C (airyZero k))).Monic :=
    Polynomial.monic_prod_of_monic _ _ fun k _ => Polynomial.monic_X_sub_C (airyZero k)
  have hprod_deg : (∏ k ∈ Finset.Icc 2 ℓ, (Polynomial.X - Polynomial.C (airyZero k))).natDegree = ℓ - 1 := by
    rw [Polynomial.natDegree_prod_of_monic _ _ fun k _ => Polynomial.monic_X_sub_C (airyZero k)]
    simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Icc]; omega
  unfold oddShellB
  have hmul_ne : (Polynomial.X - Polynomial.C b).leadingCoeff *
      (∏ k ∈ Finset.Icc 2 ℓ, (Polynomial.X - Polynomial.C (airyZero k))).leadingCoeff ≠ 0 := by
    rw [(Polynomial.monic_X_sub_C b).leadingCoeff, hprod_monic.leadingCoeff, mul_one]; exact one_ne_zero
  rw [Polynomial.natDegree_mul' hmul_ne, Polynomial.natDegree_X_sub_C, hprod_deg]; omega

lemma oddShellB_map_eval (ℓ : ℕ) (b : ℝ) (z : ℂ) :
    ((oddShellB ℓ b).map (algebraMap ℝ ℂ)).eval z =
      (z - (b : ℂ)) * ∏ k ∈ Finset.Icc 2 ℓ, (z - (airyZero k : ℂ)) := by
  unfold oddShellB
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_prod, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_prod]
  rfl

lemma oddShellB_eval_eq_zero_iff (ℓ : ℕ) (b : ℝ) (z : ℂ) :
    ((oddShellB ℓ b).map (algebraMap ℝ ℂ)).eval z = 0 ↔
      z = (b : ℂ) ∨ ∃ k ∈ Finset.Icc 2 ℓ, z = (airyZero k : ℂ) := by
  rw [oddShellB_map_eval, mul_eq_zero, Finset.prod_eq_zero_iff]; simp [sub_eq_zero]

/-- Complex shifted polynomial `i B(X + i η)`. -/
noncomputable def oddShellF (ℓ : ℕ) (b η : ℝ) : ℂ[X] :=
  Polynomial.C Complex.I *
    ((oddShellB ℓ b).map (algebraMap ℝ ℂ)).comp (Polynomial.X + Polynomial.C (Complex.I * (η : ℂ)))

/-- Real part polynomial `Q_η` in `Q_η + i P_η = i B(X + i η)`. -/
noncomputable def oddShellQ (ℓ : ℕ) (b η : ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range ((oddShellF ℓ b η).natDegree + 1),
    Polynomial.C (((oddShellF ℓ b η).coeff k).re) * Polynomial.X ^ k

/-- Imaginary part polynomial `P_η` in `Q_η + i P_η = i B(X + i η)`. -/
noncomputable def oddShellP (ℓ : ℕ) (b η : ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range ((oddShellF ℓ b η).natDegree + 1),
    Polynomial.C (((oddShellF ℓ b η).coeff k).im) * Polynomial.X ^ k

private lemma oddShellQ_coeff (ℓ : ℕ) (b η : ℝ) (n : ℕ) :
    (oddShellQ ℓ b η).coeff n = ((oddShellF ℓ b η).coeff n).re := by
  unfold oddShellQ
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow, Finset.sum_ite_eq]
  split_ifs with hn
  · rfl
  · rw [Finset.mem_range, not_lt] at hn
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Complex.zero_re]

private lemma oddShellP_coeff (ℓ : ℕ) (b η : ℝ) (n : ℕ) :
    (oddShellP ℓ b η).coeff n = ((oddShellF ℓ b η).coeff n).im := by
  unfold oddShellP
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow, Finset.sum_ite_eq]
  split_ifs with hn
  · rfl
  · rw [Finset.mem_range, not_lt] at hn
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Complex.zero_im]

lemma oddShell_map_add_I_mul_map (ℓ : ℕ) (b η : ℝ) :
    (oddShellQ ℓ b η).map (algebraMap ℝ ℂ) +
        Polynomial.C Complex.I * (oddShellP ℓ b η).map (algebraMap ℝ ℂ) = oddShellF ℓ b η := by
  ext n; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_map]
  change ((oddShellQ ℓ b η).coeff n : ℂ) + Complex.I * ((oddShellP ℓ b η).coeff n : ℂ) = _
  rw [oddShellQ_coeff, oddShellP_coeff, mul_comm Complex.I]; exact Complex.re_add_im _

lemma oddShell_complex_eq (ℓ : ℕ) (b η : ℝ) (z : ℂ) :
    ((oddShellQ ℓ b η).map (algebraMap ℝ ℂ)).eval z +
        Complex.I * ((oddShellP ℓ b η).map (algebraMap ℝ ℂ)).eval z =
      Complex.I * ((oddShellB ℓ b).map (algebraMap ℝ ℂ)).eval (z + Complex.I * (η : ℂ)) := by
  have h := congrArg (Polynomial.eval z) (oddShell_map_add_I_mul_map ℓ b η)
  simpa [oddShellF, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp] using h

lemma oddShell_airyPQc_eq (ℓ : ℕ) (b η : ℝ) (z : ℂ) :
    airyPQc (oddShellQ ℓ b η) z + Complex.I * airyPQc (oddShellP ℓ b η) z =
      Complex.I * airyPQc (oddShellB ℓ b) (z + Complex.I * (η : ℂ)) := oddShell_complex_eq ℓ b η z

/-- Every root of `Q_η + i P_η` has imaginary part `-η < 0`, so `(P_η, Q_η)` is Hermite–Biehler. -/
theorem oddShell_airypqhb (ℓ : ℕ) (b : ℝ) {η : ℝ} (hη : 0 < η) :
    AiryPQHB (oddShellP ℓ b η) (oddShellQ ℓ b η) := by
  intro z hz; rw [oddShell_airyPQc_eq] at hz
  have hB : ((oddShellB ℓ b).map (algebraMap ℝ ℂ)).eval (z + Complex.I * (η : ℂ)) = 0 :=
    (mul_eq_zero.mp hz).resolve_left Complex.I_ne_zero
  rcases (oddShellB_eval_eq_zero_iff ℓ b _).mp hB with heq | ⟨k, _, heq⟩ <;>
    · have him := congrArg Complex.im heq
      simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, one_mul, zero_add] at him
      linarith

private lemma oddShellF_coeff_top {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (b η : ℝ) :
    (oddShellF ℓ b η).coeff ℓ = Complex.I ∧
    (oddShellF ℓ b η).coeff (ℓ - 1) =
      Complex.I * ((oddShellB ℓ b).coeff (ℓ - 1) : ℂ) - ((ℓ : ℂ) * (η : ℂ)) ∧
    ∀ k : ℕ, ℓ < k → (oddShellF ℓ b η).coeff k = 0 := by
  let Bℂ : ℂ[X] := (oddShellB ℓ b).map (algebraMap ℝ ℂ)
  let α : ℂ := Complex.I * (η : ℂ)
  have hBdeg : Bℂ.natDegree = ℓ := by rw [(oddShellB_monic ℓ b).natDegree_map, oddShellB_natDegree hℓ b]
  have hBlc : Bℂ.coeff ℓ = 1 := by rw [← hBdeg]; exact ((oddShellB_monic ℓ b).map _).leadingCoeff
  have hcomp_coeff : ∀ k : ℕ, (oddShellF ℓ b η).coeff k =
      Complex.I * ∑ j ∈ Finset.range (ℓ + 1), Bℂ.coeff j * (α ^ (j - k) * (j.choose k : ℂ)) := fun k => by
    change (Polynomial.C Complex.I * Bℂ.comp (Polynomial.X + Polynomial.C α)).coeff k = _
    rw [Polynomial.coeff_C_mul]
    conv_lhs => rhs; rw [Bℂ.as_sum_range_C_mul_X_pow, hBdeg, Polynomial.sum_comp]
    simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp,
      Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  refine ⟨?_, ?_, ?_⟩
  · rw [hcomp_coeff ℓ, Finset.sum_range_succ, Finset.sum_eq_zero (fun j hj => by
        rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hj), Nat.cast_zero, mul_zero, mul_zero])]
    rw [zero_add, Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one, hBlc, mul_one, mul_one]
  · obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
    rw [show m + 1 - 1 = m by omega, hcomp_coeff m, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_eq_zero (fun j hj => by
        rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hj), Nat.cast_zero, mul_zero, mul_zero])]
    have hBm : Bℂ.coeff m = ((oddShellB (m + 1) b).coeff m : ℂ) := by simp [Bℂ, Polynomial.coeff_map]
    have hch : (m + 1).choose m = m + 1 := Nat.choose_succ_self_right m
    rw [zero_add, hBm, Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one, mul_one,
      hBlc, one_mul, show m + 1 - m = 1 by omega, pow_one, hch]
    dsimp [α]
    calc Complex.I * (((oddShellB (m + 1) b).coeff m : ℂ) + Complex.I * (η : ℂ) * ((m + 1 : ℕ) : ℂ))
        = Complex.I * ((oddShellB (m + 1) b).coeff m : ℂ) +
            (Complex.I * Complex.I) * (((m + 1 : ℕ) : ℂ) * (η : ℂ)) := by ring
      _ = Complex.I * ((oddShellB (m + 1) b).coeff m : ℂ) - (((m + 1 : ℕ) : ℂ) * (η : ℂ)) := by
            rw [Complex.I_mul_I]; ring
  · intro k hk
    rw [hcomp_coeff k, Finset.sum_eq_zero (fun j hj => by
      rw [Nat.choose_eq_zero_of_lt (by have := Finset.mem_range.mp hj; omega),
        Nat.cast_zero, mul_zero, mul_zero]), mul_zero]

theorem oddShellP_natDegree {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (b η : ℝ) : (oddShellP ℓ b η).natDegree = ℓ := by
  obtain ⟨htop, -, hhigh⟩ := oddShellF_coeff_top hℓ b η
  exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => by
      rw [oddShellP_coeff, hhigh N hN, Complex.zero_im])
    (by rw [oddShellP_coeff, htop, Complex.I_im]; exact one_ne_zero)

private lemma oddShellQ_lead_coeff {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (b η : ℝ) :
    (oddShellQ ℓ b η).coeff (ℓ - 1) = -((ℓ : ℝ) * η) := by
  obtain ⟨-, hsub, -⟩ := oddShellF_coeff_top hℓ b η
  rw [oddShellQ_coeff, hsub]; simp [Complex.mul_re]

theorem oddShellQ_ne_zero {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (b : ℝ) {η : ℝ} (hη : 0 < η) :
    oddShellQ ℓ b η ≠ 0 := fun h0 => by
  have hc := oddShellQ_lead_coeff hℓ b η
  rw [h0, Polynomial.coeff_zero] at hc
  have hpos : 0 < (ℓ : ℝ) * η := mul_pos (by exact_mod_cast (by omega : 0 < ℓ)) hη
  linarith

theorem oddShellQ_natDegree {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (b : ℝ) {η : ℝ} (hη : 0 < η) :
    (oddShellQ ℓ b η).natDegree = ℓ - 1 := by
  obtain ⟨htop, -, hhigh⟩ := oddShellF_coeff_top hℓ b η
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => by
      rw [oddShellQ_coeff]
      rcases eq_or_lt_of_le (by omega : ℓ ≤ N) with rfl | hlt
      · rw [htop, Complex.I_re]
      · rw [hhigh N hlt, Complex.zero_re]) ?_
  rw [oddShellQ_lead_coeff hℓ b η]
  exact neg_ne_zero.mpr (mul_pos (by exact_mod_cast (by omega : 0 < ℓ)) hη).ne'

theorem oddShell_at47_m {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (b : ℝ) {η : ℝ} (hη : 0 < η) :
    at47_m (oddShellP ℓ b η) (oddShellQ ℓ b η) = 2 * ℓ + 1 := by
  unfold at47_m; rw [oddShellP_natDegree hℓ b η, oddShellQ_natDegree hℓ b hη]; omega

/-- Canonical `ShellHBData` for the odd-shell family `(oddShellP ℓ b η, oddShellQ ℓ b η)`. -/
noncomputable def oddShellHBData (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (b η : ℝ) (hη : 0 < η) : ShellHBData :=
  ShellHBData.ofQNeZero (oddShell_airypqhb ℓ b hη) (oddShellQ_ne_zero hℓ b hη)

lemma oddShellHBData_Q_ne_zero (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (b η : ℝ) (hη : 0 < η) :
    (oddShellHBData ℓ hℓ b η hη).Q ≠ 0 := oddShellQ_ne_zero hℓ b hη

lemma oddShellHBData_S_card (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (b η : ℝ) (hη : 0 < η) :
    (oddShellHBData ℓ hℓ b η hη).S.card = 2 * ℓ + 1 := by
  rcases (oddShellHBData ℓ hℓ b η hη).m_eq with ⟨hQ0, _⟩ | ⟨_, hcard⟩
  · exact absurd hQ0 (oddShellQ_ne_zero hℓ b hη)
  · exact hcard.trans (oddShell_at47_m hℓ b hη)

/-! ### Section 2: Representation Formulas, Uniform Bounds, and Right-Axis Positivity -/

private lemma oddShell_airyPQc_conj (ℓ : ℕ) (b η : ℝ) (z : ℂ) :
    airyPQc (oddShellQ ℓ b η) z - Complex.I * airyPQc (oddShellP ℓ b η) z =
      -Complex.I * airyPQc (oddShellB ℓ b) (z - Complex.I * (η : ℂ)) := by
  have h := congrArg (starRingEnd ℂ) (oddShell_airyPQc_eq ℓ b η (starRingEnd ℂ z))
  rw [map_add, map_mul, map_mul, Complex.conj_I, conj_airyPQc, conj_airyPQc, conj_airyPQc,
    map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_conj,
    show z + -Complex.I * (η : ℂ) = z - Complex.I * (η : ℂ) by ring] at h
  linear_combination h

lemma oddShellP_airyPQc (ℓ : ℕ) (b η : ℝ) (z : ℂ) :
    airyPQc (oddShellP ℓ b η) z =
      (airyPQc (oddShellB ℓ b) (z + Complex.I * (η : ℂ)) +
        airyPQc (oddShellB ℓ b) (z - Complex.I * (η : ℂ))) / 2 := by
  have h1 := oddShell_airyPQc_eq ℓ b η z; have h2 := oddShell_airyPQc_conj ℓ b η z
  apply mul_left_cancel₀ (by simp [Complex.I_ne_zero] : (2 * Complex.I : ℂ) ≠ 0)
  linear_combination h1 - h2

lemma oddShellQ_airyPQc (ℓ : ℕ) (b η : ℝ) (z : ℂ) :
    airyPQc (oddShellQ ℓ b η) z =
      Complex.I * (airyPQc (oddShellB ℓ b) (z + Complex.I * (η : ℂ)) -
        airyPQc (oddShellB ℓ b) (z - Complex.I * (η : ℂ))) / 2 := by
  have h1 := oddShell_airyPQc_eq ℓ b η z; have h2 := oddShell_airyPQc_conj ℓ b η z
  apply mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0); linear_combination h1 + h2

/-- Local uniform convergence `N_η(z) → B(z) Ai(z)` on `ℂ` as `η → 0⁺`. -/
theorem oddShell_tendstoLocallyUniformly (ℓ : ℕ) (b : ℝ) :
    TendstoLocallyUniformlyOn
      (fun η z => airyPQN (oddShellP ℓ b η) (oddShellQ ℓ b η) z)
      (fun z => airyPQc (oddShellB ℓ b) z * airyAiC z) (𝓝[>] 0) univ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K _ hKc; rw [Metric.tendstoUniformlyOn_iff]; intro ε hε
  obtain ⟨R, hRK⟩ := hKc.isBounded.subset_closedBall (0 : ℂ)
  let R' := max R 0
  have hRK' : K ⊆ closedBall (0 : ℂ) R' := hRK.trans (closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨MA, hMA⟩ := hKc.exists_bound_of_continuousOn differentiable_airyAiC.continuous.continuousOn
  obtain ⟨MA', hMA'⟩ := hKc.exists_bound_of_continuousOn differentiable_airyAiC.deriv.continuous.continuousOn
  let M : ℝ := max (max MA MA') 0 + 1
  have hM_pos : 0 < M := by dsimp [M]; positivity
  have huc := (isCompact_closedBall (0 : ℂ) (R' + 1)).uniformContinuousOn_of_continuous
    (differentiable_airyPQc (oddShellB ℓ b)).continuous.continuousOn
  obtain ⟨δ, hδ, huc_bd⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / (2 * M)) (by positivity)
  filter_upwards [Ioo_mem_nhdsGT (lt_min one_pos hδ)] with η hη z hzK
  have hη0 : 0 < η := hη.1; have hη1 : η < 1 := hη.2.trans_le (min_le_left _ _)
  have hηδ : η < δ := hη.2.trans_le (min_le_right _ _); have hzR : ‖z‖ ≤ R' := mem_closedBall_zero_iff.mp (hRK' hzK)
  have hstep : ∀ σ : ℂ, ‖σ‖ = 1 →
      ‖airyPQc (oddShellB ℓ b) (z + σ * (Complex.I * (η : ℂ))) - airyPQc (oddShellB ℓ b) z‖ < ε / (2 * M) := fun σ hsn => by
    have hση : ‖σ * (Complex.I * (η : ℂ))‖ = η := by
      rw [norm_mul, hsn, one_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη0]
    simpa [dist_eq_norm, add_sub_cancel_left] using huc_bd (z + σ * (Complex.I * (η : ℂ)))
      (mem_closedBall_zero_iff.mpr ((norm_add_le z _).trans (by rw [hση]; linarith)))
      z (mem_closedBall_zero_iff.mpr (by linarith)) (by rw [dist_eq_norm, add_sub_cancel_left, hση]; exact hηδ)
  have hBp : ‖airyPQc (oddShellB ℓ b) (z + Complex.I * (η : ℂ)) - airyPQc (oddShellB ℓ b) z‖ < ε / (2 * M) := by
    simpa using hstep 1 norm_one
  have hBm : ‖airyPQc (oddShellB ℓ b) (z - Complex.I * (η : ℂ)) - airyPQc (oddShellB ℓ b) z‖ < ε / (2 * M) := by
    simpa [sub_eq_add_neg] using hstep (-1) (by simp)
  have hP_bd : ‖airyPQc (oddShellP ℓ b η) z - airyPQc (oddShellB ℓ b) z‖ < ε / (2 * M) := by
    rw [oddShellP_airyPQc, show (airyPQc (oddShellB ℓ b) (z + Complex.I * (η : ℂ)) +
        airyPQc (oddShellB ℓ b) (z - Complex.I * (η : ℂ))) / 2 - airyPQc (oddShellB ℓ b) z =
      ((airyPQc (oddShellB ℓ b) (z + Complex.I * (η : ℂ)) - airyPQc (oddShellB ℓ b) z) +
        (airyPQc (oddShellB ℓ b) (z - Complex.I * (η : ℂ)) - airyPQc (oddShellB ℓ b) z)) / 2 by ring,
      norm_div, Complex.norm_two]
    linarith [norm_add_le (airyPQc (oddShellB ℓ b) (z + Complex.I * (η : ℂ)) - airyPQc (oddShellB ℓ b) z)
      (airyPQc (oddShellB ℓ b) (z - Complex.I * (η : ℂ)) - airyPQc (oddShellB ℓ b) z)]
  have hQ_bd : ‖airyPQc (oddShellQ ℓ b η) z‖ < ε / (2 * M) := by
    rw [oddShellQ_airyPQc, show Complex.I * (airyPQc (oddShellB ℓ b) (z + Complex.I * (η : ℂ)) -
        airyPQc (oddShellB ℓ b) (z - Complex.I * (η : ℂ))) / 2 =
      Complex.I * ((airyPQc (oddShellB ℓ b) (z + Complex.I * (η : ℂ)) - airyPQc (oddShellB ℓ b) z) -
        (airyPQc (oddShellB ℓ b) (z - Complex.I * (η : ℂ)) - airyPQc (oddShellB ℓ b) z)) / 2 by ring,
      norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_two]
    linarith [norm_sub_le (airyPQc (oddShellB ℓ b) (z + Complex.I * (η : ℂ)) - airyPQc (oddShellB ℓ b) z)
      (airyPQc (oddShellB ℓ b) (z - Complex.I * (η : ℂ)) - airyPQc (oddShellB ℓ b) z)]
  have hAiM : ‖airyAiC z‖ ≤ M := (hMA z hzK).trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (by linarith)))
  have hAi'M : ‖deriv airyAiC z‖ ≤ M := (hMA' z hzK).trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (by linarith)))
  rw [dist_eq_norm, show airyPQc (oddShellB ℓ b) z * airyAiC z - airyPQN (oddShellP ℓ b η) (oddShellQ ℓ b η) z =
    (airyPQc (oddShellB ℓ b) z - airyPQc (oddShellP ℓ b η) z) * airyAiC z - airyPQc (oddShellQ ℓ b η) z * deriv airyAiC z by
    unfold airyPQN; ring]
  calc ‖(airyPQc (oddShellB ℓ b) z - airyPQc (oddShellP ℓ b η) z) * airyAiC z -
          airyPQc (oddShellQ ℓ b η) z * deriv airyAiC z‖
      ≤ ‖airyPQc (oddShellP ℓ b η) z - airyPQc (oddShellB ℓ b) z‖ * M + ‖airyPQc (oddShellQ ℓ b η) z‖ * M := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_mul, norm_mul, norm_sub_rev]; gcongr
    _ < (ε / (2 * M)) * M + (ε / (2 * M)) * M := by gcongr
    _ = ε := by field_simp [hM_pos.ne']; ring

private lemma oddShellPQ_norm_le {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (b : ℝ) :
    ∃ C_B : ℝ, 0 ≤ C_B ∧ ∀ η ∈ Ioo (0 : ℝ) 1, ∀ z : ℂ,
      ‖airyPQc (oddShellP ℓ b η) z‖ ≤ C_B * (1 + ‖z‖) ^ ℓ ∧
      ‖airyPQc (oddShellQ ℓ b η) z‖ ≤ C_B * (1 + ‖z‖) ^ ℓ := by
  let B := oddShellB ℓ b; have hdeg : B.natDegree = ℓ := oddShellB_natDegree hℓ b
  let CB₀ : ℝ := ∑ k ∈ Finset.range (ℓ + 1), |B.coeff k|
  have hCB₀ : 0 ≤ CB₀ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨CB₀ * 2 ^ ℓ, by positivity, fun η hη z => ?_⟩
  have hbd : ∀ s : ℂ, ‖s‖ ≤ 1 → ‖airyPQc B (z + s)‖ ≤ CB₀ * 2 ^ ℓ * (1 + ‖z‖) ^ ℓ := fun s hs => by
    have h1 := at47_cpoly_norm_le B (z + s); rw [hdeg] at h1
    have h2 : 1 + ‖z + s‖ ≤ 2 * (1 + ‖z‖) := by have := norm_add_le z s; linarith [norm_nonneg z]
    calc ‖airyPQc B (z + s)‖ ≤ CB₀ * (1 + ‖z + s‖) ^ ℓ := h1
      _ ≤ CB₀ * (2 * (1 + ‖z‖)) ^ ℓ := by gcongr
      _ = CB₀ * 2 ^ ℓ * (1 + ‖z‖) ^ ℓ := by rw [mul_pow]; ring
  have hIη : ‖Complex.I * (η : ℂ)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη.1]; exact hη.2.le
  have hp := hbd (Complex.I * (η : ℂ)) hIη
  have hm : ‖airyPQc B (z - Complex.I * (η : ℂ))‖ ≤ CB₀ * 2 ^ ℓ * (1 + ‖z‖) ^ ℓ := by
    simpa [sub_eq_add_neg] using hbd (-(Complex.I * (η : ℂ))) (by rwa [norm_neg])
  constructor
  · rw [oddShellP_airyPQc, norm_div, Complex.norm_two]
    linarith [norm_add_le (airyPQc B (z + Complex.I * (η : ℂ))) (airyPQc B (z - Complex.I * (η : ℂ)))]
  · rw [oddShellQ_airyPQc, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_two]
    linarith [norm_sub_le (airyPQc B (z + Complex.I * (η : ℂ))) (airyPQc B (z - Complex.I * (η : ℂ)))]

private lemma oddShellN_unif_class {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (b : ℝ) :
    ∃ C_N : ℝ, 0 ≤ C_N ∧ ∀ η ∈ Ioo (0 : ℝ) 1, ∀ z : ℂ,
      ‖airyPQN (oddShellP ℓ b η) (oddShellQ ℓ b η) z‖ ^ 2 ≤
        C_N * (1 + ‖z‖) ^ (2 * (ℓ : ℝ) + 1 / 2) * airyEnv z := by
  obtain ⟨C_B, hCB, hPQ⟩ := oddShellPQ_norm_le hℓ b
  refine ⟨2 * (C_B ^ 2 * 9 + C_B ^ 2 * 25), by positivity, fun η hη z => ?_⟩
  set x : ℝ := 1 + ‖z‖
  have hx1 : 1 ≤ x := by linarith [norm_nonneg z]
  have hx0 : 0 < x := by linarith
  obtain ⟨hpP, hpQ⟩ := hPQ η hη z
  have hA' : ‖airyAiC z‖ ^ 2 ≤ 9 * x ^ (1 / 2 : ℝ) * airyEnv z :=
    (airyAiC_norm_sq_le z).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)) (by norm_num)) (airyEnv_pos z).le)
  have hB := at47_airyAiC_deriv_norm_sq_le z
  have hexp : (x ^ ℓ) ^ 2 * x ^ (1 / 2 : ℝ) = x ^ (2 * (ℓ : ℝ) + 1 / 2) := by
    rw [Real.rpow_add hx0, ← pow_mul, mul_comm ℓ 2,
      show (2 * (ℓ : ℝ)) = ((2 * ℓ : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hN : ‖airyPQN (oddShellP ℓ b η) (oddShellQ ℓ b η) z‖ ≤
      ‖airyPQc (oddShellP ℓ b η) z‖ * ‖airyAiC z‖ + ‖airyPQc (oddShellQ ℓ b η) z‖ * ‖deriv airyAiC z‖ := by
    unfold airyPQN; exact (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
  have h1 : ‖airyPQN (oddShellP ℓ b η) (oddShellQ ℓ b η) z‖ ^ 2 ≤
      2 * (‖airyPQc (oddShellP ℓ b η) z‖ ^ 2 * ‖airyAiC z‖ ^ 2 +
        ‖airyPQc (oddShellQ ℓ b η) z‖ ^ 2 * ‖deriv airyAiC z‖ ^ 2) :=
    (pow_le_pow_left₀ (norm_nonneg _) hN 2).trans (by
      nlinarith [sq_nonneg (‖airyPQc (oddShellP ℓ b η) z‖ * ‖airyAiC z‖ -
        ‖airyPQc (oddShellQ ℓ b η) z‖ * ‖deriv airyAiC z‖)])
  have h2 : ‖airyPQc (oddShellP ℓ b η) z‖ ^ 2 * ‖airyAiC z‖ ^ 2 ≤ C_B ^ 2 * (x ^ ℓ) ^ 2 * (9 * x ^ (1 / 2 : ℝ) * airyEnv z) :=
    mul_le_mul (by rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hpP 2) hA' (sq_nonneg _) (by positivity)
  have h3 : ‖airyPQc (oddShellQ ℓ b η) z‖ ^ 2 * ‖deriv airyAiC z‖ ^ 2 ≤ C_B ^ 2 * (x ^ ℓ) ^ 2 * (25 * x ^ (1 / 2 : ℝ) * airyEnv z) :=
    mul_le_mul (by rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hpQ 2) hB (sq_nonneg _) (by positivity)
  calc ‖airyPQN (oddShellP ℓ b η) (oddShellQ ℓ b η) z‖ ^ 2
      ≤ 2 * (C_B ^ 2 * 9 + C_B ^ 2 * 25) * ((x ^ ℓ) ^ 2 * x ^ (1 / 2 : ℝ)) * airyEnv z := by linarith
    _ = _ := by rw [hexp]

private lemma oddShellN_unif_ball {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (b : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ η ∈ Ioo (0 : ℝ) 1, ∀ z ∈ closedBall (0 : ℂ) R,
      ‖airyPQN (oddShellP ℓ b η) (oddShellQ ℓ b η) z‖ ^ 2 ≤ M := by
  obtain ⟨C_N, hCN, hbd⟩ := oddShellN_unif_class hℓ b
  refine ⟨C_N * (1 + R) ^ (2 * (ℓ : ℝ) + 1 / 2) * Real.exp ((4 / 3 : ℝ) * R ^ (3 / 2 : ℝ)),
    by positivity, fun η hη z hz => ?_⟩
  have hpow : (1 + ‖z‖) ^ (2 * (ℓ : ℝ) + 1 / 2) ≤ (1 + R) ^ (2 * (ℓ : ℝ) + 1 / 2) :=
    Real.rpow_le_rpow (by linarith [norm_nonneg z]) (by linarith [mem_closedBall_zero_iff.mp hz]) (by positivity)
  have henv : airyEnv z ≤ Real.exp ((4 / 3 : ℝ) * R ^ (3 / 2 : ℝ)) := by
    unfold airyEnv; refine Real.exp_le_exp.mpr ?_
    have hre : -(z ^ (3 / 2 : ℂ)).re ≤ R ^ (3 / 2 : ℝ) := ((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans
      ((norm_cpow_three_halves z).symm ▸ Real.rpow_le_rpow (norm_nonneg z) (mem_closedBall_zero_iff.mp hz) (by norm_num))
    linarith
  exact (hbd η hη z).trans (mul_le_mul (mul_le_mul_of_nonneg_left hpow hCN) henv
    (airyEnv_pos z).le (mul_nonneg hCN (Real.rpow_nonneg (by linarith) _)))

private lemma prod_one_add_I_mul_quadrant {ι : Type*} (s : Finset ι) (t : ι → ℝ) {η : ℝ}
    (hη : 0 ≤ η) (hle : (1 + η) ^ s.card - 1 ≤ 1 / 2)
    (ht : ∀ i ∈ s, 0 ≤ t i ∧ t i ≤ η) :
    ‖(∏ i ∈ s, (1 + Complex.I * (t i : ℂ))) - 1‖ ≤ (1 + η) ^ s.card - 1 ∧
    1 / 2 ≤ (∏ i ∈ s, (1 + Complex.I * (t i : ℂ))).re ∧
    0 ≤ (∏ i ∈ s, (1 + Complex.I * (t i : ℂ))).im := by
  classical
  induction s using Finset.induction_on with
  | empty => simp; norm_num
  | @insert a s ha ih =>
    have hle' : (1 + η) ^ s.card - 1 ≤ 1 / 2 := by
      have h1 := pow_le_pow_right₀ (by linarith : 1 ≤ 1 + η) (Nat.le_succ s.card)
      rw [Nat.succ_eq_add_one, ← Finset.card_insert_of_notMem ha] at h1; linarith
    obtain ⟨ih_n, ih_re, ih_im⟩ := ih hle' (fun i hi => ht i (Finset.mem_insert_of_mem hi))
    obtain ⟨hta0, htaη⟩ := ht a (Finset.mem_insert_self _ _)
    let W := ∏ i ∈ s, (1 + Complex.I * (t i : ℂ))
    have hprod : ∏ i ∈ insert a s, (1 + Complex.I * (t i : ℂ)) = W * (1 + Complex.I * (t a : ℂ)) := by
      rw [Finset.prod_insert ha, mul_comm]
    have hta_norm : ‖Complex.I * (t a : ℂ)‖ ≤ η := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hta0]; exact htaη
    have hfa_norm : ‖1 + Complex.I * (t a : ℂ)‖ ≤ 1 + η := (norm_add_le _ _).trans (by rw [norm_one]; linarith)
    have hnn : 0 ≤ (1 + η) ^ s.card - 1 := sub_nonneg.mpr (one_le_pow₀ (by linarith))
    have hnorm : ‖W * (1 + Complex.I * (t a : ℂ)) - 1‖ ≤ (1 + η) ^ (insert a s).card - 1 := by
      rw [show W * (1 + Complex.I * (t a : ℂ)) - 1 = (W - 1) * (1 + Complex.I * (t a : ℂ)) + Complex.I * (t a : ℂ) by ring,
        Finset.card_insert_of_notMem ha]
      calc ‖(W - 1) * (1 + Complex.I * (t a : ℂ)) + Complex.I * (t a : ℂ)‖
          ≤ ‖W - 1‖ * ‖1 + Complex.I * (t a : ℂ)‖ + ‖Complex.I * (t a : ℂ)‖ := (norm_add_le _ _).trans (by rw [norm_mul])
        _ ≤ ((1 + η) ^ s.card - 1) * (1 + η) + η := by gcongr
        _ = (1 + η) ^ (s.card + 1) - 1 := by rw [pow_succ]; ring
    have hre : 1 / 2 ≤ (W * (1 + Complex.I * (t a : ℂ))).re := by
      have h1 : 1 - (W * (1 + Complex.I * (t a : ℂ))).re ≤ ‖W * (1 + Complex.I * (t a : ℂ)) - 1‖ := by
        have := Complex.abs_re_le_norm (1 - W * (1 + Complex.I * (t a : ℂ)))
        rw [norm_sub_rev] at this; simpa [Complex.sub_re, Complex.one_re] using (le_abs_self _).trans this
      linarith
    have him : 0 ≤ (W * (1 + Complex.I * (t a : ℂ))).im := by
      simp only [Complex.mul_im, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im, Complex.one_im]
      nlinarith
    rw [hprod]; exact ⟨hnorm, hre, him⟩

/-- For small `η > 0`, `N_η(u) > 0` for all `u ≥ b + 1`. -/
lemma oddShellN_pos_right {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {b : ℝ} (hb : 0 < b) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η ∈ Ioo 0 η₀, ∀ u : ℝ, b + 1 ≤ u →
      0 < at47_Nf (oddShellP ℓ b η) (oddShellQ ℓ b η) u := by
  have hlim : Tendsto (fun η : ℝ => (1 + η) ^ ℓ - 1) (𝓝 0) (𝓝 0) := by
    simpa using (Continuous.tendsto (by fun_prop : Continuous fun η : ℝ => (1 + η) ^ ℓ - 1) 0)
  obtain ⟨η₀, hη₀, hη_bd⟩ := Metric.tendsto_nhds_nhds.mp hlim (1 / 2 : ℝ) (by norm_num)
  refine ⟨min η₀ 1, lt_min hη₀ one_pos, fun η hη u hu => ?_⟩
  have hη_pos : 0 < η := hη.1
  have hη_le : (1 + η) ^ ℓ - 1 ≤ 1 / 2 := by
    have h1 := hη_bd (mem_ball.mpr (by rw [Real.dist_eq, sub_zero, abs_of_pos hη_pos]; exact hη.2.trans_le (min_le_left _ _)))
    rw [Real.dist_eq, sub_zero] at h1; exact (le_abs_self _).trans h1.le
  let S2 : Finset ℕ := Finset.Icc 2 ℓ
  have hS2_card : S2.card + 1 = ℓ := by simp only [S2, Nat.card_Icc]; omega
  have hle_S2 : (1 + η) ^ S2.card - 1 ≤ 1 / 2 := by
    have := pow_le_pow_right₀ (by linarith : 1 ≤ 1 + η) (by omega : S2.card ≤ ℓ); linarith
  have huk : ∀ k ∈ S2, 1 ≤ u - airyZero k := fun k _ => by linarith [airyZero_neg k]
  let t : ℕ → ℝ := fun k => η / (u - airyZero k); let tb : ℝ := η / (u - b)
  have htb_pos : 0 < tb := div_pos hη_pos (by linarith); have htb_le : tb ≤ η := div_le_self hη_pos.le (by linarith)
  let W₀ : ℂ := ∏ k ∈ S2, (1 + Complex.I * (t k : ℂ))
  obtain ⟨hW₀_n, hW₀_re, hW₀_im⟩ := prod_one_add_I_mul_quadrant S2 t hη_pos.le hle_S2
    (fun k hk => ⟨div_nonneg hη_pos.le (by linarith [huk k hk]), div_le_self hη_pos.le (huk k hk)⟩)
  let W : ℂ := (1 + Complex.I * (tb : ℂ)) * W₀
  have hW_re : 0 < W.re := by
    have hW0_im_bd : W₀.im ≤ (1 + η) ^ S2.card - 1 := by
      have h1 : W₀.im = (W₀ - 1).im := by simp
      linarith [(le_abs_self _).trans ((Complex.abs_im_le_norm (W₀ - 1)).trans hW₀_n)]
    have hre_eq : W.re = W₀.re - tb * W₀.im := by dsimp [W]; simp [Complex.mul_re, Complex.add_re, Complex.add_im]
    have htb_w : tb * W₀.im ≤ 1 / 4 := by
      have hη_half : η ≤ 1 / 2 := by have := pow_le_pow_right₀ (by linarith : 1 ≤ 1 + η) hℓ; linarith
      nlinarith [mul_le_mul htb_le hW0_im_bd (by linarith) (by positivity)]
    linarith
  have hW_im : 0 < W.im := by
    have him : W.im = tb * W₀.re + W₀.im := by dsimp [W]; simp [Complex.mul_im, Complex.add_re, Complex.add_im]; ring
    rw [him]; linarith [mul_pos htb_pos (by linarith : 0 < W₀.re)]
  let Cu : ℝ := (u - b) * ∏ k ∈ S2, (u - airyZero k)
  have hCu_pos : 0 < Cu := mul_pos (by linarith) (Finset.prod_pos fun k hk => by linarith [huk k hk])
  have hB_eq : airyPQc (oddShellB ℓ b) ((u : ℂ) + Complex.I * (η : ℂ)) = (Cu : ℂ) * W := by
    change ((oddShellB ℓ b).map (algebraMap ℝ ℂ)).eval _ = _; rw [oddShellB_map_eval]
    have e1 : ((u : ℂ) + Complex.I * (η : ℂ)) - (b : ℂ) = ((u - b : ℝ) : ℂ) * (1 + Complex.I * (tb : ℂ)) := by
      dsimp [tb]; have hne : (u - b : ℂ) ≠ 0 := by exact_mod_cast (by linarith : u - b ≠ 0)
      push_cast; field_simp [hne]; ring
    have e2 : ∏ k ∈ S2, (((u : ℂ) + Complex.I * (η : ℂ)) - (airyZero k : ℂ)) =
        ((∏ k ∈ S2, (u - airyZero k) : ℝ) : ℂ) * W₀ := by
      dsimp [W₀]; rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k hk => ?_
      have hne : (u - airyZero k : ℂ) ≠ 0 := by exact_mod_cast (by linarith [huk k hk] : u - airyZero k ≠ 0)
      dsimp [t]; push_cast; field_simp [hne]; ring
    rw [e1, e2]; dsimp [Cu, W]; push_cast; ring
  have hPQ_eq := oddShell_airyPQc_eq ℓ b η (u : ℂ)
  rw [hB_eq, airyPQc_ofReal (oddShellQ ℓ b η) u, airyPQc_ofReal (oddShellP ℓ b η) u] at hPQ_eq
  have hQ_neg : (oddShellQ ℓ b η).eval u < 0 := by
    have hQeq : (oddShellQ ℓ b η).eval u = -Cu * W.im := by simpa [Complex.mul_re] using congrArg Complex.re hPQ_eq
    rw [hQeq]; exact mul_neg_of_neg_of_pos (neg_neg_of_pos hCu_pos) hW_im
  have hP_pos : 0 < (oddShellP ℓ b η).eval u := by
    have hPeq : (oddShellP ℓ b η).eval u = Cu * W.re := by simpa [Complex.mul_im] using congrArg Complex.im hPQ_eq
    rw [hPeq]; exact mul_pos hCu_pos hW_re
  unfold at47_Nf
  exact add_pos (mul_pos hP_pos (airyAi_pos (by linarith)))
    (mul_pos_of_neg_of_neg hQ_neg (airyAi'_neg (by linarith)))

/-! ### Section 3: Hurwitz Zero Counting and Convergence of `∏_{t ∈ S_η} (z - t)` -/

noncomputable def oddShellSites (ℓ : ℕ) (b : ℝ) : Finset ℝ :=
  insert b ((Finset.Icc 1 (ℓ + 1)).image airyZero)

noncomputable def oddShellMult (ℓ : ℕ) (b s : ℝ) : ℕ :=
  if s = b ∨ s = airyZero 1 ∨ s = airyZero (ℓ + 1) then 1 else 2

private lemma airyZero_ne_of_pos {b : ℝ} (hb : 0 < b) (k : ℕ) : airyZero k ≠ b :=
  (airyZero_neg k |>.trans hb).ne

private lemma oddShellMult_sum {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {b : ℝ} (hb : 0 < b) :
    ∑ s ∈ oddShellSites ℓ b, oddShellMult ℓ b s = 2 * ℓ + 1 := by
  have hb_not : b ∉ (Finset.Icc 1 (ℓ + 1)).image airyZero := by
    simp only [Finset.mem_image, Finset.mem_Icc]; rintro ⟨k, -, hk⟩; exact airyZero_ne_of_pos hb k hk
  rw [oddShellSites, Finset.sum_insert hb_not, show oddShellMult ℓ b b = 1 by simp [oddShellMult],
    Finset.sum_image (fun x hx y hy hxy => airyZero_injOn
      (Set.mem_Ici.mpr (Finset.mem_Icc.mp hx).1) (Set.mem_Ici.mpr (Finset.mem_Icc.mp hy).1) hxy)]
  have h1_not : 1 ∉ insert (ℓ + 1) (Finset.Icc 2 ℓ) := by simp; omega
  have hlp1_not : ℓ + 1 ∉ Finset.Icc 2 ℓ := by simp
  have hIcc_eq : Finset.Icc 1 (ℓ + 1) = insert 1 (insert (ℓ + 1) (Finset.Icc 2 ℓ)) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hIcc_eq, Finset.sum_insert h1_not, Finset.sum_insert hlp1_not,
    show oddShellMult ℓ b (airyZero 1) = 1 by simp [oddShellMult],
    show oddShellMult ℓ b (airyZero (ℓ + 1)) = 1 by simp [oddShellMult]]
  have hmid : ∑ k ∈ Finset.Icc 2 ℓ, oddShellMult ℓ b (airyZero k) = 2 * (ℓ - 1) := by
    have hpt : ∀ k ∈ Finset.Icc 2 ℓ, oddShellMult ℓ b (airyZero k) = 2 := fun k hk => by
      simp only [Finset.mem_Icc] at hk; unfold oddShellMult; split_ifs with h
      · exfalso; rcases h with h | h | h
        · exact airyZero_ne_of_pos hb k h
        · have := airyZero_injOn (Set.mem_Ici.mpr (by omega)) (Set.mem_Ici.mpr le_rfl) h; omega
        · have := airyZero_injOn (Set.mem_Ici.mpr (by omega)) (Set.mem_Ici.mpr (by omega)) h; omega
      · rfl
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, smul_eq_mul, Nat.card_Icc]; omega
  rw [hmid]; omega

private lemma analyticOrderAt_sub_const (c z : ℂ) :
    analyticOrderAt (fun w : ℂ => w - c) z = if z = c then 1 else 0 := by
  have han : AnalyticAt ℂ (fun w : ℂ => w - c) z := analyticAt_id.sub analyticAt_const
  split_ifs with hz
  · subst hz; exact han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (sub_self z) (by simp)
  · exact han.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hz)

private lemma analyticOrderAt_finsetProd_sub {ι : Type*} (F : Finset ι) (g : ι → ℂ)
    (hinj : Set.InjOn g F) (z : ℂ) :
    analyticOrderAt (fun w : ℂ => ∏ i ∈ F, (w - g i)) z =
      letI := Classical.propDecidable; if ∃ i ∈ F, z = g i then 1 else 0 := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [(analyticAt_const : AnalyticAt ℂ (fun _ => (1 : ℂ)) z).analyticOrderAt_eq_zero]
  | @insert a F ha ih =>
    have hprod : (fun w : ℂ => ∏ i ∈ insert a F, (w - g i)) =
        (fun w => w - g a) * (fun w => ∏ i ∈ F, (w - g i)) := by ext w; exact Finset.prod_insert ha
    have hd2 : Differentiable ℂ (fun w : ℂ => ∏ i ∈ F, (w - g i)) :=
      Differentiable.fun_finsetProd (f := fun i w => w - g i) fun _ _ => differentiable_id.sub_const _
    have hd1 : AnalyticAt ℂ (fun w : ℂ => w - g a) z := analyticAt_id.sub analyticAt_const
    rw [hprod, analyticOrderAt_mul hd1 (hd2.analyticAt z),
      ih (hinj.mono (Finset.subset_insert a F)), analyticOrderAt_sub_const]
    by_cases hza : z = g a
    · have hno : ¬ ∃ i ∈ F, z = g i := fun ⟨i, hi, hzi⟩ =>
        ha (hinj (Finset.mem_insert_self a F) (Finset.mem_insert_of_mem hi) (hza.symm.trans hzi) ▸ hi)
      have hex : ∃ i ∈ insert a F, z = g i := ⟨a, Finset.mem_insert_self a F, hza⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true hza), ite_eq_right_of_eq_false _ _ (eq_false hno),
        ite_eq_left_of_eq_true _ _ (eq_true hex), add_zero]
    · by_cases hzF : ∃ i ∈ F, z = g i
      · have hex : ∃ i ∈ insert a F, z = g i :=
          let ⟨i, hi, hzi⟩ := hzF; ⟨i, Finset.mem_insert_of_mem hi, hzi⟩
        rw [ite_eq_right_of_eq_false _ _ (eq_false hza), ite_eq_left_of_eq_true _ _ (eq_true hzF),
          ite_eq_left_of_eq_true _ _ (eq_true hex), zero_add]
      · have hnex : ¬ ∃ i ∈ insert a F, z = g i := by
          rintro ⟨i, hi, hzi⟩
          rcases Finset.mem_insert.mp hi with rfl | hi'; exact hza hzi; exact hzF ⟨i, hi', hzi⟩
        rw [ite_eq_right_of_eq_false _ _ (eq_false hza), ite_eq_right_of_eq_false _ _ (eq_false hzF),
          ite_eq_right_of_eq_false _ _ (eq_false hnex), add_zero]

private lemma oddShellLimit_orderNatAt {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {b : ℝ} (hb : 0 < b)
    {s : ℝ} (hs : s ∈ oddShellSites ℓ b) :
    analyticOrderNatAt (fun z => airyPQc (oddShellB ℓ b) z * airyAiC z) (s : ℂ) =
      oddShellMult ℓ b s := by
  classical
  have hanB : AnalyticAt ℂ (airyPQc (oddShellB ℓ b)) (s : ℂ) := (differentiable_airyPQc _).analyticAt _
  have hanA : AnalyticAt ℂ airyAiC (s : ℂ) := differentiable_airyAiC.analyticAt _
  have hB_fn : airyPQc (oddShellB ℓ b) =
      (fun z => z - (b : ℂ)) * (fun z => ∏ k ∈ Finset.Icc 2 ℓ, (z - (airyZero k : ℂ))) := by
    ext z; exact oddShellB_map_eval ℓ b z
  have hinj : Set.InjOn (fun k : ℕ => (airyZero k : ℂ)) (Finset.Icc 2 ℓ) := fun x hx y hy hxy =>
    airyZero_injOn (Set.mem_Ici.mpr (by simp at hx; omega)) (Set.mem_Ici.mpr (by simp at hy; omega))
      (Complex.ofReal_injective hxy)
  have hd_prod : Differentiable ℂ (fun z : ℂ => ∏ k ∈ Finset.Icc 2 ℓ, (z - (airyZero k : ℂ))) :=
    Differentiable.fun_finsetProd (f := fun k z => z - (airyZero k : ℂ)) fun _ _ =>
      differentiable_id.sub_const _
  have hB_ordAt : analyticOrderAt (airyPQc (oddShellB ℓ b)) (s : ℂ) =
      if s = b ∨ ∃ k ∈ Finset.Icc 2 ℓ, s = airyZero k then 1 else 0 := by
    have hd_sub : AnalyticAt ℂ (fun z : ℂ => z - (b : ℂ)) (s : ℂ) := analyticAt_id.sub analyticAt_const
    rw [hB_fn, analyticOrderAt_mul hd_sub (hd_prod.analyticAt _),
      analyticOrderAt_sub_const, analyticOrderAt_finsetProd_sub (Finset.Icc 2 ℓ) _ hinj]
    by_cases h1 : s = b
    · have hc : (s : ℂ) = (b : ℂ) := by rw [h1]
      have hno : ¬ ∃ k ∈ Finset.Icc 2 ℓ, (s : ℂ) = (airyZero k : ℂ) := fun ⟨k, _, hk⟩ =>
        airyZero_ne_of_pos hb k (by linarith [Complex.ofReal_injective (hc.symm.trans hk)])
      have hdisj : s = b ∨ ∃ k ∈ Finset.Icc 2 ℓ, s = airyZero k := Or.inl h1
      rw [ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_right_of_eq_false _ _ (eq_false hno),
        ite_eq_left_of_eq_true _ _ (eq_true hdisj), add_zero]
    · have hnc : (s : ℂ) ≠ (b : ℂ) := fun h => h1 (Complex.ofReal_injective h)
      by_cases h2 : ∃ k ∈ Finset.Icc 2 ℓ, s = airyZero k
      · have h2c : ∃ k ∈ Finset.Icc 2 ℓ, (s : ℂ) = (airyZero k : ℂ) :=
          let ⟨k, hk, heq⟩ := h2; ⟨k, hk, by rw [heq]⟩
        have hdisj : s = b ∨ ∃ k ∈ Finset.Icc 2 ℓ, s = airyZero k := Or.inr h2
        rw [ite_eq_right_of_eq_false _ _ (eq_false hnc), ite_eq_left_of_eq_true _ _ (eq_true h2c),
          ite_eq_left_of_eq_true _ _ (eq_true hdisj), zero_add]
      · have hn2c : ¬ ∃ k ∈ Finset.Icc 2 ℓ, (s : ℂ) = (airyZero k : ℂ) := fun ⟨k, hk, heq⟩ =>
          h2 ⟨k, hk, Complex.ofReal_injective heq⟩
        have hndisj : ¬ (s = b ∨ ∃ k ∈ Finset.Icc 2 ℓ, s = airyZero k) := not_or.mpr ⟨h1, h2⟩
        rw [ite_eq_right_of_eq_false _ _ (eq_false hnc), ite_eq_right_of_eq_false _ _ (eq_false hn2c),
          ite_eq_right_of_eq_false _ _ (eq_false hndisj), add_zero]
  simp only [oddShellSites, Finset.mem_insert, Finset.mem_image, Finset.mem_Icc] at hs
  have hA_ordAt : analyticOrderAt airyAiC (s : ℂ) = if s = b then 0 else 1 := by
    split_ifs with hsb
    · subst hsb; exact hanA.analyticOrderAt_eq_zero.mpr (by rw [airyAiC_ofReal]; exact_mod_cast (airyAi_pos hb.le).ne')
    · rcases hs with rfl | ⟨k, -, rfl⟩
      · exact absurd rfl hsb
      · exact hanA.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (airyAiC_airyZero k) (airyZero_deriv_ne_zero k)
  have htot : analyticOrderAt (fun z => airyPQc (oddShellB ℓ b) z * airyAiC z) (s : ℂ) =
      (oddShellMult ℓ b s : ℕ∞) := by
    change analyticOrderAt (airyPQc (oddShellB ℓ b) * airyAiC) (s : ℂ) = _
    rw [analyticOrderAt_mul hanB hanA, hB_ordAt, hA_ordAt]
    rcases hs with rfl | ⟨k, hk, rfl⟩
    · simp [oddShellMult]
    · have hkb := airyZero_ne_of_pos hb k
      rcases (by omega : k = 1 ∨ k = ℓ + 1 ∨ (2 ≤ k ∧ k ≤ ℓ)) with rfl | rfl | hk2
      · have hno : ¬ (airyZero 1 = b ∨ ∃ j ∈ Finset.Icc 2 ℓ, airyZero 1 = airyZero j) := by
          rintro (h | ⟨j, hj, hij⟩); exact hkb h
          simp only [Finset.mem_Icc] at hj
          have := airyZero_injOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (by omega)) hij; omega
        have hM : oddShellMult ℓ b (airyZero 1) = 1 := by simp [oddShellMult]
        rw [ite_eq_right_of_eq_false _ _ (eq_false hno), ite_eq_right_of_eq_false _ _ (eq_false hkb), hM]; norm_num
      · have hno : ¬ (airyZero (ℓ + 1) = b ∨ ∃ j ∈ Finset.Icc 2 ℓ, airyZero (ℓ + 1) = airyZero j) := by
          rintro (h | ⟨j, hj, hij⟩); exact hkb h
          simp only [Finset.mem_Icc] at hj
          have := airyZero_injOn (Set.mem_Ici.mpr (by omega)) (Set.mem_Ici.mpr (by omega)) hij; omega
        have hM : oddShellMult ℓ b (airyZero (ℓ + 1)) = 1 := by simp [oddShellMult]
        rw [ite_eq_right_of_eq_false _ _ (eq_false hno), ite_eq_right_of_eq_false _ _ (eq_false hkb), hM]; norm_num
      · have hyes : airyZero k = b ∨ ∃ j ∈ Finset.Icc 2 ℓ, airyZero k = airyZero j :=
          Or.inr ⟨k, Finset.mem_Icc.mpr hk2, rfl⟩
        have hnot : ¬ (airyZero k = b ∨ airyZero k = airyZero 1 ∨ airyZero k = airyZero (ℓ + 1)) := by
          rintro (h | h | h); exact hkb h
          · have := airyZero_injOn (Set.mem_Ici.mpr (by omega)) (Set.mem_Ici.mpr le_rfl) h; omega
          · have := airyZero_injOn (Set.mem_Ici.mpr (by omega)) (Set.mem_Ici.mpr (by omega)) h; omega
        have hM : oddShellMult ℓ b (airyZero k) = 2 := by
          unfold oddShellMult; exact ite_eq_right_of_eq_false _ _ (eq_false hnot)
        rw [ite_eq_left_of_eq_true _ _ (eq_true hyes), ite_eq_right_of_eq_false _ _ (eq_false hkb), hM]; norm_num
  unfold analyticOrderNatAt; rw [htot]; simp

private lemma real_zeros_card_eq_zeroCount {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ z : ℂ, f z = 0 → z.im = 0)
    (hsimple : ∀ x : ℝ, f (x : ℂ) = 0 → deriv f (x : ℂ) ≠ 0)
    {x₀ r : ℝ} (hr : 0 < r) (hsph : ∀ z ∈ sphere (x₀ : ℂ) r, f z ≠ 0) :
    ∃ T : Finset ℝ, T.card = zeroCount f (x₀ : ℂ) r ∧
      ∀ t : ℝ, t ∈ T ↔ t ∈ Ioo (x₀ - r) (x₀ + r) ∧ f (t : ℂ) = 0 := by
  obtain ⟨hw, hfw⟩ := exists_nonzero_of_sphere (R := r + 1) hr (by linarith) hsph
  have hfin := support_orderNat_finite (R := r + 1) hf.differentiableOn hw hfw (by linarith)
  let Z : Finset ℂ := hfin.toFinset
  have hZ_mem : ∀ z : ℂ, z ∈ Z ↔ z ∈ ball (x₀ : ℂ) r ∧ f z = 0 := fun z => by
    simp only [Z, Set.Finite.mem_toFinset, Set.mem_inter_iff, Function.mem_support]
    exact ⟨fun ⟨hb, ho⟩ => ⟨hb, apply_eq_zero_of_analyticOrderNatAt_ne_zero ho⟩,
      fun ⟨hb, hfz⟩ => ⟨hb, (orderNat_ne_zero_iff hf.differentiableOn hw hfw (ball_subset_ball (by linarith) hb)).mpr hfz⟩⟩
  have hZ_ord : ∀ z ∈ Z, analyticOrderNatAt f z = 1 := fun z hz => by
    have hfz := ((hZ_mem z).mp hz).2; have hzr : z = (z.re : ℂ) := Complex.ext rfl (hreal z hfz)
    have h1 := (hf.analyticAt z).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hfz
      (by rw [hzr]; exact hsimple z.re (by rwa [← hzr]))
    simp [analyticOrderNatAt, h1]
  have hzc : zeroCount f (x₀ : ℂ) r = Z.card := by
    unfold zeroCount; rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hfin]
    calc ∑ z ∈ Z, analyticOrderNatAt f z = ∑ _z ∈ Z, 1 := Finset.sum_congr rfl hZ_ord
      _ = Z.card := by simp
  let T : Finset ℝ := Z.image Complex.re
  have hcard : T.card = Z.card := Finset.card_image_of_injOn fun z₁ hz₁ z₂ hz₂ heq =>
    Complex.ext heq ((hreal z₁ ((hZ_mem z₁).mp hz₁).2).trans (hreal z₂ ((hZ_mem z₂).mp hz₂).2).symm)
  refine ⟨T, hcard.trans hzc.symm, fun t => ?_⟩; simp only [T, Finset.mem_image, hZ_mem]
  constructor
  · rintro ⟨z, ⟨hzb, hfz⟩, rfl⟩
    have hzr : z = (z.re : ℂ) := Complex.ext rfl (hreal z hfz)
    rw [mem_ball, dist_eq_norm, hzr, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt] at hzb
    exact ⟨⟨by linarith, by linarith⟩, by rwa [← hzr]⟩
  · rintro ⟨ht, hft⟩
    refine ⟨(t : ℂ), ⟨?_, hft⟩, Complex.ofReal_re t⟩
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

noncomputable def oddShellS (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (b η : ℝ) : Finset ℝ :=
  if hη : 0 < η then (oddShellHBData ℓ hℓ b η hη).S else ∅

private lemma oddShell_top_zeros_partition {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {b : ℝ} (hb : 0 < b) :
    let astar := (airyZero (ℓ + 2) + airyZero (ℓ + 1)) / 2
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ < 1 / 2 ∧ r₀ < (airyZero (ℓ + 1) - astar) / 2 ∧
      (∀ s₁ ∈ oddShellSites ℓ b, ∀ s₂ ∈ oddShellSites ℓ b, s₁ ≠ s₂ → 3 * r₀ ≤ |s₁ - s₂|) ∧
      ∀ δ ∈ Ioo 0 r₀, ∀ᶠ η : ℝ in 𝓝[>] 0,
        (∀ s ∈ oddShellSites ℓ b,
          ((oddShellS ℓ hℓ b η).filter (fun t => t ∈ Ioo (s - δ) (s + δ))).card = oddShellMult ℓ b s) ∧
        (oddShellS ℓ hℓ b η = (oddShellSites ℓ b).biUnion
          (fun s => (oddShellS ℓ hℓ b η).filter (fun t => t ∈ Ioo (s - δ) (s + δ)))) ∧
        (∀ t ∈ oddShellS ℓ hℓ b η, ∃ s ∈ oddShellSites ℓ b, t ∈ Ioo (s - δ) (s + δ)) := by
  intro astar
  let f₀ : ℂ → ℂ := fun z => airyPQc (oddShellB ℓ b) z * airyAiC z
  have hf₀_diff : Differentiable ℂ f₀ := (differentiable_airyPQc _).mul differentiable_airyAiC
  have ha_lt : airyZero (ℓ + 2) < airyZero (ℓ + 1) := airyZero_strictAnti (by omega)
  have hastar_gt : airyZero (ℓ + 2) < astar := by dsimp [astar]; linarith
  have hastar_lt : astar < airyZero (ℓ + 1) := by dsimp [astar]; linarith
  have hD_ne : (oddShellSites ℓ b).offDiag.Nonempty := ⟨(b, airyZero 1), Finset.mem_offDiag.mpr
    ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)),
      (airyZero_ne_of_pos hb 1).symm⟩⟩
  obtain ⟨p₀, hp₀_mem, hp₀_min⟩ := (oddShellSites ℓ b).offDiag.exists_min_image (fun p : ℝ × ℝ => |p.1 - p.2|) hD_ne
  have hp₀_pos : 0 < |p₀.1 - p₀.2| := abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_offDiag.mp hp₀_mem).2.2)
  have hloc_each : ∀ s ∈ oddShellSites ℓ b,
      ∃ r_s : ℝ, 0 < r_s ∧ (∀ z : ℂ, 0 < dist z (s : ℂ) → dist z (s : ℂ) < r_s → f₀ z ≠ 0) := fun s hs => by
    have hnz : ¬ ∀ᶠ z in 𝓝 (s : ℂ), f₀ z = 0 := fun h => by
      have hord := oddShellLimit_orderNatAt hℓ hb hs
      have htop : analyticOrderAt f₀ (s : ℂ) = ⊤ := analyticOrderAt_eq_top.mpr h
      change (analyticOrderAt f₀ (s : ℂ)).toNat = oddShellMult ℓ b s at hord
      rw [htop] at hord; simp only [ENat.toNat_top] at hord
      have : oddShellMult ℓ b s = 0 := hord.symm; unfold oddShellMult at this; split_ifs at this
    obtain ⟨ρ, hρ, _, hρne⟩ := exists_punctured_disc hf₀_diff.differentiableOn isOpen_univ (mem_univ _) hnz
    exact ⟨ρ, hρ, hρne⟩
  choose r_of hr_pos hr_ne using fun s : {s // s ∈ oddShellSites ℓ b} => hloc_each s.1 s.2
  obtain ⟨s_min, _, hs_min⟩ := (oddShellSites ℓ b).attach.exists_min_image r_of
    ⟨⟨b, Finset.mem_insert_self _ _⟩, Finset.mem_attach _ _⟩
  let r₀ := min (1 / 4 : ℝ) (min ((airyZero (ℓ + 1) - astar) / 4) (min (|p₀.1 - p₀.2| / 4) (r_of s_min)))
  have hr₀_pos : 0 < r₀ := lt_min (by norm_num) (lt_min (by linarith) (lt_min (by linarith) (hr_pos s_min)))
  have hr₀_sep : ∀ s₁ ∈ oddShellSites ℓ b, ∀ s₂ ∈ oddShellSites ℓ b, s₁ ≠ s₂ → 3 * r₀ ≤ |s₁ - s₂| := fun s₁ hs₁ s₂ hs₂ hne => by
    have h1 := hp₀_min (s₁, s₂) (Finset.mem_offDiag.mpr ⟨hs₁, hs₂, hne⟩)
    have h2 : r₀ ≤ |p₀.1 - p₀.2| / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  refine ⟨r₀, hr₀_pos, (min_le_left (1 / 4 : ℝ) _).trans_lt (by norm_num),
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith), hr₀_sep, fun δ hδ => ?_⟩
  have hδ_pos : 0 < δ := hδ.1
  have hHurwitz_all : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ s ∈ oddShellSites ℓ b,
      (∀ z ∈ sphere (s : ℂ) δ, airyPQN (oddShellP ℓ b η) (oddShellQ ℓ b η) z ≠ 0) ∧
      zeroCount (airyPQN (oddShellP ℓ b η) (oddShellQ ℓ b η)) (s : ℂ) δ = oddShellMult ℓ b s := by
    rw [Finset.eventually_all]; intro s hs
    have hδρ : δ < r_of ⟨s, hs⟩ := hδ.2.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (hs_min ⟨s, hs⟩ (Finset.mem_attach _ _)))))
    have hsph : ∀ z ∈ sphere (s : ℂ) δ, f₀ z ≠ 0 := fun z hz =>
      hr_ne ⟨s, hs⟩ z (by rw [mem_sphere.mp hz]; exact hδ_pos) (by rw [mem_sphere.mp hz]; exact hδρ)
    have h1 := hurwitz_zeroCount isOpen_univ (oddShell_tendstoLocallyUniformly ℓ b)
      (Eventually.of_forall fun η => (differentiable_airyPQN _ _).differentiableOn)
      hf₀_diff.differentiableOn hδ_pos hδρ (subset_univ _) hsph
    have h2 := zeroCount_eq_orderNat (f := f₀) hf₀_diff.differentiableOn hδ_pos hδρ hδρ (hr_ne ⟨s, hs⟩)
    rw [oddShellLimit_orderNatAt hℓ hb hs] at h2
    exact h1.mono fun η hη => ⟨hη.1, hη.2.trans h2⟩
  let K : Set ℂ := Complex.ofReal '' Icc astar (b + 1)
  let W : Set ℂ := ⋃ s ∈ oddShellSites ℓ b, ball (s : ℂ) δ
  have hKW : ∀ z ∈ K, f₀ z = 0 → z ∈ W := by
    rintro z ⟨x, hx, rfl⟩ hfx
    refine mem_biUnion ?_ (mem_ball_self hδ_pos)
    rcases mul_eq_zero.mp hfx with hB | hA
    · rcases (oddShellB_eval_eq_zero_iff ℓ b (x : ℂ)).mp hB with heq | ⟨k, hk, heq⟩
      · rw [Complex.ofReal_injective heq]; exact Finset.mem_insert_self _ _
      · rw [Complex.ofReal_injective heq]; exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
          (Finset.mem_Icc.mpr ⟨by simp at hk; omega, by simp at hk; omega⟩))
    · obtain ⟨k, hk1, heq⟩ := (airyAiC_eq_zero_iff (x : ℂ)).mp hA
      rw [Complex.ofReal_injective heq]
      have hk_le : k ≤ ℓ + 1 := by
        by_contra hgt; push Not at hgt
        have := airyZero_le_of_le (by omega : 1 ≤ ℓ + 2) (by omega : ℓ + 2 ≤ k)
        rw [Complex.ofReal_injective heq] at hx; linarith [hx.1]
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨hk1, hk_le⟩))
  have hNoZeros := hurwitz_no_zeros_off isOpen_univ (oddShell_tendstoLocallyUniformly ℓ b)
    (Eventually.of_forall fun η => (differentiable_airyPQN _ _).continuous.continuousOn)
    (isCompact_Icc.image Complex.continuous_ofReal) (subset_univ _) (isOpen_biUnion fun _ _ => isOpen_ball) hKW
  obtain ⟨η₀, hη₀, hposR⟩ := oddShellN_pos_right hℓ hb
  filter_upwards [hHurwitz_all, hNoZeros, Ioo_mem_nhdsGT hη₀] with η hHur hOff hηI
  have hη : 0 < η := hηI.1; let D := oddShellHBData ℓ hℓ b η hη
  have hS_eq_def : oddShellS ℓ hℓ b η = D.S := by dsimp [oddShellS]; split_ifs; rfl
  have hD_card : D.S.card = 2 * ℓ + 1 := oddShellHBData_S_card ℓ hℓ b η hη
  have hHB := oddShell_airypqhb ℓ b hη; have hQ := oddShellQ_ne_zero hℓ b hη
  have hsimple_z : ∀ x : ℝ, airyPQN (oddShellP ℓ b η) (oddShellQ ℓ b η) (x : ℂ) = 0 →
      deriv (airyPQN (oddShellP ℓ b η) (oddShellQ ℓ b η)) (x : ℂ) ≠ 0 := fun x hx => by
    rw [deriv_airyPQN]; exact (airyPQ_zero_weight_pos hHB hQ hx).2
  have hball_ex : ∀ s (hs : s ∈ oddShellSites ℓ b), ∃ T : Finset ℝ,
      T.card = oddShellMult ℓ b s ∧ ∀ t : ℝ, t ∈ T ↔ t ∈ Ioo (s - δ) (s + δ) ∧
        airyPQN (oddShellP ℓ b η) (oddShellQ ℓ b η) (t : ℂ) = 0 := fun s hs => by
    obtain ⟨T, hTc, hTm⟩ := real_zeros_card_eq_zeroCount (differentiable_airyPQN _ _)
      (fun z hz => airyPQ_zero_im hHB hz) hsimple_z hδ_pos (hHur s hs).1
    exact ⟨T, hTc.trans (hHur s hs).2, hTm⟩
  choose T_of hT_card hT_mem using fun s : {s // s ∈ oddShellSites ℓ b} => hball_ex s.1 s.2
  let Z : Finset ℝ := (oddShellSites ℓ b).attach.biUnion T_of
  have hdisj : Set.PairwiseDisjoint ↑(oddShellSites ℓ b).attach T_of := by
    rintro ⟨s₁, hs₁⟩ _ ⟨s₂, hs₂⟩ _ hne; refine Finset.disjoint_left.mpr fun t ht₁ ht₂ => ?_
    have hm1 := ((hT_mem ⟨s₁, hs₁⟩ t).mp ht₁).1; have hm2 := ((hT_mem ⟨s₂, hs₂⟩ t).mp ht₂).1
    have htri : |s₁ - s₂| ≤ |s₁ - t| + |t - s₂| := (by ring_nf : |s₁ - s₂| = |(s₁ - t) + (t - s₂)|) ▸ abs_add_le _ _
    have hst1 : |s₁ - t| < δ := abs_lt.mpr ⟨by linarith [hm1.2], by linarith [hm1.1]⟩
    have hst2 : |t - s₂| < δ := abs_lt.mpr ⟨by linarith [hm2.1], by linarith [hm2.2]⟩
    linarith [hr₀_sep s₁ hs₁ s₂ hs₂ (fun h => hne (Subtype.ext h)), hδ.2]
  have hZ_card : Z.card = 2 * ℓ + 1 := by
    dsimp [Z]; rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl fun s _ => hT_card s,
      Finset.sum_attach (oddShellSites ℓ b) (oddShellMult ℓ b), oddShellMult_sum hℓ hb]
  have hZ_zero : ∀ t ∈ Z, airyPQN (oddShellP ℓ b η) (oddShellQ ℓ b η) (t : ℂ) = 0 := fun t ht => by
    obtain ⟨s, _, hts⟩ := Finset.mem_biUnion.mp ht; exact ((hT_mem s t).mp hts).2
  have hZ_ge : ∀ t ∈ Z, astar ≤ t := fun t ht => by
    obtain ⟨⟨s, hs⟩, _, hts⟩ := Finset.mem_biUnion.mp ht
    have htI := ((hT_mem ⟨s, hs⟩ t).mp hts).1
    have hs_ge : airyZero (ℓ + 1) ≤ s := by
      simp only [oddShellSites, Finset.mem_insert, Finset.mem_image, Finset.mem_Icc] at hs
      rcases hs with rfl | ⟨k, hk, rfl⟩; exact (airyZero_neg (ℓ + 1)).le.trans hb.le; exact airyZero_le_of_le hk.1 hk.2
    have hr_bd : r₀ ≤ (airyZero (ℓ + 1) - astar) / 4 := (min_le_right _ _).trans (min_le_left _ _)
    linarith [htI.1, hδ.2]
  have hS_sub_Z : D.S ⊆ Z := fun t ht => by
    have htN : airyPQN (oddShellP ℓ b η) (oddShellQ ℓ b η) (t : ℂ) = 0 := (hbTopZeros_spec hHB hQ).2.1 t ht
    have ht_lt_right : t < b + 1 := by
      by_contra hle; push Not at hle
      have hpos := hposR η hηI t hle; rw [airyPQN_ofReal] at htN; exact hpos.ne' (by exact_mod_cast htN)
    have ht_ge_astar : astar ≤ t := by
      by_contra hlt; push Not at hlt
      have hZ_sub_S : Z ⊆ D.S := fun x hx => by
        by_contra hxS; exact absurd (D.S_top x (hZ_zero x hx) hxS t ht) (not_lt.mpr (hlt.le.trans (hZ_ge x hx)))
      have := Finset.card_lt_card ⟨hZ_sub_S, fun h => absurd (hZ_ge t (h ht)) (not_le.mpr hlt)⟩; omega
    have htW : (t : ℂ) ∈ W := by by_contra hntW; exact hOff (t : ℂ) ⟨⟨t, ⟨ht_ge_astar, ht_lt_right.le⟩, rfl⟩, hntW⟩ htN
    simp only [W, Set.mem_iUnion, exists_prop] at htW; obtain ⟨s, hs, hts⟩ := htW
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt] at hts
    exact Finset.mem_biUnion.mpr ⟨⟨s, hs⟩, Finset.mem_attach _ _, (hT_mem ⟨s, hs⟩ t).mpr ⟨⟨by linarith, by linarith⟩, htN⟩⟩
  have hS_eq_Z : D.S = Z := Finset.eq_of_subset_of_card_le hS_sub_Z (by rw [hD_card, hZ_card])
  have hfilt_eq : ∀ s (hs : s ∈ oddShellSites ℓ b),
      D.S.filter (fun t => t ∈ Ioo (s - δ) (s + δ)) = T_of ⟨s, hs⟩ := fun s hs => by
    ext t; rw [Finset.mem_filter, hS_eq_Z]
    constructor
    · rintro ⟨htZ, htI⟩; obtain ⟨⟨s', hs'⟩, _, htT⟩ := Finset.mem_biUnion.mp htZ
      by_cases heq : s' = s
      · subst heq; exact htT
      · exact False.elim (Finset.disjoint_left.mp (hdisj (Finset.mem_attach _ ⟨s, hs⟩)
          (Finset.mem_attach _ ⟨s', hs'⟩) fun h => heq (congrArg Subtype.val h).symm)
          ((hT_mem ⟨s, hs⟩ t).mpr ⟨htI, hZ_zero t (Finset.mem_biUnion.mpr ⟨⟨s', hs'⟩, Finset.mem_attach _ _, htT⟩)⟩) htT)
    · intro htT; exact ⟨Finset.mem_biUnion.mpr ⟨⟨s, hs⟩, Finset.mem_attach _ _, htT⟩, ((hT_mem ⟨s, hs⟩ t).mp htT).1⟩
  rw [hS_eq_def]
  refine ⟨fun s hs => by rw [hfilt_eq s hs, hT_card], ?_, fun t ht => ?_⟩
  · ext t; rw [Finset.mem_biUnion]
    constructor
    · intro ht; rw [hS_eq_Z] at ht; obtain ⟨⟨s, hs⟩, _, htT⟩ := Finset.mem_biUnion.mp ht
      exact ⟨s, hs, by rw [hfilt_eq s hs]; exact htT⟩
    · rintro ⟨s, hs, htF⟩; rw [hfilt_eq s hs] at htF; rw [hS_eq_Z]
      exact Finset.mem_biUnion.mpr ⟨⟨s, hs⟩, Finset.mem_attach _ _, htF⟩
  · rw [hS_eq_Z, Finset.mem_biUnion] at ht; obtain ⟨⟨s, hs⟩, _, htT⟩ := ht
    exact ⟨s, hs, ((hT_mem ⟨s, hs⟩ t).mp htT).1⟩

private lemma norm_finset_prod_sub_pow_le {ι : Type*} (F : Finset ι) (w : ι → ℂ) (c : ℂ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hw : ∀ i ∈ F, ‖w i - c‖ ≤ δ) :
    ‖(∏ i ∈ F, w i) - c ^ F.card‖ ≤ (‖c‖ + δ) ^ F.card - ‖c‖ ^ F.card := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a F ha ih =>
    have hwF : ∀ i ∈ F, ‖w i - c‖ ≤ δ := fun i hi => hw i (Finset.mem_insert_of_mem hi)
    have hwa_le : ‖w a‖ ≤ ‖c‖ + δ := (by ring_nf : w a = (w a - c) + c) ▸
      (norm_add_le _ _).trans (by linarith [hw a (Finset.mem_insert_self _ _)])
    have hP_le : ‖∏ i ∈ F, w i‖ ≤ (‖c‖ + δ) ^ F.card := by
      rw [norm_prod]
      refine (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i hi => ?_).trans_eq
        (by rw [Finset.prod_const])
      calc ‖w i‖ = ‖(w i - c) + c‖ := by ring_nf
        _ ≤ ‖w i - c‖ + ‖c‖ := norm_add_le _ _
        _ ≤ ‖c‖ + δ := by linarith [hwF i hi]
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
      show w a * (∏ i ∈ F, w i) - c ^ (F.card + 1) =
        (w a - c) * (∏ i ∈ F, w i) + c * ((∏ i ∈ F, w i) - c ^ F.card) by rw [pow_succ']; ring]
    calc ‖(w a - c) * (∏ i ∈ F, w i) + c * ((∏ i ∈ F, w i) - c ^ F.card)‖
        ≤ ‖w a - c‖ * ‖∏ i ∈ F, w i‖ + ‖c‖ * ‖(∏ i ∈ F, w i) - c ^ F.card‖ :=
          (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
      _ ≤ δ * (‖c‖ + δ) ^ F.card + ‖c‖ * ((‖c‖ + δ) ^ F.card - ‖c‖ ^ F.card) := by
          gcongr; exact hw a (Finset.mem_insert_self _ _); exact ih hwF
      _ = (‖c‖ + δ) ^ (F.card + 1) - ‖c‖ ^ (F.card + 1) := by rw [pow_succ', pow_succ']; ring

noncomputable def oddShellLimitDenom (ℓ : ℕ) (b : ℝ) (z : ℂ) : ℂ :=
  ∏ s ∈ oddShellSites ℓ b, (z - (s : ℂ)) ^ oddShellMult ℓ b s

lemma oddShellLimitDenom_eq {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {b : ℝ} (hb : 0 < b) (z : ℂ) :
    oddShellLimitDenom ℓ b z =
      (z - (b : ℂ)) * (z - (airyZero 1 : ℂ)) * (z - (airyZero (ℓ + 1) : ℂ)) *
        ∏ k ∈ Finset.Icc 2 ℓ, (z - (airyZero k : ℂ)) ^ 2 := by
  unfold oddShellLimitDenom
  have hb_not : b ∉ (Finset.Icc 1 (ℓ + 1)).image airyZero := by
    simp only [Finset.mem_image, Finset.mem_Icc]; rintro ⟨k, -, hk⟩; exact airyZero_ne_of_pos hb k hk
  rw [oddShellSites, Finset.prod_insert hb_not, show oddShellMult ℓ b b = 1 by simp [oddShellMult],
    pow_one, Finset.prod_image (fun x hx y hy hxy => airyZero_injOn
      (Set.mem_Ici.mpr (Finset.mem_Icc.mp hx).1) (Set.mem_Ici.mpr (Finset.mem_Icc.mp hy).1) hxy)]
  have h1_not : 1 ∉ insert (ℓ + 1) (Finset.Icc 2 ℓ) := by simp; omega
  have hlp1_not : ℓ + 1 ∉ Finset.Icc 2 ℓ := by simp
  have hIcc_eq : Finset.Icc 1 (ℓ + 1) = insert 1 (insert (ℓ + 1) (Finset.Icc 2 ℓ)) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hIcc_eq, Finset.prod_insert h1_not, Finset.prod_insert hlp1_not,
    show oddShellMult ℓ b (airyZero 1) = 1 by simp [oddShellMult],
    show oddShellMult ℓ b (airyZero (ℓ + 1)) = 1 by simp [oddShellMult], pow_one, pow_one]
  have hmid : ∏ k ∈ Finset.Icc 2 ℓ, (z - (airyZero k : ℂ)) ^ oddShellMult ℓ b (airyZero k) =
      ∏ k ∈ Finset.Icc 2 ℓ, (z - (airyZero k : ℂ)) ^ 2 :=
    Finset.prod_congr rfl fun k hk => by
      simp only [Finset.mem_Icc] at hk
      have hm : oddShellMult ℓ b (airyZero k) = 2 := by
        unfold oddShellMult; split_ifs with h
        · exfalso; rcases h with h | h | h
          · exact airyZero_ne_of_pos hb k h
          · have := airyZero_injOn (Set.mem_Ici.mpr (by omega)) (Set.mem_Ici.mpr le_rfl) h; omega
          · have := airyZero_injOn (Set.mem_Ici.mpr (by omega)) (Set.mem_Ici.mpr (by omega)) h; omega
        · rfl
      rw [hm]
  rw [hmid]; ring

theorem oddShell_prod_tendsto {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {b : ℝ} (hb : 0 < b) (z : ℂ) :
    Tendsto (fun η => at47_pr (oddShellS ℓ hℓ b η) z) (𝓝[>] 0) (𝓝 (oddShellLimitDenom ℓ b z)) := by
  obtain ⟨r₀, hr₀, _, _, hgap, hpart⟩ := oddShell_top_zeros_partition hℓ hb
  have hpart0 := hpart (r₀ / 2) ⟨by linarith, by linarith⟩
  have hprod_eq : ∀ᶠ η : ℝ in 𝓝[>] 0, at47_pr (oddShellS ℓ hℓ b η) z =
      ∏ s ∈ oddShellSites ℓ b, ∏ t ∈ (oddShellS ℓ hℓ b η).filter
        (fun t => t ∈ Ioo (s - r₀ / 2) (s + r₀ / 2)), (z - (t : ℂ)) := by
    filter_upwards [hpart0] with η hη
    unfold at47_pr; conv_lhs => rw [hη.2.1]
    refine Finset.prod_biUnion fun s₁ hs₁ s₂ hs₂ hne => Finset.disjoint_left.mpr fun t ht1 ht2 => ?_
    have hm1 := (Finset.mem_filter.mp ht1).2; have hm2 := (Finset.mem_filter.mp ht2).2
    have htri : |s₁ - s₂| ≤ |s₁ - t| + |t - s₂| :=
      (by ring_nf : |s₁ - s₂| = |(s₁ - t) + (t - s₂)|) ▸ abs_add_le _ _
    have hst1 : |s₁ - t| < r₀ / 2 := abs_lt.mpr ⟨by linarith [hm1.2], by linarith [hm1.1]⟩
    have hst2 : |t - s₂| < r₀ / 2 := abs_lt.mpr ⟨by linarith [hm2.1], by linarith [hm2.2]⟩
    linarith [hgap s₁ hs₁ s₂ hs₂ hne]
  have hfactor : ∀ s ∈ oddShellSites ℓ b,
      Tendsto (fun η => ∏ t ∈ (oddShellS ℓ hℓ b η).filter
        (fun t => t ∈ Ioo (s - r₀ / 2) (s + r₀ / 2)), (z - (t : ℂ)))
        (𝓝[>] 0) (𝓝 ((z - (s : ℂ)) ^ oddShellMult ℓ b s)) := by
    intro s hs; rw [Metric.tendsto_nhds]; intro ε hε
    let k := oddShellMult ℓ b s
    have hlim_d : Tendsto (fun δ : ℝ => (‖z - (s : ℂ)‖ + δ) ^ k - ‖z - (s : ℂ)‖ ^ k) (𝓝 0) (𝓝 0) := by
      simpa using (Continuous.tendsto (by fun_prop : Continuous fun δ : ℝ =>
        (‖z - (s : ℂ)‖ + δ) ^ k - ‖z - (s : ℂ)‖ ^ k) 0)
    obtain ⟨δ₁, hδ₁, hδ₁_bd⟩ := Metric.tendsto_nhds_nhds.mp hlim_d ε hε
    let δ := min (r₀ / 2) (δ₁ / 2)
    have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
    have hbd_val : (‖z - (s : ℂ)‖ + δ) ^ k - ‖z - (s : ℂ)‖ ^ k < ε := by
      have h1 := hδ₁_bd (mem_ball.mpr (by rw [Real.dist_eq, sub_zero, abs_of_pos hδ_pos]; exact (min_le_right _ _).trans_lt (by linarith)))
      rw [Real.dist_eq, sub_zero] at h1; exact (le_abs_self _).trans_lt h1
    filter_upwards [hpart0, hpart δ ⟨hδ_pos, (min_le_left _ _).trans_lt (by linarith)⟩] with η hη0 hηδ
    have heq_filt : (oddShellS ℓ hℓ b η).filter (fun t => t ∈ Ioo (s - r₀ / 2) (s + r₀ / 2)) =
        (oddShellS ℓ hℓ b η).filter (fun t => t ∈ Ioo (s - δ) (s + δ)) := by
      refine (Finset.eq_of_subset_of_card_le (fun t ht => ?_) (by rw [hη0.1 s hs, hηδ.1 s hs])).symm
      rw [Finset.mem_filter] at ht ⊢; have hδle : δ ≤ r₀ / 2 := min_le_left _ _
      exact ⟨ht.1, by linarith [ht.2.1], by linarith [ht.2.2]⟩
    rw [heq_filt, dist_eq_norm]
    have hnorm := norm_finset_prod_sub_pow_le ((oddShellS ℓ hℓ b η).filter (fun t => t ∈ Ioo (s - δ) (s + δ)))
      (fun t => z - (t : ℂ)) (z - (s : ℂ)) hδ_pos.le fun t ht => by
        have htI := (Finset.mem_filter.mp ht).2
        have heq : (z - (t : ℂ)) - (z - (s : ℂ)) = ((s - t : ℝ) : ℂ) := by push_cast; ring
        rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_le]; exact ⟨by linarith [htI.2], by linarith [htI.1]⟩
    rw [hηδ.1 s hs] at hnorm; exact hnorm.trans_lt hbd_val
  exact (tendsto_finsetProd (oddShellSites ℓ b) hfactor).congr' (hprod_eq.mono fun _ h => h.symm)

/-! ### Section 4: `oddShellHC` / `oddShellH`, Pointwise Convergence, and Dominated Laplace Limit -/

/-- Limiting kernel factor `H_ℓ(z) = dslope Ai a₁ z * dslope Ai a_{ℓ+1} z` (`Ai(z)² / ((a₁ - z)(a_{ℓ+1} - z))`),
entire on `ℂ`. -/
noncomputable def oddShellHC (ℓ : ℕ) (z : ℂ) : ℂ :=
  dslope airyAiC (airyZero 1 : ℂ) z * dslope airyAiC (airyZero (ℓ + 1) : ℂ) z

/-- Real restriction `H_ℓ(u) = Re(oddShellHC ℓ u)`. -/
noncomputable def oddShellH (ℓ : ℕ) (u : ℝ) : ℝ := (oddShellHC ℓ (u : ℂ)).re

lemma oddShellHC_differentiable (ℓ : ℕ) : Differentiable ℂ (oddShellHC ℓ) :=
  (differentiable_dslope_entire differentiable_airyAiC _).mul (differentiable_dslope_entire differentiable_airyAiC _)

lemma oddShellHC_eq_div (ℓ : ℕ) {z : ℂ} (h1 : z ≠ (airyZero 1 : ℂ)) (h2 : z ≠ (airyZero (ℓ + 1) : ℂ)) :
    oddShellHC ℓ z = airyAiC z ^ 2 / (((airyZero 1 : ℂ) - z) * ((airyZero (ℓ + 1) : ℂ) - z)) := by
  unfold oddShellHC
  rw [dslope_of_ne _ h1, dslope_of_ne _ h2, slope_def_field, slope_def_field, airyAiC_airyZero, airyAiC_airyZero]
  have h1' : (airyZero 1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr h1.symm
  have h2' : (airyZero (ℓ + 1) : ℂ) - z ≠ 0 := sub_ne_zero.mpr h2.symm
  have h1'' : z - (airyZero 1 : ℂ) ≠ 0 := sub_ne_zero.mpr h1
  have h2'' : z - (airyZero (ℓ + 1) : ℂ) ≠ 0 := sub_ne_zero.mpr h2
  field_simp; ring

private lemma oddShellHC_ofReal {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (u : ℝ) :
    oddShellHC ℓ (u : ℂ) = ((airyAi u ^ 2 / ((airyZero 1 - u) * (airyZero (ℓ + 1) - u)) : ℝ) : ℂ) := by
  have hne : (airyZero 1 : ℂ) ≠ (airyZero (ℓ + 1) : ℂ) :=
    fun h => absurd (Complex.ofReal_injective h)
      (ne_of_gt (airyZero_lt_of_lt le_rfl (by omega : 1 < ℓ + 1)))
  by_cases h1 : u = airyZero 1
  · subst h1; unfold oddShellHC
    conv_lhs =>
      rhs
      rw [dslope_of_ne _ hne, slope_def_field, airyAiC_airyZero, airyAiC_airyZero, sub_self, zero_div]
    rw [mul_zero, airyAi_airyZero, sq, zero_mul, zero_div, Complex.ofReal_zero]
  · by_cases h2 : u = airyZero (ℓ + 1)
    · subst h2; unfold oddShellHC
      conv_lhs =>
        lhs
        rw [dslope_of_ne _ hne.symm, slope_def_field, airyAiC_airyZero, airyAiC_airyZero, sub_self, zero_div]
      rw [zero_mul, airyAi_airyZero, sq, zero_mul, zero_div, Complex.ofReal_zero]
    · rw [oddShellHC_eq_div ℓ (fun h => h1 (Complex.ofReal_injective h))
        (fun h => h2 (Complex.ofReal_injective h)), airyAiC_ofReal]; push_cast; rfl

lemma oddShellH_eq_div {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (u : ℝ) :
    oddShellH ℓ u = airyAi u ^ 2 / ((airyZero 1 - u) * (airyZero (ℓ + 1) - u)) := by
  unfold oddShellH; rw [oddShellHC_ofReal hℓ u, Complex.ofReal_re]

lemma oddShellHC_im_eq_zero {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (u : ℝ) : (oddShellHC ℓ (u : ℂ)).im = 0 := by
  rw [oddShellHC_ofReal hℓ u, Complex.ofReal_im]

lemma oddShellHC_inAiryClass {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : InAiryClass (oddShellHC ℓ) := by
  have hdiff := oddShellHC_differentiable ℓ
  let R₀ : ℝ := max |airyZero 1| |airyZero (ℓ + 1)| + 1
  have hR₀_abs : 0 ≤ max |airyZero 1| |airyZero (ℓ + 1)| := le_trans (abs_nonneg _) (le_max_left _ _)
  have hR₀ : 1 ≤ R₀ := by dsimp [R₀]; linarith
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R₀).exists_bound_of_continuousOn hdiff.continuous.continuousOn
  let M' := max M 0; let e₀ := Real.exp (-(4 / 3) * R₀ ^ (3 / 2 : ℝ)); have he₀ : 0 < e₀ := Real.exp_pos _
  have hden_ge : ∀ z : ℂ, R₀ < ‖z‖ →
      z ≠ (airyZero 1 : ℂ) ∧ z ≠ (airyZero (ℓ + 1) : ℂ) ∧
      1 ≤ ‖(airyZero 1 : ℂ) - z‖ ∧ 1 ≤ ‖(airyZero (ℓ + 1) : ℂ) - z‖ := fun z hz => by
    have h1 := norm_sub_norm_le z (airyZero 1 : ℂ); have h2 := norm_sub_norm_le z (airyZero (ℓ + 1) : ℂ)
    rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs] at h1 h2
    have hm1 := le_max_left |airyZero 1| |airyZero (ℓ + 1)|; have hm2 := le_max_right |airyZero 1| |airyZero (ℓ + 1)|
    refine ⟨fun h => by rw [h, Complex.norm_real, Real.norm_eq_abs] at hz; linarith,
      fun h => by rw [h, Complex.norm_real, Real.norm_eq_abs] at hz; linarith, by linarith, by linarith⟩
  have henv_bd : ∀ u : ℂ, ‖oddShellHC ℓ u‖ ≤ max 9 (M' / e₀) * (1 + ‖u‖) ^ (0 : ℝ) * airyEnv u := by
    intro u; rw [Real.rpow_zero, mul_one]
    by_cases hu : ‖u‖ ≤ R₀
    · have henv : e₀ ≤ airyEnv u := at47_env_lower hu (by linarith)
      calc ‖oddShellHC ℓ u‖ ≤ M' := (hM u (mem_closedBall_zero_iff.mpr hu)).trans (le_max_left _ _)
        _ = (M' / e₀) * e₀ := by field_simp [he₀.ne']
        _ ≤ (M' / e₀) * airyEnv u := by gcongr
        _ ≤ max 9 (M' / e₀) * airyEnv u := mul_le_mul_of_nonneg_right (le_max_right _ _) (airyEnv_pos u).le
    · push Not at hu; obtain ⟨hne1, hne2, h1_ge, h2_ge⟩ := hden_ge u hu
      rw [oddShellHC_eq_div ℓ hne1 hne2, norm_div, norm_pow, norm_mul]
      have hpow : (1 + ‖u‖) ^ (-(1 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg u]) (by norm_num)
      calc ‖airyAiC u‖ ^ 2 / (‖(airyZero 1 : ℂ) - u‖ * ‖(airyZero (ℓ + 1) : ℂ) - u‖)
          ≤ ‖airyAiC u‖ ^ 2 := div_le_self (sq_nonneg _) (by nlinarith)
        _ ≤ 9 * (1 + ‖u‖) ^ (-(1 / 2) : ℝ) * airyEnv u := airyAiC_norm_sq_le u
        _ ≤ 9 * 1 * airyEnv u := by gcongr; exact (airyEnv_pos u).le
        _ ≤ max 9 (M' / e₀) * airyEnv u := mul_le_mul_of_nonneg_right (by linarith [le_max_left 9 (M' / e₀)]) (airyEnv_pos u).le
  have hint : Integrable (fun x : ℝ => oddShellHC ℓ (x : ℂ)) := by
    let A := 2 * R₀
    have hc : Continuous (fun x : ℝ => oddShellHC ℓ (x : ℂ)) := hdiff.continuous.comp Complex.continuous_ofReal
    obtain ⟨MA, hMA⟩ := (isCompact_Icc (a := -A) (b := A)).exists_bound_of_continuousOn hc.continuousOn
    let K : ℝ := max 144 (max MA 0 * (1 + A) ^ 2)
    have hint2 : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(2 : ℝ))) := integrable_one_add_norm (E := ℝ) (by simp)
    refine (hint2.const_mul K).mono' hc.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    have hx1 : 0 < 1 + |x| := by positivity
    have hrpow2 : (1 + |x|) ^ (-(2 : ℝ)) = ((1 + |x|) ^ 2)⁻¹ := by
      rw [Real.rpow_neg hx1.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [Real.norm_eq_abs, hrpow2]
    by_cases hx : |x| ≤ A
    · have h1x : (1 + |x|) ^ 2 ≤ (1 + A) ^ 2 := by gcongr
      calc ‖oddShellHC ℓ (x : ℂ)‖ ≤ max MA 0 := (hMA x (abs_le.mp hx)).trans (le_max_left _ _)
        _ ≤ (max MA 0 * (1 + A) ^ 2) / (1 + |x|) ^ 2 := by rw [le_div_iff₀ (by positivity)]; exact mul_le_mul_of_nonneg_left h1x (le_max_right _ _)
        _ = max MA 0 * (1 + A) ^ 2 * ((1 + |x|) ^ 2)⁻¹ := div_eq_mul_inv _ _
        _ ≤ K * ((1 + |x|) ^ 2)⁻¹ := by gcongr; exact le_max_right _ _
    · push Not at hx; have hx_gt : R₀ < |x| := by dsimp [A] at hx; linarith
      obtain ⟨hne1, hne2, _, _⟩ := hden_ge (x : ℂ) (by simpa)
      have hden1 : (1 + |x|) / 4 ≤ |airyZero 1 - x| := by
        have := abs_sub_abs_le_abs_sub x (airyZero 1); rw [abs_sub_comm] at this; linarith [le_max_left |airyZero 1| |airyZero (ℓ + 1)|]
      have hden2 : (1 + |x|) / 4 ≤ |airyZero (ℓ + 1) - x| := by
        have := abs_sub_abs_le_abs_sub x (airyZero (ℓ + 1)); rw [abs_sub_comm] at this; linarith [le_max_right |airyZero 1| |airyZero (ℓ + 1)|]
      have hAi : ‖airyAiC (x : ℂ)‖ ^ 2 ≤ 9 := by
        have h := airyAiC_norm_sq_le (x : ℂ); rw [Complex.norm_real, Real.norm_eq_abs] at h
        have h1 : (1 + |x|) ^ (-(1 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
        calc ‖airyAiC (x : ℂ)‖ ^ 2 ≤ 9 * (1 + |x|) ^ (-(1 / 2) : ℝ) * airyEnv (x : ℂ) := h
          _ ≤ 9 * 1 * 1 := mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) (airyEnv_ofReal_le_one x) (airyEnv_pos _).le (by positivity)
          _ = 9 := by ring
      rw [oddShellHC_eq_div ℓ hne1 hne2, norm_div, norm_pow, norm_mul, ← Complex.ofReal_sub, ← Complex.ofReal_sub,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      have hden_mul : ((1 + |x|) / 4) ^ 2 ≤ |airyZero 1 - x| * |airyZero (ℓ + 1) - x| := by rw [sq]; exact mul_le_mul hden1 hden2 (by positivity) (by positivity)
      have heq : (9 : ℝ) / ((1 + |x|) / 4) ^ 2 = 144 * ((1 + |x|) ^ 2)⁻¹ := by
        have hxpos : (0 : ℝ) < 1 + |x| := by positivity
        rw [div_pow]; field_simp; ring
      calc ‖airyAiC (x : ℂ)‖ ^ 2 / (|airyZero 1 - x| * |airyZero (ℓ + 1) - x|)
          ≤ 9 / ((1 + |x|) / 4) ^ 2 := div_le_div₀ (by positivity) hAi (by positivity) hden_mul
        _ = 144 * ((1 + |x|) ^ 2)⁻¹ := heq
        _ ≤ K * ((1 + |x|) ^ 2)⁻¹ := by gcongr; exact le_max_left _ _
  exact ⟨hdiff, hint, ⟨max 9 (M' / e₀), 0, by positivity, henv_bd⟩, oddShellHC_im_eq_zero hℓ⟩

noncomputable def oddShellG (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (b η : ℝ) (z : ℂ) : ℂ :=
  if hη : 0 < η then (oddShellHBData ℓ hℓ b η hη).G z else 0

private lemma oddShell_G_tendsto_off {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {b : ℝ} (hb : 0 < b)
    {z : ℂ} (hz : ∀ s ∈ oddShellSites ℓ b, z ≠ (s : ℂ)) :
    Tendsto (fun η => oddShellG ℓ hℓ b η z) (𝓝[>] 0) (𝓝 (((b : ℂ) - z) * oddShellHC ℓ z)) := by
  have hb_ne : z ≠ (b : ℂ) := hz b (Finset.mem_insert_self _ _)
  have h1_ne : z ≠ (airyZero 1 : ℂ) :=
    hz _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)))
  have hlp1_ne : z ≠ (airyZero (ℓ + 1) : ℂ) :=
    hz _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)))
  have hD_ne : oddShellLimitDenom ℓ b z ≠ 0 := by
    unfold oddShellLimitDenom; rw [Finset.prod_ne_zero_iff]; intro s hs; exact pow_ne_zero _ (sub_ne_zero.mpr (hz s hs))
  have hq_lim : Tendsto
      (fun η => -(airyPQN (oddShellP ℓ b η) (oddShellQ ℓ b η) z) ^ 2 / at47_pr (oddShellS ℓ hℓ b η) z)
      (𝓝[>] 0) (𝓝 (-(airyPQc (oddShellB ℓ b) z * airyAiC z) ^ 2 / oddShellLimitDenom ℓ b z)) :=
    (((oddShell_tendstoLocallyUniformly ℓ b).tendsto_at (mem_univ z)).pow 2 |>.neg).div
      (oddShell_prod_tendsto hℓ hb z) hD_ne
  have hlim_eq : -(airyPQc (oddShellB ℓ b) z * airyAiC z) ^ 2 / oddShellLimitDenom ℓ b z =
      ((b : ℂ) - z) * oddShellHC ℓ z := by
    rw [show airyPQc (oddShellB ℓ b) z = (z - (b : ℂ)) * ∏ k ∈ Finset.Icc 2 ℓ, (z - (airyZero k : ℂ))
        from oddShellB_map_eval ℓ b z,
      oddShellLimitDenom_eq hℓ hb z, oddShellHC_eq_div ℓ h1_ne hlp1_ne, Finset.prod_pow]
    have hP_ne : (∏ k ∈ Finset.Icc 2 ℓ, (z - (airyZero k : ℂ))) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]; intro k hk
      exact sub_ne_zero.mpr (hz _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
        (Finset.mem_Icc.mpr ⟨by simp at hk; omega, by simp at hk; omega⟩))))
    have hzb := sub_ne_zero.mpr hb_ne; have hza1 := sub_ne_zero.mpr h1_ne
    have hzal := sub_ne_zero.mpr hlp1_ne; have ha1z := sub_ne_zero.mpr h1_ne.symm
    have halz := sub_ne_zero.mpr hlp1_ne.symm
    field_simp; ring
  rw [hlim_eq] at hq_lim
  refine hq_lim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, (oddShell_prod_tendsto hℓ hb z).eventually_ne hD_ne] with η hη hDη
  have hη0 : 0 < η := mem_Ioi.mp hη
  have hS_eq : oddShellS ℓ hℓ b η = (oddShellHBData ℓ hℓ b η hη0).S := by dsimp [oddShellS]; split_ifs; rfl
  have hprod := (oddShellHBData ℓ hℓ b η hη0).G_prod_eq z
  have hm_odd : (-1 : ℝ) ^ (oddShellHBData ℓ hℓ b η hη0).S.card = -1 := by
    rw [oddShellHBData_S_card ℓ hℓ b η hη0]; exact Odd.neg_one_pow ⟨ℓ, rfl⟩
  change (oddShellHBData ℓ hℓ b η hη0).G z * at47_pr (oddShellHBData ℓ hℓ b η hη0).S z =
      (((-1 : ℝ) ^ (oddShellHBData ℓ hℓ b η hη0).S.card : ℝ) : ℂ) *
        airyPQN (oddShellP ℓ b η) (oddShellQ ℓ b η) z ^ 2 at hprod
  rw [hm_odd, ← hS_eq] at hprod
  have hGeq : oddShellG ℓ hℓ b η z = (oddShellHBData ℓ hℓ b η hη0).G z := by dsimp [oddShellG]; split_ifs; rfl
  rw [hGeq, div_eq_iff hDη, hprod]; push_cast; ring

private lemma oddShellG_unif_bound {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {b : ℝ} (hb : 0 < b) :
    ∃ R_B K_L M₀ C_N η₁ : ℝ, 1 ≤ R_B ∧ 0 ≤ K_L ∧ 0 ≤ M₀ ∧ 0 ≤ C_N ∧ 0 < η₁ ∧ η₁ ≤ 1 ∧
      ∀ η ∈ Ioo (0 : ℝ) η₁,
        (∀ u : ℝ, u ≤ -2 * R_B → ‖oddShellG ℓ hℓ b η (u : ℂ)‖ ≤ K_L) ∧
        (∀ z ∈ closedBall (0 : ℂ) (2 * R_B + 1), ‖oddShellG ℓ hℓ b η z‖ ≤ M₀) ∧
        (∀ u : ℝ, 2 * R_B ≤ u →
          ‖oddShellG ℓ hℓ b η (u : ℂ)‖ ≤ C_N * (1 + u) ^ (2 * (ℓ : ℝ) + 1 / 2) * airyEnv (u : ℂ)) := by
  let R_B : ℝ := max 2 (max (b + 1) (-airyZero (ℓ + 1) + 1))
  have hRB1 : 1 ≤ R_B := le_trans (by norm_num) (le_max_left _ _)
  obtain ⟨r₀, hr₀, hr₀_half, _, _, hpart⟩ := oddShell_top_zeros_partition hℓ hb
  let δ := r₀ / 2
  obtain ⟨ηp, hηp, hPart_ev⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hpart δ ⟨half_pos hr₀, half_lt_self hr₀⟩)
  obtain ⟨M₀, hM₀, hBall⟩ := oddShellN_unif_ball hℓ b (by positivity : 0 ≤ 2 * R_B + 1)
  obtain ⟨C_N, hCN, hClass⟩ := oddShellN_unif_class hℓ b
  refine ⟨R_B, C_N * 4 ^ (2 * ℓ + 1), M₀, C_N, min ηp 1, hRB1, by positivity, hM₀, hCN,
    lt_min hηp one_pos, min_le_right _ _, fun η hη => ?_⟩
  have hη0 : 0 < η := hη.1; have hη1 : η ∈ Ioo (0 : ℝ) 1 := ⟨hη0, hη.2.trans_le (min_le_right _ _)⟩
  have hPart := (hPart_ev ⟨hη0, hη.2.trans_le (min_le_left _ _)⟩).2.2
  have hS_bd : ∀ t ∈ (oddShellHBData ℓ hℓ b η hη0).S, |t| ≤ R_B := fun t ht => by
    obtain ⟨s, hs, hts⟩ := hPart t (by dsimp [oddShellS]; split_ifs; exact ht)
    have hs_bd : |s| ≤ R_B - 1 := by
      simp only [oddShellSites, Finset.mem_insert, Finset.mem_image, Finset.mem_Icc] at hs
      rcases hs with hsb | ⟨k, hk, rfl⟩
      · have hR1 : b + 1 ≤ R_B := (le_max_left (b + 1) (-airyZero (ℓ + 1) + 1)).trans (le_max_right 2 _)
        rw [hsb, abs_of_pos hb]; linarith
      · have hle := airyZero_le_of_le hk.1 hk.2; rw [abs_of_neg (airyZero_neg k)]
        have hR2 : -airyZero (ℓ + 1) + 1 ≤ R_B := (le_max_right (b + 1) (-airyZero (ℓ + 1) + 1)).trans (le_max_right 2 _)
        linarith
    have htri : |t| ≤ |s| + |t - s| := (by ring_nf : |t| = |s + (t - s)|) ▸ abs_add_le _ _
    have hts_abs : |t - s| < δ := abs_lt.mpr ⟨by linarith [hts.1], by linarith [hts.2]⟩
    linarith [show δ < 1 by dsimp [δ]; linarith]
  let D := oddShellHBData ℓ hℓ b η hη0
  have hGeq : ∀ z : ℂ, oddShellG ℓ hℓ b η z = D.G z := fun z => by dsimp [oddShellG]; split_ifs; rfl
  have hprod_norm : ∀ z : ℂ,
      ‖D.G z‖ * ∏ t ∈ D.S, ‖z - (t : ℂ)‖ = ‖airyPQN (oddShellP ℓ b η) (oddShellQ ℓ b η) z‖ ^ 2 := fun z => by
    have h := congrArg norm (D.G_prod_eq z)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_neg, abs_one, one_pow, one_mul, norm_pow] at h
    unfold at47_pr at h; rwa [norm_prod] at h
  refine ⟨fun u hu => ?_, fun z hz => ?_, fun u hu => ?_⟩
  · set v : ℝ := -u; have hv_ge : 2 * R_B ≤ v := by linarith
    have hv0 : 0 < v := by linarith
    have hden_ge : (v / 2) ^ (2 * ℓ + 1) ≤ ∏ t ∈ D.S, ‖(u : ℂ) - (t : ℂ)‖ := by
      calc (v / 2) ^ (2 * ℓ + 1) = ∏ _t ∈ D.S, (v / 2) := by rw [Finset.prod_const, oddShellHBData_S_card ℓ hℓ b η hη0]
        _ ≤ ∏ t ∈ D.S, ‖(u : ℂ) - (t : ℂ)‖ := Finset.prod_le_prod₀ (fun _ _ => by linarith) fun t ht => by
            rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
            have h1 := abs_sub_abs_le_abs_sub u t; rw [abs_of_neg (by linarith)] at h1; linarith [hS_bd t ht]
    have hden_pos : 0 < ∏ t ∈ D.S, ‖(u : ℂ) - (t : ℂ)‖ := lt_of_lt_of_le (by positivity) hden_ge
    have hC := hClass η hη1 (u : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith), airyEnv_ofReal_neg (by linarith), mul_one] at hC
    have hpow_le : (1 + v) ^ (2 * (ℓ : ℝ) + 1 / 2) ≤ (2 * v) ^ (2 * ℓ + 1) := by
      have h1 : (1 + v) ^ (2 * (ℓ : ℝ) + 1 / 2) ≤ (1 + v) ^ ((2 * ℓ + 1 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
      rw [Real.rpow_natCast] at h1
      exact h1.trans (pow_le_pow_left₀ (by linarith) (by linarith) _)
    rw [hGeq]
    calc ‖D.G (u : ℂ)‖ = ‖airyPQN (oddShellP ℓ b η) (oddShellQ ℓ b η) (u : ℂ)‖ ^ 2 /
          ∏ t ∈ D.S, ‖(u : ℂ) - (t : ℂ)‖ := eq_div_of_mul_eq hden_pos.ne' (hprod_norm _)
      _ ≤ (C_N * (2 * v) ^ (2 * ℓ + 1)) / (v / 2) ^ (2 * ℓ + 1) :=
          div_le_div₀ (by positivity) (hC.trans (mul_le_mul_of_nonneg_left hpow_le hCN)) (by positivity) hden_ge
      _ = C_N * 4 ^ (2 * ℓ + 1) := by
        have h4 : ((2 : ℝ) ^ (2 * ℓ + 1)) ^ 2 = 4 ^ (2 * ℓ + 1) := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        rw [mul_pow, div_pow]; field_simp; rw [h4]
  · have hRad : 2 * R_B + 1 ≠ 0 := by linarith
    rw [hGeq]
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball D.G_diff.diffContOnCl
      (fun w hw => ?_) (by rw [closure_ball (0 : ℂ) hRad]; exact hz)
    rw [frontier_ball (0 : ℂ) hRad, mem_sphere_zero_iff_norm] at hw
    have hden_ge : 1 ≤ ∏ t ∈ D.S, ‖w - (t : ℂ)‖ := (by simp : (1 : ℝ) = ∏ _t ∈ D.S, (1 : ℝ)) ▸
      Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun t ht => by
        have := norm_sub_norm_le w (t : ℂ); rw [Complex.norm_real, Real.norm_eq_abs] at this; linarith [hS_bd t ht]
    calc ‖D.G w‖ ≤ ‖D.G w‖ * ∏ t ∈ D.S, ‖w - (t : ℂ)‖ := le_mul_of_one_le_right (norm_nonneg _) hden_ge
      _ = ‖airyPQN (oddShellP ℓ b η) (oddShellQ ℓ b η) w‖ ^ 2 := hprod_norm w
      _ ≤ M₀ := hBall η hη1 w (mem_closedBall_zero_iff.mpr hw.le)
  · have hden_ge : 1 ≤ ∏ t ∈ D.S, ‖(u : ℂ) - (t : ℂ)‖ := (by simp : (1 : ℝ) = ∏ _t ∈ D.S, (1 : ℝ)) ▸
      Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun t ht => by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        have := abs_sub_abs_le_abs_sub u t; rw [abs_of_nonneg (by linarith)] at this; linarith [hS_bd t ht]
    have hC := hClass η hη1 (u : ℂ); rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at hC
    rw [hGeq]
    calc ‖D.G (u : ℂ)‖ ≤ ‖D.G (u : ℂ)‖ * ∏ t ∈ D.S, ‖(u : ℂ) - (t : ℂ)‖ := le_mul_of_one_le_right (norm_nonneg _) hden_ge
      _ = ‖airyPQN (oddShellP ℓ b η) (oddShellQ ℓ b η) (u : ℂ)‖ ^ 2 := hprod_norm _
      _ ≤ C_N * (1 + u) ^ (2 * (ℓ : ℝ) + 1 / 2) * airyEnv (u : ℂ) := hC

theorem oddShell_laplace_tendsto {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {b : ℝ} (hb : 0 < b) {y : ℝ} (hy : 0 < y) :
    Tendsto (fun η => airyLaplace (fun u => (oddShellG ℓ hℓ b η (u : ℂ)).re) y) (𝓝[>] 0)
      (𝓝 (airyLaplace (fun u => (b - u) * oddShellH ℓ u) y)) := by
  obtain ⟨R_B, K_L, M₀, C_N, η₁, hRB1, hKL, hM₀, hCN, hη₁, _, hbd⟩ := oddShellG_unif_bound hℓ hb
  let bound : ℝ → ℝ := fun u =>
    if u < -2 * R_B then K_L * Real.exp (y * u)
    else if u ≤ 2 * R_B then M₀ * Real.exp (y * (2 * R_B))
    else C_N * (1 + u) ^ (2 * (ℓ : ℝ) + 1 / 2) * airyEnv (u : ℂ) * Real.exp (y * u)
  have hbi1 : IntegrableOn bound (Iio (-2 * R_B)) := by
    have hexp : IntegrableOn (fun v : ℝ => K_L * Real.exp (-y * v)) (Ioi (2 * R_B)) :=
      (integrableOn_exp_mul_Ioi (by linarith : -y < 0) (2 * R_B)).const_mul K_L
    have hmp := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (MeasurableEquiv.neg ℝ).measurableEmbedding (f := fun v : ℝ => K_L * Real.exp (-y * v)) (s := Ioi (2 * R_B))
    have e : (fun u : ℝ => -u) ⁻¹' Ioi (2 * R_B) = Iio (-2 * R_B) := by ext u; simp
    have h_neg : IntegrableOn (fun u : ℝ => K_L * Real.exp (y * u)) (Iio (-2 * R_B)) := by
      rw [e] at hmp; simpa [Function.comp_def, mul_neg, neg_mul] using hmp.mpr hexp
    exact h_neg.congr_fun (fun u hu => by
      dsimp [bound]; rw [ite_eq_left_of_eq_true _ _ (eq_true (mem_Iio.mp hu))]) measurableSet_Iio
  have hbi2 : IntegrableOn bound (Icc (-2 * R_B) (2 * R_B)) :=
    IntegrableOn.congr_fun continuousOn_const.integrableOn_Icc
      (fun u hu => by
        dsimp only [bound]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (not_lt.mpr hu.1)),
          ite_eq_left_of_eq_true _ _ (eq_true hu.2)])
      measurableSet_Icc
  have hbi3 : IntegrableOn bound (Ioi (2 * R_B)) :=
    ((integrableOn_airy_exp_Ioi hCN).mono_set (Ioi_subset_Ioi (by linarith))).congr_fun
      (fun u hu => by
        have hgt := mem_Ioi.mp hu
        have h1 : ¬ u < -2 * R_B := by linarith
        have h2 : ¬ u ≤ 2 * R_B := by linarith
        dsimp [bound]; rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2)])
      measurableSet_Ioi
  have hbfull : Integrable bound := by
    rw [← integrableOn_univ, show (univ : Set ℝ) = Iio (-2 * R_B) ∪ Icc (-2 * R_B) (2 * R_B) ∪ Ioi (2 * R_B) by
      ext u; simp only [mem_univ, mem_union, mem_Iio, mem_Icc, mem_Ioi, true_iff]
      by_cases h1 : u < -2 * R_B; exact Or.inl (Or.inl h1)
      · by_cases h2 : u ≤ 2 * R_B; exact Or.inl (Or.inr ⟨by linarith, h2⟩); exact Or.inr (by linarith)]
    exact (hbi1.union hbi2).union hbi3
  have hIoo : ∀ᶠ η : ℝ in 𝓝[>] 0, η ∈ Ioo (0 : ℝ) η₁ := Ioo_mem_nhdsGT hη₁
  have hmeas : ∀ᶠ η : ℝ in 𝓝[>] 0,
      AEStronglyMeasurable (fun u : ℝ => (oddShellG ℓ hℓ b η (u : ℂ)).re * Real.exp (y * u)) volume :=
    hIoo.mono fun η hη => by
      have hG : (fun u : ℝ => (oddShellG ℓ hℓ b η (u : ℂ)).re * Real.exp (y * u)) =
          fun u : ℝ => ((oddShellHBData ℓ hℓ b η hη.1).G (u : ℂ)).re * Real.exp (y * u) := by ext u; simp [oddShellG, hη.1]
      rw [hG]; exact (Complex.continuous_re.comp
        ((oddShellHBData ℓ hℓ b η hη.1).G_diff.continuous.comp Complex.continuous_ofReal) |>.mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  have hdom : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ᵐ u : ℝ ∂volume,
      ‖(oddShellG ℓ hℓ b η (u : ℂ)).re * Real.exp (y * u)‖ ≤ bound u :=
    hIoo.mono fun η hη => Eventually.of_forall fun u => by
      obtain ⟨hL, hM, hR⟩ := hbd η hη
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hre : |(oddShellG ℓ hℓ b η (u : ℂ)).re| ≤ ‖oddShellG ℓ hℓ b η (u : ℂ)‖ := Complex.abs_re_le_norm _
      dsimp [bound]; split_ifs with h1 h2
      · exact mul_le_mul_of_nonneg_right (hre.trans (hL u h1.le)) (Real.exp_pos _).le
      · have hum : (u : ℂ) ∈ closedBall (0 : ℂ) (2 * R_B + 1) := by
          rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith
        exact mul_le_mul (hre.trans (hM _ hum)) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h2 hy.le)) (Real.exp_pos _).le hM₀
      · push Not at h2
        calc |(oddShellG ℓ hℓ b η (u : ℂ)).re| * Real.exp (y * u)
            ≤ (C_N * (1 + u) ^ (2 * (ℓ : ℝ) + 1 / 2) * airyEnv (u : ℂ)) * Real.exp (y * u) :=
              mul_le_mul_of_nonneg_right (hre.trans (hR u h2.le)) (Real.exp_pos _).le
          _ = _ := by ring
  have hlim : ∀ᵐ u : ℝ ∂volume,
      Tendsto (fun η => (oddShellG ℓ hℓ b η (u : ℂ)).re * Real.exp (y * u)) (𝓝[>] 0)
        (𝓝 (((b - u) * oddShellH ℓ u) * Real.exp (y * u))) := by
    filter_upwards [(oddShellSites ℓ b).finite_toSet.countable.ae_notMem volume] with u hu
    have hGt : Tendsto (fun η => (oddShellG ℓ hℓ b η (u : ℂ)).re) (𝓝[>] 0)
        (𝓝 ((((b : ℂ) - (u : ℂ)) * oddShellHC ℓ (u : ℂ)).re)) :=
      Complex.continuous_re.continuousAt.tendsto.comp
        (oddShell_G_tendsto_off hℓ hb (z := (u : ℂ)) fun s hs h =>
          hu (by rw [Complex.ofReal_injective h]; exact hs))
    have hre : ((((b : ℂ) - (u : ℂ)) * oddShellHC ℓ (u : ℂ))).re = (b - u) * oddShellH ℓ u := by
      have h_eq : ((b : ℂ) - (u : ℂ)) * oddShellHC ℓ (u : ℂ) = (((b - u : ℝ) : ℂ) * oddShellHC ℓ (u : ℂ)) := by push_cast; rfl
      rw [h_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]; rfl
    rw [hre] at hGt; exact hGt.mul_const _
  exact (tendsto_integral_filter_of_dominated_convergence bound hmeas hdom hbfull hlim).const_mul _

/-! ### Section 5: Proof of Corollary `H.14a` (`thm:ce-odd-family`) -/

private lemma oddShellH_laplace_pos_large {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    ∃ y : ℝ, 0 < y ∧ 0 < ∫ u : ℝ, oddShellH ℓ u * Real.exp (y * u) := by
  have hAiC := oddShellHC_inAiryClass hℓ
  have hnn : ∀ u : ℝ, airyZero 1 ≤ u → 0 ≤ oddShellH ℓ u := fun u hu => by
    rw [oddShellH_eq_div hℓ u]; rcases hu.eq_or_lt with rfl | hgt
    · rw [sub_self, zero_mul, div_zero]
    · have := airyZero_lt_of_lt le_rfl (by omega : 1 < ℓ + 1)
      exact div_nonneg (sq_nonneg _) (mul_pos_of_neg_of_neg (by linarith) (by linarith)).le
  have hpos0 : 0 < oddShellH ℓ 0 := by
    rw [oddShellH_eq_div hℓ 0]
    exact div_pos (sq_pos_of_ne_zero (airyAi_pos le_rfl).ne')
      (mul_pos_of_neg_of_neg (by linarith [airyZero_neg 1]) (by linarith [airyZero_neg (ℓ + 1)]))
  obtain ⟨Y, hY, hpos⟩ := laplace_pos_eventually_of_nonneg_tail
    hAiC.to_polyLeftAiryRightBound.1 hAiC.2.1.re
    (fun y hy => hAiC.integrable_exp_nonneg hy) (airyZero_neg 1) hnn hpos0
  exact ⟨Y, hY, hpos Y le_rfl⟩

/-- **Corollary `H.14a` (`thm:ce-odd-family`, explicit `oddShellHBData` form)**:
for every `ℓ ≥ 1`, there exist `b, η, y > 0` such that `(oddShellP ℓ b η, oddShellQ ℓ b η)` gives
strict `ShellHBData` with `2 * ℓ + 1` nodes and `airyLaplace (-D.G) y < 0`. -/
theorem odd_shell_family_laplace_gap (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ b > (0 : ℝ), ∃ (η : ℝ) (hη : 0 < η), ∃ y > (0 : ℝ),
      airyLaplace (fun u => -((oddShellHBData ℓ hℓ b η hη).G (u : ℂ)).re) y < 0 := by
  obtain ⟨y, hy, hI0⟩ := oddShellH_laplace_pos_large hℓ
  let I₀ : ℝ := ∫ u : ℝ, oddShellH ℓ u * Real.exp (y * u)
  let I₁ : ℝ := ∫ u : ℝ, (u * oddShellH ℓ u) * Real.exp (y * u)
  let b : ℝ := max 1 ((I₁ + 1) / I₀); have hb : 0 < b := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hcomb_pos : 0 < airyLaplace (fun u => (b - u) * oddShellH ℓ u) y := by
    have hA := (oddShellHC_inAiryClass hℓ).to_polyLeftAiryRightBound
    have hint0 : Integrable (fun u : ℝ => oddShellH ℓ u * Real.exp (y * u)) := hA.integrable_exp hy
    have hint1 : Integrable (fun u : ℝ => (u * oddShellH ℓ u) * Real.exp (y * u)) := hA.mul_id.integrable_exp hy
    have heq : (fun u : ℝ => ((b - u) * oddShellH ℓ u) * Real.exp (y * u)) =
        (fun u : ℝ => b * (oddShellH ℓ u * Real.exp (y * u)) - (u * oddShellH ℓ u) * Real.exp (y * u)) := funext fun u => by ring
    unfold airyLaplace; rw [heq, integral_sub (hint0.const_mul b) hint1, integral_const_mul]
    have hmul : I₁ + 1 ≤ b * I₀ := (div_le_iff₀ hI0).mp (le_max_right _ _)
    exact mul_pos (Real.exp_pos _) (by dsimp [I₀, I₁] at hmul ⊢; linarith)
  have hlim := (oddShell_laplace_tendsto hℓ hb hy).eventually (lt_mem_nhds hcomb_pos)
  obtain ⟨η₀, hη₀, hη_bd⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hlim
  refine ⟨b, hb, η₀ / 2, half_pos hη₀, y, hy, ?_⟩
  have hpos : 0 < airyLaplace (fun u => (oddShellG ℓ hℓ b (η₀ / 2) (u : ℂ)).re) y :=
    hη_bd ⟨half_pos hη₀, half_lt_self hη₀⟩
  have hG_eq : (fun u : ℝ => (oddShellG ℓ hℓ b (η₀ / 2) (u : ℂ)).re) =
      fun u : ℝ => ((oddShellHBData ℓ hℓ b (η₀ / 2) (half_pos hη₀)).G (u : ℂ)).re := by
    ext u; dsimp [oddShellG]; split_ifs with h; rfl; exact absurd (half_pos hη₀) h
  rw [hG_eq] at hpos
  have hneg : airyLaplace (fun u => -((oddShellHBData ℓ hℓ b (η₀ / 2) (half_pos hη₀)).G (u : ℂ)).re) y =
      -airyLaplace (fun u => ((oddShellHBData ℓ hℓ b (η₀ / 2) (half_pos hη₀)).G (u : ℂ)).re) y := by
    unfold airyLaplace; simp_rw [neg_mul]; rw [integral_neg, mul_neg]
  linarith

/-- **Corollary `H.14a` (`thm:ce-odd-family`, existential `ShellHBData` form)**:
for every odd `m ≥ 3`, there exist strict Hermite–Biehler data `D : ShellHBData` (`D.Q ≠ 0`) with
`D.S.card = m` and `y > 0` satisfying `airyLaplace (-D.G) y < 0`. -/
theorem ce_odd_family_laplace_gap {m : ℕ} (hm : 3 ≤ m) (hodd : Odd m) :
    ∃ (D : ShellHBData) (y : ℝ), 0 < y ∧ D.Q ≠ 0 ∧ D.S.card = m ∧
      airyLaplace (fun u => -(D.G (u : ℂ)).re) y < 0 := by
  obtain ⟨ℓ, rfl⟩ := hodd
  obtain ⟨b, -, η, hη, y, hy, hgap⟩ := odd_shell_family_laplace_gap ℓ (by omega)
  exact ⟨oddShellHBData ℓ (by omega) b η hη, y, hy,
    oddShellHBData_Q_ne_zero ℓ (by omega) b η hη,
    oddShellHBData_S_card ℓ (by omega) b η hη, hgap⟩

/-- info: 'FormalResearch.SignUncertainty.oddShell_airypqhb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms oddShell_airypqhb

/-- info: 'FormalResearch.SignUncertainty.oddShellP_natDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms oddShellP_natDegree

/-- info: 'FormalResearch.SignUncertainty.oddShellQ_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms oddShellQ_ne_zero

/-- info: 'FormalResearch.SignUncertainty.oddShellQ_natDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms oddShellQ_natDegree

/-- info: 'FormalResearch.SignUncertainty.oddShell_at47_m' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms oddShell_at47_m

/-- info: 'FormalResearch.SignUncertainty.oddShell_tendstoLocallyUniformly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms oddShell_tendstoLocallyUniformly

/-- info: 'FormalResearch.SignUncertainty.oddShell_prod_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms oddShell_prod_tendsto

/-- info: 'FormalResearch.SignUncertainty.oddShellHC_inAiryClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms oddShellHC_inAiryClass

/-- info: 'FormalResearch.SignUncertainty.oddShell_laplace_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms oddShell_laplace_tendsto

/-- info: 'FormalResearch.SignUncertainty.odd_shell_family_laplace_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms odd_shell_family_laplace_gap

/-- info: 'FormalResearch.SignUncertainty.ce_odd_family_laplace_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_odd_family_laplace_gap

end FormalResearch.SignUncertainty
