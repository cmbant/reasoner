module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.ThmAAssemblyRel
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftW2Proved
public import FormalResearch.JacobiEigenvectors.TheoremA.NegTransport
public import FormalResearch.JacobiEigenvectors.TheoremB.NegColumns

/-!
# Paper J, Layer 2: the soft cases of the `ThmAii` assembly and `ThmAii` from `PropThaW`, `PropThaW2` (L2.C9)

Source: Paper J `thmA.tex`, proof of `thm:A (ii)` ("the three cases of `def:tha-Psihat`") and "The relative statement" (soft case: `T <= -eps` puts `n` off the window `Omega`, where prop:tha-W2 (2) gives `V_n/hat N <= C |hat Psi_n|`).

## Proved here (axiom-pinned)

* `softUpper_data`, `aiiAbs_upper`, `relUpper`: the upper soft window (eigenvalue `X_k > J_hi`, `|X_k - X_s^+| <= delta_0`): `propThaW2_proved` at `Cs0` of `stepZero` (the Step 0 premise), applied to the frozen family at `(mu, h)`
  (`frozenFamily_jacobiMat_at_step`); gives both the absolute clause (items (2), sum) and the off-window clause (R2).
* `softLower_data`, `aiiAbs_lower`, `relLower`: the lower window through the gauge transport (`NegTransport`: `IsEigenSystem.neg_frozen`, `eigVec_negU_rev`, `negFrozen_bandHi`, `TheoremB.stdAssump_neg`): `propThaW2_proved` for
  `negFamily (frozenFamily F Kidx)` at the energy `-X_k`, Step 0 premise from the *lower* bound of `stepZero`; the sign `(-1)^n` is an isometry (`abs_sub_sign`).
* `aiiAbs_bulk` (with `bulk_block_data`): the bulk absolute clause from the eigenvector clause of `PropThaW` of every block, `BulkEnvSum`, and `bulkEnv_nonneg_rows`; constants combined over the blocks by sums and `Finite.exists_min`.
* `envVec_nonneg`: `0 <= envVec` on the rows for small `h`, at every energy (the premise `hnn` of `thmAii_of_cases`).
* `thmAii_of_propThaW`: **`ThmAii` (both clauses) from the three cases**, `spectrumCovered` (proved) and `thmAii_bulk_relative`, under the named premises below.

## Premises that are not consequences of the frozen statements

* `hW : forall nu, PropThaW ..` (the frozen statement, taken as a premise for every block) and `hstdM`, `hstdK` (`StdAssump` of the frozen family on `paramSet K t0` at indices `m/2`, `Kidx`; finding F-t0: true for small `t0` only).
* `BulkEnvSum` (**F-BB-4**): the conjunct `sum_n bulkEnv^2 <= C` missing from `PropThaW`.
* `SoftWindowT` (**F-BB-5**): `T(u_n; X) <= -eps` puts `n` off the soft window `Omega` for small `h` (the allowed-region function has a simple zero at the turning point and the window is the well plus an Airy layer of width `O(sqrt h)`).
  This is the one geometric input of the soft relative clause that no frozen statement contains; it is the analogue of `bulk_relative_collar` for the soft charts and is **not formalised**.

## Differences from the paper

* The paper's `Cs0` of Step 0 is `stepZero`'s `C` (a parameter of `PropThaW2` since F-W2-12).  `Lm = 1` for the charts of `ChartInputs`.
* `0 < t0` is not used.

## Not formalised

`SoftWindowT`, `BulkEnvSum`; the discharge of `hW`, `hstdM`, `hstdK` from the chart data.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

variable {Par : Type*} [TopologicalSpace Par]

/-- `|e - (-1)^n s| = |(-1)^n e - s|` (the gauge `D = ((-1)^n)` is an isometry). -/
lemma abs_sub_sign (n : ℤ) (e s : ℝ) : |e - (-1 : ℝ) ^ n * s| = |(-1 : ℝ) ^ n * e - s| := by
  have h : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← zpow_add₀ (by norm_num), ← two_mul, zpow_mul]; norm_num
  have h2 : e - (-1 : ℝ) ^ n * s = (-1 : ℝ) ^ n * ((-1 : ℝ) ^ n * e - s) := by
    linear_combination (-e) * h
  have h3 : |(-1 : ℝ) ^ n| = 1 := by simp
  rw [h2, abs_mul, h3, one_mul]

lemma abs_sign_mul (n : ℤ) (s : ℝ) : |(-1 : ℝ) ^ n * s| = |s| := by
  have h3 : |(-1 : ℝ) ^ n| = 1 := by simp
  rw [abs_mul, h3, one_mul]

lemma two_mul_div_two_nat (Kidx : ℕ) : 2 * Kidx / 2 = Kidx := Nat.mul_div_cancel_left Kidx (by norm_num)

section Soft

variable {F : SymbolFamily Par} {K : Set Par} {m Kidx : ℕ} {t0 : ℝ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- **Upper soft window, absolute clause** (`ThmAii` case 2): `propThaW2_proved` (items (2), (3.sum)) at `Cs0` of `stepZero`, for the frozen family at `t = h`. -/
theorem softUpper_data (CI : ChartInputs F K Kidx t0 m (2 * Kidx) U V cPC CPC) (hm : 1 ≤ m)
    (hstdK : ∃ r, StdAssump (frozenFamily F Kidx) (paramSet K t0) Kidx r) :
    ∃ C hm Cs0 : ℝ, 0 < hm ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hm → F.step N ≤ t0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), (¬ ∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν) → CI.Jhi < X k →
          |X k - (frozenFamily F Kidx).bandHi (atStep F μ N)| ≤ CI.softUpL.δ0 → (AiiAbs CI C μ N X Um k ∧
            ∀ n ∈ rowsOf N, n ∉ softWindow CI.softUpL (atStep F μ N) (X k) N → envVec CI μ N (X k) n ≤ C * |psiHatVec CI μ N (X k) n|) ∧
          X k ≤ (frozenFamily F Kidx).bandHi (atStep F μ N) + Cs0 * F.step N ^ 2 := by
  obtain ⟨r, hr⟩ := hstdK
  obtain ⟨Cs, hs0, hs0p, hsp⟩ := stepZero (frozenFamily F Kidx) (paramSet K t0) Kidx r hr
  have hr2 : StdAssump (frozenFamily F Kidx) (paramSet K t0) (2 * Kidx / 2) r := by rw [two_mul_div_two_nat]; exact hr
  obtain ⟨Cc, h0, clam, Clam, hh0, hclam, H⟩ :=
    propThaW2_proved CI.softUpL CI.softUpR Cs cPC CPC CI.pc hm (fun h _ _ => le_rfl) CI.mirror_up r hr2
  set n0 : ℕ := max CI.softUpL.N0 CI.softUpR.N0 with hn0
  refine ⟨Cc, min (min h0 hs0) (F.L / ((n0 : ℝ) + 1)), Cs, lt_min (lt_min hh0 hs0p) (div_pos F.L_pos (by positivity)), ?_⟩
  intro μ hμ N hN hNt X Um hE k hk hJ hwin
  have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hN1 : F.step N ≤ h0 := hN.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hN2 : F.step N ≤ hs0 := hN.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hN3 : F.step N ≤ F.L / ((n0 : ℝ) + 1) := hN.trans (min_le_right _ _)
  have hn0N : n0 ≤ N := le_of_step_le hN3
  have hp : (μ, F.step N) ∈ paramSet K t0 := ⟨hμ, ⟨by linarith, hNt⟩⟩
  have hEf : IsEigenSystem ((frozenFamily F Kidx).jacobiMat (μ, F.step N) N) X Um := by
    rw [frozenFamily_jacobiMat_at_step]; exact hE
  have hS0 : ∀ i, X i ≤ (frozenFamily F Kidx).bandHi (μ, F.step N) + Cs * (frozenFamily F Kidx).step N ^ 2 :=
    fun i => (hsp (μ, F.step N) hp N hN2 X Um hEf i).2
  obtain ⟨hA, -, -⟩ := H (μ, F.step N) hp N hn0N hN1
  obtain ⟨-, -, -, hEc⟩ := hA (X k) hwin
  obtain ⟨h1, h2, h3⟩ := hEc X Um hEf hS0 k rfl
  have e1 : ∀ n, psiHatVec CI μ N (X k) n = softVec CI.softUpL CI.softUpR (atStep F μ N) (X k) N n := by
    intro n; unfold psiHatVec; rw [dite_eq_right hk, ite_eq_left hJ]
  have e2 : ∀ n, envVec CI μ N (X k) n = softEnv CI.softUpL CI.softUpR (atStep F μ N) (X k) N n := by
    intro n; unfold envVec; rw [dite_eq_right hk, ite_eq_left hJ]
  refine ⟨⟨⟨fun n hn => ?_, ?_⟩, fun n hn hnw => ?_⟩, ?_⟩
  · rw [e1, e2]
    have := h1 n hn
    simp only [mul_one] at this
    exact this
  · have h2' : ∑ n ∈ rowsOf N, softEnv CI.softUpL CI.softUpR (atStep F μ N) (X k) N n ^ 2 ≤ Cc := h2
    simpa only [e2] using h2'
  · rw [e1, e2]; exact h3 n hn hnw
  · exact hS0 k

/-- **Lower soft window, absolute clause** (`ThmAii` case 3): the gauge transport `NegTransport` (`IsEigenSystem.neg_frozen`, `eigVec_negU_rev`) reduces it to `propThaW2_proved` for the chart family
`negFamily (frozenFamily F Kidx)` at the energy `-X_k`, whose Step 0 premise is the *lower* bound of `stepZero`. -/
theorem softLower_data (CI : ChartInputs F K Kidx t0 m (2 * Kidx) U V cPC CPC) (hm : 1 ≤ m)
    (hstdK : ∃ r, StdAssump (frozenFamily F Kidx) (paramSet K t0) Kidx r) :
    ∃ C hm Cs0 : ℝ, 0 < hm ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hm → F.step N ≤ t0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), (¬ ∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν) → ¬ CI.Jhi < X k →
          |-X k - (negFamily (frozenFamily F Kidx)).bandHi (atStep F μ N)| ≤ CI.softLoL.δ0 → (AiiAbs CI C μ N X Um k ∧
            ∀ n ∈ rowsOf N, n ∉ softWindow CI.softLoL (atStep F μ N) (-X k) N → envVec CI μ N (X k) n ≤ C * |psiHatVec CI μ N (X k) n|) ∧
          -X k ≤ (negFamily (frozenFamily F Kidx)).bandHi (atStep F μ N) + Cs0 * F.step N ^ 2 := by
  obtain ⟨r, hr⟩ := hstdK
  obtain ⟨Cs, hs0, hs0p, hsp⟩ := stepZero (frozenFamily F Kidx) (paramSet K t0) Kidx r hr
  have hrn : StdAssump (negFamily (frozenFamily F Kidx)) (paramSet K t0) (2 * Kidx / 2) r := by
    rw [two_mul_div_two_nat]; exact TheoremB.stdAssump_neg hr
  obtain ⟨Cc, h0, clam, Clam, hh0, hclam, H⟩ :=
    propThaW2_proved CI.softLoL CI.softLoR Cs cPC CPC CI.pc hm (fun h _ _ => le_rfl) CI.mirror_lo r hrn
  set n0 : ℕ := max CI.softLoL.N0 CI.softLoR.N0 with hn0
  refine ⟨Cc, min (min h0 hs0) (F.L / ((n0 : ℝ) + 1)), Cs, lt_min (lt_min hh0 hs0p) (div_pos F.L_pos (by positivity)), ?_⟩
  intro μ hμ N hN hNt X Um hE k hk hJ hwin
  have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hN1 : F.step N ≤ h0 := hN.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hN2 : F.step N ≤ hs0 := hN.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hN3 : F.step N ≤ F.L / ((n0 : ℝ) + 1) := hN.trans (min_le_right _ _)
  have hn0N : n0 ≤ N := le_of_step_le hN3
  have hp : (μ, F.step N) ∈ paramSet K t0 := ⟨hμ, ⟨by linarith, hNt⟩⟩
  have hEf : IsEigenSystem ((frozenFamily F Kidx).jacobiMat (μ, F.step N) N) X Um := by
    rw [frozenFamily_jacobiMat_at_step]; exact hE
  have hEn : IsEigenSystem ((negFamily (frozenFamily F Kidx)).jacobiMat (μ, F.step N) N) (negX X) (negU Um) :=
    hE.neg_frozen (Kidx := Kidx)
  have hstep : (negFamily (frozenFamily F Kidx)).step N = F.step N := rfl
  have hS0 : ∀ i, negX X i ≤ (negFamily (frozenFamily F Kidx)).bandHi (μ, F.step N) +
      Cs * (negFamily (frozenFamily F Kidx)).step N ^ 2 := by
    intro i
    have h := (hsp (μ, F.step N) hp N hN2 X Um hEf (Fin.rev i)).1
    have h' : (frozenFamily F Kidx).step N = F.step N := rfl
    rw [h'] at h
    rw [hstep, negFrozen_bandHi]
    simp only [negX]
    linarith
  obtain ⟨hA, -, -⟩ := H (μ, F.step N) hp N hn0N hN1
  obtain ⟨-, -, -, hEc⟩ := hA (-X k) hwin
  obtain ⟨h1, h2, h3⟩ := hEc (negX X) (negU Um) hEn hS0 (Fin.rev k) (negX_rev X k)
  have e1 : ∀ n, psiHatVec CI μ N (X k) n =
      (-1 : ℝ) ^ n * softVec CI.softLoL CI.softLoR (atStep F μ N) (-X k) N n := by
    intro n; unfold psiHatVec; rw [dite_eq_right hk, ite_eq_right hJ]
  have e2 : ∀ n, envVec CI μ N (X k) n = softEnv CI.softLoL CI.softLoR (atStep F μ N) (-X k) N n := by
    intro n; unfold envVec; rw [dite_eq_right hk, ite_eq_right hJ]
  refine ⟨⟨⟨fun n hn => ?_, ?_⟩, fun n hn hnw => ?_⟩, ?_⟩
  · rw [e1, e2, abs_sub_sign]
    have := h1 n hn
    rw [eigVec_negU_rev] at this
    simp only [mul_one] at this
    exact this
  · have h2' : ∑ n ∈ rowsOf N, softEnv CI.softLoL CI.softLoR (atStep F μ N) (-X k) N n ^ 2 ≤ Cc := h2
    simpa only [e2] using h2'
  · rw [e1, e2, abs_sign_mul]; exact h3 n hn hnw
  · have := hS0 (Fin.rev k)
    rw [negX_rev] at this
    exact this

/-- **The soft relative window lemma** (named premise, *not formalised*; finding F-BB-5): at a site `n` of the soft window `Omega = {|Z_n| <= rho(a)}` the allowed-region function satisfies
`T(u_n; X) >= -eps` for small `h`: the window is the classically allowed well plus an Airy layer of width `O(sqrt h)` in `u`, and `T` has a simple zero at the turning points (`HypMorse`).  In the contrapositive form used by
`ThmAii` R1: `T(u_n; X) <= -eps` puts `n` off the window.  (Upper window at `X`; lower window at `-X` for the gauge family.) -/
def SoftWindowT {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}
    (CI : ChartInputs F K Kidx t0 m (2 * Kidx) U V cPC CPC) : Prop :=
  (∀ Cs0 ε : ℝ, 0 < ε → ∃ h1 : ℝ, 0 < h1 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h1 → F.step N ≤ t0 → ∀ X : ℝ,
      |X - (frozenFamily F Kidx).bandHi (atStep F μ N)| ≤ CI.softUpL.δ0 →
      X ≤ (frozenFamily F Kidx).bandHi (atStep F μ N) + Cs0 * F.step N ^ 2 → ∀ n ∈ rowsOf N,
      Tfun F.L (F.G 0 μ) (F.B 0 μ) X (uNode (F.step N) n) ≤ -ε → n ∉ softWindow CI.softUpL (atStep F μ N) X N) ∧
  (∀ Cs0 ε : ℝ, 0 < ε → ∃ h1 : ℝ, 0 < h1 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h1 → F.step N ≤ t0 → ∀ X : ℝ,
      |-X - (negFamily (frozenFamily F Kidx)).bandHi (atStep F μ N)| ≤ CI.softLoL.δ0 →
      -X ≤ (negFamily (frozenFamily F Kidx)).bandHi (atStep F μ N) + Cs0 * F.step N ^ 2 → ∀ n ∈ rowsOf N,
      Tfun F.L (F.G 0 μ) (F.B 0 μ) X (uNode (F.step N) n) ≤ -ε → n ∉ softWindow CI.softLoL (atStep F μ N) (-X) N)

theorem aiiAbs_upper (CI : ChartInputs F K Kidx t0 m (2 * Kidx) U V cPC CPC) (hm : 1 ≤ m)
    (hstdK : ∃ r, StdAssump (frozenFamily F Kidx) (paramSet K t0) Kidx r) :
    ∃ C hm : ℝ, 0 < hm ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hm → F.step N ≤ t0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), (¬ ∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν) → CI.Jhi < X k →
          |X k - (frozenFamily F Kidx).bandHi (atStep F μ N)| ≤ CI.softUpL.δ0 → AiiAbs CI C μ N X Um k := by
  obtain ⟨C, h, Cs0, hp, H⟩ := softUpper_data CI hm hstdK
  exact ⟨C, h, hp, fun μ hμ N hN hNt X Um hE k hk hJ hw => (H μ hμ N hN hNt X Um hE k hk hJ hw).1.1⟩

theorem aiiAbs_lower (CI : ChartInputs F K Kidx t0 m (2 * Kidx) U V cPC CPC) (hm : 1 ≤ m)
    (hstdK : ∃ r, StdAssump (frozenFamily F Kidx) (paramSet K t0) Kidx r) :
    ∃ C hm : ℝ, 0 < hm ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hm → F.step N ≤ t0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), (¬ ∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν) → ¬ CI.Jhi < X k →
          |-X k - (negFamily (frozenFamily F Kidx)).bandHi (atStep F μ N)| ≤ CI.softLoL.δ0 → AiiAbs CI C μ N X Um k := by
  obtain ⟨C, h, Cs0, hp, H⟩ := softLower_data CI hm hstdK
  exact ⟨C, h, hp, fun μ hμ N hN hNt X Um hE k hk hJ hw => (H μ hμ N hN hNt X Um hE k hk hJ hw).1.1⟩

/-- **`ThmAii` R1, upper soft case**: `T <= -eps` puts `n` off the window (`SoftWindowT`), where `propThaW2_proved` (item (2), off-window clause R2) gives `V_n/hat N <= C |hat Psi_n|`. -/
theorem relUpper (CI : ChartInputs F K Kidx t0 m (2 * Kidx) U V cPC CPC) (hm : 1 ≤ m)
    (hstdK : ∃ r, StdAssump (frozenFamily F Kidx) (paramSet K t0) Kidx r) (hT : SoftWindowT CI) :
    ∀ ε : ℝ, 0 < ε → ∃ Cε hε : ℝ, 0 < hε ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hε → F.step N ≤ t0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), (¬ ∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν) → CI.Jhi < X k →
          |X k - (frozenFamily F Kidx).bandHi (atStep F μ N)| ≤ CI.softUpL.δ0 → ∀ n ∈ rowsOf N,
          Tfun F.L (F.G 0 μ) (F.B 0 μ) (X k) (uNode (F.step N) n) ≤ -ε → envVec CI μ N (X k) n ≤ Cε * |psiHatVec CI μ N (X k) n| := by
  intro ε hε
  obtain ⟨C, h, Cs0, hp, H⟩ := softUpper_data CI hm hstdK
  obtain ⟨h1, h1p, HT⟩ := hT.1 Cs0 ε hε
  refine ⟨C, min h h1, lt_min hp h1p, fun μ hμ N hN hNt X Um hE k hk hJ hw n hn hTn => ?_⟩
  have H' := H μ hμ N (hN.trans (min_le_left _ _)) hNt X Um hE k hk hJ hw
  exact H'.1.2 n hn (HT μ hμ N (hN.trans (min_le_right _ _)) hNt (X k) hw H'.2 n hn hTn)

/-- **`ThmAii` R1, lower soft case** (through the gauge transport; `SoftWindowT`, second clause). -/
theorem relLower (CI : ChartInputs F K Kidx t0 m (2 * Kidx) U V cPC CPC) (hm : 1 ≤ m)
    (hstdK : ∃ r, StdAssump (frozenFamily F Kidx) (paramSet K t0) Kidx r) (hT : SoftWindowT CI) :
    ∀ ε : ℝ, 0 < ε → ∃ Cε hε : ℝ, 0 < hε ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hε → F.step N ≤ t0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), (¬ ∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν) → ¬ CI.Jhi < X k →
          |-X k - (negFamily (frozenFamily F Kidx)).bandHi (atStep F μ N)| ≤ CI.softLoL.δ0 → ∀ n ∈ rowsOf N,
          Tfun F.L (F.G 0 μ) (F.B 0 μ) (X k) (uNode (F.step N) n) ≤ -ε → envVec CI μ N (X k) n ≤ Cε * |psiHatVec CI μ N (X k) n| := by
  intro ε hε
  obtain ⟨C, h, Cs0, hp, H⟩ := softLower_data CI hm hstdK
  obtain ⟨h1, h1p, HT⟩ := hT.2 Cs0 ε hε
  refine ⟨C, min h h1, lt_min hp h1p, fun μ hμ N hN hNt X Um hE k hk hJ hw n hn hTn => ?_⟩
  have H' := H μ hμ N (hN.trans (min_le_left _ _)) hNt X Um hE k hk hJ hw
  exact H'.1.2 n hn (HT μ hμ N (hN.trans (min_le_right _ _)) hNt (X k) hw H'.2 n hn hTn)

/-- **The bulk envelope-sum clause** (named premise; finding F-BB-4): the missing conjunct of `PropThaW`, `sum_n (V_n/hat N)^2 <= C` uniformly in `X` of the block (paper: `sum (E M)^2 <= sum M_Web^2 <= C h^{-1/2}`
while `hat N^2 ~ h^{-1/2}`).  Used in the first clause of `ThmAii` for bulk eigenvalues. -/
def BulkEnvSum {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}
    (CI : ChartInputs F K Kidx t0 m (2 * Kidx) U V cPC CPC) : Prop :=
  ∀ ν, ∃ Cb h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ X ∈ Icc (CI.lo ν) (CI.hi ν), ∀ N : ℕ,
    max (CI.bulkL ν).N0 (CI.bulkR ν).N0 ≤ N → F.step N ≤ h0 → F.step N ≤ t0 →
      ∑ n ∈ rowsOf N, bulkEnv (CI.bulkL ν) (CI.bulkR ν) (atStep F μ N) X N n ^ 2 ≤ Cb

/-- Per-block package: the eigenvector clause of `PropThaW`, the envelope sum and the nonnegativity of `bulkEnv` on the rows. -/
lemma bulk_block_data (CI : ChartInputs F K Kidx t0 m (2 * Kidx) U V cPC CPC) (hm : 1 ≤ m)
    {r : ℕ} (hr : StdAssump (frozenFamily F Kidx) (paramSet K t0) (m / 2) r) (hBS : BulkEnvSum CI) (ν : Fin CI.nb)
    (hW : PropThaW (frozenFamily F Kidx) (paramSet K t0) (CI.lo ν) (CI.hi ν) m U V (CI.bulkL ν) (CI.bulkR ν)) :
    ∃ Cc Cb h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ X ∈ Icc (CI.lo ν) (CI.hi ν), ∀ N : ℕ,
      max (CI.bulkL ν).N0 (CI.bulkR ν).N0 ≤ N → F.step N ≤ h0 → F.step N ≤ t0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
        ∀ k : Fin (N + 1), Xs k = X →
          (∀ n ∈ rowsOf N, |eigVec Um k n - bulkVec (CI.bulkL ν) (CI.bulkR ν) (atStep F μ N) X N n| ≤
              Cc * F.step N ^ m * bulkEnv (CI.bulkL ν) (CI.bulkR ν) (atStep F μ N) X N n) ∧
          ∑ n ∈ rowsOf N, bulkEnv (CI.bulkL ν) (CI.bulkR ν) (atStep F μ N) X N n ^ 2 ≤ Cb := by
  obtain ⟨-, -, ⟨Cc, h0, cN, CN, cκ, Cκ, hh0, -, -, H⟩, -⟩ := hW hm (CI.overlap_match ν) r hr
  obtain ⟨Cb, hb0, hb0p, HB⟩ := hBS ν
  refine ⟨Cc, Cb, min h0 hb0, lt_min hh0 hb0p, fun μ hμ X hX N hN hst hst' Xs Um hE k hk => ?_⟩
  have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hp : (μ, F.step N) ∈ paramSet K t0 := ⟨hμ, ⟨by linarith, hst'⟩⟩
  have hEf : IsEigenSystem ((frozenFamily F Kidx).jacobiMat (μ, F.step N) N) Xs Um := by
    rw [frozenFamily_jacobiMat_at_step]; exact hE
  obtain ⟨-, -, -, -, hEc⟩ := H (μ, F.step N) hp X hX N hN (hst.trans (min_le_left _ _))
  obtain ⟨-, hrow⟩ := hEc Xs Um hEf k hk
  exact ⟨hrow, HB μ hμ X hX N hN (hst.trans (min_le_right _ _)) hst'⟩

/-- **Bulk absolute clause** (`ThmAii` case 1): the eigenvector clause of `PropThaW` for every block, the envelope sum (`BulkEnvSum`), and the nonnegativity of the envelope on the rows. -/
theorem aiiAbs_bulk (CI : ChartInputs F K Kidx t0 m (2 * Kidx) U V cPC CPC) (hm : 1 ≤ m)
    (hstdM : ∃ r, StdAssump (frozenFamily F Kidx) (paramSet K t0) (m / 2) r) (hBS : BulkEnvSum CI)
    (hW : ∀ ν, PropThaW (frozenFamily F Kidx) (paramSet K t0) (CI.lo ν) (CI.hi ν) m U V (CI.bulkL ν) (CI.bulkR ν)) :
    ∃ C hm : ℝ, 0 < hm ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hm → F.step N ≤ t0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), (∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν) → AiiAbs CI C μ N X Um k := by
  obtain ⟨r, hr⟩ := hstdM
  have hcl := fun ν => bulk_block_data CI hm hr hBS ν (hW ν)
  choose Cc Cb h0 hh0 hH using hcl
  set Csum : ℝ := ∑ ν, (|Cc ν| + |Cb ν|) with hCsum
  set n0 : ℕ := ∑ ν, max (CI.bulkL ν).N0 (CI.bulkR ν).N0 with hn0
  have hn0le : ∀ ν, max (CI.bulkL ν).N0 (CI.bulkR ν).N0 ≤ n0 :=
    fun ν => Finset.single_le_sum (f := fun ν => max (CI.bulkL ν).N0 (CI.bulkR ν).N0) (fun _ _ => Nat.zero_le _) (Finset.mem_univ ν)
  by_cases hnb : Nonempty (Fin CI.nb)
  · obtain ⟨ν0⟩ := hnb
    haveI : Nonempty (Fin CI.nb) := ⟨ν0⟩
    obtain ⟨i, hi⟩ := Finite.exists_min h0
    refine ⟨Csum, min (h0 i) (F.L / ((n0 : ℝ) + 1)), lt_min (hh0 i) (div_pos F.L_pos (by positivity)), ?_⟩
    intro μ hμ N hN hNt X Um hE k hk
    have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
    have hN2 : F.step N ≤ h0 i := hN.trans (min_le_left _ _)
    have hN3 : F.step N ≤ F.L / ((n0 : ℝ) + 1) := hN.trans (min_le_right _ _)
    have hn0N : n0 ≤ N := le_of_step_le hN3
    have hp : (μ, F.step N) ∈ paramSet K t0 := ⟨hμ, ⟨by linarith, hNt⟩⟩
    have hd : ∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν := hk
    have hspec := Classical.choose_spec hd
    set ν := Classical.choose hd with hν
    have hXI : X k ∈ Icc (CI.lo ν) (CI.hi ν) := hspec
    have hNN : max (CI.bulkL ν).N0 (CI.bulkR ν).N0 ≤ N := (hn0le ν).trans hn0N
    obtain ⟨hrow, hsum⟩ := hH ν μ hμ (X k) hXI N hNN (hN2.trans (hi ν)) hNt X Um hE k rfl
    have hEnn : ∀ n ∈ rowsOf N, 0 ≤ bulkEnv (CI.bulkL ν) (CI.bulkR ν) (atStep F μ N) (X k) N n := fun n hn =>
      TheoremB.bulkEnv_nonneg_rows (CI.bulkL ν) (CI.bulkR ν) (CI.overlap_match ν) (μ, F.step N) hp (X k) hXI N
        (le_trans (le_max_left _ _) hNN) (le_trans (le_max_right _ _) hNN) hpos
        (fun j hj0 hjN => TheoremB.chart_envL_nonneg (CI.bulkL ν) (μ, F.step N) hp (X k) hXI N (le_trans (le_max_left _ _) hNN) j hj0 hjN)
        (fun j hj0 hjN => TheoremB.chart_envL_nonneg (CI.bulkR ν) (μ, F.step N) hp (X k) hXI N (le_trans (le_max_right _ _) hNN) j hj0 hjN) n hn
    have hCc : Cc ν ≤ Csum := by
      have h1 : |Cc ν| + |Cb ν| ≤ Csum :=
        Finset.single_le_sum (f := fun ν => |Cc ν| + |Cb ν|) (fun _ _ => by positivity) (Finset.mem_univ ν)
      linarith [le_abs_self (Cc ν), abs_nonneg (Cb ν)]
    have hCb : Cb ν ≤ Csum := by
      have h1 : |Cc ν| + |Cb ν| ≤ Csum :=
        Finset.single_le_sum (f := fun ν => |Cc ν| + |Cb ν|) (fun _ _ => by positivity) (Finset.mem_univ ν)
      linarith [le_abs_self (Cb ν), abs_nonneg (Cc ν)]
    have e1 : ∀ n, psiHatVec CI μ N (X k) n = bulkVec (CI.bulkL ν) (CI.bulkR ν) (atStep F μ N) (X k) N n := by
      intro n; unfold psiHatVec; rw [dite_eq_left hd]
    have e2 : ∀ n, envVec CI μ N (X k) n = bulkEnv (CI.bulkL ν) (CI.bulkR ν) (atStep F μ N) (X k) N n := by
      intro n; unfold envVec; rw [dite_eq_left hd]
    refine ⟨fun n hn => ?_, ?_⟩
    · rw [e1, e2]
      exact (hrow n hn).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCc (pow_nonneg hpos.le _)) (hEnn n hn))
    · simpa only [e2] using hsum.trans hCb
  · refine ⟨0, 1, one_pos, ?_⟩
    intro μ hμ N hN hNt X Um hE k hk
    obtain ⟨ν, -⟩ := hk
    exact (hnb ⟨ν⟩).elim

/-- **Nonnegativity of the envelope `V_{k,n}` on the rows**, for small `h`, at every energy (the premise `hnn` of `thmAii_of_cases`): `softEnv_nonneg` in the soft cases and `bulkEnv_nonneg_rows` for the block chosen by `envVec`. -/
theorem envVec_nonneg (CI : ChartInputs F K Kidx t0 m (2 * Kidx) U V cPC CPC) :
    ∃ hn : ℝ, 0 < hn ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hn → F.step N ≤ t0 → ∀ x : ℝ, ∀ n ∈ rowsOf N, 0 ≤ envVec CI μ N x n := by
  set n0 : ℕ := ∑ ν, max (CI.bulkL ν).N0 (CI.bulkR ν).N0 with hn0
  have hn0le : ∀ ν, max (CI.bulkL ν).N0 (CI.bulkR ν).N0 ≤ n0 :=
    fun ν => Finset.single_le_sum (f := fun ν => max (CI.bulkL ν).N0 (CI.bulkR ν).N0) (fun _ _ => Nat.zero_le _) (Finset.mem_univ ν)
  refine ⟨F.L / ((n0 : ℝ) + 1), div_pos F.L_pos (by positivity), ?_⟩
  intro μ hμ N hN hNt x n hn
  have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hn0N : n0 ≤ N := le_of_step_le hN
  have hp : (μ, F.step N) ∈ paramSet K t0 := ⟨hμ, ⟨by linarith, hNt⟩⟩
  unfold envVec
  by_cases hd : ∃ ν, CI.lo ν ≤ x ∧ x ≤ CI.hi ν
  · rw [dite_eq_left hd]
    have hspec := Classical.choose_spec hd
    set ν := Classical.choose hd with hν
    have hXI : x ∈ Icc (CI.lo ν) (CI.hi ν) := hspec
    have hNN : max (CI.bulkL ν).N0 (CI.bulkR ν).N0 ≤ N := (hn0le ν).trans hn0N
    exact TheoremB.bulkEnv_nonneg_rows (CI.bulkL ν) (CI.bulkR ν) (CI.overlap_match ν) (μ, F.step N) hp x hXI N
        (le_trans (le_max_left _ _) hNN) (le_trans (le_max_right _ _) hNN) hpos
        (fun j hj0 hjN => TheoremB.chart_envL_nonneg (CI.bulkL ν) (μ, F.step N) hp x hXI N (le_trans (le_max_left _ _) hNN) j hj0 hjN)
        (fun j hj0 hjN => TheoremB.chart_envL_nonneg (CI.bulkR ν) (μ, F.step N) hp x hXI N (le_trans (le_max_right _ _) hNN) j hj0 hjN) n hn
  · rw [dite_eq_right hd]
    split_ifs
    · exact softEnv_nonneg CI.softUpL CI.softUpR CI.pc _ _ _ _
    · exact softEnv_nonneg CI.softLoL CI.softLoR CI.pc _ _ _ _

/-- **`ThmAii` from `PropThaW`, `PropThaW2` (proved) and `spectrumCovered`** (thm:A (ii), all three cases, including the relative clause R1).  The premises that are *not* consequences of the frozen statements:
`hstdM`, `hstdK` (the standing assumptions of the frozen family on `paramSet K t0`, finding F-t0), `hW` (`PropThaW` for every block), `hBS` (`BulkEnvSum`, finding F-BB-4), `hT` (`SoftWindowT`, finding F-BB-5). -/
theorem thmAii_of_propThaW (CI : ChartInputs F K Kidx t0 m (2 * Kidx) U V cPC CPC)
    (hstdM : ∃ r, StdAssump (frozenFamily F Kidx) (paramSet K t0) (m / 2) r)
    (hstdK : ∃ r, StdAssump (frozenFamily F Kidx) (paramSet K t0) Kidx r) (hBS : BulkEnvSum CI) (hT : SoftWindowT CI)
    (hW : ∀ ν, PropThaW (frozenFamily F Kidx) (paramSet K t0) (CI.lo ν) (CI.hi ν) m U V (CI.bulkL ν) (CI.bulkR ν)) :
    ThmAii F K m Kidx t0 U V cPC CPC CI := by
  intro hm1 hKidx hK hH hD
  have hD1 : DM F K 1 := dm_mono F K (by omega : 1 ≤ 2 * ((m + 1) / 2) + 1) hK hD
  have hDc : DM F K (2 * Kidx + 1) := by rw [hKidx]; exact hD
  exact thmAii_of_cases CI (envVec_nonneg CI) (aiiAbs_bulk CI hm1 hstdM hBS hW) (aiiAbs_upper CI hm1 hstdK)
    (aiiAbs_lower CI hm1 hstdK) (spectrumCovered CI) hKidx hK hH hDc
    (fun ε hε => thmAii_bulk_relative CI hm1 hK hD1 hstdM hstdK hW hε) (relUpper CI hm1 hstdK hT) (relLower CI hm1 hstdK hT)

end Soft

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.softUpper_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.softUpper_data

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.softLower_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.softLower_data

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.aiiAbs_bulk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.aiiAbs_bulk

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.envVec_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.envVec_nonneg

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.relUpper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.relUpper

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.relLower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.relLower

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.thmAii_of_propThaW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.thmAii_of_propThaW

end FormalResearch.JacobiEigenvectors.TheoremA

end
