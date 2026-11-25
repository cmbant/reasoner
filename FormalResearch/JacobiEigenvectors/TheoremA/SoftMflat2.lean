module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftMflat
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftCountChart
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftSigns3
public import FormalResearch.JacobiEigenvectors.TheoremB.SpliceSoft
public import FormalResearch.JacobiEigenvectors.TheoremB.Statements

/-!
# Paper J, Layer 3 (L3.3, part 2): `lem:tha-Mflat` (`PropThaMflat`)

Source: Paper J `app_thmB.tex`, proof of `lem:tha-Mflat` (*The fold row*, *Half-windows*, *Seam rows*).  Statement: `PropThaMflat CL CR cPC CPC` (`TheoremB/Statements.lean`; F-B14 applied in round 10).

## Proved here

`propThaMflat_proved : PropThaMflat CL CR cPC CPC`, with no premise beyond the statement's own (`ParabolicCylinderFacts`, `1 <= m`, `SoftMirror`).  `SoftFoldSmall CL` is the chart field `delta0_small`; the sign analysis of Step 6
(label = index, `soft_count_chart`) uses `softCountHyps_proved`.
* flat0: `fold_Z_bound` (`SoftMflat.lean`) for `n_c = nearestRow u_c`.
* flat1: `propThaM_of_facts` at the cut `s = Z_{n_c}` (`fold_in_window`: `|s| <= s_A`); the half-windows `Omega_- = {n <= n_c}`, `Omega_+ = {n > n_c}` are `{Z_n <= s}`, `{Z_n > s}` on `Omega` (`Zof_le`, `Zof_incr` on the collar).
* flat2: the seam rows `n_c, n_c + 1` lie in `Omega` (`fold_pair`, `Zof_succ_le`), `|softNum| <= K T M_bal` and `hat N^2 >= c_n T^2 h^{-1/2}` (`soft_splice_facts`), and `M_bal(a,Z_n)^2 <= 2 (1+k)^{-1/2}` (`mbal_seam`: `k_2 >= (1+A)/4`, `A >= k` from the label `a = -(k+1/2) + O(h^m)`, `soft_count_chart`).

## Differences from the paper

None of substance: the paper's proof uses Olver's bounds (`ParabolicCylinderFacts`), `delta_0` small (the chart field `delta0_small`) and Step 6 (`softCountHyps_proved`).

## Findings

* **F-B14 (applied).**  `PropThaMflat` lacked the premises `1 <= m` and `SoftMirror CL CR` (and `ParabolicCylinderFacts`), but flat2 is about `softVec CL CR` (built from the *mirror* chart `CR`) and needs the eigenvector/matching estimates, whose engine smallness
  `h^m Theta <= c_*` is unavailable for `m = 0` (cf. F-W2-4); for an unrelated `CR` flat2 is false.  Same pattern as F-B9.  The statement now starts `ParabolicCylinderFacts U V cPC CPC -> 1 <= m -> SoftMirror CL CR ->` (flat0, flat1 do not use the last two).
* **chart constants** (applied): the field `SoftEdgeChart.delta0_small` (`SoftFoldSmall`, see `SoftMflat.lean`).

## Not formalised

Nothing.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

section Seam

/-- `M_bal(a,z)^2 <= 2 (sqrt(1+k))^{-1}` when `k <= A = max(-a,0)` and `z^2 <= 2 A` if `A >= 1` (the seam-row estimate of the paper: `k_2 >= (1+A)/4`). -/
theorem mbal_seam (a z k : ℝ) (hk : k ≤ max (-a) 0) (hk0 : 0 ≤ k) (hz : 1 ≤ max (-a) 0 → z ^ 2 ≤ 2 * max (-a) 0) :
    Mbal a z ^ 2 ≤ 2 * (Real.sqrt (1 + k))⁻¹ := by
  set A := max (-a) 0 with hA
  have hA0 : 0 ≤ A := le_max_right _ _
  have hg : 0 < (1 + A) / 4 := by positivity
  have hgk : (1 + A) / 4 ≤ k2 a z := by
    by_cases h1 : 1 ≤ A
    · have hna : 1 ≤ -a := (le_max_iff.mp (hA ▸ h1)).resolve_right (by norm_num)
      have hAe : A = -a := max_eq_left (by linarith)
      have hz2 := hz h1
      have : A - z ^ 2 / 4 ≤ |z ^ 2 / 4 + a| := by
        have := neg_le_abs (z ^ 2 / 4 + a)
        linarith
      unfold k2
      refine le_trans ?_ (le_trans this (le_max_left _ _))
      linarith
    · push Not at h1
      unfold k2
      have h2 : (1 : ℝ) ≤ (max |a| 1) ^ ((1 : ℝ) / 3) := Real.one_le_rpow (le_max_right _ _) (by norm_num)
      refine le_trans ?_ (le_trans h2 (le_max_right _ _))
      linarith
  have h1 : Mbal a z ^ 2 ≤ (Real.sqrt ((1 + A) / 4))⁻¹ := by
    unfold Mbal
    have h1 : k2 a z ^ (-(1 : ℝ) / 4) ≤ ((1 + A) / 4) ^ (-(1 : ℝ) / 4) := Real.rpow_le_rpow_of_nonpos hg hgk (by norm_num)
    have hk0' : 0 ≤ k2 a z ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg (le_trans hg.le hgk) _
    have h2 := pow_le_pow_left₀ hk0' h1 2
    have h3 : (((1 + A) / 4) ^ (-(1 : ℝ) / 4)) ^ 2 = (Real.sqrt ((1 + A) / 4))⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hg.le, Real.sqrt_eq_rpow, ← Real.rpow_neg hg.le]
      norm_num
    rw [h3] at h2
    exact h2
  refine h1.trans ?_
  have e : Real.sqrt ((1 + A) / 4) = Real.sqrt (1 + A) / 2 := by
    rw [Real.sqrt_div (by linarith), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)]
  rw [e]
  have hs1 : 0 < Real.sqrt (1 + k) := Real.sqrt_pos.mpr (by linarith)
  have hs2 : Real.sqrt (1 + k) ≤ Real.sqrt (1 + A) := Real.sqrt_le_sqrt (by linarith)
  rw [inv_div]
  have : 2 / Real.sqrt (1 + A) ≤ 2 / Real.sqrt (1 + k) := div_le_div_of_nonneg_left (by norm_num) hs1 hs2
  calc 2 / Real.sqrt (1 + A) ≤ 2 / Real.sqrt (1 + k) := this
    _ = 2 * (Real.sqrt (1 + k))⁻¹ := by ring

/-- the hypothesis of `mbal_seam`: `z^2 <= 2 A` when `A >= 1` and `|z| <= sqrt A + 2/5`. -/
lemma mflat_seam_z {A z : ℝ} (hA : 1 ≤ A) (hz : |z| ≤ Real.sqrt A + 2 / 5) : z ^ 2 ≤ 2 * A := by
  have hsA1 : 1 ≤ Real.sqrt A := Real.one_le_sqrt.mpr hA
  have hsA2 : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt (by linarith)
  have h1 : z ^ 2 ≤ (Real.sqrt A + 2 / 5) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hz 2
  have h2 : (Real.sqrt A + 2 / 5) ^ 2 = Real.sqrt A * Real.sqrt A + 4 / 5 * Real.sqrt A + 4 / 25 := by ring
  have h3 : (1 : ℝ) / 5 ≤ Real.sqrt A - 4 / 5 := by linarith
  have h4 : 1 * (1 / 5 : ℝ) ≤ Real.sqrt A * (Real.sqrt A - 4 / 5) :=
    mul_le_mul hsA1 h3 (by norm_num) (by linarith)
  have h5 : Real.sqrt A * (Real.sqrt A - 4 / 5) = Real.sqrt A * Real.sqrt A - 4 / 5 * Real.sqrt A := by ring
  linarith only [h1, h2, h4, h5, hsA2]

/-- the seam constant: `Cl s^(m+1) <= s/2` for `m >= 1`, `s <= 1` and `s <= 1/(2(|Cl|+1))`. -/
lemma mflat_small_Cl {m : ℕ} (hm : 1 ≤ m) {s Cl : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hsCl : s ≤ 1 / (2 * (|Cl| + 1))) : Cl * s ^ (m + 1) ≤ s / 2 := by
  have h1 : s ^ (m + 1) ≤ s * s := by
    calc s ^ (m + 1) ≤ s ^ 2 := pow_le_pow_of_le_one hs0.le hs1 (by omega)
      _ = s * s := by ring
  have h2 : |Cl| * s ≤ 1 / 2 := by
    refine (mul_le_mul_of_nonneg_left hsCl (abs_nonneg Cl)).trans ?_
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith only [abs_nonneg Cl]
  calc Cl * s ^ (m + 1) ≤ |Cl| * (s * s) := mul_le_mul (le_abs_self _) h1 (pow_nonneg hs0.le _) (abs_nonneg _)
    _ = (|Cl| * s) * s := by ring
    _ ≤ (1 / 2) * s := mul_le_mul_of_nonneg_right h2 hs0.le
    _ = s / 2 := by ring

/-- the label bound of a seam row: `mu >= k s` from the count estimate, and `-a = mu / s`. -/
lemma mflat_label {k mu Cl s a : ℝ} {m : ℕ} (hs0 : 0 < s) (hCl : Cl * s ^ (m + 1) ≤ s / 2)
    (hlk : -(Cl * s ^ (m + 1)) ≤ mu - (k + 1 / 2) * s) (hae : a = -(1 / s) * mu) : k ≤ -a := by
  have hmu : k * s ≤ mu := by linarith only [hCl, hlk]
  rw [hae, show -(-(1 / s) * mu) = mu / s by ring, le_div_iff₀ hs0]
  exact hmu

/-- the quotient bound of a seam row: `(num/den)^2 <= (K^2/cn) sqrt s M^2` from `|num| <= K T M` and
`cn T^2 s^(-1/2) <= den^2`. -/
lemma mflat_quot_sq {num den K cn T s M : ℝ} (hs0 : 0 < s) (hT : 0 < T) (hcn : 0 < cn)
    (hnum : |num| ≤ K * (T * M)) (hden : cn * (T ^ 2 * s ^ (-(1 : ℝ) / 2)) ≤ den ^ 2) :
    num ^ 2 / den ^ 2 ≤ (K ^ 2 / cn) * Real.sqrt s * M ^ 2 := by
  have hsq : num ^ 2 ≤ (K * (T * M)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hnum 2
  have hBpos : 0 < cn * (T ^ 2 * s ^ (-(1 : ℝ) / 2)) :=
    mul_pos hcn (mul_pos (pow_pos hT 2) (Real.rpow_pos_of_pos hs0 _))
  refine (div_le_div₀ (sq_nonneg _) hsq hBpos hden).trans (le_of_eq ?_)
  have hs' : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
  rw [rpow_half_eq hs0]
  field_simp

end Seam

section Rows

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (C : SoftEdgeChart Fz P m q U V Lm)

/-- consecutive collar rows: `0 <= Z_{j+1} - Z_j <= d_+ sqrt h`. -/
theorem Zof_succ_le {μ : Par × ℝ} (hμ : μ ∈ P) {X : ℝ} (hX : |X - Fz.bandHi μ| ≤ C.δ0) (N : ℕ) {j : ℤ}
    (hj : |uNode (Fz.step N) j - C.uc μ| ≤ C.η / 2) (hj1 : |uNode (Fz.step N) (j + 1) - C.uc μ| ≤ C.η / 2) :
    C.Zof μ X N j ≤ C.Zof μ X N (j + 1) ∧ C.Zof μ X N (j + 1) - C.Zof μ X N j ≤ C.dp * Real.sqrt (Fz.step N) := by
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hs : 0 < Real.sqrt (Fz.step N) := Real.sqrt_pos.mpr hh0
  have hsq : Real.sqrt (Fz.step N) * Real.sqrt (Fz.step N) = Fz.step N := Real.mul_self_sqrt hh0.le
  have hα := C.abs_alpha_le hX
  have hη := C.consts_pos.2.1
  refine ⟨Zof_le C hμ hX N (by omega) hj hj1, ?_⟩
  have hj' := abs_le.mp hj
  have hj1' := abs_le.mp hj1
  have hd : uNode (Fz.step N) (j + 1) - uNode (Fz.step N) j = Fz.step N := uNode_succ_sub' _ _
  have hmv := C.zeta_mvt hμ hα (x1 := uNode (Fz.step N) j - C.uc μ) (x2 := uNode (Fz.step N) (j + 1) - C.uc μ)
    (by linarith) (by linarith) (by linarith)
  have hmv2 := hmv.2
  have e : (uNode (Fz.step N) (j + 1) - C.uc μ) - (uNode (Fz.step N) j - C.uc μ) = Fz.step N := by linarith
  rw [e] at hmv2
  unfold SoftEdgeCore.Zof
  rw [← sub_div, div_le_iff₀ hs]
  calc _ ≤ C.dp * Fz.step N := hmv2
    _ = C.dp * Real.sqrt (Fz.step N) * Real.sqrt (Fz.step N) := by rw [mul_assoc, hsq]

/-- a row within `eta/2` of the fold is a lattice row. -/
theorem row_mem_near {μ : Par × ℝ} (hμ : μ ∈ P) (N : ℕ) {n : ℤ} (hn : |uNode (Fz.step N) n - C.uc μ| ≤ C.η / 2) : n ∈ rowsOf N := by
  have hh : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  obtain ⟨huc0, huc1⟩ := C.ucη_in μ hμ
  have hη := C.consts_pos.2.1
  have hLs : Fz.step N * ((N : ℝ) + 1) = Fz.L := step_mul_succ Fz N
  have hb := abs_le.mp hn
  have hu : uNode (Fz.step N) n = ((n : ℝ) + 1 / 2) * Fz.step N := rfl
  have hpos : 0 < ((n : ℝ) + 1 / 2) * Fz.step N := by rw [← hu]; linarith
  have hlt : ((n : ℝ) + 1 / 2) * Fz.step N < Fz.step N * ((N : ℝ) + 1) := by rw [hLs, ← hu]; linarith
  have h1' : (0 : ℝ) < (n : ℝ) + 1 / 2 := by
    by_contra hc; push Not at hc; nlinarith
  have h2' : (n : ℝ) + 1 / 2 < (N : ℝ) + 1 := by
    by_contra hc; push Not at hc; nlinarith
  unfold rowsOf
  rw [Finset.mem_Icc]
  constructor
  · have : (-1 : ℝ) < (n : ℝ) := by linarith
    exact_mod_cast (show (-1 : ℤ) < n by exact_mod_cast this)
  · have : (n : ℝ) < (N : ℝ) + 1 := by linarith
    have h3 : n < (N : ℤ) + 1 := by exact_mod_cast this
    omega

/-- **The fold row and its successor lie in the window** (`n_0, n_0 + 1 in Omega`), with `|Z| <= sqrt A + C_p sqrt h`, `4 C_p sqrt h <= l_A` and `C_p sqrt h <= 2/5`. -/
theorem fold_pair (hsmall : SoftFoldSmall C) :
    ∃ Cp h0 : ℝ, 0 < Cp ∧ 0 < h0 ∧ ∀ p ∈ P, ∀ X, |X - Fz.bandHi p| ≤ C.δ0 → ∀ N : ℕ, C.N0 ≤ N → Fz.step N ≤ h0 → C.aOf p X N ≤ 1 →
      ∀ n0 : ℤ, |uNode (Fz.step N) n0 - C.uc p| ≤ Fz.step N / 2 →
        n0 ∈ softWindow C p X N ∧ n0 + 1 ∈ softWindow C p X N ∧
        |C.Zof p X N n0| ≤ Real.sqrt (max (-C.aOf p X N) 0) + Cp * Real.sqrt (Fz.step N) ∧
        |C.Zof p X N (n0 + 1)| ≤ Real.sqrt (max (-C.aOf p X N) 0) + Cp * Real.sqrt (Fz.step N) ∧
        Cp * Real.sqrt (Fz.step N) ≤ 2 / 5 := by
  obtain ⟨Cf, h1, hCf, hh1p, H⟩ := fold_Z_bound C hsmall
  obtain ⟨hδ, hη, hdm, hdmp, -⟩ := C.consts_pos
  have hdp : 0 < C.dp := lt_of_lt_of_le hdm hdmp
  have hBm : 0 ≤ C.Cmu * (1 + ((q / 2 : ℕ) : ℝ)) := mul_nonneg C.consts_pos2.1 (by positivity)
  set B : ℝ := C.Cmu * (1 + ((q / 2 : ℕ) : ℝ)) with hB
  set Cp : ℝ := Cf + C.dp with hCp
  have hCp0 : 0 < Cp := by positivity
  refine ⟨Cp, min (min h1 1) (min (C.η / 3) (min (1 / (4096 * Cp ^ 6 * (1 + B) + 1)) ((2 / (5 * Cp)) ^ 2))), hCp0,
    lt_min (lt_min hh1p one_pos) (lt_min (by positivity) (lt_min (by positivity) (by positivity))), ?_⟩
  intro p hp X hX N hN hstep ha n0 hn0
  have hh : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hs1 : Fz.step N ≤ h1 := hstep.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hs2 : Fz.step N ≤ 1 := hstep.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hs3 : Fz.step N ≤ C.η / 3 := hstep.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs4 : Fz.step N ≤ 1 / (4096 * Cp ^ 6 * (1 + B) + 1) :=
    hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hs5 : Fz.step N ≤ (2 / (5 * Cp)) ^ 2 := hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hK : 4096 * Cp ^ 6 * (1 + B) * Fz.step N ≤ 1 := by
    have h0 : 0 < 4096 * Cp ^ 6 * (1 + B) + 1 := by positivity
    rw [le_div_iff₀ h0] at hs4
    nlinarith
  have hsqrt : Real.sqrt (Fz.step N) ≤ 2 / (5 * Cp) := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 / (5 * Cp))]
    exact Real.sqrt_le_sqrt hs5
  have hCps : Cp * Real.sqrt (Fz.step N) ≤ 2 / 5 := by
    calc Cp * Real.sqrt (Fz.step N) ≤ Cp * (2 / (5 * Cp)) := mul_le_mul_of_nonneg_left hsqrt hCp0.le
      _ = 2 / 5 := by field_simp
  have hx0 := abs_le.mp hn0
  have hx1 : |uNode (Fz.step N) (n0 + 1) - C.uc p| ≤ C.η / 2 := by
    have : uNode (Fz.step N) (n0 + 1) = uNode (Fz.step N) n0 + Fz.step N := by unfold uNode; push_cast; ring
    rw [abs_le]; constructor <;> linarith
  have hx0' : |uNode (Fz.step N) n0 - C.uc p| ≤ C.η / 2 := by rw [abs_le]; constructor <;> linarith
  have hfold := H p hp X hX N hs1 ha n0 hn0
  have hsucc := Zof_succ_le C hp hX N hx0' hx1
  set A := max (-C.aOf p X N) 0 with hAdef
  have hA0 : 0 ≤ A := le_max_right _ _
  have hAh : A * Fz.step N ≤ B := by
    have hmu := C.muTilde_abs_le hp hX hs2
    rcases le_total (C.aOf p X N) 0 with ha0 | ha0
    · have hAe : A = -C.aOf p X N := max_eq_left (by linarith)
      rw [hAe, C.aOf_eq p X N]
      have : -(-(1 / Fz.step N) * C.muTilde p X N) * Fz.step N = C.muTilde p X N := by field_simp
      rw [this]
      exact (le_abs_self _).trans hmu
    · have : A = 0 := max_eq_right (by linarith)
      rw [this]; linarith
  have hell := sqrt_le_ell Cp B (Fz.step N) A hCp0.le hBm hh hs2 hA0 hAh hK
  have hsA := Real.sqrt_nonneg A
  have hsq0 := Real.sqrt_nonneg (Fz.step N)
  have hZ0 : |C.Zof p X N n0| ≤ Real.sqrt A + Cp * Real.sqrt (Fz.step N) := by
    refine hfold.trans ?_
    have : Cf * Real.sqrt (Fz.step N) ≤ Cp * Real.sqrt (Fz.step N) := mul_le_mul_of_nonneg_right (by rw [hCp]; linarith) hsq0
    linarith
  have hZ1 : |C.Zof p X N (n0 + 1)| ≤ Real.sqrt A + Cp * Real.sqrt (Fz.step N) := by
    have h1' : |C.Zof p X N (n0 + 1)| ≤ |C.Zof p X N n0| + C.dp * Real.sqrt (Fz.step N) := by
      calc |C.Zof p X N (n0 + 1)| = |C.Zof p X N n0 + (C.Zof p X N (n0 + 1) - C.Zof p X N n0)| := by rw [add_sub_cancel]
        _ ≤ |C.Zof p X N n0| + |C.Zof p X N (n0 + 1) - C.Zof p X N n0| := abs_add_le _ _
        _ = |C.Zof p X N n0| + (C.Zof p X N (n0 + 1) - C.Zof p X N n0) := by rw [abs_of_nonneg (sub_nonneg.mpr hsucc.1)]
        _ ≤ |C.Zof p X N n0| + C.dp * Real.sqrt (Fz.step N) := by linarith [hsucc.2]
    have : Cf * Real.sqrt (Fz.step N) + C.dp * Real.sqrt (Fz.step N) = Cp * Real.sqrt (Fz.step N) := by rw [hCp]; ring
    have h3 : |C.Zof p X N n0| ≤ Real.sqrt A + Cf * Real.sqrt (Fz.step N) := hfold
    linarith
  have hmemb : ∀ n, |uNode (Fz.step N) n - C.uc p| ≤ C.η / 2 → |C.Zof p X N n| ≤ Real.sqrt A + Cp * Real.sqrt (Fz.step N) →
      n ∈ softWindow C p X N := by
    intro n hn hZ
    unfold softWindow
    rw [Finset.mem_filter]
    refine ⟨row_mem_near C hp N hn, ?_⟩
    unfold rhoWin
    have hl : 0 ≤ (1 + max (-C.aOf p X N) 0) ^ (-(1 : ℝ) / 6) := ell_nonneg' _
    nlinarith [hZ, hell, hsA, hl]
  exact ⟨hmemb _ hx0' hZ0, hmemb _ hx1 hZ1, hZ0, hZ1, hCps⟩

end Rows

section Main

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ}

/-- **`lem:tha-Mflat`** (`PropThaMflat CL CR cPC CPC`; the premises `ParabolicCylinderFacts`, `1 <= m`, `SoftMirror` are part of the statement since round 10, finding F-B14 applied; `SoftFoldSmall` is the chart field `delta0_small`;
`SoftCountHyps` is `softCountHyps_proved`). -/
theorem propThaMflat_proved {cPC CPC : ℝ} (CL : SoftEdgeChart Fz P m q U V (fun _ => 1))
    (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V (fun _ => 1)) : PropThaMflat CL CR cPC CPC := by
  unfold PropThaMflat
  intro hf hm hM r hr
  have hfold : SoftFoldSmall CL := CL.delta0_small
  have hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ (fun _ : ℝ => (1 : ℝ)) h := fun _ _ _ => le_rfl
  obtain ⟨cM, hM0, hcM, hM0p, HM⟩ := propThaM_of_facts (cPC := cPC) (CPC := CPC) CL 1 hf r hr
  obtain ⟨Cp, hp0, hCp, hp0p, Hp⟩ := fold_pair CL hfold
  obtain ⟨hw0, hw0p, Hw⟩ := fold_in_window CL hfold
  obtain ⟨Cf, hf1, hCf, hf1p, Hf'⟩ := fold_Z_bound CL hfold
  obtain ⟨Cenv, Cm, K, CM, cn, clb, hF0, hCenv, hCm, hK, hCM, hcn, hclb, hF0p, Hf⟩ := soft_splice_facts CL CR hM hf hm hLm
  obtain ⟨Cz, hz0, hz0p, Hz⟩ := stepZero Fz P (q / 2) r hr
  obtain ⟨Cl, hl0, hl0p, Hl⟩ := soft_count_chart CL CR hM hf hm hLm Cz (softCountHyps_proved CL CR hM hf hm hLm Cz)
  have hC0 : 0 ≤ 4 * K ^ 2 / cn := by positivity
  refine ⟨cM, max Cf (4 * K ^ 2 / cn),
    min (min (min hp0 hM0) (min hw0 hf1)) (min (min (min hF0 hl0) (min hz0 CL.softH1)) (min (min CR.softH1 CL.η) (min CR.η (min (asmH0 CL) (1 / (2 * (|Cl| + 1))))))),
    hcM, lt_min (lt_min (lt_min hp0p hM0p) (lt_min hw0p hf1p)) (lt_min (lt_min (lt_min hF0p hl0p) (lt_min hz0p CL.softH1_pos))
      (lt_min (lt_min CR.softH1_pos CL.consts_pos.2.1) (lt_min CR.consts_pos.2.1 (lt_min (asmH0_pos CL) (by positivity))))), ?_⟩
  intro p hp X hX N hN hstep ha
  have hA1 := hstep.trans (min_le_left _ _)
  have hA2 := hstep.trans (min_le_right _ _)
  have sp : Fz.step N ≤ hp0 := hA1.trans ((min_le_left _ _).trans (min_le_left _ _))
  have sM : Fz.step N ≤ hM0 := hA1.trans ((min_le_left _ _).trans (min_le_right _ _))
  have sw : Fz.step N ≤ hw0 := hA1.trans ((min_le_right _ _).trans (min_le_left _ _))
  have sf1 : Fz.step N ≤ hf1 := hA1.trans ((min_le_right _ _).trans (min_le_right _ _))
  have sF : Fz.step N ≤ hF0 := hA2.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have sl : Fz.step N ≤ hl0 := hA2.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have sz : Fz.step N ≤ hz0 := hA2.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have sH1 : Fz.step N ≤ CL.softH1 := hA2.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have sH1R : Fz.step N ≤ CR.softH1 := hA2.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have sη : Fz.step N ≤ CL.η := hA2.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have sηR : Fz.step N ≤ CR.η := hA2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have sAs : Fz.step N ≤ asmH0 CL := hA2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have sCl : Fz.step N ≤ 1 / (2 * (|Cl| + 1)) :=
    hA2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hN1 : CL.N0 ≤ N := (le_max_left _ _).trans hN
  have hN2 : CR.N0 ≤ N := (le_max_right _ _).trans hN
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hh1 : Fz.step N ≤ 1 := sAs.trans (asmH0_le_one CL)
  have hnc : |uNode (Fz.step N) (nearestRow (Fz.step N) (CL.uc p)) - CL.uc p| ≤ Fz.step N / 2 := nearestRow_close _ _ hh0
  set nc := nearestRow (Fz.step N) (CL.uc p) with hncdef
  have hsq0 := Real.sqrt_nonneg (Fz.step N)
  -- flat0
  have F0 : |CL.Zof p X N nc| ≤ Real.sqrt (max (-CL.aOf p X N) 0) + max Cf (4 * K ^ 2 / cn) * Real.sqrt (Fz.step N) := by
    refine (Hf' p hp X hX N sf1 ha nc hnc).trans ?_
    have := mul_le_mul_of_nonneg_right (le_max_left Cf (4 * K ^ 2 / cn)) hsq0
    linarith
  -- flat1
  obtain ⟨hncW, hncC⟩ := Hw p hp X hX N hN1 sw ha nc hnc
  obtain ⟨hpn, hpn1, -, -, -⟩ := Hp p hp X hX N hN1 sp ha nc hnc
  have h1M := HM p hp X hX N hN1 sM ha (CL.Zof p X N nc) (by unfold wmCut at hncC; exact hncC)
  obtain ⟨M1, M2, M3⟩ := h1M
  have hiff : ∀ n ∈ softWindow CL p X N, (n ≤ nc ↔ CL.Zof p X N n ≤ CL.Zof p X N nc) := by
    intro n hn
    have hc1 := soft_win_loc CL hp hX sAs hn
    have hc2 := soft_win_loc CL hp hX sAs hncW
    have hη := CL.consts_pos.2.1
    have hdm := CL.consts_pos.2.2.1
    constructor
    · intro hle
      exact Zof_le CL hp hX N hle (by linarith) (by linarith)
    · intro hZ
      by_contra hcon
      push Not at hcon
      have hinc := Zof_incr CL hp hX N hcon.le (by linarith) (by linarith)
      have h1 : (1 : ℝ) ≤ (n : ℝ) - nc := by
        have : nc + 1 ≤ n := hcon
        have : ((nc : ℝ) + 1) ≤ n := by exact_mod_cast this
        linarith
      have hs0 : 0 < Real.sqrt (Fz.step N) := Real.sqrt_pos.mpr hh0
      have : 0 < CL.dm * ((n : ℝ) - nc) * Real.sqrt (Fz.step N) := by positivity
      linarith
  have hfil1 : (softWindow CL p X N).filter (fun n => n ≤ nc) = (softWindow CL p X N).filter (fun n => CL.Zof p X N n ≤ CL.Zof p X N nc) :=
    Finset.filter_congr fun n hn => hiff n hn
  have hfil2 : (softWindow CL p X N).filter (fun n => nc < n) = (softWindow CL p X N).filter (fun n => CL.Zof p X N nc < CL.Zof p X N n) :=
    Finset.filter_congr fun n hn => by rw [← not_le, ← not_le, hiff n hn]
  refine ⟨F0, ?_, ?_, ?_, ?_⟩
  · rw [hfil1]; exact M2
  · rw [hfil2]; exact M1
  · rw [hfil1]; exact M3
  -- flat2
  intro Xs Um hE k hk
  subst hk
  have hη0 := CL.consts_pos.2.1
  obtain ⟨ψL, ψ', κ, hJL, hsL, hJR, hsR, hrel⟩ := eig_exact_data CL CR hM hp hN1 hN2 sH1 sH1R sη sηR Xs Um hE k hX
  obtain ⟨hT, E1, E2, E3, E4, E5, E7⟩ := Hf p hp N hN sF (Xs k) hX ha ψL ψ' κ hJL hsL hJR hsR hrel
  have hst0 : ∀ i, Xs i ≤ Fz.bandHi p + Cz * Fz.step N ^ 2 := fun i => (Hz p hp N sz Xs Um hE i).2
  obtain ⟨hlab, -⟩ := Hl p hp N hN sl Xs Um hE hst0
  have hlk := hlab k hX
  simp only [mul_one] at hlk
  set a := CL.aOf p (Xs k) N with hadef
  set T := |CL.lamL p (Xs k) N| / kappaBal a with hTdef
  -- label: k <= A
  have hkA : (k : ℝ) ≤ max (-a) 0 := by
    have hmt : CL.muTilde p (Xs k) N = CL.muS 0 p (Fz.bandHi p - Xs k) + ∑ s ∈ Finset.Icc 1 (q / 2), Fz.step N ^ (2 * s) * CL.muS s p (Fz.bandHi p - Xs k) := rfl
    have hlk' := (abs_le.mp hlk).1
    rw [← hmt] at hlk'
    exact (mflat_label hh0 (mflat_small_Cl hm hh0 hh1 sCl) hlk' (CL.aOf_eq p (Xs k) N)).trans (le_max_left _ _)
  have hk0 : (0 : ℝ) ≤ (k : ℕ) := Nat.cast_nonneg _
  have hsqk : 0 < Real.sqrt (1 + ((k : ℕ) : ℝ)) := Real.sqrt_pos.mpr (by linarith)
  -- one seam row
  have seam : ∀ n, n ∈ softWindow CL p (Xs k) N → |CL.Zof p (Xs k) N n| ≤ Real.sqrt (max (-a) 0) + Cp * Real.sqrt (Fz.step N) →
      Cp * Real.sqrt (Fz.step N) ≤ 2 / 5 →
      softVec CL CR p (Xs k) N n ^ 2 ≤ (K ^ 2 / cn) * Real.sqrt (Fz.step N) * (2 * (Real.sqrt (1 + ((k : ℕ) : ℝ)))⁻¹) := by
    intro n hn hZ hCps
    have hMn := mbal_seam a (CL.Zof p (Xs k) N n) (k : ℕ) hkA hk0
      (fun hA1' => mflat_seam_z hA1' (by linarith only [hZ, hCps]))
    have hnum : |softNum CL CR p (Xs k) N n| ≤ K * (T * Mbal a (CL.Zof p (Xs k) N n)) := by
      have h3 := E3 n hn
      unfold softNum
      by_cases hz : CL.Zof p (Xs k) N n ≤ 0
      · rw [ite_eq_left hz]
        linarith only [h3, mul_nonneg (abs_nonneg (softKappa CL CR p (Xs k) N)) (abs_nonneg (softSeqR CR p (Xs k) N n))]
      · rw [ite_eq_right hz, abs_mul]
        linarith only [h3, abs_nonneg (CL.psiHatL p (Xs k) N n)]
    have hvec : softVec CL CR p (Xs k) N n = softNum CL CR p (Xs k) N n / softNorm CL CR p (Xs k) N :=
      softVec_eq CL CR _ _ _ _
    rw [hvec, div_pow]
    exact (mflat_quot_sq hh0 hT hcn hnum E5).trans
      (mul_le_mul_of_nonneg_left hMn (mul_nonneg (div_nonneg (sq_nonneg K) hcn.le) (Real.sqrt_nonneg _)))
  obtain ⟨hn0W, hn1W, hZ0, hZ1, hCps⟩ := Hp p hp (Xs k) hX N hN1 sp ha nc hnc
  have s0 := seam nc hn0W hZ0 hCps
  have s1 := seam (nc + 1) hn1W hZ1 hCps
  have hrp : (1 + ((k : ℕ) : ℝ)) ^ (-(1 : ℝ) / 2) = (Real.sqrt (1 + ((k : ℕ) : ℝ)))⁻¹ := rpow_half_eq (by linarith)
  rw [hrp]
  have hinv : 0 ≤ (Real.sqrt (1 + ((k : ℕ) : ℝ)))⁻¹ := inv_nonneg.mpr hsqk.le
  have hfin : 4 * K ^ 2 / cn ≤ max Cf (4 * K ^ 2 / cn) := le_max_right _ _
  calc _ ≤ (K ^ 2 / cn) * Real.sqrt (Fz.step N) * (2 * (Real.sqrt (1 + ((k : ℕ) : ℝ)))⁻¹) +
        (K ^ 2 / cn) * Real.sqrt (Fz.step N) * (2 * (Real.sqrt (1 + ((k : ℕ) : ℝ)))⁻¹) := add_le_add s0 s1
    _ = (4 * K ^ 2 / cn) * Real.sqrt (Fz.step N) * (Real.sqrt (1 + ((k : ℕ) : ℝ)))⁻¹ := by ring
    _ ≤ max Cf (4 * K ^ 2 / cn) * Real.sqrt (Fz.step N) * (Real.sqrt (1 + ((k : ℕ) : ℝ)))⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfin hsq0) hinv

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.propThaMflat_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms propThaMflat_proved

end Main

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.mbal_seam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mbal_seam

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.Zof_succ_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Zof_succ_le

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.row_mem_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms row_mem_near

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.fold_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fold_pair


end FormalResearch.JacobiEigenvectors.TheoremB

end
