module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftTails

/-!
# Paper J, Layer 2 (L2.C7): the parabolic-cylinder tail beyond the Airy layer (chain step E6 (i) of `PLAN.md`), `app_thmA` Step 4 (d) (i)

Source: `app_thmA.tex`, "The soft edges: proof of Proposition prop:tha-W2", Step 4 (d) (i) of `(S4tail)`: the parabolic-cylinder sites with
`|u_n - u_c| < eta/2` and `|Z_n| > rho`, `rho = rhoWin(a)` (eq:tha-winnot).

## The exact chain of lemmas (written before the proofs; every hypothesis is listed)

Notation: `a = aOf`, `A = max(-a,0)`, `rho = rhoWin a = 2 sqrt A + (1+A)^{-1/6}`, `g = rho^2/4 + a`, `gamma = sqrt g`, `c = dm sqrt h` (`h = step N`),
`x_n = u_n - u_c`, `Z_n = Zof n`, `E = Eminus a`, `M = Mbal a` (`M(a,z) = k_2(a,z)^{-1/4}`).  The left block is `B_L = {n in [0,N] : |x_n| < eta/2, Z_n < -rho}`.

* **T3.0 (margin).**  `rhoWin_margin`: `(1+A)^{1/3}/8 <= g` and `0 <= rho`.  Hypotheses: none (real arithmetic; `r = (1+A)^{1/6}`, `r^6 = 1+A`).
* **T3.1 (weight of `M`).**  `Mbal_sq_le`: `0 < g <= z^2/4 + a` gives `M(a,z)^2 <= gamma^{-1}`.  `Mbal_neg`: `M(a,-z) = M(a,z)`.  No hypotheses.
* **T3.2 (consecutive sites).**  `Zof_incr`: for rows `j <= k` with `|x_j|, |x_k| <= eta/2` (so both lie in the chart `|x| <= 2 eta`):
  `dm (k-j) sqrt h <= Z_k - Z_j`, hence `Zof_le`: `Z_j <= Z_k`.  Hypotheses: `mu in P`, `|X - X_s^+| <= delta_0`, `zeta_deriv` (through `zeta_mvt`).
* **T3.3 (geometric decay of the weight).**  `chain_decay`: if `gamma^2 <= z^2/4 + a` for all `z <= -rho`, `Z` is monotone on `[n0, T]` and `Z_T <= -rho`, then
  `E(Z_n) <= exp(-gamma (Z_T - Z_n)) E(Z_T)` for `n0 <= n <= T` (induction; `Eminus_decay` for each consecutive pair).
* **T3.4 (geometric sum).**  `sum_geom_block`: rows `n <= T` with `T - n <= K` and `0 <= e_n <= q^{T-n}` give `sum e <= 1/(1-q)`.  `inv_one_sub_exp_le`: `1/(1-exp(-x)) <= 1 + 1/x`.
* **T3.5 (left block) `pc_tail_left`.**  With `T = max B_L`, `q = exp(-2 gamma c)`: `E(Z_n)^2 <= q^{T-n}` (T3.2, T3.3, `E <= 1`), so by T3.1
  `sum_{B_L} (E M)^2 <= gamma^{-1} (1 + 1/(2 gamma c)) = gamma^{-1} + 1/(2 g c)`.  With `gamma^{-1} <= 3` (`g >= 1/8`) and `g >= (1+A)^{1/3}/8`:
  `sum_{B_L} (E M)^2 <= 3 + (4/dm) (1+A)^{-1/3} h^{-1/2}`.  (Order `(1+A)^{-1/3} h^{-1/2}` of the paper's (S4tail) (i).)
* **T3.6 (right block) `pc_tail_right`.**  The right sites `Z_n > rho` are the left sites of the mirror chart: `Zof_mirror` (`Z^R_{N-n} = -Z_n`), `aOf_mirror`,
  `uNode_mirror` (`|x^R_{N-n}| = |x_n|`), `Mbal_neg`, and the reindexing `n -> N - n` (`Finset.sum_nbij'`).  Constant `4/CR.dm` (the mirror chart's own `dm`).

## Differences from the paper

* The split at `|x_n| = eta/4` with a crude bound `E <= exp(-c/h)` on `eta/4 <= |x_n|` (in the plan of `SoftTails.lean`, T3) is **not needed**: `zeta_deriv`
  gives `zeta' >= d_-` on all of `|x| <= 2 eta`, so consecutive sites with `|x| < eta/2` satisfy the geometric step bound.  The tail is summed in one block.
* The Riemann-sum comparison of the paper (`f` monotone, `sum f(Z_n) <= 1 + (d_- sqrt h)^{-1} int f`) is replaced by the geometric sum over consecutive sites (as the plan says);
  it gives the same order `(1+A)^{-1/3} h^{-1/2}`, with the explicit constants `3` and `4/dm`.
* The weight is stated for `E M` (the factor `|lam_L| kappa_bal^{-1}` of `softEnv` and the premise constant are not part of this file).

## Proved here

`margin_aux`, `rhoWin_margin`, `Mbal_sq_le`, `Mbal_neg`, `chain_decay`, `sum_geom_block`, `inv_one_sub_exp_le`, `Zof_incr`, `Zof_le`, `pc_tail_left`, `pc_tail_right`.  Axioms pinned at the end of the file for the headline results `pc_tail_left`, `pc_tail_right`, and for `rhoWin_margin`, `chain_decay`, `sum_geom_block`, `Mbal_sq_le`; the other lemmas are auxiliary to these.

## Not formalised

* The relative form `(S4tail)` (the whole tail against the window mass `m_Omega`): needs the window mass lower bound `m_Omega >= c h^{-1/2}` (`PropThaWin`, E4) and the Weber tails `T1`, `T2`;
  and the identity of `softEnv` with the envelope `V_n` on these sites (T4 `softEnv_eq`).  Not done here.
* The soft-edge `PropThaWin` inputs (`rho`-window masses); not used.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

/-! ### T3.0: the margin `rho^2/4 + a >= (1+A)^{1/3}/8` -/

/-- The margin for `a <= 0` (`A = -a`, the proof with `r = (1+A)^{1/6}`, `r^6 = 1 + A`, `sigma = sqrt A`). -/
lemma margin_aux (A : ℝ) (hA : 0 ≤ A) :
    (1 + A) ^ ((1 : ℝ) / 3) / 8 ≤ (2 * Real.sqrt A + (1 + A) ^ (-(1 : ℝ) / 6)) ^ 2 / 4 - A ∧
      0 ≤ 2 * Real.sqrt A + (1 + A) ^ (-(1 : ℝ) / 6) := by
  have hA1 : 0 < 1 + A := by linarith
  have hr0 : 0 < (1 + A) ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hA1 _
  have hr6 : ((1 + A) ^ ((1 : ℝ) / 6)) ^ 6 = 1 + A := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA1.le]; norm_num
  have hr3 : (1 + A) ^ ((1 : ℝ) / 3) = ((1 + A) ^ ((1 : ℝ) / 6)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA1.le]; norm_num
  have hrneg : (1 + A) ^ (-(1 : ℝ) / 6) = ((1 + A) ^ ((1 : ℝ) / 6))⁻¹ := by
    rw [neg_div, Real.rpow_neg hA1.le]
  have hr1 : 1 ≤ (1 + A) ^ ((1 : ℝ) / 6) := Real.one_le_rpow (by linarith) (by norm_num)
  rw [hr3, hrneg]
  generalize hr : (1 + A) ^ ((1 : ℝ) / 6) = r at hr0 hr6 hr1 ⊢
  have hσ2 : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA
  have hσ0 : 0 ≤ Real.sqrt A := Real.sqrt_nonneg _
  generalize hσ : Real.sqrt A = σ at hσ2 hσ0 ⊢
  have key : r ^ 4 ≤ 8 * r * σ + 2 := by
    rcases le_total (r ^ 4) 2 with h2 | h2
    · nlinarith [mul_nonneg hr0.le hσ0]
    · have hr2 : 1 ≤ r ^ 2 := by nlinarith
      have h6 : 2 ≤ r ^ 6 := by nlinarith [mul_nonneg (sub_nonneg.mpr h2) (sq_nonneg r)]
      have hAeq : A = r ^ 6 - 1 := by linarith
      have hsq : (r ^ 4) ^ 2 ≤ (8 * r * σ) ^ 2 := by
        have e : (8 * r * σ) ^ 2 = 64 * r ^ 2 * (r ^ 6 - 1) := by
          rw [show (8 * r * σ) ^ 2 = 64 * r ^ 2 * σ ^ 2 by ring, hσ2, hAeq]
        rw [e]
        nlinarith [mul_nonneg (sq_nonneg r) (show (0 : ℝ) ≤ 63 * r ^ 6 - 64 by linarith)]
      nlinarith [mul_nonneg hr0.le hσ0]
  have e3 : (2 * σ + r⁻¹) ^ 2 / 4 - A = σ * r⁻¹ + (r⁻¹) ^ 2 / 4 := by
    linear_combination hσ2
  have e4 : σ * r⁻¹ + (r⁻¹) ^ 2 / 4 = (8 * r * σ + 2) / (8 * r ^ 2) := by
    field_simp; ring
  have e5 : r ^ 2 / 8 = r ^ 4 / (8 * r ^ 2) := by
    field_simp
  constructor
  · rw [e3, e4, e5]
    exact div_le_div_of_nonneg_right key (by positivity)
  · have : 0 < r⁻¹ := inv_pos.mpr hr0
    linarith

/-- The margin `(1+A)^{1/3}/8 <= rho^2/4 + a` and `rho >= 0`, `A = max(-a,0)`, `rho = rhoWin a`. -/
lemma rhoWin_margin (a : ℝ) :
    (1 + max (-a) 0) ^ ((1 : ℝ) / 3) / 8 ≤ rhoWin a ^ 2 / 4 + a ∧ 0 ≤ rhoWin a := by
  rcases le_total a 0 with ha | ha
  · have hm : max (-a) 0 = -a := max_eq_left (by linarith)
    have h := margin_aux (-a) (by linarith)
    unfold rhoWin
    rw [hm]
    exact ⟨by linarith [h.1], h.2⟩
  · have hm : max (-a) 0 = 0 := max_eq_right (by linarith)
    unfold rhoWin
    rw [hm]
    refine ⟨?_, ?_⟩
    · norm_num
      linarith
    · norm_num

/-! ### T3.1: the weight `M_bal` -/

/-- `M_bal(a,Z)^2 <= g^{-1/2} = (sqrt g)^{-1}` when `g <= Z^2/4 + a` and `g > 0`. -/
lemma Mbal_sq_le (a z g : ℝ) (hg : 0 < g) (hz : g ≤ z ^ 2 / 4 + a) : Mbal a z ^ 2 ≤ (Real.sqrt g)⁻¹ := by
  have hk : g ≤ k2 a z := by
    unfold k2
    exact le_trans hz (le_trans (le_abs_self _) (le_max_left _ _))
  unfold Mbal
  have h1 : k2 a z ^ (-(1 : ℝ) / 4) ≤ g ^ (-(1 : ℝ) / 4) := Real.rpow_le_rpow_of_nonpos hg hk (by norm_num)
  have hk0 : 0 ≤ k2 a z ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg (le_trans hg.le hk) _
  have h2 : (k2 a z ^ (-(1 : ℝ) / 4)) ^ 2 ≤ (g ^ (-(1 : ℝ) / 4)) ^ 2 := pow_le_pow_left₀ hk0 h1 2
  have h3 : (g ^ (-(1 : ℝ) / 4)) ^ 2 = (Real.sqrt g)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hg.le, Real.sqrt_eq_rpow, ← Real.rpow_neg hg.le]
    norm_num
  rw [h3] at h2
  exact h2

/-- `M_bal` is even in `Z`. -/
lemma Mbal_neg (a z : ℝ) : Mbal a (-z) = Mbal a z := by
  unfold Mbal k2
  rw [neg_sq]

/-! ### T3.3, T3.4: geometric decay and the geometric sum -/

/-- **T3.3** geometric decay of the weight along consecutive rows, towards the reference row `T`. -/
lemma chain_decay (a γ ρ : ℝ) (hρ : 0 ≤ ρ) (hγ : 0 ≤ γ) (hg : ∀ z : ℝ, z ≤ -ρ → γ ^ 2 ≤ z ^ 2 / 4 + a)
    (Zf : ℤ → ℝ) (n0 T : ℤ) (hT : Zf T ≤ -ρ) (hmono : ∀ j, n0 ≤ j → j ≤ T → Zf j ≤ Zf T)
    (hstep : ∀ j, n0 ≤ j → j + 1 ≤ T → Zf j ≤ Zf (j + 1)) :
    ∀ k : ℕ, ∀ n : ℤ, n0 ≤ n → n + (k : ℤ) = T →
      Eminus a (Zf n) ≤ Real.exp (-(γ * (Zf T - Zf n))) * Eminus a (Zf T) := by
  intro k
  induction k with
  | zero =>
    intro n _ hn
    have hnT : n = T := by simpa using hn
    subst hnT
    simp
  | succ k ih =>
    intro n hn0 hn
    push_cast at hn
    have hIH := ih (n + 1) (by omega) (by omega)
    have hZle : Zf n ≤ Zf (n + 1) := hstep n hn0 (by omega)
    have hZ1 : Zf (n + 1) ≤ -ρ := (hmono (n + 1) (by omega) (by omega)).trans hT
    have hZ1' : Zf (n + 1) ≤ 0 := hZ1.trans (by linarith)
    have hdec := Eminus_decay a γ hZle hZ1' hγ (hg (Zf (n + 1)) hZ1)
    calc Eminus a (Zf n) ≤ Real.exp (-(γ * (Zf (n + 1) - Zf n))) * Eminus a (Zf (n + 1)) := hdec
      _ ≤ Real.exp (-(γ * (Zf (n + 1) - Zf n))) * (Real.exp (-(γ * (Zf T - Zf (n + 1)))) * Eminus a (Zf T)) :=
          mul_le_mul_of_nonneg_left hIH (Real.exp_pos _).le
      _ = Real.exp (-(γ * (Zf T - Zf n))) * Eminus a (Zf T) := by
          rw [← mul_assoc, ← Real.exp_add]
          congr 2
          ring

/-- **T3.4** a geometric sum over rows `n <= T` with `T - n <= K`. -/
lemma sum_geom_block (S : Finset ℤ) (T K : ℤ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (e : ℤ → ℝ)
    (hS : ∀ n ∈ S, n ≤ T ∧ T - n ≤ K) (he : ∀ n ∈ S, 0 ≤ e n ∧ e n ≤ q ^ (T - n).toNat) :
    ∑ n ∈ S, e n ≤ 1 / (1 - q) := by
  have hinj : Set.InjOn (fun n : ℤ => (T - n).toNat) (S : Set ℤ) := by
    intro x hx y hy hxy
    have h1 := hS x hx
    have h2 := hS y hy
    simp only at hxy
    omega
  calc ∑ n ∈ S, e n ≤ ∑ n ∈ S, q ^ (T - n).toNat := Finset.sum_le_sum (fun n hn => (he n hn).2)
    _ = ∑ k ∈ S.image (fun n : ℤ => (T - n).toNat), q ^ k := (Finset.sum_image hinj).symm
    _ ≤ ∑ k ∈ Finset.range (K.toNat + 1), q ^ k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          rw [Finset.mem_image] at hk
          obtain ⟨n, hn, rfl⟩ := hk
          have h1 := hS n hn
          rw [Finset.mem_range]
          omega
        · intro k _ _
          exact pow_nonneg hq0 k
    _ ≤ 1 / (1 - q) := by
        have := geom_sum_Ico_le_of_lt_one (m := 0) (n := K.toNat + 1) hq0 hq1
        rw [← Finset.range_eq_Ico] at this
        simpa using this

/-- **T3.4'** `1/(1 - exp(-x)) <= 1 + 1/x` for `x > 0`. -/
lemma inv_one_sub_exp_le (x : ℝ) (hx : 0 < x) : 1 / (1 - Real.exp (-x)) ≤ 1 + 1 / x := by
  have hexp : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have hadd := Real.add_one_le_exp x
  have h1 : Real.exp (-x) * (1 + x) ≤ 1 :=
    calc Real.exp (-x) * (1 + x) ≤ Real.exp (-x) * Real.exp x :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = 1 := hexp
  have hlt : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hq1 : 0 < 1 - Real.exp (-x) := by linarith
  rw [div_le_iff₀ hq1]
  have key : (1 + 1 / x) * (1 - Real.exp (-x)) - 1 = (1 - Real.exp (-x) * (1 + x)) / x := by
    field_simp
    ring
  have hnn : 0 ≤ (1 - Real.exp (-x) * (1 + x)) / x := div_nonneg (by linarith) hx.le
  linarith

/-! ### T3.2: consecutive sites of the chart -/

section PCTail

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (C : SoftEdgeChart Fz P m q U V Lm)

/-- **T3.2** for rows `j <= k` with `|x_j|, |x_k| <= eta/2`: `dm (k-j) sqrt h <= Z_k - Z_j`. -/
lemma Zof_incr {μ : Par × ℝ} (hμ : μ ∈ P) {X : ℝ} (hX : |X - Fz.bandHi μ| ≤ C.δ0) (N : ℕ) {j k : ℤ}
    (hjk : j ≤ k) (hj : |uNode (Fz.step N) j - C.uc μ| ≤ C.η / 2)
    (hk : |uNode (Fz.step N) k - C.uc μ| ≤ C.η / 2) :
    C.dm * ((k : ℝ) - j) * Real.sqrt (Fz.step N) ≤ C.Zof μ X N k - C.Zof μ X N j := by
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hs : 0 < Real.sqrt (Fz.step N) := Real.sqrt_pos.mpr hh0
  have hsq : Real.sqrt (Fz.step N) * Real.sqrt (Fz.step N) = Fz.step N := Real.mul_self_sqrt hh0.le
  have hα : |Fz.bandHi μ - X| ≤ C.δ0 := by rw [abs_sub_comm]; exact hX
  have hj' := abs_le.mp hj
  have hk' := abs_le.mp hk
  have hη := C.consts_pos.2.1
  have hdm := C.consts_pos.2.2.1
  have hjkR : (j : ℝ) ≤ k := by exact_mod_cast hjk
  have hxk : uNode (Fz.step N) k - uNode (Fz.step N) j = ((k : ℝ) - j) * Fz.step N := by
    unfold uNode; ring
  have hnn : 0 ≤ ((k : ℝ) - j) * Fz.step N := mul_nonneg (by linarith) hh0.le
  have hmv := C.zeta_mvt hμ hα (x1 := uNode (Fz.step N) j - C.uc μ) (x2 := uNode (Fz.step N) k - C.uc μ)
    (by linarith) (by linarith) (by linarith)
  have e : C.dm * ((k : ℝ) - j) * Real.sqrt (Fz.step N) * Real.sqrt (Fz.step N) =
      C.dm * ((uNode (Fz.step N) k - C.uc μ) - (uNode (Fz.step N) j - C.uc μ)) := by
    rw [mul_assoc, hsq]
    unfold uNode
    ring
  unfold SoftEdgeChart.Zof
  rw [← sub_div, le_div_iff₀ hs, e]
  exact hmv.1

/-- **T3.2'** `Z_j <= Z_k` for rows `j <= k` with `|x_j|, |x_k| <= eta/2`. -/
lemma Zof_le {μ : Par × ℝ} (hμ : μ ∈ P) {X : ℝ} (hX : |X - Fz.bandHi μ| ≤ C.δ0) (N : ℕ) {j k : ℤ}
    (hjk : j ≤ k) (hj : |uNode (Fz.step N) j - C.uc μ| ≤ C.η / 2)
    (hk : |uNode (Fz.step N) k - C.uc μ| ≤ C.η / 2) :
    C.Zof μ X N j ≤ C.Zof μ X N k := by
  have h := Zof_incr C hμ hX N hjk hj hk
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hs : 0 < Real.sqrt (Fz.step N) := Real.sqrt_pos.mpr hh0
  have hdm := C.consts_pos.2.2.1
  have hjkR : (j : ℝ) ≤ k := by exact_mod_cast hjk
  have : 0 ≤ C.dm * ((k : ℝ) - j) * Real.sqrt (Fz.step N) :=
    mul_nonneg (mul_nonneg hdm.le (by linarith)) hs.le
  linarith

end PCTail

/-! ### T3.5: the left block -/

section PCTailLeft

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (C : SoftEdgeChart Fz P m q U V Lm)

/-- **T3.5 (left block).**  The sites `|u_n - u_c| < eta/2`, `Z_n < -rho(a)` (the left parabolic-cylinder tail beyond the Airy layer):
`sum (E_-(a,Z_n) M_bal(a,Z_n))^2 <= 3 + (4/dm) (1+A)^{-1/3} h^{-1/2}`, `A = max(-a,0)`. -/
theorem pc_tail_left {μ : Par × ℝ} (hμ : μ ∈ P) {X : ℝ} (hX : |X - Fz.bandHi μ| ≤ C.δ0) (N : ℕ) :
    ∑ n ∈ (rowsOf N).filter (fun n => |uNode (Fz.step N) n - C.uc μ| < C.η / 2 ∧
        C.Zof μ X N n < -rhoWin (C.aOf μ X N)),
      (Eminus (C.aOf μ X N) (C.Zof μ X N n) * Mbal (C.aOf μ X N) (C.Zof μ X N n)) ^ 2 ≤
    3 + 4 / C.dm * ((1 + max (-(C.aOf μ X N)) 0) ^ ((1 : ℝ) / 3))⁻¹ / Real.sqrt (Fz.step N) := by
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hs : 0 < Real.sqrt (Fz.step N) := Real.sqrt_pos.mpr hh0
  have hdm := C.consts_pos.2.2.1
  have hη := C.consts_pos.2.1
  obtain ⟨hmarg, hρ0⟩ := rhoWin_margin (C.aOf μ X N)
  set a := C.aOf μ X N with ha
  set ρ := rhoWin a with hρ
  set rr := (1 + max (-a) 0) ^ ((1 : ℝ) / 3) with hrr
  have hrr1 : 1 ≤ rr := Real.one_le_rpow (by have := le_max_right (-a) 0; linarith) (by norm_num)
  set g := ρ ^ 2 / 4 + a with hg
  have hg0 : 0 < g := by linarith
  set γ := Real.sqrt g with hγ
  have hγpos : 0 < γ := Real.sqrt_pos.mpr hg0
  have hγ2 : γ ^ 2 = g := Real.sq_sqrt hg0.le
  set c := C.dm * Real.sqrt (Fz.step N) with hc
  have hcpos : 0 < c := mul_pos hdm hs
  have hgam : ∀ z : ℝ, z ≤ -ρ → γ ^ 2 ≤ z ^ 2 / 4 + a := by
    intro z hz
    rw [hγ2, hg]
    have : ρ ^ 2 ≤ z ^ 2 := by nlinarith
    linarith
  set B := (rowsOf N).filter (fun n => |uNode (Fz.step N) n - C.uc μ| < C.η / 2 ∧ C.Zof μ X N n < -ρ) with hB
  have hmemB : ∀ n, n ∈ B ↔ (0 ≤ n ∧ n ≤ (N : ℤ)) ∧ |uNode (Fz.step N) n - C.uc μ| < C.η / 2 ∧
      C.Zof μ X N n < -ρ := by
    intro n
    rw [hB, Finset.mem_filter, rowsOf, Finset.mem_Icc]
  have hRHS0 : 0 ≤ 3 + 4 / C.dm * rr⁻¹ / Real.sqrt (Fz.step N) := by
    have : 0 < rr⁻¹ := inv_pos.mpr (by linarith)
    have : 0 ≤ 4 / C.dm * rr⁻¹ := mul_nonneg (div_nonneg (by norm_num) hdm.le) this.le
    have : 0 ≤ 4 / C.dm * rr⁻¹ / Real.sqrt (Fz.step N) := div_nonneg this hs.le
    linarith
  -- empty block
  rcases B.eq_empty_or_nonempty with hE | hne
  · have : (rowsOf N).filter (fun n => |uNode (Fz.step N) n - C.uc μ| < C.η / 2 ∧
        C.Zof μ X N n < -rhoWin (C.aOf μ X N)) = ∅ := hE
    rw [hE, Finset.sum_empty]
    exact hRHS0
  set T := B.max' hne with hT
  have hTB : T ∈ B := Finset.max'_mem B hne
  have hTle : ∀ n ∈ B, n ≤ T := fun n hn => Finset.le_max' B n hn
  obtain ⟨hTrows, hTx, hTZ⟩ := (hmemB T).mp hTB
  have hTN : T ≤ (N : ℤ) := hTrows.2
  have hTZ' : C.Zof μ X N T ≤ -ρ := hTZ.le
  have hTZ0 : C.Zof μ X N T ≤ 0 := hTZ'.trans (by linarith)
  -- monotone on the block between a row and `T`
  have hbetween : ∀ n ∈ B, ∀ j : ℤ, n ≤ j → j ≤ T → |uNode (Fz.step N) j - C.uc μ| ≤ C.η / 2 := by
    intro n hn j hnj hjT
    obtain ⟨-, hxn, -⟩ := (hmemB n).mp hn
    obtain ⟨-, hxT, -⟩ := (hmemB T).mp hTB
    have h1 := SoftEdgeChart.uNode_mono_le (h := Fz.step N) hh0.le hnj
    have h2 := SoftEdgeChart.uNode_mono_le (h := Fz.step N) hh0.le hjT
    have hxn' := abs_le.mp hxn.le
    have hxT' := abs_le.mp hxT.le
    rw [abs_le]
    constructor <;> linarith [hxn'.1, hxT'.2]
  -- the sum over the geometric block
  set q' := Real.exp (-(2 * γ * c)) with hq'
  have hq0 : 0 ≤ q' := (Real.exp_pos _).le
  have hq1 : q' < 1 := Real.exp_lt_one_iff.mpr (by have : 0 < 2 * γ * c := mul_pos (mul_pos two_pos hγpos) hcpos; linarith)
  have hpt : ∀ n ∈ B, Eminus a (C.Zof μ X N n) ^ 2 ≤ q' ^ (T - n).toNat ∧ 0 ≤ Eminus a (C.Zof μ X N n) ^ 2 := by
    intro n hn
    have hnT := hTle n hn
    obtain ⟨⟨hn0, -⟩, -, hZn⟩ := (hmemB n).mp hn
    have hchain := chain_decay a γ ρ hρ0 hγpos.le hgam (fun j => C.Zof μ X N j) n T hTZ'
      (fun j hj1 hj2 => Zof_le C hμ hX N hj2 (hbetween n hn j hj1 hj2) (hbetween n hn T hnT le_rfl))
      (fun j hj1 hj2 => Zof_le C hμ hX N (by omega) (hbetween n hn j hj1 (by omega)) (hbetween n hn (j + 1) (by omega) hj2))
      (T - n).toNat n le_rfl (by omega)
    have hEn := hchain
    have hET : Eminus a (C.Zof μ X N T) ≤ 1 := Eminus_le_one a hTZ0
    have hincr := Zof_incr C hμ hX N hnT (hbetween n hn n le_rfl (by omega)) (hbetween n hn T hnT le_rfl)
    have hkR : ((T : ℝ) - (n : ℝ)) = (((T - n).toNat : ℕ) : ℝ) := by
      have : (((T - n).toNat : ℕ) : ℤ) = T - n := by omega
      have h' : ((((T - n).toNat : ℕ) : ℤ) : ℝ) = ((T : ℤ) : ℝ) - ((n : ℤ) : ℝ) := by
        rw [this]; push_cast; ring
      exact_mod_cast h'.symm
    set k := (T - n).toNat with hk
    have hincr' : c * (k : ℝ) ≤ C.Zof μ X N T - C.Zof μ X N n := by
      rw [hc, ← hkR]
      have : C.dm * ((T : ℝ) - n) * Real.sqrt (Fz.step N) = C.dm * Real.sqrt (Fz.step N) * ((T : ℝ) - n) := by ring
      linarith [hincr]
    have hexpo : Real.exp (-(γ * (C.Zof μ X N T - C.Zof μ X N n))) ≤ Real.exp (-(γ * c * (k : ℝ))) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hincr' hγpos.le
      linarith [this]
    have hEn1 : Eminus a (C.Zof μ X N n) ≤ Real.exp (-(γ * c * (k : ℝ))) := by
      calc Eminus a (C.Zof μ X N n) ≤ Real.exp (-(γ * (C.Zof μ X N T - C.Zof μ X N n))) * Eminus a (C.Zof μ X N T) := hEn
        _ ≤ Real.exp (-(γ * c * (k : ℝ))) * 1 :=
            mul_le_mul (hexpo) hET (Eminus_pos _ _).le (Real.exp_pos _).le
        _ = Real.exp (-(γ * c * (k : ℝ))) := mul_one _
    have hsq : Real.exp (-(γ * c * (k : ℝ))) ^ 2 = q' ^ k := by
      rw [hq', ← Real.exp_nat_mul, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    refine ⟨?_, sq_nonneg _⟩
    rw [← hsq]
    exact pow_le_pow_left₀ (Eminus_pos _ _).le hEn1 2
  have hsumE : ∑ n ∈ B, Eminus a (C.Zof μ X N n) ^ 2 ≤ 1 / (1 - q') := by
    apply sum_geom_block B T (N : ℤ) q' hq0 hq1 (fun n => Eminus a (C.Zof μ X N n) ^ 2)
    · intro n hn
      have := (hmemB n).mp hn
      exact ⟨hTle n hn, by have := this.1.1; omega⟩
    · intro n hn
      exact ⟨(hpt n hn).2, (hpt n hn).1⟩
  have hsumM : ∑ n ∈ B, (Eminus a (C.Zof μ X N n) * Mbal a (C.Zof μ X N n)) ^ 2 ≤
      γ⁻¹ * ∑ n ∈ B, Eminus a (C.Zof μ X N n) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hZn : g ≤ C.Zof μ X N n ^ 2 / 4 + a := by
      have := (hmemB n).mp hn
      have hz := this.2.2
      have : ρ ^ 2 ≤ C.Zof μ X N n ^ 2 := by nlinarith
      rw [hg]; linarith
    have hM : Mbal a (C.Zof μ X N n) ^ 2 ≤ γ⁻¹ := Mbal_sq_le a (C.Zof μ X N n) g hg0 hZn
    calc (Eminus a (C.Zof μ X N n) * Mbal a (C.Zof μ X N n)) ^ 2
        = Eminus a (C.Zof μ X N n) ^ 2 * Mbal a (C.Zof μ X N n) ^ 2 := mul_pow _ _ _
      _ ≤ Eminus a (C.Zof μ X N n) ^ 2 * γ⁻¹ := mul_le_mul_of_nonneg_left hM (sq_nonneg _)
      _ = γ⁻¹ * Eminus a (C.Zof μ X N n) ^ 2 := mul_comm _ _
  -- the geometric factor `1/(1-q') <= 1 + 1/(2 gamma c)`
  have hgeo : 1 / (1 - q') ≤ 1 + 1 / (2 * γ * c) := inv_one_sub_exp_le (2 * γ * c) (mul_pos (mul_pos two_pos hγpos) hcpos)
  have hγinv : γ⁻¹ ≤ 3 := by
    have h1 : (1 / 3 : ℝ) ≤ γ := by nlinarith
    rw [inv_le_comm₀ hγpos (by norm_num)]
    linarith
  -- the closing algebra
  have hfin1 : γ⁻¹ * (1 + 1 / (2 * γ * c)) = γ⁻¹ + 1 / (2 * g * c) := by
    rw [← hγ2]
    field_simp
  have hfin2 : 1 / (2 * g * c) ≤ 4 / C.dm * rr⁻¹ / Real.sqrt (Fz.step N) := by
    have hgl : rr / 8 ≤ g := hmarg
    have hrr0 : 0 < rr := by linarith
    have h1 : 1 / (2 * g * c) ≤ 1 / (2 * (rr / 8) * c) := by
      apply one_div_le_one_div_of_le
      · exact mul_pos (by positivity) hcpos
      · exact mul_le_mul_of_nonneg_right (by linarith) hcpos.le
    have h2 : 1 / (2 * (rr / 8) * c) = 4 / C.dm * rr⁻¹ / Real.sqrt (Fz.step N) := by
      rw [hc]
      field_simp
      ring
    linarith [h1, h2]
  calc ∑ n ∈ (rowsOf N).filter (fun n => |uNode (Fz.step N) n - C.uc μ| < C.η / 2 ∧
          C.Zof μ X N n < -rhoWin (C.aOf μ X N)),
        (Eminus (C.aOf μ X N) (C.Zof μ X N n) * Mbal (C.aOf μ X N) (C.Zof μ X N n)) ^ 2
      = ∑ n ∈ B, (Eminus a (C.Zof μ X N n) * Mbal a (C.Zof μ X N n)) ^ 2 := rfl
    _ ≤ γ⁻¹ * ∑ n ∈ B, Eminus a (C.Zof μ X N n) ^ 2 := hsumM
    _ ≤ γ⁻¹ * (1 + 1 / (2 * γ * c)) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hγpos.le)
        exact hsumE.trans hgeo
    _ = γ⁻¹ + 1 / (2 * g * c) := hfin1
    _ ≤ 3 + 4 / C.dm * rr⁻¹ / Real.sqrt (Fz.step N) := by linarith [hfin2, hγinv]

end PCTailLeft

/-! ### T3.6: the right block, as the left block of the mirror chart -/

section PCTailRight

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  {CL : SoftEdgeChart Fz P m q U V Lm} {CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm}

/-- **T3.6 (right block).**  The sites `|u_n - u_c| < eta/2`, `Z_n > rho(a)`: `sum (E_-(a,-Z_n) M_bal(a,Z_n))^2 <= 3 + (4/dm_R)(1+A)^{-1/3} h^{-1/2}`
(`dm_R` the mirror chart's `dm`).  The right sites are the left sites of the mirror chart, row `N - n` (`Zof_mirror`, `aOf_mirror`, `uNode_mirror`). -/
theorem pc_tail_right (hM : SoftMirror CL CR) {μ : Par × ℝ} (hμ : μ ∈ P) {X : ℝ} (hX : |X - Fz.bandHi μ| ≤ CL.δ0)
    (N : ℕ) :
    ∑ n ∈ (rowsOf N).filter (fun n => |uNode (Fz.step N) n - CL.uc μ| < CL.η / 2 ∧
        rhoWin (CL.aOf μ X N) < CL.Zof μ X N n),
      (Eminus (CL.aOf μ X N) (-CL.Zof μ X N n) * Mbal (CL.aOf μ X N) (CL.Zof μ X N n)) ^ 2 ≤
    3 + 4 / CR.dm * ((1 + max (-(CL.aOf μ X N)) 0) ^ ((1 : ℝ) / 3))⁻¹ / Real.sqrt (Fz.step N) := by
  have hδ : CR.δ0 = CL.δ0 := hM.2.2.2.2.1
  have hηe : CR.η = CL.η := hM.2.2.2.1
  have huc : CR.uc μ = Fz.L - CL.uc μ := hM.1 μ hμ
  have hX' : |X - (mirrorFamily Fz).bandHi μ| ≤ CR.δ0 := by
    rw [bandHi_mirror, hδ]; exact hX
  have H := pc_tail_left CR hμ hX' N
  rw [aOf_mirror hM hμ X N] at H
  have hL := step_mul_succ Fz N
  have hrefl : ∀ n : ℤ, uNode (Fz.step N) ((N : ℤ) - n) = Fz.L - uNode (Fz.step N) n :=
    fun n => uNode_mirror Fz.L (Fz.step N) N n hL
  have hsum : ∑ n ∈ (rowsOf N).filter (fun n => |uNode (Fz.step N) n - CL.uc μ| < CL.η / 2 ∧
        rhoWin (CL.aOf μ X N) < CL.Zof μ X N n),
      (Eminus (CL.aOf μ X N) (-CL.Zof μ X N n) * Mbal (CL.aOf μ X N) (CL.Zof μ X N n)) ^ 2 =
      ∑ k ∈ (rowsOf N).filter (fun k => |uNode ((mirrorFamily Fz).step N) k - CR.uc μ| < CR.η / 2 ∧
        CR.Zof μ X N k < -rhoWin (CL.aOf μ X N)),
      (Eminus (CL.aOf μ X N) (CR.Zof μ X N k) * Mbal (CL.aOf μ X N) (CR.Zof μ X N k)) ^ 2 := by
    apply Finset.sum_nbij' (fun n => (N : ℤ) - n) (fun k => (N : ℤ) - k)
    · intro n hn
      simp only [rowsOf, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      refine ⟨⟨by omega, by omega⟩, ?_, ?_⟩
      · show |uNode (Fz.step N) ((N : ℤ) - n) - CR.uc μ| < CR.η / 2
        rw [hrefl, huc, hηe]
        have : Fz.L - uNode (Fz.step N) n - (Fz.L - CL.uc μ) = -(uNode (Fz.step N) n - CL.uc μ) := by ring
        rw [this, abs_neg]
        exact hn.2.1
      · show CR.Zof μ X N ((N : ℤ) - n) < -rhoWin (CL.aOf μ X N)
        rw [Zof_mirror hM hμ X N n]
        linarith [hn.2.2]
    · intro k hk
      simp only [rowsOf, Finset.mem_filter, Finset.mem_Icc] at hk ⊢
      refine ⟨⟨by omega, by omega⟩, ?_, ?_⟩
      · have hk1 : |uNode ((mirrorFamily Fz).step N) k - CR.uc μ| < CR.η / 2 := hk.2.1
        have e : uNode (Fz.step N) ((N : ℤ) - k) = Fz.L - uNode (Fz.step N) k := hrefl k
        show |uNode (Fz.step N) ((N : ℤ) - k) - CL.uc μ| < CL.η / 2
        rw [e]
        have hk1' : |uNode (Fz.step N) k - (Fz.L - CL.uc μ)| < CL.η / 2 := by
          rw [huc, hηe] at hk1; exact hk1
        have : Fz.L - uNode (Fz.step N) k - CL.uc μ = -(uNode (Fz.step N) k - (Fz.L - CL.uc μ)) := by ring
        rw [this, abs_neg]
        exact hk1'
      · have hk2 : CR.Zof μ X N k < -rhoWin (CL.aOf μ X N) := hk.2.2
        have := Zof_mirror hM hμ X N ((N : ℤ) - k)
        rw [show (N : ℤ) - ((N : ℤ) - k) = k by ring] at this
        show rhoWin (CL.aOf μ X N) < CL.Zof μ X N ((N : ℤ) - k)
        rw [← neg_neg (CL.Zof μ X N ((N : ℤ) - k)), ← this]
        linarith [hk2]
    · intro n hn
      simp only [rowsOf, Finset.mem_filter, Finset.mem_Icc] at hn
      simp
    · intro k hk
      simp
    · intro n _
      show (Eminus (CL.aOf μ X N) (-CL.Zof μ X N n) * Mbal (CL.aOf μ X N) (CL.Zof μ X N n)) ^ 2 =
        (Eminus (CL.aOf μ X N) (CR.Zof μ X N ((N : ℤ) - n)) * Mbal (CL.aOf μ X N) (CR.Zof μ X N ((N : ℤ) - n))) ^ 2
      rw [Zof_mirror hM hμ X N n, Mbal_neg]
  rw [hsum]
  exact H

end PCTailRight

/-! ### Pins -/

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.pc_tail_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pc_tail_left

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.pc_tail_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pc_tail_right

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.rhoWin_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rhoWin_margin

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.chain_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chain_decay

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.sum_geom_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sum_geom_block

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.Mbal_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Mbal_sq_le

end FormalResearch.JacobiEigenvectors.TheoremA

end
